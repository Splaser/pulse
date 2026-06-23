package com.kei.pulse.appwatch

import android.app.AppOpsManager
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.app.usage.UsageEvents
import android.app.usage.UsageStatsManager
import android.content.Context
import android.content.Intent
import android.os.Build
import android.os.Handler
import android.os.IBinder
import android.os.Looper
import android.os.Process
import android.widget.Toast
import androidx.core.app.NotificationCompat
import androidx.core.app.ServiceCompat
import androidx.core.content.ContextCompat
import androidx.core.content.getSystemService
import com.kei.pulse.AppContainer
import com.kei.pulse.MainActivity
import com.kei.pulse.R
import com.kei.pulse.data.AutoTuneController
import com.kei.pulse.data.FanController
import com.kei.pulse.data.FanCurveController
import com.kei.pulse.data.FpsReader
import com.kei.pulse.data.FrameLimiter
import com.kei.pulse.data.GovernorController
import com.kei.pulse.data.RefreshRateController
import com.kei.pulse.data.RgbController
import com.kei.pulse.data.SocDetector
import com.kei.pulse.data.TelemetryReader
import com.kei.pulse.data.TelemetrySnapshot
import com.kei.pulse.model.AppSettings
import com.kei.pulse.model.AutoTdpBias
import com.kei.pulse.model.FanCurve
import com.kei.pulse.model.FanTempController
import com.kei.pulse.model.CpuPolicyInfo
import com.kei.pulse.model.PerAppConfig
import com.kei.pulse.model.PerAppRestoreState
import com.kei.pulse.model.PowerTier
import com.kei.pulse.model.ProfileStateResolver
import com.kei.pulse.model.RgbMode
import com.kei.pulse.overlay.AutoTdpReadout
import com.kei.pulse.overlay.ClusterReadout
import com.kei.pulse.overlay.OverlayConfig
import com.kei.pulse.overlay.OverlayStats
import com.kei.pulse.overlay.PerformanceOverlay
import com.kei.pulse.overlay.MINUTES_SMOOTH_ALPHA
import com.kei.pulse.overlay.batteryMinutesLeft
import com.kei.pulse.overlay.batteryMinutesToFull
import com.kei.pulse.overlay.displayMinutes
import com.kei.pulse.overlay.smoothMinutes
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.cancel
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.isActive
import kotlinx.coroutines.launch
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import kotlin.math.roundToInt

/**
 * Watches the foreground app via UsageStats (needs the "Usage access" special permission) and
 * applies the bound per-app config when a configured app launches, restoring the pre-launch
 * state when it leaves. Mirrors the sleep monitor's structure: foreground service, mutex-guarded
 * transitions, persisted restore snapshot so a service restart mid-game can still revert.
 */
class ForegroundAppMonitorService : Service() {

    private val serviceScope = CoroutineScope(SupervisorJob() + Dispatchers.IO)
    private val transitionMutex = Mutex()
    private val container by lazy { AppContainer(this) }
    private val fanController = FanController()
    private val fanCurveController = FanCurveController()
    private val fanTempController = FanTempController() // closed-loop temp-target PI (Smart Custom-fan mode)
    private var customFanSupportedCache: Boolean? = null // null = not yet probed (Odin-only node check)
    @Volatile private var customFanRunning = false
    private var fanLoopJob: Job? = null // fast duty slew loop (drives the Custom curve smoothly)
    private var smoothedFanTempC: Float? = null // EMA of the SoC temp so curve targeting ignores ±1°C noise
    private val refreshRateController = RefreshRateController()
    private val governorController = GovernorController()
    private val telemetryReader = TelemetryReader()
    private val fpsReader by lazy { FpsReader(this) }
    private val overlay by lazy { PerformanceOverlay(this) }
    private val rgbController by lazy { RgbController(applicationContext) }
    private var rgbOn = false
    private var overlayPolicies: List<CpuPolicyInfo> = emptyList()
    private var overlaySoc: String? = null
    private var overlayProfileLabel: String = ""
    private var overlayDrawEma: Float? = null
    // Smoothed charge rate (W into the battery) while plugged in — kept separate from the discharge EMA so the
    // two never cross-contaminate across a plug/unplug. Each branch of overlayPower nulls the other.
    private var overlayChargeEma: Float? = null
    // Slow EMA of the battery time-left/time-to-full MINUTES (output-domain smoothing): capacity/draw turns
    // draw jitter into big jumps, so the displayed minutes are EMA'd + quantized. Re-seeds on a plug/unplug
    // (the two regimes have different magnitudes).
    private var overlayMinutesEma: Float? = null
    private var overlayMinutesDischarging: Boolean? = null
    // Full-battery energy (Wh) for the overlay's "LEFT" estimate. Constant, so it's cached on the first
    // successful read; a null (transient PServer-not-ready) just retries next poll rather than latching dead.
    private var overlayCapacityWh: Float? = null
    // Overlay session timer: accumulates foreground play time for the current bound game and
    // resumes (does not reset) when you minimize and return; only a different game resets it.
    private var sessionPackage: String? = null
    private var sessionAccumulatedMs: Long = 0L
    private var sessionResumeAt: Long = 0L
    @Volatile private var overlayLocked = true
    private var pollJob: Job? = null
    private var lastForeground: String? = null
    private var boundPackage: String? = null
    private var boundConfig: PerAppConfig? = null
    // Bug 9: the caps a non-AutoTDP per-app binding (saved Custom profile / power tier) actually wrote, held by
    // re-asserting them ~every 2s so the vendor game-boost daemon can't stomp them back up (AutoTDP already
    // self-protects this way; Custom/tier bindings didn't). policyId -> kHz; empty = nothing held. Its locks
    // (including the prime scaling_min) are released back to stock when the binding leaves.
    @Volatile private var boundReassertFreqs: Map<Int, Int> = emptyMap()
    private var boundReassertTick = 0
    // Vendor QS-tile coexistence: armed when the managed fan changes, so the override notice fires once per value.
    @Volatile private var fanOverrideNotified = false
    @Volatile private var lastManagedFan: Int? = null
    // DIAG (fan investigation): dedupe the per-tick fan-decision log so a steady state logs once, not every poll.
    @Volatile private var lastFanDecisionLog: String? = null
    @Volatile private var lastDriftLogMs = 0L // throttle the fast-loop "vendor re-pinned the duty" diagnostic
    private var ticksSincePersist = 0
    private var lastActiveLoadPercent = 0 // max(cpu,gpu) load from the last tick — gates per-app draw tracking
    // The TelemetrySnapshot tick() read THIS iteration, shared with the draw-tracker + RGB so they don't re-read
    // the battery/telemetry nodes again. Null when tick() didn't read this tick (overlay + AutoTDP both off);
    // consumers then fall back to their own cheap read so behavior in that case is unchanged.
    @Volatile private var tickTelemetry: TelemetrySnapshot? = null
    // Debounce state: a newly-seen foreground package must be observed on two consecutive polls
    // before we act on it (see pollLoop).
    private var candidatePackage: String? = null
    private var candidateConfirmCount = 0
    // Current foreground package, used to drive a standalone overlay (no per-app binding).
    private var overlayForeground: String? = null

    // ── AutoTDP: dynamic CPU→GPU clock trimming that holds the game's refresh-rate FPS ──
    private val autoTune = AutoTuneController()
    private var autoTdpPackage: String? = null
    private var autoTdpTick = 0
    private var autoTdpLogTick = 0

    override fun onCreate() {
        super.onCreate()
        createNotificationChannel()
        ServiceCompat.startForeground(
            this,
            NOTIFICATION_ID,
            buildNotification(),
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.UPSIDE_DOWN_CAKE) {
                android.content.pm.ServiceInfo.FOREGROUND_SERVICE_TYPE_SPECIAL_USE
            } else {
                0
            },
        )
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        if (intent?.action == ACTION_TOGGLE_OVERLAY_LOCK) {
            serviceScope.launch {
                overlayLocked = !overlayLocked
                val settings = container.settingsStorage.settings.first()
                overlay.setConfig(
                    OverlayConfig(settings.overlayPreset, settings.overlayOpacity, overlayLocked, settings.overlayElements),
                )
                updateNotification(
                    if (overlayLocked) "Overlay locked" else "Overlay unlocked — drag to reposition",
                )
            }
            return START_STICKY
        }
        if (pollJob?.isActive != true) {
            pollJob = serviceScope.launch { pollLoop() }
        }
        return START_STICKY
    }

    override fun onBind(intent: Intent?): IBinder? = null

    override fun onDestroy() {
        overlay.hide()
        // Disable TimeStats off the main thread (it goes through the blocking root shell) so the
        // compositor isn't left recording if the service is torn down while a game is showing.
        Thread { runCatching { fpsReader.stop() } }.start()
        // Safety net: if the prime is parked when the service is destroyed, re-online it off-main so a
        // teardown can't strand the cores offline. Best-effort (the root shell may already be gone);
        // the pollLoop startup net re-onlines on the next service start as the backstop for a hard kill.
        if (autoTune.isPrimeParked) {
            val cores = primeCoresOf(overlayPolicies)
            if (cores.isNotEmpty()) {
                Thread { runCatching { AutoTuneController.setCoresOnlineToDevice(cores, true) } }.start()
            }
        }
        // Safety net: if Custom was driving (vendor left in manual passthrough), hand the fan back to the Smart
        // auto-curve off-main so a teardown can't strand it in manual mode with no vendor thermal regulation.
        if (customFanRunning) {
            Thread { runCatching { fanController.setMode(FanController.SMART) } }.start()
        }
        serviceScope.cancel()
        super.onDestroy()
    }

    private suspend fun pollLoop() {
        // Master switch OFF: hand every control back to manufacturer stock and don't run at all (the service
        // shouldn't have been started, but self-terminate cleanly if it was).
        if (!container.settingsStorage.settings.first().pulseEnabled) {
            transitionMutex.withLock { revertToStock() }
            stopSelf()
            return
        }
        // Anti-stranding net: a hard process death can't run onDestroy, so a game parked at kill time
        // would leave the prime cores offline until reboot. On every fresh service start, hand the managed
        // prime cluster back online (idempotent; the kernel re-idles them if they're truly idle). Any
        // session resumed below re-decides parking from scratch via startAutoTdp → release().
        runCatching {
            val primeCores = primeCoresOf(ensurePolicies())
            if (primeCores.isNotEmpty()) AutoTuneController.setCoresOnlineToDevice(primeCores, true)
        }
        // A restore snapshot surviving from before a service restart means a bound app was
        // active. If it's still foreground, resume tracking it; otherwise revert right away.
        if (container.perAppConfigStorage.restoreState.first() != null) {
            val foreground = currentForegroundPackage()
            val cfg = foreground?.let { fg ->
                container.perAppConfigStorage.configs.first().firstOrNull { it.packageName == fg }
            }
            if (foreground != null && cfg != null) {
                boundPackage = foreground
                boundConfig = cfg
                lastForeground = foreground
                startOrResumeSession(foreground)
                // Resume an AutoTDP binding without re-snapshotting (boundPackage is already set, so
                // the pre-crash restore snapshot stands).
                if (PerAppConfig.isAuto(cfg.profileBinding)) startAutoTdp(foreground, cfg)
            } else {
                transitionMutex.withLock { restoreSnapshot() }
            }
        }
        while (serviceScope.isActive) {
            val perAppEnabled = container.perAppConfigStorage.enabled.first()
            // Any saved per-app binding keeps the watcher alive so it ALWAYS engages and overrides the
            // global mode — a binding must never sit inert behind the master toggle ("per-app comes first").
            val hasPerAppConfigs = container.perAppConfigStorage.configs.first().isNotEmpty()
            val settings = container.settingsStorage.settings.first()
            if (!settings.pulseEnabled) {
                // Master flipped OFF mid-run — revert to stock and stop the service.
                transitionMutex.withLock { revertToStock() }
                stopSelf()
                return
            }
            // The watcher also runs for a standalone overlay or the RP6 RGB LED (no per-app/AutoTDP needed).
            if ((!perAppEnabled && !hasPerAppConfigs && !settings.autoTdpDefaultEnabled &&
                    !settings.overlayEnabled && settings.rgbMode == RgbMode.OFF &&
                    settings.managedFanMode == null) || !hasUsageAccess(this)
            ) {
                stopSelf()
                return
            }
            val foreground = currentForegroundPackage()
            overlayForeground = foreground
            if (foreground != null && foreground != lastForeground) {
                // Debounce: a game's foreground package can flap with overlays/splash activities,
                // and acting on a single sample causes apply->restore thrash. Require the new
                // package to persist across two consecutive polls (~1.5s extra latency) before
                // switching bound state.
                if (foreground == candidatePackage) {
                    candidateConfirmCount++
                } else {
                    candidatePackage = foreground
                    candidateConfirmCount = 1
                }
                if (candidateConfirmCount >= 2) {
                    lastForeground = foreground
                    candidatePackage = null
                    candidateConfirmCount = 0
                    handleForegroundChange(foreground)
                }
            } else if (foreground == lastForeground) {
                // Settled back on the current foreground — drop any pending candidate.
                candidatePackage = null
                candidateConfirmCount = 0
            }
            tick() // reads telemetry once (when active) and caches it for the draw-tracker + RGB below
            trackDrawForBoundApp()
            reassertManagedFan(settings)
            reassertBoundCaps() // Bug 9: hold a Custom/tier binding's caps against the vendor game-boost daemon
            updateRgb(settings)
            delay(POLL_INTERVAL_MS)
        }
    }

    /**
     * One poll step for the overlay + AutoTDP. Reads telemetry/FPS once and feeds both consumers,
     * so an active overlay and an AutoTDP session never double up the (serialized) PServer work.
     * Wrapped so an overlay/FPS/tuning error can never take down the poll loop (which also drives
     * profile-switching and draw-tracking).
     */
    private suspend fun tick() {
        try {
            tickTelemetry = null // repopulated below only if we actually read telemetry this tick
            val settings = container.settingsStorage.settings.first()
            // Never draw the OSD over PULSE itself, the home screen, or Android UI, even if a just-left game's
            // boundPackage hasn't cleared yet (the foreground-change debounce lags by a poll or two). NB this
            // uses boundPackage (not overlayForeground) for the show, since overlayForeground briefly goes null
            // during steady play (no new ACTIVITY_RESUMED events) — the OSD must NOT flicker off then.
            // The OSD's target app: the tuning-bound package if PULSE is tuning one, else the confirmed
            // foreground app. Using `lastForeground` (debounced, stable during play) lets the OSD work as a
            // STANDALONE overlay — just the toggle on, no per-app/AutoTDP binding. It was gated on boundPackage
            // before, so the OSD silently never showed over a game/benchmark PULSE wasn't also tuning.
            val osdTarget = boundPackage ?: lastForeground
            val neutralForeground = isNeutralForeground(overlayForeground)
            val overlayShouldShow = osdTarget != null &&
                !isNeutralForeground(osdTarget) &&
                settings.overlayEnabled &&
                PerformanceOverlay.hasPermission(this) &&
                !neutralForeground
            val autoActive = autoTdpPackage != null
            if (!overlayShouldShow && !autoActive) {
                if (overlay.isShowing) hideOverlay()
                fpsReader.stop() // nothing needs FPS — ensure TimeStats isn't left recording
                return
            }
            val policies = ensurePolicies()
            val telemetry = telemetryReader.read(policies)
            tickTelemetry = telemetry // share this one read with trackDrawForBoundApp() + updateRgb()
            // Drives the per-app draw gate: only count draw toward peak/avg while the device is actually
            // working, so idle/menu/paused time can't poison the battery-life estimate.
            lastActiveLoadPercent = maxOf(telemetry.cpuLoadPercent ?: 0, telemetry.gpuLoadPercent ?: 0)
            val fps = fpsReader.read(osdTarget) // FPS for the OSD target (works for standalone-overlay apps too)
            val auto = if (autoActive) buildAutoReadout(policies, telemetry) else null
            when {
                overlayShouldShow && !overlay.isShowing -> { showOverlay(settings); feedOverlay(settings, telemetry, fps, auto) }
                overlayShouldShow -> feedOverlay(settings, telemetry, fps, auto)
                overlay.isShowing -> hideOverlay()
            }
            if (autoActive) stepAutoTdp(policies, telemetry, fps)
        } catch (t: Throwable) {
            android.util.Log.e("PulseOverlay", "overlay/auto tick failed", t)
        }
    }

    /**
     * Vendor QS-tile coexistence. While PULSE is actively managing the fan for the foreground app
     * (`boundConfig.fanMode` set), the system Fan tile can change `fan_mode` out from under us. If it drifted,
     * re-apply PULSE's value and pop a one-time-per-session notice. Only runs while managing — when PULSE is
     * idle/off, `boundConfig` is null so the tile behaves normally. Performance/RGB are intentionally left alone:
     * AutoTDP's per-tick cap re-assert already overrides the vendor `cpu_init`, and RGB has its own re-assert.
     */
    /** DIAG (fan investigation): log a fan-decision line only when it changes, so a steady state logs once. */
    private fun fanLog(msg: String) {
        if (msg != lastFanDecisionLog) {
            lastFanDecisionLog = msg
            android.util.Log.d("PulseFan", msg)
        }
    }

    /**
     * Drive the Custom fan (closed-loop PI when "Hold Target Temp" is on, else the manual spline) for this
     * tick. Returns true if it ran (device exposes the gpio5_pwm2 node). Used as the normal global Custom mode
     * AND during AutoTDP when the user's fan mode is Custom: AutoTDP's thermal ceiling cools via CLOCKS, so the
     * fan PI (targeting a temp ≥ the ceiling) sees the chip below its target and idles ⇒ quiet, vs. the vendor
     * Smart curve that ramps hard at the same temp.
     */
    private suspend fun runCustomFan(settings: AppSettings): Boolean {
        if (!isCustomFanSupported()) return false
        // Writing fan_mode=6 RESETS the Odin's duty to a ~50% mode-init default, so pin our current intended
        // duty in the SAME command (read-first → only on drift). Also beats the QS fan tile.
        val intendedDuty = FanCurve.percentToDuty(fanCurveController.appliedPercent, fanCurveController.period)
        fanController.ensureManualMode(intendedDuty)
        val t = tickTelemetry ?: telemetryReader.read(ensurePolicies())
        fanCurveController.slewPerSecond = settings.fanResponseStep
        // Smooth the SoC temp (EMA) before targeting so ±1–2°C sensor noise doesn't wiggle the duty.
        val rawTemp = maxOf(t.cpuTempC ?: 0, t.gpuTempC ?: 0)
        val sm = smoothedFanTempC?.let { it * 0.6f + rawTemp * 0.4f } ?: rawTemp.toFloat()
        smoothedFanTempC = sm
        if (settings.fanSmartEnabled) {
            // During AutoTDP, cascade the fan BELOW the clock-trim ceiling so it spins up first (buys GPU
            // clocks on a hot AAA game) instead of the clocks throttling while the fan idles. Otherwise the
            // user's manual target.
            val targetC = if (autoTdpPackage != null)
                AutoTuneController.autoTdpFanTargetC(settings.fanTargetTempC, autoTune.thermalCeilingC())
            else settings.fanTargetTempC
            val duty = fanTempController.update(sm.roundToInt(), targetC, POLL_INTERVAL_MS / 1000.0)
            fanCurveController.setTargetPercent(duty)
        } else {
            fanCurveController.curve = settings.fanCurve.shiftedBy(settings.fanBias)
            fanCurveController.setTarget(sm.roundToInt())
        }
        customFanRunning = true
        ensureFanReassertLoop()
        lastManagedFan = FanController.CUSTOM
        fanLog("CUSTOM fan running (autoTdp=${autoTdpPackage != null} smart=${settings.fanSmartEnabled} temp=${sm.roundToInt()} applied=${fanCurveController.appliedPercent}% target=${settings.fanTargetTempC})")
        return true
    }

    private suspend fun reassertManagedFan(settings: AppSettings) {
        // Autocalibrate is sweeping the duty node directly — stand down so we don't fight its writes.
        if (FanCurveController.externalControlActive) return
        // AutoTDP owns the clocks/governor. The FAN follows the user's mode: if they picked Custom (and it's
        // supported), keep driving the quiet closed-loop Custom fan DURING AutoTDP — AutoTDP's thermal ceiling
        // cools via clocks, so the fan PI idles ⇒ quiet (vs. vendor Smart ramping hard). Otherwise stand down
        // to the vendor Smart that startAutoTdp set.
        if (autoTdpPackage != null) {
            if (settings.managedFanMode == FanController.CUSTOM && runCustomFan(settings)) return
            stopCustomFan(); return
        }
        // The fan PULSE wants: a foreground app's per-app fan takes priority, else the global Fan-card mode.
        var desired = boundConfig?.fanMode ?: settings.managedFanMode
        val neutralFg = isNeutralForeground(overlayForeground)
        if (desired == null) {
            fanLog("desired=null → RELEASE to vendor (neutralFg=$neutralFg boundFan=${boundConfig?.fanMode} managed=${settings.managedFanMode})")
            lastManagedFan = null; stopCustomFan(restoreVendor = true); return
        }

        // Custom fan curve (Odin 3 / RP6 / Thor — all expose the gpio5_pwm2 node): PULSE puts the vendor in
        // manual passthrough then drives the PWM duty straight from the user's temp→% curve, slewing smoothly.
        // On any device without the node Custom falls back to Smart so we never sit on a phantom mode. Switching
        // to any other mode calls stopCustomFan() and the caller sets that mode, cleanly retaking the fan.
        if (desired == FanController.CUSTOM) {
            if (runCustomFan(settings)) return
            desired = FanController.SMART // unsupported device: don't sit on a phantom Custom mode
        }
        stopCustomFan()

        if (desired != lastManagedFan) { lastManagedFan = desired; fanOverrideNotified = false } // re-arm on change
        val live = fanController.readMode() ?: run { fanLog("desired=$desired live=READ-FAILED (neutralFg=$neutralFg)"); return }
        fanLog("desired=$desired live=$live neutralFg=$neutralFg boundFan=${boundConfig?.fanMode} managed=${settings.managedFanMode} ${if (live == desired) "HELD" else "WILL-REWRITE"}")
        if (live == desired) return
        android.util.Log.d("PulseFan", "system Fan tile drifted fan_mode=$live, want=$desired — re-applying")
        fanController.setMode(desired)
        if (!fanOverrideNotified && container.perAppConfigStorage.switchNotices.first()) {
            fanOverrideNotified = true
            showToast("PULSE · system Fan tile changed the fan — re-applied ${FanController.labelFor(desired)}")
        }
    }

    /**
     * Stop driving the custom fan curve (if running). Pass [restoreVendor] = true when NO other fan mode is
     * about to take over (PULSE going idle / shutting down) so we hand the fan back to the vendor's Smart auto
     * curve — otherwise it'd be stranded in manual passthrough with no thermal regulation. When switching to
     * another vendor mode the caller sets that mode itself, so the restore is skipped.
     */
    private fun stopCustomFan(restoreVendor: Boolean = false) {
        if (customFanRunning) {
            customFanRunning = false
            fanLoopJob?.cancel()
            fanLoopJob = null
            fanCurveController.reset()
            fanTempController.reset() // clear the PI integral so a new session starts clean
            smoothedFanTempC = null // re-seed the temp EMA on the next Custom session
            if (restoreVendor) {
                serviceScope.launch(Dispatchers.IO) { fanController.setMode(FanController.SMART) }
            }
        }
    }

    /**
     * Start (once) the fast (~300ms) loop that SLEWS the fan duty toward the target the telemetry tick set,
     * in small steps so the fan ramps smoothly and quietly. Each pass also RECONCILES against the live duty
     * node: the Odin vendor re-pins the duty (to ~50%) the instant you leave a game to the home screen even in
     * manual passthrough, and catching it here — not at the ~1s poll — shrinks the audible rev window to one
     * [FAN_SLEW_MS] pass. The reconcile is a no-op where nothing re-pins (RP6/Thor), so it never adds writes
     * there. The loop self-exits when [customFanRunning] clears; [serviceScope] cancellation tears it down too.
     */
    private fun ensureFanReassertLoop() {
        if (fanLoopJob?.isActive == true) return
        fanLoopJob = serviceScope.launch {
            var sinceSlewMs = 0L
            while (customFanRunning) {
                // Pause everything while autocalibrate drives the duty directly (avoids a write race).
                if (!FanCurveController.externalControlActive) {
                    // Re-check the live duty every FAN_RECHECK_MS. The Odin vendor slams the duty to ~50% on
                    // game foreground-transitions even in manual passthrough (firmware game-detection we can't
                    // disable); catch it and re-pin OUR value immediately so the rev is inaudible.
                    val live = FanCurveController.readDutyFromDevice()
                    if (fanCurveController.reconcileActualDuty(live)) {
                        fanCurveController.reassertCurrentDuty()
                        val now = android.os.SystemClock.elapsedRealtime()
                        if (now - lastDriftLogMs > 800) {
                            lastDriftLogMs = now
                            android.util.Log.d("PulseFan", "fast-loop drift: node=$live fan_mode=${fanController.readMode()} re-pinned=${fanCurveController.appliedPercent}%")
                        }
                    }
                    // Advance the smooth ramp on its own slower cadence so the fan-response-step tuning is
                    // unchanged by the faster duty re-check above.
                    sinceSlewMs += FAN_RECHECK_MS
                    if (sinceSlewMs >= FAN_SLEW_MS) {
                        fanCurveController.slew(sinceSlewMs)
                        sinceSlewMs = 0L
                    }
                }
                delay(FAN_RECHECK_MS)
            }
        }
    }

    /** Lazily probe once whether this device exposes the writable custom-fan PWM node; cache the period. */
    private suspend fun isCustomFanSupported(): Boolean {
        customFanSupportedCache?.let { return it }
        val ok = FanController.customFanAvailable()
        if (ok) {
            fanCurveController.period =
                FanCurveController.readPeriodFromDevice() ?: FanCurveController.DEFAULT_PERIOD
        }
        customFanSupportedCache = ok
        return ok
    }

    /**
     * Bug 9: a per-app Custom-profile or power-tier binding applies its CPU/GPU caps once on entry, but the
     * vendor game-boost daemon re-pins `scaling_max`/`max_pwrlevel` as root mid-game — so the cap silently stops
     * biting (AutoTDP already counters this with a per-tick re-assert; Custom/tier didn't). Capture the caps
     * that actually got written so [reassertBoundCaps] can hold them.
     */
    private suspend fun captureBoundReassertCaps() {
        val policies = ensurePolicies()
        val applied = container.repository.readCurrentValues()
        // Hold only the clocks the binding actually capped (below their top OPP); skip anything left at max so we
        // never needlessly lock/lower an uncapped cluster (esp. the prime, whose min we only touch when capped).
        boundReassertFreqs = applied.filter { (id, freq) ->
            val p = policies.firstOrNull { it.id == id } ?: return@filter false
            freq in 1 until p.selectableMaxFreq
        }
        boundReassertTick = 0
        if (boundReassertFreqs.isNotEmpty()) {
            android.util.Log.d("PulseReassert", "holding ${boundReassertFreqs.size} capped clock(s) vs vendor daemon: $boundReassertFreqs")
        }
    }

    /** Re-assert the held Custom/tier caps ~every other tick (≈2s), the same locked path AutoTDP re-asserts on. */
    private suspend fun reassertBoundCaps() {
        val freqs = boundReassertFreqs
        if (freqs.isEmpty()) return
        if (boundReassertTick++ % 2 != 0) return
        AutoTuneController.applyFreqsToDevice(ensurePolicies(), freqs)
    }

    /** Stop holding a binding's caps and hand its locks (incl. the prime `scaling_min`) back to stock (`644`). */
    private suspend fun clearBoundReassert() {
        if (boundReassertFreqs.isEmpty()) return
        boundReassertFreqs = emptyMap()
        AutoTuneController.releaseCapsToDevice(ensurePolicies())
    }

    /**
     * RP6 RGB joystick LED (Phase 1). Each poll it drives the SN3112 LED from the selected mode: BATTERY
     * (green→red as it drains, Game-Boy-Color style), HEAT (blue→orange→dark-red as it warms), or MANUAL
     * (a fixed color). Self-gated by [RgbController.available] — completely inert on the Odin, which has no
     * such LED, so it never touches that device. Reads telemetry only when a live (battery/heat) mode needs it.
     */
    private suspend fun updateRgb(settings: AppSettings) {
        try {
            if (settings.rgbMode == RgbMode.OFF || !rgbController.available()) {
                if (rgbOn) { rgbController.off(); rgbOn = false }
                return
            }
            when (settings.rgbMode) {
                RgbMode.MANUAL -> rgbController.setManual(
                    settings.rgbManualLeftColor, settings.rgbManualLeftBrightness,
                    settings.rgbManualRightColor, settings.rgbManualRightBrightness,
                )
                RgbMode.BATTERY -> {
                    // Reuse tick()'s snapshot when it read this tick; else a direct read (RGB-only, no overlay/AutoTDP).
                    val pct = (tickTelemetry ?: telemetryReader.read(ensurePolicies())).batteryPercent ?: 100
                    val c = RgbController.batteryColor(pct)
                    rgbController.setColor(c.first, c.second, c.third)
                }
                RgbMode.HEAT -> {
                    val t = tickTelemetry ?: telemetryReader.read(ensurePolicies())
                    val c = RgbController.heatColor(maxOf(t.cpuTempC ?: 0, t.gpuTempC ?: 0))
                    rgbController.setColor(c.first, c.second, c.third)
                }
                RgbMode.OFF -> return
            }
            rgbOn = true
        } catch (t: Throwable) {
            android.util.Log.e("PulseRgb", "rgb update failed", t)
        }
    }

    /** CPU+GPU policies, loaded once and reused for telemetry, the overlay, and AutoTDP. */
    private suspend fun ensurePolicies(): List<CpuPolicyInfo> {
        if (overlayPolicies.isEmpty()) overlayPolicies = container.repository.currentPolicies()
        return overlayPolicies
    }

    /**
     * The prime cluster's offlinable cpu ids (highest-max-freq CPU policy, never cpu0) — mirrors
     * [AutoTuneController]'s own `primeCores` so the service can re-online them as a stranding safety net
     * (onDestroy + service-start), independent of the controller's internal `primeParked` state.
     */
    private fun primeCoresOf(policies: List<CpuPolicyInfo>): List<Int> =
        policies.filterNot { it.isGpu }.maxByOrNull { it.selectableMaxFreq }?.cpuIds?.filter { it != 0 }.orEmpty()

    private suspend fun showOverlay(settings: AppSettings) {
        ensurePolicies()
        if (overlaySoc == null) overlaySoc = SocDetector.displayName(container.repository.socModel())
        overlayProfileLabel = resolveProfileLabel(settings)
        overlay.show(
            settings = settings,
            config = OverlayConfig(settings.overlayPreset, settings.overlayOpacity, overlayLocked, settings.overlayElements),
            onMoved = { x, y -> serviceScope.launch { container.settingsStorage.persistOverlayPosition(x, y) } },
            onPresetCycled = { preset -> serviceScope.launch { container.settingsStorage.persistOverlayPreset(preset) } },
            // Keep the service's lock state synced with the in-overlay 🔒 button so a later config push
            // doesn't revert it (lock is intentionally not persisted — it resets to locked each start).
            onLockToggled = { locked ->
                overlayLocked = locked
                serviceScope.launch {
                    updateNotification(if (locked) "Overlay locked" else "Overlay unlocked — drag to reposition")
                }
            },
        )
    }

    /** The bound app's profile/tier, for the overlay banner (e.g. "Balanced", "Custom", a saved name). */
    private suspend fun resolveProfileLabel(settings: AppSettings): String {
        if (autoTdpPackage != null) return "AutoTDP"
        val cfg = boundConfig ?: return settings.activeTierLabel
        PerAppConfig.tierFromBinding(cfg.profileBinding)?.let { return it.label }
        val binding = cfg.profileBinding ?: return settings.activeTierLabel
        return container.repository.observeState().first().displayProfiles
            .firstOrNull { it.id == binding }?.name ?: settings.activeTierLabel
    }

    private fun feedOverlay(
        settings: AppSettings,
        telemetry: TelemetrySnapshot,
        fps: FpsReader.FpsSample?,
        auto: AutoTdpReadout?,
    ) {
        val (powerW, isCharging) = overlayPower(telemetry)
        // Battery readout: on battery = time-LEFT from the smoothed draw; plugged in = time-to-FULL from the
        // smoothed charge rate (= powerW while charging). Capacity is read once. Unknown/tiny cases → null → "—".
        if (overlayCapacityWh == null) overlayCapacityWh = com.kei.pulse.data.BatteryReader.capacityWh()
        val rawMinutes = if (telemetry.isDischarging) {
            batteryMinutesLeft(overlayCapacityWh, telemetry.batteryPercent, overlayDrawEma, discharging = true)
        } else {
            batteryMinutesToFull(overlayCapacityWh, telemetry.batteryPercent, chargeWatts = powerW)
        }
        // Smooth the displayed minutes so they don't jump around (capacity/draw amplifies draw jitter). Re-seed
        // the EMA across a plug/unplug since time-left and time-to-full are different magnitudes.
        if (telemetry.isDischarging != overlayMinutesDischarging) overlayMinutesEma = null
        overlayMinutesDischarging = telemetry.isDischarging
        overlayMinutesEma = smoothMinutes(overlayMinutesEma, rawMinutes, MINUTES_SMOOTH_ALPHA)
        val minutesLeft = displayMinutes(overlayMinutesEma)
        overlay.update(
            OverlayStats(
                telemetry = telemetry,
                fps = fps,
                sessionElapsedMs = sessionElapsedMs(),
                socModel = overlaySoc,
                profileLabel = overlayProfileLabel,
                powerDrawW = powerW,
                powerIsCharging = isCharging,
                minutesLeft = minutesLeft,
                autoTdp = auto,
            ),
        )
    }

    /** Snapshot of what AutoTDP is doing now (per-cluster caps + clocks, GPU, learning) for the overlay. */
    private fun buildAutoReadout(
        policies: List<CpuPolicyInfo>,
        telemetry: TelemetrySnapshot,
    ): AutoTdpReadout {
        val caps = autoTune.caps
        val cpuClusters = policies.filterNot { it.isGpu }
            .sortedByDescending { it.selectableMaxFreq } // prime first
            .map { ClusterReadout(caps[it.id] ?: 100, telemetry.cpuClocksMhz[it.id]) }
        val gpu = policies.firstOrNull { it.isGpu }
        return AutoTdpReadout(
            cpuClusters = cpuClusters,
            gpuCapPercent = gpu?.let { caps[it.id] ?: 100 },
            gpuMhz = telemetry.gpuMhz,
            targetFps = autoTune.targetFps,
            primeParked = autoTune.isPrimeParked,
            learningPercent = autoTune.learnedPercent(),
            learned = autoTune.powerModel.hasSplit(),
        )
    }

    // ── AutoTDP session ─────────────────────────────────────────────────────────────────────────

    /**
     * Every home/launcher package — the home screen is the "neutral" state (along with PULSE itself) the
     * global AutoTDP default does NOT tune and the OSD never draws over. A device can expose several home
     * activities, or none set as default (then `resolveActivity` returns the system *resolver*, not a
     * launcher). Resolved lazily but **never cached empty**: the old `by lazy { resolveActivity… }` cached a
     * transient/early null for the service's whole life, which leaked the OSD onto the home screen and made
     * the global default bind to the launcher. Re-resolving while empty fixes that.
     */
    private var cachedHomePackages: Set<String> = emptySet()
    private fun homePackages(): Set<String> {
        if (cachedHomePackages.isNotEmpty()) return cachedHomePackages
        val intent = Intent(Intent.ACTION_MAIN).addCategory(Intent.CATEGORY_HOME)
        val resolved = runCatching {
            val all = packageManager.queryIntentActivities(intent, 0)
                .mapNotNull { it.activityInfo?.packageName }
            val default = packageManager
                .resolveActivity(intent, android.content.pm.PackageManager.MATCH_DEFAULT_ONLY)
                ?.activityInfo?.packageName
            (all + listOfNotNull(default)).toSet()
        }.getOrNull().orEmpty()
        if (resolved.isNotEmpty()) cachedHomePackages = resolved
        return resolved
    }

    /**
     * Android's own shell surfaces — the notification shade / quick settings / recents (systemui) and the
     * Settings app. The global default never tunes these and the OSD never draws over them: they're "Android
     * UI", not a game or app. This is why the OSD leaked only with the global default on — per-app binds to a
     * named app, but the global default treated every non-home package (Settings included) as a target.
     */
    private val systemUiPackages = setOf("com.android.systemui", "com.android.settings")

    /**
     * The foreground is "neutral" — PULSE itself, the home screen, or an Android shell surface — so the global
     * default never tunes it and the OSD stays hidden. (Per-app bindings are unaffected: they only ever engage
     * on their named app.)
     */
    private fun isNeutralForeground(pkg: String?): Boolean =
        uiInForeground || // PULSE's own UI is on screen (even if a keyboard/dialog is the latest resumed pkg)
            (pkg != null && (pkg == packageName || pkg in systemUiPackages || pkg in homePackages()))

    /** Global AutoTDP tunes any foreground app except PULSE itself and the home screen. */
    private fun isGlobalAutoTdpTarget(pkg: String): Boolean = !isNeutralForeground(pkg)

    /**
     * Begin an AutoTDP session for [pkg]: snapshot the pre-game state (caps + fan + governor) when
     * entering from unbound, reopen the clocks to full as the loop's starting point, and lock the
     * managed controls — **Smart fan** + the **Balanced governor** (which scales freq to load under
     * AutoTDP's caps, the SoC-appropriate scaler being auto-picked). The app's per-app refresh rate
     * is kept (the only control left adjustable). [config] is null for global-default games. Caller
     * must hold [transitionMutex] and have released any prior session first.
     */
    private suspend fun startAutoTdp(pkg: String, config: PerAppConfig?) {
        val policies = ensurePolicies()
        val settings = container.settingsStorage.settings.first()
        if (boundPackage == null) {
            val priorGovernor = policies.firstOrNull { !it.isGpu }?.let { governorController.readGovernor(it) }
            container.perAppConfigStorage.persistRestoreState(
                PerAppRestoreState(
                    values = container.repository.readCurrentValues(),
                    appliedDisplayProfileId = ProfileStateResolver.MANUAL_PROFILE_ID,
                    activeTierLabel = settings.activeTierLabel,
                    fanMode = fanController.readMode(),
                    // AutoTDP always forces max refresh, so always capture the prior rate to restore.
                    refreshRateHz = refreshRateController.readPeak(),
                    governor = priorGovernor,
                ),
            )
        }
        autoTune.release(policies) // reset state + reopen clocks to full — AutoTDP's starting point
        autoTune.powerModel = container.settingsStorage.loadPowerModel(container.repository.socModel() ?: "")
        // Warm-start from this app's last converged caps so the loop fine-tunes instead of
        // re-discovering from full clocks every launch (gets quicker the more it's played).
        container.settingsStorage.loadAutoTdpCaps(pkg)?.let { autoTune.warmStart(policies, it) }
        // Regulate to this app's FPS target (per-app override, else the global default), snapped to this
        // SoC's valid options so a legacy 45/0 or an Odin value carried onto an 8 Gen 2 can't slip through.
        val soc = container.repository.socModel()
        val target = PerAppConfig.snapFpsTarget(
            config?.fpsTarget ?: settings.autoTdpFpsTarget,
            PerAppConfig.fpsTargetsFor(soc),
        )
        autoTune.targetFps = target
        // Per-app parking overrides the global default (parking is part of the AutoTDP algorithm).
        autoTune.aggressivePark = config?.aggressivePark ?: settings.autoTdpAggressivePark
        // Efficiency↔smoothness lean: per-app overrides the global default (per-app-first).
        autoTune.bias = AutoTdpBias.resolve(config?.bias, settings.autoTdpBias)
        // Enforce the target. Use the Game Mode fps cap (panel held at max refresh, 120 Hz, for latency)
        // only when the SoC honors it AND the target evenly divides 120 — 30/40/60/120 cap cleanly. 90
        // can't be frame-paced at 120 Hz (floors to 60), and the 8 Gen 2 (Thor/RP6) doesn't honor the cap
        // at all; both take the refresh-rate path (the panel rate IS the cap). The clock loop holds [target].
        val maxRefresh = RefreshRateController.RATES.max()
        if (PerAppConfig.useGameModeCap(soc, target, maxRefresh)) {
            refreshRateController.setRate(maxRefresh)
            val applied = FrameLimiter.setCap(pkg, target)
            // Confirm the firmware honored the value (not floored) — read it back in the diagnostic log.
            if (AUTO_DEBUG) {
                android.util.Log.d("PulseAutoTdp", "FRAME-CAP requested=$target applied=[${applied?.trim()}]")
            }
        } else {
            FrameLimiter.clear(pkg)
            refreshRateController.setRate(target)
        }
        autoTdpPackage = pkg
        autoTdpTick = 0
        // Fan: force vendor Smart UNLESS the user runs the Custom fan — then reassertManagedFan keeps driving
        // their (quieter) closed-loop Custom fan during AutoTDP instead.
        if (settings.managedFanMode != FanController.CUSTOM) fanController.setMode(FanController.SMART)
        GovernorController.OPTIONS.firstOrNull { it.label == "Balanced" }
            ?.let { governorController.setGovernor(policies, it) }
        overlayProfileLabel = "AutoTDP"
        // Only announce explicit per-app AutoTDP bindings — the global default would spam on every
        // app switch.
        if (config != null && container.perAppConfigStorage.switchNotices.first()) {
            val appName = config.appLabel.takeIf { it.isNotBlank() } ?: pkg
            showToast("PULSE · $appName: AutoTDP")
            updateNotification("$appName: AutoTDP")
        }
    }

    /** End the AutoTDP session, reopening the clocks. The fan/governor/caps are reverted by restoreSnapshot. */
    private fun stopAutoTdp() {
        val pkg = autoTdpPackage ?: return
        FrameLimiter.clear(pkg) // drop the Game Mode fps cap
        val converged = autoTune.caps // snapshot before release() resets the caps
        if (overlayPolicies.isNotEmpty()) autoTune.release(overlayPolicies)
        val learned = autoTune.powerModel
        serviceScope.launch {
            container.settingsStorage.persistPowerModel(learned) // keep what it learned
            // Remember this app's operating point for a faster warm-start next time (skip no-op all-100).
            if (converged.values.any { it < 100 }) {
                container.settingsStorage.persistAutoTdpCaps(pkg, converged)
            }
        }
        autoTdpPackage = null
        autoTdpTick = 0
    }

    /**
     * Advance the AutoTDP loop ~every other poll (≈2s). Passes the live battery draw so the controller
     * can learn the SoC's CPU/GPU power split; the learned model is persisted periodically.
     */
    private fun stepAutoTdp(policies: List<CpuPolicyInfo>, telemetry: TelemetrySnapshot, fps: FpsReader.FpsSample?) {
        if (autoTdpTick++ % 2 != 0) return
        val drawW = telemetry.batteryDrawW?.takeIf { telemetry.isDischarging }
        // Peak load among the PRIME cluster's own cores (highest-max-freq CPU policy) — the park guard, so a
        // busy perf core running the game thread can't block parking an idle prime.
        val primePeak = policies.filterNot { it.isGpu }.maxByOrNull { it.selectableMaxFreq }
            ?.cpuIds?.mapNotNull { telemetry.cpuCoreLoadsPercent.getOrNull(it) }?.maxOrNull()
        val decision = autoTune.step(
            policies = policies,
            fps = fps?.fps,
            jankFrames = fps?.jankFrames,
            drawW = drawW,
            cpuTempC = telemetry.cpuTempC,
            gpuTempC = telemetry.gpuTempC,
            // Bottleneck (Bug 6): AGGREGATE cpu load — a single pegged render thread must NOT shield the
            // whole CPU from trimming (that froze it at 3.28 GHz). For the GPU, feed the **raw kgsl busy%**
            // (`gpuBusyPercent`) = saturation at the *current* clock — the correct control signal: a GPU
            // pegged at a PULSE-capped 525 MHz reads ~99 % and is rightly flagged as the limiter so it gets
            // raised. (Clock-weighting it read ~46 %, which HID a maxed-but-capped GPU and let the loop harvest
            // it to a 525 MHz floor while the CPU climbed — the CPU-over-GPU bias seen in the field. The
            // weighted `gpuLoadPercent` stays the overlay/display metric only.) Prime peak is the park guard.
            cpuBusyPercent = telemetry.cpuLoadPercent,
            gpuBusyPercent = telemetry.gpuBusyPercent,
            cpuPeakPercent = primePeak,
            // Busiest single core across ALL clusters — lets the bottleneck detector see a hot game/emulator
            // thread that the 8-core aggregate hides, so it feeds the CPU instead of over-raising the GPU.
            cpuCorePeakPercent = telemetry.cpuCoreLoadsPercent.maxOrNull(),
            // Worst present-to-present interval (the frametime tail) — the margin gate pre-empts a scene-
            // transition stutter while the average rate still reads on-target.
            worstFrameMs = fps?.worstFrameTimeMs,
        )
        if (AUTO_DEBUG) logAutoTdp(policies, telemetry, fps, drawW, decision)
        // Counter the vendor game-boost perflock that re-pins the prime: re-assert its cap EVERY tick (we
        // otherwise only write on TRIM/RAISE, so perfd wins every HOLD stretch). If racing it still loses,
        // the log's mn/mx[prime] stays 3283/4320 and parking is the answer.
        if (!autoTune.isPrimeParked) {
            val prime = policies.filterNot { it.isGpu }.maxByOrNull { it.selectableMaxFreq }
            if (prime != null && (autoTune.caps[prime.id] ?: 100) < 100) {
                AutoTuneController.applyCapsToDevice(listOf(prime), autoTune.caps)
            }
        }
        // Hold the perf/non-prime CPU caps EVERY tick — including while the prime is PARKED (the block above is
        // skipped then). Otherwise the vendor stomps perf's scaling_max back to full and the CPU runs free in
        // GPU-bound/parked scenes (the 72-76°C heat → loud fan). This writes only the non-prime maps and never
        // their scaling_min, so it can't wake the HAL into stomping the perf cap.
        AutoTuneController.applyNonPrimeCpuCaps(policies, autoTune.caps)
        // The SAME daemon reverts the GPU's max_pwrlevel to 0 (uncapped) — proven during media by
        // gcap=1100[0/13] while we cap to 40% (min_pwrlevel=13 holds, only the ceiling is stomped). Re-assert
        // the GPU ceiling every tick too so the cap bites; verify via gcap=<ceil>[<max>/..] tracking our cap.
        policies.firstOrNull { it.isGpu }?.let { gpu ->
            if ((autoTune.caps[gpu.id] ?: 100) < 100) {
                AutoTuneController.applyCapsToDevice(listOf(gpu), autoTune.caps)
            }
        }
        if (AUTO_DEBUG && autoTdpTick == 20) probePerflockNodes(policies) // one-shot, mid-game
        if (autoTdpTick % 40 == 0) {
            val learned = autoTune.powerModel
            serviceScope.launch { container.settingsStorage.persistPowerModel(learned) }
        }
    }

    /**
     * One-shot root probe (PULSE has root via PServer) to expose HOW the vendor pins the prime mid-game —
     * our writes to its `scaling_min` are reverted while the perf cluster's stick, so something re-pins it.
     * Dumps the usual Qualcomm "game boost"/perflock candidate nodes so we can counter or release the source.
     */
    private fun probePerflockNodes(policies: List<CpuPolicyInfo>) {
        val prime = policies.filterNot { it.isGpu }.maxByOrNull { it.selectableMaxFreq }
        val gpuRoot = policies.firstOrNull { it.isGpu }?.policyPath ?: "/sys/class/kgsl/kgsl-3d0"
        val candidates = listOf(
            "/sys/module/msm_performance/parameters/cpu_min_freq",
            "/sys/module/msm_performance/parameters/cpu_max_freq",
            "/sys/module/cpu_boost/parameters/input_boost_freq",
            "/sys/devices/system/cpu/cpu_boost/parameters/input_boost_freq",
            "/sys/devices/system/cpu/cpu_boost/parameters/input_boost_ms",
            "/proc/sys/kernel/sched_boost",
            "/sys/devices/system/cpu/cpu${prime?.cpuIds?.firstOrNull() ?: 6}/cpufreq/scaling_min_freq",
            // GPU-boost candidates (Batch 4): something pins the GPU at ~1050 during media even with the
            // ceiling open. Whichever of these reads high is the media perflock node to counter/lock.
            "$gpuRoot/devfreq/governor",
            "$gpuRoot/devfreq/min_freq",
            "$gpuRoot/devfreq/max_freq",
            "$gpuRoot/default_pwrlevel",
            "$gpuRoot/thermal_pwrlevel",
            "$gpuRoot/idle_timer",
            "$gpuRoot/force_clk_on",
            "/sys/module/msm_performance/parameters/gpu_min_freq",
            "/sys/module/msm_performance/parameters/gpu_max_freq",
        )
        val dump = candidates.joinToString("\n") { path ->
            val v = com.kei.pulse.root.RootSupport.runRootCommand("cat $path 2>/dev/null")
                ?.trim()?.replace("\n", " ")
            "  $path = ${if (v.isNullOrBlank()) "(absent)" else v}"
        }
        android.util.Log.d("PulseAutoTdp", "PERFLOCK-PROBE prime=policy${prime?.id} cpus=${prime?.cpuIds}\n$dump")
    }

    /**
     * One diagnostic line per AutoTDP step: what it decided, the caps it's holding, the live clocks, and
     * — every ~20 steps — a read-back of the actual `scaling_max_freq` so we can confirm the caps are
     * really biting (vs. the loop thinking it trimmed while the hardware ignored the write). `adb logcat
     * -s PulseAutoTdp`.
     */
    private fun logAutoTdp(
        policies: List<CpuPolicyInfo>,
        telemetry: TelemetrySnapshot,
        fps: FpsReader.FpsSample?,
        drawW: Float?,
        decision: AutoTuneController.Decision,
    ) {
        val caps = autoTune.caps
        val capsStr = policies.joinToString(",") { "${it.id}:${caps[it.id] ?: 100}" }
        val curStr = policies.filterNot { it.isGpu }
            .joinToString(",") { "${it.id}:${telemetry.cpuClocksMhz[it.id] ?: -1}" }
        // Every ~10 logged steps, read the real min+max ceilings back. min[] is the key prime diagnostic:
        // if the prime's scaling_min stays high (~3.28 GHz) the vendor re-floored it and the cap can't bite;
        // if it's low, our selective min-lower held and the prime should follow its cap down.
        val mmStr = if (autoTdpLogTick++ % 10 == 0) {
            fun readMhz(path: String) = com.kei.pulse.root.RootSupport
                .runRootCommand("cat $path")?.trim()?.toIntOrNull()?.div(1000) ?: -1
            " mn/mx[" + policies.filterNot { it.isGpu }.joinToString(",") { p ->
                "${p.id}:${readMhz("${p.policyPath}/scaling_min_freq")}/${readMhz(p.scalingMaxPath)}"
            } + "]"
        } else {
            ""
        }
        android.util.Log.d(
            "PulseAutoTdp",
            "tgt=${autoTune.targetFps} fps=${fps?.fps?.let { String.format("%.1f", it) } ?: "-"} " +
                "jank=${fps?.jankFrames ?: 0} tail=${fps?.worstFrameTimeMs?.let { String.format("%.0f", it) } ?: "-"}ms " +
                "act=${decision.action} bn=${autoTune.bottleneckLabel} " +
                "cpuB=${telemetry.cpuLoadPercent ?: -1} cpuPk=${telemetry.cpuCoreLoadsPercent.maxOrNull() ?: -1} " +
                "io=${telemetry.cpuIowaitPercent ?: -1} " +
                "gpuB=${telemetry.gpuBusyPercent ?: -1} gpuL=${telemetry.gpuLoadPercent ?: -1} " +
                "capped=${autoTune.stalledDomainCount} " +
                "prk=${if (autoTune.isPrimeParked) 1 else 0} stl=${if (autoTune.isPrimeWalled) 1 else 0} " +
                "draw=${drawW?.let { String.format("%.2f", it) } ?: "-"}W " +
                "cT=${telemetry.cpuTempC} gT=${telemetry.gpuTempC} " +
                "caps%[$capsStr] curMHz[$curStr]$mmStr gpu=${telemetry.gpuMhz} " +
                "gcap=${telemetry.gpuCeilingMhz ?: -1}[${telemetry.gpuMaxLevel ?: -1}/${telemetry.gpuMinLevel ?: -1}] " +
                "lrn=${autoTune.learnedPercent()}",
        )
    }

    // ── Overlay session timer (accumulates foreground play time; resumes on return) ──
    private fun startOrResumeSession(pkg: String) {
        if (sessionPackage != pkg) {
            sessionPackage = pkg
            sessionAccumulatedMs = 0L
        }
        sessionResumeAt = System.currentTimeMillis()
    }

    private fun pauseSession() {
        if (sessionResumeAt > 0L) {
            sessionAccumulatedMs += System.currentTimeMillis() - sessionResumeAt
            sessionResumeAt = 0L
        }
    }

    private fun sessionElapsedMs(): Long =
        sessionAccumulatedMs + if (sessionResumeAt > 0L) System.currentTimeMillis() - sessionResumeAt else 0L

    /**
     * Overlay power readout: on battery, an EMA-smoothed measured system draw (kills the per-sample
     * 0.1 W flicker); while charging current_now is charger current, not draw, so fall back to a
     * load-scaled estimate at the current ceilings (flagged so the overlay shows ⚡).
     */
    private fun overlayPower(t: TelemetrySnapshot): Pair<Float?, Boolean> {
        if (t.isDischarging) {
            overlayChargeEma = null
            val w = t.batteryDrawW ?: return overlayDrawEma to false
            val ema = overlayDrawEma?.let { it * 0.7f + w * 0.3f } ?: w
            overlayDrawEma = ema
            return ema to false // false = on battery (system draw)
        }
        // Plugged in: batteryDrawW is now |current_now| × voltage_now = the charge rate INTO the battery
        // (the kernel reports the charge current while charging). Show that, smoothed; true ⇒ overlay shows ⚡.
        overlayDrawEma = null
        val w = t.batteryDrawW ?: return overlayChargeEma to true
        val ema = overlayChargeEma?.let { it * 0.7f + w * 0.3f } ?: w
        overlayChargeEma = ema
        return ema to true
    }

    private fun hideOverlay() {
        overlay.hide()
        overlayDrawEma = null
        overlayChargeEma = null
        overlayMinutesEma = null
        overlayMinutesDischarging = null
        overlayProfileLabel = ""
        // Policies are kept (stable, and AutoTDP may still need them); FPS is stopped by the caller
        // when the game is truly gone. The session timer is NOT reset here — it pauses on leaving
        // the game and resumes when the same game returns (see startOrResumeSession / pauseSession).
    }

    /**
     * While a bound app plays on battery, track its real draw: the highest sample (PK display)
     * and a smoothed average (EMA, ~30s time constant) that the battery-life estimate is based
     * on. The average persists across sessions, so it keeps refining the more the app is played.
     * Persisted on meaningful peak jumps or every ~30s; a final write happens on leaving the app.
     */
    private suspend fun trackDrawForBoundApp() {
        val config = boundConfig ?: return
        // Reuse the telemetry tick() already read this tick; only hit the battery nodes directly when tick()
        // didn't read (overlay + AutoTDP both off) — identical values either way (same draw formula).
        val cached = tickTelemetry
        val watts: Float?
        val discharging: Boolean
        if (cached != null) {
            watts = cached.batteryDrawW
            discharging = cached.isDischarging
        } else {
            val snap = com.kei.pulse.data.BatteryReader.drawSnapshot()
            watts = snap.first
            discharging = snap.second
        }
        if (!discharging || watts == null) return
        // Only fold the sample in while the app is doing real work — idle/menu/paused draw is frozen out so
        // the average (and the battery-life estimate built on it) reflects actual play. Peak is rise-limited
        // inside the helper so a spiky current_now reading can't bake in a false max.
        val active = lastActiveLoadPercent >= MIN_ACTIVE_LOAD_PERCENT
        val updated = config.foldMeasuredDraw(watts, active)
        if (updated == config) return // idle (or no change) — nothing to record this tick
        boundConfig = updated
        ticksSincePersist++
        if (updated.measuredPeakW > config.measuredPeakW + 0.2f || ticksSincePersist >= 20) {
            persistMeasuredDraw()
        }
    }

    private suspend fun persistMeasuredDraw() {
        val config = boundConfig ?: return
        if (config.measuredPeakW <= 0f) return
        ticksSincePersist = 0
        container.perAppConfigStorage.updateMeasuredDraw(
            packageName = config.packageName,
            peakW = config.measuredPeakW,
            avgW = config.measuredAvgW,
        )
    }

    private fun currentForegroundPackage(): String? {
        val usageStats = getSystemService<UsageStatsManager>() ?: return null
        val now = System.currentTimeMillis()
        val events = usageStats.queryEvents(now - EVENT_WINDOW_MS, now)
        var latest: String? = null
        val event = UsageEvents.Event()
        while (events.hasNextEvent()) {
            events.getNextEvent(event)
            if (event.eventType == UsageEvents.Event.ACTIVITY_RESUMED) {
                latest = event.packageName
            }
        }
        return latest
    }

    private suspend fun handleForegroundChange(foreground: String) {
        transitionMutex.withLock {
            val config = container.perAppConfigStorage.configs.first()
                .firstOrNull { it.packageName == foreground }
            // Global default: AutoTDP also engages for any foreground app (except PULSE + the home
            // screen) when the user turned it on — games, emulators, and media alike.
            val autoDefault = config == null &&
                container.settingsStorage.settings.first().autoTdpDefaultEnabled &&
                isGlobalAutoTdpTarget(foreground)
            val engages = config != null || autoDefault
            when {
                engages && boundPackage != foreground -> {
                    // Release any prior AutoTDP session first (e.g. switching directly between apps).
                    stopAutoTdp()
                    clearBoundReassert() // drop any prior Custom/tier cap-hold + its locks before re-binding
                    val firstEntry = boundPackage == null
                    when {
                        config != null && PerAppConfig.isAuto(config.profileBinding) ->
                            startAutoTdp(foreground, config)
                        config != null -> {
                            // Snapshot only when entering from unbound; switching between two bound
                            // apps keeps the original pre-launch snapshot.
                            if (firstEntry) snapshotCurrentState(config)
                            applyConfig(config)
                            captureBoundReassertCaps() // Bug 9: remember the caps so we can hold them each tick
                        }
                        else -> startAutoTdp(foreground, null) // global default
                    }
                    boundPackage = foreground
                    boundConfig = config
                    startOrResumeSession(foreground)
                }
                !engages && boundPackage != null -> {
                    // Left the bound app for a neutral one (PULSE itself or the home screen), so the
                    // tuner always shows (and edits) the general OS state, never a game's.
                    val wasExplicit = boundConfig != null
                    persistMeasuredDraw() // final draw stats write for the session
                    pauseSession() // accrue play time; resumes if the user returns to this game
                    stopAutoTdp() // reopen clocks before restoring the pre-game snapshot
                    clearBoundReassert() // Bug 9: stop holding caps + hand their locks back to stock before restore
                    restoreSnapshot(notify = wasExplicit) // stay quiet for global-default switches
                    fpsReader.stop()
                    boundPackage = null
                    boundConfig = null
                    hideOverlay()
                }
            }
        }
    }

    private suspend fun snapshotCurrentState(config: PerAppConfig) {
        val settings = container.settingsStorage.settings.first()
        container.perAppConfigStorage.persistRestoreState(
            PerAppRestoreState(
                values = container.repository.readCurrentValues(),
                appliedDisplayProfileId = ProfileStateResolver.MANUAL_PROFILE_ID,
                activeTierLabel = settings.activeTierLabel,
                fanMode = if (config.fanMode != null) fanController.readMode() else null,
                refreshRateHz = if (config.refreshRateHz != null) refreshRateController.readPeak() else null,
                // Tiers/Custom re-assert a governor on apply, so capture it to restore on exit.
                governor = ensurePolicies().firstOrNull { !it.isGpu }?.let { governorController.readGovernor(it) },
            ),
        )
    }

    private suspend fun applyConfig(config: PerAppConfig) {
        val parts = mutableListOf<String>()
        val tier = PerAppConfig.tierFromBinding(config.profileBinding)
        when {
            tier == PowerTier.CUSTOM -> {
                // Custom = the user's saved Custom setup, same as the Custom tier in-app.
                container.repository.restoreCustomValues().onSuccess {
                    container.settingsStorage.persistActiveTierLabel(tier.label)
                    // Match in-app Custom: re-assert the governor the user saved for Custom.
                    container.settingsStorage.customTuning.first().governorLabel?.let { label ->
                        GovernorController.OPTIONS.firstOrNull { it.label == label }?.let { option ->
                            val policies = container.repository.observeState().first().policies
                            governorController.setGovernor(policies, option)
                        }
                    }
                    parts += tier.label
                }
            }
            tier != null -> {
                container.repository.applyTier(tier).onSuccess {
                    container.settingsStorage.persistActiveTierLabel(tier.label)
                    parts += tier.label
                }
            }
            config.profileBinding != null ->
                container.repository.applyDisplayProfileById(config.profileBinding).onSuccess {
                    parts += container.repository.observeState().first().displayProfiles
                        .firstOrNull { it.id == config.profileBinding }?.name ?: "Saved profile"
                }
        }
        config.fanMode?.let { mode ->
            fanController.setMode(mode)
            parts += "Fan ${FanController.labelFor(mode)}"
        }
        config.refreshRateHz?.let { hz ->
            refreshRateController.setRate(hz)
            parts += "${hz}Hz"
        }
        if (parts.isNotEmpty() && container.perAppConfigStorage.switchNotices.first()) {
            val appName = config.appLabel.ifBlank { config.packageName }
            val summary = "$appName: ${parts.joinToString(" · ")}"
            showToast("PULSE · $summary")
            updateNotification(summary)
        }
    }

    /**
     * Master OFF / clean-uninstall: hand every managed control back to manufacturer stock so the device runs
     * exactly as the system would — uncapped clocks, Smart fan (the confirmed Odin factory default), and the
     * captured pre-PULSE governor/refresh restored. Drops AutoTDP/per-app and the overlay. Idempotent, so a
     * service that gets started while the master is off can safely run it again before stopping.
     */
    private suspend fun revertToStock() {
        if (autoTdpPackage != null) stopAutoTdp() // drop the Game-Mode fps cap + reopen the clocks
        clearBoundReassert() // Bug 9: release any held Custom/tier cap locks (incl. the prime scaling_min) to stock
        // Uncap the CPU/GPU clocks to the stock profile (full freq + stock writability handed back to the HAL).
        container.repository.applyDisplayProfileById(ProfileStateResolver.STOCK_PROFILE_ID)
        fanController.setMode(FanController.SMART) // Smart = the confirmed factory-default fan mode
        container.settingsStorage.persistManagedFanMode(null) // PULSE releases the fan — the system Fan tile owns it again
        // Restore the durable settings that survive a reboot (fan handled above) to the user's pre-PULSE values.
        container.perAppConfigStorage.restoreState.first()?.let { restore ->
            restore.refreshRateHz?.let { refreshRateController.setRate(it) }
            restore.governor?.let { governorController.setGovernorRaw(ensurePolicies(), it) }
        }
        container.perAppConfigStorage.persistRestoreState(null)
        boundPackage = null
        boundConfig = null
        autoTdpPackage = null
        overlay.hide()
    }

    private suspend fun restoreSnapshot(notify: Boolean = true) {
        val restore = container.perAppConfigStorage.restoreState.first() ?: return
        if (restore.values.isNotEmpty()) {
            container.repository.applyRawValues(restore.values, restore.appliedDisplayProfileId)
        }
        restore.activeTierLabel?.let { container.settingsStorage.persistActiveTierLabel(it) }
        restore.fanMode?.let { fanController.setMode(it) }
        restore.refreshRateHz?.let { refreshRateController.setRate(it) }
        // Restore the CPU governor AutoTDP replaced with Balanced (captured pre-game).
        restore.governor?.let { governorController.setGovernorRaw(ensurePolicies(), it) }
        container.perAppConfigStorage.persistRestoreState(null)
        if (notify && container.perAppConfigStorage.switchNotices.first()) {
            showToast("PULSE · previous settings restored")
            updateNotification("Previous settings restored")
        }
    }

    private fun showToast(message: String) {
        Handler(Looper.getMainLooper()).post {
            Toast.makeText(applicationContext, message, Toast.LENGTH_SHORT).show()
        }
    }

    private fun updateNotification(text: String) {
        getSystemService<NotificationManager>()?.notify(NOTIFICATION_ID, buildNotification(text))
    }

    private fun createNotificationChannel() {
        val channel = NotificationChannel(
            CHANNEL_ID,
            "Per-app profile monitoring",
            NotificationManager.IMPORTANCE_LOW,
        ).apply {
            setShowBadge(false)
            description = "Keeps PULSE ready to switch profiles when configured apps launch."
        }
        getSystemService<NotificationManager>()?.createNotificationChannel(channel)
    }

    private fun buildNotification(
        contentText: String = "Watching for configured apps to apply their profiles.",
    ) =
        NotificationCompat.Builder(this, CHANNEL_ID)
            .setSmallIcon(R.drawable.ic_tile_underclock)
            .setContentTitle("PULSE per-app profiles")
            .setContentText(contentText)
            .setOngoing(true)
            .setShowWhen(false)
            .setPriority(NotificationCompat.PRIORITY_LOW)
            .setContentIntent(
                PendingIntent.getActivity(
                    this,
                    0,
                    Intent(this, MainActivity::class.java),
                    PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT,
                ),
            )
            // In-game entry point to (un)lock the overlay for repositioning — works from the
            // notification shade, which is reachable over full-screen games.
            .addAction(
                NotificationCompat.Action.Builder(
                    R.drawable.ic_tile_underclock,
                    "Move overlay",
                    PendingIntent.getService(
                        this,
                        1,
                        Intent(this, ForegroundAppMonitorService::class.java)
                            .setAction(ACTION_TOGGLE_OVERLAY_LOCK),
                        PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT,
                    ),
                ).build(),
            )
            .build()

    companion object {
        private const val CHANNEL_ID = "per_app_profile_monitoring"
        private const val NOTIFICATION_ID = 32
        // Diagnostic AutoTDP logging (adb logcat -s PulseAutoTdp) — on while verifying on-device.
        private const val AUTO_DEBUG = true
        private const val POLL_INTERVAL_MS = 1_000L
        private const val FAN_SLEW_MS = 300L // smooth-ramp cadence: small steps → smooth & quiet
        private const val FAN_RECHECK_MS = 120L // duty re-check cadence: catch the vendor's game-transition
        // 50% reset fast enough that the re-pin is inaudible (decoupled from the slower ramp above)
        private const val EVENT_WINDOW_MS = 10_000L
        // Per-app draw is only counted above this load — idle/menu (≈1-2%) is frozen out so it can't poison
        // the average; real play (CPU/GPU load ~15-50%) clears it easily.
        private const val MIN_ACTIVE_LOAD_PERCENT = 12
        const val ACTION_TOGGLE_OVERLAY_LOCK = "com.kei.pulse.action.TOGGLE_OVERLAY_LOCK"

        /**
         * True while PULSE's own UI is on screen (set by MainActivity onResume/onPause). The OSD must never draw
         * over PULSE itself — but the usage-events foreground probe reports the LATEST `ACTIVITY_RESUMED`, which
         * becomes the IME/keyboard package the moment a text field is focused in our settings, so PULSE no
         * longer reads as "foreground" and the OSD leaked over our own UI. This lifecycle flag is authoritative:
         * if our Activity is resumed, treat the foreground as neutral regardless of any transient on top of us.
         */
        @Volatile var uiInForeground = false

        fun hasUsageAccess(context: Context): Boolean {
            val appOps = context.getSystemService<AppOpsManager>() ?: return false
            val mode = appOps.unsafeCheckOpNoThrow(
                AppOpsManager.OPSTR_GET_USAGE_STATS,
                Process.myUid(),
                context.packageName,
            )
            return mode == AppOpsManager.MODE_ALLOWED
        }

        fun start(context: Context) {
            ContextCompat.startForegroundService(
                context,
                Intent(context, ForegroundAppMonitorService::class.java),
            )
        }

        fun stop(context: Context) {
            context.stopService(Intent(context, ForegroundAppMonitorService::class.java))
        }
    }
}
