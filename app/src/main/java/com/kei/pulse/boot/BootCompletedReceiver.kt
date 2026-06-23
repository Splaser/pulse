package com.kei.pulse.boot

import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import com.kei.pulse.AppContainer
import com.kei.pulse.appwatch.ForegroundAppMonitorService
import com.kei.pulse.model.RgbMode
import com.kei.pulse.sleep.SleepProfileMonitorService
import com.kei.pulse.tile.QuickSettingsTileRefresher
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.launch

class BootCompletedReceiver : BroadcastReceiver() {

    override fun onReceive(context: Context, intent: Intent?) {
        when (intent?.action) {
            Intent.ACTION_BOOT_COMPLETED -> handleBootCompleted(context)
            Intent.ACTION_MY_PACKAGE_REPLACED -> QuickSettingsTileRefresher.requestUpdate(context)
        }
    }

    private fun handleBootCompleted(context: Context) {
        val pendingResult = goAsync()
        CoroutineScope(Dispatchers.IO).launch {
            try {
                val container = AppContainer(context)
                val settings = container.settingsStorage.settings.first()
                if (settings.sleepProfileEnabled) {
                    SleepProfileMonitorService.start(context)
                }
                // Restart the watcher for ANY feature that needs it (mirrors the pollLoop keep-alive set), not
                // just per-app — else an RGB-only / global-AutoTDP / overlay / managed-fan setup silently dies
                // across a reboot until the app is reopened.
                val needsWatcher = container.perAppConfigStorage.enabled.first() ||
                    container.perAppConfigStorage.configs.first().isNotEmpty() ||
                    settings.autoTdpDefaultEnabled ||
                    settings.overlayEnabled ||
                    settings.rgbMode != RgbMode.OFF ||
                    settings.managedFanMode != null
                if (needsWatcher && ForegroundAppMonitorService.hasUsageAccess(context)) {
                    ForegroundAppMonitorService.start(context)
                }
                if (!settings.applyLastProfileOnBoot) {
                    return@launch
                }
                container.repository.applyPersistedLastValuesOnBoot()
                QuickSettingsTileRefresher.requestUpdate(context)
            } finally {
                pendingResult.finish()
            }
        }
    }
}
