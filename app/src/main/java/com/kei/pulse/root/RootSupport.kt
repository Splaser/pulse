package com.kei.pulse.root

import android.content.Context
import java.io.File
import java.util.concurrent.locks.ReentrantLock
import kotlin.concurrent.withLock

object RootSupport {

    // Process-wide serialization of PServer access. The binder cannot service overlapping
    // transacts reliably, and several callers (per-app watcher apply, telemetry poll, tile,
    // sleep monitor) hit it concurrently. Every PServer path — cat() reads and the
    // runGeneratedScript apply pipeline — funnels through runRootCommand, so locking here
    // serializes all of them at command granularity. Each command is short and all callers
    // run on Dispatchers.IO, so a blocking lock is fine. runGeneratedScript does not lock
    // itself, so there is no re-entrancy.
    private val pServerLock = ReentrantLock()

    fun runRootCommand(command: String): String? {
        return pServerLock.withLock {
            RootExec().executeAsRoot(command).getOrNull()
        }
    }

    fun runGeneratedScript(
        context: Context,
        scriptName: String,
        scriptContents: String,
    ): String? {
        val scriptDir = File(context.filesDir, "root-scripts")
        if (!scriptDir.exists()) {
            scriptDir.mkdirs()
        }

        val scriptFile = File(scriptDir, scriptName)
        scriptFile.writeText(scriptContents)
        scriptFile.setReadable(true, false)
        scriptFile.setExecutable(true, false)

        val command = "sh ${scriptFile.absolutePath}"
        return runRootCommand(command)
    }
}
