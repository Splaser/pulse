package com.kei.pulse.root

import android.content.Context
import java.io.File
import java.util.concurrent.locks.ReentrantLock
import kotlin.concurrent.withLock

object RootSupport {

    // Keep one executor for the lifetime of the app process.
    // This avoids repeatedly probing PServer and repeatedly running "su -c id".
    private val rootExec: RootExec by lazy {
        RootExec()
    }

    // Serialize privileged commands across PServer and su backends.
    //
    // PServer cannot reliably service overlapping Binder transactions.
    // The lock also prevents concurrent profile scripts from interleaving sysfs
    // writes when the su backend is active.
    private val commandLock = ReentrantLock()

    val isAvailable: Boolean
        get() = rootExec.pServerAvailable || rootExec.suAvailable

    val backendName: String
        get() = when {
            rootExec.suAvailable -> "Root (su)"
            rootExec.pServerAvailable -> "PServer"
            else -> "Unavailable"
        }

    fun runRootCommand(command: String): String? {
        return commandLock.withLock {
            rootExec.executeAsRoot(command).getOrNull()
        }
    }

    fun runGeneratedScript(
        context: Context,
        scriptName: String,
        scriptContents: String,
    ): String? {
        val scriptDir = File(context.filesDir, "root-scripts")

        if (!scriptDir.exists() && !scriptDir.mkdirs()) {
            return null
        }

        val scriptFile = File(scriptDir, scriptName)

        scriptFile.writeText(scriptContents)
        scriptFile.setReadable(true, false)
        scriptFile.setExecutable(true, false)

        val escapedPath = shellQuote(scriptFile.absolutePath)
        return runRootCommand("sh $escapedPath")
    }

    private fun shellQuote(value: String): String {
        return "'" + value.replace("'", "'\\''") + "'"
    }
}