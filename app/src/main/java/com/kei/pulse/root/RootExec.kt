package com.kei.pulse.root

import android.annotation.SuppressLint
import android.os.IBinder
import android.os.Parcel
import java.nio.charset.Charset
import java.util.concurrent.TimeUnit

@SuppressLint("DiscouragedPrivateApi", "PrivateApi")
class RootExec {

    private val binder: IBinder? = findPServerBinder()

    val pServerAvailable: Boolean
        get() = binder != null

    val suAvailable: Boolean = checkSuAvailable()

    fun executeAsRoot(cmd: String): Result<String?> {
        return when {
            // Personal/root build: prefer Magisk or KernelSU when available.
            suAvailable -> executeWithSu(cmd)

            // Stock AYN firmware fallback.
            binder != null -> executeWithPServer(cmd)

            else -> Result.failure(
                IllegalStateException(
                    "Neither root access nor PServer is available",
                ),
            )
        }
    }

    private fun findPServerBinder(): IBinder? {
        return runCatching {
            val serviceManager = Class.forName("android.os.ServiceManager")
            val getService = serviceManager.getDeclaredMethod(
                "getService",
                String::class.java,
            )

            getService.invoke(
                serviceManager,
                "PServerBinder",
            ) as? IBinder
        }.getOrNull()
    }

    private fun executeWithPServer(cmd: String): Result<String?> {
        val activeBinder = binder
            ?: return Result.failure(
                IllegalStateException("PServer is not available"),
            )

        val data = Parcel.obtain()
        val reply = Parcel.obtain()

        return try {
            data.writeStringArray(arrayOf(cmd, "1"))

            val transactionSucceeded = activeBinder.transact(
                0,
                data,
                reply,
                0,
            )

            if (!transactionSucceeded) {
                error("PServer transaction failed")
            }

            Result.success(decodeReply(reply))
        } catch (throwable: Throwable) {
            Result.failure(throwable)
        } finally {
            data.recycle()
            reply.recycle()
        }
    }

    private fun executeWithSu(cmd: String): Result<String?> {
        return runCatching {
            val process = ProcessBuilder(
                "su",
                "-c",
                cmd,
            )
                .redirectErrorStream(true)
                .start()

            if (!process.waitFor(COMMAND_TIMEOUT_SECONDS, TimeUnit.SECONDS)) {
                process.destroyForcibly()
                process.waitFor(1, TimeUnit.SECONDS)
                error("Root command timed out")
            }

            val output = process.inputStream
                .bufferedReader()
                .use { reader -> reader.readText() }
                .trim()

            val exitCode = process.exitValue()
            if (exitCode != 0) {
                error(
                    "Root command failed with exit code $exitCode" +
                        output.takeIf { it.isNotEmpty() }
                            ?.let { ": $it" }
                            .orEmpty(),
                )
            }

            output.ifEmpty { null }
        }
    }

    private fun checkSuAvailable(): Boolean {
        return runCatching {
            val process = ProcessBuilder(
                "su",
                "-c",
                "id",
            )
                .redirectErrorStream(true)
                .start()

            if (!process.waitFor(SU_CHECK_TIMEOUT_SECONDS, TimeUnit.SECONDS)) {
                process.destroyForcibly()
                process.waitFor(1, TimeUnit.SECONDS)
                return@runCatching false
            }

            val output = process.inputStream
                .bufferedReader()
                .use { reader -> reader.readText() }

            process.exitValue() == 0 &&
                UID_ZERO_PATTERN.containsMatchIn(output)
        }.getOrDefault(false)
    }

    private fun decodeReply(reply: Parcel): String? {
        return reply.createByteArray()
            ?.toString(Charset.defaultCharset())
            ?.trim()
            ?.let { value ->
                value.takeUnless { it == "null" }
            }
    }

    private companion object {
        const val COMMAND_TIMEOUT_SECONDS = 10L
        const val SU_CHECK_TIMEOUT_SECONDS = 5L

        val UID_ZERO_PATTERN = Regex(
            pattern = """\buid=0(?:\(|\s|$)""",
        )
    }
}