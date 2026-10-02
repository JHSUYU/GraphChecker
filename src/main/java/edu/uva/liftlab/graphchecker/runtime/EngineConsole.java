package edu.uva.liftlab.graphchecker.runtime;

import java.io.FileDescriptor;
import java.io.FileOutputStream;
import java.io.PrintStream;

/**
 * THE ENGINE'S CONSOLE in a workload JVM: the standard error the JVM started
 * with, whatever {@code System.err} the workload installed since.  A test may
 * capture {@code System.err} and assert on what a tool printed there
 * ({@code TestDFSAdminWithHA#verifyUpgradeQueryOutput}); a line of the
 * engine's in it is a run the recording never made: sweep a40h2's
 * FSImage-851 seed replay failed that assertion on the schedule's own
 * {@code Causynth schedule: ...} lines, before the declared occurrence ran.
 * Nothing the engine prints is the workload's to read, and the replay log --
 * where its stage reads the workload's terminating exception -- gets every
 * line, redirected or not.
 */
final class EngineConsole {
    private static final PrintStream ERR = new PrintStream(
            new FileOutputStream(FileDescriptor.err), true);

    private EngineConsole() {
    }

    /** One line to the engine's console. */
    static void println(String line) {
        ERR.println(line);
    }

    /** A throwable's stack to the engine's console. */
    static void trace(Throwable thrown) {
        thrown.printStackTrace(ERR);
    }
}
