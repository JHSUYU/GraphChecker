package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.HeapWatch;

/**
 * The entry point every {@code execute.sh} launches: the workload session
 * opens before the test method and lasts the JVM, so an exported expression
 * can outlive its producer's thread, and every exit path ends in
 * {@link #exit}.  The method itself is run by {@link JUnitLifecycle}.  A
 * replay draws its RSA key pairs from {@link ReplayKeys}.
 */
public final class JUnitMethodRunner {
    private static final Object ENDING = new Object();
    /** Guarded by {@link #ENDING}: whether some thread ends the run. */
    private static boolean ending;
    private static volatile String testClass = "";

    private JUnitMethodRunner() {
    }

    public static void main(String[] args) {
        if (RuntimeTraceMode.configured() == RuntimeTraceMode.REPLAY_CONTEXT) {
            ReplayKeys.install();
            HeapWatch.start();
        }
        String refusedOpen = ConcolicRegionRuntime.openWorkloadSession();
        if (!refusedOpen.isEmpty()) {
            // Without a session every cross-thread expression is lost.
            // Nothing has run yet, so throwing is enough.
            throw new IllegalStateException(refusedOpen);
        }
        // A focused replay that stands still ends by name, not at its bound.
        ConcolicResultPublisher.watchProgress();
        int status = 0;
        Throwable ended = null;
        testClass = args == null || args.length == 0 ? "" : args[0];
        try {
            JUnitLifecycle.run(args);
        } catch (Throwable failure) {
            // The replay's outcome is read from stderr.
            EngineConsole.trace(failure);
            status = 1;
            ended = failure;
        }
        // The workload ended by itself, whatever it threw: a replay's world
        // may be refuted by it (FocusedReplay#refuted).
        FocusedReplay.workloadEnded(ended, testClass);
        exit(status);
    }

    /**
     * The one end of every workload JVM -- the recording, a focused or a
     * CONFIRM replay, a native reproduction -- whether its workload ended
     * ({@link #main}) or an early end came first ({@code
     * ConcolicResultPublisher#conclude}, {@code RecordingPlant#end}).
     * THE RUN ENDS BEFORE ITS JVM DOES: admission ends, what is live settles
     * (the publications first, each after the read-out pages queued before
     * it: closing under a pending one is refused), the run totals close the
     * session's rows and then state the replay's verdict to its worker --
     * nothing is published after them -- the schedule states how its order
     * went, the recording's trace is flushed and closed, and the JVM HALTS.
     * 0 when the method returned, 1 when it, a publication or the close
     * failed.
     *
     * <p>A halt, not {@code System.exit}: nothing runs after the end.  A
     * cluster's own shutdown hook may never return: PV7-adhoc-38, 35 decided
     * replays (stalled after their flip, or refused) whose verdicts were
     * written, then hung in Jetty's hook while the test thread retried
     * against the stopped servers, until the worker killed each at
     * replay_timeout_s and recorded REPLAY_BOUNDED.  Every row the end owes
     * is written by the steps above, so the JVM has no shutdown hook of the
     * engine's; and its VM session is freed with it.</p>
     *
     * <p>A JVM told to end before its run did -- a signal (the worker's
     * bound) or the workload's own {@code System.exit} -- states nothing: a
     * cluster its shutdown stopped is no run that ended by itself, so a
     * verdict the worker reads is only ever a decided end's
     * ({@code run_engine.sh campaign_obligation_replay}).</p>
     *
     * <p>ONE END: the first caller ends the run and a later one waits for its
     * halt.  SOLR-18413 r8: the declared update's throw failed the test, and
     * its witness stop and the failed test both ended the run; the witness
     * began the run totals, the test found them begun, closed the session
     * and exited while the verdict was still being written.</p>
     */
    static void exit(int status) {
        synchronized (ENDING) {
            if (ending) standUntilHalt();
            ending = true;
        }
        if (shutdownBegun()) {
            EngineConsole.println("Causynth: this JVM was told to end (a"
                    + " signal, or the workload's System.exit) before its run"
                    + " ended; the run states nothing");
            halt(status);
        }
        markEnding();
        int code = status;
        ConcolicRegionRuntime.endAdmission();
        try {
            ConcolicResultPublisher.awaitSelectedResultPublications();
        } catch (Throwable publicationFailure) {
            EngineConsole.trace(publicationFailure);
            code = 1;
        }
        try {
            ConcolicResultPublisher.publishRunTotals();
        } catch (Throwable closeFailure) {
            // A failure while unwinding must not skip the halt below.
            EngineConsole.trace(closeFailure);
            code = 1;
        }
        try {
            ScheduleLog.stateProgress();
            CausynthTraceRecorder.closeTrace();
        } catch (Throwable endFailure) {
            EngineConsole.trace(endFailure);
            code = 1;
        }
        halt(code);
    }

    static void endAtWindowClose() {
        Throwable failed = JUnitLifecycle.methodFailure();
        if (failed != null) EngineConsole.trace(failed);
        FocusedReplay.windowClosed(failed, testClass);
        EngineConsole.println("Causynth " + java.time.Instant.now()
                + ": the replay ends at its window's close: its test is"
                + " over, and its teardown does not run");
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        new Thread(root, () -> exit(0), "causynth-window-close").start();
        synchronized (ENDING) {
            standUntilHalt();
        }
    }

    static final String ENDING_FILE = "workload_ending";

    private static void markEnding() {
        String worker = FocusedReplay.workerDir();
        if (worker.isEmpty()) return;
        try {
            java.nio.file.Files.write(java.nio.file.Paths.get(worker,
                    ENDING_FILE), new byte[0]);
        } catch (java.io.IOException | RuntimeException unwritten) {
            EngineConsole.println("Causynth could not mark its end in "
                    + worker + ": " + unwritten);
        }
    }

    private static void standUntilHalt() {
        while (true) {
            try {
                ENDING.wait();
            } catch (InterruptedException ignored) {
                // The first end halts the JVM; nothing else does.
            }
        }
    }

    /**
     * Whether this JVM's shutdown has begun.  The JDK takes its hook list
     * away before it starts any hook, and refuses a new one from then on,
     * so the answer is known before any cluster's hook has run.
     */
    static boolean shutdownBegun() {
        Thread probe = new Thread("causynth-shutdown-probe");
        try {
            Runtime.getRuntime().addShutdownHook(probe);
            Runtime.getRuntime().removeShutdownHook(probe);
            return false;
        } catch (IllegalStateException shuttingDown) {
            return true;
        } catch (SecurityException unaskable) {
            // A workload's security manager that forbids hooks: no signal
            // is known to have come.
            return false;
        }
    }

    /** The replay log's last engine line, as a UTC instant (a workload may
     *  randomize the JVM's zone), then the halt. */
    private static void halt(int code) {
        EngineConsole.println("Causynth " + java.time.Instant.now()
                + ": the run's end halts its JVM (status " + code + ")");
        System.out.flush();
        System.err.flush();
        Runtime.getRuntime().halt(code);
    }
}
