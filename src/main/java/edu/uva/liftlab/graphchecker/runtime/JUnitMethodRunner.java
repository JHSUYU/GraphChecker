package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.HeapWatch;

public final class JUnitMethodRunner {
    private static final Object ENDING = new Object();
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
            throw new IllegalStateException(refusedOpen);
        }
        ConcolicResultPublisher.watchProgress();
        int status = 0;
        Throwable ended = null;
        testClass = args == null || args.length == 0 ? "" : args[0];
        try {
            JUnitLifecycle.run(args);
        } catch (Throwable failure) {
            EngineConsole.trace(failure);
            status = 1;
            ended = failure;
        }
        FocusedReplay.workloadEnded(ended, testClass);
        exit(status);
    }

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
            }
        }
    }

    static boolean shutdownBegun() {
        Thread probe = new Thread("causynth-shutdown-probe");
        try {
            Runtime.getRuntime().addShutdownHook(probe);
            Runtime.getRuntime().removeShutdownHook(probe);
            return false;
        } catch (IllegalStateException shuttingDown) {
            return true;
        } catch (SecurityException unaskable) {
            return false;
        }
    }

    private static void halt(int code) {
        EngineConsole.println("Causynth " + java.time.Instant.now()
                + ": the run's end halts its JVM (status " + code + ")");
        System.out.flush();
        System.err.flush();
        Runtime.getRuntime().halt(code);
    }
}
