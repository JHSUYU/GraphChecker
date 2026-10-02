package edu.uva.liftlab.graphchecker.runtime;

/**
 * The entry point every {@code execute.sh} launches: the workload session
 * opens before the test method and closes after it on every exit path, so
 * an exported expression can outlive its producer's thread.  The method
 * itself is run by {@link JUnitLifecycle}.  A replay draws its RSA key pairs
 * from {@link ReplayKeys}.
 */
public final class JUnitMethodRunner {
    private static final Object ENDING = new Object();
    /** Guarded by {@link #ENDING}: whether some thread ends the run. */
    private static boolean ending;

    private JUnitMethodRunner() {
    }

    public static void main(String[] args) {
        if (RuntimeTraceMode.configured() == RuntimeTraceMode.REPLAY_CONTEXT) {
            ReplayKeys.install();
        }
        String refusedOpen = ConcolicRegionRuntime.openWorkloadSession();
        if (!refusedOpen.isEmpty()) {
            // Without a session every cross-thread expression is lost.
            // Nothing has run yet, so throwing is enough.
            throw new IllegalStateException(refusedOpen);
        }
        int status = 0;
        try {
            JUnitLifecycle.run(args);
        } catch (Throwable failure) {
            // The replay's outcome is read from stderr.
            EngineConsole.trace(failure);
            status = 1;
        }
        exit(status);
    }

    /**
     * The one end of a replay, the workload's or its witness's
     * ({@code ConcolicResultPublisher#concludeAtWitness}).  THE RUN ENDS
     * BEFORE ITS SESSION DOES: admission ends, what is live settles (the
     * publications first: closing under a pending one is refused), the run
     * totals close the rows -- nothing is published after them -- and only
     * then the VM session closes.  Non-daemon cluster threads outlive the
     * test, so the exit is explicit.  0 when the method returned, 1 when it,
     * a publication or the close failed.
     *
     * <p>ONE END: the first caller ends the run and a later one waits for its
     * exit.  SOLR-18413 r8: the declared update's throw failed the test, and
     * its witness stop and the failed test both ended the run; the witness
     * began the run totals, the test found them begun, closed the session
     * and exited while the verdict was still being written.</p>
     */
    static void exit(int status) {
        synchronized (ENDING) {
            if (ending) {
                while (true) {
                    try {
                        ENDING.wait();
                    } catch (InterruptedException ignored) {
                        // The first end exits the JVM; nothing else does.
                    }
                }
            }
            ending = true;
        }
        int code = status;
        ConcolicRegionRuntime.endAdmission();
        try {
            ConcolicResultPublisher.awaitSelectedResultPublications();
        } catch (Throwable publicationFailure) {
            EngineConsole.trace(publicationFailure);
            code = 1;
        }
        try {
            // Here, not in a conditional shutdown hook: once per JVM.
            ConcolicResultPublisher.publishRunTotals();
            reportWorkloadSessionClose();
        } catch (Throwable closeFailure) {
            // A failure while unwinding must not skip the exit below.
            EngineConsole.trace(closeFailure);
            code = 1;
        }
        System.exit(code);
    }

    /**
     * Closes the workload session; a refusal is printed, not thrown, so it
     * never hides the workload's own outcome.
     */
    private static void reportWorkloadSessionClose() {
        String refusedClose = ConcolicRegionRuntime.closeWorkloadSession();
        if (!refusedClose.isEmpty()) {
            EngineConsole.println(refusedClose);
        }
    }
}
