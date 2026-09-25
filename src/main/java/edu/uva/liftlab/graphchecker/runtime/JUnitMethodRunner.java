package edu.uva.liftlab.graphchecker.runtime;

/**
 * The entry point every {@code execute.sh} launches: the workload session
 * opens before the test method and closes after it on every exit path, so
 * an exported expression can outlive its producer's thread.  The method
 * itself is run by {@link JUnitLifecycle}.
 */
public final class JUnitMethodRunner {
    private JUnitMethodRunner() {
    }

    public static void main(String[] args) {
        String refusedOpen = ConcolicRegionRuntime.openWorkloadSession();
        if (!refusedOpen.isEmpty()) {
            // Without a session every cross-thread expression is lost.
            // Nothing has run yet, so throwing is enough.
            throw new IllegalStateException(refusedOpen);
        }
        int status = 0;
        try {
            try {
                JUnitLifecycle.run(args);
            } catch (Throwable failure) {
                // The replay's outcome is read from stderr.
                failure.printStackTrace(System.err);
                status = 1;
            } finally {
                // Publications first: closing under a pending one is refused.
                ConcolicResultPublisher.awaitSelectedResultPublications();
                // Run totals here, on the one exit path every replay takes,
                // not in a conditional shutdown hook (once per JVM).
                ConcolicResultPublisher.publishRunTotals();
                reportWorkloadSessionClose();
            }
        } catch (Throwable publicationFailure) {
            // A failure while unwinding must not skip the exit below.
            publicationFailure.printStackTrace(System.err);
            status = 1;
        }
        // Explicit exit: non-daemon cluster threads may outlive the test.
        // 0 when the method returned, 1 when it, a publication or the close
        // failed.
        System.exit(status);
    }

    /**
     * Closes the workload session; a refusal is printed, not thrown, so it
     * never hides the workload's own outcome.
     */
    private static void reportWorkloadSessionClose() {
        String refusedClose = ConcolicRegionRuntime.closeWorkloadSession();
        if (!refusedClose.isEmpty()) {
            System.err.println(refusedClose);
        }
    }
}
