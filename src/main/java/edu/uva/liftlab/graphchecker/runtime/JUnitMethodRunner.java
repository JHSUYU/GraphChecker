package edu.uva.liftlab.graphchecker.runtime;

/**
 * The workload's symbolic lifetime, and this process's exit status.
 *
 * <p>The entry point every {@code execute.sh} launches.  The test method is
 * what "the workload" means for GraphChecker, so the workload-wide session
 * opens before the method starts and closes after it ends -- on every exit
 * path, including a failing test, which is also where the process's own
 * exit status is stated.  Region entry and exit no longer bound that
 * lifetime, which is what lets one producer's exported expression outlive
 * the producer's thread.</p>
 *
 * <p>Running the method is {@link JUnitLifecycle}'s: that is a reflective
 * JUnit lifecycle and it shares nothing with a session but this {@code
 * main}.</p>
 */
public final class JUnitMethodRunner {
    private JUnitMethodRunner() {
    }

    public static void main(String[] args) {
        String refusedOpen = ConcolicRegionRuntime.openWorkloadSession();
        if (!refusedOpen.isEmpty()) {
            // A campaign whose session the VM refused would run with
            // per-region symbolic lifetimes and quietly lose every
            // cross-thread expression it exists to record.  Thrown rather
            // than exited: no workload code has run yet, so there is no
            // publication to make, nothing to close, and no workload thread
            // to be held up by.
            throw new IllegalStateException(refusedOpen);
        }
        int status = 0;
        try {
            try {
                JUnitLifecycle.run(args);
            } catch (Throwable failure) {
                // The workload's own throwable, on stderr, where every
                // replay's outcome has always been read from.
                failure.printStackTrace(System.err);
                status = 1;
            } finally {
                // Publications first: a result still being appended belongs
                // to a region that is still a session member, and closing
                // under it would be refused anyway.
                ConcolicResultPublisher.awaitSelectedResultPublications();
                // And then what only the end of a run can state, on the one
                // exit path every replay takes.  The seed replay also
                // reaches this through the halt after its selected result
                // settled; a focused replay does not halt, and the shutdown
                // hook that would have done it is registered only when some
                // candidate went unaddressed -- so a focused session whose
                // every candidate was addressed closed with no expression
                // table at all (2 bytes, the "{}" written when the session
                // dir was created) while its rows cited 28 refs.  One
                // publication path for both kinds of session;
                // publishRunTotals is once per JVM.
                ConcolicResultPublisher.publishRunTotals();
                reportWorkloadSessionClose();
            }
        } catch (Throwable publicationFailure) {
            // A publication or a close that threw while unwinding: named on
            // stderr and failed, like any other refusal, but not allowed to
            // skip the exit below.
            publicationFailure.printStackTrace(System.err);
            status = 1;
        }
        // Stated, not left to the JVM: the workload's teardown hands back a
        // cluster whose non-daemon threads may outlive the test method, and
        // a replay that never returns is not a fail-closed replay -- the
        // campaign would wait on it instead of reading its outcome.  The
        // status is the outcome the uncaught throwable used to carry: 0 when
        // the workload method returned, 1 when it, a publication or the
        // session close did not.  A concolic worker still reaches its own
        // halt after the selected result settles and never gets here.
        System.exit(status);
    }

    /**
     * Closes the workload session and names a refusal on stderr.
     *
     * <p>The refusal is reported rather than thrown: it is discovered while
     * unwinding, possibly already on a failure path, and replacing the
     * workload's own outcome with it would hide the original result.</p>
     */
    private static void reportWorkloadSessionClose() {
        String refusedClose = ConcolicRegionRuntime.closeWorkloadSession();
        if (!refusedClose.isEmpty()) {
            System.err.println(refusedClose);
        }
    }
}
