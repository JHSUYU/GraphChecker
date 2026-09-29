package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.RawSharedStateReadOut;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ACTIVE;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.assembleRecordedSharedState;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.rootCause;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;

/**
 * Settling one region occurrence: the daemon pool that publishes its rows,
 * the process-exit barrier, and the {@link GapKind#TASK_UNANSWERED} row for
 * a planned task nothing answered.  No result envelope: the row set
 * ({@link SessionPublisher}) is the whole contract.
 */
final class ConcolicResultPublisher {
    private static final Object PUBLICATION_LOCK = new Object();
    private static final AtomicLong PUBLICATION_THREAD_COUNTER =
            new AtomicLong();
    /**
     * Publication must not hold an RPC handler after the VM read-out, and
     * must not drop a completed occurrence either: its queue has no bound.
     * Bounded at 128, it rejected SOLR-18406's declared occurrence while the
     * interpreter was still hashing the expressions of earlier ones.
     */
    private static final ThreadPoolExecutor RESULT_PUBLICATION_EXECUTOR =
            new ThreadPoolExecutor(1, 1, 0L, TimeUnit.MILLISECONDS,
                    new LinkedBlockingQueue<Runnable>(),
                    new ThreadFactory() {
                        @Override
                        public Thread newThread(Runnable runnable) {
                            // In the JVM's root group, not the group of the
                            // test that first published: a test framework
                            // fails its suite on a thread its group leaks.
                            ThreadGroup root =
                                    Thread.currentThread().getThreadGroup();
                            while (root.getParent() != null) {
                                root = root.getParent();
                            }
                            // Compaction recurses along an expression
                            // chain: the engine's stack (java.sh -Xss).
                            Thread thread = new Thread(root, runnable,
                                    "causynth-result-publication-"
                                            + PUBLICATION_THREAD_COUNTER
                                            .incrementAndGet(),
                                    512L << 20);
                            thread.setDaemon(true);
                            return thread;
                        }
                    });
    /** Guarded by {@link #PUBLICATION_LOCK}. */
    private static int resultPublicationsInFlight;
    /** Live selected activations not yet publishing. */
    private static int liveSelectedRegions;

    /** Barrier wait for a live activation making no progress. */
    private static final long TERMINAL_GRACE_MILLIS = 30_000L;

    /** The row naming a task nothing answered; {@code detail} says why. */
    static void taskUnanswered(RuntimeTask task, String detail) {
        // An abandoned occurrence publishes nothing, so the replay's verdict
        // must know before it calls a prefix reproduced.
        FocusedReplay.noteUnansweredTask(detail);
        // Never name nothing: Fields.text would refuse; taskId may be blank.
        RowRuntime.gap(GapKind.TASK_UNANSWERED, GapClass.DIAGNOSTIC,
                task == null ? RowRuntime.sessionId()
                        : firstNonBlank(task.taskId, task.regionId,
                                task.occurrenceId, RowRuntime.sessionId()),
                detail);
    }

    /** Waits until every live or publishing selected activation settles. */
    public static void awaitSelectedResultPublications() {
        boolean interrupted = false;
        List<ActiveRegion> stranded = new ArrayList<>();
        synchronized (PUBLICATION_LOCK) {
            long progress = liveRegionProgress();
            long deadline = System.nanoTime()
                    + TERMINAL_GRACE_MILLIS * 1_000_000L;
            while (liveSelectedRegions > 0
                    || resultPublicationsInFlight > 0) {
                long remaining = deadline - System.nanoTime();
                if (remaining <= 0L) {
                    // Nothing published and no body ran for the whole grace.
                    if (resultPublicationsInFlight == 0) {
                        stranded.addAll(ACTIVE.values());
                    }
                    // Live but not yet ACTIVE: keep waiting.
                    if (!stranded.isEmpty()) break;
                    remaining = TERMINAL_GRACE_MILLIS * 1_000_000L;
                    deadline = System.nanoTime() + remaining;
                }
                int live = liveSelectedRegions;
                int publishing = resultPublicationsInFlight;
                try {
                    PUBLICATION_LOCK.wait(remaining / 1_000_000L,
                            (int) (remaining % 1_000_000L));
                } catch (InterruptedException ignored) {
                    interrupted = true;
                }
                long observed = liveRegionProgress();
                if (observed != progress || live != liveSelectedRegions
                        || publishing != resultPublicationsInFlight) {
                    progress = observed;
                    deadline = System.nanoTime()
                            + TERMINAL_GRACE_MILLIS * 1_000_000L;
                }
            }
        }
        // Outside the barrier lock: each of these files a durable row.
        for (ActiveRegion active : stranded) {
            strandWithoutTerminal(active);
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    private static long liveRegionProgress() {
        long charged = 0L;
        for (ActiveRegion active : ACTIVE.values()) {
            charged += active.chargedLoopBodies;
        }
        return charged;
    }

    /**
     * Ends a focused replay at its witness: the case's declared occurrence
     * observed the fatal, which answers the replay's question, and what the
     * workload does after it no stage reads (SOLR-18406: a follower retried
     * the download it could no longer get, every bound lifted, until the
     * worker's clock killed the JVM and the witness session was withdrawn).
     * Once, on a thread of its own: every publication in flight settles
     * (the witness's own among them), every activation still live is
     * stranded now rather than after a grace its retries keep resetting,
     * and the replay ends as every replay does ({@link JUnitMethodRunner}).
     */
    static void concludeAtWitness() {
        synchronized (PUBLICATION_LOCK) {
            if (concludingAtWitness) return;
            concludingAtWitness = true;
        }
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        new Thread(root, new Runnable() {
            @Override
            public void run() {
                List<ActiveRegion> stranded = new ArrayList<>();
                synchronized (PUBLICATION_LOCK) {
                    while (resultPublicationsInFlight > 0) {
                        try {
                            PUBLICATION_LOCK.wait();
                        } catch (InterruptedException ignored) {
                            // The witness stands; settle and end regardless.
                        }
                    }
                    stranded.addAll(ACTIVE.values());
                }
                for (ActiveRegion active : stranded) {
                    strandWithoutTerminal(active, "AT_WITNESS: the region"
                            + " root was still running when the declared"
                            + " occurrence observed the fatal, and the replay"
                            + " ended there");
                }
                JUnitMethodRunner.exit(0);
            }
        }, "causynth-witness-stop").start();
    }

    /** Guarded by {@link #PUBLICATION_LOCK}. */
    private static boolean concludingAtWitness;

    /** Names one activation whose root never reached a terminal. */
    private static void strandWithoutTerminal(ActiveRegion active) {
        strandWithoutTerminal(active, "TERMINAL_NEVER_REACHED: the"
                + " region root was still running " + TERMINAL_GRACE_MILLIS
                + "ms after the workload ended and charged no loop body in"
                + " that time, so this occurrence reached no NORMAL, THROW"
                + " or bounded CUT terminal");
    }

    private static void strandWithoutTerminal(ActiveRegion active,
                                              String detail) {
        if (!active.finished.compareAndSet(false, true)) return;
        active.releaseActivation();
        active.abandoned = true;
        ACTIVE.remove(active.token, active);
        endLiveSelectedRegion();
        taskUnanswered(active.activation, detail);
    }

    static void beginLiveSelectedRegion() {
        synchronized (PUBLICATION_LOCK) {
            liveSelectedRegions++;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static void endLiveSelectedRegion() {
        synchronized (PUBLICATION_LOCK) {
            if (liveSelectedRegions <= 0) {
                throw new IllegalStateException(
                        "live selected region underflow");
            }
            liveSelectedRegions--;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static void beginSelectedResultPublication() {
        synchronized (PUBLICATION_LOCK) {
            resultPublicationsInFlight++;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static void endSelectedResultPublication() {
        synchronized (PUBLICATION_LOCK) {
            if (resultPublicationsInFlight <= 0) {
                throw new IllegalStateException(
                        "selected result publication underflow");
            }
            resultPublicationsInFlight--;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    private static final Object RUN_TOTALS_LOCK = new Object();
    private static boolean runTotalsHookRegistered;

    static void registerRunTotalsHook() {
        synchronized (RUN_TOTALS_LOCK) {
            if (runTotalsHookRegistered) return;
            runTotalsHookRegistered = true;
            try {
                Runtime.getRuntime().addShutdownHook(new Thread(
                        new Runnable() {
                            @Override
                            public void run() {
                                publishRunTotals();
                            }
                        }, "concolic-run-totals"));
            } catch (IllegalStateException shuttingDown) {
                // Never replaces the workload's own outcome.
            }
        }
    }

    /** Publishes what only the end of a run can state, once per JVM. */
    static void publishRunTotals() {
        synchronized (RUN_TOTALS_LOCK) {
            if (runTotalsPublished) return;
            runTotalsPublished = true;
        }
        configuration().publishUnansweredAddresses();
        // Called from every exit path: a halt runs no shutdown hook.
        RowRuntime.closeSession();
    }

    private static boolean runTotalsPublished;

    static boolean submitCompletedResultPublication(
            final ActiveRegion active,
            final RawSharedStateReadOut rawSharedState) {
        // Reserve loop evidence BEFORE reopening admission, so a later turn
        // cannot claim the same anchor.  Fail-closed: a failure terminates
        // the task, never rolls back a reservation another turn relies on.
        active.activation.reserveCompletedEvidence();
        configuration().releaseCandidate(active.activation);
        try {
            RESULT_PUBLICATION_EXECUTOR.execute(new Runnable() {
                @Override
                public void run() {
                    publishCompletedResult(active, rawSharedState);
                }
            });
            return true;
        } catch (RejectedExecutionException rejected) {
            // Never decode on the RPC owner as a fallback.
            taskUnanswered(active.activation, "RESULT_PUBLICATION_REJECTED: "
                    + "the row publication of a completed VM occurrence could"
                    + " not be enqueued: " + rootCause(rejected));
            return false;
        }
    }

    private static void publishCompletedResult(
            ActiveRegion active, RawSharedStateReadOut rawSharedState) {
        try {
            assembleRecordedSharedState(active, rawSharedState);
            // Here, where the write log is assembled: once, on one thread.
            RowPublication.publish(active);
            if (resultAnswersSelectedGoal(active)) {
                configuration().markOccurrenceClaimed(active.activation);
            }
        } catch (Throwable failure) {
            // Terminal: a later activation may already use the reservation.
            configuration().markOccurrenceClaimed(active.activation);
            try {
                taskUnanswered(active.activation,
                        "RESULT_PUBLICATION_FAILED: a completed VM occurrence"
                                + " could not publish its rows: "
                                + rootCause(failure));
            } catch (Throwable reportingFailure) {
                System.err.println("Causynth could not publish"
                        + " TASK_UNANSWERED for "
                        + active.activation.taskId + ": "
                        + rootCause(reportingFailure));
            }
        } finally {
            endSelectedResultPublication();
        }
    }

    /**
     * A complete non-loop activation settles its task, target or not; a
     * loop body only by deciding the declared fatal target (no declared
     * target is "not reached": no throw stands in for it).
     */
    private static boolean resultAnswersSelectedGoal(ActiveRegion active) {
        RuntimeTask task = active.activation;
        if (!task.loopBodyRoot) return true;
        return !task.capturesTargetReach
                || task.reachedRequiredTargetOutcome(active.targetReach);
    }
}
