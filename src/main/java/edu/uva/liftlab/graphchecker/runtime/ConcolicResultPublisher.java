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
        boolean decided = FocusedReplay.noteUnansweredTask(detail);
        // Never name nothing: Fields.text would refuse; taskId may be blank.
        RowRuntime.gap(GapKind.TASK_UNANSWERED, GapClass.DIAGNOSTIC,
                task == null ? RowRuntime.sessionId()
                        : firstNonBlank(task.taskId, task.regionId,
                                task.occurrenceId, RowRuntime.sessionId()),
                detail);
        if (decided) concludeAtRefusal();
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

    /** Why a focused replay ends before its workload does. */
    private enum Conclusion {
        /** The case's declared occurrence observed the fatal. */
        AT_WITNESS("the declared occurrence observed the fatal"),
        /** A refusal decided every obligation the replay carries
         *  ({@code FocusedReplay#refusedAt}). */
        AT_REFUSAL("a refusal decided every obligation this replay carries");

        private final String when;

        Conclusion(String when) {
            this.when = when;
        }
    }

    /**
     * Ends a focused replay at its witness: the case's declared occurrence
     * observed the fatal, which answers the replay's question, and what the
     * workload does after it no stage reads (SOLR-18406: a follower retried
     * the download it could no longer get, every bound lifted, until the
     * worker's clock killed the JVM and the witness session was withdrawn).
     * The schedule states the run cut there ({@link ScheduleLog#witnessed}).
     */
    static void concludeAtWitness() {
        conclude(Conclusion.AT_WITNESS);
    }

    /**
     * Ends a focused replay at the refusal that decided every obligation it
     * carries ({@code FocusedReplay#refusedAt}): each verdict is NOT_ADMITTED
     * whatever the run does next, and the session is published to no stage,
     * so the rest of the workload answers nothing (SOLR-18413 r5: 67 focused
     * replays of 10 to 22 minutes, each refused at a constructor's branch and
     * run to the test's end).
     */
    static void concludeAtRefusal() {
        conclude(Conclusion.AT_REFUSAL);
    }

    /**
     * The one early end, once, on a thread of its own: admission ends, every
     * publication in flight settles, every activation still live is stranded
     * now rather than after a grace its retries keep resetting, and the
     * replay ends as every replay does ({@link JUnitMethodRunner}).
     *
     * <p>What still publishes differs.  At the witness, every occurrence
     * completed before it (the witness's own among them): its session is a
     * corpus session, read whole up to there.  At a refusal, no publication
     * that has not started: the session is withdrawn, and draining the queue
     * into it cost a Solr replay two to five minutes past the test's end
     * (solr-18413 r5, ee).  A withheld one's mints still publish.</p>
     */
    private static void conclude(final Conclusion end) {
        synchronized (PUBLICATION_LOCK) {
            if (concluded != null) return;
            concluded = end;
            submittedAtEnd = end == Conclusion.AT_WITNESS ? submitted : 0L;
        }
        ConcolicRegionRuntime.endAdmission();
        if (end == Conclusion.AT_WITNESS) ScheduleLog.witnessed();
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        new Thread(root, new Runnable() {
            @Override
            public void run() {
                // The replay log's one line saying when and why it ended, as
                // a UTC instant: a workload may randomize the JVM's zone
                // (Solr's test framework does).
                System.err.println("Causynth " + java.time.Instant.now()
                        + ": the replay ends " + end + ": " + end.when);
                List<ActiveRegion> stranded = new ArrayList<>();
                synchronized (PUBLICATION_LOCK) {
                    while (resultPublicationsInFlight > 0) {
                        try {
                            PUBLICATION_LOCK.wait();
                        } catch (InterruptedException ignored) {
                            // The end stands; settle and end regardless.
                        }
                    }
                    stranded.addAll(ACTIVE.values());
                }
                for (ActiveRegion active : stranded) {
                    strandWithoutTerminal(active, end + ": the region root"
                            + " was still running when " + end.when
                            + ", and the replay ended there");
                }
                JUnitMethodRunner.exit(0);
            }
        }, "causynth-early-end").start();
    }

    /** Guarded by {@link #PUBLICATION_LOCK}. */
    private static Conclusion concluded;
    /**
     * Publications submitted, and how many were when the replay's end
     * stood: one completed after it is no part of the question, and
     * publishing it kept the queue from ever draining (SOLR-18406's follower
     * retried the download, each retry an occurrence with its own
     * publication).  Guarded by {@link #PUBLICATION_LOCK}.
     */
    private static long submitted;
    private static long submittedAtEnd = Long.MAX_VALUE;

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
        // Its path is withheld and its mints published, as an abandoned
        // occurrence's are: other activations' rows already name those
        // symbols (hdfs-11741 r1: IMPORT invariant 11, a root symbol with
        // no RootMintRow).  Its thread still runs and may mint meanwhile.
        synchronized (active) {
            RowPublication.publishMints(active);
        }
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

    /**
     * Publishes what only the end of a run can state, once per JVM, and
     * returns only once it is published, whoever publishes it.
     *
     * <p>Two threads end one run when an early end meets the workload's own
     * (solr-18413 r8: the witness's end and the test's failure).  A second
     * caller that returned at once went on to {@code System.exit}, which
     * halted the first inside {@link RowRuntime#closeSession}: the session
     * lost its verdict rows and the worker's row kept SAT_MODEL_READY.  Not
     * held under the lock, so a woven thread still filing a candidate
     * ({@code ConcolicTaskPlan#noteUnaddressedCandidate}: its task's monitor,
     * then this lock) cannot deadlock against the render.</p>
     */
    static void publishRunTotals() {
        boolean interrupted = false;
        synchronized (RUN_TOTALS_LOCK) {
            if (runTotalsStarted) {
                while (!runTotalsPublished) {
                    try {
                        RUN_TOTALS_LOCK.wait();
                    } catch (InterruptedException ignored) {
                        interrupted = true;
                    }
                }
                if (interrupted) Thread.currentThread().interrupt();
                return;
            }
            runTotalsStarted = true;
        }
        try {
            configuration().publishUnansweredAddresses();
            // Called from every exit path: a halt runs no shutdown hook.
            RowRuntime.closeSession();
        } finally {
            synchronized (RUN_TOTALS_LOCK) {
                runTotalsPublished = true;
                RUN_TOTALS_LOCK.notifyAll();
            }
        }
    }

    /** Guarded by {@link #RUN_TOTALS_LOCK}. */
    private static boolean runTotalsStarted;
    private static boolean runTotalsPublished;

    static boolean submitCompletedResultPublication(
            final ActiveRegion active,
            final RawSharedStateReadOut rawSharedState) {
        // Reserve loop evidence BEFORE reopening admission, so a later turn
        // cannot claim the same anchor.  Fail-closed: a failure terminates
        // the task, never rolls back a reservation another turn relies on.
        active.activation.reserveCompletedEvidence();
        configuration().releaseCandidate(active.activation);
        final long ordinal;
        synchronized (PUBLICATION_LOCK) {
            ordinal = ++submitted;
        }
        try {
            RESULT_PUBLICATION_EXECUTOR.execute(new Runnable() {
                @Override
                public void run() {
                    publishCompletedResult(active, rawSharedState, ordinal);
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
            ActiveRegion active, RawSharedStateReadOut rawSharedState,
            long ordinal) {
        try {
            Conclusion late;
            synchronized (PUBLICATION_LOCK) {
                late = ordinal > submittedAtEnd ? concluded : null;
            }
            if (late != null) {
                // Withheld as a stranded one is: its mints still published.
                configuration().markOccurrenceClaimed(active.activation);
                RowPublication.publishMints(active);
                taskUnanswered(active.activation, late + ": this occurrence"
                        + " was still unpublished when " + late.when
                        + ", and the replay ended there");
                return;
            }
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
        if (!task.loopBodyRoot || !task.capturesTargetReach) return true;
        return task.targetGuards.size() > 1
                ? RowPublication.tookDisjunct(active, new ArrayList<String>())
                : task.reachedRequiredTargetOutcome(active.targetReach);
    }
}
