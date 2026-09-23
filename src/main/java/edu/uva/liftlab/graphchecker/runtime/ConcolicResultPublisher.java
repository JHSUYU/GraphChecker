package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.RawSharedStateReadOut;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ArrayBlockingQueue;
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
 * Settling one region occurrence: the bounded daemon pool that publishes its
 * rows, the process-exit barrier that waits for every selected activation,
 * and the one gap row that names a planned task nothing answered.
 *
 * <p>There is no result envelope.  The per-kind row set a session publishes
 * ({@link SessionPublisher}) is a replay's whole contract, so an activation
 * that reached a terminal publishes rows and an address nothing answered
 * publishes {@link GapKind#TASK_UNANSWERED}.</p>
 */
final class ConcolicResultPublisher {
    /** Guards the process-exit barrier alone. */
    private static final Object PUBLICATION_LOCK = new Object();
    private static final AtomicLong PUBLICATION_THREAD_COUNTER =
            new AtomicLong();
    /**
     * Row publication must not hold an RPC handler after its VM-owned
     * read-outs are complete.
     */
    private static final ThreadPoolExecutor RESULT_PUBLICATION_EXECUTOR =
            new ThreadPoolExecutor(1, 1, 0L, TimeUnit.MILLISECONDS,
                    new ArrayBlockingQueue<Runnable>(128),
                    new ThreadFactory() {
                        @Override
                        public Thread newThread(Runnable runnable) {
                            Thread thread = new Thread(runnable,
                                    "causynth-result-publication-"
                                            + PUBLICATION_THREAD_COUNTER
                                            .incrementAndGet());
                            thread.setDaemon(true);
                            return thread;
                        }
                    }, new ThreadPoolExecutor.AbortPolicy());
    /** Guarded by {@link #PUBLICATION_LOCK}. */
    private static int resultPublicationsInFlight;
    /**
     * Selected activations that are live but have not yet registered a
     * publication.
     */
    private static int liveSelectedRegions;

    /**
     * How long the process-exit barrier waits for a live activation that is
     * making no instrumented progress.
     */
    private static final long TERMINAL_GRACE_MILLIS = 30_000L;

    /**
     * Files the one row that names a planned task no activation answered.
     *
     * <p>{@code detail} opens with the reason -- the same words the skip
     * envelope used to carry as its {@code skipKind} -- so a reader of
     * {@code gaps.jsonl} sees why without a second file.</p>
     */
    static void taskUnanswered(RuntimeTask task, String detail) {
        // A prefix this replay was abandoned on is not only a row.  The
        // abandoned occurrence publishes nothing, so the session loses its
        // whole row set, and the one account of what this replay settled
        // has to know that before it calls a prefix reproduced.
        FocusedReplay.noteUnansweredTask(detail);
        // The task, else the region it plans, else this session: a row that
        // named nothing would refuse inside Fields.text, out of the hook
        // that filed it.  taskId is the plan's own optionalString, so it
        // can be blank even when the task is not.
        RowRuntime.gap(GapKind.TASK_UNANSWERED, GapClass.DIAGNOSTIC,
                task == null ? RowRuntime.sessionId()
                        : firstNonBlank(task.taskId, task.regionId,
                                task.occurrenceId, RowRuntime.sessionId()),
                detail);
    }

    /**
     * Waits until every selected activation that is live or already
     * publishing has either published its rows or reported a failure.
     */
    public static void awaitSelectedResultPublications() {
        boolean interrupted = false;
        List<ActiveRegion> stranded = new ArrayList<>();
        synchronized (PUBLICATION_LOCK) {
            // The live-region count covers the interval after a selected
            // activation is ACTIVE but before finish registers publication.
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
                    // An activation counted live but not yet ACTIVE is a few
                    // instructions from being one; there is nothing to name
                    // and the barrier keeps covering that window.
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

    /** Instrumented loop bodies every live activation has charged so far. */
    private static long liveRegionProgress() {
        long charged = 0L;
        for (ActiveRegion active : ACTIVE.values()) {
            charged += active.chargedLoopBodies;
        }
        return charged;
    }

    /** Names one activation whose root never reached a terminal. */
    private static void strandWithoutTerminal(ActiveRegion active) {
        if (!active.finished.compareAndSet(false, true)) return;
        active.releaseActivation();
        active.abandoned = true;
        ACTIVE.remove(active.token, active);
        endLiveSelectedRegion();
        taskUnanswered(active.activation, "TERMINAL_NEVER_REACHED: the"
                + " region root was still running " + TERMINAL_GRACE_MILLIS
                + "ms after the workload ended and charged no loop body in"
                + " that time, so this occurrence reached no NORMAL, THROW"
                + " or bounded CUT terminal");
    }

    /** Marks one selected activation live. */
    static void beginLiveSelectedRegion() {
        synchronized (PUBLICATION_LOCK) {
            liveSelectedRegions++;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    /** Marks one selected activation no longer live. */
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

    /**
     * Registers the one shutdown hook that publishes what only the end of a
     * run can state.
     */
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
                // A run already shutting down cannot register one.  The
                // workload's own outcome is never replaced by this.
            }
        }
    }

    /**
     * Publishes what only the end of a run can state: every selected address
     * that nothing answered, and this run's handoff aggregates.
     */
    static void publishRunTotals() {
        synchronized (RUN_TOTALS_LOCK) {
            if (runTotalsPublished) return;
            runTotalsPublished = true;
        }
        configuration().publishUnansweredAddresses();
        // What only the end of a replay can state: the verdict of every
        // obligation it was handed, and the expression table every row that
        // cites a ref needs.  Once per JVM, from whichever exit path gets
        // here first: a campaign halts the JVM as soon as the selected
        // result settles, which runs no shutdown hook, and a replay that
        // ends by its workload throwing exits through JUnitMethodRunner.
        RowRuntime.closeSession();
    }

    private static boolean runTotalsPublished;

    /** Transfers one completed native read-out to the bounded daemon pool. */
    static boolean submitCompletedResultPublication(
            final ActiveRegion active,
            final RawSharedStateReadOut rawSharedState) {
        // The VM context and its raw read-out are complete.  Do not keep the
        // task's admission slot hostage while the daemon performs the much
        // larger row decode.  Reserve the retained loop evidence before
        // reopening admission, so a later body turn cannot claim the same
        // semantic anchor.  Publication remains fail-closed: an
        // enqueue/decode failure terminates the task instead of rolling this
        // reservation back underneath a later activation that may already
        // depend on it.  Nothing is reserved for a configured source: it is
        // ONE symbol, so a later turn's read of it is the same variable and
        // there is no ordinal to carry across turns.
        active.activation.reserveCompletedEvidence(
                targetReachedByActivation(active));
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
            // Never run a large decode on the RPC owner as a rejection
            // fallback.  The row says what happened.
            taskUnanswered(active.activation, "RESULT_PUBLICATION_REJECTED: "
                    + "the row publication of a completed VM occurrence could"
                    + " not be enqueued: " + rootCause(rejected));
            return false;
        }
    }

    /** Assembles and publishes the rows of one already-closed region. */
    private static void publishCompletedResult(
            ActiveRegion active, RawSharedStateReadOut rawSharedState) {
        try {
            assembleRecordedSharedState(active, rawSharedState);
            // The activation, as the per-kind row set.  Here because this is
            // where the write log has been assembled: every row this
            // activation can state is complete exactly once, on one thread.
            RowPublication.publish(active);
            if (resultAnswersSelectedGoal(active)) {
                configuration().markOccurrenceClaimed(active.activation);
            }
        } catch (Throwable failure) {
            // Admission was already reopened after the VM raw read-out.  A
            // failure is terminal because a later activation may have used
            // the reserved loop phase; silently rolling back would make its
            // identity false.
            configuration().markOccurrenceClaimed(active.activation);
            try {
                taskUnanswered(active.activation,
                        "RESULT_PUBLICATION_FAILED: a completed VM occurrence"
                                + " could not publish its rows: "
                                + rootCause(failure));
            } catch (Throwable reportingFailure) {
                // The last resort: the gap row itself could not be filed, so
                // there is nowhere left to state this but stderr.
                System.err.println("Causynth could not publish"
                        + " TASK_UNANSWERED for "
                        + active.activation.taskId + ": "
                        + rootCause(reportingFailure));
            }
        } finally {
            endSelectedResultPublication();
        }
    }

    /** Whether this candidate supplied the evidence its selected goal needs. */
    private static boolean resultAnswersSelectedGoal(ActiveRegion active) {
        // One complete non-loop activation is the selected occurrence.  An
        // occurrence that reached no target is its seed case and must settle
        // the task; a later replay is a separate planned task, not another
        // candidate for this physical occurrence.
        RuntimeTask task = active.activation;
        if (!task.loopBodyRoot) return true;
        return !task.capturesTargetReach
                || targetReachedByActivation(active);
    }

    /**
     * Whether this activation decided the selected fatal target event.
     *
     * <p>Only the declared target occurrence answers this.  A task that
     * captures target reach and declares no target branch used to have
     * <em>any</em> throw count as a reach: whatever exception the workload
     * happened to exit through stood in for a fatal site nobody checked.
     * That fabricates the target link itself -- the one edge the whole claim
     * rests on -- out of an unrelated exception.</p>
     *
     * <p>There is nothing to state when the plan never named which
     * occurrence of which site is the target, so the honest answer is "not
     * reached", and the target row says so: {@code reachedAnchor false}.</p>
     */
    /** Package-visible for the target-reach contract test. */
    static boolean targetReachedByActivation(ActiveRegion active) {
        RuntimeTask task = active.activation;
        return task.declaresTargetBranch()
                && task.reachedRequiredTargetOutcome(active.targetReach);
    }
}
