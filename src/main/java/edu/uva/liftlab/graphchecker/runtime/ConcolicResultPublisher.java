package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.RecordedEvidenceIdentity;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ActiveRegion;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.RawSharedStateReadOut;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.shallowCopy;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ACTIVE;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.CONFIGURED_SOURCE_PHASE_GAPS;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.CONFIGURED_SOURCE_PHASE_OBSERVATIONS;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.GSON;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.HALT_AFTER_SELECTED_RESULT_PROPERTY;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.SKIP_RESULT_PUBLICATION_FAILED;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.SKIP_TERMINAL_NEVER_REACHED;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.diagAfterVmClose;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.exceptionChain;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.assembleRecordedSharedState;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.evidenceIdentity;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.rootCause;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;

/**
 * Publishing one region result: the bounded daemon pool that decodes and
 * appends it, the process-exit barrier that waits for every selected
 * activation, and the JSONL writer they both end at.
 */
final class ConcolicResultPublisher {
    private static final Object WRITE_LOCK = new Object();
    /** Guards the process-exit barrier alone. */
    private static final Object PUBLICATION_LOCK = new Object();
    private static final AtomicLong PUBLICATION_THREAD_COUNTER =
            new AtomicLong();
    /**
     * JSON decoding and durable result publication must not hold an RPC
     * handler after its VM-owned read-outs are complete.
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
     * Waits until every selected activation that is live or already publishing
     * a result has either durably closed its JSONL record or reported a write
     * failure.
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
        // Outside the barrier lock: each of these appends a durable row.
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
        active.releaseActivationOrdinal();
        active.abandoned = true;
        ACTIVE.remove(active.token, active);
        endLiveSelectedRegion();
        writeSkipped(active.activation, SKIP_TERMINAL_NEVER_REACHED,
                "the region root was still running "
                        + TERMINAL_GRACE_MILLIS
                        + "ms after the workload ended and charged no loop "
                        + "body in that time, so this occurrence reached no "
                        + "NORMAL, THROW or bounded CUT terminal",
                null);
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
        configuration().publishUnansweredAddresses();
    }

    /** Transfers one completed native read-out to the bounded daemon pool. */
    static boolean submitCompletedResultPublication(
            final ActiveRegion active, final JsonObject result,
            final String rawEngineSummary,
            final RawSharedStateReadOut rawSharedState) {
        // The VM context and its raw read-out are complete.  Do not keep the
        // task's admission slot hostage while the daemon performs the much
        // larger JSON decode: a later loop-body turn may be the exact next
        // source phase this bounded address reserved.  Reserve the retained
        // loop evidence before reopening admission, so that next turn sees
        // phase n+1 and cannot claim the same semantic anchor.  Publication
        // remains fail-closed: an enqueue/decode/append failure terminates
        // the task instead of rolling this reservation back underneath a
        // later activation that may already depend on it.
        active.activation.reserveCompletedOccurrence(
                active.configuredSourcePhaseOrdinals,
                active.retainedSemanticAnchorIds);
        active.activation.reserveCompletedEvidence(
                targetReachedByActivation(active));
        configuration().releaseCandidate(active.activation);
        try {
            RESULT_PUBLICATION_EXECUTOR.execute(new Runnable() {
                @Override
                public void run() {
                    publishCompletedResult(active, result, rawEngineSummary,
                            rawSharedState);
                }
            });
            return true;
        } catch (RejectedExecutionException rejected) {
            // Never run a large decode on the RPC owner as a rejection
            // fallback.
            diagAfterVmClose("RESULT_PUBLICATION_REJECTED",
                    rootCause(rejected));
            haltWhenCampaignSettled(active.activation.taskId, 2);
            return false;
        }
    }

    /**
     * Brings the VM's summary into the row before the row is compacted.
     *
     * <p>The summary used to be spliced into the line as the VM serialized
     * it, beside a result that had already been compacted.  That published
     * two tables for the same expressions under two reference schemes -- the
     * portable anchors for everything the Java side had touched, the VM's own
     * ids for the path condition -- and neither could ever cover the other,
     * because the two were never in the same object.  Merging the summary in
     * first means one table, one scheme, and every expression stored once
     * however it was reached.</p>
     *
     * <p>A summary that will not decode is a gap, not a silent omission: the
     * row says so and keeps what it has.</p>
     */
    private static void mergeEngineSummary(ActiveRegion active,
                                           JsonObject result,
                                           String rawEngineSummary) {
        if (rawEngineSummary == null) return;
        try {
            result.add("engineSummary",
                    active.expressionStore.importEnvelope(rawEngineSummary));
        } catch (RuntimeException undecodable) {
            result.addProperty("engineSummaryError",
                    rootCause(undecodable));
        }
    }

    /** Decodes, assembles, appends, and settles one already-closed region. */
    private static void publishCompletedResult(
            ActiveRegion active, JsonObject result,
            String rawEngineSummary, RawSharedStateReadOut rawSharedState) {
        try {
            assembleRecordedSharedState(active, rawSharedState);
            addRecordedSharedStateToResult(result, active,
                    rawSharedState == null ? evidenceIdentity(active)
                            : rawSharedState.identity);
            mergeEngineSummary(active, result, rawEngineSummary);
            JsonObject portableResult = active.expressionStore.compact(result);
            boolean written = appendResult(portableResult);
            boolean goalAnswered = written
                    && resultAnswersSelectedGoal(active.activation, result);
            if (goalAnswered) {
                configuration().markOccurrenceClaimed(active.activation);
            }
            // A compatible root is only a candidate for an occurrence address.
            // Keep admitting candidates until the selected target is reached.
            if (!written || goalAnswered) {
                haltWhenCampaignSettled(active.activation.taskId,
                        written ? 0 : 2);
            }
        } catch (Throwable failure) {
            // Admission was already reopened after the VM raw read-out.  A
            // failure is terminal because a later activation may have used
            // the reserved loop phase; silently rolling back would make its
            // identity false.
            diagAfterVmClose("RESULT_PUBLICATION_FAILED",
                    rootCause(failure));
            configuration().markOccurrenceClaimed(active.activation);
            try {
                writeSkipped(active.activation,
                        SKIP_RESULT_PUBLICATION_FAILED,
                        "completed VM occurrence could not be published: "
                                + rootCause(failure), null);
            } catch (Throwable reportingFailure) {
                diagAfterVmClose("RESULT_PUBLICATION_FAILURE_REPORT_FAILED",
                        rootCause(reportingFailure));
            } finally {
                haltWhenCampaignSettled(active.activation.taskId, 2);
            }
        } finally {
            endSelectedResultPublication();
        }
    }

    /** Builds one occurrence result before the VM summary is spliced in. */
    static void buildCompletedResult(
            JsonObject result, ActiveRegion active,
            RecordedEvidenceIdentity identity) {
        String exitKind = active.exitKind;
        // A loop-bound cut is itself the terminal of the bounded local path.
        boolean boundedPathExit = "CUT".equals(exitKind)
                && active.loopBoundCut != null
                && active.replayResourceCut == null;
        String completedExitKind = boundedPathExit
                ? "BOUNDED" : exitKind;
        if (!active.activation.symbolize.isEmpty()
                && !active.pathRecordingStarted) {
            active.addUnresolvedOnce("NO_SELECTED_INPUT_MATERIALIZED");
        }
        populateCompletedResult(result, active, completedExitKind,
                active.exceptionType, active.exitThrowable, identity);
    }

    /**
     * Ends the workload once every campaign task has reached a terminal
     * outcome, when the caller asked for that.
     */
    static void haltWhenCampaignSettled(String taskId, int status) {
        int campaignStatus = configuration().settle(taskId, status);
        if (campaignStatus >= 0 && Boolean.getBoolean(
                HALT_AFTER_SELECTED_RESULT_PROPERTY)) {
            // A halt runs no shutdown hook, so the run's totals are
            // published here or never.
            publishRunTotals();
            Runtime.getRuntime().halt(campaignStatus);
        }
    }

    /**
     * The activation's exact configured-source and planned-action
     * observations, one runtime hook result per row.
     */
    private static JsonArray symbolizedInputs(ActiveRegion active) {
        return sharedRows(active.symbolizedRows);
    }

    /** One array shell over immutable evidence rows and expression DAGs. */
    private static JsonArray sharedRows(Collection<JsonObject> source) {
        JsonArray rows = new JsonArray();
        if (source != null) {
            for (JsonObject row : source) rows.add(row);
        }
        return rows;
    }

    /** Copies {@code rows} with the identity stamp applied to each. */
    private static JsonArray stamped(List<JsonObject> rows,
                                     RecordedEvidenceIdentity identity) {
        JsonArray stamped = new JsonArray();
        for (JsonObject row : rows) {
            JsonObject copy = shallowCopy(row);
            if (identity != null
                    && !RecordedEvidenceIdentity.stamped(copy)) {
                identity.stamp(copy);
            }
            stamped.add(copy);
        }
        return stamped;
    }

    private static void populateCompletedResult(
            JsonObject result, ActiveRegion active, String exitKind,
            String exceptionType, Throwable throwable,
            RecordedEvidenceIdentity identity) {
        active.nameUnreachedTargetBranch();
        addResultIdentity(result, active, exitKind, exceptionType);
        if (throwable != null && !"CUT".equals(exitKind)) {
            result.add("exceptionChain", exceptionChain(throwable));
        }
        if (active.loopBoundCut != null) {
            result.add("pathCut", active.loopBoundCut.deepCopy());
        }
        if (active.replayResourceCut != null) {
            result.add("replayResourceCut",
                    active.replayResourceCut.deepCopy());
        }
        result.add("loopBackedgeTraversals",
                active.loopBackedges.toJson());
        result.add("replayLoopBodies",
                active.loopBackedges.bodiesToJson());
        if (!active.loopCardinalities.isEmpty()) {
            result.add(LoopBoundPolicy.LOOP_CARDINALITIES,
                    sharedRows(active.loopCardinalities));
        }
        if (!active.loopCardinalityGaps.isEmpty()) {
            result.add(LoopBoundPolicy.LOOP_CARDINALITY_GAPS,
                    sharedRows(active.loopCardinalityGaps));
        }
        if (active.targetReach != null) {
            result.add("targetReach", active.targetReach);
        }
        result.add("unresolvedInputs", GSON.toJsonTree(active.unresolved));
        result.add("symbolizedInputs", symbolizedInputs(active));
        SymbolicSourceEvidence.writeTo(result,
                new ArrayList<>(active.symbolicSources.values()));
        if (!active.activation.configuredSourcePhases.isEmpty()) {
            result.add(CONFIGURED_SOURCE_PHASE_OBSERVATIONS,
                    sharedRows(active.configuredSourcePhaseObservations));
            result.add(CONFIGURED_SOURCE_PHASE_GAPS,
                    sharedRows(active.configuredSourcePhaseGaps));
        }
        result.add("branchMappings", sharedRows(active.branchMappings));
        // Every evidence row this activation publishes names the run, the
        // session, the activation, and the read-out batch it came from.
        VmHandoffEvidence.writeTo(result, active.vmHandoffEvents);
        if (!active.rpcHandoffGaps.isEmpty()) {
            result.add("rpcHandoffGaps",
                    stamped(active.rpcHandoffGaps, identity));
        }
    }

    /** Whether this candidate supplied the evidence its selected goal needs. */
    private static boolean resultAnswersSelectedGoal(
            RuntimeTask task, JsonObject result) {
        // One complete non-loop activation is the selected occurrence.  A
        // targetReached:false row is its seed case and must settle the task;
        // a later replay is a separate planned task, not another candidate
        // for this physical occurrence.
        if (!task.loopBodyRoot) {
            return true;
        }
        if (task.capturesTargetReach) {
            return optionalBool(result, "targetReached", false);
        }
        return true;
    }

    /**
     * Whether this activation decided the selected fatal target event.
     *
     * <p>Only the declared target occurrence answers this.  A task that
     * captures target reach and declares no target branch used to have
     * <em>any</em> throw count as a reach: whatever exception the workload
     * happened to exit through stood in for a fatal site nobody checked, and
     * {@link ConcolicRegionRuntime.ActiveRegion#nameUnreachedTargetBranch}
     * returned early for exactly that case, so no gap was filed either.  That
     * fabricates the target link itself -- the one edge the whole claim rests
     * on -- out of an unrelated exception.</p>
     *
     * <p>There is nothing to state when the plan never named which occurrence
     * of which site is the target, so the honest answer is "not reached", and
     * the missing declaration is filed as {@code TARGET_REACH_NOT_OBSERVED}
     * by {@code nameUnreachedTargetBranch}.  An occurrence that was never
     * composed is already a first-class answer downstream: {@code
     * TargetOccurrenceElection.SKIPPED_UNOBSERVED}.</p>
     */
    /** Package-visible for the target-reach contract test. */
    static boolean targetReachedByActivation(ActiveRegion active) {
        RuntimeTask task = active.activation;
        return task.declaresTargetBranch()
                && task.reachedRequiredTargetOutcome(active.targetReach);
    }

    /** Adds decoded shared-state evidence to an otherwise complete result. */
    private static void addRecordedSharedStateToResult(
            JsonObject result, ActiveRegion active,
            RecordedEvidenceIdentity identity) {
        if (!active.sharedStateRecords.isEmpty()) {
            // Map states travel in this same member, and deliberately: the
            // importer admits a MAP_STATE location through the code path a
            // field location takes, so publishing them in a second member
            // would be the first step towards a second admission rule.
            result.add("sharedFieldVersions", stamped(
                    new ArrayList<>(active.sharedStateRecords.values()),
                    identity));
        }
        if (!active.sharedStateGaps.isEmpty()) {
            result.add("sharedStateGaps",
                    stamped(active.sharedStateGaps, identity));
        }
    }

    static void addResultIdentity(
            JsonObject result, ActiveRegion active, String exitKind,
            String exceptionType) {
        RuntimeTask task = active.activation;
        result.addProperty("event", "CONCOLIC_REGION_RESULT");
        result.addProperty("schemaVersion", 1);
        result.addProperty("taskId", task.taskId);
        addReplayIdentity(result, task);
        result.addProperty("exitKind", exitKind);
        result.addProperty("exceptionType", safe(exceptionType));
        // README OCC-1 result-row contract, consumed by the importer:
        // one row per activation of the address, each naming which activation
        // it is and what it did or did not reach.
        result.addProperty("plannedOccurrenceId", task.occurrenceId);
        result.addProperty("occurrenceId", active.occurrenceId());
        result.addProperty("activationOrdinal", active.activationOrdinal);
        // Telemetry only: which activation cost the wall clock.  The importer
        // builds its summary from a named field list, so nothing downstream
        // hashes these and no replay match can turn on them.
        result.addProperty("startedAtMillis", active.startedAtMillis);
        result.addProperty("elapsedMillis", active.elapsedMillis());
        if (task.capturesTargetReach) {
            // Only a target-reach address selects on this.
            result.addProperty("targetReached",
                    targetReachedByActivation(active));
        }
    }

    /** Publishes the linked replay family carried by this exact task. */
    private static void addReplayIdentity(JsonObject result,
                                          RuntimeTask task) {
        result.addProperty("replayGroupId", task.replayGroupId);
        result.addProperty("linkedReplayRole", task.linkedReplayRole);
        result.addProperty("familySnapshotDigest",
                task.familySnapshotDigest);
        result.addProperty("topologyEpoch", task.topologyEpoch);
    }

    /** Records that an activation published nothing, and why. */
    static void writeSkipped(RuntimeTask activation, String skipKind,
                                     String reason, JsonObject evidence) {
        JsonObject result = new JsonObject();
        result.addProperty("event", "CONCOLIC_REGION_SKIPPED");
        result.addProperty("schemaVersion", 1);
        result.addProperty("taskId", activation.taskId);
        addReplayIdentity(result, activation);
        result.addProperty("skipKind", skipKind);
        result.addProperty("reason", reason);
        if (evidence != null) {
            for (Map.Entry<String, JsonElement> entry
                    : evidence.entrySet()) {
                result.add(entry.getKey(), entry.getValue());
            }
        }
        appendResult(result);
    }

    static boolean appendResult(JsonObject result) {
        return appendResultLine(configuration().resultFile, result);
    }

    /**
     * Appends one durable result without depending on interruptible NIO
     * channels.
     */
    static boolean appendResultLine(Path output, JsonObject result) {
        synchronized (WRITE_LOCK) {
            try {
                Path parent = output.toAbsolutePath().getParent();
                if (parent != null) {
                    Files.createDirectories(parent);
                }
                try (BufferedWriter writer = new BufferedWriter(
                        new OutputStreamWriter(new FileOutputStream(
                                output.toFile(), true),
                                StandardCharsets.UTF_8))) {
                    writer.write(GSON.toJson(result));
                    writer.newLine();
                }
                return true;
            } catch (IOException exception) {
                System.err.println("Causynth could not write concolic result: "
                        + exception);
                return false;
            }
        }
    }

    static boolean jsonObjectEnvelope(String value) {
        if (value == null) return false;
        int start = 0;
        int end = value.length() - 1;
        while (start <= end && Character.isWhitespace(value.charAt(start))) {
            start++;
        }
        while (end >= start && Character.isWhitespace(value.charAt(end))) {
            end--;
        }
        return start <= end && value.charAt(start) == '{'
                && value.charAt(end) == '}';
    }
}
