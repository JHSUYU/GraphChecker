package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.exactInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.shallowCopy;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.exactText;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/** Converts one VM execution row into one semantic path row. */
public final class ConcolicSummaryImporter {
    static final String MANUAL_INPUT_OBSERVATION_FIELD =
            "manualSymbolicInputObservations";
    static final String MANUAL_INPUT_OBSERVATION_KIND =
            "MANUAL_SYMBOLIC_INPUT_OBSERVATION";
    static final String MANUAL_INPUT_OBSERVATION_AUTHORITY =
            "EXACT_PLANNED_SYMBOLIZATION_ACTION_V1";
    private static final Set<String> MANUAL_INPUT_OBSERVATION_MEMBERS =
            Collections.unmodifiableSet(new LinkedHashSet<>(java.util.Arrays
                    .asList("schemaVersion", "kind", "authority", "portId",
                            "actionDigest", "plannedOccurrenceId",
                            "occurrenceId", "symbol", "fieldPath",
                            "fieldSignature", "expression", "rawSymbol",
                            "javaType", "minted", "reused")));
    /**
     * Members a mint row may add, and what they mean.
     *
     * <p>The publication of a mint is one shape.  A manual mint now states
     * the value it read, exactly as a configured source does -- the runtime
     * suppresses it only for a modelled mint, where the replay was handed
     * the value instead of reading one -- so the member is expected and may
     * be absent.  The reader required an <em>exact</em> member set, so the
     * addition read as an unsupported schema and refused six of laneVM13's
     * seed paths.  Required members are still required and an unknown member
     * is still a refusal; what changed is that a stated value is not an
     * unknown member.</p>
     */
    private static final Set<String> MANUAL_INPUT_OBSERVATION_OPTIONAL =
            Collections.unmodifiableSet(new LinkedHashSet<>(java.util.Arrays
                    .asList("recordedValue")));

    /** The members one observation carries beyond the required set. */
    private static Set<String> extraMembers(JsonObject observation) {
        Set<String> extra = new LinkedHashSet<>(observation.keySet());
        extra.removeAll(MANUAL_INPUT_OBSERVATION_MEMBERS);
        return extra;
    }

    private static final String AUXILIARY_PATH_CONDITION_FIELD =
            "auxiliaryPathCondition";
    private static final String SELECTED_BRANCH_AND_AUXILIARY_AUTHORITY =
            "VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1";
    private static final String AUXILIARY_PATH_CONDITION_KIND =
            "CONCOLIC_AUXILIARY_PATH_CONDITION";
    /** How many conditions the VM actually serialized into the window.
     *  Equal to the declared count: the serializer emits one truncation
     *  marker per remaining index, so an absent or disagreeing count is a
     *  malformed envelope. */
    private static final String EMITTED_CONDITION_COUNT =
            "emittedConditionCount";
    private static final String AUXILIARY_PATH_CONDITION_AUTHORITY =
            "VM_THREAD_AUXILIARY_PATH_CONDITION_V1";
    private static final String CONFIGURED_SOURCE_PHASE_OBSERVATIONS =
            "configuredSourcePhaseObservations";
    private static final String CONFIGURED_SOURCE_PHASE_GAPS =
            "configuredSourcePhaseGaps";
    /** The runtime facts one observation must state.  Everything else in the
     * row restates the catalog row {@code matchedPhaseId} already names. */
    private static final Set<String> CONFIGURED_SOURCE_PHASE_OBSERVATION_FIELDS =
            Collections.unmodifiableSet(new LinkedHashSet<>(java.util.Arrays
                    .asList("schemaVersion", "kind", "authority",
                            "observationIndex", "matchedPhaseId",
                            "ownerCallId", "invocationId")));

    /** A {@code symbolizedInputs} entry that is not one mint row. */
    private static final String SYMBOLIZED_INPUT_ROW_MALFORMED =
            "SYMBOLIZED_INPUT_ROW_MALFORMED";
    /**
     * A declared configured source this execution reached and left with no
     * symbolic root of its own.
     */
    private static final String RESULT_SCHEMA_UNSUPPORTED =
            "CONCOLIC_RESULT_SCHEMA_UNSUPPORTED";
    private static final String RESULT_ACTIVATION_TUPLE_MALFORMED =
            "CONCOLIC_RESULT_ACTIVATION_TUPLE_MALFORMED";
    private static final String RESULT_REPLAY_GROUP_MISSING =
            "CONCOLIC_RESULT_REPLAY_GROUP_MISSING";
    private static final String VM_SUMMARY_ACTIVATION_MISMATCH =
            "VM_SUMMARY_ACTIVATION_MISMATCH";

    private ConcolicSummaryImporter() {
    }

    /**
     * One replay execution's raw result, decoded exactly once.
     *
     * <p>README "Minimal cross-stage contract": the importer is the sole
     * decoder of a raw region result.  The topology delta, the worklist and
     * the composer receive this object or the case rows built from it, and
     * never re-read the result JSON.  A {@code null} member was not stated by
     * the result at all, which is not the same as being stated empty.</p>
     */
    static final class ResultRow {
        /** Zero-based result line, or negative when there is no result. */
        final int line;
        final String taskId;
        /** Linked replays share this exact VM-allocation scope. */
        final String boundarySessionScope;
        final String replayGroupId;
        final String event;
        final String skipKind;
        final String skipReason;
        final String exitKind;
        final String exceptionType;
        final JsonObject engine;
        final JsonObject pathCut;
        final JsonObject resourceCut;
        final JsonArray unresolvedInputs;
        final JsonArray branchMappings;
        final JsonArray branchCoverageGaps;
        final boolean statesBranchEvidence;
        /** One row per entry of a declared mint site. */
        final List<JsonObject> symbolizedInputs;
        /** Every mint this execution filed at a declared hook site. */
        final List<JsonObject> symbolicSourceEvidence;
        /** Why that ledger did not decode, or "" when it did. */
        final String symbolicSourceEvidenceIssue;
        final JsonArray vmHandoffs;
        final JsonArray sharedFieldVersions;
        final JsonArray sourcePhaseObservations;
        final JsonArray sourcePhaseGaps;
        /** A stated hook-ledger member that is not an array. */
        final boolean sourcePhaseLedgerMalformed;
        final JsonObject replayLoopBodies;
        final JsonObject loopBackedgeTraversals;
        final JsonArray loopCardinalities;
        final JsonArray loopCardinalityGaps;
        final JsonArray rpcHandoffGaps;
        final JsonArray sharedStateGaps;
        final JsonElement targetReach;
        /** Sites decided symbolically, and sites decided either way. */
        final Set<String> decidedBranchSites;
        final SortedSet<String> observedBranchSites;
        /** The named shape refusal, or "" when the row decoded. */
        final String refusal;
        /** OCC-1: this result activation's required positive ordinal. */
        final int activationOrdinal;
        /** OCC-1: the planned address every activation of the task shares. */
        final String plannedOccurrenceId;
        /** OCC-1: this activation's own occurrence identity. */
        final String rowOccurrenceId;
        /** OCC-1: whether this activation exited through the target throw;
         *  null on a non-target goal. */
        final Boolean targetReachedFlag;

        ResultRow(JsonObject raw, int line) {
            this.line = line;
            this.taskId = optionalString(raw, "taskId");
            this.replayGroupId = optionalString(raw, "replayGroupId");
            this.event = optionalString(raw, "event");
            this.activationOrdinal = exactInteger(raw,
                    PathObservation.ACTIVATION_ORDINAL, -1);
            this.plannedOccurrenceId = exactText(raw,
                    PathObservation.PLANNED_OCCURRENCE_ID);
            this.rowOccurrenceId = exactText(raw, "occurrenceId");
            this.targetReachedFlag =
                    raw.has(PathObservation.TARGET_REACHED)
                    ? Boolean.valueOf(optionalBool(raw,
                            PathObservation.TARGET_REACHED, false))
                    : null;
            this.skipKind = optionalString(raw, "skipKind");
            this.skipReason = optionalString(raw, "reason");
            this.exitKind = optionalString(raw, "exitKind");
            this.exceptionType = optionalString(raw, "exceptionType");
            this.engine = object(raw, "engineSummary");
            this.boundarySessionScope = replayGroupId.isEmpty()
                    ? "" : "replay-group:" + replayGroupId;
            this.pathCut = raw.has("pathCut") ? object(raw, "pathCut") : null;
            this.resourceCut = raw.has("replayResourceCut")
                    ? object(raw, "replayResourceCut") : null;
            this.unresolvedInputs = array(raw, "unresolvedInputs");
            this.branchMappings = array(raw, "branchMappings");
            this.branchCoverageGaps = array(raw, "branchCoverageGaps");
            this.statesBranchEvidence = raw.has("branchMappings");
            this.vmHandoffs = raw.has(VmHandoffEvidence.FIELD)
                    ? array(raw, VmHandoffEvidence.FIELD) : null;
            this.sharedFieldVersions = array(raw, "sharedFieldVersions");
            this.sourcePhaseObservations = statedArray(raw,
                    CONFIGURED_SOURCE_PHASE_OBSERVATIONS);
            this.sourcePhaseGaps = statedArray(raw,
                    CONFIGURED_SOURCE_PHASE_GAPS);
            this.sourcePhaseLedgerMalformed =
                    raw.has(CONFIGURED_SOURCE_PHASE_OBSERVATIONS)
                            && sourcePhaseObservations == null
                            || raw.has(CONFIGURED_SOURCE_PHASE_GAPS)
                            && sourcePhaseGaps == null;
            this.replayLoopBodies = object(raw, "replayLoopBodies");
            this.loopBackedgeTraversals = object(raw,
                    "loopBackedgeTraversals");
            this.loopCardinalities = array(raw,
                    LoopBoundPolicy.LOOP_CARDINALITIES);
            this.loopCardinalityGaps = array(raw,
                    LoopBoundPolicy.LOOP_CARDINALITY_GAPS);
            this.rpcHandoffGaps = array(raw, "rpcHandoffGaps");
            this.sharedStateGaps = array(raw, "sharedStateGaps");
            this.targetReach = raw.get(
                    PathObservation.TargetReachEvent.FIELD);
            this.decidedBranchSites = siteIds(branchMappings);
            this.observedBranchSites =
                    new TreeSet<>(decidedBranchSites);
            String refused = resultShapeRefusal(raw, event,
                    activationOrdinal, plannedOccurrenceId,
                    rowOccurrenceId, replayGroupId);
            List<JsonObject> mints = new ArrayList<>();
            for (JsonElement element : array(raw, "symbolizedInputs")) {
                JsonObject mint = element.isJsonObject()
                        ? element.getAsJsonObject() : null;
                Boolean reused = mint == null ? null
                        : exactBoolean(mint, SymbolicSourceEvidence.REUSED);
                if (reused == null || !reused
                        && optionalString(mint, SymbolicSourceEvidence.SYMBOL)
                        .isEmpty()) {
                    if (refused.isEmpty()) {
                        refused = SYMBOLIZED_INPUT_ROW_MALFORMED;
                    }
                    break;
                }
                mints.add(mint);
            }
            this.symbolizedInputs = mints;
            List<JsonObject> minted = Collections.emptyList();
            String malformed = "";
            try {
                minted = SymbolicSourceEvidence.eventsOf(raw);
            } catch (IllegalArgumentException rejected) {
                malformed = firstNonBlank(rejected.getMessage(), "UNKNOWN");
            }
            this.symbolicSourceEvidence = minted;
            this.symbolicSourceEvidenceIssue = malformed;
            this.refusal = refused;
        }

        /** The matched catalog rows this execution's hook ledger named. */
        SortedSet<String> observedSourcePhases() {
            SortedSet<String> result = new TreeSet<>();
            for (JsonElement element : sourcePhaseObservations) {
                if (!element.isJsonObject()) continue;
                String matched = optionalString(element.getAsJsonObject(),
                        "matchedPhaseId");
                if (!matched.isEmpty()) result.add(matched);
            }
            return result;
        }

        private static JsonArray statedArray(JsonObject raw, String field) {
            JsonElement stated = raw.get(field);
            return stated != null && stated.isJsonArray()
                    ? stated.getAsJsonArray() : null;
        }

        private static Set<String> siteIds(JsonArray rows) {
            Set<String> result = new LinkedHashSet<>();
            for (JsonElement element : rows) {
                if (!element.isJsonObject()) continue;
                String site = optionalString(element.getAsJsonObject(), "siteId");
                if (!site.isEmpty()) result.add(site);
            }
            return result;
        }
    }

    public static void main(String[] args) throws Exception {
        Map<String, String> options = CliArgs.pairs(args);
        Path results = required(options, "results");
        Path tasks = required(options, "task-plan");
        Path runtimePlan = required(options, "runtime-plan");
        Path output = Paths.get(firstNonBlank(options.get("output"),
                ArtifactIO.sibling(results,
                        "concolic_region_summaries.jsonl").toString()));
        Path diagnostics = Paths.get(firstNonBlank(
                options.get("diagnostics"),
                ArtifactIO.sibling(results,
                        "concolic_import_diagnostics.jsonl").toString()));
        Set<String> regions = regionIds(RuntimePlanArtifact.read(
                runtimePlan).regions());
        String iterationId = requiredValue(options, "iteration-id");
        ImportResult imported = importSummaries(results, tasks, regions,
                output, diagnostics, iterationId);
        if (imported.diagnosticCount > 0) {
            try (BufferedReader reader = Files.newBufferedReader(diagnostics,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    System.err.println("[concolic-import] " + line);
                }
            }
        }
        if (!imported.contractViolations.isEmpty()) {
            System.err.println("[concolic-import] publication contract: "
                    + imported.contractViolations.size()
                    + " blocking row(s); the corpus does not carry what the"
                    + " plan asked for, so the campaign stops here rather"
                    + " than meeting it as an unexecutable worklist");
            for (String line : PublicationContract.table(
                    imported.contractViolations)) {
                System.err.println("[concolic-import]   " + line);
            }
            System.exit(3);
        }
        if (imported.validSummaryCount == 0
                && imported.rawResultCount > 0) {
            System.exit(2);
        }
    }

    static ImportResult importSummaries(
            Path resultsFile, Path taskPlanFile, Set<String> regions,
            Path outputFile, Path diagnosticFile,
            String iterationId) throws IOException {
        Map<String, ExecutionTask> tasks = taskIndex(
                ArtifactIO.readJsonl(taskPlanFile));
        SharedExpressionTable.Decoder expressions =
                new SharedExpressionTable.Decoder();
        List<JsonObject> rawResults = decodeVmExpressionArtifacts(
                ArtifactIO.readJsonl(resultsFile), expressions);
        List<JsonObject> summaries = new ArrayList<>();
        IdentityHashMap<JsonObject, ResultRow> sourceRows =
                new IdentityHashMap<>();
        List<JsonObject> diagnostics = new ArrayList<>();
        Set<String> hashes = new LinkedHashSet<>();
        // Every re-plan receives a new iteration id. Unlike a digest of the
        // task rows, it stays stable while linked replays add case tasks for
        // the same topology epoch.
        String topologyEpoch = iterationId;
        // OCC-1: which activations each task published, decided once over the
        // whole file.  Two questions are task-level and cannot be answered
        // while importing one row: whether an ordinal was published twice,
        // and whether any activation of a target task reached the target.
        ActivationCensus census = ActivationCensus.of(rawResults);
        census.refusals(tasks, diagnostics);

        for (int index = 0; index < rawResults.size(); index++) {
            // The one decode of this raw result; nothing below re-reads it.
            ResultRow row = new ResultRow(rawResults.get(index), index);
            if (!"CONCOLIC_REGION_RESULT".equals(row.event)) {
                String code = skippedEventCode(row);
                diagnostics.add(diagnostic(row, code,
                        skippedEventDetail(row)));
                continue;
            }
            ExecutionTask task = tasks.get(row.taskId);
            if (task == null) {
                diagnostics.add(diagnostic(row,
                        "UNKNOWN_EXECUTION_TASK", row.taskId));
                continue;
            }
            if (!regions.contains(task.regionId())) {
                diagnostics.add(diagnostic(row,
                        "UNKNOWN_REGION", task.regionId()));
                continue;
            }
            // A topology-divergent bundle is not epoch e's evidence.  Its
            // paths are exact about a topology this epoch's plan does not
            // address, and the anchor's own address may shift under that
            // topology, so "the same anchor" is not guaranteed across the
            // two.  It is kept whole, named by its own rows, and it
            // instantiates epoch e+1 instead of extending this one.
            if (topologyDivergences(row, task, diagnostics)) {
                continue;
            }
            JsonObject summary = importRow(row, task, hashes,
                    diagnostics, topologyEpoch, expressions);
            if (summary != null) {
                // No renaming pass: a location is named by the object the VM
                // filed it under, and that name is already the one the read
                // nodes carry.
                summaries.add(summary);
                sourceRows.put(summary, row);
            }
        }
        for (int index = 0; index < summaries.size(); index++) {
            summaries.set(index, expressions.compact(summaries.get(index)));
        }
        // A planned activation that produced no row at all is the plainest
        // "planned event that did not occur"; it is named, never dropped.

        // An occurrence one run did not answer is not a refusal when another
        // run of the same replay did.  A workload with two JVM epochs on one
        // node asks both about every task addressed at that node, and the
        // epoch that never registered the addressed one says so -- that is a
        // statement about which JVM was asked, not about the region.  It
        // stays only where no run answered the task at all.
        Set<String> answered = new LinkedHashSet<>();
        for (JsonObject summary : summaries) {
            answered.add(optionalString(summary, "taskId"));
        }
        diagnostics.removeIf(row ->
                "REGION_OCCURRENCE_ANCHOR_UNMATCHED".equals(
                        optionalString(row, "code"))
                        && answered.contains(optionalString(row, "taskId")));

        // The contract runs last, over what was actually written: every
        // check it makes is a statement the corpus can make about itself,
        // and making it here is what keeps a missing publication from
        // arriving at EXPLORE as an unexecutable worklist.
        List<JsonObject> contract = PublicationContract.check(tasks,
                summaries, diagnostics);
        diagnostics.addAll(contract);

        ArtifactIO.replaceJsonl(outputFile, summaries);
        ArtifactIO.replaceJsonl(diagnosticFile, diagnostics);
        return new ImportResult(rawResults.size(), summaries.size(),
                diagnostics.size(), contract);
    }

    /** Converts the VM transport DAG, then interns portable content anchors. */
    private static List<JsonObject> decodeVmExpressionArtifacts(
            List<JsonObject> rows,
            SharedExpressionTable.Decoder expressions) throws IOException {
        List<JsonObject> portable = new ArrayList<>(rows.size());
        for (int index = 0; index < rows.size(); index++) {
            JsonObject row = rows.get(index);
            try {
                portable.add(VmExpressionTable.usesNativeDag(row)
                        ? VmExpressionTable.portable(row) : row);
            } catch (RuntimeException malformed) {
                throw new IOException("malformed VM expression DAG at result "
                        + "row " + (index + 1), malformed);
            }
        }
        try {
            return expressions.expandAll(portable);
        } catch (RuntimeException malformed) {
            throw new IOException("malformed content-addressed expression "
                    + "table in concolic results", malformed);
        }
    }

    /** One mutable record shell around an otherwise immutable value DAG. */
    private static JsonObject shallowCopyWithout(JsonObject source,
                                                 String omitted) {
        JsonObject result = new JsonObject();
        if (source == null) return result;
        for (Map.Entry<String, JsonElement> field : source.entrySet()) {
            if (!field.getKey().equals(omitted)) {
                result.add(field.getKey(), field.getValue());
            }
        }
        return result;
    }

    /** Imports one raw VM result, or refuses it under one named gap.
     *
     * @return the admitted summary, or {@code null} when the row was refused
     */
    /**
     * OCC-1: the activations each task published, counted once over the whole
     * results file.
     *
     * <p>Three findings are task-level and cannot be made while importing a
     * single row: an ordinal published twice (the runtime's activation
     * counter is not a counter), a target task none of whose activations
     * reached the target, and a planned task the run left no row for at all.
     * All three are named here and all three stay refusals -- the rows
     * themselves are still imported, so a reader can see what the
     * activations did instead of being handed an empty member set.</p>
     *
     * <p>The third is only answerable against the plan: a task whose region
     * was skipped still publishes a row and is named by that row's own
     * diagnostic, but a task that published nothing at all appears nowhere
     * in the results and would otherwise leave the selected case set short
     * one region in silence.  A later stage then meets that hole as an
     * unresolvable writer case rather than as a named coverage gap.</p>
     */
    private static final class ActivationCensus {
        private final Map<String, Set<Integer>> ordinalsByTask =
                new LinkedHashMap<>();
        private final Map<String, List<Integer>> duplicatesByTask =
                new LinkedHashMap<>();
        private final Set<String> targetReachedTasks = new LinkedHashSet<>();
        private final Set<String> tasksWithRows = new LinkedHashSet<>();

        private static ActivationCensus of(List<JsonObject> rawResults) {
            ActivationCensus census = new ActivationCensus();
            for (JsonObject raw : rawResults) {
                // Every row this run published for a task answers for it,
                // whatever the row says happened: a skipped region names
                // itself through its own row-level diagnostic.
                String rowTaskId = optionalString(raw, "taskId");
                if (!rowTaskId.isEmpty()) census.tasksWithRows.add(rowTaskId);
                if (!"CONCOLIC_REGION_RESULT".equals(optionalString(raw, "event"))) {
                    continue;
                }
                int ordinal = exactInteger(raw,
                        PathObservation.ACTIVATION_ORDINAL, -1);
                if (ordinal < 1) continue;
                String taskId = optionalString(raw, "taskId");
                if (!census.ordinalsByTask.computeIfAbsent(taskId,
                        ignored -> new LinkedHashSet<>()).add(ordinal)) {
                    census.duplicatesByTask.computeIfAbsent(taskId,
                            ignored -> new ArrayList<>()).add(ordinal);
                }
                // Reaching the target is the selected site having executed,
                // which is what the reach event records.  targetReached is a
                // different fact -- whether the activation left through the
                // annotated throw -- and on a healthy recording it is false
                // at every activation that nonetheless ran the site.  Reading
                // it here refused the healthy disjunct as a missing one.
                if (raw.has(PathObservation.TargetReachEvent.FIELD)) {
                    census.targetReachedTasks.add(taskId);
                }
            }
            return census;
        }

        private void refusals(Map<String, ExecutionTask> tasks,
                              List<JsonObject> diagnostics) {
            for (Map.Entry<String, ExecutionTask> entry : tasks.entrySet()) {
                ExecutionTask task = entry.getValue();
                if (task == null || !task.executable()
                        || tasksWithRows.contains(entry.getKey())) {
                    continue;
                }
                diagnostics.add(taskDiagnostic(entry.getKey(),
                        "REGION_TASK_NO_PUBLISHED_ACTIVATION",
                        "this planned task published no activation and no "
                        + "skip, so its region contributes no case to the "
                        + "selected path set; its anchor names "
                        + task.occurrenceId()));
            }
            for (Map.Entry<String, List<Integer>> entry
                    : duplicatesByTask.entrySet()) {
                diagnostics.add(taskDiagnostic(entry.getKey(),
                        "DUPLICATE_ACTIVATION_ORDINAL",
                        "this task published ordinal(s) " + entry.getValue()
                        + " more than once, so its activations do not name "
                        + "distinct occurrences"));
            }
            for (Map.Entry<String, Set<Integer>> entry
                    : ordinalsByTask.entrySet()) {
                ExecutionTask task = tasks.get(entry.getKey());
                if (task == null
                        || !task.goalKind().capturesTargetReach()
                        || targetReachedTasks.contains(entry.getKey())) {
                    continue;
                }
                diagnostics.add(taskDiagnostic(entry.getKey(),
                        "TARGET_REACH_NO_ACTIVATION_REACHED_TARGET",
                        "none of the " + entry.getValue().size()
                        + " published activation(s) of this target task "
                        + "executed the selected target site"));
            }
        }
    }

    /** A diagnostic about a task rather than about one raw row. */
    private static JsonObject taskDiagnostic(String taskId, String code,
                                             String detail) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", "CONCOLIC_IMPORT_DIAGNOSTIC");
        row.addProperty("code", code);
        row.addProperty("detail", detail);
        row.addProperty("taskId", taskId);
        return row;
    }

    private static JsonObject importRow(
            ResultRow row, ExecutionTask task,
            Set<String> hashes, List<JsonObject> diagnostics,
            String topologyEpoch,
            SharedExpressionTable.Decoder expressions) {
        // The decode already refused an artifact shape this importer does not
        // read; it is a named gap like any other.
        if (!row.refusal.isEmpty()) {
            return refuse(row, row.refusal, row.exitKind, diagnostics);
        }
        // An aborted symbolic execution stops recording branch events and path
        // condition at the point it gave up, and the activation then runs on
        // concretely to whatever exit it reaches.
        JsonObject engine = row.engine;
        String engineTaskId = optionalString(engine, "taskId");
        String engineRegionId = optionalString(engine, "regionId");
        if ((!engineTaskId.isEmpty()
                && !engineTaskId.equals(task.taskId()))
                || (!engineRegionId.isEmpty()
                && !engineRegionId.equals(task.regionId()))) {
            return refuse(row, VM_SUMMARY_ACTIVATION_MISMATCH,
                    "result " + row.taskId + "/" + task.regionId()
                            + " contains VM summary " + engineTaskId + "/"
                            + engineRegionId,
                    diagnostics);
        }
        if (optionalBool(engine, "aborted", false)) {
            return refuse(row, "SYMBOLIC_EXECUTION_ABORTED",
                    firstNonBlank(optionalString(engine, "abortReason"),
                            "UNSPECIFIED"), diagnostics);
        }
        String exitKind = row.exitKind;
        boolean hasCut = row.pathCut != null || row.resourceCut != null;
        boolean boundedPathExit = "BOUNDED".equals(exitKind);
        if ("CUT".equals(exitKind)
                || hasCut && !boundedPathExit) {
            // The two ledgers cut for opposite reasons and are answered by
            // opposite work: an unroll bound says the path space was too wide
            // to walk, a resource cap says a service loop outlasted the replay
            // budget.
            boolean resourceCut = row.resourceCut != null;
            String cutDetail = (resourceCut ? row.resourceCut : row.pathCut)
                    .toString();
            // No admitted bounded prefix exists here.  Keep the cut as an
            // explicit gap rather than inventing an output relation.
            return refuse(row, resourceCut ? "REPLAY_LOOP_RESOURCE_CAP"
                            : "LOOP_BOUND_PATH_CUT", cutDetail,
                    diagnostics);
        }
        List<String> issues = new ArrayList<>();
        JsonArray phaseNotes = new JsonArray();
        for (JsonElement unresolved : row.unresolvedInputs) {
            String note = unresolved == null ? "" : unresolved.toString();
            // A replay that reached a configured-source phase the plan did
            // not address has still answered its roots: the mint it made
            // carries the same phase and the same raw symbol as the
            // recording's, and this activation's decisions are decisions
            // about that root.  How many times a hook was reached is a fact
            // about the path the replay took -- which is the thing a flip
            // changes on purpose -- so it is recorded beside the summary.
            // Refusing the activation for it threw away the only evidence
            // tying the root to the outcome the flip produced.
            if (note.contains("CONFIGURED_SOURCE_PHASE_EXTRA")
                    || note.contains("CONFIGURED_SOURCE_PHASE_MISSING")) {
                phaseNotes.add(note);
                continue;
            }
            issues.add("UNRESOLVED_INPUT:" + unresolved);
        }

        boolean relationOnlySeed = relationOnlySeed(task);
        // A relation-only seed that carries no decision at all still imports
        // as empty.
        boolean anyBranchDecision =
                SemanticPath.hasAdmissibleBranchDecision(
                        row.branchMappings);
        boolean pathConditionOmitted = optionalBool(engine,
                "pathConditionOmitted", false);
        boolean branchAndAuxiliarySummary =
                SELECTED_BRANCH_AND_AUXILIARY_AUTHORITY.equals(
                        optionalString(engine, "pathConditionAuthority"));
        if (pathConditionOmitted) {
            JsonElement omittedPath = engine.get("pathCondition");
            if (omittedPath == null || !omittedPath.isJsonArray()
                    || omittedPath.getAsJsonArray().size() != 0) {
                issues.add("OMITTED_PATH_CONDITION_NOT_EMPTY");
            }
            if (!branchAndAuxiliarySummary) {
                issues.add("OMITTED_PATH_CONDITION_AUTHORITY_MISSING");
            }
            if (!optionalBool(engine, "active", false)) {
                issues.add("OMITTED_PATH_CONDITION_ENGINE_INACTIVE");
            }
        } else if (optionalBool(engine, "active", false)) {
            // Only the selected branch plus bounded auxiliary channel is
            // admitted.
            issues.add("AMBIENT_PATH_CONDITION_NOT_ADMITTED");
        }
        if (!optionalBool(engine, "complete", false)) {
            issues.add("VM_SUMMARY_INCOMPLETE:"
                    + optionalString(engine, "abortReason"));
        }
        // One shape, one reader.
        SemanticPath path = SemanticPath.fromSelectedEvidence(engine,
                row.branchMappings, issues);
        JsonArray mappings = relationOnlySeed && !anyBranchDecision
                ? new JsonArray()
                : branchMappings(row, task, path, issues);
        ReplayAdmission replayAdmission = relationOnlySeed
                ? ReplayAdmission.NONE
                : branchReplayAdmission(row, task, mappings);
        if (!replayAdmission.mismatch.isEmpty()) {
            return refuse(row, "BRANCH_REPLAY_MISMATCH",
                    replayAdmission.mismatch, diagnostics);
        }
        JsonObject targetReach = admittedTargetReach(row, task,
                path.expressions, mappings, replayAdmission,
                diagnostics);
        if (targetReach == null) return null;
        PathLoopCounts loopCounts = pathLoopCounts(row, task);
        if (!loopCounts.refusal.isEmpty()) {
            return refuse(row, LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND,
                    loopCounts.refusal, diagnostics);
        }
        JsonArray alignmentGaps = alignmentGaps(row);
        JsonObject recordedSharedState =
                recordedSharedState(row, alignmentGaps);
        List<JsonObject> vmHandoffEvents =
                vmHandoffEvents(row, task, topologyEpoch, alignmentGaps);
        // The catalog of declared mint SITES, decoded once by the task row.
        List<ConfiguredSourcePhaseContract.Occurrence> mintSites =
                task.configuredSourcePhases();
        validateConfiguredSourcePhaseObservations(row, mintSites, issues);
        JsonArray symbolicSources = symbolicSourceEvidence(row,
                mintSites, issues);
        ManualInputEvidence manualInputs = manualSymbolicSourceEvidence(row,
                task, issues);
        for (JsonElement manual : manualInputs.sources) {
            symbolicSources.add(manual);
        }
        JsonElement replayContract = task.replayContract();

        JsonObject summary = new JsonObject();
        summary.addProperty("schemaVersion", 1);
        summary.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        summary.addProperty("goalId", task.goalId());
        summary.addProperty("taskId", task.taskId());
        summary.addProperty("sourceKey", task.sourceKey());
        summary.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, topologyEpoch);
        summary.addProperty("boundarySessionScope",
                row.boundarySessionScope);
        if (!row.replayGroupId.isEmpty()) {
            summary.addProperty("replayGroupId", row.replayGroupId);
        }
        summary.addProperty("regionId", task.regionId());
        // Current result rows always carry the exact activation tuple. The
        // importer copies it; it does not reconstruct old coarse occurrences.
        summary.addProperty("occurrenceId", row.rowOccurrenceId);
        summary.addProperty(PathObservation.ACTIVATION_ORDINAL,
                row.activationOrdinal);
        summary.addProperty(PathObservation.PLANNED_OCCURRENCE_ID,
                row.plannedOccurrenceId);
        if (task.goalKind().capturesTargetReach()) {
            summary.addProperty(PathObservation.TARGET_REACHED,
                    row.targetReachedFlag != null && row.targetReachedFlag);
        }
        summary.addProperty("relationKey", task.relationKey());
        task.loopBound().writeTo(summary);
        task.goalKind().writeToTask(summary);
        if (symbolicSources.size() > 0) {
            summary.add(SymbolicSourceEvidence.FIELD, symbolicSources);
        }
        if (manualInputs.observations.size() > 0) {
            summary.add(MANUAL_INPUT_OBSERVATION_FIELD,
                    manualInputs.observations);
        }
        // Graph edges describe topology; receiver boundaries carry values.

        summary.add("pathCondition", path.expressions);
        summary.add("branchMappings", mappings);
        if (targetReach.size() > 0) {
            summary.add(PathObservation.TargetReachEvent.FIELD,
                    targetReach);
        }
        if (loopCounts.counts.size() > 0) {
            summary.add(LoopBoundPolicy.PATH_LOOP_COUNTS,
                    loopCounts.counts);
        }
        if (loopCounts.gaps.size() > 0) {
            summary.add(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS,
                    loopCounts.gaps);
        }
        if (alignmentGaps.size() > 0) {
            summary.add("alignmentGaps", alignmentGaps);
        }
        if (phaseNotes.size() > 0) {
            summary.add("configuredSourcePhaseGaps", phaseNotes);
        }
        if (recordedSharedState.size() > 0) {
            summary.add(SharedStateEvidence.RECORDED_FIELD,
                    recordedSharedState);
        }
        VmHandoffEvidence.writeTo(summary, vmHandoffEvents);
        boolean boundedExit = "BOUNDED".equals(exitKind);
        summary.addProperty("normalExit", boundedExit
                || "NORMAL".equals(exitKind));
        summary.addProperty("boundedExit", boundedExit);
        summary.addProperty("exceptionType", row.exceptionType);
        if (!issues.isEmpty()) {
            return refuse(row, replayContract == null
                            ? "REGION_PATH_ADMISSION_REJECTED"
                            : "PATH_REPLAY_ADMISSION_REJECTED",
                    String.join(";", issues), diagnostics);
        }

        // A local case is the region's control path.  Runtime observation
        // fields and propagated expression payloads remain in summaryId, but
        // never split this identity across replays or family snapshots.
        summary.addProperty(LocalCaseIdentity.FIELD,
                LocalCaseIdentity.compute(summary));

        JsonObject semantic = shallowCopyWithout(summary, "taskId");
        // A summary id names the complete execution observation and is
        // intentionally independent of its storage encoding.  Expression
        // anchors identify value nodes only; they never become case or
        // observation identity.
        String hash = expressions.semanticDigest(semantic);
        if (!hashes.add(hash)) {
            return refuse(row, "DUPLICATE_SUMMARY", hash, diagnostics);
        }
        summary.addProperty("summaryId",
                "SUMMARY." + task.regionId() + "." + hash);
        if (!issues.isEmpty()) {
            diagnostics.add(diagnostic(row, "INCOMPLETE_RELATION",
                    String.join(";", issues)));
        }
        // Exact typed delivery evidence and recorded state versions are
        // different evidence classes from the guarded case itself, so the
        // delta names each of them once beside it.
        return summary;
    }

    /** Validates the runtime hook ledger against the task's frozen catalog of
     * mint SITES.  Which minted value reaches which read is decided by the
     * VM at replay, so nothing here matches a predicted subsequence. */
    private static void validateConfiguredSourcePhaseObservations(
            ResultRow row,
            List<ConfiguredSourcePhaseContract.Occurrence> catalog,
            List<String> issues) {
        boolean stated = row.sourcePhaseObservations != null
                && row.sourcePhaseGaps != null;
        if (!catalog.isEmpty() && !stated) {
            issues.add("SYMBOLIC_SOURCE_PHASE_RUNTIME_LEDGER_MISSING");
            return;
        }
        if (row.sourcePhaseLedgerMalformed) {
            issues.add("SYMBOLIC_SOURCE_PHASE_RUNTIME_LEDGER_MALFORMED");
            return;
        }
        if (row.sourcePhaseGaps != null) {
            for (JsonElement gap : row.sourcePhaseGaps) {
                // How many times a replay reached a root's hook is a
                // property of the path it took, and taking a different path
                // is what a flip is for: a replay that runs the hook twice
                // where the recording ran it once has minted the same root
                // at the same site, under the same phase id, and answered
                // it.  That is recorded beside the summary.  Reaching it
                // FEWER times is a different statement -- a root the plan
                // expected may have gone unminted -- and still refuses.
                if ("EXTRA".equals(optionalString(
                        gap.isJsonObject() ? gap.getAsJsonObject()
                                : new JsonObject(), "gapKind"))) {
                    continue;
                }
                issues.add("SYMBOLIC_SOURCE_PHASE_RUNTIME_GAP:"
                        + CanonicalJson.render(gap));
            }
        }
        if (row.sourcePhaseObservations == null) return;

        Set<String> declaredPhases = new LinkedHashSet<>();
        for (ConfiguredSourcePhaseContract.Occurrence phase : catalog) {
            declaredPhases.add(phase.phaseId());
        }
        Set<String> exactObserved = new LinkedHashSet<>();
        Set<Long> invocationIds = new LinkedHashSet<>();
        int expectedIndex = 1;
        for (JsonElement element : row.sourcePhaseObservations) {
            if (!element.isJsonObject()) {
                issues.add("SYMBOLIC_SOURCE_PHASE_OBSERVATION_MALFORMED:"
                        + expectedIndex++);
                continue;
            }
            JsonObject observation = element.getAsJsonObject();
            int index = exactInteger(observation, "observationIndex", -1);
            // The row states exactly the seven runtime facts.  Anything else
            // it could carry is the catalog row matchedPhaseId already names,
            // so an extra member is a malformed row, not a tolerated one.
            boolean exactSchema =
                    CONFIGURED_SOURCE_PHASE_OBSERVATION_FIELDS.equals(
                            observation.keySet())
                    && exactInteger(observation, "schemaVersion", -1) == 1
                    && "CONFIGURED_SOURCE_PHASE_OBSERVATION".equals(
                    optionalString(observation, "kind"))
                    && "EXACT_ACTIVE_CALL_SITE_REPLAY_V1".equals(
                    optionalString(observation, "authority"))
                    && index == expectedIndex;
            expectedIndex++;
            if (!exactSchema) {
                issues.add("SYMBOLIC_SOURCE_PHASE_OBSERVATION_MALFORMED:"
                        + index);
                continue;
            }
            String phaseId = optionalString(observation, "matchedPhaseId");
            long invocationId = positiveExactLong(observation,
                    "invocationId");
            if (!declaredPhases.contains(phaseId)
                    || !exactObserved.add(phaseId)
                    || positiveExactLong(observation, "ownerCallId") <= 0L
                    || invocationId <= 0L
                    || !invocationIds.add(invocationId)) {
                issues.add("SYMBOLIC_SOURCE_PHASE_OBSERVATION_MISMATCH:"
                        + phaseId);
            }
        }
    }

    private static long positiveExactLong(JsonObject row, String field) {
        JsonElement value = row == null ? null : row.get(field);
        try {
            return value == null || !value.isJsonPrimitive()
                    || !value.getAsJsonPrimitive().isNumber()
                    ? -1L : new java.math.BigDecimal(
                    value.getAsString()).longValueExact();
        } catch (RuntimeException malformed) {
            return -1L;
        }
    }

    /** Decodes the aggregate runtime counters as one replay path's loop-count
     * vector. */
    private static PathLoopCounts pathLoopCounts(
            ResultRow source, ExecutionTask task) {
        PathLoopCounts result = new PathLoopCounts();
        JsonObject fixedBodies = source.replayLoopBodies;
        JsonObject conditionBodies = source.loopBackedgeTraversals;
        Set<String> decidedSites = source.decidedBranchSites;
        for (JsonElement element : array(task.json(),
                BoundedLoopComposition.PLAN_FIELD)) {
            if (!element.isJsonObject()) continue;
            JsonObject declaration = element.getAsJsonObject();
            String loopSiteId = optionalString(declaration,
                    LoopBoundPolicy.LOOP_SITE_ID);
            String classification = optionalString(declaration,
                    LoopBoundPolicy.LOOP_CLASSIFICATION);
            if (loopSiteId.isEmpty()) {
                result.gap(LoopBoundPolicy.PATH_LOOP_COUNT_MISSING, "",
                        "retained loop declares no loopSiteId");
                continue;
            }
            int bound = 0;
            if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(
                    classification)) {
                bound = task.loopBound().maxBackedgeTraversals(loopSiteId);
                JsonElement stated = declaration.get(
                        LoopBoundPolicy.LOOP_BODY_BOUND);
                if (stated != null && (!stated.isJsonPrimitive()
                        || !stated.getAsJsonPrimitive().isNumber()
                        || stated.getAsInt() != bound)) {
                    result.refusal = loopSiteId + " retained row states K_L="
                            + stated + " but task loopBound states K_L="
                            + bound;
                    return result;
                }
            }
            String runtimeLoopId = runtimeLoopId(declaration);
            boolean controlObserved = false;
            for (JsonElement site : array(declaration,
                    LoopBoundPolicy.LOOP_CONTROL_SITE_IDS)) {
                if (site.isJsonPrimitive()
                        && decidedSites.contains(site.getAsString())) {
                    controlObserved = true;
                }
            }
            if (decidedSites.contains(loopSiteId)) controlObserved = true;
            JsonObject bodies = LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                    .equals(classification) ? fixedBodies : conditionBodies;
            int bodyCount = sparseLoopCount(bodies, runtimeLoopId);
            if (bodyCount < 0 && !controlObserved) bodyCount = 0;
            if (bodyCount < 0) {
                result.gap(LoopBoundPolicy.PATH_LOOP_COUNT_MISSING,
                        loopSiteId, "declared loop control executed but "
                                + (LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                                .equals(classification)
                                ? "replayLoopBodies" : "loopBackedgeTraversals")
                                + " names no matching "
                                + "runtime loop id");
                continue;
            }
            if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(
                    classification) && bodyCount > bound) {
                result.refusal = loopSiteId + " executed " + bodyCount
                        + " bodies outside declared 0.." + bound;
                return result;
            }
            JsonObject row = shallowCopy(declaration);
            if (LoopBoundPolicy.LOOP_CONDITION_BOUNDED.equals(
                    classification)) {
                row.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND, bound);
                // README LOOP-1 wants experiment-owned bound declarations.
                if (task.loopBound().declaredBounds().containsKey(
                        loopSiteId)) {
                    row.addProperty(
                            LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY,
                            LoopBoundPolicy.BOUND_FROM_DECLARATION);
                } else if (LoopBoundPolicy.failureRelevantLoop(declaration)) {
                    result.gap(
                            BoundedLoopComposition.LOOP_BODY_BOUND_UNDECLARED,
                            task.occurrenceId() + "\n" + loopSiteId,
                            "retained condition loop inherits the core "
                                    + "default K_L=" + bound + " with no "
                                    + "experiment-owned bound declaration");
                }
            }
            row.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, runtimeLoopId);
            row.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, bodyCount);
            boolean loopReached = controlObserved || bodyCount > 0;
            row.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, loopReached);
            if (LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(
                    classification)) {
                JsonArray cardinalities = exactCardinalities(
                        source, runtimeLoopId, loopSiteId, result);
                if (cardinalities.size() == 0 && loopReached) {
                    result.gap(
                            LoopBoundPolicy.PATH_ARRAY_CARDINALITY_MISSING,
                            loopSiteId, "fixed-count loop has a path-local "
                                    + "body count but no exact dynamic array "
                                    + "cardinality observation");
                } else if (cardinalities.size() > 0) {
                    row.add(LoopBoundPolicy.LOOP_CARDINALITIES,
                            cardinalities);
                }
            }
            result.counts.add(row);
        }
        return result;
    }

    /** Runtime loop counters are sparse: an absent declared id means that
     * this path completed no backedge traversal. */
    static int sparseLoopCount(JsonObject counters, String runtimeLoopId) {
        return runtimeLoopId.isEmpty()
                ? -1 : optionalInteger(counters, runtimeLoopId, 0);
    }

    /** Exact dynamic array lengths published for one runtime natural loop. */
    private static JsonArray exactCardinalities(
            ResultRow source, String runtimeLoopId, String loopSiteId,
            PathLoopCounts result) {
        JsonArray exact = new JsonArray();
        Map<Integer, Integer> byOccurrence = new LinkedHashMap<>();
        for (JsonElement element : source.loopCardinalities) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (!runtimeLoopId.equals(optionalString(row,
                    LoopBoundPolicy.RUNTIME_LOOP_ID))) {
                continue;
            }
            int occurrence = optionalInteger(row,
                    LoopBoundPolicy.DYNAMIC_OCCURRENCE, -1);
            int cardinality = optionalInteger(row,
                    LoopBoundPolicy.LOOP_CARDINALITY, -1);
            if (occurrence < 1 || cardinality < 0
                    || !LoopBoundPolicy.PATH_CARDINALITY_AUTHORITY.equals(
                    optionalString(row, "cardinalityAuthority"))) {
                result.gap(LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS,
                        loopSiteId, "malformed exact array cardinality row");
                continue;
            }
            Integer previous = byOccurrence.putIfAbsent(
                    occurrence, cardinality);
            if (previous != null) {
                if (previous.intValue() != cardinality) {
                    result.gap(LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS,
                            loopSiteId, "dynamic occurrence " + occurrence
                                    + " observes both N=" + previous
                                    + " and N=" + cardinality);
                }
                continue;
            }
            exact.add(row);
        }
        for (JsonElement element : source.loopCardinalityGaps) {
            if (!element.isJsonObject()) continue;
            JsonObject gap = element.getAsJsonObject();
            if (!runtimeLoopId.equals(optionalString(gap,
                    LoopBoundPolicy.RUNTIME_LOOP_ID))) {
                continue;
            }
            result.gap(firstNonBlank(optionalString(gap, "reason"),
                            LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS),
                    loopSiteId, firstNonBlank(optionalString(gap, "detail"),
                            "runtime array cardinality observation gap"));
        }
        return exact;
    }

    /** Exact natural-loop counter id published with the retained loop. */
    private static String runtimeLoopId(JsonObject declaration) {
        return optionalString(declaration, LoopBoundPolicy.RUNTIME_LOOP_ID);
    }

    private static final class PathLoopCounts {
        private final JsonArray counts = new JsonArray();
        private final JsonArray gaps = new JsonArray();
        private String refusal = "";

        private void gap(String reason, String subject, String detail) {
            JsonObject row = new JsonObject();
            row.addProperty("reason", reason);
            row.addProperty("subject", subject);
            row.addProperty("detail", detail);
            gaps.add(row);
        }
    }

    /** Files one named import gap and refuses the row under that code. */
    private static JsonObject refuse(ResultRow row, String code,
                                     String detail,
                                     List<JsonObject> diagnostics) {
        diagnostics.add(diagnostic(row, code, detail));
        return null;
    }

    /** Joins runtime alignment gaps without an output projection contract. */
    private static JsonArray alignmentGaps(ResultRow row) {
        JsonArray result = new JsonArray();
        for (JsonElement gap : row.rpcHandoffGaps) {
            if (gap.isJsonObject()
                    && RpcExpressionHandoff.isGap(gap.getAsJsonObject())) {
                result.add(gap);
            }
        }
        for (JsonElement gap : row.sharedStateGaps) {
            if (gap.isJsonObject()
                    && SharedStateEvidence.isGap(gap.getAsJsonObject())) {
                result.add(gap);
            }
        }
        for (JsonElement gap : row.branchCoverageGaps) {
            if (gap.isJsonObject() && CoverageDivergence.isDivergence(
                    gap.getAsJsonObject())) {
                result.add(gap);
            }
        }
        return result;
    }

    /** Ingests the VM handoff references this execution recorded.
     *
     * <p>Schema {@value VmHandoffEvidence#SCHEMA_VERSION} requires the attach
     * endpoint (README {@code RPC-1}).</p> */
    private static List<JsonObject> vmHandoffEvents(
            ResultRow row, ExecutionTask task, String topologyEpoch,
            JsonArray gaps) {
        List<JsonObject> events = new ArrayList<>();
        if (row.vmHandoffs == null) return events;
        Map<String, Integer> ordinals = new LinkedHashMap<>();
        for (JsonElement element : row.vmHandoffs) {
            JsonObject record = element.isJsonObject()
                    ? element.getAsJsonObject() : new JsonObject();
            if (VmHandoffEvidence.isEvent(record)) {
                String port = optionalString(record, "portId");
                int ordinal = ordinals.merge(port, 1, Integer::sum);
                String familyKey =
                        SymbolicPropagationClosure.boundaryFamilyKey(
                                topologyEpoch, row.plannedOccurrenceId,
                                VmExpressionIr.RPC_ATTACH, port, ordinal);
                JsonObject admitted = VmHandoffEvidence.withBoundaryFamily(
                        record, familyKey, topologyEpoch);
                admitted.addProperty("boundarySessionScope",
                        row.boundarySessionScope);
                admitted.addProperty("consumerOccurrenceId",
                        row.rowOccurrenceId);
                events.add(admitted);
            } else {
                gaps.add(RpcExpressionHandoff.gap(
                        RpcExpressionHandoff.STAGE_ATTACH,
                        RpcExpressionHandoff.MALFORMED_RESULT,
                        0L,
                        "recorded VM handoff reference did not survive "
                                + "import admission"));
            }
        }
        return events;
    }

    /**
     * Admits every mint this replay recorded at a declared hook site.
     *
     * <p>A configured source is declared by SITE, so it is one variable per
     * replay: the catalog carries one phase id for every execution of that
     * site, and a repeat is the same variable observed again rather than a
     * malformed catalog.  Indexing it by id and raising on the second row
     * rejected every region path whose site ran more than once -- lane BH's
     * 50 REGION_PATH_ADMISSION_REJECTED, all naming one id.</p>
     *
     * <p>The first row wins, deterministically: the catalog is in event
     * order, so that is the execution the recording saw first, and the rows
     * differ only in the evidence of where each execution happened.</p>
     */
    static JsonArray symbolicSourceEvidence(
            ResultRow row,
            List<ConfiguredSourcePhaseContract.Occurrence> catalog,
            List<String> issues) {
        Map<String, ConfiguredSourcePhaseContract.Occurrence> mintSites =
                new LinkedHashMap<>();
        for (ConfiguredSourcePhaseContract.Occurrence phase : catalog) {
            mintSites.putIfAbsent(phase.phaseId(), phase);
        }
        JsonArray admitted = new JsonArray();
        Set<String> observed = new LinkedHashSet<>();
        if (!row.symbolicSourceEvidenceIssue.isEmpty()) {
            issues.add("SYMBOLIC_SOURCE_EVIDENCE_MALFORMED:"
                    + row.symbolicSourceEvidenceIssue);
            return admitted;
        }
        for (JsonObject event : row.symbolicSourceEvidence) {
            String phaseId = optionalString(event, "sourcePhaseId");
            String id = optionalString(event, "sourceId");
            String field = optionalString(event, "fieldSignature");
            String sourceOccurrence = optionalString(event,
                    "sourceOccurrenceId");
            String expectedOccurrence = row.rowOccurrenceId;
            boolean exactRowOccurrence = sourceOccurrence.equals(
                    expectedOccurrence);
            ConfiguredSourcePhaseContract.Occurrence phase =
                    mintSites.get(phaseId);
            if (phase == null
                    || !exactRowOccurrence
                    || !id.equals(phase.sourceId())
                    || !field.equals(phase.fieldSignature())) {
                issues.add("SYMBOLIC_SOURCE_EVIDENCE_NOT_DECLARED:"
                        + phaseId + ":" + id);
                continue;
            }
            // One site is one variable, so a second execution of it inside
            // this activation is the same root observed again -- admitted
            // once, and not a second root nor a malformed one.
            if (!observed.add(phaseId)) continue;
            admitted.add(event);
        }
        return admitted;
    }

    /** Validated observations and the strict minted-root subset of them. */
    static final class ManualInputEvidence {
        final JsonArray observations = new JsonArray();
        final JsonArray sources = new JsonArray();
    }

    /**
     * Normalizes the other explicit root API -- a frozen task {@code SYMBOLIC}
     * action -- into source evidence only when the runtime published the exact
     * post-mint VM root. A retained propagated expression remains an
     * action-bound observation and never acquires a second root identity.
     */
    static ManualInputEvidence manualSymbolicSourceEvidence(
            ResultRow row, ExecutionTask task, List<String> issues) {
        ManualInputEvidence admitted = new ManualInputEvidence();
        Map<String, String> rawByIdentity = new LinkedHashMap<>();
        for (JsonObject observation : row.symbolizedInputs) {
            if (!optionalString(observation, "sourceId").isEmpty()) continue;
            if (!MANUAL_INPUT_OBSERVATION_KIND.equals(
                    optionalString(observation, "kind"))) {
                issues.add("MANUAL_SYMBOLIC_INPUT_OBSERVATION_MALFORMED:"
                        + firstNonBlank(optionalString(observation, "symbol"),
                        "UNKNOWN") + ":unsupported observation schema");
                continue;
            }
            String port = optionalString(observation, "portId");
            JsonObject action = exactManualAction(task, observation);
            String problem = manualObservationProblem(row, task, observation,
                    action);
            if (!problem.isEmpty()) {
                issues.add("MANUAL_SYMBOLIC_INPUT_OBSERVATION_MALFORMED:"
                        + firstNonBlank(port, "UNKNOWN") + ":" + problem);
                continue;
            }
            admitted.observations.add(observation);
            if (!optionalBool(observation, "minted", false)) {
                // Reused expressions are dependency observations. Their roots
                // must resolve through their original source/boundary evidence.
                continue;
            }
            JsonObject expression = VmExpressionIr.exactSymbolRoot(
                    observation.get("expression"));
            if (expression == null) {
                // A container/compound expression may have been created by the
                // action without being one replay-addressable scalar root.
                continue;
            }
            String raw = optionalString(expression, "_exp");
            String javaType = optionalString(expression, "_java_type");
            if (!sameJavaType(optionalString(action, "javaType"), javaType)) {
                // The VM may expose a structural/reference bookkeeping root
                // for a container or object. It is an exact observation, but
                // not the typed scalar input promised by this action.
                continue;
            }
            String field = optionalString(observation, "fieldSignature");
            String identity = "MANUAL."
                    + CanonicalJson.sha256(task.sourceKey() + "\n"
                    + task.regionId() + "\n" + task.occurrenceId()
                    + "\n" + port);
            String heldRaw = rawByIdentity.putIfAbsent(identity, raw);
            if (heldRaw != null && !heldRaw.equals(raw)) {
                issues.add("MANUAL_SYMBOLIC_ROOT_IDENTITY_CONFLICT:" + port);
                continue;
            }
            if (heldRaw != null) continue;
            try {
                admitted.sources.add(SymbolicSourceEvidence.manualEvent(port,
                        task.occurrenceId(), field, javaType, raw, identity));
            } catch (IllegalArgumentException malformed) {
                issues.add("MANUAL_SYMBOLIC_ROOT_MALFORMED:" + raw + ":"
                        + firstNonBlank(malformed.getMessage(), "UNKNOWN"));
            }
        }
        return admitted;
    }

    /** The exact frozen action named jointly by port and canonical digest. */
    private static JsonObject exactManualAction(
            ExecutionTask task, JsonObject observation) {
        String port = optionalString(observation, "portId");
        String digest = optionalString(observation, "actionDigest");
        JsonObject selected = null;
        for (JsonElement element : task.inputActions().symbolic()) {
            JsonObject action = element.getAsJsonObject();
            if (!port.equals(optionalString(action, "symbol"))
                    || !digest.equals(CanonicalJson.sha256(action))) {
                continue;
            }
            if (selected != null) return null;
            selected = action;
        }
        return selected;
    }

    /** Structural checks before an observation can influence composition. */
    private static String manualObservationProblem(
            ResultRow row, ExecutionTask task, JsonObject observation,
            JsonObject action) {
        if (!observation.keySet().containsAll(
                MANUAL_INPUT_OBSERVATION_MEMBERS)
                || !MANUAL_INPUT_OBSERVATION_OPTIONAL.containsAll(
                        extraMembers(observation))
                || exactInteger(observation, "schemaVersion", -1) != 1
                || !MANUAL_INPUT_OBSERVATION_AUTHORITY.equals(
                optionalString(observation, "authority"))) {
            return "unsupported exact-action observation schema";
        }
        if (action == null) return "action is not in the frozen task";
        // The join is on the address, not on the bytes that spell it: node,
        // epoch, region and the k-th activation.  String equality answered
        // the same way while both sides were minted by one build, which is
        // exactly the condition under which a fourth spelling of an identity
        // goes unnoticed until it drifts.  An address neither side can read
        // refuses, rather than matching another unreadable one.
        if (!sameOccurrence(task.occurrenceId(), row.plannedOccurrenceId)
                || !sameOccurrence(row.plannedOccurrenceId,
                optionalString(observation, "plannedOccurrenceId"))
                || !row.rowOccurrenceId.equals(optionalString(observation,
                "occurrenceId"))) {
            return "observation belongs to another occurrence";
        }
        Boolean minted = exactBoolean(observation, "minted");
        Boolean reused = exactBoolean(observation,
                SymbolicSourceEvidence.REUSED);
        if (minted == null || reused == null
                || minted.booleanValue() == reused.booleanValue()) {
            return "observation must be exactly minted or reused";
        }
        JsonElement encodedPath = observation.get("fieldPath");
        if (encodedPath == null || !encodedPath.isJsonArray()) {
            return "fieldPath is not an exact array";
        }
        for (JsonElement segment : encodedPath.getAsJsonArray()) {
            if (!segment.isJsonPrimitive()
                    || !segment.getAsJsonPrimitive().isString()
                    || segment.getAsString().trim().isEmpty()) {
                return "fieldPath contains a malformed segment";
            }
        }
        String field = optionalString(observation, "fieldSignature");
        if (!manualFieldDeclared(action, field)) {
            return "field is not declared by the frozen action";
        }
        String actionType = optionalString(action, "javaType");
        String observedType = optionalString(observation, "javaType");
        if (actionType.isEmpty() || observedType.isEmpty()) {
            return "Java type is absent";
        }
        JsonElement expression = observation.get("expression");
        JsonObject exact = VmExpressionIr.exactSymbolRoot(expression);
        if (exact == null) {
            if (!optionalString(observation, "rawSymbol").isEmpty()) {
                return "non-root expression claims a raw symbol";
            }
            if (!sameJavaType(actionType, observedType)) {
                return "non-root Java type differs from the frozen action";
            }
        } else if (!optionalString(observation, "rawSymbol").equals(
                optionalString(exact, "_exp"))
                || !observedType.equals(optionalString(exact, "_java_type"))) {
            return "root metadata differs from the exact expression";
        }
        if (reused
                && !VmExpressionIr.carriesPropagatedValue(expression)) {
            return "reused observation contains no propagated expression";
        }
        return optionalString(observation, "symbol").isEmpty()
                ? "requested VM label is empty" : "";
    }

    private static boolean sameJavaType(String left, String right) {
        return !firstNonBlank(left).isEmpty()
                && !firstNonBlank(right).isEmpty()
                && JavaPrimitiveSmtSemantics.javaTypeDescriptor(left).equals(
                JavaPrimitiveSmtSemantics.javaTypeDescriptor(right));
    }

    /** A field-bearing row must name a field stated by this exact action. */
    private static boolean manualFieldDeclared(JsonObject action,
                                               String observed) {
        Set<String> declared = new LinkedHashSet<>();
        for (String name : new String[]{"leafFieldSignature",
                "accessFieldSignature", "declaredFieldSignature",
                "fieldSignature", "cell"}) {
            String value = optionalString(action, name);
            if (value.startsWith("<") && value.endsWith(">")) {
                declared.add(value);
            }
        }
        for (JsonElement element : array(action, "fieldPathDeclarations")) {
            if (element.isJsonPrimitive()) {
                declared.add(element.getAsString().trim());
            }
        }
        declared.remove("");
        return declared.isEmpty() ? observed.isEmpty()
                : declared.contains(observed);
    }

    /** Ingests the shared-state evidence this execution recorded. */
    private static JsonObject recordedSharedState(ResultRow row,
                                                  JsonArray gaps) {
        List<JsonObject> versions = new ArrayList<>();
        for (JsonElement element : row.sharedFieldVersions) {
            JsonObject record = element.isJsonObject()
                    ? element.getAsJsonObject() : new JsonObject();
            if (SharedStateEvidence.isVersionsRecord(record)) {
                versions.add(shallowCopy(record));
            } else {
                gaps.add(SharedStateEvidence.gap(
                        SharedStateEvidence.STAGE_VERSIONS,
                        SharedStateEvidence.MALFORMED_ENVELOPE,
                        optionalString(record, "locationKey"),
                        "recorded version store did not survive import "
                                + "admission"));
            }
        }
        return SharedStateEvidence.recorded(versions);
    }

    /** Admits a VM row only when it belongs to the canonical bounded path that
     * selected the task. */
    private static ReplayAdmission branchReplayAdmission(
            ResultRow row, ExecutionTask task, JsonArray mappings) {
        final BranchReplayContract.RuntimeSchedule replay;
        try {
            replay = task.replaySchedule();
        } catch (IllegalArgumentException malformed) {
            return ReplayAdmission.refused(
                    "malformed replayContract: " + malformed.getMessage());
        }
        BranchEventCatalog seed = taskSeedEvents(task);
        if (!seed.issue.isEmpty()) {
            return ReplayAdmission.refused(seed.issue);
        }
        BranchEventCatalog observed = observedBranchEvents(mappings,
                replay == null ? task : null);
        if (!observed.issue.isEmpty()) {
            return ReplayAdmission.refused(observed.issue);
        }
        if (replay == null) {
            return ReplayAdmission.of(exactSeedMismatch(task.goalId(),
                    seed.events, observed.events,
                    "BOUNDED".equals(row.exitKind),
                    task.loopExitSites()), null);
        }
        return replayPrefixAdmission(task.goalId(), observed.events, replay);
    }

    /**
     * The seed-wave branch refusal for one task and one published decision
     * set, as {@link #branchReplayAdmission} computes it.
     *
     * <p>The seam a test can reach: the surrounding admission needs a whole
     * result row and a VM summary, and the rule under test is this one
     * comparison.</p>
     */
    static String seedBranchMismatchForTest(ExecutionTask task,
                                            JsonArray mappings) {
        BranchEventCatalog seed = taskSeedEvents(task);
        if (!seed.issue.isEmpty()) return seed.issue;
        BranchEventCatalog observed = observedBranchEvents(mappings, task);
        if (!observed.issue.isEmpty()) return observed.issue;
        return exactSeedMismatch(task.goalId(), seed.events, observed.events,
                false, task.loopExitSites());
    }

    private static BranchEventCatalog taskSeedEvents(ExecutionTask task) {
        BranchEventCatalog result = new BranchEventCatalog();
        JsonObject selectedTarget = object(task.json(), "targetBranch");
        String targetSite = optionalString(selectedTarget, "siteId");
        int targetOccurrence = JsonFields.exactInteger(selectedTarget,
                "occurrence", -1);
        int branchIndex = 0;
        for (JsonElement element : task.branches()) {
            if (!element.isJsonObject()) {
                result.issue = "task branch " + branchIndex
                        + " is not an object";
                return result;
            }
            JsonObject branch = element.getAsJsonObject();
            String site = optionalString(branch, "siteId");
            JsonElement encodedOccurrences = branch.get("occurrences");
            if (site.isEmpty() || encodedOccurrences == null
                    || !encodedOccurrences.isJsonArray()) {
                result.issue = "task branch " + branchIndex
                        + " has no stable site/occurrence contract";
                return result;
            }
            for (JsonElement occurrenceElement
                    : encodedOccurrences.getAsJsonArray()) {
                if (!occurrenceElement.isJsonObject()) {
                    result.issue = "task branch occurrence is not an object at "
                            + site;
                    return result;
                }
                JsonObject occurrence = occurrenceElement.getAsJsonObject();
                int ordinal = JsonFields.exactInteger(
                        occurrence, "occurrence", -1);
                Boolean outcome = exactBoolean(occurrence, "outcome");
                if (ordinal < 1 || outcome == null) {
                    result.issue = "task branch occurrence is malformed at "
                            + site;
                    return result;
                }
                // The exact selected goal event is flipped by this task and
                // therefore is not a seed-prefix event.  Earlier occurrences
                // at the same loop site remain in the prefix.
                if (site.equals(targetSite)
                        && ordinal == targetOccurrence) {
                    continue;
                }
                final BranchEvent event;
                try {
                    event = branchEvent(site, ordinal, outcome, occurrence);
                } catch (IllegalArgumentException malformed) {
                    result.issue = "task branch occurrence is malformed at "
                            + site + ": " + malformed.getMessage();
                    return result;
                }
                if (result.byIdentity.put(event.identity, event) != null) {
                    result.issue = "duplicate task branch event "
                            + event.display();
                    return result;
                }
                result.events.add(event);
            }
            branchIndex++;
        }
        return result;
    }

    private static BranchEventCatalog observedBranchEvents(
            JsonArray mappings, ExecutionTask seedTask) {
        BranchEventCatalog result = new BranchEventCatalog();
        JsonObject selectedTarget = seedTask == null ? new JsonObject()
                : object(seedTask.json(), "targetBranch");
        String targetSite = optionalString(selectedTarget, "siteId");
        int targetOccurrence = JsonFields.exactInteger(selectedTarget,
                "occurrence", -1);
        int mappingIndex = 0;
        for (JsonElement element : mappings) {
            if (!element.isJsonObject()) {
                result.issue = "runtime branch mapping " + mappingIndex
                        + " is not an object";
                return result;
            }
            final SummaryBranchMapping mapping;
            try {
                mapping = SummaryBranchMapping.fromImmutableJson(
                        element.getAsJsonObject());
            } catch (IllegalArgumentException malformed) {
                result.issue = "runtime branch mapping " + mappingIndex
                        + " is malformed: " + malformed.getMessage();
                return result;
            }
            if (mapping.siteId().equals(targetSite)
                    && mapping.occurrence() == targetOccurrence) {
                mappingIndex++;
                continue;
            }
            if (mapping.isWitnessed()
                    && mapping.witness().isPcPredicateDecision()) {
                mappingIndex++;
                continue;
            }
            BranchEvent event = BranchEvent.mapping(mapping);
            if (result.byIdentity.put(event.identity, event) != null) {
                result.issue = "duplicate runtime branch event "
                        + event.display();
                return result;
            }
            result.events.add(event);
            mappingIndex++;
        }
        return result;
    }

    /**
     * Attests a seed replay against the recorded branch witnesses.
     *
     * <p>A pre-gate witness set used to widen {@code found} here, which is
     * the only thing it was ever read for.  Its producer arm was
     * unreachable -- {@code observeDecision} returns for every undeclared
     * site before {@code recordConcreteDecision} can file one -- so the
     * excuse was permanently empty on every corpus, and the union was a
     * no-op.</p>
     */
    private static String exactSeedMismatch(
            String replayId, List<BranchEvent> expected,
            List<BranchEvent> observed, boolean earlyStop,
            Set<String> admittedBoundarySites) {
        Map<String, Set<String>> wanted = decisionsBySite(expected);
        Map<String, Set<String>> actual = decisionsBySite(observed);
        Set<String> rootDependent = rootDependentSites(observed);
        for (Map.Entry<String, Set<String>> entry : wanted.entrySet()) {
            Set<String> found = actual.get(entry.getKey());
            if (found == null || found.isEmpty()) {
                if (earlyStop) continue;
                return replayDetail(replayId, "missing " + entry.getKey());
            }
            // The prefix a replay must reproduce is pi: the decisions this
            // region took over a root.  A site the replay decided without
            // contributing a path condition has no predicate over anything,
            // so it cannot be part of pi, and its outcome is not something a
            // replay can be asked to reproduce -- on hdfs-17899 bug2 every
            // decision of REGION.763d087e is concrete, and
            // Client$Connection.sendRpcRequest#u16 came out true where the
            // recording had false, which is the IPC client's own state and
            // not a divergence of this region's path.  Recorded here as
            // evidence; refused nowhere.
            if (!rootDependent.contains(entry.getKey())) continue;
            for (String decision : entry.getValue()) {
                if (!found.contains(decision)) {
                    return replayDetail(replayId, "wrong decision at "
                            + entry.getKey() + ": expected " + decision
                            + " but observed " + found);
                }
            }
        }
        for (String site : actual.keySet()) {
            if (!wanted.containsKey(site)
                    && !admittedBoundarySites.contains(site)
                    && rootDependent.contains(site)) {
                return replayDetail(replayId, "unexpected " + site);
            }
        }
        return "";
    }

    /** Sites whose observed decisions carried a path condition. */
    private static Set<String> rootDependentSites(
            List<BranchEvent> observed) {
        Set<String> sites = new LinkedHashSet<>();
        for (BranchEvent event : observed) {
            if (event.rootDependent) sites.add(event.site);
        }
        return sites;
    }

    private static ReplayAdmission replayPrefixAdmission(
            String replayId, List<BranchEvent> observed,
            BranchReplayContract.RuntimeSchedule replay) {
        BranchReplayContract.ReplayProgress progress =
                new BranchReplayContract.ReplayProgress(replay);
        BranchEvent matchedSource = null;
        for (BranchEvent actual : observed) {
            if (progress.observeDecision(actual.site, actual.occurrence,
                    actual.decisionToken,
                    actual.symbolicSupportDigest)) {
                matchedSource = actual;
            }
            if (progress.failed()) {
                return ReplayAdmission.refused(replayDetail(replayId,
                        progress.failure()));
            }
        }
        if (!progress.complete() || matchedSource == null) {
            return ReplayAdmission.refused(replayDetail(replayId,
                    progress.failure()));
        }
        return ReplayAdmission.of("", matchedSource);
    }

    private static Map<String, Set<String>> decisionsBySite(
            List<BranchEvent> events) {
        Map<String, Set<String>> result = new LinkedHashMap<>();
        for (BranchEvent event : events) {
            result.computeIfAbsent(event.site,
                    ignored -> new LinkedHashSet<>()).add(
                    event.decisionToken);
        }
        return result;
    }

    /** Decodes a binary decision or one complete switch successor. */
    private static BranchEvent branchEvent(
            String site, int occurrence, boolean outcome,
            JsonObject evidence) {
        boolean hasKind = evidence.has("branchKind");
        boolean hasKeys = evidence.has("caseKeys");
        boolean hasSuccessor = evidence.has("observedSuccessorIndex");
        if (!hasKind && !hasKeys && !hasSuccessor) {
            return new BranchEvent(site, occurrence, outcome);
        }
        if (!(hasKind && hasKeys && hasSuccessor)) {
            throw new IllegalArgumentException(
                    "incomplete exact switch decision");
        }
        List<Integer> keys = ExactConcreteBranchObservation.exactCaseKeys(
                evidence.get("caseKeys"));
        int successor = JsonFields.exactInteger(evidence,
                "observedSuccessorIndex", -1);
        String token = ExactConcreteBranchObservation.switchDecisionToken(
                exactText(evidence, "branchKind"), keys, successor);
        if (outcome != (successor < keys.size())) {
            throw new IllegalArgumentException(
                    "switch outcome differs from exact successor");
        }
        // A planned event states no root-dependence: every branch of a
        // region is planned with policy EXPLORE, so the observation is the
        // only side that can answer it.
        return new BranchEvent(site, occurrence, token, "", false);
    }

    private static Boolean exactBoolean(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                ? value.getAsBoolean() : null;
    }

    /**
     * Whether two ids name one planned occurrence.
     *
     * <p>Structural: {@code (node, epoch, region, k-th activation)}, parsed
     * once on each side.  An id that does not spell an address matches
     * nothing, including another unreadable one -- a join is a claim that two
     * rows are the same occurrence, and two strings nobody could read are not
     * evidence of that.</p>
     */
    private static boolean sameOccurrence(String left, String right) {
        return OccurrenceAddress.parse(left)
                .matches(OccurrenceAddress.parse(right));
    }

    private static String resultShapeRefusal(
            JsonObject raw, String event, int activationOrdinal,
            String plannedOccurrenceId, String occurrenceId,
            String replayGroupId) {
        if (!"CONCOLIC_REGION_RESULT".equals(event)) return "";
        if (exactInteger(raw, "schemaVersion", -1) != 1) {
            return RESULT_SCHEMA_UNSUPPORTED;
        }
        if (replayGroupId.isEmpty()) return RESULT_REPLAY_GROUP_MISSING;
        if (activationOrdinal < 1 || plannedOccurrenceId.isEmpty()
                || !occurrenceId.equals(OccurrenceId.parse(plannedOccurrenceId)
                .withActivation(activationOrdinal).render())) {
            return RESULT_ACTIVATION_TUPLE_MALFORMED;
        }
        return "";
    }

    /** Admits the runtime's exact target event against both authorities fixed
     * before composition: the task-selected branch identity and the witnessed
     * branch mapping imported from this execution. */
    private static JsonObject admittedTargetReach(
            ResultRow row, ExecutionTask task,
            JsonArray pathCondition, JsonArray mappings,
            ReplayAdmission replayAdmission,
            List<JsonObject> diagnostics) {
        if (!task.goalKind().capturesTargetReach()) {
            return new JsonObject();
        }
        if (row.targetReach == null) {
            return refuse(row, "TARGET_REACH_EVENT_MISSING",
                    "selected target execution published no targetReach",
                    diagnostics);
        }
        final PathObservation.TargetReachEvent event;
        try {
            event = PathObservation.TargetReachEvent.decode(row.targetReach);
        } catch (IllegalArgumentException malformed) {
            return refuse(row, "TARGET_REACH_EVENT_MALFORMED",
                    firstNonBlank(malformed.getMessage(), "UNKNOWN"),
                    diagnostics);
        }

        JsonObject selected = object(task.json(), "targetBranch");
        String selectedSite = optionalString(selected, "siteId");
        int selectedOccurrence = JsonFields.exactInteger(selected,
                "occurrence", -1);
        if (!event.siteId().equals(selectedSite)
                || event.occurrence() != selectedOccurrence) {
            return refuse(row, "TARGET_REACH_EVENT_MISMATCH",
                    "event " + event.siteId() + "#" + event.occurrence()
                            + " does not match selected target "
                            + firstNonBlank(selectedSite, "<missing>") + "#"
                            + selectedOccurrence, diagnostics);
        }

        JsonObject canonical = new JsonObject();
        canonical.add("pathCondition", pathCondition);
        canonical.add("branchMappings", mappings);
        int exactMappings = 0;
        try {
            for (SummaryBranchMapping mapping
                    : SummaryBranchMapping.fromSummary(canonical)) {
                if (mapping.isWitnessed()
                        && mapping.witness().isPcPredicateDecision()) {
                    continue;
                }
                if (replayAdmission.matchedSource == null
                        ? event.matches(mapping.siteId(),
                        mapping.occurrence(),
                        mapping.sourceTakenOutcome())
                        : replayAdmission.matchedSource.matches(mapping)) {
                    exactMappings++;
                }
            }
        } catch (IllegalArgumentException malformed) {
            return refuse(row, "TARGET_REACH_EVENT_MISMATCH",
                    "target branch evidence is malformed: "
                            + firstNonBlank(malformed.getMessage(),
                            "UNKNOWN"), diagnostics);
        }
        if (exactMappings != 1) {
            return refuse(row, "TARGET_REACH_EVENT_MISMATCH",
                    "event has " + exactMappings
                            + " exact branch mapping(s)",
                    diagnostics);
        }
        if (replayAdmission.matchedSource != null
                && !ExactConcreteBranchObservation.binaryDecisionToken(
                event.outcome()).equals(
                replayAdmission.matchedSource.decisionToken)) {
            return refuse(row, "TARGET_REACH_EVENT_MISMATCH",
                    "planned target outcome differs from matched replay "
                            + "source", diagnostics);
        }
        return event.toJson();
    }

    private static String replayDetail(String replayId, String issue) {
        return replayId + ": " + issue;
    }

    private static final class BranchEventCatalog {
        private final List<BranchEvent> events = new ArrayList<>();
        private final Map<String, BranchEvent> byIdentity =
                new LinkedHashMap<>();
        private String issue = "";
    }

    /** Replay validation result, including the actual event that answered the
     * planner's semantic source address. */
    private static final class ReplayAdmission {
        private static final ReplayAdmission NONE = new ReplayAdmission(
                "", null);
        private final String mismatch;
        private final BranchEvent matchedSource;

        private ReplayAdmission(String mismatch, BranchEvent matchedSource) {
            this.mismatch = mismatch == null ? "" : mismatch;
            this.matchedSource = matchedSource;
        }

        private static ReplayAdmission refused(String mismatch) {
            return new ReplayAdmission(mismatch, null);
        }

        private static ReplayAdmission of(String mismatch,
                                          BranchEvent matchedSource) {
            return mismatch == null || mismatch.isEmpty()
                    ? new ReplayAdmission("", matchedSource)
                    : refused(mismatch);
        }
    }

    private static final class BranchEvent {
        private final String site;
        private final int occurrence;
        private final String identity;
        private final String decisionToken;
        private final String symbolicSupportDigest;
        /**
         * Whether this decision carried a path condition.
         *
         * <p>The replay's own statement about the decision, and the only one
         * that answers "does its condition mention a root": a decision the
         * VM contributed no condition for has no predicate at all, so no
         * root occurs in it.  A planned event states nothing about this --
         * every branch of a region is planned with policy EXPLORE -- so it
         * is read off the observation.</p>
         */
        private final boolean rootDependent;

        private BranchEvent(String site, int occurrence, boolean outcome) {
            this(site, occurrence,
                    ExactConcreteBranchObservation.binaryDecisionToken(
                            outcome), "", false);
        }

        private BranchEvent(String site, int occurrence, String decisionToken,
                            String symbolicSupportDigest,
                            boolean rootDependent) {
            this.site = site;
            this.occurrence = occurrence;
            this.identity = site + "\u0000" + occurrence;
            this.decisionToken = decisionToken;
            this.symbolicSupportDigest = symbolicSupportDigest == null
                    ? "" : symbolicSupportDigest;
            this.rootDependent = rootDependent;
        }

        private static BranchEvent mapping(SummaryBranchMapping mapping) {
            return new BranchEvent(mapping.siteId(), mapping.occurrence(),
                    mapping.exactDecisionToken(), mapping.isWitnessed()
                    ? mapping.witness().symbolicSupportDigest() : "",
                    mapping.isWitnessed());
        }

        private boolean matches(SummaryBranchMapping mapping) {
            return mapping != null && site.equals(mapping.siteId())
                    && occurrence == mapping.occurrence()
                    && decisionToken.equals(mapping.exactDecisionToken())
                    && (symbolicSupportDigest.isEmpty()
                    || mapping.isWitnessed()
                    && symbolicSupportDigest.equals(mapping.witness()
                    .symbolicSupportDigest()));
        }

        private String siteOccurrence() {
            return site + '#' + occurrence;
        }

        private String display() {
            return siteOccurrence() + '=' + decisionToken;
        }
    }

    private static JsonArray branchMappings(
            ResultRow source, ExecutionTask task, SemanticPath path,
            List<String> issues) {
        Map<String, SummaryBranchMapping.Policy> policies =
                branchPolicies(task);
        JsonArray result = new JsonArray();
        Set<String> events = new LinkedHashSet<>();
        Set<Integer> decisionPositions = new LinkedHashSet<>();
        for (JsonElement element : source.branchMappings) {
            if (!element.isJsonObject()) {
                issues.add("MALFORMED_BRANCH_MAPPING");
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            String site = optionalString(row, "siteId");
            int occurrence = optionalInteger(row, "occurrence", -1);
            if (site.isEmpty() || occurrence < 1) {
                issues.add("AMBIGUOUS_BRANCH_EVENT:" + site);
                continue;
            }
            SummaryBranchMapping.Policy policy = policies.get(site);
            if (policy == null) {
                policy = SummaryBranchMapping.Policy.PATH_ASSUMPTION;
            }
            try {
                BranchWitness direct = null;
                JsonElement originalPredicate = null;
                ExactConcreteBranchObservation concrete = null;
                if (row.has("witness")
                        && row.get("witness").isJsonObject()) {
                    direct = BranchWitness.fromImmutableJson(
                            row.getAsJsonObject("witness"));
                    int pcIndex = direct.vmPcIndex();
                    originalPredicate = path.originalAt(pcIndex);
                    if (pcIndex < 0 || pcIndex >= path.vmWatermark()
                            || originalPredicate == null
                            || !BranchPredicateAlgebra.equivalent(
                            direct.sourceSatisfiedPredicateView(),
                            originalPredicate)) {
                        issues.add("BRANCH_PC_MISMATCH:" + site);
                        continue;
                    }
                } else if (row.has("concreteObservation")
                        && row.get("concreteObservation").isJsonObject()) {
                    concrete = ExactConcreteBranchObservation.fromJson(
                            row.getAsJsonObject("concreteObservation"));
                } else {
                    // A marker without a VM event is a concrete branch outside
                    // the selected symbolic slice.
                    continue;
                }

                String eventIdentity = direct != null
                        ? direct.decisionIdentity()
                        : concrete.siteId() + "\u0000"
                        + concrete.occurrence() + "\u0000" + 0;
                if (!events.add(eventIdentity)) {
                    issues.add("AMBIGUOUS_BRANCH_EVENT:" + site);
                    continue;
                }
                policy = importedBranchPolicy(policy, direct, concrete);

                int baseline = exactInteger(row,
                        "rawPathConditionBaseline", -1);
                int limit = exactInteger(row, "rawPathConditionSize", -1);
                if (baseline < 0 || limit < baseline
                        || limit > path.vmWatermark()
                        || direct != null
                        && (direct.vmPcIndex() < baseline
                        || direct.vmPcIndex() >= limit)) {
                    issues.add("INVALID_BRANCH_PC_WINDOW:" + site);
                    continue;
                }

                if (direct != null) {
                    int summaryPcIndex = path.summaryIndex(
                            direct.vmPcIndex());
                    if (summaryPcIndex < 0) {
                        issues.add("MISSING_BRANCH_PC:" + site);
                        continue;
                    }
                    if (!decisionPositions.add(summaryPcIndex)) {
                        issues.add("AMBIGUOUS_BRANCH_PC:"
                                + summaryPcIndex);
                        continue;
                    }
                    result.add(SummaryBranchMapping.witnessed(
                            direct.atPcIndex(summaryPcIndex,
                                    originalPredicate),
                            summaryPcIndex, policy).toImmutableJsonView());
                } else if (concrete != null) {
                    result.add(SummaryBranchMapping.concrete(concrete,
                            policy).toJson());
                }
            } catch (IllegalArgumentException malformed) {
                issues.add("MALFORMED_BRANCH_MAPPING:" + site + ":"
                        + malformed.getMessage());
            }
        }
        return result;
    }

    /** A switch successor and each VM predicate that proves its selected arm
     * constrain a later binary flip; neither is itself a Boolean flip source. */
    static SummaryBranchMapping.Policy importedBranchPolicy(
            SummaryBranchMapping.Policy planned, BranchWitness witness,
            ExactConcreteBranchObservation concrete) {
        if ((witness != null && witness.isPcPredicateDecision())
                || (concrete != null && concrete.isSwitchObservation())) {
            return SummaryBranchMapping.Policy.PATH_ASSUMPTION;
        }
        return planned;
    }

    /** True only for a binary VM predicate that would need branch authority. */
    private static boolean pcPredicate(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(object, "_type"))
                || ContainerSmtCodec.handlesFieldBinding(expression)
                || ContainerSmtCodec.handlesAccessConstraint(expression)) {
            return false;
        }
        try {
            BranchPredicateAlgebra.complementOperator(
                    optionalString(object, "_op"));
            return true;
        } catch (IllegalArgumentException unsupported) {
            return false;
        }
    }

    private static Map<String, SummaryBranchMapping.Policy> branchPolicies(
            ExecutionTask task) {
        Map<String, SummaryBranchMapping.Policy> result =
                new LinkedHashMap<>();
        for (JsonElement element : task.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            String site = optionalString(branch, "siteId");
            try {
                result.put(site, SummaryBranchMapping.Policy.fromWire(
                        optionalString(branch, "policy")));
            } catch (IllegalArgumentException unsupported) {
                result.put(site, SummaryBranchMapping.Policy.EXPLORE);
            }
        }
        return result;
    }

    private static Map<String, ExecutionTask> taskIndex(
            List<JsonObject> rows) throws IOException {
        Map<String, ExecutionTask> result = new LinkedHashMap<>();
        for (JsonObject row : rows) {
            final ExecutionTask task;
            try {
                task = ExecutionTask.decode(row);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("Malformed execution task: "
                        + malformed.getMessage(), malformed);
            }
            if (result.put(task.taskId(), task) != null) {
                throw new IOException("Duplicate taskId " + task.taskId());
            }
        }
        return result;
    }

    static Set<String> regionIds(List<JsonObject> rows)
            throws IOException {
        Set<String> result = new LinkedHashSet<>();
        for (JsonObject row : rows) {
            String id = optionalString(row, "regionId");
            if (id.isEmpty() || !result.add(id)) {
                throw new IOException("Missing or duplicate regionId " + id);
            }
        }
        return result;
    }

    /** Names why a non-result row published nothing. */
    private static String skippedEventCode(ResultRow row) {
        return row.skipKind.isEmpty() ? "SKIPPED_RUNTIME_EVENT"
                : "REGION_" + row.skipKind;
    }

    private static String skippedEventDetail(ResultRow row) {
        return row.skipReason.isEmpty() ? row.event
                : row.event + ": " + row.skipReason;
    }

    /** Every gap code this stage publishes for a changed topology. */
    static final String TOPOLOGY_DIVERGENCE = "TOPOLOGY_DIVERGENCE";

    /**
     * What this replay ran that its epoch's plan did not name, and back.
     *
     * <p>A flip can change the topology -- take a branch that opens a wire
     * the recording never used, or run a region occurrence the plan never
     * addressed.  That is a <em>new topology to take into account</em>, not
     * evidence to drop: the replay is exact about what it did, and refusing
     * it would throw away every other path it also published.  So each
     * difference is one diagnostic row stamped with the replay that found
     * it, and the iteration loop uses them to plan the next epoch -- the
     * unplanned handoff becomes a family of its own with the one pair this
     * replay delivered, and the unplanned occurrence becomes a task
     * addressed by the address it was observed at.</p>
     */
    static boolean topologyDivergences(ResultRow row,
                                               ExecutionTask task,
                                               List<JsonObject> diagnostics) {
        boolean divergent = false;
        Set<String> planned = new LinkedHashSet<>();
        for (CommunicationHandoffSpec site : task.communicationHandoffs()) {
            planned.add(site.portId());
        }
        Set<String> ran = new LinkedHashSet<>();
        for (JsonElement encoded : row.vmHandoffs == null
                ? new JsonArray() : row.vmHandoffs) {
            if (!encoded.isJsonObject()) continue;
            JsonObject event = encoded.getAsJsonObject();
            String phase = optionalString(event,
                    InSessionReadResolver.HANDOFF_PHASE_ID);
            String port = optionalString(event, "portId");
            ran.add(port);
            if (!phase.isEmpty() && !planned.contains(port)) {
                diagnostics.add(diagnostic(row, TOPOLOGY_DIVERGENCE,
                        "UNPLANNED_HANDOFF:" + phase + " at port " + port
                                + " on " + row.rowOccurrenceId));
                divergent = true;
            }
        }
        for (String port : planned) {
            if (!ran.contains(port)) {
                // Not a new topology: a selected binding this replay did
                // not reproduce is an admission gap of this epoch, and the
                // paths it did publish still extend it.
                diagnostics.add(diagnostic(row,
                        "PLANNED_HANDOFF_NOT_REPRODUCED", port + " on "
                                + row.rowOccurrenceId));
            }
        }
        OccurrenceAddress address = OccurrenceAddress.parse(
                row.rowOccurrenceId);
        OccurrenceAddress addressed = OccurrenceAddress.parse(
                task.occurrenceId());
        if (address.isNamed() && addressed.isNamed()
                && !address.render().equals(addressed.render())) {
            diagnostics.add(diagnostic(row, TOPOLOGY_DIVERGENCE,
                    "UNPLANNED_OCCURRENCE:" + address.render()
                            + " where the plan addressed "
                            + addressed.render()));
            divergent = true;
        }
        if (divergent) {
            diagnostics.add(diagnostic(row, TOPOLOGY_DIVERGENCE,
                    "BUNDLE:" + row.taskId + " line " + (row.line + 1)
                            + " is held for the next epoch"));
        }
        return divergent;
    }

    private static JsonObject diagnostic(
            ResultRow row, String code, String detail) {
        JsonObject result = new JsonObject();
        result.addProperty("kind", "CONCOLIC_IMPORT_DIAGNOSTIC");
        result.addProperty("code", code);
        result.addProperty("detail", firstNonBlank(detail, "UNKNOWN"));
        result.addProperty("taskId", row.taskId);
        result.addProperty("line", row.line + 1);
        return result;
    }

    /** Whether this is the initial full region-path observation. */
    private static boolean relationOnlySeed(ExecutionTask task) {
        if (!task.goalKind().capturesRegionPath()
                || task.replayContract() != null) {
            return false;
        }
        for (JsonElement element : task.inputActions().all()) {
            if (element.isJsonObject()
                    && "EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1".equals(
                    optionalString(element.getAsJsonObject(), "authority"))) {
                return false;
            }
        }
        return true;
    }

    /** Removes replay-only container observations and remaps PC ownership. */
    private static final class SemanticPath {
        /** Exact retained VM terms by absolute full-PC index. */
        private final NavigableMap<Integer, JsonElement> original;
        private final JsonArray expressions;
        /** Absolute VM index to compact summary index. */
        private final Map<Integer, Integer> summaryIndices;
        /** Size of the VM full PC without allocating its omitted holes. */
        private final int vmWatermark;

        private SemanticPath(NavigableMap<Integer, JsonElement> original,
                             JsonArray expressions,
                             Map<Integer, Integer> summaryIndices,
                             int vmWatermark) {
            this.original = original;
            this.expressions = expressions;
            this.summaryIndices = summaryIndices;
            this.vmWatermark = vmWatermark;
        }

        /** Reconstructs one compact case from its selected branch witnesses
         * and the VM's separately bounded non-branch solver constraints. */
        private static SemanticPath fromSelectedEvidence(
                JsonObject engine, JsonArray branchMappings,
                List<String> issues) {
            Map<Integer, JsonElement> evidence = new LinkedHashMap<>();
            int size = selectedBranchEvidence(branchMappings, evidence,
                    issues);

            JsonElement encoded = engine.get(
                    AUXILIARY_PATH_CONDITION_FIELD);
            if (encoded == null || !encoded.isJsonObject()) {
                issues.add("AUXILIARY_PATH_CONDITION_MISSING");
                return fromSparseEvidence(evidence, size, branchMappings);
            }
            JsonObject auxiliary = encoded.getAsJsonObject();
            if (exactInteger(auxiliary, "schemaVersion", -1) != 1
                    || !AUXILIARY_PATH_CONDITION_KIND.equals(
                    optionalString(auxiliary, "kind"))
                    || !AUXILIARY_PATH_CONDITION_AUTHORITY.equals(
                    optionalString(auxiliary, "authority"))
                    || !optionalBool(auxiliary, "active", false)
                    || optionalBool(auxiliary, "aborted", false)) {
                issues.add("AUXILIARY_PATH_CONDITION_MALFORMED:ENVELOPE");
                return fromSparseEvidence(evidence, size, branchMappings);
            }

            int watermark = exactInteger(auxiliary,
                    "pathConditionWatermark", -1);
            int count = exactInteger(auxiliary, "conditionCount", -1);
            JsonElement encodedIndices = auxiliary.get(
                    "pathConditionIndices");
            JsonElement encodedConditions = auxiliary.get("conditions");
            JsonArray indices = encodedIndices != null
                    && encodedIndices.isJsonArray()
                    ? encodedIndices.getAsJsonArray() : new JsonArray();
            JsonArray conditions = encodedConditions != null
                    && encodedConditions.isJsonArray()
                    ? encodedConditions.getAsJsonArray() : new JsonArray();
            // The VM states how many conditions it actually wrote beside how
            // many it recorded.  On the auxiliary envelope the serializer
            // emits one entry per recorded condition -- a real expression or
            // a truncation marker -- so the three counts agree
            // unconditionally, and a disagreement is a genuine fault again.
            int emitted = exactInteger(auxiliary,
                    EMITTED_CONDITION_COUNT, -1);
            if (watermark < 0 || count < 0 || count != indices.size()
                    || count != conditions.size()
                    || emitted != conditions.size()
                    || encodedIndices == null
                    || !encodedIndices.isJsonArray()
                    || encodedConditions == null
                    || !encodedConditions.isJsonArray()) {
                issues.add("AUXILIARY_PATH_CONDITION_MALFORMED:CARDINALITY:"
                        + "declared=" + count + ",emitted=" + emitted
                        + ",conditions=" + conditions.size()
                        + ",indices=" + indices.size());
                return fromSparseEvidence(evidence,
                        Math.max(size, watermark), branchMappings);
            }

            int prior = -1;
            for (int ordinal = 0; ordinal < count; ordinal++) {
                JsonElement indexElement = indices.get(ordinal);
                JsonElement condition = conditions.get(ordinal);
                JsonObject indexHolder = new JsonObject();
                indexHolder.add("value", indexElement);
                int index = exactInteger(indexHolder, "value", -1);
                if (index < 0) {
                    issues.add("AUXILIARY_PATH_CONDITION_MALFORMED:INDEX_"
                            + ordinal);
                    continue;
                }
                if (index <= prior || index < 0 || index >= watermark) {
                    issues.add("AUXILIARY_PATH_CONDITION_MALFORMED:ORDER_"
                            + ordinal);
                    prior = Math.max(prior, index);
                    continue;
                }
                prior = index;
                if (condition == null || condition.isJsonNull()) {
                    issues.add("AUXILIARY_PATH_CONDITION_MALFORMED:NULL_"
                            + index);
                    continue;
                }
                if (SharedStateEvidence.containsVmSerializationTruncation(
                        condition)) {
                    // The VM stated a marker in this slot instead of the
                    // expression.  It names why and where; this path is
                    // fail-closed on it, and only this path -- another
                    // activation of the same task keeps its own case.
                    issues.add("VM_EXPRESSION_SERIALIZATION_TRUNCATED:"
                            + truncationKind(condition) + ":"
                            + truncationIndex(condition, ordinal, index));
                    continue;
                }
                JsonElement existing = evidence.get(index);
                if (existing != null) {
                    issues.add("AUXILIARY_PATH_CONDITION_CONFLICT:" + index);
                    continue;
                }
                evidence.put(index, condition);
            }
            for (Integer branchIndex : witnessedVmPcIndices(branchMappings)) {
                if (branchIndex >= watermark) {
                    issues.add("AUXILIARY_PATH_CONDITION_MALFORMED:"
                            + "BRANCH_INDEX_" + branchIndex);
                }
            }
            return fromSparseEvidence(evidence,
                    Math.max(size, watermark), branchMappings);
        }

        /** The VM's own name for why this slot holds no expression. */
        private static String truncationKind(JsonElement condition) {
            String kind = condition != null && condition.isJsonObject()
                    ? optionalString(condition.getAsJsonObject(), "truncationKind")
                    : "";
            return kind.isEmpty() ? "AUXILIARY_PATH_CONDITION" : kind;
        }

        /**
         * Where the marker says it sits.  {@code _index} is the position in
         * the serialized vector, which is what a reader needs to line the
         * marker up against {@code conditions}; the absolute path-condition
         * index is the fallback for a marker that states none.
         */
        private static String truncationIndex(JsonElement condition,
                                              int ordinal, int index) {
            if (condition != null && condition.isJsonObject()) {
                JsonObject marker = condition.getAsJsonObject();
                if (marker.has("_index")) {
                    return String.valueOf(exactInteger(marker, "_index",
                            ordinal));
                }
            }
            return String.valueOf(index);
        }

        private static int selectedBranchEvidence(
                JsonArray branchMappings,
                Map<Integer, JsonElement> evidence,
                List<String> issues) {
            int size = 0;
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                if (!row.has("witness")
                        || !row.get("witness").isJsonObject()) {
                    continue;
                }
                try {
                    BranchWitness witness = BranchWitness.fromImmutableJson(
                            row.getAsJsonObject("witness"));
                    int index = witness.vmPcIndex();
                    if (index < 0) continue;
                    if (evidence.putIfAbsent(index,
                            witness.sourceSatisfiedPredicateView())
                            != null) {
                        issues.add("AMBIGUOUS_BRANCH_PC:" + index);
                    }
                    size = Math.max(size, Math.max(index + 1,
                            exactInteger(row, "rawPathConditionSize", 0)));
                } catch (IllegalArgumentException ignored) {
                    // branchMappings() reports the malformed witness by name.
                }
            }
            return size;
        }

        private static SemanticPath fromSparseEvidence(
                Map<Integer, JsonElement> evidence, int size,
                JsonArray branchMappings) {
            NavigableMap<Integer, JsonElement> original = new TreeMap<>();
            JsonArray expressions = new JsonArray();
            Map<Integer, Integer> summaryIndices = new LinkedHashMap<>();
            Set<Integer> branchDecisions =
                    witnessedVmPcIndices(branchMappings);
            for (Map.Entry<Integer, JsonElement> entry
                    : new TreeMap<>(evidence).entrySet()) {
                int index = entry.getKey();
                JsonElement expression = entry.getValue();
                if (index < 0 || expression == null
                        || expression.isJsonNull()) {
                    continue;
                }
                original.put(index, expression);
                boolean witnessed = branchDecisions.contains(index);
                if (!witnessed
                        && (InitialContainerObservation.isConcreteEquality(
                        expression) || pcPredicate(expression))) {
                    continue;
                }
                summaryIndices.put(index, expressions.size());
                expressions.add(expression);
            }
            return new SemanticPath(original, expressions, summaryIndices,
                    Math.max(0, size));
        }

        /** Whether any row carries a decision the summary can admit: a
         * selected branch witness the VM indexed, or a concrete
         * observation of a branch outside the symbolic slice. */
        private static boolean hasAdmissibleBranchDecision(
                JsonArray branchMappings) {
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                JsonElement concrete = row.get("concreteObservation");
                if (concrete != null && concrete.isJsonObject()) return true;
                if (!row.has("witness")
                        || !row.get("witness").isJsonObject()) {
                    continue;
                }
                try {
                    if (BranchWitness.fromImmutableJson(row.getAsJsonObject(
                            "witness")).vmPcIndex() >= 0) {
                        return true;
                    }
                } catch (IllegalArgumentException ignored) {
                    // branchMappings() owns the diagnostic.
                }
            }
            return false;
        }

        private static Set<Integer> witnessedVmPcIndices(
                JsonArray branchMappings) {
            Set<Integer> result = new LinkedHashSet<>();
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) continue;
                JsonObject witness = object(
                        element.getAsJsonObject(), "witness");
                int index = optionalInteger(witness, "vmPcIndex", -1);
                if (index >= 0) result.add(index);
            }
            return result;
        }

        private int summaryIndex(int vmIndex) {
            Integer index = summaryIndices.get(vmIndex);
            return index == null ? -1 : index;
        }

        private JsonElement originalAt(int vmIndex) {
            return original.get(vmIndex);
        }

        private int vmWatermark() {
            return vmWatermark;
        }
    }

    private static Path required(
            Map<String, String> options, String name) {
        return Paths.get(requiredValue(options, name));
    }

    private static String requiredValue(
            Map<String, String> options, String name) {
        String value = options.get(name);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException(
                    "missing required --" + name);
        }
        return value.trim();
    }

    public static final class ImportResult {
        public final int rawResultCount;
        public final int validSummaryCount;
        public final int diagnosticCount;
        /** Every way this publication is short of the plan, in plan order. */
        public final List<JsonObject> contractViolations;

        private ImportResult(int rawResultCount, int validSummaryCount,
                             int diagnosticCount,
                             List<JsonObject> contractViolations) {
            this.rawResultCount = rawResultCount;
            this.validSummaryCount = validSummaryCount;
            this.diagnosticCount = diagnosticCount;
            this.contractViolations = contractViolations;
        }
    }
}
