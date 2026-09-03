package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.BoundedOutputVersions;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.exactInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Converts one VM execution row into one semantic path row. */
public final class ConcolicSummaryImporter {
    private static final String AUXILIARY_PATH_CONDITION_FIELD =
            "auxiliaryPathCondition";
    private static final String SELECTED_BRANCH_AND_AUXILIARY_AUTHORITY =
            "VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1";
    private static final String AUXILIARY_PATH_CONDITION_KIND =
            "CONCOLIC_AUXILIARY_PATH_CONDITION";
    /** How many conditions the VM actually serialized into the window.
     *  Equal to the declared count once the serializer emits one truncation
     *  marker per remaining index; absent on a pre-marker VM. */
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
    static final String CONFIGURED_SOURCE_ROOT_NOT_MATERIALIZED =
            "CONFIGURED_SOURCE_ROOT_NOT_MATERIALIZED";
    /** A result that published no {@code freeSymbols} array at all. */
    private static final String FREE_SYMBOL_LEDGER_MISSING =
            "FREE_SYMBOL_LEDGER_MISSING";
    private static final String RESULT_SCHEMA_UNSUPPORTED =
            "CONCOLIC_RESULT_SCHEMA_UNSUPPORTED";
    private static final String RESULT_ACTIVATION_TUPLE_MALFORMED =
            "CONCOLIC_RESULT_ACTIVATION_TUPLE_MALFORMED";

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
        final JsonArray concreteBranchWitnesses;
        final boolean statesBranchEvidence;
        /** Every output capture of the run, by the binding it answers. */
        final Map<String, List<JsonObject>> capturesByBinding;
        /** One row per entry of a declared mint site. */
        final List<JsonObject> symbolizedInputs;
        /** The C2 free roots; stated by every result, empty when none. */
        final List<JsonObject> freeSymbols;
        /** Every mint this execution filed at a declared hook site. */
        final List<JsonObject> symbolicSourceEvidence;
        /** Why that ledger did not decode, or "" when it did. */
        final String symbolicSourceEvidenceIssue;
        final JsonArray vmHandoffs;
        final JsonArray sharedFieldVersions;
        final JsonObject sessionEventLedger;
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
        final JsonArray readCutGaps;
        /** One structural row per output site that ran past its bounded
         * output version capacity; empty when none did. */
        final List<JsonObject> outputVersionGaps;
        final JsonElement targetReach;
        final JsonObject rootOutput;
        /** Sites decided symbolically, and sites decided either way. */
        final Set<String> decidedBranchSites;
        final SortedSet<String> observedBranchSites;
        final SortedSet<String> observedCaptureBindings;
        /** The named shape refusal, or "" when the row decoded. */
        final String refusal;
        /** OCC-1: this result activation's required positive ordinal. */
        final int activationOrdinal;
        /** OCC-1: the planned address every activation of the task shares. */
        final String plannedOccurrenceId;
        /** OCC-1: this activation's own occurrence identity. */
        final String rowOccurrenceId;
        /** OCC-1: whether the runtime saw this activation satisfy the
         *  demanded output boundary; required on a result row. */
        final Boolean activationComplete;
        /** OCC-1: whether this activation exited through the target throw;
         *  null on a non-target goal. */
        final Boolean targetReachedFlag;

        ResultRow(JsonObject raw, int line) {
            this.line = line;
            this.taskId = string(raw, "taskId");
            this.event = string(raw, "event");
            this.activationOrdinal = exactInteger(raw,
                    PathObservation.ACTIVATION_ORDINAL, -1);
            this.plannedOccurrenceId = exactText(raw,
                    PathObservation.PLANNED_OCCURRENCE_ID);
            this.rowOccurrenceId = exactText(raw, "occurrenceId");
            this.activationComplete = exactBoolean(raw,
                    "relationallyComplete");
            this.targetReachedFlag =
                    raw.has(PathObservation.TARGET_REACHED)
                    ? Boolean.valueOf(bool(raw,
                            PathObservation.TARGET_REACHED, false))
                    : null;
            this.skipKind = string(raw, "skipKind");
            this.skipReason = string(raw, "reason");
            this.exitKind = string(raw, "exitKind");
            this.exceptionType = string(raw, "exceptionType");
            this.engine = object(raw, "engineSummary");
            this.pathCut = raw.has("pathCut") ? object(raw, "pathCut") : null;
            this.resourceCut = raw.has("replayResourceCut")
                    ? object(raw, "replayResourceCut") : null;
            this.unresolvedInputs = array(raw, "unresolvedInputs");
            this.branchMappings = array(raw, "branchMappings");
            this.concreteBranchWitnesses = array(raw,
                    "concreteBranchWitnesses");
            this.statesBranchEvidence = raw.has("branchMappings")
                    || raw.has("concreteBranchWitnesses");
            this.vmHandoffs = raw.has(VmHandoffEvidence.FIELD)
                    ? array(raw, VmHandoffEvidence.FIELD) : null;
            this.sharedFieldVersions = array(raw, "sharedFieldVersions");
            this.sessionEventLedger = object(raw, "sessionEventLedger");
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
            this.readCutGaps = array(raw, "readCutGaps");
            this.targetReach = raw.get(
                    PathObservation.TargetReachEvent.FIELD);
            JsonElement root = raw.get("rootOutputExpression");
            this.rootOutput = root != null && root.isJsonObject()
                    ? root.getAsJsonObject() : null;
            this.decidedBranchSites = siteIds(branchMappings);
            SortedSet<String> sites = new TreeSet<>(decidedBranchSites);
            sites.addAll(siteIds(concreteBranchWitnesses));
            this.observedBranchSites = sites;
            this.capturesByBinding = new LinkedHashMap<>();
            SortedSet<String> bindings = new TreeSet<>();
            for (JsonElement element : array(raw, "outputCaptures")) {
                if (!element.isJsonObject()) continue;
                JsonObject capture = element.getAsJsonObject();
                String id = string(capture, "captureBindingId");
                if (id.isEmpty()) continue;
                capturesByBinding.computeIfAbsent(id,
                        ignored -> new ArrayList<>()).add(capture);
                bindings.add(id);
            }
            this.observedCaptureBindings = bindings;
            String refused = resultShapeRefusal(raw, event,
                    activationOrdinal, plannedOccurrenceId, rowOccurrenceId,
                    activationComplete);
            List<JsonObject> mints = new ArrayList<>();
            for (JsonElement element : array(raw, "symbolizedInputs")) {
                JsonObject mint = element.isJsonObject()
                        ? element.getAsJsonObject() : null;
                Boolean reused = mint == null ? null
                        : exactBoolean(mint, SymbolicSourceEvidence.REUSED);
                if (reused == null || !reused
                        && string(mint, SymbolicSourceEvidence.SYMBOL)
                        .isEmpty()) {
                    if (refused.isEmpty()) {
                        refused = SYMBOLIZED_INPUT_ROW_MALFORMED;
                    }
                    break;
                }
                mints.add(mint);
            }
            this.symbolizedInputs = mints;
            // The C2 census is required, not optional: silence and "this
            // producer found none" are different facts.
            List<JsonObject> free = Collections.emptyList();
            try {
                free = SymbolicSourceEvidence.freeSymbolsOf(raw);
            } catch (IllegalArgumentException unstated) {
                if (refused.isEmpty()) refused = FREE_SYMBOL_LEDGER_MISSING;
            }
            this.freeSymbols = free;
            List<JsonObject> minted = Collections.emptyList();
            String malformed = "";
            try {
                minted = SymbolicSourceEvidence.eventsOf(raw);
            } catch (IllegalArgumentException rejected) {
                malformed = firstNonBlank(rejected.getMessage(), "UNKNOWN");
            }
            this.symbolicSourceEvidence = minted;
            this.symbolicSourceEvidenceIssue = malformed;
            // README's resource rule: the runtime states this truncation
            // structurally, so the importer validates the stated row and
            // carries it, and never reconstructs one from prose.
            List<JsonObject> versionGaps = new ArrayList<>();
            for (JsonElement element : array(raw, "outputVersionGaps")) {
                JsonObject gap = element.isJsonObject()
                        ? element.getAsJsonObject() : null;
                if (gap == null
                        || !"OUTPUT_VERSION_ALIGNMENT_GAP".equals(
                                string(gap, "kind"))
                        || !"BOUNDED_OUTPUT_VERSION_CAPACITY_V1".equals(
                                string(gap, "authority"))
                        || string(gap, "captureBindingId").isEmpty()
                        || string(gap, "reason").isEmpty()
                        || exactInteger(gap, "versionCapacity", -1) < 0
                        || exactInteger(gap, "versionsObserved", -1) < 0
                        || exactInteger(gap, "versionsCaptured", -1) < 0) {
                    if (refused.isEmpty()) refused =
                            "OUTPUT_VERSION_GAP_ROW_MALFORMED";
                    break;
                }
                versionGaps.add(gap);
            }
            this.outputVersionGaps = versionGaps;
            this.refusal = refused;
        }

        /** Every capture that answered one binding, in observed order. */
        List<JsonObject> captures(String bindingId) {
            List<JsonObject> rows = capturesByBinding.get(bindingId);
            return rows == null ? Collections.<JsonObject>emptyList() : rows;
        }

        /** The roots this execution minted: a reused read is not a root, the
         * expression it carries names the root it was propagated from. */
        JsonArray mintedRoots() {
            JsonArray result = new JsonArray();
            Set<String> unique = new LinkedHashSet<>();
            for (JsonObject mint : symbolizedInputs) {
                if (!bool(mint, SymbolicSourceEvidence.REUSED, false)
                        && unique.add(string(mint,
                        SymbolicSourceEvidence.SYMBOL))) {
                    result.add(string(mint, SymbolicSourceEvidence.SYMBOL));
                }
            }
            return result;
        }

        /** The matched catalog rows this execution's hook ledger named. */
        SortedSet<String> observedSourcePhases() {
            SortedSet<String> result = new TreeSet<>();
            for (JsonElement element : sourcePhaseObservations) {
                if (!element.isJsonObject()) continue;
                String matched = string(element.getAsJsonObject(),
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
                String site = string(element.getAsJsonObject(), "siteId");
                if (!site.isEmpty()) result.add(site);
            }
            return result;
        }
    }

    public static void main(String[] args) throws Exception {
        Map<String, String> options = parseArgs(args);
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
        Path delta = Paths.get(firstNonBlank(options.get("topology-delta"),
                ArtifactIO.sibling(output, TopologyDelta.FILE_NAME).toString()));
        Set<String> regions = regionIds(RuntimePlanArtifact.read(
                runtimePlan).regions());
        String iterationId = requiredValue(options, "iteration-id");
        ImportResult imported = importSummaries(results, tasks, regions,
                output, diagnostics, delta, iterationId);
        if (imported.diagnosticCount > 0) {
            try (BufferedReader reader = Files.newBufferedReader(diagnostics,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    System.err.println("[concolic-import] " + line);
                }
            }
        }
        if (imported.validSummaryCount == 0
                && imported.rawResultCount > 0) {
            System.exit(2);
        }
    }

    static ImportResult importSummaries(
            Path resultsFile, Path taskPlanFile, Set<String> regions,
            Path outputFile, Path diagnosticFile, Path deltaFile,
            String iterationId) throws IOException {
        Map<String, ExecutionTask> tasks = taskIndex(
                ArtifactIO.readJsonl(taskPlanFile));
        List<JsonObject> rawResults = ArtifactIO.readJsonl(resultsFile);
        List<JsonObject> summaries = new ArrayList<>();
        List<JsonObject> diagnostics = new ArrayList<>();
        Set<String> hashes = new LinkedHashSet<>();
        // README "Delta ownership is also singular": the frozen-plan
        // comparison happens here, while each raw row is imported, and not as
        // a later pass over a second store.
        TopologyDelta delta = new TopologyDelta(iterationId,
                tasks.values());
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
                delta.classify(tasks.get(row.taskId), row,
                        TopologyDelta.Observation.refused(code));
                continue;
            }
            ExecutionTask task = tasks.get(row.taskId);
            if (task == null) {
                diagnostics.add(diagnostic(row,
                        "UNKNOWN_EXECUTION_TASK", row.taskId));
                delta.classify(null, row,
                        TopologyDelta.Observation.unplanned(
                                "UNKNOWN_EXECUTION_TASK"));
                continue;
            }
            if (!regions.contains(task.regionId())) {
                diagnostics.add(diagnostic(row,
                        "UNKNOWN_REGION", task.regionId()));
                delta.classify(task, row,
                        TopologyDelta.Observation.unplanned("UNKNOWN_REGION"));
                continue;
            }
            TopologyDelta.Observation observation =
                    new TopologyDelta.Observation();
            JsonObject summary = importRow(row, task, hashes,
                    diagnostics, observation);
            if (summary != null) {
                // The VM's location rid is a per-session allocation ordinal,
                // so two replays of one occurrence name the same map with
                // different rids and every later index splits it in two.
                for (String location
                        : SharedStateEvidence.canonicalizeLocations(summary)) {
                    diagnostics.add(diagnostic(row,
                            "LOCATION_NOT_NAMED_ACROSS_SESSIONS", location));
                }
                for (String location : SharedStateEvidence
                        .canonicalizeContainerStateSymbols(summary)) {
                    diagnostics.add(diagnostic(row,
                            "AMBIGUOUS_CONTAINER_STATE_INPUT", location));
                }
                for (String entry
                        : unmaterializedConfiguredSourceRoots(row)) {
                    diagnostics.add(diagnostic(row,
                            CONFIGURED_SOURCE_ROOT_NOT_MATERIALIZED, entry));
                }
                summaries.add(summary);
            }
            delta.classify(task, row, observation);
        }
        // A planned activation that produced no row at all is the plainest
        // "planned event that did not occur"; it is named, never dropped.
        delta.classifyUnobservedTasks(tasks.values());

        ArtifactIO.replaceJsonl(outputFile, summaries);
        ArtifactIO.replaceJsonl(diagnosticFile, diagnostics);
        // Written even when empty: an absent file and an empty file must not
        // mean the same thing to the campaign that validates it.
        ArtifactIO.replaceJsonl(deltaFile, delta.rows());
        return new ImportResult(rawResults.size(), summaries.size(),
                diagnostics.size());
    }

    /** Imports one raw VM result, or refuses it under one named gap.
     *
     * @return the admitted summary, or {@code null} when the row was refused
     */
    /**
     * OCC-1: the activations each task published, counted once over the whole
     * results file.
     *
     * <p>Two findings are task-level and cannot be made while importing a
     * single row: an ordinal published twice (the runtime's activation
     * counter is not a counter), and a target task none of whose activations
     * reached the target.  Both are named here and both stay refusals -- the
     * rows themselves are still imported, so a reader can see what the
     * activations did instead of being handed an empty member set.</p>
     */
    private static final class ActivationCensus {
        private final Map<String, Set<Integer>> ordinalsByTask =
                new LinkedHashMap<>();
        private final Map<String, List<Integer>> duplicatesByTask =
                new LinkedHashMap<>();
        private final Set<String> targetReachedTasks = new LinkedHashSet<>();

        private static ActivationCensus of(List<JsonObject> rawResults) {
            ActivationCensus census = new ActivationCensus();
            for (JsonObject raw : rawResults) {
                if (!"CONCOLIC_REGION_RESULT".equals(string(raw, "event"))) {
                    continue;
                }
                int ordinal = exactInteger(raw,
                        PathObservation.ACTIVATION_ORDINAL, -1);
                if (ordinal < 1) continue;
                String taskId = string(raw, "taskId");
                if (!census.ordinalsByTask.computeIfAbsent(taskId,
                        ignored -> new LinkedHashSet<>()).add(ordinal)) {
                    census.duplicatesByTask.computeIfAbsent(taskId,
                            ignored -> new ArrayList<>()).add(ordinal);
                }
                if (bool(raw, PathObservation.TARGET_REACHED, false)) {
                    census.targetReachedTasks.add(taskId);
                }
            }
            return census;
        }

        private void refusals(Map<String, ExecutionTask> tasks,
                              List<JsonObject> diagnostics) {
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
                        + "exited through the selected target throw"));
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
            TopologyDelta.Observation observation) {
        // The decode already refused an artifact shape this importer does not
        // read; it is a named gap like any other.
        if (!row.refusal.isEmpty()) {
            return refuse(row, row.refusal, row.exitKind, diagnostics,
                    observation);
        }
        // An aborted symbolic execution stops recording branch events and path
        // condition at the point it gave up, and the activation then runs on
        // concretely to whatever exit it reaches.
        JsonObject engine = row.engine;
        if (bool(engine, "aborted", false)) {
            return refuse(row, "SYMBOLIC_EXECUTION_ABORTED",
                    firstNonBlank(string(engine, "abortReason"),
                            "UNSPECIFIED"), diagnostics, observation);
        }
        String exitKind = row.exitKind;
        boolean hasCut = row.pathCut != null || row.resourceCut != null;
        if ("CUT".equals(exitKind)
                || hasCut && !boundedOutputExit(row, task)) {
            // The two ledgers cut for opposite reasons and are answered by
            // opposite work: an unroll bound says the path space was too wide
            // to walk, a resource cap says a service loop outlasted the replay
            // budget.
            boolean resourceCut = row.resourceCut != null;
            String cutDetail = (resourceCut ? row.resourceCut : row.pathCut)
                    .toString();
            if (resourceCut && !hasCapturedDemandedOutput(row, task)) {
                cutDetail += "; no demanded output relation was "
                        + "captured before cut";
            }
            // No admitted bounded prefix exists here.  Keep the cut as an
            // explicit gap rather than inventing an output relation.
            return refuse(row, resourceCut ? "REPLAY_LOOP_RESOURCE_CAP"
                            : "LOOP_BOUND_PATH_CUT", cutDetail,
                    diagnostics, observation);
        }
        List<String> issues = new ArrayList<>();
        for (JsonElement unresolved : row.unresolvedInputs) {
            issues.add("UNRESOLVED_INPUT:" + unresolved);
        }

        boolean relationOnlySeed = relationOnlySeed(task);
        // A relation-only seed that carries no decision at all still imports
        // as empty.
        boolean anyBranchDecision =
                SemanticPath.hasAdmissibleBranchDecision(
                        row.branchMappings);
        boolean pathConditionOmitted = bool(engine,
                "pathConditionOmitted", false);
        boolean branchAndAuxiliarySummary =
                SELECTED_BRANCH_AND_AUXILIARY_AUTHORITY.equals(
                        string(engine, "pathConditionAuthority"));
        if (pathConditionOmitted) {
            JsonElement omittedPath = engine.get("pathCondition");
            if (omittedPath == null || !omittedPath.isJsonArray()
                    || omittedPath.getAsJsonArray().size() != 0) {
                issues.add("OMITTED_PATH_CONDITION_NOT_EMPTY");
            }
            if (!branchAndAuxiliarySummary) {
                issues.add("OMITTED_PATH_CONDITION_AUTHORITY_MISSING");
            }
            if (!bool(engine, "active", false)) {
                issues.add("OMITTED_PATH_CONDITION_ENGINE_INACTIVE");
            }
        } else if (bool(engine, "active", false)) {
            // Only the selected branch plus bounded auxiliary channel is
            // admitted.
            issues.add("AMBIENT_PATH_CONDITION_NOT_ADMITTED");
        }
        if (!bool(engine, "complete", false)) {
            issues.add("VM_SUMMARY_INCOMPLETE:"
                    + string(engine, "abortReason"));
        }
        // One shape, one reader.
        SemanticPath path = SemanticPath.fromSelectedEvidence(engine,
                row.branchMappings, issues);
        JsonArray mappings = relationOnlySeed && !anyBranchDecision
                ? new JsonArray()
                : branchMappings(row, task, path, issues);
        JsonObject targetReach = admittedTargetReach(row, task,
                path.expressions, mappings, diagnostics, observation);
        if (targetReach == null) return null;
        String branchReplayMismatch = relationOnlySeed ? ""
                : branchReplayMismatch(row, task, mappings);
        if (!branchReplayMismatch.isEmpty()) {
            return refuse(row, "BRANCH_REPLAY_MISMATCH",
                    branchReplayMismatch, diagnostics, observation);
        }
        JsonObject outputs = outputExpressions(row, task, issues);
        JsonArray interactionEvents = interactionEvents(row, task, issues);
        PathLoopCounts loopCounts = pathLoopCounts(row, task);
        if (!loopCounts.refusal.isEmpty()) {
            return refuse(row, LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND,
                    loopCounts.refusal, diagnostics, observation);
        }
        JsonArray alignmentGaps = alignmentGaps(task, row);
        JsonObject recordedSharedState =
                recordedSharedState(row, alignmentGaps);
        List<JsonObject> vmHandoffEvents =
                vmHandoffEvents(row, alignmentGaps);
        // The catalog of declared mint SITES, decoded once by the task row.
        List<ConfiguredSourcePhaseContract.Occurrence> mintSites =
                task.configuredSourcePhases();
        validateConfiguredSourcePhaseObservations(row, mintSites, issues);
        JsonArray symbolicSources = symbolicSourceEvidence(row, task,
                mintSites, issues);
        // A replay that carried a selected read cut is validated against
        // its own recorded evidence, never against the reference run's
        // event ids: this is a different session, and its events restart.
        ReplayedReadCut readCut = ReplayedReadCut.validate(
                SelectedReadCut.planOf(task.json()),
                Collections.singletonList(recordedSharedState));
        for (JsonObject gap : readCut.gaps()) alignmentGaps.add(gap);
        JsonArray symbolicInputs = row.mintedRoots();
        JsonElement replayContract = task.replayContract();

        JsonObject summary = new JsonObject();
        summary.addProperty("schemaVersion", 1);
        summary.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        summary.addProperty("goalId", task.goalId());
        summary.addProperty("taskId", task.taskId());
        summary.addProperty("sourceKey", task.sourceKey());
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
        if (task.outputClosure() != null) {
            summary.add(OutputClosureContract.FIELD,
                    task.outputClosure().toJson());
        }
        summary.add("symbolicInputs", symbolicInputs);
        if (symbolicSources.size() > 0) {
            summary.add(SymbolicSourceEvidence.FIELD, symbolicSources);
        }
        summary.add("edgeBindings", resolvedEdgeBindings(task,
                recordedSharedState));
        summary.add("pathCondition", path.expressions);
        summary.add("branchMappings", mappings);
        if (targetReach.size() > 0) {
            summary.add(PathObservation.TargetReachEvent.FIELD,
                    targetReach);
        }
        if (pathConditionOmitted) {
            summary.addProperty("pathConditionAuthority",
                    SELECTED_BRANCH_AND_AUXILIARY_AUTHORITY);
            summary.addProperty("pathConditionVmWatermark",
                    path.vmWatermark());
        }
        summary.add("outputExpressions", outputs);
        if (loopCounts.counts.size() > 0) {
            summary.add(LoopBoundPolicy.PATH_LOOP_COUNTS,
                    loopCounts.counts);
        }
        if (loopCounts.gaps.size() > 0) {
            summary.add(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS,
                    loopCounts.gaps);
        }
        if (interactionEvents.size() > 0) {
            summary.add(RelationSummary.INTERACTION_EVENTS,
                    interactionEvents);
        }
        if (alignmentGaps.size() > 0) {
            summary.add("alignmentGaps", alignmentGaps);
        }
        if (recordedSharedState.size() > 0) {
            summary.add(SharedStateEvidence.RECORDED_FIELD,
                    recordedSharedState);
        }
        VmHandoffEvidence.writeTo(summary, vmHandoffEvents);
        // C2 coverage travels with the case, never as a refusal: the composer
        // reads this ledger off every case-evidence row, so a row that states
        // nothing hands the case an empty array.
        JsonArray freeSymbols = new JsonArray();
        for (JsonObject free : row.freeSymbols) freeSymbols.add(free);
        summary.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, freeSymbols);
        boolean boundedExit = "BOUNDED".equals(exitKind);
        summary.addProperty("normalExit", boundedExit
                || "NORMAL".equals(exitKind));
        summary.addProperty("boundedExit", boundedExit);
        summary.addProperty("exceptionType", row.exceptionType);
        // OCC-1: the runtime states whether THIS activation satisfied the
        // demanded boundary.  The importer's own findings still decide, and
        // the runtime's "no" is folded in as one more named issue: an
        // activation the recorder called incomplete never becomes a complete
        // case just because the importer found nothing else wrong with it.
        if (Boolean.FALSE.equals(row.activationComplete)
                && issues.isEmpty()) {
            issues.add("ACTIVATION_BOUNDARY_INCOMPLETE:a"
                    + row.activationOrdinal);
        }
        summary.addProperty("relationallyComplete", issues.isEmpty());

        if (replayContract != null && !issues.isEmpty()) {
            return refuse(row, "PATH_REPLAY_ADMISSION_REJECTED",
                    String.join(";", issues), diagnostics, observation);
        }

        JsonObject semantic = summary.deepCopy();
        semantic.remove("taskId");
        String hash = sha256(CanonicalJson.render(semantic));
        if (!hashes.add(hash)) {
            return refuse(row, "DUPLICATE_SUMMARY", hash, diagnostics,
                    observation);
        }
        summary.addProperty("summaryId",
                "SUMMARY." + task.regionId() + "." + hash);
        if (!issues.isEmpty()) {
            diagnostics.add(diagnostic(row, "INCOMPLETE_RELATION",
                    String.join(";", issues)));
            observation.gap = "INCOMPLETE_RELATION";
        }
        observation.summary = summary;
        // Exact typed delivery evidence and recorded state versions are
        // different evidence classes from the guarded case itself, so the
        // delta names each of them once beside it.
        observation.binding = !vmHandoffEvents.isEmpty();
        observation.effect = recordedSharedState.size() > 0;
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
                    string(observation, "kind"))
                    && "EXACT_ACTIVE_CALL_SITE_REPLAY_V1".equals(
                    string(observation, "authority"))
                    && index == expectedIndex;
            expectedIndex++;
            if (!exactSchema) {
                issues.add("SYMBOLIC_SOURCE_PHASE_OBSERVATION_MALFORMED:"
                        + index);
                continue;
            }
            String phaseId = string(observation, "matchedPhaseId");
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
            String loopSiteId = string(declaration,
                    LoopBoundPolicy.LOOP_SITE_ID);
            String classification = string(declaration,
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
            int bodyCount = runtimeLoopId.isEmpty()
                    ? -1 : integer(bodies, runtimeLoopId, -1);
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
            JsonObject row = declaration.deepCopy();
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

    /** Exact dynamic array lengths published for one runtime natural loop. */
    private static JsonArray exactCardinalities(
            ResultRow source, String runtimeLoopId, String loopSiteId,
            PathLoopCounts result) {
        JsonArray exact = new JsonArray();
        Map<Integer, Integer> byOccurrence = new LinkedHashMap<>();
        for (JsonElement element : source.loopCardinalities) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (!runtimeLoopId.equals(string(row,
                    LoopBoundPolicy.RUNTIME_LOOP_ID))) {
                continue;
            }
            int occurrence = integer(row,
                    LoopBoundPolicy.DYNAMIC_OCCURRENCE, -1);
            int cardinality = integer(row,
                    LoopBoundPolicy.LOOP_CARDINALITY, -1);
            if (occurrence < 1 || cardinality < 0
                    || !LoopBoundPolicy.PATH_CARDINALITY_AUTHORITY.equals(
                    string(row, "cardinalityAuthority"))) {
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
            exact.add(row.deepCopy());
        }
        for (JsonElement element : source.loopCardinalityGaps) {
            if (!element.isJsonObject()) continue;
            JsonObject gap = element.getAsJsonObject();
            if (!runtimeLoopId.equals(string(gap,
                    LoopBoundPolicy.RUNTIME_LOOP_ID))) {
                continue;
            }
            result.gap(firstNonBlank(string(gap, "reason"),
                            LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS),
                    loopSiteId, firstNonBlank(string(gap, "detail"),
                            "runtime array cardinality observation gap"));
        }
        return exact;
    }

    /** Exact natural-loop counter id published with the retained loop. */
    private static String runtimeLoopId(JsonObject declaration) {
        return string(declaration, LoopBoundPolicy.RUNTIME_LOOP_ID);
    }

    private static final class PathLoopCounts {
        private final JsonArray counts = new JsonArray();
        private final JsonArray gaps = new JsonArray();
        private String refusal = "";

        private void gap(String reason, String subject, String detail) {
            JsonObject row = new JsonObject();
            row.addProperty("kind", "PATH_LOCAL_LOOP_COUNT_GAP");
            row.addProperty("authority", "PATH_LOCAL_LOOP_COUNT_GAP_V1");
            row.addProperty("reason", reason);
            row.addProperty("subject", subject);
            row.addProperty("detail", detail);
            gaps.add(row);
        }
    }

    /** Files one named import gap and refuses the row under that same code,
     * which is also what the delta carries as the gap. */
    private static JsonObject refuse(ResultRow row, String code,
                                     String detail,
                                     List<JsonObject> diagnostics,
                                     TopologyDelta.Observation observation) {
        diagnostics.add(diagnostic(row, code, detail));
        observation.gap = code;
        return null;
    }

    /** Joins the planned output-version gaps with the handoff gaps this
     * execution recorded. */
    private static JsonArray alignmentGaps(ExecutionTask task,
                                           ResultRow row) {
        JsonArray result = new JsonArray();
        for (JsonObject gap : row.outputVersionGaps) {
            result.add(gap.deepCopy());
        }
        if (task.outputClosure() != null) {
            for (OutputClosureContract.Member member
                    : task.outputClosure().members()) {
                for (JsonElement gap : array(member.slice(),
                        "alignmentGaps")) {
                    result.add(gap.deepCopy());
                }
            }
        }
        for (JsonElement gap : row.rpcHandoffGaps) {
            if (gap.isJsonObject()
                    && RpcExpressionHandoff.isGap(gap.getAsJsonObject())) {
                result.add(gap.deepCopy());
            }
        }
        for (JsonElement gap : row.sharedStateGaps) {
            if (gap.isJsonObject()
                    && SharedStateEvidence.isGap(gap.getAsJsonObject())) {
                result.add(gap.deepCopy());
            }
        }
        for (JsonElement gap : row.readCutGaps) {
            if (gap.isJsonObject() && SparseReadCutGate.GAP_KIND.equals(
                    string(gap.getAsJsonObject(), "kind"))) {
                result.add(gap.deepCopy());
            }
        }
        return result;
    }

    /** Applies this execution's recorded read-from evidence to the candidate
     * writers the trace retained. */
    private static JsonArray resolvedEdgeBindings(ExecutionTask task,
                                                  JsonObject recorded) {
        JsonArray bindings = task.edgeBindings();
        if (recorded.size() == 0 || bindings.size() == 0) return bindings;
        List<JsonObject> rows = new ArrayList<>();
        for (JsonElement element : bindings) {
            if (element.isJsonObject()) rows.add(element.getAsJsonObject());
        }
        RecordedReadFrom.index(Collections.singletonList(recorded))
                .resolve(rows);
        return bindings;
    }

    /** Ingests the VM handoff references this execution recorded.
     *
     * <p>Schema {@value VmHandoffEvidence#SCHEMA_VERSION} requires the attach
     * endpoint (README {@code RPC-1}).</p> */
    private static List<JsonObject> vmHandoffEvents(ResultRow row,
                                                    JsonArray gaps) {
        List<JsonObject> events = new ArrayList<>();
        if (row.vmHandoffs == null) return events;
        for (JsonElement element : row.vmHandoffs) {
            JsonObject record = element.isJsonObject()
                    ? element.getAsJsonObject() : new JsonObject();
            if (VmHandoffEvidence.isEvent(record)) {
                events.add(record);
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

    /** Admits every mint this replay recorded at a declared hook site.
     * Every occurrence of a declared site is its own symbol, so nothing
     * here predicts which of them a given replay executed. */
    private static JsonArray symbolicSourceEvidence(
            ResultRow row, ExecutionTask task,
            List<ConfiguredSourcePhaseContract.Occurrence> catalog,
            List<String> issues) {
        Map<String, ConfiguredSourcePhaseContract.Occurrence> mintSites =
                new LinkedHashMap<>();
        for (ConfiguredSourcePhaseContract.Occurrence phase : catalog) {
            if (mintSites.putIfAbsent(phase.phaseId(), phase) != null) {
                issues.add("SYMBOLIC_SOURCE_PHASE_CATALOG_MALFORMED:"
                        + phase.phaseId());
            }
        }
        JsonArray admitted = new JsonArray();
        Set<String> observed = new LinkedHashSet<>();
        if (!row.symbolicSourceEvidenceIssue.isEmpty()) {
            issues.add("SYMBOLIC_SOURCE_EVIDENCE_MALFORMED:"
                    + row.symbolicSourceEvidenceIssue);
            return admitted;
        }
        for (JsonObject event : row.symbolicSourceEvidence) {
            String phaseId = string(event, "sourcePhaseId");
            String id = string(event, "sourceId");
            String field = string(event, "fieldSignature");
            String sourceOccurrence = string(event,
                    "sourceOccurrenceId");
            String expectedOccurrence = row.rowOccurrenceId;
            boolean exactRowOccurrence = sourceOccurrence.equals(
                    expectedOccurrence);
            ConfiguredSourcePhaseContract.Occurrence phase =
                    mintSites.get(phaseId);
            if (phase == null
                    || !exactRowOccurrence
                    || !id.equals(phase.sourceId())
                    || !field.equals(phase.fieldSignature())
                    || !observed.add(phaseId)) {
                issues.add("SYMBOLIC_SOURCE_EVIDENCE_NOT_DECLARED:"
                        + phaseId + ":" + id);
                continue;
            }
            admitted.add(event.deepCopy());
        }
        return admitted;
    }

    /** Ingests the shared-state evidence this execution recorded. */
    private static JsonObject recordedSharedState(ResultRow row,
                                                  JsonArray gaps) {
        List<JsonObject> versions = new ArrayList<>();
        for (JsonElement element : row.sharedFieldVersions) {
            JsonObject record = element.isJsonObject()
                    ? element.getAsJsonObject() : new JsonObject();
            if (SharedStateEvidence.isVersionsRecord(record)) {
                versions.add(record);
            } else {
                gaps.add(SharedStateEvidence.gap(
                        SharedStateEvidence.STAGE_VERSIONS,
                        SharedStateEvidence.MALFORMED_ENVELOPE,
                        string(record, "locationKey"),
                        "recorded version store did not survive import "
                                + "admission"));
            }
        }
        JsonObject ledger = row.sessionEventLedger;
        if (ledger.size() > 0
                && !SharedStateEvidence.isLedgerRecord(ledger)) {
            gaps.add(SharedStateEvidence.gap(
                    SharedStateEvidence.STAGE_LEDGER,
                    SharedStateEvidence.MALFORMED_ENVELOPE, "",
                    "recorded event ledger did not survive import "
                            + "admission"));
        }
        return SharedStateEvidence.recorded(versions, ledger);
    }

    /** Admits a VM row only when it belongs to the canonical bounded path that
     * selected the task. */
    private static String branchReplayMismatch(
            ResultRow row, ExecutionTask task, JsonArray mappings) {
        JsonElement encodedReplay = task.replayContract();
        BranchEventCatalog seed = taskSeedEvents(task);
        if (!seed.issue.isEmpty()) {
            return seed.issue;
        }
        BranchEventCatalog observed = observedBranchEvents(mappings,
                encodedReplay == null ? task : null);
        if (!observed.issue.isEmpty()) {
            return observed.issue;
        }
        if (encodedReplay == null) {
            return exactSeedMismatch(task.goalId(), seed.events,
                    observed.events, concreteBranchOutcomes(row),
                    "BOUNDED".equals(row.exitKind));
        }
        if (!encodedReplay.isJsonObject()) {
            return "replayContract is not an object";
        }

        final BranchReplayContract replay;
        try {
            replay = BranchReplayContract.fromJson(
                    encodedReplay.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            return "malformed replayContract: " + malformed.getMessage();
        }
        return replayPrefixMismatch(task.goalId(), observed.events, replay);
    }

    private static BranchEventCatalog taskSeedEvents(ExecutionTask task) {
        BranchEventCatalog result = new BranchEventCatalog();
        JsonObject selectedTarget = object(task.json(), "targetBranch");
        String targetSite = string(selectedTarget, "siteId");
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
            String site = string(branch, "siteId");
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
                BranchEvent event = new BranchEvent(site, ordinal, outcome);
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
        String targetSite = string(selectedTarget, "siteId");
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
                mapping = SummaryBranchMapping.fromJson(
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
            BranchEvent event = new BranchEvent(mapping.siteId(),
                    mapping.occurrence(), mapping.sourceTakenOutcome());
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

    /** Attests a seed replay against the recorded branch witnesses. */
    private static String exactSeedMismatch(
            String replayId, List<BranchEvent> expected,
            List<BranchEvent> observed,
            Map<String, Set<Boolean>> concrete, boolean earlyStop) {
        Map<String, Set<Boolean>> wanted = outcomesBySite(expected);
        Map<String, Set<Boolean>> actual = outcomesBySite(observed);
        for (Map.Entry<String, Set<Boolean>> entry : wanted.entrySet()) {
            Set<Boolean> found = union(actual.get(entry.getKey()),
                    concrete.get(entry.getKey()));
            if (found.isEmpty()) {
                if (earlyStop) continue;
                return replayDetail(replayId, "missing " + entry.getKey());
            }
            for (Boolean outcome : entry.getValue()) {
                if (!found.contains(outcome)) {
                    return replayDetail(replayId, "wrong outcome at "
                            + entry.getKey() + ": expected " + outcome
                            + " but observed " + found);
                }
            }
        }
        for (String site : actual.keySet()) {
            if (!wanted.containsKey(site)) {
                return replayDetail(replayId, "unexpected " + site);
            }
        }
        return "";
    }

    /** Indexes the branches an activation executed before its symbolic gate
     * opened. */
    private static Map<String, Set<Boolean>> concreteBranchOutcomes(
            ResultRow row) {
        Map<String, Set<Boolean>> outcomes = new LinkedHashMap<>();
        for (JsonElement element : row.concreteBranchWitnesses) {
            if (!element.isJsonObject()) continue;
            JsonObject witness = element.getAsJsonObject();
            String site = string(witness, "siteId");
            JsonElement outcome = witness.get("sourceTakenOutcome");
            if (site.isEmpty() || outcome == null
                    || !outcome.isJsonPrimitive()
                    || !outcome.getAsJsonPrimitive().isBoolean()) {
                continue;
            }
            Set<Boolean> seen = outcomes.get(site);
            if (seen == null) {
                seen = new LinkedHashSet<>();
                outcomes.put(site, seen);
            }
            seen.add(outcome.getAsBoolean());
        }
        return outcomes;
    }

    private static Set<Boolean> union(Set<Boolean> first, Set<Boolean> second) {
        Set<Boolean> result = new LinkedHashSet<>();
        if (first != null) result.addAll(first);
        if (second != null) result.addAll(second);
        return result;
    }

    private static String replayPrefixMismatch(
            String replayId, List<BranchEvent> observed,
            BranchReplayContract replay) {
        List<BranchEvent> expected = new ArrayList<>();
        for (BranchWitness witness : replay.orderedPrefix()) {
            if (witness.isPcPredicateDecision()) continue;
            expected.add(new BranchEvent(witness.siteId(),
                    witness.occurrence(), witness.sourceTakenOutcome()));
        }
        BranchWitness source = replay.source();
        expected.add(new BranchEvent(source.siteId(), source.occurrence(),
                replay.requiredTakenOutcome()));

        int next = 0;
        for (BranchEvent actual : observed) {
            if (next == expected.size()) {
                // The flip source has been reached.  Its suffix is precisely
                // the new path that concolic exploration is meant to discover.
                break;
            }
            BranchEvent wanted = expected.get(next);
            if (wanted.identity.equals(actual.identity)) {
                if (wanted.outcome != actual.outcome) {
                    return replayDetail(replayId, "wrong replay outcome at "
                            + wanted.siteOccurrence() + ": expected "
                            + wanted.outcome + " but observed "
                            + actual.outcome);
                }
                next++;
                continue;
            }
            for (int future = next + 1; future < expected.size(); future++) {
                if (expected.get(future).identity.equals(actual.identity)) {
                    return replayDetail(replayId, "replay event "
                            + actual.siteOccurrence() + " occurred before "
                            + wanted.siteOccurrence());
                }
            }
            // A union-instrumented campaign records selected sites belonging
            // to other tasks as well.
        }
        if (next != expected.size()) {
            return replayDetail(replayId, "missing replay event "
                    + expected.get(next).display());
        }
        return "";
    }

    private static Map<String, Set<Boolean>> outcomesBySite(
            List<BranchEvent> events) {
        Map<String, Set<Boolean>> result = new LinkedHashMap<>();
        for (BranchEvent event : events) {
            result.computeIfAbsent(event.site,
                    ignored -> new LinkedHashSet<>()).add(event.outcome);
        }
        return result;
    }

    private static Boolean exactBoolean(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                ? value.getAsBoolean() : null;
    }

    private static String exactText(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isString()
                ? value.getAsString().trim() : "";
    }

    private static String resultShapeRefusal(
            JsonObject raw, String event, int activationOrdinal,
            String plannedOccurrenceId, String occurrenceId,
            Boolean relationallyComplete) {
        if (!"CONCOLIC_REGION_RESULT".equals(event)) return "";
        if (exactInteger(raw, "schemaVersion", -1) != 1) {
            return RESULT_SCHEMA_UNSUPPORTED;
        }
        if (activationOrdinal < 1 || plannedOccurrenceId.isEmpty()
                || !occurrenceId.equals(plannedOccurrenceId + "#a"
                + activationOrdinal) || relationallyComplete == null) {
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
            List<JsonObject> diagnostics,
            TopologyDelta.Observation observation) {
        if (!task.goalKind().capturesTargetReach()) {
            return new JsonObject();
        }
        if (row.targetReach == null) {
            return refuse(row, "TARGET_REACH_EVENT_MISSING",
                    "selected target execution published no targetReach",
                    diagnostics, observation);
        }
        final PathObservation.TargetReachEvent event;
        try {
            event = PathObservation.TargetReachEvent.decode(row.targetReach);
        } catch (IllegalArgumentException malformed) {
            return refuse(row, "TARGET_REACH_EVENT_MALFORMED",
                    firstNonBlank(malformed.getMessage(), "UNKNOWN"),
                    diagnostics, observation);
        }

        JsonObject selected = object(task.json(), "targetBranch");
        String selectedSite = string(selected, "siteId");
        int selectedOccurrence = JsonFields.exactInteger(selected,
                "occurrence", -1);
        if (!event.siteId().equals(selectedSite)
                || event.occurrence() != selectedOccurrence) {
            return refuse(row, "TARGET_REACH_EVENT_MISMATCH",
                    "event " + event.siteId() + "#" + event.occurrence()
                            + " does not match selected target "
                            + firstNonBlank(selectedSite, "<missing>") + "#"
                            + selectedOccurrence, diagnostics, observation);
        }

        JsonObject canonical = new JsonObject();
        canonical.add("pathCondition", pathCondition.deepCopy());
        canonical.add("branchMappings", mappings.deepCopy());
        int exactMappings = 0;
        try {
            for (SummaryBranchMapping mapping
                    : SummaryBranchMapping.fromSummary(canonical)) {
                if (event.matches(mapping.siteId(),
                        mapping.occurrence(),
                        mapping.sourceTakenOutcome())) {
                    exactMappings++;
                }
            }
        } catch (IllegalArgumentException malformed) {
            return refuse(row, "TARGET_REACH_EVENT_MISMATCH",
                    "target branch evidence is malformed: "
                            + firstNonBlank(malformed.getMessage(),
                            "UNKNOWN"), diagnostics, observation);
        }
        if (exactMappings != 1) {
            return refuse(row, "TARGET_REACH_EVENT_MISMATCH",
                    "event has " + exactMappings
                            + " exact branch mapping(s)",
                    diagnostics, observation);
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

    private static final class BranchEvent {
        private final String site;
        private final int occurrence;
        private final boolean outcome;
        private final String identity;

        private BranchEvent(String site, int occurrence, boolean outcome) {
            this.site = site;
            this.occurrence = occurrence;
            this.outcome = outcome;
            this.identity = site + "\u0000" + occurrence;
        }

        private String siteOccurrence() {
            return site + '#' + occurrence;
        }

        private String display() {
            return siteOccurrence() + '=' + outcome;
        }
    }

    private static boolean boundedOutputExit(ResultRow row,
                                             ExecutionTask task) {
        if (!task.goalKind().capturesOutputRelation()
                || !"BOUNDED".equals(row.exitKind)) {
            return false;
        }
        if (row.resourceCut != null) {
            JsonObject cut = row.resourceCut;
            int maxBodies = integer(cut, "maxLoopBodies", -1);
            long attemptedBody = longInteger(cut, "attemptedBody", -1L);
            return "REPLAY_LOOP_RESOURCE_CAP".equals(string(cut, "kind"))
                    && "REPLAY_LOOP_RESOURCE_CAP".equals(
                    string(cut, "reason"))
                    && !string(cut, "loopId").isEmpty()
                    && maxBodies > 0
                    && attemptedBody > maxBodies
                    && hasCapturedDemandedOutput(row, task);
        }
        JsonObject cut = row.pathCut;
        String loopId = string(cut, "backedgeId");
        return "LOOP_BOUND".equals(string(cut, "kind"))
                && "MAX_LOOP_BODY_ITERATIONS_REACHED".equals(
                string(cut, "reason"))
                && !loopId.isEmpty()
                && task.loopBound().acceptsInstrumentedBound(
                integer(cut, "maxBackedgeTraversals", -1))
                && hasCapturedDemandedOutput(row, task);
    }

    /** Admits only a complete, exact producer prefix as a normal relation. */
    /** Resource-bounded output is admitted per port. */
    private static boolean hasCapturedDemandedOutput(
            ResultRow row, ExecutionTask task) {
        if (!task.goalKind().capturesOutputRelation()
                || task.outputCaptures().isEmpty()) {
            return false;
        }
        for (OutputCaptureSpec request : task.outputCaptures()) {
            if (!(request.capturesCallOutput()
                    || request.capturesCommunicationEffect()
                    || request.capturesFieldWriteState()
                    || request.capturesMutationState())) {
                continue;
            }
            for (JsonObject capture
                    : row.captures(request.captureBindingId())) {
                JsonElement expression = capture.get("expression");
                boolean related = request.capturesCommunicationEffect()
                        ? "COMMUNICATION_EFFECT".equals(
                        string(capture, "interactionKind"))
                        && "INSTRUMENTED_INTERACTION_SITE_V1".equals(
                        string(capture, "authority"))
                        : expression != null && !expression.isJsonNull();
                if (related
                        && exactOutputCaptureOccurrence(request, capture)) {
                    return true;
                }
            }
        }
        return false;
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
            String site = string(row, "siteId");
            int occurrence = integer(row, "occurrence", -1);
            if (site.isEmpty() || occurrence < 1
                    || !events.add(site + "\u0000" + occurrence)) {
                issues.add("AMBIGUOUS_BRANCH_EVENT:" + site);
                continue;
            }
            SummaryBranchMapping.Policy policy = policies.get(site);
            if (policy == null) {
                policy = SummaryBranchMapping.Policy.PATH_ASSUMPTION;
            }
            try {
                BranchWitness direct = null;
                ExactConcreteBranchObservation concrete = null;
                if (row.has("witness")
                        && row.get("witness").isJsonObject()) {
                    direct = BranchWitness.fromJson(
                            row.getAsJsonObject("witness"));
                    int pcIndex = direct.vmPcIndex();
                    JsonElement originalPredicate = path.originalAt(pcIndex);
                    if (pcIndex < 0 || pcIndex >= path.vmWatermark()
                            || originalPredicate == null
                            || !BranchPredicateAlgebra.equivalent(
                            direct.sourceSatisfiedPredicate(),
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
                            direct.atPcIndex(summaryPcIndex),
                            summaryPcIndex, policy).toJson());
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

    /** True only for a binary VM predicate that would need branch authority. */
    private static boolean pcPredicate(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        if (!"BinaryExpression".equals(string(object, "_type"))
                || ContainerSmtCodec.handlesFieldBinding(expression)
                || ContainerSmtCodec.handlesAccessConstraint(expression)) {
            return false;
        }
        try {
            BranchPredicateAlgebra.complementOperator(
                    string(object, "_op"));
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
            String site = string(branch, "siteId");
            try {
                result.put(site, SummaryBranchMapping.Policy.fromWire(
                        string(branch, "policy")));
            } catch (IllegalArgumentException unsupported) {
                result.put(site, SummaryBranchMapping.Policy.EXPLORE);
            }
        }
        return result;
    }

    private static JsonObject outputExpressions(
            ResultRow row, ExecutionTask task, List<String> issues) {
        JsonObject result = new JsonObject();
        OutputClosureContract closure = task.outputClosure();
        if (closure == null) return result;

        Map<String, List<OutputCaptureSpec>> specsByPort =
                new LinkedHashMap<>();
        for (OutputCaptureSpec spec : task.outputCaptures()) {
            specsByPort.computeIfAbsent(spec.outputPort(),
                    ignored -> new ArrayList<>()).add(spec);
        }
        // The contract's own statement of which ports are produced only by
        // once-only instance-scoped heap writes, read once for the whole
        // closure.  One authority answers this for every owner of the rule:
        // the set is empty for every closure the rule never fired on, and
        // fail-closed on a port whose writer set will not decode.
        SortedSet<String> onceOnlyPorts =
                closure.onceOnlyInstanceScopedPorts();
        for (String port : closure.outputPorts()) {
            List<OutputCaptureSpec> specs = specsByPort.get(port);
            boolean communicationEffect = specs != null
                    && !specs.isEmpty()
                    && specs.stream().allMatch(
                    OutputCaptureSpec::capturesCommunicationEffect);
            if (communicationEffect) {
                // The event is imported separately.
                continue;
            }
            List<JsonObject> admitted = new ArrayList<>();
            if (specs != null) {
                for (OutputCaptureSpec spec : specs) {
                    for (JsonObject value
                            : row.captures(spec.captureBindingId())) {
                        JsonElement expression = value.get("expression");
                        if (expression == null || expression.isJsonNull()) {
                            // A guarded observation of an occurrence that
                            // produced nothing; another occurrence of the
                            // same site may still carry the relation.
                            continue;
                        }
                        if (!exactOutputCaptureOccurrence(spec, value)) {
                            issues.add("OUTPUT_CAPTURE_OCCURRENCE_MISMATCH:"
                                    + port + ":"
                                    + spec.captureBindingId());
                            continue;
                        }
                        admitted.add(value.deepCopy());
                    }
                }
            }
            if (admitted.size() == 1) {
                result.add(port, admitted.get(0).get("expression"));
                continue;
            }
            if (admitted.size() > 1) {
                JsonElement versionSet = siteLocalBoundedVersions(port,
                        exactOutputSiteId(port, specs, issues), admitted,
                        issues);
                if (versionSet != null) result.add(port, versionSet);
                continue;
            }
            // A port published as the activation's own return value has no
            // capture site to bind, so the root observation is the whole
            // relation - and only when this is the one output demanded, since
            // one returned value cannot be several ports.
            boolean rootPublished = (specs == null || specs.isEmpty())
                    && closure.outputPorts().size() == 1;
            JsonElement root = rootOutputExpression(row);
            if (rootPublished && root != null) {
                result.add(port, root);
                continue;
            }
            if (rootPublished) {
                // Nothing was ever counted here, so a capture count names the
                // wrong thing.  Say what the root observation actually was.
                issues.add("OUTPUT_ROOT_VALUE_UNRELATED:" + port + ":"
                        + (row.rootOutput == null ? ""
                        : string(row.rootOutput, "kind")));
                continue;
            }
            // Once-only-root rule (OutputCaptureSpec#INSTANCE_SCOPED_PRODUCER)
            // -- the same question the recorder already answers this way in
            // ConcolicRegionRuntime#completeExactOutputBoundary.  A field
            // belongs to the object, not to the seventh loop iteration: an
            // instance-scoped heap write's recorded version is decided once
            // at instance scope, so an occurrence that never sampled the
            // once-entered write owes no per-occurrence production of this
            // port and is not incomplete because of it.  The importer is the
            // second owner of this completeness check and must not disagree
            // with the recorder; the port simply carries no expression here,
            // which the composer already reads as the once-only rule rather
            // than as a joint-set mismatch.
            if (onceOnlyPorts.contains(port)) continue;
            issues.add("OUTPUT_CAPTURE_COUNT:" + port + ":"
                    + admitted.size());
        }
        return result;
    }

    /** Case-local declared interaction events observed by this execution. */
    private static JsonArray interactionEvents(
            ResultRow row, ExecutionTask task, List<String> issues) {
        JsonArray result = new JsonArray();
        Map<String, OutputCaptureSpec> requested = new LinkedHashMap<>();
        for (OutputCaptureSpec spec : task.outputCaptures()) {
            if (spec.capturesCommunicationEffect()) {
                requested.put(spec.captureBindingId(), spec);
            }
        }
        for (Map.Entry<String, OutputCaptureSpec> entry
                : requested.entrySet()) {
            OutputCaptureSpec spec = entry.getValue();
            boolean observed = false;
            for (JsonObject capture : row.captures(entry.getKey())) {
                if (!"COMMUNICATION_EFFECT".equals(
                        string(capture, "interactionKind"))
                        || !"INSTRUMENTED_INTERACTION_SITE_V1".equals(
                        string(capture, "authority"))
                        || !exactOutputCaptureOccurrence(spec, capture)) {
                    continue;
                }
                JsonObject event = capture.deepCopy();
                event.remove("captureBindingId");
                event.addProperty("portId", spec.outputPort());
                result.add(event);
                observed = true;
            }
            if (!observed) {
                issues.add("INTERACTION_EVENT_MISSING:" + entry.getKey());
            }
        }
        return result;
    }

    /** Exports every bounded occurrence version observed at one output site.
     */
    /** The one static site every capture binding of this port declares.  It
     * is the plan's statement, not the wire's; a result row that restates it
     * is still checked against it. */
    private static String exactOutputSiteId(String port,
                                            List<OutputCaptureSpec> specs,
                                            List<String> issues) {
        String site = "";
        for (OutputCaptureSpec spec : specs == null
                ? Collections.<OutputCaptureSpec>emptyList() : specs) {
            if (site.isEmpty()) {
                site = spec.outputSiteId();
            } else if (!site.equals(spec.outputSiteId())) {
                issues.add("OUTPUT_CAPTURE_VERSION_SITE_MISMATCH:" + port
                        + ":" + site + ":" + spec.outputSiteId());
                return "";
            }
        }
        return site;
    }

    private static JsonElement siteLocalBoundedVersions(
            String port, String site, List<JsonObject> admitted,
            List<String> issues) {
        NavigableMap<Integer, JsonElement> byOrdinal = new TreeMap<>();
        for (JsonObject capture : admitted) {
            int occurrence = integer(capture, "outputVersionOrdinal", -1);
            if (site.isEmpty() || occurrence < 1) {
                // A capture without its site-local ordinal is ambiguous.
                issues.add("OUTPUT_CAPTURE_COUNT:" + port + ":"
                        + admitted.size());
                return null;
            }
            JsonElement expression = capture.get("expression");
            JsonElement prior = byOrdinal.get(occurrence);
            if (prior != null && !prior.equals(expression)) {
                issues.add("OUTPUT_CAPTURE_VERSION_COLLISION:" + port + ":"
                        + occurrence);
                return null;
            }
            if (prior == null) byOrdinal.put(occurrence, expression);
        }
        return byOrdinal.size() == 1 ? byOrdinal.firstEntry().getValue()
                : BoundedOutputVersions.encodeVersionSet(site, byOrdinal);
    }

    /** Admits an observation of the recorded output relation.  The
     * occurrence counts every activation-local execution of the site, nested
     * calls included; it is not itself replay identity. */
    private static boolean exactOutputCaptureOccurrence(
            OutputCaptureSpec request, JsonObject capture) {
        return !request.occurrenceScoped()
                || integer(capture, "outputOccurrence", -1) >= 1;
    }

    /** What the VM observed the activation's root output value to be. */
    private static JsonElement rootOutputExpression(ResultRow row) {
        JsonElement expression = row.rootOutput == null ? null
                : row.rootOutput.get("expression");
        return expression != null && !expression.isJsonNull()
                ? expression.deepCopy() : null;
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
            String id = string(row, "regionId");
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

    /**
     * Names every declared configured-source entry this execution reached
     * and left with no root in its own evidence ledger.
     *
     * <p>A mint that finds a value the VM had already propagated files no
     * {@link SymbolicSourceEvidence} row unless what it found is itself one
     * bare VM root: a propagated compound names roots that live elsewhere,
     * and binding the declared source to it would name a root that does not
     * exist.  Not naming a root is right; saying nothing at all is not.  The
     * site was reached, the mint row was published, and the ledger is silent
     * - which is indistinguishable, one layer down, from a source that was
     * never declared, so a model value the declaration demanded goes missing
     * behind a result that reads complete.  This is the same difference the
     * runtime already decided at {@code
     * ConcolicRegionRuntime#symbolizeConfiguredSourceField}; the importer
     * re-asks it on the published row so the absence is stated instead of
     * inferred.  It is a named coverage gap, never a refusal: the relation
     * this execution did produce is still exactly what it observed.</p>
     */
    private static List<String> unmaterializedConfiguredSourceRoots(
            ResultRow row) {
        Set<String> filed = new LinkedHashSet<>();
        for (JsonObject minted : row.symbolicSourceEvidence) {
            filed.add(configuredSourceEntryKey(
                    string(minted, "sourceId"),
                    string(minted, "fieldSignature"),
                    integer(minted, SymbolicSourceEvidence.ORDINAL, 0)));
        }
        List<String> result = new ArrayList<>();
        Set<String> named = new LinkedHashSet<>();
        for (JsonObject mint : row.symbolizedInputs) {
            String sourceId = string(mint, "sourceId");
            String fieldSignature = string(mint, "fieldSignature");
            int ordinal = integer(mint, SymbolicSourceEvidence.ORDINAL, 0);
            // A mint row that names no configured source is a region input
            // root, which this ledger never claimed to carry.
            if (sourceId.isEmpty() || fieldSignature.isEmpty()) continue;
            if (filed.contains(configuredSourceEntryKey(sourceId,
                    fieldSignature, ordinal))) {
                continue;
            }
            String detail = sourceId + " at "
                    + string(mint, "siteId") + "#" + ordinal + ": "
                    + fieldSignature
                    + " was reached and materialized no symbolic root"
                    + (Boolean.TRUE.equals(exactBoolean(mint,
                    SymbolicSourceEvidence.REUSED))
                    ? "; the value it found already carried a propagated "
                    + "expression that names no VM root of its own"
                    : "");
            if (named.add(detail)) result.add(detail);
        }
        return result;
    }

    /** Identity of one entry of one declared mint site. */
    private static String configuredSourceEntryKey(String sourceId,
                                                   String fieldSignature,
                                                   int ordinal) {
        return sourceId + "\n" + fieldSignature + "\n" + ordinal;
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

    /** Whether this seed publishes the one relation observed at its own
     * boundary rather than a branch-by-branch replay path. */
    private static boolean relationOnlySeed(ExecutionTask task) {
        if (!task.goalKind().capturesOutputRelation()
                || task.replayContract() != null) {
            return false;
        }
        for (JsonElement element : task.inputActions().all()) {
            if (element.isJsonObject()
                    && "EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1".equals(
                    string(element.getAsJsonObject(), "authority"))) {
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
                    string(auxiliary, "kind"))
                    || !AUXILIARY_PATH_CONDITION_AUTHORITY.equals(
                    string(auxiliary, "authority"))
                    || !bool(auxiliary, "active", false)
                    || bool(auxiliary, "aborted", false)) {
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
                indexHolder.add("value", indexElement.deepCopy());
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
                evidence.put(index, condition.deepCopy());
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
                    ? string(condition.getAsJsonObject(), "truncationKind")
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
                    BranchWitness witness = BranchWitness.fromJson(
                            row.getAsJsonObject("witness"));
                    int index = witness.vmPcIndex();
                    if (index < 0) continue;
                    if (evidence.putIfAbsent(index,
                            witness.sourceSatisfiedPredicate().deepCopy())
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
                original.put(index, expression.deepCopy());
                boolean witnessed = branchDecisions.contains(index);
                if (!witnessed
                        && (InitialContainerObservation.isConcreteEquality(
                        expression) || pcPredicate(expression))) {
                    continue;
                }
                summaryIndices.put(index, expressions.size());
                expressions.add(expression.deepCopy());
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
                    if (BranchWitness.fromJson(row.getAsJsonObject(
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
                int index = integer(witness, "vmPcIndex", -1);
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

    private static Map<String, String> parseArgs(String[] args) {
        Map<String, String> result = new LinkedHashMap<>();
        for (int index = 0; index < args.length; index++) {
            String argument = args[index];
            if (!argument.startsWith("--")) {
                throw new IllegalArgumentException(
                        "expected --name value, got " + argument);
            }
            String name = argument.substring(2);
            int equals = name.indexOf('=');
            if (equals >= 0) {
                result.put(name.substring(0, equals),
                        name.substring(equals + 1));
            } else if (index + 1 < args.length) {
                result.put(name, args[++index]);
            } else {
                throw new IllegalArgumentException(
                        "missing value for " + argument);
            }
        }
        return result;
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

        private ImportResult(int rawResultCount, int validSummaryCount,
                             int diagnosticCount) {
            this.rawResultCount = rawResultCount;
            this.validSummaryCount = validSummaryCount;
            this.diagnosticCount = diagnosticCount;
        }
    }
}
