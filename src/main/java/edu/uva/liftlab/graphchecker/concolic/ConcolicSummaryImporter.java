package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.BoundedOutputVersions;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourceSelectorContract;
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
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.exactInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Converts one VM execution row into one semantic path row.
 *
 * <p>The VM expression graph is the authority for scalars, fields and
 * containers.  Import therefore performs one decode and one admission pass;
 * it does not reconstruct Map entries, array elements or dynamic field
 * selectors from concrete runtime snapshots.</p>
 */
public final class ConcolicSummaryImporter {
    private static final String AUXILIARY_PATH_CONDITION_FIELD =
            "auxiliaryPathCondition";
    private static final String SELECTED_BRANCH_AND_AUXILIARY_AUTHORITY =
            "VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1";
    private static final String AUXILIARY_PATH_CONDITION_KIND =
            "CONCOLIC_AUXILIARY_PATH_CONDITION";
    private static final String AUXILIARY_PATH_CONDITION_AUTHORITY =
            "VM_THREAD_AUXILIARY_PATH_CONDITION_V1";
    private static final String CONFIGURED_SOURCE_PHASE_OBSERVATIONS =
            "configuredSourcePhaseObservations";
    private static final String CONFIGURED_SOURCE_PHASE_GAPS =
            "configuredSourcePhaseGaps";
    private static final Set<String> CONFIGURED_SOURCE_PHASE_OBSERVATION_FIELDS =
            Collections.unmodifiableSet(new LinkedHashSet<>(java.util.Arrays
                    .asList("schemaVersion", "kind", "authority",
                            "observationIndex", "phaseKind", "siteId",
                            "replayOrdinal", "sourceId", "fieldSignature",
                            "matchedPhaseId", "ownerCallId", "invocationId",
                            "declaredCallee", "exactMatch", "selectedPhase",
                            "orderMatched")));

    private ConcolicSummaryImporter() {
    }

    public static void main(String[] args) throws Exception {
        Map<String, String> options = parseArgs(args);
        Path results = required(options, "results");
        Path tasks = required(options, "task-plan");
        Path runtimePlan = required(options, "runtime-plan");
        Path output = Paths.get(firstNonBlank(options.get("output"),
                sibling(results,
                        "concolic_region_summaries.jsonl").toString()));
        Path diagnostics = Paths.get(firstNonBlank(
                options.get("diagnostics"),
                sibling(results,
                        "concolic_import_diagnostics.jsonl").toString()));
        Path delta = Paths.get(firstNonBlank(options.get("topology-delta"),
                sibling(output, TopologyDelta.FILE_NAME).toString()));
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

    public static ImportResult importSummaries(
            Path resultsFile, Path taskPlanFile, Path regionFile,
            Path outputFile, Path diagnosticFile, Path deltaFile,
            String iterationId) throws IOException {
        return importSummaries(resultsFile, taskPlanFile,
                regionIds(ArtifactIO.readJsonl(regionFile)), outputFile,
                diagnosticFile, deltaFile, iterationId);
    }

    private static ImportResult importSummaries(
            Path resultsFile, Path taskPlanFile, Set<String> regions,
            Path outputFile, Path diagnosticFile, Path deltaFile,
            String iterationId) throws IOException {
        String immutableIterationId = requireIterationId(iterationId);
        Map<String, ExecutionTask> tasks = taskIndex(
                ArtifactIO.readJsonl(taskPlanFile));
        List<JsonObject> rawResults = ArtifactIO.readJsonl(resultsFile);
        List<JsonObject> summaries = new ArrayList<>();
        List<JsonObject> diagnostics = new ArrayList<>();
        Set<String> hashes = new LinkedHashSet<>();
        // README "Delta ownership is also singular": the frozen-plan
        // comparison happens here, while each raw row is imported, and not as
        // a later pass over a second store.
        TopologyDelta delta = new TopologyDelta(immutableIterationId,
                TopologyDelta.planDigest(tasks.values()));

        for (int index = 0; index < rawResults.size(); index++) {
            JsonObject raw = rawResults.get(index);
            String taskId = string(raw, "taskId");
            if (!"CONCOLIC_REGION_RESULT".equals(string(raw, "event"))) {
                String code = skippedEventCode(raw);
                diagnostics.add(diagnostic(raw, index, code,
                        skippedEventDetail(raw)));
                delta.classify(tasks.get(taskId), raw, index,
                        TopologyDelta.Observation.refused(code));
                continue;
            }
            ExecutionTask task = tasks.get(taskId);
            if (task == null) {
                diagnostics.add(diagnostic(raw, index,
                        "UNKNOWN_EXECUTION_TASK", taskId));
                delta.classify(null, raw, index,
                        TopologyDelta.Observation.unplanned(
                                "UNKNOWN_EXECUTION_TASK"));
                continue;
            }
            if (!regions.contains(task.regionId())) {
                diagnostics.add(diagnostic(raw, index,
                        "UNKNOWN_REGION", task.regionId()));
                delta.classify(task, raw, index,
                        TopologyDelta.Observation.unplanned("UNKNOWN_REGION"));
                continue;
            }
            TopologyDelta.Observation observation =
                    new TopologyDelta.Observation();
            JsonObject summary = importRow(raw, index, task, hashes,
                    diagnostics, observation);
            if (summary != null) {
                // The VM's location rid is a per-session allocation ordinal,
                // so two replays of one occurrence name the same map with
                // different rids and every later index splits it in two.
                // Renaming here - the earliest stage holding both the edges
                // that carry the receiver id and the rows keyed on the rid -
                // is what lets the whole downstream read one name.
                for (String location
                        : SharedStateEvidence.canonicalizeLocations(summary)) {
                    diagnostics.add(diagnostic(raw, index,
                            "LOCATION_NOT_NAMED_ACROSS_SESSIONS", location));
                }
                for (String location : SharedStateEvidence
                        .canonicalizeContainerStateSymbols(summary)) {
                    diagnostics.add(diagnostic(raw, index,
                            "AMBIGUOUS_CONTAINER_STATE_INPUT", location));
                }
                summaries.add(summary);
            }
            delta.classify(task, raw, index, observation);
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

    /**
     * Imports one raw VM result, or refuses it under one named gap.
     *
     * @return the admitted summary, or {@code null} when the row was refused
     */
    private static JsonObject importRow(
            JsonObject raw, int index, ExecutionTask task,
            Set<String> hashes, List<JsonObject> diagnostics,
            TopologyDelta.Observation observation) {
        String taskId = task.taskId();
        // An aborted symbolic execution stops recording branch events and
        // path condition at the point it gave up, and the activation then
        // runs on concretely to whatever exit it reaches.  Every later
        // attestation therefore reads a truncated execution: coverage of
        // the recorded sites, the output boundary, the replay prefix.
        // Charging the truncation to any of them names a gap the run does
        // not have and hides the one it does, so the abort is charged to
        // itself, first, and the summary is refused.
        JsonObject engine = object(raw, "engineSummary");
        if (bool(engine, "aborted", false)) {
            diagnostics.add(diagnostic(raw, index,
                    "SYMBOLIC_EXECUTION_ABORTED",
                    firstNonBlank(string(engine, "abortReason"),
                            "UNSPECIFIED")));
            return refuse(observation, diagnostics);
        }
        String exitKind = string(raw, "exitKind");
        boolean hasCut = raw.has("pathCut")
                || raw.has("replayResourceCut");
        if ("CUT".equals(exitKind)
                || hasCut && !boundedOutputExit(raw, task)) {
            // The two ledgers cut for opposite reasons and are answered by
            // opposite work: an unroll bound says the path space was too
            // wide to walk, a resource cap says a service loop outlasted
            // the replay budget.  The latter may still preserve demanded
            // ports the VM captured before the cut.
            // The runtime publishes each under its own field and lets the
            // resource cap outrank the unroll bound; reading only the
            // unroll field reports the resource cap under the other
            // ledger's name and with an empty body, which is exactly the
            // confusion the two ledgers exist to prevent.
            boolean resourceCut = raw.has("replayResourceCut");
            String cutDetail = object(raw,
                    resourceCut ? "replayResourceCut"
                            : "pathCut").toString();
            if (resourceCut && !hasCapturedDemandedOutput(raw, task)) {
                cutDetail += "; no demanded output relation was "
                        + "captured before cut";
            }
            diagnostics.add(diagnostic(raw, index,
                    resourceCut ? "REPLAY_LOOP_RESOURCE_CAP"
                            : "LOOP_BOUND_PATH_CUT",
                    cutDetail));
            // No admitted bounded prefix exists here.  Keep the cut as an
            // explicit gap rather than inventing an output relation.
            return refuse(observation, diagnostics);
        }
        List<String> issues = new ArrayList<>();
        for (JsonElement unresolved : array(raw,
                "unresolvedInputs")) {
            // A bounded output-version capacity notice is a statement about
            // how much of the run the model covers, not about an input that
            // found no authority.  Charged as an unresolved input it made
            // relationallyComplete false, and one output site exceeding its
            // capacity then discarded the whole producer relation - so the
            // run published nothing instead of publishing a model with a
            // stated limit. It travels as a named bounded-coverage gap
            // instead; the relation remains usable for a satisfying witness,
            // while the Composer's UNSAT-closure authority remains open.
            if (boundedOutputVersionNotice(unresolved)) continue;
            issues.add("UNRESOLVED_INPUT:" + unresolved);
        }

        boolean relationOnlySeed = relationOnlySeed(task);
        // A relation-only seed that carries no decision at all still imports
        // as empty.  What it may no longer do is discard the decisions it
        // does carry: the runtime records a declared site's decision as a
        // concreteObservation when the symbolic gate was closed, and
        // demanding a witness threw those rows away - which is exactly
        // LOOP-1's entersLoop/continue_i attribution.  The two authorities
        // stay distinct either way, because branchMappings() builds a
        // witnessed row only from a `witness` and a concrete row only from a
        // `concreteObservation`, and never promotes one into the other.
        boolean anyBranchDecision =
                SemanticPath.hasAdmissibleBranchDecision(
                        array(raw, "branchMappings"));
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
        }
        if (!bool(engine, "complete", false)) {
            issues.add("VM_SUMMARY_INCOMPLETE:"
                    + string(engine, "abortReason"));
        }
        SemanticPath path = pathConditionOmitted
                ? SemanticPath.fromSelectedEvidence(engine,
                array(raw, "branchMappings"), issues)
                : relationOnlySeed
                ? SemanticPath.atRelationBoundary(
                array(engine, "pathCondition"), task)
                : SemanticPath.from(array(engine, "pathCondition"),
                array(raw, "branchMappings"));
        JsonArray mappings = relationOnlySeed && !anyBranchDecision
                ? new JsonArray()
                : branchMappings(raw, task, path, issues);
        JsonObject targetReach = admittedTargetReach(raw, index, task,
                path.expressions, mappings, diagnostics);
        if (targetReach == null) {
            return refuse(observation, diagnostics);
        }
        String branchReplayMismatch = relationOnlySeed ? ""
                : branchReplayMismatch(raw, task, mappings);
        if (!branchReplayMismatch.isEmpty()
                && (task.replayContract() != null
                || !reachedRequiredTargetOutcome(task, targetReach))) {
            diagnostics.add(diagnostic(raw, index,
                    "BRANCH_REPLAY_MISMATCH", branchReplayMismatch));
            return refuse(observation, diagnostics);
        }
        JsonObject outputs = outputExpressions(raw, task, issues);
        JsonArray interactionEvents = interactionEvents(raw, task, issues);
        PathLoopCounts loopCounts = pathLoopCounts(raw, task);
        if (!loopCounts.refusal.isEmpty()) {
            diagnostics.add(diagnostic(raw, index,
                    LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND,
                    loopCounts.refusal));
            return refuse(observation, diagnostics);
        }
        JsonArray alignmentGaps = alignmentGaps(task, raw);
        JsonObject recordedSharedState =
                recordedSharedState(raw, alignmentGaps);
        List<JsonObject> vmHandoffEvents =
                vmHandoffEvents(raw, alignmentGaps);
        validateConfiguredSourcePhaseObservations(raw, task, issues);
        JsonArray symbolicSources = symbolicSourceEvidence(raw, task,
                issues);
        JsonArray sourceSelectorEvidence = configuredSourceSelectorEvidence(
                raw, task, issues);
        // A replay that carried a selected read cut is validated against
        // its own recorded evidence, never against the reference run's
        // event ids: this is a different session, and its events restart.
        ReplayedReadCut readCut = ReplayedReadCut.validate(
                SelectedReadCut.planOf(task.json()),
                Collections.singletonList(recordedSharedState));
        for (JsonObject gap : readCut.gaps()) alignmentGaps.add(gap);
        JsonArray symbolicInputs = symbolicInputs(raw);
        JsonElement replayContract = task.replayContract();

        JsonObject summary = new JsonObject();
        summary.addProperty("schemaVersion", 1);
        summary.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        summary.addProperty("goalId", task.goalId());
        summary.addProperty("taskId", task.taskId());
        summary.addProperty("sourceKey", task.sourceKey());
        summary.addProperty("regionId", task.regionId());
        summary.addProperty("occurrenceId", task.occurrenceId());
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
        if (sourceSelectorEvidence.size() > 0) {
            summary.add(ConfiguredSourceSelectorContract.EVIDENCE_FIELD,
                    sourceSelectorEvidence);
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
        if (!readCut.isEmpty()) {
            summary.add("readCutRealisation", readCut.toJson());
        }
        boolean boundedExit = "BOUNDED".equals(exitKind);
        summary.addProperty("normalExit", boundedExit
                || "NORMAL".equals(exitKind));
        summary.addProperty("boundedExit", boundedExit);
        summary.addProperty("exceptionType",
                string(raw, "exceptionType"));
        summary.addProperty("relationallyComplete", issues.isEmpty());

        if (replayContract != null && !issues.isEmpty()) {
            diagnostics.add(diagnostic(raw, index,
                    "PATH_REPLAY_ADMISSION_REJECTED",
                    String.join(";", issues)));
            return refuse(observation, diagnostics);
        }

        JsonObject semantic = summary.deepCopy();
        semantic.remove("taskId");
        String hash = sha256(CanonicalJson.render(semantic));
        if (!hashes.add(hash)) {
            diagnostics.add(diagnostic(raw, index,
                    "DUPLICATE_SUMMARY", hash));
            return refuse(observation, diagnostics);
        }
        summary.addProperty("summaryId",
                "SUMMARY." + task.regionId() + "." + hash);
        if (!issues.isEmpty()) {
            diagnostics.add(diagnostic(raw, index,
                    "INCOMPLETE_RELATION",
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

    /**
     * Validates the runtime hook ledger against the task's frozen full
     * catalog and selected subsequence.  Exact catalog landmarks that this
     * task did not select remain admissible audit evidence, but they cannot
     * stand in for a selected publication/consumption or materialize a
     * source.  Any unmatched, duplicated, reordered, missing, or gapped
     * selected phase is a causal-topology refusal.
     */
    private static void validateConfiguredSourcePhaseObservations(
            JsonObject raw, ExecutionTask task, List<String> issues) {
        final List<ConfiguredSourcePhaseContract.Occurrence> catalog;
        final List<String> selected;
        try {
            catalog = ConfiguredSourcePhaseContract.occurrencesOf(
                    task.json().get(ConfiguredSourcePhaseContract.PLAN_FIELD));
            selected = ConfiguredSourcePhaseContract.selectedPhaseIdsOf(
                    task.json(), catalog);
        } catch (IllegalArgumentException malformed) {
            issues.add("SYMBOLIC_SOURCE_PHASE_CATALOG_MALFORMED:"
                    + firstNonBlank(malformed.getMessage(), "UNKNOWN"));
            return;
        }

        boolean observationsArray = raw.has(
                CONFIGURED_SOURCE_PHASE_OBSERVATIONS)
                && raw.get(CONFIGURED_SOURCE_PHASE_OBSERVATIONS).isJsonArray();
        boolean gapsArray = raw.has(CONFIGURED_SOURCE_PHASE_GAPS)
                && raw.get(CONFIGURED_SOURCE_PHASE_GAPS).isJsonArray();
        if (!selected.isEmpty() && (!observationsArray || !gapsArray)) {
            issues.add("SYMBOLIC_SOURCE_PHASE_RUNTIME_LEDGER_MISSING");
            return;
        }
        if (raw.has(CONFIGURED_SOURCE_PHASE_OBSERVATIONS)
                && !observationsArray
                || raw.has(CONFIGURED_SOURCE_PHASE_GAPS) && !gapsArray) {
            issues.add("SYMBOLIC_SOURCE_PHASE_RUNTIME_LEDGER_MALFORMED");
            return;
        }
        if (!gapsArray || !array(raw, CONFIGURED_SOURCE_PHASE_GAPS).isEmpty()) {
            if (gapsArray) {
                for (JsonElement gap : array(raw,
                        CONFIGURED_SOURCE_PHASE_GAPS)) {
                    issues.add("SYMBOLIC_SOURCE_PHASE_RUNTIME_GAP:"
                            + CanonicalJson.render(gap));
                }
            }
            if (!selected.isEmpty() && !gapsArray) {
                // The missing-ledger issue above already states this case.
                return;
            }
        }
        if (!observationsArray) return;

        Map<String, ConfiguredSourcePhaseContract.Occurrence> phasesById =
                new LinkedHashMap<>();
        Map<String, Integer> replayOrdinals = new LinkedHashMap<>();
        Map<String, Integer> nextOrdinal = new LinkedHashMap<>();
        for (ConfiguredSourcePhaseContract.Occurrence phase : catalog) {
            phasesById.put(phase.phaseId(), phase);
            String siteKey = configuredSourcePhaseSiteKey(phase);
            int ordinal = nextOrdinal.getOrDefault(siteKey, 0) + 1;
            nextOrdinal.put(siteKey, ordinal);
            replayOrdinals.put(phase.phaseId(), ordinal);
        }
        Set<String> selectedSet = new LinkedHashSet<>(selected);
        Set<String> exactObserved = new LinkedHashSet<>();
        Set<Long> invocationIds = new LinkedHashSet<>();
        List<String> selectedObserved = new ArrayList<>();
        int expectedIndex = 1;
        for (JsonElement element : array(raw,
                CONFIGURED_SOURCE_PHASE_OBSERVATIONS)) {
            if (!element.isJsonObject()) {
                issues.add("SYMBOLIC_SOURCE_PHASE_OBSERVATION_MALFORMED:"
                        + expectedIndex++);
                continue;
            }
            JsonObject observation = element.getAsJsonObject();
            int index = exactInteger(observation, "observationIndex", -1);
            boolean exactSchema =
                    CONFIGURED_SOURCE_PHASE_OBSERVATION_FIELDS.equals(
                            observation.keySet())
                    && exactInteger(observation, "schemaVersion", -1) == 1
                    && "CONFIGURED_SOURCE_PHASE_OBSERVATION".equals(
                    string(observation, "kind"))
                    && "EXACT_ACTIVE_CALL_SITE_REPLAY_V1".equals(
                    string(observation, "authority"))
                    && index == expectedIndex
                    && exactBoolean(observation, "exactMatch") != null
                    && exactBoolean(observation, "selectedPhase") != null
                    && exactBoolean(observation, "orderMatched") != null;
            expectedIndex++;
            if (!exactSchema) {
                issues.add("SYMBOLIC_SOURCE_PHASE_OBSERVATION_MALFORMED:"
                        + index);
                continue;
            }
            boolean exact = exactBoolean(observation, "exactMatch");
            String phaseId = string(observation, "matchedPhaseId");
            if (!exact) {
                issues.add("SYMBOLIC_SOURCE_PHASE_OBSERVATION_UNMATCHED:"
                        + phaseId + ":" + string(observation, "sourceId"));
                continue;
            }
            ConfiguredSourcePhaseContract.Occurrence phase =
                    phasesById.get(phaseId);
            boolean shouldSelect = selectedSet.contains(phaseId);
            long invocationId = positiveExactLong(observation,
                    "invocationId");
            if (phase == null
                    || !exactObserved.add(phaseId)
                    || !phase.phase().name().equals(
                    string(observation, "phaseKind"))
                    || !phase.siteId().equals(string(observation, "siteId"))
                    || replayOrdinals.get(phaseId) == null
                    || replayOrdinals.get(phaseId) != exactInteger(
                    observation, "replayOrdinal", -1)
                    || !phase.sourceId().equals(
                    string(observation, "sourceId"))
                    || !phase.fieldSignature().equals(
                    string(observation, "fieldSignature"))
                    || !phase.runtimeDeclaredCallee().equals(
                    string(observation, "declaredCallee"))
                    || positiveExactLong(observation, "ownerCallId") <= 0L
                    || invocationId <= 0L
                    || !invocationIds.add(invocationId)
                    || exactBoolean(observation, "selectedPhase")
                    != shouldSelect
                    || !exactBoolean(observation, "orderMatched")) {
                issues.add("SYMBOLIC_SOURCE_PHASE_OBSERVATION_MISMATCH:"
                        + phaseId);
                continue;
            }
            if (shouldSelect) selectedObserved.add(phaseId);
        }
        if (!selected.equals(selectedObserved)) {
            issues.add("SYMBOLIC_SOURCE_PHASE_SELECTED_SEQUENCE_MISMATCH:"
                    + selected + ":" + selectedObserved);
        }
    }

    private static String configuredSourcePhaseSiteKey(
            ConfiguredSourcePhaseContract.Occurrence phase) {
        return phase.phase().name() + "\n" + phase.sourceId() + "\n"
                + phase.siteId();
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

    /**
     * Decodes the aggregate runtime counters as one replay path's loop-count
     * vector.  The vector is case evidence: it never creates iteration-local
     * states or ports.  An absent counter for a retained while is zero when
     * none of that loop's declared control sites executed; evidence that did
     * execute but cannot be joined to the runtime loop id is named as a
     * coverage gap.  Only a count beyond the declared K_L refuses the row.
     */
    private static PathLoopCounts pathLoopCounts(
            JsonObject raw, ExecutionTask task) {
        PathLoopCounts result = new PathLoopCounts();
        JsonObject fixedBodies = object(raw, "replayLoopBodies");
        JsonObject conditionBodies = object(raw,
                "loopBackedgeTraversals");
        Set<String> decidedSites = new LinkedHashSet<>();
        for (JsonElement element : array(raw, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            String site = string(element.getAsJsonObject(), "siteId");
            if (!site.isEmpty()) decidedSites.add(site);
        }
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
                row.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND_AUTHORITY,
                        task.loopBound().declaredBounds().containsKey(loopSiteId)
                                ? LoopBoundPolicy.BOUND_FROM_DECLARATION
                                : LoopBoundPolicy.BOUND_FROM_POLICY);
            }
            row.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, runtimeLoopId);
            row.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, bodyCount);
            boolean loopReached = controlObserved || bodyCount > 0;
            row.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, loopReached);
            row.addProperty("countAuthority",
                    LoopBoundPolicy.PATH_BODY_COUNT_AUTHORITY);
            if (LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(
                    classification)) {
                JsonArray cardinalities = exactCardinalities(
                        raw, runtimeLoopId, loopSiteId, result);
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
            JsonObject raw, String runtimeLoopId, String loopSiteId,
            PathLoopCounts result) {
        JsonArray exact = new JsonArray();
        Map<Integer, Integer> byOccurrence = new LinkedHashMap<>();
        for (JsonElement element : array(raw,
                LoopBoundPolicy.LOOP_CARDINALITIES)) {
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
        for (JsonElement element : array(raw,
                LoopBoundPolicy.LOOP_CARDINALITY_GAPS)) {
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

    /**
     * Refuses the row the caller just filed one diagnostic for, and carries
     * that diagnostic's own code into the delta as the named gap.  Every
     * refusal path files exactly one diagnostic immediately before returning
     * here, so a dropped row can never leave the delta silent.
     */
    private static JsonObject refuse(TopologyDelta.Observation observation,
                                     List<JsonObject> diagnostics) {
        observation.gap = string(
                diagnostics.get(diagnostics.size() - 1), "code");
        return null;
    }

    /**
     * Joins the planned output-version gaps with the handoff gaps this
     * execution recorded.  A failed symbolic expression handoff is a coverage
     * fact of the run, not of the plan, so it enters the summary from the VM
     * result row; keeping it in the same stream means the worklist and the
     * composer see it exactly the way they already see a loop, read-from or
     * output-version misalignment.
     */
    /**
     * The runtime's text for one bounded output-version capacity notice.
     *
     * <p>Matching on the message is the only channel the notice has today; a
     * structured row would be better and belongs with the hook that raises
     * it in {@code runtime/}.  The prefix is matched rather than the whole
     * sentence so that the site and the number stay readable from it.</p>
     */
    private static final String BOUNDED_OUTPUT_VERSION_NOTICE =
            ": bounded output version capacity ";

    /** The notice's trailing clause, stripped to recover the site id. */
    private static final String BOUNDED_OUTPUT_VERSION_TAIL =
            "; later occurrences are counted, not captured";

    /** Kind the coverage filter already admits for this class of gap. */
    private static final String BOUNDED_OUTPUT_VERSION_GAP_KIND =
            "OUTPUT_VERSION_ALIGNMENT_GAP";

    private static boolean boundedOutputVersionNotice(JsonElement notice) {
        return notice != null && notice.isJsonPrimitive()
                && notice.getAsString().contains(
                        BOUNDED_OUTPUT_VERSION_NOTICE);
    }

    /**
     * One named bounded-coverage gap per output site that ran past its
     * bounded version capacity.
     *
     * <p>README's resource rule: truncation of selected evidence is a named
     * gap and is never read as the evidence being absent.  The gap states
     * the site and the capacity so the next reader can size the real bound
     * instead of rediscovering it.  It also states how many versions were
     * captured, and says outright that the number actually observed is not
     * carried on the result - the runtime counts it but its notice does not
     * publish it, and inventing the figure here would be worse than naming
     * its absence.</p>
     */
    private static List<JsonObject> boundedOutputVersionGaps(JsonObject raw) {
        List<JsonObject> gaps = new ArrayList<>();
        for (JsonElement notice : array(raw, "unresolvedInputs")) {
            if (!boundedOutputVersionNotice(notice)) continue;
            String text = notice.getAsString();
            int mark = text.indexOf(BOUNDED_OUTPUT_VERSION_NOTICE);
            String binding = text.substring(0, mark);
            String tail = text.substring(
                    mark + BOUNDED_OUTPUT_VERSION_NOTICE.length());
            String capacity = tail.split(" ", 2)[0];
            int at = tail.indexOf(" reached at ");
            String site = at < 0 ? "" : tail.substring(
                    at + " reached at ".length());
            // Anchored on the notice's own trailing clause, not on the
            // first "; ": a site id embeds Java descriptors and one of those
            // may legitimately contain a semicolon.
            int clause = site.lastIndexOf(BOUNDED_OUTPUT_VERSION_TAIL);
            if (clause >= 0) site = site.substring(0, clause);
            int captured = 0;
            for (JsonElement element : array(raw, "outputCaptures")) {
                if (element.isJsonObject() && binding.equals(string(
                        element.getAsJsonObject(), "captureBindingId"))) {
                    captured++;
                }
            }
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", BOUNDED_OUTPUT_VERSION_GAP_KIND);
            gap.addProperty("schemaVersion", 1);
            gap.addProperty("authority",
                    "BOUNDED_OUTPUT_VERSION_CAPACITY_V1");
            gap.addProperty("captureBindingId", binding);
            gap.addProperty("outputSiteId", site);
            gap.addProperty("versionCapacity", capacity);
            gap.addProperty("versionsCaptured", captured);
            gap.addProperty("versionsObserved", "NOT_CARRIED_BY_RESULT");
            gap.addProperty("reason", binding + " ran past its bounded"
                    + " output version capacity " + capacity + " at " + site
                    + "; " + captured + " version(s) were captured and the"
                    + " model covers only those, so this relation is a"
                    + " bounded prefix of the run and not a closed one");
            gaps.add(gap);
        }
        return gaps;
    }

    private static JsonArray alignmentGaps(ExecutionTask task,
                                           JsonObject raw) {
        JsonArray result = new JsonArray();
        for (JsonObject gap : boundedOutputVersionGaps(raw)) {
            result.add(gap);
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
        for (JsonElement gap : array(raw, "rpcHandoffGaps")) {
            if (gap.isJsonObject()
                    && RpcExpressionHandoff.isGap(gap.getAsJsonObject())) {
                result.add(gap.deepCopy());
            }
        }
        for (JsonElement gap : array(raw, "sharedStateGaps")) {
            if (gap.isJsonObject()
                    && SharedStateEvidence.isGap(gap.getAsJsonObject())) {
                result.add(gap.deepCopy());
            }
        }
        for (JsonElement gap : array(raw, "readCutGaps")) {
            if (gap.isJsonObject() && SparseReadCutGate.GAP_KIND.equals(
                    string(gap.getAsJsonObject(), "kind"))) {
                result.add(gap.deepCopy());
            }
        }
        return result;
    }

    /**
     * Applies this execution's recorded read-from evidence to the candidate
     * writers the trace retained.
     *
     * <p>This is campaign completion for one execution, and it is where the
     * two halves of the design finally meet. Trace refinement ran before any
     * symbolic session existed, so it could only state which writers the run
     * made possible; the session then observed which one the read took, or
     * that it could not tell. Resolving here rather than at refinement is what
     * keeps the reader's own relation reusable: a second run with a different
     * legal writer changes this binding and nothing else about the summary.
     * </p>
     *
     * <p>The store is session-wide, so a reader's own read-out holds the
     * writes its siblings published; a task therefore resolves its own edges
     * without needing another task's summary. Whatever this execution did not
     * record stays a candidate under its existing gap, and the composer
     * reports it there.</p>
     */
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

    /**
     * Ingests the VM handoff references this execution recorded.
     *
     * <p>A successful attach means the receiver holds the sender's own
     * expression; the session ledger relates the two events once, as
     * {@code VALUE_HANDOFF}.  What enters the summary is only the reference
     * into that ledger - the declared port, VM export event, and exact
     * producer execution carried beside the handle - and it enters through
     * the same admission the runtime applied. A malformed or incomplete row
     * is dropped and named, never repaired.</p>
     */
    private static List<JsonObject> vmHandoffEvents(JsonObject raw,
                                                    JsonArray gaps) {
        List<JsonObject> events = new ArrayList<>();
        for (JsonElement element : array(raw, VmHandoffEvidence.FIELD)) {
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

    /** Admits only the exact source declarations frozen into this task. */
    private static JsonArray symbolicSourceEvidence(
            JsonObject raw, ExecutionTask task, List<String> issues) {
        Map<String, JsonObject> expectedDeclarations =
                new LinkedHashMap<>();
        for (JsonElement element : array(task.json(),
                SymbolicSourceEvidence.TASK_FIELD)) {
            if (!element.isJsonObject()) {
                issues.add("SYMBOLIC_SOURCE_DECLARATION_MALFORMED");
                continue;
            }
            JsonObject declaration = element.getAsJsonObject();
            String id = string(declaration, "sourceId");
            String phaseId = string(declaration, "sourcePhaseId");
            String sourceOccurrenceId = string(declaration,
                    "sourceOccurrenceId");
            String phaseSiteId = string(declaration,
                    "sourcePhaseSiteId");
            int phaseOrdinal = exactInteger(declaration,
                    "sourcePhaseOrdinal", -1);
            String sourceRole = string(declaration, "sourceRole");
            String field = string(declaration, "fieldSignature");
            Set<String> outputs = new LinkedHashSet<>();
            String output = string(declaration,
                    "requiredOutputFieldSignature");
            if (!output.isEmpty()) outputs.add(output);
            for (JsonElement encoded : array(declaration,
                    "requiredOutputFieldSignatures")) {
                if (!encoded.isJsonPrimitive()
                        || encoded.getAsString().trim().isEmpty()
                        || !outputs.add(encoded.getAsString())) {
                    issues.add("SYMBOLIC_SOURCE_DECLARATION_MALFORMED:"
                            + id);
                }
            }
            Set<String> targetInputs = new LinkedHashSet<>();
            String targetInput = string(declaration,
                    "requiredTargetInputPort");
            if (!targetInput.isEmpty()) targetInputs.add(targetInput);
            for (JsonElement encoded : array(declaration,
                    "requiredTargetInputPorts")) {
                if (!encoded.isJsonPrimitive()
                        || encoded.getAsString().trim().isEmpty()
                        || !targetInputs.add(encoded.getAsString())) {
                    issues.add("SYMBOLIC_SOURCE_DECLARATION_MALFORMED:"
                            + id);
                }
            }
            if (!SymbolicSourceEvidence.DECLARATION_AUTHORITY.equals(
                    string(declaration, "authority"))
                    || id.isEmpty() || phaseId.isEmpty() || field.isEmpty()
                    || !task.occurrenceId().equals(sourceOccurrenceId)
                    || phaseSiteId.isEmpty() || phaseOrdinal <= 0
                    || !outputs.isEmpty()
                    && !"OUTPUT_RELATION".equals(sourceRole)
                    || !targetInputs.isEmpty()
                    && !"TARGET_REACH".equals(sourceRole)
                    || outputs.isEmpty() == targetInputs.isEmpty()
                    || (!output.isEmpty()
                    && declaration.has("requiredOutputFieldSignatures"))
                    || (!targetInput.isEmpty()
                    && declaration.has("requiredTargetInputPorts"))
                    || expectedDeclarations.putIfAbsent(
                    phaseId, declaration) != null) {
                issues.add("SYMBOLIC_SOURCE_DECLARATION_MALFORMED:"
                        + phaseId + ":" + id);
            }
        }
        Map<String, ConfiguredSourcePhaseContract.Occurrence>
                expectedPhases = new LinkedHashMap<>();
        final List<ConfiguredSourcePhaseContract.Occurrence> taskPhases;
        final Set<String> selectedPhaseIds;
        try {
            taskPhases = ConfiguredSourcePhaseContract.occurrencesOf(
                    task.json().get(ConfiguredSourcePhaseContract.PLAN_FIELD));
            selectedPhaseIds = new LinkedHashSet<>(
                    ConfiguredSourcePhaseContract.selectedPhaseIdsOf(
                            task.json(), taskPhases));
        } catch (IllegalArgumentException malformed) {
            issues.add("SYMBOLIC_SOURCE_PHASE_CATALOG_MALFORMED:"
                    + firstNonBlank(malformed.getMessage(), "UNKNOWN"));
            return new JsonArray();
        }
        Map<String, ConfiguredSourcePhaseContract.Occurrence> phasesById =
                new LinkedHashMap<>();
        for (ConfiguredSourcePhaseContract.Occurrence phase : taskPhases) {
            if (phasesById.putIfAbsent(phase.phaseId(), phase) != null) {
                issues.add("SYMBOLIC_SOURCE_PHASE_CATALOG_MALFORMED:"
                        + phase.phaseId());
            }
        }
        for (Map.Entry<String, JsonObject> selected
                : expectedDeclarations.entrySet()) {
            JsonObject declaration = selected.getValue();
            String id = string(declaration, "sourceId");
            String phaseId = string(declaration, "sourcePhaseId");
            ConfiguredSourcePhaseContract.Occurrence phase =
                    phasesById.get(phaseId);
            if (phase == null
                    || phase.phase()
                    != ConfiguredSourcePhaseContract.Phase.PUBLISH
                    || !selectedPhaseIds.contains(phaseId)
                    || !task.occurrenceId().equals(
                    phase.sourceOccurrenceId())
                    || !id.equals(phase.sourceId())
                    || !string(declaration, "fieldSignature").equals(
                    phase.fieldSignature())
                    || !string(declaration, "sourcePhaseSiteId").equals(
                    phase.siteId())
                    || exactInteger(declaration, "sourcePhaseOrdinal", -1)
                    != phase.baselineOrdinal()) {
                issues.add("SYMBOLIC_SOURCE_PHASE_MISSING:"
                        + phaseId + ":" + id);
                continue;
            }
            if (expectedPhases.putIfAbsent(phase.phaseId(), phase) != null) {
                issues.add("SYMBOLIC_SOURCE_PHASE_CATALOG_MALFORMED:"
                        + phase.phaseId());
            }
        }
        JsonArray admitted = new JsonArray();
        Set<String> observed = new LinkedHashSet<>();
        final List<JsonObject> events;
        try {
            events = SymbolicSourceEvidence.eventsOf(raw);
        } catch (IllegalArgumentException malformed) {
            issues.add("SYMBOLIC_SOURCE_EVIDENCE_MALFORMED:"
                    + malformed.getMessage());
            return admitted;
        }
        for (JsonObject event : events) {
            String phaseId = string(event, "sourcePhaseId");
            String id = string(event, "sourceId");
            String field = string(event, "fieldSignature");
            ConfiguredSourcePhaseContract.Occurrence phase =
                    expectedPhases.get(phaseId);
            if (phase == null
                    || !task.occurrenceId().equals(string(event,
                    "sourceOccurrenceId"))
                    || !id.equals(phase.sourceId())
                    || !field.equals(phase.fieldSignature())
                    || !observed.add(phaseId)) {
                issues.add("SYMBOLIC_SOURCE_EVIDENCE_NOT_DECLARED:"
                        + phaseId + ":" + id);
                continue;
            }
            admitted.add(event.deepCopy());
        }
        for (Map.Entry<String, ConfiguredSourcePhaseContract.Occurrence>
                expectedPhase : expectedPhases.entrySet()) {
            if (!observed.contains(expectedPhase.getKey())) {
                issues.add("SYMBOLIC_SOURCE_EVIDENCE_MISSING:"
                        + expectedPhase.getValue().phaseId() + ":"
                        + expectedPhase.getValue().sourceId());
            }
        }
        return admitted;
    }

    /** Admits one exact session source value for each declared selector. */
    private static JsonArray configuredSourceSelectorEvidence(
            JsonObject raw, ExecutionTask task, List<String> issues) {
        JsonArray admitted = new JsonArray();
        final List<ConfiguredSourceSelectorContract.Selector> selectors;
        final List<JsonObject> evidence;
        try {
            selectors = ConfiguredSourceSelectorContract.decode(task.json());
            evidence = ConfiguredSourceSelectorContract.evidenceOf(raw);
        } catch (IllegalArgumentException malformed) {
            issues.add("CONFIGURED_SOURCE_SELECTOR_EVIDENCE_MALFORMED:"
                    + firstNonBlank(malformed.getMessage(), "UNKNOWN"));
            return admitted;
        }
        Map<String, ConfiguredSourceSelectorContract.Selector> expected =
                new LinkedHashMap<>();
        for (ConfiguredSourceSelectorContract.Selector selector : selectors) {
            expected.put(selector.consumePhaseId(), selector);
        }
        Map<String, ConfiguredSourcePhaseContract.Occurrence> consumePhases =
                new LinkedHashMap<>();
        Set<String> selectedPhaseIds = new LinkedHashSet<>();
        try {
            List<ConfiguredSourcePhaseContract.Occurrence> taskPhases =
                    ConfiguredSourcePhaseContract.occurrencesOf(
                    task.json().get(ConfiguredSourcePhaseContract
                            .PLAN_FIELD));
            selectedPhaseIds.addAll(
                    ConfiguredSourcePhaseContract.selectedPhaseIdsOf(
                            task.json(), taskPhases));
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : taskPhases) {
                if (phase.phase()
                        != ConfiguredSourcePhaseContract.Phase.CONSUME) {
                    continue;
                }
                if (consumePhases.putIfAbsent(phase.phaseId(), phase)
                        != null) {
                    issues.add("CONFIGURED_SOURCE_CONSUME_PHASE_DUPLICATE:"
                            + phase.phaseId());
                }
            }
        } catch (IllegalArgumentException malformed) {
            issues.add("CONFIGURED_SOURCE_PHASE_CATALOG_MALFORMED:"
                    + firstNonBlank(malformed.getMessage(), "UNKNOWN"));
            return admitted;
        }
        for (ConfiguredSourceSelectorContract.Selector selector : selectors) {
            ConfiguredSourcePhaseContract.Occurrence phase =
                    consumePhases.get(selector.consumePhaseId());
            if (phase == null
                    || !selectedPhaseIds.contains(
                    selector.consumePhaseId())
                    || !task.occurrenceId().equals(
                    phase.sourceOccurrenceId())
                    || !selector.sourceId().equals(phase.sourceId())) {
                issues.add("CONFIGURED_SOURCE_CONSUME_PHASE_MISMATCH:"
                        + selector.consumePhaseId());
            }
        }
        Set<String> observed = new LinkedHashSet<>();
        for (JsonObject row : evidence) {
            String sourceId = string(row, "sourceId");
            String consumePhaseId = string(row, "consumePhaseId");
            ConfiguredSourceSelectorContract.Selector selector =
                    expected.get(consumePhaseId);
            if (selector == null || !selector.matches(row)
                    || !observed.add(consumePhaseId)) {
                issues.add("CONFIGURED_SOURCE_SELECTOR_EVIDENCE_NOT_DECLARED:"
                        + consumePhaseId + ":" + sourceId);
                continue;
            }
            admitted.add(row.deepCopy());
        }
        for (Map.Entry<String, ConfiguredSourceSelectorContract.Selector>
                selected : expected.entrySet()) {
            if (!observed.contains(selected.getKey())) {
                issues.add("CONFIGURED_SOURCE_SELECTOR_EVIDENCE_MISSING:"
                        + selected.getKey() + ":"
                        + selected.getValue().sourceId());
            }
        }
        return admitted;
    }

    /**
     * Ingests the shared-state evidence this execution recorded.
     *
     * <p>The version store and the event ledger are the runtime's answer to
     * "which write did this read take" and "what is ordered against what".
     * They enter the summary only after passing the same admission the
     * runtime applied, because a record that cannot prove its own claim is
     * worse than no record: a consumer would read a writer set as complete,
     * or an order domain as acyclic, on the strength of a field that was
     * never checked.  A row that fails admission here is dropped and named,
     * never repaired.</p>
     */
    private static JsonObject recordedSharedState(JsonObject raw,
                                                  JsonArray gaps) {
        List<JsonObject> versions = new ArrayList<>();
        for (JsonElement element : array(raw, "sharedFieldVersions")) {
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
        JsonObject ledger = object(raw, "sessionEventLedger");
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

    /**
     * Admits a VM row only when it belongs to the canonical bounded path that
     * selected the task.  Cross-run call ids and object identities are not
     * replay addresses: the contract consists solely of static branch sites,
     * activation-local occurrences and outcomes.
     *
     * <p>A seed execution must reproduce the complete branch event set encoded
     * by {@code task.branches}.  A flip execution must reproduce its ordered
     * replay prefix and the requested opposite source outcome; only behavior
     * after that source event may form a newly discovered path.</p>
     */
    private static String branchReplayMismatch(
            JsonObject raw, ExecutionTask task, JsonArray mappings) {
        JsonElement encodedReplay = task.replayContract();
        BranchEventCatalog seed = taskSeedEvents(task.branches());
        if (!seed.issue.isEmpty()) {
            return seed.issue;
        }
        BranchEventCatalog observed = observedBranchEvents(mappings);
        if (!observed.issue.isEmpty()) {
            return observed.issue;
        }
        if (encodedReplay == null) {
            return exactSeedMismatch(task.goalId(), seed.events,
                    observed.events, concreteBranchOutcomes(raw),
                    boundedPrefixExit(string(raw, "exitKind")));
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

    private static BranchEventCatalog taskSeedEvents(JsonArray branches) {
        BranchEventCatalog result = new BranchEventCatalog();
        int branchIndex = 0;
        for (JsonElement element : branches) {
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
            JsonArray mappings) {
        BranchEventCatalog result = new BranchEventCatalog();
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

    /**
     * Attests a seed replay against the recorded branch witnesses.
     *
     * <p>Recording and replay are two executions of the same concurrent
     * workload, so a site repeats as many times as the surrounding
     * environment happens to be wide: a loop over a shared container runs
     * once per element that execution holds.  The demanded slice constrains
     * which way a branch goes, never how many times an environment-sized
     * loop revisits it, so pinning the recorded occurrence ordinals rejects
     * a faithful replay for a fact the failure never depended on.</p>
     *
     * <p>The contract is therefore stated per static site: every outcome the
     * recording witnessed at a site must also be witnessed there by the
     * replay, and the replay may not decide a site the task never planned.
     * A site the replay drives only the other way is a real witness conflict
     * and still fails closed.</p>
     *
     * <p>Coverage is attested by execution, not by solvability.  A branch the
     * replay decided before its symbolic gate opened produces no VM event and
     * therefore no mapping, yet it demonstrably ran; those concrete witnesses
     * satisfy coverage while never entering the path condition.  They cannot
     * make a site unexpected either: a concrete prefix decides branches the
     * demanded slice never planned, and that is ordinary execution.</p>
     *
     * <p>An activation that deliberately stops early — at its reach target,
     * at its output boundary, or at a loop bound — never executes the tail of
     * the recorded region at all.  Demanding coverage of sites the task chose
     * not to reach would reject every bounded summary, so an early stop keeps
     * only the contradiction rules.</p>
     */
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

    /**
     * The one exit kind where the activation stopped before its own terminal.
     *
     * <p>A bounded cut is the declared bound running out, so the region tail
     * it never ran is that bound and not a coverage finding.  Reaching the
     * target is not such an exit: the occurrence records the reach and keeps
     * running to its terminal, so its unreached sites remain findings.</p>
     */
    static boolean boundedPrefixExit(String exitKind) {
        return "BOUNDED".equals(exitKind);
    }

    /**
     * Indexes the branches an activation executed before its symbolic gate
     * opened.  These rows carry no path condition and no occurrence ordinal,
     * so they can only ever answer "was this site reached, and which way".
     */
    public static Map<String, Set<Boolean>> concreteBranchOutcomes(
            JsonObject raw) {
        Map<String, Set<Boolean>> outcomes = new LinkedHashMap<>();
        for (JsonElement element : array(raw, "concreteBranchWitnesses")) {
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
            // to other tasks as well. They are evidence for later refinement,
            // not members of this task's replay contract. Only an expected
            // event occurring early, missing, or with the wrong outcome can
            // contradict this ordered prefix.
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

    /**
     * Admits the runtime's exact target event against both authorities fixed
     * before composition: the task-selected branch identity and the
     * witnessed branch mapping imported from this execution.  A selected
     * target task with no such event is not a partial target path.
     */
    private static JsonObject admittedTargetReach(
            JsonObject raw, int index, ExecutionTask task,
            JsonArray pathCondition, JsonArray mappings,
            List<JsonObject> diagnostics) {
        if (!task.goalKind().capturesTargetReach()) {
            return new JsonObject();
        }
        JsonElement encoded = raw.get(PathObservation.TargetReachEvent.FIELD);
        if (encoded == null) {
            diagnostics.add(diagnostic(raw, index,
                    "TARGET_REACH_EVENT_MISSING",
                    "selected target execution published no targetReach"));
            return null;
        }
        final PathObservation.TargetReachEvent event;
        try {
            event = PathObservation.TargetReachEvent.decode(encoded);
        } catch (IllegalArgumentException malformed) {
            diagnostics.add(diagnostic(raw, index,
                    "TARGET_REACH_EVENT_MALFORMED",
                    firstNonBlank(malformed.getMessage(), "UNKNOWN")));
            return null;
        }

        JsonObject selected = object(task.json(), "targetBranch");
        String selectedSite = string(selected, "siteId");
        int selectedOccurrence = JsonFields.exactInteger(selected,
                "occurrence", -1);
        if (!event.siteId().equals(selectedSite)
                || event.occurrence() != selectedOccurrence) {
            diagnostics.add(diagnostic(raw, index,
                    "TARGET_REACH_EVENT_MISMATCH",
                    "event " + event.siteId() + "#" + event.occurrence()
                            + " does not match selected target "
                            + firstNonBlank(selectedSite, "<missing>") + "#"
                            + selectedOccurrence));
            return null;
        }

        JsonObject canonical = new JsonObject();
        canonical.add("pathCondition", pathCondition.deepCopy());
        canonical.add("branchMappings", mappings.deepCopy());
        int exactWitnesses = 0;
        try {
            for (SummaryBranchMapping mapping
                    : SummaryBranchMapping.fromSummary(canonical)) {
                if (mapping.isWitnessed()
                        && event.matches(mapping.siteId(),
                        mapping.occurrence(),
                        mapping.sourceTakenOutcome())) {
                    exactWitnesses++;
                }
            }
        } catch (IllegalArgumentException malformed) {
            diagnostics.add(diagnostic(raw, index,
                    "TARGET_REACH_EVENT_MISMATCH",
                    "target branch evidence is malformed: "
                            + firstNonBlank(malformed.getMessage(),
                            "UNKNOWN")));
            return null;
        }
        if (exactWitnesses != 1) {
            diagnostics.add(diagnostic(raw, index,
                    "TARGET_REACH_EVENT_MISMATCH",
                    "event has " + exactWitnesses
                            + " exact witnessed branch mapping(s)"));
            return null;
        }
        return event.toJson();
    }

    /**
     * An exact runtime witness of the planner-required target outcome is
     * stronger than the seed path contract. Upstream producer replay is
     * specifically allowed to change that seed outcome; otherwise the
     * failure-producing receiver row would be discarded as a replay mismatch.
     * The exemption is limited to the selected target site, occurrence and
     * unique planner-authored required outcome. Other mismatches remain
     * fail-closed.
     */
    private static boolean reachedRequiredTargetOutcome(
            ExecutionTask task, JsonObject targetReach) {
        if (!task.goalKind().capturesTargetReach()
                || targetReach == null || targetReach.size() == 0) {
            return false;
        }
        JsonObject selected = object(task.json(), "targetBranch");
        String targetSite = string(selected, "siteId");
        int targetOccurrence = JsonFields.exactInteger(selected,
                "occurrence", -1);
        if (targetSite.isEmpty() || targetOccurrence < 1
                || !targetSite.equals(string(targetReach, "siteId"))
                || targetOccurrence != JsonFields.exactInteger(
                targetReach, "occurrence", -1)) {
            return false;
        }

        Boolean required = null;
        for (JsonElement element : task.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (!targetSite.equals(string(branch, "siteId"))
                    || targetOccurrence != JsonFields.exactInteger(
                    branch, "selectedOccurrence", -1)) {
                continue;
            }
            Boolean candidate = exactBoolean(branch, "requiredOutcome");
            if (candidate == null
                    || required != null && required != candidate) {
                return false;
            }
            required = candidate;
        }
        Boolean witnessed = exactBoolean(targetReach, "outcome");
        return required != null && required.equals(witnessed);
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

    private static boolean boundedOutputExit(JsonObject raw,
                                             ExecutionTask task) {
        if (!task.goalKind().capturesOutputRelation()
                || !"BOUNDED".equals(string(raw, "exitKind"))) {
            return false;
        }
        if (raw.has("replayResourceCut")) {
            JsonObject cut = object(raw, "replayResourceCut");
            int maxBodies = integer(cut, "maxLoopBodies", -1);
            long attemptedBody = longInteger(cut, "attemptedBody", -1L);
            return "REPLAY_LOOP_RESOURCE_CAP".equals(string(cut, "kind"))
                    && "REPLAY_LOOP_RESOURCE_CAP".equals(
                    string(cut, "reason"))
                    && !string(cut, "loopId").isEmpty()
                    && maxBodies > 0
                    && attemptedBody > maxBodies
                    && hasCapturedDemandedOutput(raw, task);
        }
        JsonObject cut = object(raw, "pathCut");
        String loopId = string(cut, "backedgeId");
        return "LOOP_BOUND".equals(string(cut, "kind"))
                && "MAX_LOOP_BODY_ITERATIONS_REACHED".equals(
                string(cut, "reason"))
                && !loopId.isEmpty()
                && task.loopBound().acceptsInstrumentedBound(loopId,
                integer(cut, "maxBackedgeTraversals", -1))
                && hasCapturedDemandedOutput(raw, task);
    }

    /** Admits only a complete, exact producer prefix as a normal relation. */
    /**
     * Resource-bounded output is admitted per port.  One real VM capture is
     * enough to preserve that port from this path; missing demanded ports are
     * still reported by {@link #outputExpressions} and keep the summary
     * relationally incomplete.
     */
    private static boolean hasCapturedDemandedOutput(
            JsonObject raw, ExecutionTask task) {
        if (!task.goalKind().capturesOutputRelation()
                || task.outputCaptures().isEmpty()) {
            return false;
        }
        JsonArray captures = array(raw, "outputCaptures");
        for (OutputCaptureSpec request : task.outputCaptures()) {
            if (!(request.capturesCallArgument()
                    || request.capturesCommunicationEffect()
                    || request.capturesHandoffBoundLeaf()
                    || request.capturesFieldWriteState()
                    || request.capturesMutationState())) {
                continue;
            }
            for (JsonElement element : captures) {
                if (!element.isJsonObject()) continue;
                JsonObject capture = element.getAsJsonObject();
                if (!request.captureBindingId().equals(
                        string(capture, "captureBindingId"))) {
                    continue;
                }
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
            JsonObject raw, ExecutionTask task, SemanticPath path,
            List<String> issues) {
        Map<String, SummaryBranchMapping.Policy> policies =
                branchPolicies(task);
        JsonArray result = new JsonArray();
        Set<String> events = new LinkedHashSet<>();
        Set<Integer> decisionPositions = new LinkedHashSet<>();
        for (JsonElement element : array(raw, "branchMappings")) {
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
                    // the selected symbolic slice.  It has no guard to retain
                    // or flip, so it is intentionally absent from the summary.
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
            JsonObject raw, ExecutionTask task, List<String> issues) {
        JsonObject result = new JsonObject();
        OutputClosureContract closure = task.outputClosure();
        if (closure == null) return result;

        Map<String, List<JsonObject>> captures = new LinkedHashMap<>();
        for (JsonElement element : array(raw, "outputCaptures")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            JsonElement expression = row.get("expression");
            if (expression != null && !expression.isJsonNull()) {
                captures.computeIfAbsent(string(row, "captureBindingId"),
                        ignored -> new ArrayList<>())
                        .add(row.deepCopy());
            }
        }

        Map<String, List<OutputCaptureSpec>> specsByPort =
                new LinkedHashMap<>();
        for (OutputCaptureSpec spec : task.outputCaptures()) {
            specsByPort.computeIfAbsent(spec.outputPort(),
                    ignored -> new ArrayList<>()).add(spec);
        }
        for (String port : closure.outputPorts()) {
            List<OutputCaptureSpec> specs = specsByPort.get(port);
            boolean communicationEffect = specs != null
                    && !specs.isEmpty()
                    && specs.stream().allMatch(
                    OutputCaptureSpec::capturesCommunicationEffect);
            if (communicationEffect) {
                // The event is imported separately.  Its payload is never a
                // synthetic whole-object expression; the VM handoff ledger
                // is the only value authority across the boundary.
                continue;
            }
            List<JsonObject> admitted = new ArrayList<>();
            if (specs != null) {
                for (OutputCaptureSpec spec : specs) {
                    List<JsonObject> values = captures.get(
                            spec.captureBindingId());
                    if (values == null) continue;
                    for (JsonObject value : values) {
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
                        admitted, issues);
                if (versionSet != null) result.add(port, versionSet);
                continue;
            }
            // A port published as the activation's own return value has no
            // capture site to bind, so the root observation is the whole
            // relation - and only when this is the one output demanded, since
            // one returned value cannot be several ports.
            boolean rootPublished = (specs == null || specs.isEmpty())
                    && closure.outputPorts().size() == 1;
            JsonElement root = rootOutputExpression(raw);
            if (rootPublished && root != null) {
                result.add(port, root);
                continue;
            }
            if (rootPublished) {
                // Nothing was ever counted here, so a capture count names the
                // wrong thing.  Say what the root observation actually was.
                issues.add("OUTPUT_ROOT_VALUE_UNRELATED:" + port + ":"
                        + rootOutputKind(raw));
                continue;
            }
            issues.add("OUTPUT_CAPTURE_COUNT:" + port + ":"
                    + admitted.size());
        }
        return result;
    }

    /** Case-local declared interaction events observed by this execution. */
    private static JsonArray interactionEvents(
            JsonObject raw, ExecutionTask task, List<String> issues) {
        JsonArray result = new JsonArray();
        Map<String, OutputCaptureSpec> requested = new LinkedHashMap<>();
        for (OutputCaptureSpec spec : task.outputCaptures()) {
            if (spec.capturesCommunicationEffect()) {
                requested.put(spec.captureBindingId(), spec);
            }
        }
        if (requested.isEmpty()) return result;
        Set<String> observed = new LinkedHashSet<>();
        for (JsonElement element : array(raw, "outputCaptures")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            OutputCaptureSpec spec = requested.get(
                    string(row, "captureBindingId"));
            if (spec == null
                    || !"COMMUNICATION_EFFECT".equals(
                    string(row, "interactionKind"))
                    || !"INSTRUMENTED_INTERACTION_SITE_V1".equals(
                    string(row, "authority"))
                    || !exactOutputCaptureOccurrence(spec, row)) {
                continue;
            }
            JsonObject event = row.deepCopy();
            event.remove("captureBindingId");
            event.addProperty("portId", spec.outputPort());
            result.add(event);
            observed.add(spec.captureBindingId());
        }
        for (String binding : requested.keySet()) {
            if (!observed.contains(binding)) {
                issues.add("INTERACTION_EVENT_MISSING:" + binding);
            }
        }
        return result;
    }

    /**
     * Exports every bounded occurrence version observed at one output site.
     *
     * <p>The recorded version ordinal is a site-local bounded index inside this
     * activation, not a cross-execution identity.  Each version becomes one
     * guarded relation case downstream; which version a reader observes is
     * settled by the composed versioned channel, never by collapsing here.</p>
     *
     * <p>Versions are keyed by {@code outputVersionOrdinal}, which runs across
     * the whole output boundary, and not by {@code outputOccurrence}, which
     * restarts inside each definition invocation and so cannot separate the
     * successive states one activation publishes at the same port.</p>
     */
    private static JsonElement siteLocalBoundedVersions(
            String port, List<JsonObject> admitted, List<String> issues) {
        String site = null;
        NavigableMap<Integer, JsonElement> byOrdinal = new TreeMap<>();
        for (JsonObject capture : admitted) {
            String captureSite = string(capture, "outputSiteId");
            int occurrence = integer(capture, "outputVersionOrdinal", -1);
            if (captureSite.isEmpty() || occurrence < 1) {
                // A capture without its site-local ordinal is ambiguous.
                issues.add("OUTPUT_CAPTURE_COUNT:" + port + ":"
                        + admitted.size());
                return null;
            }
            if (site == null) {
                site = captureSite;
            } else if (!site.equals(captureSite)) {
                issues.add("OUTPUT_CAPTURE_VERSION_SITE_MISMATCH:" + port
                        + ":" + site + ":" + captureSite);
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

    /**
     * Admits an observation of the recorded output relation.
     *
     * <p>The recorded ordinal is provenance, not replay identity.  The raw
     * capture must name the requested static endpoint and a positive bounded
     * occurrence; task-level semantic-boundary gating already happened before
     * the row was emitted.</p>
     */
    private static boolean exactOutputCaptureOccurrence(
            OutputCaptureSpec request, JsonObject capture) {
        if (!request.occurrenceScoped()) return true;
        int occurrence = integer(capture, "outputOccurrence", -1);
        // The occurrence counts every activation-local execution of the
        // site, nested calls included; it is not itself replay identity.
        return request.outputSiteId().equals(
                string(capture, "outputSiteId"))
                && occurrence >= 1;
    }

    private static JsonElement rootOutputExpression(JsonObject raw) {
        JsonElement encoded = raw.get("rootOutputExpression");
        if (encoded == null || !encoded.isJsonObject()) return null;
        JsonObject wrapper = encoded.getAsJsonObject();
        JsonElement expression = wrapper.get("expression");
        return expression != null && !expression.isJsonNull()
                ? expression.deepCopy() : null;
    }

    /** What the custom VM observed the activation's root output to be. */
    private static String rootOutputKind(JsonObject raw) {
        JsonElement encoded = raw.get("rootOutputExpression");
        return encoded != null && encoded.isJsonObject()
                ? string(encoded.getAsJsonObject(), "kind") : "";
    }

    private static JsonArray symbolicInputs(JsonObject raw) {
        JsonArray result = new JsonArray();
        Set<String> unique = new LinkedHashSet<>();
        for (JsonElement element : array(raw, "symbolizedInputs")) {
            if (element.isJsonPrimitive()) {
                String symbol = element.getAsString();
                if (!symbol.isEmpty() && unique.add(symbol)) {
                    result.add(symbol);
                }
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

    private static Set<String> regionIds(List<JsonObject> rows)
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

    /**
     * Names why a non-result row published nothing.  An activation that never
     * obtained the single symbolic engine was not refuted, it was never
     * explored; one that ran and contradicted its recording is a finding
     * about the path.  A caller that sees one code for both charges a
     * scheduling artifact to the path -- or the reverse -- so the runtime's
     * own skip kind is carried through instead of being flattened away.
     */
    private static String skippedEventCode(JsonObject raw) {
        String skipKind = string(raw, "skipKind");
        return skipKind.isEmpty() ? "SKIPPED_RUNTIME_EVENT"
                : "REGION_" + skipKind;
    }

    private static String skippedEventDetail(JsonObject raw) {
        String reason = string(raw, "reason");
        String event = string(raw, "event");
        return reason.isEmpty() ? event : event + ": " + reason;
    }

    private static JsonObject diagnostic(
            JsonObject raw, int index, String code, String detail) {
        JsonObject result = new JsonObject();
        result.addProperty("kind", "CONCOLIC_IMPORT_DIAGNOSTIC");
        result.addProperty("code", code);
        result.addProperty("detail", firstNonBlank(detail, "UNKNOWN"));
        result.addProperty("taskId", string(raw, "taskId"));
        result.addProperty("line", index + 1);
        return result;
    }

    /**
     * Whether this seed publishes the one relation observed at its own
     * boundary rather than a branch-by-branch replay path.
     *
     * <p>A producer's relation is read at its semantic output boundary.  It
     * does not stop at every branch and has no branch mapping to be checked
     * against a path seed.</p>
     *
     * <p>Written as the kind that says yes and not as
     * {@code !capturesTargetReach()}: {@code ClosureGoalKind} states outright
     * that its kinds are not complements, and a further kind must have to be
     * added here deliberately rather than inherit this exemption by
     * default.</p>
     */
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

        private static SemanticPath from(JsonArray raw,
                                         JsonArray branchMappings) {
            JsonArray source = raw == null ? new JsonArray() : raw;
            NavigableMap<Integer, JsonElement> original = new TreeMap<>();
            JsonArray expressions = new JsonArray();
            Map<Integer, Integer> indices = new LinkedHashMap<>();
            Set<Integer> branchDecisions =
                    witnessedVmPcIndices(branchMappings);
            for (int index = 0; index < source.size(); index++) {
                JsonElement expression = source.get(index);
                original.put(index, expression == null
                        ? JsonNull.INSTANCE : expression.deepCopy());
                boolean witnessed = branchDecisions.contains(index);
                if (!witnessed
                        && (expression == null || expression.isJsonNull())) {
                } else if (!witnessed
                        && (InitialContainerObservation.isConcreteEquality(
                        expression)
                        || pcPredicate(expression))) {
                } else {
                    indices.put(index, expressions.size());
                    expressions.add(expression.deepCopy());
                }
            }
            return new SemanticPath(original, expressions, indices,
                    source.size());
        }

        /**
         * Reconstructs one compact case from its selected branch witnesses
         * and the VM's separately bounded non-branch solver constraints.
         *
         * <p>The two channels name positions in the same full VM path
         * condition.  Keeping that index is what lets us carry a container
         * or method relation once per case without copying it into every
         * shared-field version guard.  Missing, conflicting or truncated
         * evidence is a named incomplete relation; no position is guessed or
         * silently overwritten.</p>
         */
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
            if (watermark < 0 || count < 0 || count != indices.size()
                    || count != conditions.size()
                    || encodedIndices == null
                    || !encodedIndices.isJsonArray()
                    || encodedConditions == null
                    || !encodedConditions.isJsonArray()) {
                issues.add("AUXILIARY_PATH_CONDITION_MALFORMED:CARDINALITY");
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
                    issues.add("VM_EXPRESSION_SERIALIZATION_TRUNCATED:"
                            + "AUXILIARY_PATH_CONDITION:" + index);
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

        /**
         * Whether any row carries a decision the summary can admit.
         *
         * <p>Deliberately weaker than {@link #hasSelectedBranchWitness}: that
         * one asks for a witnessed row because it decides whether the path
         * condition can be rebuilt from witnesses, and a concrete observation
         * owns no path-condition term to rebuild from.  This one only asks
         * whether the execution decided anything a case could attribute.</p>
         */
        private static boolean hasAdmissibleBranchDecision(
                JsonArray branchMappings) {
            if (hasSelectedBranchWitness(branchMappings)) return true;
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) continue;
                JsonElement concrete = element.getAsJsonObject()
                        .get("concreteObservation");
                if (concrete != null && concrete.isJsonObject()) return true;
            }
            return false;
        }

        private static boolean hasSelectedBranchWitness(
                JsonArray branchMappings) {
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                if (!row.has("witness")
                        || !row.get("witness").isJsonObject()) {
                    continue;
                }
                try {
                    int index = BranchWitness.fromJson(
                            row.getAsJsonObject("witness")).vmPcIndex();
                    if (index >= 0) return true;
                } catch (IllegalArgumentException ignored) {
                    // branchMappings() owns the diagnostic.
                }
            }
            return false;
        }

        /**
         * A producer seed reads the VM path condition once, at its semantic
         * output boundary.  There are intentionally no per-branch mappings
         * in that mode, so filtering predicates by mapping ownership would
         * erase the guard of the exported input/output relation.
         */
        private static SemanticPath atRelationBoundary(
                JsonArray raw, ExecutionTask task) {
            JsonArray source = raw == null ? new JsonArray() : raw;
            NavigableMap<Integer, JsonElement> original = new TreeMap<>();
            JsonArray expressions = new JsonArray();
            Map<Integer, Integer> indices = new LinkedHashMap<>();
            Set<String> composedFieldInputs = new LinkedHashSet<>();
            for (JsonElement element : task.inputActions().all()) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                if (!string(action, "intraRegionSourceOutputPort").isEmpty()
                        && "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1".equals(
                        string(action, "intraRegionReadFromAuthority"))) {
                    String symbol = firstNonBlank(string(action, "symbol"),
                            string(action, "portId"));
                    if (!symbol.isEmpty()) composedFieldInputs.add(symbol);
                }
            }
            for (int index = 0; index < source.size(); index++) {
                JsonElement expression = source.get(index);
                original.put(index, expression == null
                        ? JsonNull.INSTANCE : expression.deepCopy());
                if (composedFieldMaterialization(
                        expression, composedFieldInputs)) {
                } else {
                    indices.put(index, expressions.size());
                    expressions.add(expression.deepCopy());
                }
            }
            return new SemanticPath(original, expressions, indices,
                    source.size());
        }

        /**
         * A composed field input is defined by its exact producer edge.  The
         * VM equality emitted while installing that symbol only describes the
         * replay heap used to seed this run; retaining it would join the exact
         * producer relation to an unrelated replay pre-state.  All later
         * predicates that use the symbol remain part of the relation case.
         */
        private static boolean composedFieldMaterialization(
                JsonElement expression, Set<String> composedInputs) {
            if (composedInputs.isEmpty() || expression == null
                    || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            if (!"BinaryExpression".equals(string(object, "_type"))
                    || !string(object, "_code_position").contains(
                    "java.lang.System.symbolizeExactField(")) {
                return false;
            }
            String left = symbolExpression(object.get("_left"));
            String right = symbolExpression(object.get("_right"));
            for (String input : composedInputs) {
                if (left.contains(input) || right.contains(input)) {
                    return true;
                }
            }
            return false;
        }

        private static String symbolExpression(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return "";
            JsonObject object = expression.getAsJsonObject();
            return "SymbolExpression".equals(string(object, "_type"))
                    ? string(object, "_exp") : "";
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

    private static String requireIterationId(String iterationId) {
        if (iterationId == null || iterationId.trim().isEmpty()) {
            throw new IllegalArgumentException(
                    "import iteration id must be non-blank");
        }
        return iterationId.trim();
    }

    private static Path sibling(Path input, String name) {
        Path parent = input.toAbsolutePath().normalize().getParent();
        return parent == null ? Paths.get(name) : parent.resolve(name);
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
