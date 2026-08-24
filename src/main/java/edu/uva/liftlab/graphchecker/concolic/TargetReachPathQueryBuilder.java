package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourceSelectorContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Builds one failure-directed solver query from exact source-attested target
 * paths. The desired outcome is the witnessed source decision's complement;
 * it need not already have a concrete replay.
 */
public final class TargetReachPathQueryBuilder {
    static final String TARGET_ATTESTATION_ROLE =
            "targetReachAttestationRole";
    static final String SOURCE_TARGET_REACH_EVENT =
            "SOURCE_TARGET_REACH_EVENT";
    static final String REQUIRED_TARGET_REACH_EVENT =
            "REQUIRED_TARGET_REACH_EVENT";
    static final String SOURCE_FATAL_BRANCH_AUTHORITY =
            "RUNTIME_SOURCE_EVENT_AND_WITNESS_FLIP_V1";
    static final String REQUIRED_FATAL_BRANCH_AUTHORITY =
            "RUNTIME_REQUIRED_TARGET_EVENT_V1";
    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private TargetReachPathQueryBuilder() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject result = build(arguments);
        String encoded = JSON.toJson(result);
        ArtifactIO.replace(arguments.output,
                encoded + System.lineSeparator());
        System.out.println(encoded);
    }

    static JsonObject build(Arguments arguments) throws IOException {
        JsonObject manifest = ArtifactIO.readObject(arguments.pathManifest);
        validatePathManifest(manifest);
        if (!ClosureGoalKind.TARGET_REACH_CLOSURE.name().equals(
                string(manifest, ClosureGoalKind.TASK_FIELD))) {
            // Not an evidence disagreement: this artifact is not a target
            // reach worklist at all, so there is nothing to merge from it.
            throw new IOException(
                    "target path worklist is not a target reach closure");
        }
        // Named, never silent, but never a reason to publish nothing: a
        // worklist that stopped short or carried gaps is a partial region,
        // and a partial region is what best effort merging produces. A
        // satisfying path may still be accepted; the downstream UNSAT
        // closure authority prevents absence in this set from becoming an
        // unreachability claim.
        List<JsonObject> coverageGaps = new ArrayList<>();
        for (JsonElement element : array(manifest, "coverageGaps")) {
            if (element.isJsonObject()) {
                JsonObject raw = element.getAsJsonObject();
                String kind = string(raw, "kind");
                if (isTargetPathCoverageGap(kind)) {
                    coverageGaps.add(CoverageDivergence.of(
                            CoverageDivergence.Kind.TARGET, kind,
                            string(raw, "queryKey"),
                            string(raw, "reason")));
                } else {
                    coverageGaps.add(raw.deepCopy());
                }
            }
        }
        String worklistState = string(manifest, "state");
        String coverageState = string(manifest, "coverageState");
        JsonArray worklistGaps = array(manifest, "gaps");
        boolean hasClassifiedCoverage = false;
        for (JsonObject gap : coverageGaps) {
            if (CoverageDivergence.classify(gap) != null) {
                hasClassifiedCoverage = true;
                break;
            }
        }
        if (!"CLOSED".equals(worklistState) || worklistGaps.size() != 0
                || !"CLOSED".equals(coverageState)
                && !hasClassifiedCoverage) {
            coverageGaps.add(CoverageDivergence.of(
                    CoverageDivergence.Kind.TARGET,
                    "TARGET_WORKLIST_NOT_CLOSED",
                    string(manifest, "occurrenceId"),
                    "state=" + worklistState + ", coverageState="
                            + firstNonBlank(coverageState, "UNSTATED")
                            + ", gaps="
                            + worklistGapReasons(worklistGaps)));
        }

        List<JsonObject> seeds = ArtifactIO.readJsonl(arguments.seedQuery,
                "Malformed target seed query %1$s:%2$d",
                "Non-object target seed query %1$s:%2$d");
        List<JsonObject> ready = new ArrayList<>();
        for (JsonObject row : seeds) {
            if ("TARGET_BRANCH_SOLVER_QUERY".equals(string(row, "kind"))
                    && bool(row, "readyForSolver", false)) {
                ready.add(row);
            }
        }
        JsonObject seed = decidingSeed(ready);
        if (seed == null) {
            throw new IOException("one solver-ready target seed query must"
                    + " decide the target; found " + ready.size()
                    + " and none of them waits on all the others");
        }
        String queryKey = string(seed, "queryKey");
        if (queryKey.isEmpty()) {
            throw new IOException(
                    "target seed query has no stable queryKey");
        }
        String region = string(seed, "regionId");
        String occurrenceId = string(seed, "occurrenceId");
        String goalId = string(seed, "goalId");
        String targetSite = string(seed, "targetSiteId");
        if (!region.equals(string(manifest, "regionId"))
                || !goalId.equals(string(manifest, "goalId"))
                || !occurrenceId.equals(string(manifest, "occurrenceId"))
                || region.isEmpty() || occurrenceId.isEmpty()
                || goalId.isEmpty() || targetSite.isEmpty()) {
            throw new IOException(
                    "target seed and closed path scope do not match");
        }
        if (!arguments.targetInstance.isEmpty()
                && !arguments.targetInstance.equals(occurrenceId)) {
            throw new IOException("selected target occurrence does not match "
                    + "the seed query");
        }
        LoopBoundPolicy seedLoopBound = loopBound(seed,
                "target seed query");
        LoopBoundPolicy worklistLoopBound = loopBound(manifest,
                "target path worklist");
        if (!seedLoopBound.identity().equals(
                worklistLoopBound.identity())) {
            throw new IOException("target seed and closed path worklist "
                    + "do not have the same loopBound authority");
        }
        SelectedOccurrence selected = SelectedOccurrence.decode(
                object(seed, "selectedTargetOccurrence"), region,
                occurrenceId, "target seed query");
        BranchReplayContract targetReplay;
        try {
            targetReplay = BranchReplayContract.fromJson(
                    object(seed, "replayContract"));
        } catch (IllegalArgumentException malformed) {
            throw new IOException("malformed target replay contract",
                    malformed);
        }
        if (!targetSite.equals(targetReplay.source().siteId())) {
            throw new IOException(
                    "target replay contract does not match target site");
        }
        int targetOccurrence = targetReplay.source().occurrence();
        JsonElement fatalOutcome = seed.get("fatalRequiredTakenOutcome");
        if (fatalOutcome == null || !fatalOutcome.isJsonPrimitive()
                || !fatalOutcome.getAsJsonPrimitive().isBoolean()) {
            throw new IOException(
                    "target seed query has no fatal branch outcome");
        }
        boolean fatalRequiredOutcome = fatalOutcome.getAsBoolean();
        if (fatalRequiredOutcome != targetReplay.requiredTakenOutcome()) {
            throw new IOException("target seed desired outcome is not the "
                    + "exact source witness flip");
        }

        List<JsonObject> summaries = ArtifactIO.readJsonl(arguments.summaries,
                "Malformed target summary %1$s:%2$d",
                "Non-object target summary %1$s:%2$d");
        TargetDecision progressed = progressedTargetDecision(seed,
                summaries, region, occurrenceId, goalId, targetSite);
        if (progressed != null) {
            targetSite = progressed.siteId;
            targetOccurrence = progressed.occurrence;
            fatalRequiredOutcome = progressed.requiredOutcome;
            targetReplay = progressed.replayContract;
        }

        Map<String, JsonObject> pathsByKey = new LinkedHashMap<>();
        Map<String, JsonObject> runtimeBindings = new LinkedHashMap<>();
        // Edges whose runtime evidence two target paths state differently.
        Map<String, String> contestedBindings = new LinkedHashMap<>();
        // Path keys two summaries describe differently.  Neither is kept:
        // picking one would be a semantic choice this class cannot make.
        Map<String, String> conflictingPaths = new LinkedHashMap<>();
        Map<String, JsonObject> symbolicSources = new LinkedHashMap<>();
        // One exact required-outcome execution is already an existential
        // failure witness. Prefer one deterministic direct witness over the
        // seed projection and over other direct witnesses. Hoisting several
        // executions' RPC handoffs into one query would incorrectly require
        // different producer cases to hold simultaneously at the same
        // receiver port.
        JsonObject directWitness = directRequiredWitness(summaries, region,
                occurrenceId, goalId, targetSite, targetOccurrence,
                fatalRequiredOutcome);
        for (JsonObject summary : summaries) {
            if (directWitness != null && summary != directWitness) continue;
            if (!region.equals(string(summary, "regionId"))
                    || !occurrenceId.equals(string(summary,
                    "occurrenceId"))
                    || !goalId.equals(string(summary, "goalId"))
                    || !ClosureGoalKind.fromTask(summary)
                    .capturesTargetReach()
                    || !bool(summary, "relationallyComplete", false)) {
                continue;
            }
            selected.requireExactDemandLedger(summary);
            // Parsing is the schema/admission boundary for branch-owned
            // predicates. The importer already normalized the PC; this check
            // prevents a malformed mapping row from entering the path set.
            PathObservation observation = PathObservation.decode(
                    summary, null);
            if (!seedLoopBound.identity().equals(
                    observation.scope().loopBound().identity())) {
                throw new IOException("target summary and seed query do not "
                        + "have the same loopBound authority");
            }
            if (!observation.branchMappingIssue().isEmpty()) {
                throw new IOException("Malformed target branch mapping: "
                        + observation.branchMappingIssue());
            }
            SummaryBranchMapping targetMapping = targetSiteMapping(
                    observation, targetSite, targetOccurrence);
            if (targetMapping == null) {
                continue;
            }
            BranchWitness sourceWitness = targetReplay.source();
            if (!sourceWitness.decisionIdentity().equals(
                    targetMapping.witness().decisionIdentity())) {
                continue;
            }
            final PathObservation.TargetReachEvent targetReach;
            try {
                targetReach = observation.targetReachEvent();
            } catch (IllegalArgumentException malformed) {
                throw new IOException("Malformed target reach event: "
                        + malformed.getMessage(), malformed);
            }
            if (targetReach == null
                    || !targetReach.matches(targetMapping.siteId(),
                    targetMapping.occurrence(),
                    targetMapping.sourceTakenOutcome())) {
                continue;
            }
            boolean sourceAttested = sourceWitness.sourceTakenOutcome()
                    == targetMapping.sourceTakenOutcome();
            boolean requiredAttested = fatalRequiredOutcome
                    == targetMapping.sourceTakenOutcome();
            if (!sourceAttested && !requiredAttested) continue;
            // No side evidence from an unattested target path enters the
            // query either.  Bindings, shared state and handoff references
            // belong to the same execution as this exact target event.
            collectRuntimeBindings(summary, runtimeBindings,
                    contestedBindings);
            JsonObject shared = object(summary,
                    SharedStateEvidence.RECORDED_FIELD);
            for (JsonObject source
                    : SymbolicSourceEvidence.eventsOf(summary)) {
                String identity = SymbolicSourceEvidence.identity(source);
                JsonObject prior = symbolicSources.putIfAbsent(identity,
                        source.deepCopy());
                if (prior != null && !prior.equals(source)) {
                    throw new IOException("target paths disagree on exact "
                            + "configured source phase " + identity);
                }
            }

            JsonObject path = new JsonObject();
            if (shared.size() > 0) {
                path.add(SharedStateEvidence.RECORDED_FIELD,
                        shared.deepCopy());
            }
            JsonArray constraints = requiredAttested
                    ? witnessedTargetConstraints(summary, targetMapping)
                    : flippedTargetConstraints(summary, targetMapping);
            path.addProperty("fatalBranchConditionAuthority",
                    requiredAttested
                            ? REQUIRED_FATAL_BRANCH_AUTHORITY
                            : SOURCE_FATAL_BRANCH_AUTHORITY);
            path.addProperty(TARGET_ATTESTATION_ROLE,
                    requiredAttested ? REQUIRED_TARGET_REACH_EVENT
                            : SOURCE_TARGET_REACH_EVENT);
            path.add(PathObservation.TargetReachEvent.FIELD,
                    targetReach.toJson());
            path.addProperty("desiredTakenOutcome",
                    fatalRequiredOutcome);
            List<JsonObject> selectorEvidence =
                    ConfiguredSourceSelectorContract.evidenceOf(summary);
            if (!selectorEvidence.isEmpty()) {
                JsonArray encodedSelectors = new JsonArray();
                for (JsonObject evidence : selectorEvidence) {
                    encodedSelectors.add(evidence.deepCopy());
                }
                // Unlike RPC/session catalogs, this value was consumed by
                // one concrete target replay.  Hoisting it to the query root
                // would let a different target prefix reuse that replay's
                // selected application object.
                path.add(ConfiguredSourceSelectorContract.EVIDENCE_FIELD,
                        encodedSelectors);
            }
            // The attached expression belongs to this exact target replay.
            // Hoisting it to the query root lets another target-prefix case
            // reuse a delivery that did not occur in that replay.
            VmHandoffEvidence.writeTo(path,
                    VmHandoffEvidence.eventsOf(summary));
            JsonArray loopCounts = observation.pathLoopCounts();
            if (loopCounts.size() > 0) {
                path.add(LoopBoundPolicy.PATH_LOOP_COUNTS, loopCounts);
            }
            JsonArray loopCountGaps = observation.pathLoopCountGaps();
            if (loopCountGaps.size() > 0) {
                path.add(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS,
                        loopCountGaps);
            }
            String pathKey = observation.pathKey();
            path.add("constraints", constraints.deepCopy());
            if (conflictingPaths.containsKey(pathKey)) continue;
            JsonObject previous = pathsByKey.put(pathKey, path);
            if (previous != null && !previous.equals(path)) {
                // Same key, different content: drop both and name it.  One
                // of them is not "the" path, and choosing would assert a
                // prefix the recording never singled out.
                pathsByKey.remove(pathKey);
                conflictingPaths.put(pathKey,
                        disagreementDetail(previous, path));
            }
        }

        List<String> pathKeys = new ArrayList<>(pathsByKey.keySet());
        Collections.sort(pathKeys);
        JsonArray encodedPaths = new JsonArray();
        for (String pathKey : pathKeys) {
            encodedPaths.add(pathsByKey.get(pathKey));
        }
        if (encodedPaths.size() == 0) {
            throw new IOException(
                    "target path set contains no exact "
                            + "source-attested target path");
        }

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        result.addProperty("queryKey", queryKey);
        result.addProperty("regionId", region);
        result.addProperty("occurrenceId", occurrenceId);
        if (!string(seed, "sourceKey").isEmpty()) {
            result.addProperty("sourceKey", string(seed, "sourceKey"));
        }
        result.addProperty("targetSiteId", targetSite);
        result.addProperty("targetOccurrence", targetOccurrence);
        result.addProperty("requiredTakenOutcome", fatalRequiredOutcome);
        result.add("paths", encodedPaths);
        result.add("seedReplayContract", targetReplay.toJson());
        seedLoopBound.writeTo(result);
        JsonObject symbolicContext =
                object(seed, "symbolicContext").deepCopy();
        selected.requireExactContext(symbolicContext);
        result.add("symbolicContext", symbolicContext);
        result.add("selectedTargetBindings",
                selected.exactBindings(runtimeBindings));
        SymbolicSourceEvidence.writeTo(result,
                new ArrayList<>(symbolicSources.values()));
        // Named, never silent: an edge dropped from refinement is coverage
        // the query does not carry, and the composer folds these rows into
        // the same coverage stream as every other named gap.
        for (Map.Entry<String, String> entry
                : contestedBindings.entrySet()) {
            coverageGaps.add(CoverageDivergence.of(
                    CoverageDivergence.Kind.FLOW,
                    "TARGET_PATH_BINDING_NOT_USABLE", entry.getKey(),
                    "target paths describe this edge differently, so it"
                            + " does not refine its seed binding: "
                            + entry.getValue()));
        }
        for (Map.Entry<String, String> entry
                : conflictingPaths.entrySet()) {
            coverageGaps.add(CoverageDivergence.of(
                    CoverageDivergence.Kind.TARGET,
                    "TARGET_PATH_NOT_USABLE", entry.getKey(),
                    "target summaries describe this path differently, so"
                            + " neither description is carried: "
                            + entry.getValue()));
        }
        if (!coverageGaps.isEmpty()) {
            JsonArray gaps = new JsonArray();
            for (JsonObject row : coverageGaps) gaps.add(row);
            result.add("coverageGaps", gaps);
        }
        result.add("selectedTargetOccurrence", selected.encoded.deepCopy());
        result.addProperty("constraintAuthority",
                "RECORDED_TARGET_PREFIX_V1");
        return result;
    }

    private static boolean isTargetPathCoverageGap(String kind) {
        return kind.startsWith("PATH_FLIP_")
                || "UNSUPPORTED_PATH_FLIP".equals(kind)
                || "BOUND_REACHED".equals(kind);
    }

    private static void validatePathManifest(JsonObject manifest)
            throws IOException {
        if (JsonFields.integer(manifest, "schemaVersion", -1) != 1
                || !"REGION_PATH_WORKLIST".equals(string(manifest, "kind"))) {
            throw new IOException("target path worklist schema is invalid");
        }
        String state = string(manifest, "state");
        if (!("NOT_STARTED".equals(state) || "GAPPED".equals(state)
                || "PENDING".equals(state) || "CLOSED".equals(state))) {
            throw new IOException("target path worklist state is invalid");
        }
        for (String field : new String[]{"gaps", "coverageGaps"}) {
            JsonElement value = manifest.get(field);
            if (value == null || !value.isJsonArray()) {
                throw new IOException("target path worklist " + field
                        + " must be an array");
            }
        }
        String coverage = string(manifest, "coverageState");
        if (!("CLOSED".equals(coverage) || "PARTIAL".equals(coverage)
                || "SEED_ONLY".equals(coverage))) {
            throw new IOException(
                    "target path worklist coverageState is invalid");
        }
    }

    /** Decodes one exact loop authority at an artifact boundary. */
    private static LoopBoundPolicy loopBound(JsonObject owner, String label)
            throws IOException {
        try {
            return LoopBoundPolicy.decode(owner);
        } catch (IllegalArgumentException malformed) {
            throw new IOException(label + " has no usable loopBound authority",
                    malformed);
        }
    }

    /**
     * Promotes an observed outer target frontier to the next exact guard of
     * the same annotated throw.
     *
     * <p>The compact catalog is static authority for membership and required
     * polarity; the fresh summary is runtime authority that the successor was
     * actually reached.  With a pending successor and no such summary the
     * outer complement is not a fatal query and is refused.</p>
     */
    private static TargetDecision progressedTargetDecision(
            JsonObject seed, List<JsonObject> summaries,
            String region, String occurrenceId, String goalId,
            String currentSite) throws IOException {
        JsonArray encoded = array(seed, "targetGuardCatalog");
        List<JsonObject> catalog = new ArrayList<>();
        for (JsonElement element : encoded) {
            if (element.isJsonObject()) {
                catalog.add(element.getAsJsonObject());
            }
        }
        if (catalog.isEmpty()) return null;
        int current = uniqueGuardIndex(catalog, currentSite);
        if (current < 0) {
            throw new IOException("target guard catalog does not contain "
                    + "the selected site " + currentSite);
        }
        Set<String> corridor = guardedTargetIdentities(
                catalog.get(current));
        Set<Integer> successors = new LinkedHashSet<>();
        for (int index = current + 1; index < catalog.size(); index++) {
            JsonObject candidate = catalog.get(index);
            if (!bool(candidate, "failureTarget", false)
                    || requiredOutcome(candidate) == null
                    || Collections.disjoint(corridor,
                    guardedTargetIdentities(candidate))) {
                continue;
            }
            successors.add(index);
        }
        if (successors.isEmpty()) return null;

        TargetDecision selected = null;
        String selectedPath = null;
        int selectedIndex = -1;
        for (JsonObject summary : summaries) {
            if (!region.equals(string(summary, "regionId"))
                    || !occurrenceId.equals(string(summary,
                    "occurrenceId"))
                    || !goalId.equals(string(summary, "goalId"))
                    || !ClosureGoalKind.fromTask(summary)
                    .capturesTargetReach()
                    || !bool(summary, "relationallyComplete", false)) {
                continue;
            }
            PathObservation observation = PathObservation.decode(
                    summary, null);
            if (!observation.branchMappingIssue().isEmpty()) {
                throw new IOException("Malformed target branch mapping: "
                        + observation.branchMappingIssue());
            }
            final PathObservation.TargetReachEvent reach;
            try {
                reach = observation.targetReachEvent();
            } catch (IllegalArgumentException malformed) {
                throw new IOException("Malformed target reach event: "
                        + malformed.getMessage(), malformed);
            }
            if (reach == null) continue;
            int index = uniqueGuardIndex(catalog, reach.siteId());
            if (!successors.contains(index)) continue;
            SummaryBranchMapping mapping = targetSiteMapping(observation,
                    reach.siteId(), reach.occurrence());
            if (mapping == null || !reach.matches(mapping.siteId(),
                    mapping.occurrence(),
                    mapping.sourceTakenOutcome())) {
                continue;
            }
            Boolean required = requiredOutcome(catalog.get(index));
            if (required == null) continue;
            BranchReplayContract replay = BranchReplayContract.fromSummary(
                    summary, reach.siteId(), reach.occurrence());
            // A normal successor event is the source witness whose complement
            // final composition must solve.  An already-failing execution is
            // a different direct-attestation protocol; never encode it as an
            // opposite-polarity replay by accident.
            if (replay.requiredTakenOutcome() != required) continue;
            String pathKey = observation.pathKey();
            if (selected == null || index > selectedIndex
                    || index == selectedIndex
                    && pathKey.compareTo(selectedPath) < 0) {
                selected = new TargetDecision(reach.siteId(),
                        reach.occurrence(), required, replay);
                selectedPath = pathKey;
                selectedIndex = index;
            }
        }
        if (selected == null) {
            throw new IOException("target frontier " + currentSite
                    + " has an unobserved successor guard in the same "
                    + "annotated exception corridor");
        }
        return selected;
    }

    private static int uniqueGuardIndex(List<JsonObject> catalog,
                                        String siteId) throws IOException {
        int result = -1;
        for (int index = 0; index < catalog.size(); index++) {
            if (!siteId.equals(string(catalog.get(index), "siteId"))) {
                continue;
            }
            if (result >= 0) {
                throw new IOException("target guard catalog contains the "
                        + "same site twice: " + siteId);
            }
            result = index;
        }
        return result;
    }

    private static Boolean requiredOutcome(JsonObject branch) {
        JsonElement encoded = branch.get("requiredOutcome");
        return encoded != null && encoded.isJsonPrimitive()
                && encoded.getAsJsonPrimitive().isBoolean()
                ? encoded.getAsBoolean() : null;
    }

    private static Set<String> guardedTargetIdentities(JsonObject branch) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement cell : array(branch, "failureTargetCells")) {
            if (!cell.isJsonPrimitive()) continue;
            String value = cell.getAsString();
            int suffix = value.indexOf("#exception:");
            result.add(suffix < 0 ? value : value.substring(0, suffix));
        }
        for (JsonElement element : array(branch,
                "guardedSiteOutcomes")) {
            if (!element.isJsonObject()) continue;
            String site = string(element.getAsJsonObject(), "siteId");
            if (!site.isEmpty()) result.add(site);
        }
        return result;
    }

    private static final class TargetDecision {
        private final String siteId;
        private final int occurrence;
        private final boolean requiredOutcome;
        private final BranchReplayContract replayContract;

        private TargetDecision(String siteId, int occurrence,
                               boolean requiredOutcome,
                               BranchReplayContract replayContract) {
            this.siteId = siteId;
            this.occurrence = occurrence;
            this.requiredOutcome = requiredOutcome;
            this.replayContract = replayContract;
        }
    }

    /** Selects one exact required-outcome target execution by stable key. */
    private static JsonObject directRequiredWitness(
            List<JsonObject> summaries, String region, String occurrenceId,
            String goalId, String targetSite, int targetOccurrence,
            boolean requiredOutcome) throws IOException {
        JsonObject selected = null;
        String selectedKey = null;
        for (JsonObject summary : summaries) {
            if (!region.equals(string(summary, "regionId"))
                    || !occurrenceId.equals(string(summary, "occurrenceId"))
                    || !goalId.equals(string(summary, "goalId"))
                    || !ClosureGoalKind.fromTask(summary)
                    .capturesTargetReach()
                    || !bool(summary, "relationallyComplete", false)) {
                continue;
            }
            PathObservation observation = PathObservation.decode(
                    summary, null);
            if (!observation.branchMappingIssue().isEmpty()) continue;
            SummaryBranchMapping mapping = targetSiteMapping(observation,
                    targetSite, targetOccurrence);
            PathObservation.TargetReachEvent event;
            try {
                event = observation.targetReachEvent();
            } catch (IllegalArgumentException malformed) {
                throw new IOException("Malformed target reach event: "
                        + malformed.getMessage(), malformed);
            }
            if (mapping == null || !mapping.isWitnessed()
                    || mapping.sourceTakenOutcome() != requiredOutcome
                    || event == null || !event.matches(targetSite,
                    targetOccurrence, requiredOutcome)) {
                continue;
            }
            String key = observation.pathKey();
            if (selected == null || key.compareTo(selectedKey) < 0) {
                selected = summary;
                selectedKey = key;
            }
        }
        return selected;
    }

    /**
     * The one seed query that decides the target, or null when none does.
     *
     * <p>{@code if (p && q) throw} is lowered to two conditional sites.  Both
     * are eligible failure targets carrying an exception guard into the
     * <em>same</em> throw, so the scheduler plans a solver query per conjunct
     * and this file legitimately holds several.  They are not rival targets:
     * the conjunct the throw actually waited on carries every earlier one in
     * its own {@code orderedPrefix}, because that is what the recording
     * observed.  That containment is the selection - not file order, not the
     * longest prefix, not the highest unit index - and a set in which no
     * member waits on all the others names two unrelated failures and is
     * refused by the caller.</p>
     */
    private static JsonObject decidingSeed(List<JsonObject> ready) {
        if (ready.size() == 1) return ready.get(0);
        for (JsonObject candidate : ready) {
            BranchReplayContract contract = replayContract(candidate);
            if (contract == null) continue;
            Set<String> waitedOn = new LinkedHashSet<>();
            for (BranchWitness witness : contract.orderedPrefix()) {
                waitedOn.add(witness.decisionIdentity());
            }
            boolean decides = true;
            for (JsonObject other : ready) {
                if (other == candidate) continue;
                BranchReplayContract rival = replayContract(other);
                if (rival == null || !waitedOn.contains(
                        rival.source().decisionIdentity())) {
                    decides = false;
                    break;
                }
            }
            if (decides) return candidate;
        }
        return null;
    }

    private static BranchReplayContract replayContract(JsonObject seed) {
        try {
            return BranchReplayContract.fromJson(
                    object(seed, "replayContract"));
        } catch (IllegalArgumentException malformed) {
            return null;
        }
    }

    /**
     * Collects the runtime binding evidence the target paths agree on.
     *
     * <p>A region is merged best effort: not every path has to be usable, and
     * one edge two paths describe differently is not a reason to publish no
     * query at all.  README: observed cases are an existential
     * under-approximation, so a SAT witness may retain named coverage gaps;
     * only an UNSAT conclusion requires a closed path set. The contested edge
     * simply does not refine its seed and the query is still built.</p>
     *
     * <p>The contested edge is dropped rather than resolved.  Choosing one of
     * two descriptions would be a pairing decision this class has no
     * authority to make, and the field they disagree on is exactly the one a
     * later stage keys the map carrier on.  Dropping keeps the seed's own
     * binding and names what was lost.</p>
     */
    private static void collectRuntimeBindings(
            JsonObject summary, Map<String, JsonObject> bindings,
            Map<String, String> contested) {
        for (JsonElement element : array(summary, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String id = string(binding, "edgeId");
            if (id.isEmpty() || contested.containsKey(id)) continue;
            JsonObject previous = bindings.putIfAbsent(id,
                    binding.deepCopy());
            if (previous != null
                    && !comparable(previous).equals(comparable(binding))) {
                bindings.remove(id);
                contested.put(id, disagreementDetail(
                        comparable(previous), comparable(binding)));
            }
        }
    }

    /** The worklist's own gap reasons, so the partial region names itself. */
    private static String worklistGapReasons(JsonArray gaps) {
        List<String> reasons = new ArrayList<>();
        for (JsonElement element : gaps) {
            if (element.isJsonObject()) {
                JsonObject row = element.getAsJsonObject();
                String reason = string(row, "reason");
                reasons.add(reason.isEmpty()
                        ? string(row, "kind") : reason);
            } else {
                reasons.add(element.toString());
            }
        }
        return reasons.isEmpty() ? "none" : String.join(";", reasons);
    }

    /**
     * The binding members two sessions must agree on.  The VM's own
     * location triple is session-local by construction -- the rid counter
     * restarts per replay session -- so it is retained as provenance beside
     * the canonical key and deliberately differs between two recordings of
     * one location.  Contesting on it would make every canonicalized edge
     * disagree with itself.
     */
    private static JsonObject comparable(JsonObject binding) {
        if (!binding.has(SharedStateEvidence.SESSION_LOCATION_FIELD)) {
            return binding;
        }
        JsonObject copy = binding.deepCopy();
        copy.remove(SharedStateEvidence.SESSION_LOCATION_FIELD);
        return copy;
    }

    private static String disagreementDetail(JsonObject left,
                                             JsonObject right) {
        java.util.List<String> fields = new ArrayList<>();
        java.util.Set<String> names = new java.util.TreeSet<>(left.keySet());
        names.addAll(right.keySet());
        for (String name : names) {
            JsonElement a = left.get(name);
            JsonElement b = right.get(name);
            if (a == null ? b != null : !a.equals(b)) {
                fields.add(name + "=" + string(left, name) + "|"
                        + string(right, name));
            }
        }
        return String.join(",", fields);
    }

    /** The witnessed decision of the exact target site, or null. */
    private static SummaryBranchMapping targetSiteMapping(
            PathObservation observation, String siteId, int occurrence) {
        for (SummaryBranchMapping mapping
                : observation.branchMappings()) {
            if (mapping.isWitnessed()
                    && siteId.equals(mapping.siteId())
                    && occurrence == mapping.occurrence()) {
                return mapping;
            }
        }
        return null;
    }

    /**
     * Projects one attested source path into the requested target flip.
     *
     * <p>The runtime event proves only that the exact source decision was
     * reached with its recorded outcome.  It is not evidence that the
     * opposite, failure-directed outcome has already been replayed.  Keep the
     * recorded prefix, discard the source-only suffix, and make the exact
     * witnessed target predicate's complement the final case condition.  The
     * untouched {@code TARGET_REACH_EVENT} remains beside this projection as
     * source attestation; no synthetic fatal event is created.</p>
     */
    private static JsonArray flippedTargetConstraints(
            JsonObject summary, SummaryBranchMapping target) {
        JsonArray recorded = array(summary, "pathCondition");
        int targetPosition = target.summaryPcIndex();
        if (!target.isWitnessed() || targetPosition < 0
                || targetPosition >= recorded.size()) {
            throw new IllegalArgumentException(
                    "target witness is outside the recorded path");
        }
        JsonArray result = new JsonArray();
        for (int index = 0; index < targetPosition; index++) {
            result.add(recorded.get(index).deepCopy());
        }
        result.add(BranchPredicateAlgebra.complement(
                target.witness().sourceSatisfiedPredicate()));
        return result;
    }

    /** Keeps the recorded prefix through an already-required target event. */
    private static JsonArray witnessedTargetConstraints(
            JsonObject summary, SummaryBranchMapping target) {
        JsonArray recorded = array(summary, "pathCondition");
        int targetPosition = target.summaryPcIndex();
        if (!target.isWitnessed() || targetPosition < 0
                || targetPosition >= recorded.size()) {
            throw new IllegalArgumentException(
                    "target witness is outside the recorded path");
        }
        JsonArray result = new JsonArray();
        for (int index = 0; index <= targetPosition; index++) {
            result.add(recorded.get(index).deepCopy());
        }
        return result;
    }

    /**
     * The activation the seed query selected.
     *
     * <p>Its {@code inputPorts} are the exact port ids of that one
     * activation, so nothing here renames a canonical template port onto an
     * exact one: the scheduler already emits the activation's own symbols and
     * the decoder only admits ports that are minted for this occurrence --
     * an input of its region, or a port the cut it sits behind declares.</p>
     */
    private static final class SelectedOccurrence {
        private final JsonObject encoded;
        private final String instance;
        private final Set<String> exactInputPorts;
        private final Set<String> bindingIds;

        private SelectedOccurrence(JsonObject encoded, String instance,
                                   Set<String> inputPorts,
                                   Set<String> bindingIds) {
            this.encoded = encoded.deepCopy();
            this.instance = instance;
            this.exactInputPorts = inputPorts;
            this.bindingIds = bindingIds;
        }

        private static SelectedOccurrence decode(
                JsonObject encoded, String region, String expectedInstance,
                String source) throws IOException {
            String instance = string(encoded, "occurrenceId");
            if (!expectedInstance.equals(instance)) {
                throw new IOException(source + " has inconsistent selected "
                        + "target occurrence identity");
            }
            Set<String> inputPorts = new LinkedHashSet<>();
            for (JsonElement element : array(encoded, "inputPorts")) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isString()) {
                    throw new IOException(source + " has malformed inputPorts");
                }
                String port = element.getAsString().trim();
                // Two exact port id forms reach this decoder, and both are
                // minted rather than resembled.  A region port is
                // `<regionId>.in.<uuid>`.  A fragment behind a communication
                // cut takes its input through the cut's declared port, which
                // is named after the exchange *site* and carries no region id
                // at all -- README section 3's `Req_in` is exactly that -- so
                // the region test says nothing about it and the contract that
                // mints it is asked instead.  A canonical template port is
                // still neither, which is what this refuses.
                if (port.isEmpty()
                        || !(port.startsWith(region + ".in.")
                        || CommunicationCatalogContract.declaredPortId(
                        port))) {
                    throw new IOException(source + " names target input port "
                            + port + ", which is neither an input of region "
                            + region + " nor a declared cut port");
                }
                if (!inputPorts.add(port)) {
                    throw new IOException(source
                            + " has ambiguous target inputPorts");
                }
            }
            Set<String> bindingIds = new LinkedHashSet<>();
            for (JsonElement element : array(encoded, "bindingIds")) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isString()) {
                    throw new IOException(source
                            + " has malformed binding ledger");
                }
                String id = element.getAsString().trim();
                if (id.isEmpty() || !bindingIds.add(id)) {
                    throw new IOException(source
                            + " has ambiguous binding ledger");
                }
            }
            return new SelectedOccurrence(encoded, instance,
                    inputPorts, bindingIds);
        }

        private void requireExactDemandLedger(JsonObject summary)
                throws IOException {
            Set<String> exactInputs = exactInputPorts;
            Set<String> demanded = new LinkedHashSet<>();
            for (JsonElement element : array(summary, "edgeBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (!instance.equals(string(binding,
                        "toOccurrenceId")) || !exactInputs.contains(
                        string(binding, "toInputPort"))) {
                    continue;
                }
                String id = string(binding, "edgeId");
                if (id.isEmpty()) {
                    throw new IOException("selected target demand binding "
                            + "has no edgeId");
                }
                demanded.add(id);
            }
            if (!bindingIds.equals(demanded)) {
                throw new IOException("selected target demand ledger does "
                        + "not exactly cover mapped input ports");
            }
        }

        private void requireExactContext(JsonObject context)
                throws IOException {
            if (!instance.equals(string(context, "occurrenceId"))) {
                throw new IOException("selected target symbolic context has "
                        + "the wrong occurrence identity");
            }
        }

        private JsonArray exactBindings(
                Map<String, JsonObject> runtimeBindings) throws IOException {
            List<String> ids = new ArrayList<>(bindingIds);
            Collections.sort(ids);
            JsonArray result = new JsonArray();
            for (String id : ids) {
                JsonObject binding = runtimeBindings.get(id);
                if (binding == null) {
                    throw new IOException("selected target demand binding "
                            + id + " has no runtime evidence");
                }
                result.add(binding.deepCopy());
            }
            return result;
        }

    }

    static final class Arguments {
        private final Path summaries;
        private final Path pathManifest;
        private final Path seedQuery;
        private final String targetInstance;
        private final Path output;

        private Arguments(Path summaries, Path pathManifest,
                          Path seedQuery, String targetInstance,
                          Path output) {
            this.summaries = summaries;
            this.pathManifest = pathManifest;
            this.seedQuery = seedQuery;
            this.targetInstance = targetInstance;
            this.output = output;
        }

        static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; index < argv.length; index++) {
                String option = argv[index];
                if (!option.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --name value, got " + option);
                }
                values.put(option.substring(2), argv[++index]);
            }
            return new Arguments(requiredPath(values, "summaries"),
                    requiredPath(values, "path-manifest"),
                    requiredPath(values, "seed-query"),
                    optional(values, "target-instance"),
                    requiredPath(values, "output"));
        }

        private static Path requiredPath(Map<String, String> values,
                                         String name) {
            return Paths.get(required(values, name));
        }

        private static String required(Map<String, String> values,
                                       String name) {
            String value = values.get(name);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + name);
            }
            return value.trim();
        }

        private static String optional(Map<String, String> values,
                                       String name) {
            String value = values.get(name);
            return value == null ? "" : value.trim();
        }
    }
}
