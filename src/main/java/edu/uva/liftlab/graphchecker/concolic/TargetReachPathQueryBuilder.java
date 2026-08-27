package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
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
import java.util.IdentityHashMap;
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

public final class TargetReachPathQueryBuilder {
    public static final int SCHEMA_VERSION = 2;
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
    static final String TARGET_BRANCH_WITNESS =
            "targetBranchWitness";
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
        // One decode per summary for the whole build: each one runs
        // Scope.decode, the loop-bound authority and the relation-path
        // fixpoint, and the three passes below read the same rows.  Filled
        // on first use, so a malformed row is still refused by the pass that
        // first looks at it.
        Map<JsonObject, PathObservation> observations =
                new IdentityHashMap<>();
        TargetDecision progressed = progressedTargetDecision(seed,
                summaries, observations, region, occurrenceId, goalId,
                targetSite);
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
        Map<String, JsonObject> symbolicSources = new LinkedHashMap<>();
        // C2 coverage, unioned by symbol: the composer reads this ledger off
        // the fatal query and off every fatal path it kept.
        Map<String, JsonObject> freeSymbols = new LinkedHashMap<>();
        // One exact required-outcome execution is already an existential
        JsonObject directWitness = directRequiredWitness(summaries,
                observations, region, occurrenceId, goalId, targetSite,
                targetOccurrence, fatalRequiredOutcome);
        for (JsonObject summary : summaries) {
            if (directWitness != null && summary != directWitness) continue;
            if (!inScope(summary, region, occurrenceId, goalId)) continue;
            selected.requireExactDemandLedger(summary);
            // Parsing is the schema/admission boundary for branch-owned
            // predicates. The importer already normalized the PC; this check
            PathObservation observation = observed(observations, summary);
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
                    ? witnessedTargetConstraints(summary, observation,
                    targetMapping)
                    : flippedTargetConstraints(summary, observation,
                    targetMapping);
            path.addProperty("fatalBranchConditionAuthority",
                    requiredAttested
                            ? REQUIRED_FATAL_BRANCH_AUTHORITY
                            : SOURCE_FATAL_BRANCH_AUTHORITY);
            path.addProperty(TARGET_ATTESTATION_ROLE,
                    requiredAttested ? REQUIRED_TARGET_REACH_EVENT
                            : SOURCE_TARGET_REACH_EVENT);
            path.add(PathObservation.TargetReachEvent.FIELD,
                    targetReach.toJson());
            // The producer cases selected for this fresh replay may attach a
            path.add(TARGET_BRANCH_WITNESS,
                    targetMapping.witness().toJson());
            path.addProperty("desiredTakenOutcome",
                    fatalRequiredOutcome);
            // The attached expression belongs to this exact target replay.
            // Hoisting it to the query root lets another target-prefix case
            VmHandoffEvidence.writeTo(path,
                    VmHandoffEvidence.eventsOf(summary));
            JsonArray pathFreeSymbols = new JsonArray();
            for (JsonObject row
                    : SymbolicSourceEvidence.freeSymbolsOf(summary)) {
                freeSymbols.putIfAbsent(string(row, "symbol"), row);
                pathFreeSymbols.add(row);
            }
            path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                    pathFreeSymbols);
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
            // PathObservation's key intentionally describes only the local
            String caseKey = pathKey + "\u0000"
                    + CanonicalJson.sha256(path);
            pathsByKey.putIfAbsent(caseKey, path);
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
        result.addProperty("schemaVersion", SCHEMA_VERSION);
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
        JsonArray queryFreeSymbols = new JsonArray();
        for (JsonObject row : freeSymbols.values()) queryFreeSymbols.add(row);
        result.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                queryFreeSymbols);
        // Named, never silent: an edge dropped from refinement is coverage
        // the query does not carry, and the composer folds these rows into
        for (Map.Entry<String, String> entry
                : contestedBindings.entrySet()) {
            coverageGaps.add(CoverageDivergence.of(
                    CoverageDivergence.Kind.FLOW,
                    "TARGET_PATH_BINDING_NOT_USABLE", entry.getKey(),
                    "target paths describe this edge differently, so it"
                            + " does not refine its seed binding: "
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
     */
    private static TargetDecision progressedTargetDecision(
            JsonObject seed, List<JsonObject> summaries,
            Map<JsonObject, PathObservation> observations,
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
            if (!inScope(summary, region, occurrenceId, goalId)) continue;
            PathObservation observation = observed(observations, summary);
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

    /** The outcome a branch row states reaches the failure, or null when it
     * states none.  The single copy: the worklist and the discovery pass read
     * this one. */
    static Boolean requiredOutcome(JsonObject branch) {
        JsonElement encoded = branch == null
                ? null : branch.get("requiredOutcome");
        return encoded != null && encoded.isJsonPrimitive()
                && encoded.getAsJsonPrimitive().isBoolean()
                ? encoded.getAsBoolean() : null;
    }

    /** The failure identities one branch row guards.  The single copy: the
     * worklist reads this one. */
    static Set<String> guardedTargetIdentities(JsonObject branch) {
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
            List<JsonObject> summaries,
            Map<JsonObject, PathObservation> observations,
            String region, String occurrenceId,
            String goalId, String targetSite, int targetOccurrence,
            boolean requiredOutcome) throws IOException {
        JsonObject selected = null;
        String selectedKey = null;
        for (JsonObject summary : summaries) {
            if (!inScope(summary, region, occurrenceId, goalId)) continue;
            PathObservation observation = observed(observations, summary);
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
     * query at all.  README: observed cases are an existential
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
     * session-local location name is dropped, and the canonical name is read
     * at its planned address, so that the two activation-local spellings of
     * one location are the one member.  Every other member is compared
     * exactly as recorded: a binding that disagrees on anything else is still
     * contested.
     */
    private static JsonObject comparable(JsonObject binding) {
        String location = string(binding, LOCATION_FIELD);
        String planned = plannedLocationKey(location);
        boolean session =
                binding.has(SharedStateEvidence.SESSION_LOCATION_FIELD);
        if (!session && planned.equals(location)) {
            return binding;
        }
        JsonObject copy = binding.deepCopy();
        copy.remove(SharedStateEvidence.SESSION_LOCATION_FIELD);
        if (!planned.equals(location)) {
            copy.addProperty(LOCATION_FIELD, planned);
        }
        return copy;
    }

    /** The member naming the shared location one binding read from. */
    private static final String LOCATION_FIELD = "locationKey";

    /**
     * OCC-1: one canonical location name read at its planned address.
     *
     * <p>{@link SharedStateEvidence#canonicalLocationKey} names a location
     * {@code <kind>/<occurrenceId>@receiver:<id>@<field>#<slot>}, and the
     * occurrence it embeds is the per-activation name
     * {@code <plannedAddress>#a<ordinal>}.  One task activated many times in
     * an iteration therefore records the same location under one name per
     * activation -- the VM's own session-local name for all of them is a
     * single string -- while the reach query is stated over the planned
     * address, exactly as {@code inScope} matches summaries.  Only the
     * occurrence segment is re-read, and only by
     * {@link PathObservation#plannedOccurrenceOf}: the receiver, the field
     * and the slot are left as recorded, so two genuinely different
     * locations still disagree.  A name this rule cannot read -- any key
     * that is not a canonical location -- is returned unchanged.</p>
     */
    private static String plannedLocationKey(String locationKey) {
        int kind = locationKey.indexOf('/');
        if (kind <= 0) return locationKey;
        int receiver = locationKey.indexOf('@', kind + 1);
        if (receiver <= kind + 1) return locationKey;
        String occurrence = PathObservation.plannedOccurrenceOf(
                locationKey.substring(kind + 1, receiver));
        return locationKey.substring(0, kind + 1) + occurrence
                + locationKey.substring(receiver);
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

    /** A complete recorded case of the closed scope this query is stated
     *  over; every pass below asks the same question of the same rows. */
    private static boolean inScope(JsonObject summary, String region,
                                   String occurrenceId, String goalId) {
        // OCC-1: the reach query is keyed on the planned target address; the
        // summaries are one per activation, named <address>#a<ordinal>.  A
        // summary is in scope when it is an activation of that address, so
        // the direct-throw witness and its non-failing siblings are all seen
        // and the failure occurrence is selected among them by
        // directRequiredWitness.
        return region.equals(string(summary, "regionId"))
                && occurrenceId.equals(PathObservation.plannedOccurrenceOf(
                        string(summary, "occurrenceId")))
                && goalId.equals(string(summary, "goalId"))
                && ClosureGoalKind.fromTask(summary).capturesTargetReach()
                && bool(summary, "relationallyComplete", false);
    }

    /** This build's one decode of {@code summary}. */
    private static PathObservation observed(
            Map<JsonObject, PathObservation> observations,
            JsonObject summary) {
        PathObservation decoded = observations.get(summary);
        if (decoded == null) {
            decoded = PathObservation.decode(summary, null);
            observations.put(summary, decoded);
        }
        return decoded;
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
     */
    private static JsonArray flippedTargetConstraints(
            JsonObject summary, PathObservation observation,
            SummaryBranchMapping target) {
        JsonArray result = slicedTargetPrefix(summary, observation, target);
        result.add(BranchPredicateAlgebra.complement(
                target.witness().sourceSatisfiedPredicate()));
        return result;
    }

    /** Keeps the sliced prefix through an already-required target event. */
    private static JsonArray witnessedTargetConstraints(
            JsonObject summary, PathObservation observation,
            SummaryBranchMapping target) {
        JsonArray result = slicedTargetPrefix(summary, observation, target);
        result.add(array(summary, "pathCondition")
                .get(target.summaryPcIndex()).deepCopy());
        return result;
    }

    /**
     * <p>README PC-1: a case guard carries the decisions that are relevant
     */
    private static JsonArray slicedTargetPrefix(
            JsonObject summary, PathObservation observation,
            SummaryBranchMapping target) {
        JsonArray recorded = array(summary, "pathCondition");
        int targetPosition = target.summaryPcIndex();
        if (!target.isWitnessed() || targetPosition < 0
                || targetPosition >= recorded.size()) {
            throw new IllegalArgumentException(
                    "target witness is outside the recorded path");
        }
        JsonArray projected = observation.relationPathCondition();
        List<Integer> positions =
                observation.relationPathConditionPositions();
        JsonArray prefix = new JsonArray();
        for (int index = 0; index < positions.size(); index++) {
            if (positions.get(index) < targetPosition) {
                prefix.add(projected.get(index));
            }
        }
        return prefix;
    }

    /**
     * The activation the seed query selected.
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
                // at all -- README section 3's `Req_in` is exactly that -- so
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

        /**
         * Whether one binding row feeds a mapped input port of this exact
         * selected occurrence.  The two passes below read demand the same
         * way, so a row can never be ledger demand for one and not for the
         * other.
         */
        private boolean demandsMappedInput(JsonObject binding) {
            return instance.equals(string(binding, "toOccurrenceId"))
                    && exactInputPorts.contains(
                            string(binding, "toInputPort"));
        }

        private void requireExactDemandLedger(JsonObject summary)
                throws IOException {
            Set<String> demanded = new LinkedHashSet<>();
            for (JsonElement element : array(summary, "edgeBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (!demandsMappedInput(binding)) continue;
                String id = string(binding, "edgeId");
                if (id.isEmpty()) {
                    throw new IOException("selected target demand binding "
                            + "has no edgeId");
                }
                // An exchange pairing a replay recorded and the scheduler
                // absorbed is, by construction, one this ledger does not
                // hold: the ledger is the demand the baseline discovery
                // saw, and the absorbed pairing is what it did not.  Its
                // authority is the VM's own send and receive events, named
                // on the row, so it is no ledger demand here -- and nothing
                // else is: a row without that stamp still has to be in the
                // ledger, so a plan that grew a binding on its own is still
                // caught.  Exempt is not dropped: exactBindings below
                // publishes the same row, so the pairing still reaches
                // composition.
                if (VmHandoffEvidence.absorbed(binding)) continue;
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
            Set<String> demanded = new LinkedHashSet<>(bindingIds);
            // The pairings the ledger could not name are demand on these
            // same mapped input ports.  Dropping them would hand
            // composition the producer the frozen plan guessed while the
            // recorded handoff names another, so the fully stamped rows an
            // attested target path carried are published beside the ledger's
            // own -- and only those: an unstamped row is never here, because
            // the ledger check above would already have refused it.
            for (Map.Entry<String, JsonObject> entry
                    : runtimeBindings.entrySet()) {
                if (VmHandoffEvidence.absorbed(entry.getValue())
                        && demandsMappedInput(entry.getValue())) {
                    demanded.add(entry.getKey());
                }
            }
            List<String> ids = new ArrayList<>(demanded);
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
