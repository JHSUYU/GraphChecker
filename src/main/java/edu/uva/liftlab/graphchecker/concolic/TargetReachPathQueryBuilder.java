package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.TargetAnchorEvidence;

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
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

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
    static final String REQUIRED_CONCRETE_BRANCH_AUTHORITY =
            "RUNTIME_REQUIRED_CONCRETE_TARGET_EVENT_V1";
    static final String TARGET_BRANCH_WITNESS =
            "targetBranchWitness";
    static final String TARGET_CONCRETE_OBSERVATION =
            "targetConcreteObservation";
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
        SharedExpressionTable.Decoder expressions =
                new SharedExpressionTable.Decoder();
        JsonObject manifest = ArtifactIO.readObject(arguments.pathManifest);
        validatePathManifest(manifest);
        if (!ClosureGoalKind.TARGET_REACH_CLOSURE.name().equals(
                optionalString(manifest, ClosureGoalKind.TASK_FIELD))) {
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
                String kind = optionalString(raw, "kind");
                if (isTargetPathCoverageGap(kind)) {
                    coverageGaps.add(CoverageDivergence.of(
                            CoverageDivergence.Kind.TARGET, kind,
                            optionalString(raw, "queryKey"),
                            optionalString(raw, "reason")));
                } else {
                    coverageGaps.add(raw.deepCopy());
                }
            }
        }
        String worklistState = optionalString(manifest, "state");
        String coverageState = optionalString(manifest, "coverageState");
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
                    optionalString(manifest, "occurrenceId"),
                    "state=" + worklistState + ", coverageState="
                            + firstNonBlank(coverageState, "UNSTATED")
                            + ", gaps="
                            + worklistGapReasons(worklistGaps)));
        }

        List<JsonObject> seeds;
        try {
            seeds = expressions.expandAll(ArtifactIO.readJsonl(
                    arguments.seedQuery,
                    "Malformed target seed query %1$s:%2$d",
                    "Non-object target seed query %1$s:%2$d"));
        } catch (IllegalArgumentException malformed) {
            throw new IOException("Malformed target seed expression table",
                    malformed);
        }
        List<JsonObject> ready = solverReadySeedsForScope(seeds, manifest);
        JsonObject seed = decidingSeed(ready);
        // An anchor is an address, and the evidence for it is every replay
        // of the campaign that reached it.  A solver-ready seed query is one
        // way to name the anchor, not a precondition for having one: the
        // scheduler publishes it only for a decision it could make
        // solver-ready, and on bug3 it published none at all while nine
        // replays published targetReach at the anchor.  Refusing there threw
        // away the whole disjunction because one optional row was missing.
        // With no seed the address is the worklist's own, which the campaign
        // planned, and the site is the one every reached replay names.
        boolean seedless = seed == null;
        if (seedless) {
            seed = anchorFromWorklist(manifest);
        }
        String queryKey = optionalString(seed, "queryKey");
        if (queryKey.isEmpty()) {
            throw new IOException(
                    "target seed query has no stable queryKey");
        }
        String region = optionalString(seed, "regionId");
        String occurrenceId = optionalString(seed, "occurrenceId");
        String goalId = optionalString(seed, "goalId");
        String targetSite = optionalString(seed, "targetSiteId");
        if (!region.equals(optionalString(manifest, "regionId"))
                || !goalId.equals(optionalString(manifest, "goalId"))
                || !occurrenceId.equals(optionalString(manifest, "occurrenceId"))
                || region.isEmpty() || occurrenceId.isEmpty()
                || goalId.isEmpty()
                || !seedless && targetSite.isEmpty()) {
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
        SelectedOccurrence selected = seedless ? null
                : SelectedOccurrence.decode(
                        object(seed, "selectedTargetOccurrence"), region,
                        occurrenceId, "target seed query");
        BranchReplayContract targetReplay = null;
        ExactConcreteBranchObservation targetConcrete = null;
        JsonElement encodedConcrete = seed.get(TARGET_CONCRETE_OBSERVATION);
        boolean hasConcrete = encodedConcrete != null
                && !encodedConcrete.isJsonNull();
        boolean hasReplay = seed.has("replayContract")
                && !seed.get("replayContract").isJsonNull();
        if (!seedless && hasConcrete == hasReplay) {
            throw new IOException("target seed must have exactly one branch "
                    + "authority");
        }
        int targetOccurrence = optionalInteger(seed,
                "targetOccurrence", 1);
        if (hasConcrete) {
            if (!encodedConcrete.isJsonObject()) {
                throw new IOException(
                        "malformed concrete target observation");
            }
            try {
                targetConcrete = ExactConcreteBranchObservation.fromJson(
                        encodedConcrete.getAsJsonObject());
            } catch (IllegalArgumentException malformed) {
                throw new IOException(
                        "malformed concrete target observation", malformed);
            }
            if (!targetSite.equals(targetConcrete.siteId())) {
                throw new IOException("concrete target observation does not "
                        + "match target site");
            }
            if (targetConcrete.isMultiwaySwitch()) {
                throw new IOException("multiway concrete target requires an "
                        + "exact successor; fatal target policy states only "
                        + "a Boolean outcome");
            }
            targetOccurrence = targetConcrete.occurrence();
        } else if (!seedless) {
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
            targetOccurrence = targetReplay.source().occurrence();
        }
        JsonElement fatalOutcome = seed.get("fatalRequiredTakenOutcome");
        if (!seedless && (fatalOutcome == null
                || !fatalOutcome.isJsonPrimitive()
                || !fatalOutcome.getAsJsonPrimitive().isBoolean())) {
            throw new IOException(
                    "target seed query has no fatal branch outcome");
        }
        // The composer records this and gates nothing on it: every replay
        // that reached the anchor contributes its own phi, whichever arm it
        // decided.
        boolean fatalRequiredOutcome = fatalOutcome != null
                && fatalOutcome.isJsonPrimitive()
                && fatalOutcome.getAsJsonPrimitive().isBoolean()
                && fatalOutcome.getAsBoolean();
        if (targetConcrete != null) {
            if (fatalRequiredOutcome
                    != targetConcrete.sourceTakenOutcome()) {
                throw new IOException("concrete target observation did not "
                        + "take the required outcome");
            }
        }

        List<JsonObject> summaries;
        try {
            summaries = expressions.expandAll(
                    ArtifactIO.readJsonl(arguments.summaries,
                            "Malformed target summary %1$s:%2$d",
                            "Non-object target summary %1$s:%2$d"));
        } catch (IllegalArgumentException malformed) {
            throw new IOException("Malformed target expression table",
                    malformed);
        }
        // One decode per summary for the whole build: each one runs
        // Scope.decode, the loop-bound authority and the relation-path
        // fixpoint, and the three passes below read the same rows.  Filled
        // on first use, so a malformed row is still refused by the pass that
        // first looks at it.
        Map<JsonObject, PathObservation> observations =
                new IdentityHashMap<>();
        if (targetReplay != null) {
            TargetDecision progressed = progressedTargetDecision(seed,
                    summaries, observations, region, occurrenceId, goalId,
                    targetSite);
            if (progressed != null) {
                targetSite = progressed.siteId;
                targetOccurrence = progressed.occurrence;
                fatalRequiredOutcome = progressed.requiredOutcome;
                targetReplay = progressed.replayContract;
            }
        }

        if (seedless) {
            // The site is the one every replay that reached this address
            // names in its own targetReach event.  Two that disagree state
            // no anchor, which is a refusal rather than a choice.
            for (JsonObject summary : summaries) {
                if (!inScope(summary, region, occurrenceId, goalId)) continue;
                JsonObject reach = object(summary, "targetReach");
                String site = optionalString(reach, "siteId");
                if (site.isEmpty()) continue;
                if (targetSite.isEmpty()) {
                    targetSite = site;
                    targetOccurrence = optionalInteger(reach,
                            "occurrence", 1);
                } else if (!targetSite.equals(site)) {
                    throw new IOException("replays that reached "
                            + occurrenceId + " name two anchored sites: "
                            + targetSite + " and " + site);
                }
            }
            if (targetSite.isEmpty()) {
                throw new IOException("no replay published a target reach "
                        + "at " + occurrenceId);
            }
        }

        Map<String, JsonObject> pathsByKey = new LinkedHashMap<>();
        Map<String, JsonObject> symbolicSources = new LinkedHashMap<>();
        // Every activation that executed the anchored site is a disjunct of
        // Fatal_T.  One of them taking the failing edge used to end the
        // search here -- an execution that reached the failure was read as
        // the whole existential answer -- and the query then held that one
        // path.  But a disjunction over one path says nothing about which
        // root valuation reaches the failure: the activations that decided
        // against it, with their own values, are what make the answer
        // depend on the root at all.
        for (JsonObject summary : summaries) {
            if (!inScope(summary, region, occurrenceId, goalId)) continue;
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
            // Which decision this activation made at the anchor is not an
            // admission test either.  It used to be: a summary was admitted
            // only if its target decision was the *same decision* as the
            // elected seed's -- the same concrete observation, or the same
            // witness identity.  Two replays of one anchor legitimately
            // decide it differently, and that is the whole evidence: on
            // laneVM10 the seed decided u8#1 true and the flip replay
            // TASK.REPLAY.7f26859ea2 decided it false and threw
            // InvalidEncryptionKeyException.  Requiring sameness dropped the
            // half that carries the claim.  What is required is that this
            // activation executed the anchored site and published its
            // targetReach, which is checked below.
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
            boolean requiredAttested = fatalRequiredOutcome
                    == targetMapping.sourceTakenOutcome();
            // Which outcome this activation decided is not an admission
            // test.  It used to be: a path was admitted only if its target
            // decision agreed with the elected source's or with the one the
            // failure needs, which on a healthy recording drops whichever of
            // the two families the elected source is not -- and the merge
            // wants both.  The activation that decided against the failure
            // contributes the disjunct its own values make false; the one
            // that decided for it contributes the disjunct that carries the
            // claim.  What is required is that this activation executed the
            // anchored site and said so, which is checked above.
            // No side evidence from an unattested target path enters the
            // query either. Shared state and consumer-boundary references
            JsonObject shared = object(summary,
                    SharedStateEvidence.RECORDED_FIELD);
            for (JsonObject source
                    : SymbolicSourceEvidence.eventsOf(summary)) {
                String identity = SymbolicSourceEvidence.identity(source);
                JsonObject prior = symbolicSources.putIfAbsent(identity,
                        source);
                if (prior != null && !prior.equals(source)) {
                    throw new IOException("target paths disagree on exact "
                            + "configured source phase " + identity);
                }
            }

            JsonObject path = new JsonObject();
            for (String metadata : new String[]{"taskId", "sourceTaskId",
                    "boundarySessionScope", "replayGroupId",
                    "topologyEpoch"}) {
                if (summary.has(metadata)) {
                    path.add(metadata, summary.get(metadata).deepCopy());
                }
            }
            path.addProperty(LocalCaseIdentity.FIELD,
                    observation.pathKey());
            path.addProperty("caseId", observation.pathKey());
            path.addProperty("occurrenceId",
                    observation.occurrenceId());
            // The worklist is keyed by the planned occurrence while this
            // path is keyed by one physical activation of it.  Carry the
            // closure verdict across that boundary with the same OCC-1
            // canonicalization used for scope admission; otherwise a closed
            // target occurrence such as "...#2" becomes an unclosed case
            // merely because its attested path is named "...#2#a1".
            path.addProperty("pathSetClosed",
                    closedPathSetApplies(manifest, summary));
            if (shared.size() > 0) {
                path.add(SharedStateEvidence.RECORDED_FIELD,
                        shared);
            }
            JsonArray constraints = targetMapping.isConcreteObservation()
                    ? observation.pathCondition()
                    : requiredAttested
                    ? witnessedTargetConstraints(summary, observation,
                    targetMapping)
                    : flippedTargetConstraints(summary, observation,
                    targetMapping);
            path.addProperty("fatalBranchConditionAuthority",
                    targetMapping.isConcreteObservation()
                            ? REQUIRED_CONCRETE_BRANCH_AUTHORITY
                            : requiredAttested
                            ? REQUIRED_FATAL_BRANCH_AUTHORITY
                            : SOURCE_FATAL_BRANCH_AUTHORITY);
            path.addProperty(TARGET_ATTESTATION_ROLE,
                    requiredAttested ? REQUIRED_TARGET_REACH_EVENT
                            : SOURCE_TARGET_REACH_EVENT);
            path.add(PathObservation.TargetReachEvent.FIELD,
                    targetReach.toJson());
            // The producer cases selected for this fresh replay may attach a
            if (targetMapping.isConcreteObservation()) {
                path.add(TARGET_CONCRETE_OBSERVATION,
                        targetMapping.concreteObservation().toJson());
            } else {
                path.add(TARGET_BRANCH_WITNESS,
                        targetMapping.witness().toImmutableJsonView());
            }
            path.addProperty("desiredTakenOutcome",
                    fatalRequiredOutcome);
            // The attached expression belongs to this exact target replay.
            // Hoisting it to the query root lets another target-prefix case
            if (selected == null) {
                // Nothing narrows the handoff rows: the family join keys on
                // the recorded handoff occurrence, not on a port allowlist.
                VmHandoffEvidence.writeTo(path,
                        VmHandoffEvidence.eventsOf(summary));
            } else if (!selected.writeConsumerBoundaryEvidence(path, summary,
                    coverageGaps)) {
                continue;
            }
            JsonArray loopCounts = observation.pathLoopCounts();
            if (loopCounts.size() > 0) {
                path.add(LoopBoundPolicy.PATH_LOOP_COUNTS, loopCounts);
            }
            JsonArray loopCountGaps = observation.pathLoopCountGaps();
            if (loopCountGaps.size() > 0) {
                path.add(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS,
                        loopCountGaps);
            }
            // One path is one replay's traversal of this region-local case.
            // Keying by the case alone kept the first replay to reach it and
            // dropped every other replay's values for the same shape, which
            // is precisely the set the disjunction is over.
            String pathKey = observation.pathKey() + "\u0000"
                    + optionalString(summary, "replayGroupId");
            path.add("constraints", constraints);
            path.add(TargetAnchorEvidence.FIELD, anchorEvidence(
                    summary, observation, targetMapping, constraints,
                    fatalRequiredOutcome));
            // Closure already rejects two observations of one local case
            // when their rewritten consumer payloads disagree.  Runtime
            // metadata must therefore not duplicate the same target case.
            pathsByKey.putIfAbsent(pathKey, path);
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
        if (!optionalString(seed, "sourceKey").isEmpty()) {
            result.addProperty("sourceKey", optionalString(seed, "sourceKey"));
        }
        result.addProperty("targetSiteId", targetSite);
        result.addProperty("targetOccurrence", targetOccurrence);
        result.addProperty("requiredTakenOutcome", fatalRequiredOutcome);
        result.add("paths", encodedPaths);
        if (targetConcrete != null) {
            result.add(TARGET_CONCRETE_OBSERVATION,
                    targetConcrete.toJson());
        } else if (targetReplay != null) {
            result.add("seedReplayContract",
                    targetReplay.toImmutableJsonView());
        }
        seedLoopBound.writeTo(result);
        if (selected != null) {
            JsonObject symbolicContext =
                    object(seed, "symbolicContext").deepCopy();
            selected.requireExactContext(symbolicContext);
            result.add("symbolicContext", symbolicContext);
            result.add("selectedTargetOccurrence",
                    selected.encoded.deepCopy());
        }
        SymbolicSourceEvidence.writeTo(result,
                new ArrayList<>(symbolicSources.values()));
        if (!coverageGaps.isEmpty()) {
            JsonArray gaps = new JsonArray();
            for (JsonObject row : coverageGaps) gaps.add(row);
            result.add("coverageGaps", gaps);
        }
        return expressions.compact(result);
    }

    private static boolean isTargetPathCoverageGap(String kind) {
        return kind.startsWith("PATH_FLIP_")
                || "UNSUPPORTED_PATH_FLIP".equals(kind)
                || "BOUND_REACHED".equals(kind);
    }

    /**
     * The anchor a closed worklist names, as a seed the rest can read.
     *
     * <p>Region, planned occurrence and goal are the address the campaign
     * planned; the site is the one the summaries that reached it name; the
     * loop authority is the worklist's own.  Nothing here is inferred from a
     * graph -- every member is copied from the artifact that owns it.</p>
     */
    private static JsonObject anchorFromWorklist(JsonObject manifest) {
        JsonObject anchor = new JsonObject();
        String region = optionalString(manifest, "regionId");
        String occurrence = optionalString(manifest, "occurrenceId");
        String goal = optionalString(manifest, "goalId");
        anchor.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        anchor.addProperty("queryKey", CanonicalJson.sha256(
                region + "\n" + occurrence + "\n" + goal));
        anchor.addProperty("regionId", region);
        anchor.addProperty("occurrenceId", occurrence);
        anchor.addProperty("goalId", goal);
        anchor.addProperty("targetSiteId",
                optionalString(manifest, "targetSiteId"));
        JsonElement loopBound = manifest.get(LoopBoundPolicy.FIELD);
        if (loopBound != null) anchor.add(LoopBoundPolicy.FIELD, loopBound);
        return anchor;
    }

    private static void validatePathManifest(JsonObject manifest)
            throws IOException {
        if (JsonFields.optionalInteger(manifest, "schemaVersion", -1) != 1
                || !"REGION_PATH_WORKLIST".equals(optionalString(manifest, "kind"))) {
            throw new IOException("target path worklist schema is invalid");
        }
        String state = optionalString(manifest, "state");
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
        String coverage = optionalString(manifest, "coverageState");
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
            if (!optionalBool(candidate, "failureTarget", false)
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
            if (mapping == null || !mapping.isWitnessed()
                    || !reach.matches(mapping.siteId(),
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
            if (!siteId.equals(optionalString(catalog.get(index), "siteId"))) {
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
            String site = optionalString(element.getAsJsonObject(), "siteId");
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


    /** Solver-ready candidates for this exact target worklist. Multiplicity is
     * preserved so decidingSeed still rejects a true in-scope ambiguity. */
    static List<JsonObject> solverReadySeedsForScope(
            List<JsonObject> seeds, JsonObject manifest) {
        List<JsonObject> ready = new ArrayList<>();
        String region = optionalString(manifest, "regionId");
        String occurrence = optionalString(manifest, "occurrenceId");
        String goal = optionalString(manifest, "goalId");
        for (JsonObject row : seeds) {
            if ("TARGET_BRANCH_SOLVER_QUERY".equals(optionalString(row, "kind"))
                    && optionalBool(row, "readyForSolver", false)
                    && region.equals(optionalString(row, "regionId"))
                    && occurrence.equals(optionalString(row, "occurrenceId"))
                    && goal.equals(optionalString(row, "goalId"))) {
                ready.add(row);
            }
        }
        return ready;
    }

    /** The one seed query that decides the target, or null when none does. */
    private static JsonObject decidingSeed(List<JsonObject> ready) {
        if (ready.size() == 1) return ready.get(0);
        JsonObject direct = null;
        for (JsonObject candidate : ready) {
            if (!candidate.has(TARGET_CONCRETE_OBSERVATION)) continue;
            if (direct != null) return null;
            direct = candidate;
        }
        if (direct != null) return direct;
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

    /** The worklist's own gap reasons, so the partial region names itself. */
    private static String worklistGapReasons(JsonArray gaps) {
        List<String> reasons = new ArrayList<>();
        for (JsonElement element : gaps) {
            if (element.isJsonObject()) {
                JsonObject row = element.getAsJsonObject();
                String reason = optionalString(row, "reason");
                reasons.add(reason.isEmpty()
                        ? optionalString(row, "kind") : reason);
            } else {
                reasons.add(element.toString());
            }
        }
        return reasons.isEmpty() ? "none" : String.join(";", reasons);
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
        return region.equals(optionalString(summary, "regionId"))
                && occurrenceId.equals(OccurrenceId.parse(
                        optionalString(summary, "occurrenceId")).planned())
                && goalId.equals(optionalString(summary, "goalId"))
                && ClosureGoalKind.fromTask(summary).capturesTargetReach();
    }

    /**
     * Whether the planned-occurrence worklist is the complete closure
     * authority for one physical activation summary.
     *
     * <p>Both sides are reduced to their planned occurrence before matching.
     * This is the one identity boundary between a worklist row and the
     * activation-local paths copied into the target query.</p>
     */
    static boolean closedPathSetApplies(JsonObject manifest,
                                        JsonObject summary) {
        if (manifest == null || summary == null
                || !"CLOSED".equals(optionalString(manifest, "state"))
                || !"CLOSED".equals(optionalString(manifest, "coverageState"))
                || array(manifest, "gaps").size() != 0
                || array(manifest, "coverageGaps").size() != 0) {
            return false;
        }
        String manifestSource = optionalString(manifest, "sourceKey");
        String summarySource = optionalString(summary, "sourceKey");
        return optionalString(manifest, "regionId").equals(
                optionalString(summary, "regionId"))
                && optionalString(manifest, "goalId").equals(
                optionalString(summary, "goalId"))
                && (manifestSource.isEmpty()
                || manifestSource.equals(summarySource))
                && OccurrenceId.parse(optionalString(manifest,
                "occurrenceId")).planned().equals(
                OccurrenceId.parse(optionalString(summary,
                        "occurrenceId")).planned());
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

    /** The exact decision of the target site, or null. */
    private static SummaryBranchMapping targetSiteMapping(
            PathObservation observation, String siteId, int occurrence) {
        for (SummaryBranchMapping mapping
                : observation.branchMappings()) {
            if (siteId.equals(mapping.siteId())
                    && occurrence == mapping.occurrence()) {
                return mapping;
            }
        }
        return null;
    }

    /**
     * Projects one attested source path into the requested target flip.
     */
    /**
     * The anchored target row this replay publishes.
     *
     * <p>Everything the path-merge composition reads, stated once and
     * versioned: reaching the target is the site having executed, so a
     * healthy activation publishes the same row and contributes the
     * disjunct its own values make false.  It travels beside the members
     * the old composition reads, which stay until that composition goes.</p>
     */
    private static JsonObject anchorEvidence(
            JsonObject summary, PathObservation observation,
            SummaryBranchMapping target, JsonArray constraints,
            boolean fatalRequiredOutcome) {
        JsonObject selectors = new JsonObject();
        selectors.addProperty(LocalCaseIdentity.FIELD, observation.pathKey());
        selectors.addProperty("desiredTakenOutcome", fatalRequiredOutcome);
        for (String metadata : new String[]{"taskId", "replayGroupId",
                "boundarySessionScope", "topologyEpoch"}) {
            if (summary.has(metadata)) {
                selectors.add(metadata, summary.get(metadata).deepCopy());
            }
        }
        JsonArray mappings = new JsonArray();
        for (SummaryBranchMapping mapping : observation.branchMappings()) {
            if (!mapping.isExplore()) continue;
            JsonObject row = new JsonObject();
            row.addProperty("siteId", mapping.siteId());
            row.addProperty("occurrence", mapping.occurrence());
            row.addProperty("sourceTakenOutcome",
                    mapping.sourceTakenOutcome());
            mappings.add(row);
        }
        selectors.add("exploredBranches", mappings);
        List<JsonObject> roots = new ArrayList<>(
                SymbolicSourceEvidence.eventsOf(summary));
        Set<String> carriers = new LinkedHashSet<>();
        for (JsonElement encoded : array(object(summary,
                SharedStateEvidence.RECORDED_FIELD), "versions")) {
            if (!encoded.isJsonObject()) continue;
            String location = InSessionReadResolver.sessionLocation(
                    object(object(encoded.getAsJsonObject(), "envelope"),
                            "location"));
            if (!location.isEmpty()) carriers.add(location);
        }
        // pi_p is every decision this activation made on the way to the
        // target, not the slice of them the target's operands depend on.
        // The slice is computed over the unresolved dependency graph; once a
        // predicate's operands resolve to the values the replay produced it
        // depends on nothing, and the slice then drops exactly the guards
        // that say which root valuation this execution ran under -- which is
        // the only thing that makes the disjunction a question about roots.
        JsonArray whole = new JsonArray();
        JsonArray recorded = observation.pathCondition();
        for (int index = 0; index < recorded.size(); index++) {
            if (index == target.summaryPcIndex()) continue;
            whole.add(recorded.get(index));
        }
        whole.add(constraints.get(constraints.size() - 1));
        return TargetAnchorEvidence.build(target.siteId(),
                target.occurrence(), optionalString(summary, "sourceKey"),
                optionalString(summary, "regionId"),
                observation.occurrenceId(),
                optionalString(summary, "topologyEpoch"),
                target.sourceTakenOutcome(), fatalRequiredOutcome,
                whole, selectors, roots, carriers);
    }

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
                .get(target.summaryPcIndex()));
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
        JsonArray projected = observation.pathCondition();
        List<Integer> positions =
                observation.pathConditionPositions();
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

        private SelectedOccurrence(JsonObject encoded, String instance,
                                   Set<String> inputPorts) {
            this.encoded = encoded.deepCopy();
            this.instance = instance;
            this.exactInputPorts = inputPorts;
        }

        private static SelectedOccurrence decode(
                JsonObject encoded, String region, String expectedInstance,
                String source) throws IOException {
            String instance = optionalString(encoded, "occurrenceId");
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
            return new SelectedOccurrence(encoded, instance, inputPorts);
        }

        private void requireExactContext(JsonObject context)
                throws IOException {
            if (!instance.equals(optionalString(context, "occurrenceId"))) {
                throw new IOException("selected target symbolic context has "
                        + "the wrong occurrence identity");
            }
        }

        /** Retains the VM's exact consumer receive; graph ports are topology
         * labels only and never rebuild the carried value. */
        private boolean writeConsumerBoundaryEvidence(
                JsonObject path, JsonObject summary,
                List<JsonObject> coverageGaps) {
            List<JsonObject> bound = new ArrayList<>();
            for (JsonObject event : VmHandoffEvidence.eventsOf(summary)) {
                String port = optionalString(event, "portId");
                if (!exactInputPorts.contains(port)) {
                    coverageGaps.add(CoverageDivergence.of(
                            CoverageDivergence.Kind.FLOW,
                            "TARGET_PATH_HANDOFF_ENDPOINT_NOT_SELECTED",
                            instance + ":" + port,
                            "target VM handoff port is not an input of the"
                                    + " selected occurrence"));
                    return false;
                }
                bound.add(event);
            }
            VmHandoffEvidence.writeTo(path, bound);
            return true;
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
            Map<String, String> values = CliArgs.pairs(argv);
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
