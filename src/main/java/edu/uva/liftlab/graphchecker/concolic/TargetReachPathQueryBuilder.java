package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
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
        if (!ClosureGoalKind.TARGET_REACH_CLOSURE.name().equals(
                string(manifest, ClosureGoalKind.TASK_FIELD))) {
            // Not an evidence disagreement: this artifact is not a target
            // reach worklist at all, so there is nothing to merge from it.
            throw new IOException(
                    "target path worklist is not a target reach closure");
        }
        // Named, never silent, but never a reason to publish nothing: a
        // worklist that stopped short or carried gaps is a partial region,
        // and a partial region is what best effort merging produces.  The
        // gate downstream still refuses an incomplete path set.
        List<JsonObject> coverageGaps = new ArrayList<>();
        String worklistState = string(manifest, "state");
        JsonArray worklistGaps = array(manifest, "gaps");
        if (!"CLOSED".equals(worklistState) || worklistGaps.size() != 0) {
            coverageGaps.add(CoverageDivergence.of(
                    CoverageDivergence.Kind.TARGET,
                    "TARGET_WORKLIST_NOT_CLOSED",
                    string(manifest, "occurrenceId"),
                    "state=" + worklistState + ", gaps="
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
        SelectedOccurrence selected = SelectedOccurrence.decode(
                object(seed, "selectedTargetOccurrence"), region,
                occurrenceId, "target seed query");
        final BranchReplayContract targetReplay;
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

        Map<String, JsonObject> pathsByKey = new LinkedHashMap<>();
        Map<String, JsonObject> runtimeBindings = new LinkedHashMap<>();
        // Edges whose runtime evidence two target paths state differently.
        Map<String, String> contestedBindings = new LinkedHashMap<>();
        // Path keys two summaries describe differently.  Neither is kept:
        // picking one would be a semantic choice this class cannot make.
        Map<String, String> conflictingPaths = new LinkedHashMap<>();
        List<JsonObject> recordedSharedState = new ArrayList<>();
        List<JsonObject> vmHandoffEvents = new ArrayList<>();
        List<JsonObject> symbolicSources = new ArrayList<>();
        List<JsonObject> summaries = ArtifactIO.readJsonl(arguments.summaries,
                "Malformed target summary %1$s:%2$d",
                "Non-object target summary %1$s:%2$d");
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
            if (shared.size() > 0) recordedSharedState.add(shared);
            vmHandoffEvents.addAll(VmHandoffEvidence.eventsOf(summary));
            symbolicSources.addAll(SymbolicSourceEvidence.eventsOf(summary));

            JsonObject path = new JsonObject();
            JsonArray constraints = requiredAttested
                    ? witnessedTargetConstraints(summary, targetMapping)
                    : flippedTargetConstraints(summary, targetMapping);
            path.addProperty("fatalBranchConditionAuthority",
                    requiredAttested
                            ? "RUNTIME_REQUIRED_TARGET_EVENT_V1"
                            : "RUNTIME_SOURCE_EVENT_AND_WITNESS_FLIP_V1");
            path.addProperty(TARGET_ATTESTATION_ROLE,
                    requiredAttested ? REQUIRED_TARGET_REACH_EVENT
                            : SOURCE_TARGET_REACH_EVENT);
            path.add(PathObservation.TargetReachEvent.FIELD,
                    targetReach.toJson());
            path.addProperty("desiredTakenOutcome",
                    fatalRequiredOutcome);
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
                    "closed target worklist contains no exact "
                            + "source-attested target path");
        }

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        result.addProperty("regionId", region);
        result.addProperty("occurrenceId", occurrenceId);
        if (!string(seed, "sourceKey").isEmpty()) {
            result.addProperty("sourceKey", string(seed, "sourceKey"));
        }
        result.addProperty("targetSiteId", targetSite);
        result.addProperty("targetOccurrence", targetOccurrence);
        result.addProperty("requiredTakenOutcome", fatalRequiredOutcome);
        result.addProperty("targetExceptionType", arguments.exceptionType);
        result.add("paths", encodedPaths);
        result.add("seedReplayContract",
                object(seed, "replayContract").deepCopy());
        JsonObject symbolicContext =
                object(seed, "symbolicContext").deepCopy();
        refineContextBindings(symbolicContext, runtimeBindings);
        selected.requireExactContext(symbolicContext);
        result.add("symbolicContext", symbolicContext);
        result.add("selectedTargetBindings",
                selected.exactBindings(runtimeBindings));
        JsonObject shared = SharedStateEvidence.mergeRecorded(
                recordedSharedState);
        if (shared.size() > 0) {
            result.add(SharedStateEvidence.RECORDED_FIELD, shared);
        }
        VmHandoffEvidence.writeTo(result, vmHandoffEvents);
        SymbolicSourceEvidence.writeTo(result, symbolicSources);
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

    /** The target replay's VM evidence supersedes the seed trace candidate. */
    /**
     * Collects the runtime binding evidence the target paths agree on.
     *
     * <p>A region is merged best effort: not every path has to be usable, and
     * one edge two paths describe differently is not a reason to publish no
     * query at all.  README: observed cases are an existential
     * under-approximation and the milestone makes no UNSAT-completeness
     * claim, so production is best effort while acceptance stays strict - the
     * contested edge simply does not refine its seed, the query is still
     * built, and the gate still refuses an incomplete path set.</p>
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

    /** Which members two descriptions of one edge disagree on. */
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

    private static void refineContextBindings(
            JsonObject context, Map<String, JsonObject> runtimeBindings)
            throws IOException {
        refineRelations(array(context, "equalityRelations"),
                runtimeBindings);
    }

    private static void refineRelations(
            JsonArray relations, Map<String, JsonObject> runtimeBindings)
            throws IOException {
        for (JsonElement element : relations) {
            if (!element.isJsonObject()) continue;
            JsonArray selected = array(element.getAsJsonObject(),
                    "selectedBindings");
            for (int index = 0; index < selected.size(); index++) {
                if (!selected.get(index).isJsonObject()) continue;
                JsonObject seed = selected.get(index).getAsJsonObject();
                JsonObject runtime = runtimeBindings.get(string(seed,
                        "edgeId"));
                if (runtime == null) continue;
                for (String identity : new String[]{"edgeId",
                        "fromOccurrenceId", "toOccurrenceId",
                        "fromOutputPort", "toInputPort"}) {
                    if (!string(seed, identity).equals(string(runtime,
                            identity))) {
                        throw new IOException("runtime binding changes "
                                + identity + " of seed edge "
                                + string(seed, "edgeId"));
                    }
                }
                selected.set(index, runtime.deepCopy());
            }
        }
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
            Set<String> exactInputs = exactInputPorts;
            Set<String> contextBindings = new LinkedHashSet<>();
            collectContextBindings(array(context, "equalityRelations"),
                    exactInputs, contextBindings);
            if (!bindingIds.containsAll(contextBindings)) {
                throw new IOException("selected target symbolic context "
                        + "contains a binding outside the demanded ledger");
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

        private void collectContextBindings(
                JsonArray relations, Set<String> exactInputs,
                Set<String> result) throws IOException {
            for (JsonElement element : relations) {
                if (!element.isJsonObject()) continue;
                JsonObject relation = element.getAsJsonObject();
                for (JsonElement selected : array(relation,
                        "selectedBindings")) {
                    if (!selected.isJsonObject()) continue;
                    JsonObject binding = selected.getAsJsonObject();
                    if (!instance.equals(string(binding,
                            "toOccurrenceId")) || !exactInputs.contains(
                            string(binding, "toInputPort"))) {
                        throw new IOException("selected target symbolic "
                                + "context contains an unrelated binding");
                    }
                    String id = string(binding, "edgeId");
                    if (id.isEmpty()) {
                        throw new IOException("selected target symbolic "
                                + "context binding has no edgeId");
                    }
                    result.add(id);
                }
            }
        }
    }

    static final class Arguments {
        private final Path summaries;
        private final Path pathManifest;
        private final Path seedQuery;
        private final String exceptionType;
        private final String targetInstance;
        private final Path output;

        private Arguments(Path summaries, Path pathManifest,
                          Path seedQuery, String exceptionType,
                          String targetInstance,
                          Path output) {
            this.summaries = summaries;
            this.pathManifest = pathManifest;
            this.seedQuery = seedQuery;
            this.exceptionType = exceptionType;
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
                    required(values, "exception-type"),
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
