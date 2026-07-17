package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Plans bounded, discovery-only captures for an unobserved protocol
 * transition.
 *
 * <p>The static edge is used only as a search hint.  A request emitted here
 * has {@code automaticRelationEligible=false}; neither the edge nor a seed
 * path produced by the request is an SMT relation.  The campaign may promote
 * a replay only when the same fresh execution observes the consumer and a
 * runtime edge accepted by {@link AutomaticRegionEdge#composable(JsonObject)}.
 * </p>
 */
public final class RegionTransitionDiscoveryWorklist {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private RegionTransitionDiscoveryWorklist() {
    }

    public static Result plan(List<JsonObject> regions,
                              List<JsonObject> activations,
                              List<JsonObject> edges,
                              List<JsonObject> roots,
                              List<JsonObject> records,
                              Bounds bounds) {
        return plan(regions, activations, edges, roots, records, bounds,
                Focus.none());
    }

    public static Result plan(List<JsonObject> regions,
                              List<JsonObject> activations,
                              List<JsonObject> edges,
                              List<JsonObject> roots,
                              List<JsonObject> records,
                              Bounds bounds,
                              Focus focus) {
        return new Planner(regions, activations, edges, roots, records,
                bounds == null ? Bounds.defaults() : bounds,
                focus == null ? Focus.none() : focus).run();
    }

    private static final class Planner {
        private final Bounds bounds;
        private final Focus focus;
        private final Map<String, JsonObject> regions = new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> activations =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> records = new LinkedHashMap<>();
        private final List<JsonObject> edges = new ArrayList<>();
        private final Set<String> targetCone = new LinkedHashSet<>();
        private final List<JsonObject> requests = new ArrayList<>();
        private final List<JsonObject> gaps = new ArrayList<>();
        private final Set<String> emitted = new LinkedHashSet<>();
        private int candidateEdgeCount;
        private int exactSliceCandidateCount;
        private int terminalRecordCount;
        private boolean targetConeBoundReached;
        private boolean focusedEdgeSeen;
        private boolean focusedCandidateSeen;
        private boolean focusedActivationSeen;
        private boolean focusedGuardSeen;
        private boolean focusedConsumerAlreadyObserved;
        private boolean focusedEdgeAlreadyComposable;
        private boolean focusedGapIssued;

        private Planner(List<JsonObject> regionRows,
                        List<JsonObject> activationRows,
                        List<JsonObject> edgeRows,
                        List<JsonObject> roots,
                        List<JsonObject> recordRows,
                        Bounds bounds,
                        Focus focus) {
            this.bounds = bounds;
            this.focus = focus;
            for (JsonObject region : safe(regionRows)) {
                String id = string(region, "regionId");
                if (!id.isEmpty()) regions.put(id, region);
            }
            for (JsonObject activation : safe(activationRows)) {
                add(activations, string(activation, "regionId"), activation);
            }
            for (List<JsonObject> values : activations.values()) {
                Collections.sort(values, Comparator.comparing(value ->
                        firstNonBlank(string(value, "activationId"),
                                string(value, "regionInstanceId"))));
            }
            for (JsonObject edge : safe(edgeRows)) {
                this.edges.add(edge);
            }
            Collections.sort(this.edges, Comparator.comparing(value ->
                    firstNonBlank(string(value, "edgeId"),
                            edgeIdentity(value))));
            for (JsonObject record : safe(recordRows)) {
                String key = firstNonBlank(string(record, "requestId"),
                        string(record, "queryKey"));
                if (!key.isEmpty()) records.put(key, record);
            }
            buildTargetCone(roots);
        }

        private Result run() {
            if (targetConeBoundReached) {
                gap("BOUND_REACHED", "MAX_TRANSITION_TARGET_CONE_REGIONS",
                        new JsonObject(), "", "");
            }
            for (JsonObject edge : edges) {
                // Exact focus filtering is deliberately the first edge
                // operation.  A bounded focused run must not spend request,
                // diagnostic, or execution budget on an unrelated mapping.
                if (!focus.matchesEdge(edge)) continue;
                if (focus.hasEdge()) focusedEdgeSeen = true;
                if (requests.size() >= bounds.maxRequests) {
                    gap("BOUND_REACHED", "MAX_TRANSITION_REQUESTS", edge,
                            "", "");
                    break;
                }
                if (!AutomaticRegionEdge.transitionDiscoveryCandidate(edge)) {
                    if (focus.hasEdge()
                            && AutomaticRegionEdge.composable(edge)) {
                        focusedEdgeAlreadyComposable = true;
                    } else if (focus.hasEdge()) {
                        focusedGap(
                                "FOCUSED_EDGE_NOT_TRANSITION_DISCOVERY_CANDIDATE",
                                edge, string(edge, "fromRegion"),
                                string(edge, "fromPort"));
                    }
                    continue;
                }
                if (focus.hasEdge()) focusedCandidateSeen = true;
                candidateEdgeCount++;
                String producer = string(edge, "fromRegion");
                String consumer = string(edge, "toRegion");
                if (!targetCone.contains(consumer)) {
                    if (focus.hasEdge()) focusedGap(
                            "FOCUSED_EDGE_CONSUMER_OUTSIDE_TARGET_CONE",
                            edge, producer, string(edge, "fromPort"));
                    continue;
                }
                if (hasActivation(consumer)) {
                    if (focus.hasEdge()) {
                        focusedConsumerAlreadyObserved = true;
                    }
                    continue;
                }
                List<JsonObject> producerActivations = activations.get(
                        producer);
                if (producerActivations == null
                        || producerActivations.isEmpty()) {
                    gap("TRANSITION_DISCOVERY_GAP",
                            "NO_OBSERVED_PRODUCER_ACTIVATION", edge,
                            producer, "");
                    continue;
                }
                if (focus.hasActivation()) {
                    List<JsonObject> exact = new ArrayList<>();
                    for (JsonObject activation : producerActivations) {
                        if (focus.activationId.equals(string(activation,
                                "activationId"))) {
                            exact.add(activation);
                        }
                    }
                    if (exact.size() != 1) {
                        focusedGap(exact.isEmpty()
                                        ? "FOCUSED_SOURCE_ACTIVATION_NOT_FOUND"
                                        : "FOCUSED_SOURCE_ACTIVATION_AMBIGUOUS",
                                edge, producer, string(edge, "fromPort"));
                        continue;
                    }
                    producerActivations = exact;
                    focusedActivationSeen = true;
                }

                CanonicalEndpoint endpoint = canonicalEndpoint(edge);
                if (!endpoint.complete) {
                    gap("TRANSITION_DISCOVERY_GAP", endpoint.reason, edge,
                            producer, string(edge, "fromPort"));
                    continue;
                }
                OutputSlice output = exactOutputSlice(producer,
                        endpoint.endpoint);
                if (!output.complete) {
                    gap("TRANSITION_DISCOVERY_GAP", output.reason, edge,
                            producer, string(edge, "fromPort"));
                    continue;
                }
                exactSliceCandidateCount++;
                boolean foundGuard = false;
                for (JsonObject activation : producerActivations) {
                    List<JsonObject> eligibleGuards = new ArrayList<>();
                    for (JsonElement element : array(activation,
                            "branches")) {
                        if (!element.isJsonObject()) continue;
                        JsonObject branch = element.getAsJsonObject();
                        String site = string(branch, "siteId");
                        if (!output.sites.contains(site)
                                || !"REACHABILITY".equals(string(branch,
                                "role"))
                                || !bool(branch, "observed", false)
                                || !branch.has("requiredOutcome")
                                || branch.get("requiredOutcome").isJsonNull()) {
                            continue;
                        }
                        boolean observed = bool(branch, "observedOutcome",
                                false);
                        boolean desired = bool(branch, "requiredOutcome",
                                observed);
                        if (observed == desired) continue;
                        if (focus.hasGuard()
                                && !focus.guardSiteId.equals(site)) {
                            continue;
                        }
                        eligibleGuards.add(branch);
                    }
                    if (focus.hasGuard() && eligibleGuards.size() != 1) {
                        focusedGap(eligibleGuards.isEmpty()
                                        ? "FOCUSED_GUARD_NOT_UNIQUE_MISMATCHED_"
                                        + "REACHABILITY_GUARD"
                                        : "FOCUSED_GUARD_AMBIGUOUS",
                                edge, producer, output.port);
                        break;
                    }
                    for (JsonObject branch : eligibleGuards) {
                        boolean observed = bool(branch, "observedOutcome",
                                false);
                        boolean desired = bool(branch, "requiredOutcome",
                                observed);
                        foundGuard = true;
                        if (focus.hasGuard()) focusedGuardSeen = true;
                        emit(edge, activation, output, branch, observed,
                                desired, endpoint.aliasUsed);
                        if (requests.size() >= bounds.maxRequests) break;
                    }
                    if (foundGuard || requests.size() >= bounds.maxRequests) {
                        // One exact concrete producer instance is sufficient
                        // for a semantic guard query.  Repeated instances are
                        // runtime provenance, not distinct solver problems.
                        break;
                    }
                }
                if (!foundGuard && !(focus.hasGuard()
                        && focusedGapIssued)) {
                    gap("TRANSITION_DISCOVERY_GAP",
                            "NO_OBSERVED_MISMATCHED_OUTPUT_REACHABILITY_GUARD",
                            edge, producer, output.port);
                }
            }

            if (focus.hasEdge() && !focusedEdgeSeen) {
                focusedGap("FOCUSED_EDGE_NOT_FOUND", new JsonObject(),
                        "", "");
            }

            JsonObject manifest = new JsonObject();
            manifest.addProperty("schemaVersion", 1);
            manifest.addProperty("kind",
                    "REGION_TRANSITION_DISCOVERY_WORKLIST");
            manifest.addProperty("candidateEdgeCount", candidateEdgeCount);
            manifest.addProperty("exactSliceCandidateCount",
                    exactSliceCandidateCount);
            manifest.addProperty("pendingRequestCount", requests.size());
            manifest.addProperty("terminalRecordCount", terminalRecordCount);
            manifest.addProperty("targetConeBoundReached",
                    targetConeBoundReached);
            manifest.addProperty("focusConfigured", focus.configured());
            manifest.addProperty("focusedEdgeId", focus.edgeId);
            manifest.addProperty("focusedActivationId",
                    focus.activationId);
            manifest.addProperty("focusedGuardSiteId", focus.guardSiteId);
            manifest.addProperty("focusedEdgeSeen", focusedEdgeSeen);
            manifest.addProperty("focusedCandidateSeen",
                    focusedCandidateSeen);
            manifest.addProperty("focusedActivationSeen",
                    focusedActivationSeen);
            manifest.addProperty("focusedGuardSeen", focusedGuardSeen);
            manifest.addProperty("focusedConsumerAlreadyObserved",
                    focusedConsumerAlreadyObserved);
            manifest.addProperty("focusedEdgeAlreadyComposable",
                    focusedEdgeAlreadyComposable);
            manifest.addProperty("focusedGapIssued", focusedGapIssued);
            manifest.addProperty("gapCount", gaps.size());
            manifest.add("gaps", GSON.toJsonTree(gaps));
            manifest.addProperty("staticMappingIsSemanticEvidence", false);
            manifest.addProperty("automaticRelationEligible", false);
            manifest.addProperty("eligibleForAutomaticSmt", false);
            manifest.addProperty("promotionRequirement",
                    "NORMAL_EXACT_OUTPUT_PLUS_CONSUMER_ACTIVATION_PLUS_"
                            + "COMPOSABLE_EDGE_FROM_ONE_FRESH_EXECUTION");
            manifest.addProperty("complete", requests.isEmpty()
                    && gaps.isEmpty());
            return new Result(requests, manifest);
        }

        private void emit(JsonObject edge, JsonObject activation,
                          OutputSlice output, JsonObject branch,
                          boolean observed, boolean desired,
                          boolean canonicalAliasUsed) {
            int occurrence = integer(branch, "selectedOccurrence", 1);
            if (occurrence < 1) occurrence = 1;
            String semantic = edgeIdentity(edge) + "\n" + output.port
                    + "\n" + string(branch, "siteId") + "\n"
                    + occurrence + "\n" + desired;
            if (focus.hasActivation()) {
                semantic += "\nFOCUSED_ACTIVATION\n"
                        + string(activation, "activationId");
            }
            String requestId = "TRANSITION.DISCOVERY."
                    + sha256(semantic).substring(0, 16);
            if (!emitted.add(requestId)) return;
            JsonObject prior = records.get(requestId);
            if (prior != null && terminal(prior)) {
                terminalRecordCount++;
                return;
            }

            JsonObject request = new JsonObject();
            request.addProperty("schemaVersion", 1);
            request.addProperty("kind", "TRANSITION_DISCOVERY_SEED");
            request.addProperty("requestId", requestId);
            request.addProperty("queryKey", requestId);
            request.add("captureGoal", RegionCaptureGoal
                    .transitionDiscovery().toJson());
            request.addProperty("candidateEdgeId", string(edge, "edgeId"));
            request.addProperty("upstreamRegion", string(edge,
                    "fromRegion"));
            request.addProperty("upstreamOutputPort", output.port);
            request.addProperty("upstreamOutputCell", output.cell);
            request.addProperty("edgeOutputEndpoint", string(edge,
                    "fromPort"));
            request.addProperty("canonicalOutputAuthority",
                    canonicalAliasUsed ? "STATIC_UNIQUE_ALIAS_PROOF"
                            : "EXACT_REGION_EDGE_ENDPOINT");
            request.add("aliasProofEdgeIds", array(edge,
                    "aliasProofEdgeIds").deepCopy());
            request.addProperty("downstreamRegion", string(edge,
                    "toRegion"));
            request.addProperty("downstreamInputPort", string(edge,
                    "toPort"));
            request.addProperty("sourceActivationId", string(activation,
                    "activationId"));
            request.addProperty("sourceRegionInstanceId", string(activation,
                    "regionInstanceId"));
            request.add("requestedOutput", output.output.deepCopy());
            request.add("requestedOutputSlice", output.slice.deepCopy());
            JsonObject guard = new JsonObject();
            guard.addProperty("siteId", string(branch, "siteId"));
            guard.addProperty("occurrence", occurrence);
            guard.addProperty("observedOutcome", observed);
            guard.addProperty("desiredOutcome", desired);
            guard.addProperty("authority",
                    "STATIC_EXACT_OUTPUT_SLICE_PLUS_RUNTIME_BRANCH_OUTCOME");
            request.add("transitionGuard", guard);
            request.addProperty("automaticRelationEligible", false);
            request.addProperty("eligibleForAutomaticSmt", false);
            request.addProperty("discoveryOnly", true);
            request.addProperty("summaryCacheAdmission", "QUARANTINED");
            requests.add(request);
        }

        private OutputSlice exactOutputSlice(String regionId,
                                             String endpoint) {
            JsonObject region = regions.get(regionId);
            List<JsonObject> matchingOutputs = new ArrayList<>();
            String expected = canonicalPort(endpoint);
            for (JsonElement element : array(region, "outputs")) {
                if (!element.isJsonObject()) continue;
                JsonObject output = element.getAsJsonObject();
                if (expected.equals(canonicalPort(string(output, "portId")))
                        || expected.equals(canonicalPort(string(output,
                        "cell")))) {
                    matchingOutputs.add(output);
                }
            }
            if (matchingOutputs.size() != 1) {
                return OutputSlice.gap(matchingOutputs.isEmpty()
                        ? "NO_EXACT_STATIC_OUTPUT_FOR_TRANSITION_ENDPOINT"
                        : "AMBIGUOUS_STATIC_OUTPUT_FOR_TRANSITION_ENDPOINT");
            }
            JsonObject output = matchingOutputs.get(0);
            List<JsonObject> matchingSlices = new ArrayList<>();
            for (JsonElement element : array(region, "outputSlices")) {
                if (!element.isJsonObject()) continue;
                JsonObject slice = element.getAsJsonObject();
                if (canonicalPort(string(output, "portId")).equals(
                        canonicalPort(string(slice, "outputPort")))
                        || canonicalPort(string(output, "cell")).equals(
                        canonicalPort(string(slice, "outputCell")))) {
                    matchingSlices.add(slice);
                }
            }
            if (matchingSlices.size() != 1) {
                return OutputSlice.gap(matchingSlices.isEmpty()
                        ? "NO_EXACT_OUTPUT_SLICE_FOR_TRANSITION_ENDPOINT"
                        : "AMBIGUOUS_OUTPUT_SLICE_FOR_TRANSITION_ENDPOINT");
            }
            JsonObject slice = matchingSlices.get(0);
            if (!bool(slice, "complete", false)) {
                return OutputSlice.gap(
                        "INCOMPLETE_OUTPUT_SLICE_FOR_TRANSITION_ENDPOINT");
            }
            Set<String> sites = new LinkedHashSet<>();
            for (JsonElement site : array(slice, "sites")) {
                if (site.isJsonPrimitive()) sites.add(site.getAsString());
            }
            if (sites.isEmpty()) {
                return OutputSlice.gap(
                        "OUTPUT_SLICE_HAS_NO_EXACT_REACHABILITY_SITES");
            }
            return OutputSlice.complete(firstNonBlank(string(output,
                    "portId"), endpoint), string(output, "cell"), output,
                    slice, sites);
        }

        /**
         * Runtime fingerprinting keeps using edge.fromPort.  A distinct
         * canonical region output may be selected only when the planner has
         * persisted its exact alias proof; field-name or suffix matching is
         * never attempted here.
         */
        private CanonicalEndpoint canonicalEndpoint(JsonObject edge) {
            String canonicalOutputPort = string(edge, "fromOutputPort");
            String canonicalCell = string(edge, "fromOutputCell");
            if (!hasCanonicalOutputMetadata(edge)) {
                return CanonicalEndpoint.complete(string(edge, "fromPort"),
                        false);
            }
            if (!bool(edge, "aliasProofComplete", false)
                    || !("STATIC_EXACT_PROJECTED_RETURN_VALUE_FLOW_"
                    + "AND_DECLARED_RETURN_FIELD").equals(string(edge,
                    "aliasProofAuthority"))
                    || canonicalOutputPort.isEmpty()
                    || canonicalCell.isEmpty()
                    || !nonEmptyProofIds(edge)) {
                return CanonicalEndpoint.gap(
                        "INCOMPLETE_CANONICAL_OUTPUT_ALIAS_PROOF");
            }
            JsonObject region = regions.get(string(edge, "fromRegion"));
            int matches = 0;
            for (JsonElement element : array(region, "outputs")) {
                if (!element.isJsonObject()) continue;
                JsonObject output = element.getAsJsonObject();
                if (canonicalPort(canonicalOutputPort).equals(canonicalPort(
                        string(output, "portId")))
                        && canonicalPort(canonicalCell).equals(
                        canonicalPort(string(output, "cell")))) {
                    matches++;
                }
            }
            if (matches != 1) {
                return CanonicalEndpoint.gap(matches == 0
                        ? "CANONICAL_OUTPUT_PORT_CELL_PAIR_NOT_FOUND"
                        : "CANONICAL_OUTPUT_PORT_CELL_PAIR_AMBIGUOUS");
            }
            return CanonicalEndpoint.complete(firstNonBlank(
                    canonicalOutputPort, canonicalCell), true);
        }

        private boolean hasCanonicalOutputMetadata(JsonObject edge) {
            return edge != null && (edge.has("fromOutputPort")
                    || edge.has("fromOutputCell")
                    || edge.has("aliasProofEdgeIds")
                    || edge.has("aliasProofAuthority")
                    || edge.has("aliasProofComplete"));
        }

        private boolean nonEmptyProofIds(JsonObject edge) {
            JsonArray ids = array(edge, "aliasProofEdgeIds");
            if (ids.size() == 0) return false;
            for (JsonElement id : ids) {
                if (!id.isJsonPrimitive()
                        || id.getAsString().trim().isEmpty()) return false;
            }
            return true;
        }

        private void buildTargetCone(List<JsonObject> roots) {
            Map<String, Set<String>> predecessors = new LinkedHashMap<>();
            for (JsonObject edge : edges) {
                String from = string(edge, "fromRegion");
                String to = string(edge, "toRegion");
                if (from.isEmpty() || to.isEmpty()) continue;
                Set<String> values = predecessors.get(to);
                if (values == null) {
                    values = new LinkedHashSet<>();
                    predecessors.put(to, values);
                }
                values.add(from);
            }
            Deque<String> pending = new ArrayDeque<>();
            for (JsonObject root : safe(roots)) {
                String region = string(root, "regionId");
                if (!region.isEmpty() && targetCone.add(region)) {
                    pending.addLast(region);
                }
            }
            while (!pending.isEmpty()
                    && targetCone.size() < bounds.maxTargetConeRegions) {
                Set<String> previous = predecessors.get(
                        pending.removeFirst());
                if (previous == null) continue;
                for (String region : previous) {
                    if (targetCone.add(region)) pending.addLast(region);
                }
            }
            targetConeBoundReached = !pending.isEmpty();
        }

        private boolean hasActivation(String region) {
            List<JsonObject> values = activations.get(region);
            return values != null && !values.isEmpty();
        }

        private void gap(String kind, String reason, JsonObject edge,
                         String region, String output) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("reason", reason);
            gap.addProperty("edgeId", string(edge, "edgeId"));
            gap.addProperty("regionId", region);
            gap.addProperty("outputEndpoint", output);
            gaps.add(gap);
        }

        private void focusedGap(String reason, JsonObject edge,
                                String region, String output) {
            gap("TRANSITION_DISCOVERY_FOCUS_GAP", reason, edge, region,
                    output);
            focusedGapIssued = true;
        }
    }

    /** Exact optional selector for one bounded transition experiment. */
    public static final class Focus {
        public final String edgeId;
        public final String activationId;
        public final String guardSiteId;

        public Focus(String edgeId, String activationId,
                     String guardSiteId) {
            this.edgeId = clean(edgeId);
            this.activationId = clean(activationId);
            this.guardSiteId = clean(guardSiteId);
        }

        public static Focus none() {
            return new Focus("", "", "");
        }

        public boolean configured() {
            return hasEdge() || hasActivation() || hasGuard();
        }

        public boolean hasEdge() {
            return !edgeId.isEmpty();
        }

        public boolean hasActivation() {
            return !activationId.isEmpty();
        }

        public boolean hasGuard() {
            return !guardSiteId.isEmpty();
        }

        public boolean matchesTask(JsonObject task) {
            return matchesDiscovery(object(task, "transitionDiscovery"));
        }

        public boolean matchesDiscovery(JsonObject discovery) {
            return (!hasEdge() || edgeId.equals(string(discovery,
                    "candidateEdgeId")))
                    && (!hasActivation() || activationId.equals(string(
                    discovery, "sourceActivationId")))
                    && (!hasGuard() || guardSiteId.equals(string(discovery,
                    "guardSiteId")));
        }

        private boolean matchesEdge(JsonObject edge) {
            return !hasEdge() || edgeId.equals(string(edge, "edgeId"));
        }

        private static String clean(String value) {
            return value == null ? "" : value.trim();
        }
    }

    public static final class Bounds {
        public final int maxRequests;
        public final int maxTargetConeRegions;

        public Bounds(int maxRequests, int maxTargetConeRegions) {
            this.maxRequests = Math.max(1, maxRequests);
            this.maxTargetConeRegions = Math.max(1, maxTargetConeRegions);
        }

        public static Bounds defaults() {
            return new Bounds(32, 256);
        }
    }

    public static final class Result {
        public final List<JsonObject> requests;
        public final JsonObject manifest;

        private Result(List<JsonObject> requests, JsonObject manifest) {
            this.requests = requests;
            this.manifest = manifest;
        }
    }

    private static final class OutputSlice {
        private final boolean complete;
        private final String reason;
        private final String port;
        private final String cell;
        private final JsonObject output;
        private final JsonObject slice;
        private final Set<String> sites;

        private OutputSlice(boolean complete, String reason, String port,
                            String cell, JsonObject output, JsonObject slice,
                            Set<String> sites) {
            this.complete = complete;
            this.reason = reason;
            this.port = port;
            this.cell = cell;
            this.output = output;
            this.slice = slice;
            this.sites = sites;
        }

        private static OutputSlice gap(String reason) {
            return new OutputSlice(false, reason, "", "",
                    new JsonObject(), new JsonObject(),
                    Collections.<String>emptySet());
        }

        private static OutputSlice complete(String port, String cell,
                                            JsonObject output,
                                            JsonObject slice,
                                            Set<String> sites) {
            return new OutputSlice(true, "", port, cell, output, slice,
                    sites);
        }
    }

    private static final class CanonicalEndpoint {
        private final boolean complete;
        private final String endpoint;
        private final String reason;
        private final boolean aliasUsed;

        private CanonicalEndpoint(boolean complete, String endpoint,
                                  String reason, boolean aliasUsed) {
            this.complete = complete;
            this.endpoint = endpoint;
            this.reason = reason;
            this.aliasUsed = aliasUsed;
        }

        private static CanonicalEndpoint complete(String endpoint,
                                                  boolean aliasUsed) {
            return new CanonicalEndpoint(true, endpoint, "", aliasUsed);
        }

        private static CanonicalEndpoint gap(String reason) {
            return new CanonicalEndpoint(false, "", reason, false);
        }
    }

    private static boolean terminal(JsonObject record) {
        String status = string(record, "status");
        return "TRANSITION_VALIDATED".equals(status)
                || "TRANSITION_SEED_CAPTURED".equals(status)
                || "UNSAT".equals(status)
                || "UNSUPPORTED".equals(status)
                || "MATERIALIZATION_GAP".equals(status)
                || "EXECUTION_ERROR".equals(status)
                || "NO_RUNTIME_TRANSITION_EVIDENCE".equals(status)
                || "BOUND_REACHED".equals(status);
    }

    private static String edgeIdentity(JsonObject edge) {
        return string(edge, "edgeId") + "\n"
                + string(edge, "fromRegion") + "\n"
                + canonicalPort(string(edge, "fromPort")) + "\n"
                + string(edge, "toRegion") + "\n"
                + canonicalPort(string(edge, "toPort"));
    }

    private static String canonicalPort(String value) {
        if (value == null) return "";
        String result = value.trim();
        while (result.startsWith("M_") || result.startsWith("C_")) {
            result = result.substring(2);
        }
        return result;
    }

    private static String sha256(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(value.getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException exception) {
            throw new IllegalStateException(exception);
        }
    }

    private static <T> List<T> safe(List<T> values) {
        return values == null ? Collections.<T>emptyList() : values;
    }

    private static <T> void add(Map<String, List<T>> values, String key,
                                T value) {
        if (key == null || key.isEmpty()) return;
        List<T> items = values.get(key);
        if (items == null) {
            items = new ArrayList<>();
            values.put(key, items);
        }
        items.add(value);
    }

    private static JsonArray array(JsonObject object, String field) {
        if (object == null) return new JsonArray();
        JsonElement value = object.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static JsonObject object(JsonObject owner, String field) {
        if (owner == null) return new JsonObject();
        JsonElement value = owner.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static String string(JsonObject object, String field) {
        if (object == null) return "";
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject object, String field,
                                boolean fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject object, String field,
                               int fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value;
        }
        return "";
    }
}
