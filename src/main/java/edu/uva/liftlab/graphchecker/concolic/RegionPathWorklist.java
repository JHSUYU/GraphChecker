package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Builds bounded branch-flip work for path-sensitive summaries of region
 * outputs.
 *
 * <p>A graph work item answers "which upstream region defines this input?".
 * A path work item answers "which other feasible path through this one region
 * changes its requested output?".  Keeping these queues separate prevents an
 * alternative data-flow edge from being misreported as a concolic path.</p>
 */
public final class RegionPathWorklist {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private RegionPathWorklist() {
    }

    public static Result plan(List<JsonObject> summaries,
                              List<JsonObject> activations,
                              List<JsonObject> explorationRecords,
                              Bounds bounds) {
        Bounds effective = bounds == null ? Bounds.defaults() : bounds;
        return new Planner(summaries, activations, explorationRecords,
                effective).run();
    }

    /** Stable identity of a semantic flip; runtime activation ids are absent. */
    public static String stableFlipKey(String regionId,
                                       JsonElement requestedOutput,
                                       JsonArray prefix,
                                       String siteId,
                                       int occurrence,
                                       boolean desiredOutcome) {
        return stableFlipKey(regionId, requestedOutput, siteId,
                occurrence, desiredOutcome, canonical(prefix), "", "");
    }

    private static String stableFlipKey(String regionId,
                                        JsonElement requestedOutput,
                                        String siteId,
                                        int occurrence,
                                        boolean desiredOutcome,
                                        String prefixIdentity,
                                        String dynamicBindingIdentity,
                                        String queryPurpose) {
        StringBuilder value = new StringBuilder();
        component(value, regionId);
        component(value, canonical(requestedOutput));
        component(value, prefixIdentity);
        component(value, siteId);
        component(value, String.valueOf(occurrence));
        component(value, String.valueOf(desiredOutcome));
        component(value, dynamicBindingIdentity);
        if (queryPurpose != null && !queryPurpose.isEmpty()) {
            component(value, queryPurpose);
        }
        return sha256(value.toString());
    }

    /** Content identity of one observed path, independent of activation ids. */
    public static String stablePathKey(JsonObject summary) {
        AlphaNormalizer alpha = new AlphaNormalizer(summary);
        StringBuilder value = new StringBuilder();
        component(value, string(summary, "regionId"));
        component(value, canonical(summary.get("requestedOutput")));
        component(value, alphaCanonical(summary.get("pathCondition"), alpha));
        component(value, alphaCanonical(summary.get("outputExpressions"), alpha));
        component(value, alphaCanonical(summary.get("heapEffects"), alpha));
        component(value, stableRuntimeBindings(summary, alpha));
        component(value, string(summary, "normalExit"));
        component(value, string(summary, "exceptionType"));
        return sha256(value.toString());
    }

    private static final class Planner {
        private final Bounds bounds;
        private final long startedNanos = System.nanoTime();
        private final Map<String, JsonObject> activations =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> records = new LinkedHashMap<>();
        private final List<JsonObject> summaries = new ArrayList<>();
        private final List<JsonObject> tasks = new ArrayList<>();
        private final List<JsonObject> gaps = new ArrayList<>();
        private final Set<String> gapKeys = new LinkedHashSet<>();
        private final Set<String> emitted = new LinkedHashSet<>();
        private final Map<String, Integer> pathCountByRegion =
                new LinkedHashMap<>();
        private int candidateFlipCount;
        private int terminalFlipCount;
        private int duplicateTaskCount;
        private int transitionDiscoverySeedCount;
        private int transitionDiscoveryTaskCount;
        private boolean wallClockReached;

        private Planner(List<JsonObject> summaries,
                        List<JsonObject> activations,
                        List<JsonObject> explorationRecords,
                        Bounds bounds) {
            this.bounds = bounds;
            for (JsonObject activation : safe(activations)) {
                String id = string(activation, "activationId");
                if (!id.isEmpty()) this.activations.put(id, activation);
            }
            for (JsonObject record : safe(explorationRecords)) {
                String key = string(record, "queryKey");
                if (!key.isEmpty()) this.records.put(key, record);
            }
            this.summaries.addAll(safe(summaries));
            Collections.sort(this.summaries, Comparator.comparing(value ->
                    string(value, "regionId") + "\n"
                            + stablePathKey(value)));
        }

        private Result run() {
            Set<String> seenPaths = new LinkedHashSet<>();
            for (JsonObject summary : summaries) {
                if (!bool(summary, "valid", true)) continue;
                String region = string(summary, "regionId");
                if (region.isEmpty()) continue;
                JsonObject activation = activations.get(string(summary,
                        "activationId"));
                RegionCaptureGoal goal = RegionCaptureGoal.from(
                        activation == null ? summary : activation);
                if (!goal.isOutputClosure()) continue;

                String pathKey = stablePathKey(summary);
                if (!seenPaths.add(region + "\n" + pathKey)) continue;
                increment(pathCountByRegion, region);
                boolean transitionDiscovery = goal.isTransitionDiscovery();
                if (transitionDiscovery) transitionDiscoverySeedCount++;
                if (!bool(summary, "relationallyComplete", false)
                        && !(transitionDiscovery
                        && admissibleTransitionDiscoverySeed(summary))) {
                    gap("INCOMPLETE_REGION_SUMMARY",
                            "RELATIONAL_INPUT_OUTPUT_SUMMARY_NOT_COMPLETE",
                            region, pathKey, "", -1);
                    continue;
                }
                if (pathCountByRegion.get(region) > bounds.maxPathsPerRegion) {
                    gap("BOUND_REACHED", "MAX_PATHS_PER_REGION", region,
                            pathKey, "", -1);
                    continue;
                }
                if (wallClockExceeded()) {
                    wallClockReached = true;
                    gap("BOUND_REACHED", "MAX_WALL_CLOCK", region,
                            pathKey, "", -1);
                    break;
                }
                planSummary(summary, activation, pathKey);
                if (tasks.size() >= bounds.maxTasks) break;
            }

            JsonObject manifest = manifest(seenPaths.size());
            return new Result(tasks, manifest);
        }

        private void planSummary(JsonObject summary, JsonObject activation,
                                 String pathKey) {
            JsonArray conditions = array(summary, "pathCondition");
            JsonArray mappings = array(summary, "branchMappings");
            boolean policyAware = hasBranchPolicy(mappings);
            Set<String> outputSites = outputSliceSites(summary, activation);
            RegionCaptureGoal goal = RegionCaptureGoal.from(
                    activation == null ? summary : activation);
            JsonObject discovery = object(summary, "transitionDiscovery");
            String discoverySite = goal.isTransitionDiscovery()
                    ? string(discovery, "guardSiteId") : "";
            int discoveryOccurrence = integer(discovery,
                    "guardOccurrence", -1);
            boolean discoveryDesired = bool(discovery,
                    "desiredOutcome", false);
            List<JsonObject> candidates = new ArrayList<>();
            for (JsonElement element : mappings) {
                if (!element.isJsonObject()) continue;
                JsonObject mapping = element.getAsJsonObject();
                if (policyAware && !isExplorePolicy(mapping)) {
                    continue;
                }
                String site = string(mapping, "siteId");
                if (!outputSites.isEmpty() && !outputSites.contains(site)) {
                    continue;
                }
                if (goal.isTransitionDiscovery()
                        && (!discoverySite.equals(site)
                        || discoveryOccurrence > 0
                        && discoveryOccurrence != integer(mapping,
                        "occurrence", 1)
                        || discoveryDesired == bool(mapping, "outcome",
                        false))) {
                    continue;
                }
                int conditionIndex = integer(mapping, "conditionIndex", -1);
                if (conditionIndex < 0 || conditionIndex >= conditions.size()) {
                    gap("UNMAPPED_BRANCH", "NO_NORMALIZED_CONDITION", string(
                                    summary, "regionId"), pathKey, site,
                            integer(mapping, "occurrence", -1));
                    continue;
                }
                candidates.add(mapping);
            }
            // Classic depth-first concolic order: flip the latest relevant
            // decision first, then progressively shorter prefixes.
            Collections.sort(candidates, (left, right) -> {
                int byIndex = Integer.compare(integer(right,
                        "conditionIndex", -1), integer(left,
                        "conditionIndex", -1));
                if (byIndex != 0) return byIndex;
                int bySite = string(left, "siteId").compareTo(
                        string(right, "siteId"));
                if (bySite != 0) return bySite;
                return Integer.compare(integer(left, "occurrence", 1),
                        integer(right, "occurrence", 1));
            });

            int limit = Math.min(candidates.size(), bounds.maxFlipsPerPath);
            if (candidates.size() > limit) {
                gap("BOUND_REACHED", "MAX_FLIPS_PER_PATH", string(summary,
                                "regionId"), pathKey, "", -1);
            }
            for (int index = 0; index < limit; index++) {
                if (tasks.size() >= bounds.maxTasks) {
                    gap("BOUND_REACHED", "MAX_TASKS", string(summary,
                                    "regionId"), pathKey, "", -1);
                    return;
                }
                emitTask(summary, activation, pathKey, conditions,
                        candidates.get(index));
            }
        }

        private boolean hasBranchPolicy(JsonArray mappings) {
            for (JsonElement element : mappings) {
                if (element.isJsonObject()
                        && element.getAsJsonObject().has("policy")) {
                    return true;
                }
            }
            return false;
        }

        private boolean isExplorePolicy(JsonObject mapping) {
            JsonElement policy = mapping.get("policy");
            return policy != null && policy.isJsonPrimitive()
                    && policy.getAsJsonPrimitive().isString()
                    && "EXPLORE".equals(policy.getAsString());
        }

        private void emitTask(JsonObject summary, JsonObject activation,
                              String pathKey, JsonArray conditions,
                              JsonObject mapping) {
            int conditionIndex = integer(mapping, "conditionIndex", -1);
            JsonArray prefix = new JsonArray();
            for (int index = 0; index < conditionIndex; index++) {
                prefix.add(conditions.get(index).deepCopy());
            }
            JsonElement original = conditions.get(conditionIndex);
            JsonElement negated = negate(original);
            JsonArray query = prefix.deepCopy();
            query.add(negated.deepCopy());
            boolean desired = !bool(mapping, "outcome", false);
            String region = string(summary, "regionId");
            String site = string(mapping, "siteId");
            int occurrence = integer(mapping, "occurrence", 1);
            JsonElement output = summary.get("requestedOutput");
            RegionCaptureGoal goal = RegionCaptureGoal.from(
                    activation == null ? summary : activation);
            String purpose = goal.isTransitionDiscovery()
                    ? stableTransitionDiscoveryPurpose(summary) : "";
            AlphaNormalizer alpha = new AlphaNormalizer(summary);
            String key = stableFlipKey(region, output, site,
                    occurrence, desired, alphaCanonical(prefix, alpha),
                    stableRuntimeBindings(summary, alpha), purpose);
            candidateFlipCount++;

            JsonObject previous = records.get(key);
            if (previous != null && terminal(previous)) {
                terminalFlipCount++;
                if (gapStatus(previous)) {
                    gap("EXPLORATION_GAP", firstNonBlank(string(previous,
                                    "reason"), string(previous, "status")),
                            region, pathKey, site, occurrence);
                }
                return;
            }
            if (!emitted.add(key)) {
                duplicateTaskCount++;
                return;
            }

            JsonObject task = new JsonObject();
            task.addProperty("schemaVersion", 1);
            task.addProperty("kind", "REGION_PATH_FLIP");
            task.addProperty("queryKey", key);
            task.addProperty("regionId", region);
            task.add("captureGoal", (goal.isTransitionDiscovery()
                    ? RegionCaptureGoal.transitionDiscovery()
                    : RegionCaptureGoal.outputClosure()).toJson());
            if (goal.isTransitionDiscovery()) {
                task.addProperty("discoveryOnly", true);
                task.addProperty("summaryCacheAdmission", "QUARANTINED");
                task.add("transitionDiscovery", object(summary,
                        "transitionDiscovery").deepCopy());
                transitionDiscoveryTaskCount++;
            }
            task.addProperty("sourceSummaryId", string(summary, "summaryId"));
            task.addProperty("sourcePathKey", pathKey);
            task.addProperty("sourceActivationId", string(summary,
                    "activationId"));
            task.addProperty("rootMethod", firstNonBlank(string(summary,
                    "rootMethod"), string(activation, "rootMethod")));
            task.add("requestedOutput", copy(output, new JsonObject()));
            task.addProperty("flipSite", site);
            task.addProperty("flipOccurrence", occurrence);
            task.addProperty("conditionIndex", conditionIndex);
            task.addProperty("observedOutcome", bool(mapping, "outcome",
                    false));
            task.addProperty("desiredOutcome", desired);
            task.addProperty("prefixPolicy", "KEEP_BEFORE_FLIP");
            task.addProperty("targetPolicy", "NEGATE_SELECTED_CONDITION");
            task.addProperty("suffixPolicy", "DROP_OLD_SUFFIX");
            task.add("prefix", prefix);
            task.add("expectedBranchPrefix", expectedBranchPrefix(
                    mappingsFor(summary), conditionIndex));
            task.add("originalCondition", original.deepCopy());
            task.add("negatedCondition", negated);
            task.add("constraints", query);
            task.add("dynamicFieldBindings", array(summary,
                    "dynamicFieldBindings").deepCopy());
            task.add("engineArrayInputBindings", array(summary,
                    "engineArrayInputBindings").deepCopy());
            task.addProperty("status", "PENDING_SOLVE");
            task.addProperty("dynamicIdsExcludedFromQueryKey", true);
            tasks.add(task);
        }

        private String stableTransitionDiscoveryPurpose(JsonObject summary) {
            JsonObject stable = object(summary,
                    "transitionDiscovery").deepCopy();
            stable.remove("seedExecutionId");
            stable.remove("promotionAdmission");
            return canonical(stable);
        }

        private JsonArray mappingsFor(JsonObject summary) {
            return array(summary, "branchMappings");
        }

        private JsonArray expectedBranchPrefix(JsonArray mappings,
                                               int flipConditionIndex) {
            List<JsonObject> ordered = new ArrayList<>();
            for (JsonElement element : mappings) {
                if (!element.isJsonObject()) continue;
                JsonObject mapping = element.getAsJsonObject();
                int index = integer(mapping, "conditionIndex", -1);
                if (index >= 0 && index < flipConditionIndex) {
                    ordered.add(mapping);
                }
            }
            Collections.sort(ordered, Comparator.comparingInt(value ->
                    integer(value, "conditionIndex", -1)));
            JsonArray result = new JsonArray();
            for (JsonObject mapping : ordered) {
                JsonObject expected = new JsonObject();
                expected.addProperty("siteId", string(mapping, "siteId"));
                expected.addProperty("occurrence", integer(mapping,
                        "occurrence", 1));
                expected.addProperty("outcome", bool(mapping, "outcome",
                        false));
                expected.addProperty("conditionIndex", integer(mapping,
                        "conditionIndex", -1));
                result.add(expected);
            }
            return result;
        }

        private JsonObject manifest(int observedPathCount) {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind", "REGION_PATH_WORKLIST");
            result.addProperty("captureScope",
                    "OUTPUT_RELEVANT_BOUNDED_PATH_CLOSURE");
            result.addProperty("targetRegionPolicy",
                    "ONE_DIRECTED_TARGET_BRANCH_OUTSIDE_THIS_WORKLIST");
            result.addProperty("stableKeyAlgorithm",
                    "SHA-256_CANONICAL_FLIP_QUERY_V1");
            result.addProperty("dynamicIdsExcludedFromStableKey", true);
            result.add("bounds", bounds.toJson());
            result.addProperty("observedPathCount", observedPathCount);
            result.addProperty("candidateFlipCount", candidateFlipCount);
            result.addProperty("terminalFlipCount", terminalFlipCount);
            result.addProperty("pendingTaskCount", tasks.size());
            result.addProperty("duplicateTaskCount", duplicateTaskCount);
            result.addProperty("transitionDiscoverySeedCount",
                    transitionDiscoverySeedCount);
            result.addProperty("transitionDiscoveryTaskCount",
                    transitionDiscoveryTaskCount);
            result.addProperty("wallClockBoundReached", wallClockReached);
            result.add("pathCountByRegion", GSON.toJsonTree(
                    pathCountByRegion));
            result.addProperty("gapCount", gaps.size());
            result.add("gaps", GSON.toJsonTree(gaps));
            boolean closed = tasks.isEmpty() && gaps.isEmpty();
            result.addProperty("complete", closed);
            result.addProperty("status", closed
                    ? "COMPLETE_BOUNDED_PATH_CLOSURE"
                    : gaps.isEmpty()
                    ? "PATH_CLOSURE_HAS_PENDING_WORK"
                    : "PATH_CLOSURE_WITH_EXPLICIT_GAPS");
            result.addProperty("soundnessScope",
                    "OBSERVED_AND_SOLVER_CLOSED_OUTPUT_RELEVANT_PATHS_WITHIN_BOUNDS");
            return result;
        }

        private boolean admissibleTransitionDiscoverySeed(
                JsonObject summary) {
            JsonObject discovery = object(summary, "transitionDiscovery");
            String site = string(discovery, "guardSiteId");
            int occurrence = integer(discovery, "guardOccurrence", -1);
            if (!bool(summary, "normalExit", false)
                    || !bool(summary, "requestedOutputSliceComplete", false)
                    || site.isEmpty() || occurrence < 1
                    || array(summary, "pathCondition").size() == 0
                    || array(summary, "branchMappings").size() == 0) {
                return false;
            }
            for (JsonElement element : array(summary, "branchMappings")) {
                if (!element.isJsonObject()) continue;
                JsonObject mapping = element.getAsJsonObject();
                if (site.equals(string(mapping, "siteId"))
                        && occurrence == integer(mapping, "occurrence", 1)
                        && integer(mapping, "conditionIndex", -1) >= 0) {
                    return true;
                }
            }
            return false;
        }

        private void gap(String kind, String reason, String region,
                         String pathKey, String site, int occurrence) {
            String key = kind + "\n" + reason + "\n" + region + "\n"
                    + pathKey + "\n" + site + "\n" + occurrence;
            if (!gapKeys.add(key)) return;
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("reason", reason);
            gap.addProperty("regionId", region);
            gap.addProperty("pathKey", pathKey);
            gap.addProperty("siteId", site);
            gap.addProperty("occurrence", occurrence);
            gaps.add(gap);
        }

        private boolean wallClockExceeded() {
            return (System.nanoTime() - startedNanos) / 1_000_000L
                    >= bounds.maxWallClockMillis;
        }
    }

    public static final class Bounds {
        public final int maxPathsPerRegion;
        public final int maxFlipsPerPath;
        public final int maxTasks;
        public final long maxWallClockMillis;

        public Bounds(int maxPathsPerRegion, int maxFlipsPerPath,
                      int maxTasks, long maxWallClockMillis) {
            this.maxPathsPerRegion = Math.max(1, maxPathsPerRegion);
            this.maxFlipsPerPath = Math.max(1, maxFlipsPerPath);
            this.maxTasks = Math.max(1, maxTasks);
            this.maxWallClockMillis = Math.max(1L, maxWallClockMillis);
        }

        public static Bounds defaults() {
            return new Bounds(64, 32, 256, 30_000L);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("maxPathsPerRegion", maxPathsPerRegion);
            result.addProperty("maxFlipsPerPath", maxFlipsPerPath);
            result.addProperty("maxTasks", maxTasks);
            result.addProperty("maxWallClockMillis", maxWallClockMillis);
            return result;
        }
    }

    public static final class Result {
        public final List<JsonObject> tasks;
        public final JsonObject manifest;

        private Result(List<JsonObject> tasks, JsonObject manifest) {
            this.tasks = tasks;
            this.manifest = manifest;
        }
    }

    private static Set<String> outputSliceSites(JsonObject summary,
                                                JsonObject activation) {
        Set<String> result = new LinkedHashSet<>();
        collectStrings(result, array(object(summary, "requestedOutputSlice"),
                "sites"));
        collectStrings(result, array(object(activation,
                "requestedOutputSlice"), "sites"));
        return result;
    }

    private static void collectStrings(Set<String> output, JsonArray values) {
        for (JsonElement value : values) {
            try {
                if (value.isJsonPrimitive()) output.add(value.getAsString());
            } catch (RuntimeException ignored) {
            }
        }
    }

    private static boolean terminal(JsonObject record) {
        String status = string(record, "status");
        return "UNSAT".equals(status)
                || "TRANSITION_VALIDATED".equals(status)
                || "NO_RUNTIME_TRANSITION_EVIDENCE".equals(status)
                || "EXECUTED_NEW_PATH".equals(status)
                || "EXECUTED_DUPLICATE_PATH".equals(status)
                || "UNSUPPORTED".equals(status)
                || "MATERIALIZATION_GAP".equals(status)
                || "EXECUTION_ERROR".equals(status)
                || "BOUND_REACHED".equals(status);
    }

    private static boolean gapStatus(JsonObject record) {
        String status = string(record, "status");
        return "UNSUPPORTED".equals(status)
                || "NO_RUNTIME_TRANSITION_EVIDENCE".equals(status)
                || "MATERIALIZATION_GAP".equals(status)
                || "EXECUTION_ERROR".equals(status)
                || "BOUND_REACHED".equals(status);
    }

    static JsonElement negate(JsonElement expression) {
        if (expression != null && expression.isJsonObject()) {
            JsonObject object = expression.getAsJsonObject();
            if ("BinaryExpression".equals(string(object, "_type"))) {
                String opposite = opposite(string(object, "_op"));
                if (!opposite.isEmpty()) {
                    JsonObject copy = object.deepCopy();
                    copy.addProperty("_op", opposite);
                    return copy;
                }
            }
            if ("NotExpression".equals(string(object, "_type"))) {
                JsonElement operand = object.get("_operand");
                return operand == null ? JsonNull.INSTANCE
                        : operand.deepCopy();
            }
        }
        JsonObject negated = new JsonObject();
        negated.addProperty("_type", "NotExpression");
        negated.add("_operand", copy(expression, JsonNull.INSTANCE));
        return negated;
    }

    private static String opposite(String operator) {
        if ("==".equals(operator)) return "!=";
        if ("!=".equals(operator)) return "==";
        if ("<".equals(operator)) return ">=";
        if ("<=".equals(operator)) return ">";
        if (">".equals(operator)) return "<=";
        if (">=".equals(operator)) return "<";
        return "";
    }

    private static String canonical(JsonElement value) {
        if (value == null || value.isJsonNull()) return "null";
        if (value.isJsonPrimitive()) {
            JsonPrimitive primitive = value.getAsJsonPrimitive();
            return GSON.toJson(primitive);
        }
        if (value.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement element : value.getAsJsonArray()) {
                if (!first) result.append(',');
                first = false;
                result.append(canonical(element));
            }
            return result.append(']').toString();
        }
        JsonObject object = value.getAsJsonObject();
        StringBuilder result = new StringBuilder("{");
        boolean first = true;
        for (String key : new TreeSet<>(object.keySet())) {
            if (!first) result.append(',');
            first = false;
            result.append(GSON.toJson(key)).append(':')
                    .append(canonical(object.get(key)));
        }
        return result.append('}').toString();
    }

    private static String stableDynamicBindings(JsonObject summary,
                                                AlphaNormalizer alpha) {
        List<String> bindings = new ArrayList<>();
        for (JsonElement element : array(summary, "dynamicFieldBindings")) {
            if (!element.isJsonObject()) {
                bindings.add(alphaCanonical(element, alpha));
                continue;
            }
            JsonObject source = element.getAsJsonObject();
            JsonObject stable = new JsonObject();
            stable.addProperty("kind", string(source, "kind"));
            stable.addProperty("baseInputSymbol", string(source,
                    "baseInputSymbol"));
            stable.addProperty("dynamicFieldSymbol", string(source,
                    "dynamicFieldSymbol"));
            stable.addProperty("materializationSiteId", string(source,
                    "materializationSiteId"));
            stable.addProperty("materializationOccurrence", integer(source,
                    "materializationOccurrence", -1));
            copyStable(source, stable, "fieldSignature");
            copyStable(source, stable, "fieldPath");
            copyStable(source, stable, "keyExpression");
            copyStable(source, stable, "keyExpressionAuthority");
            copyStable(source, stable, "mapProjectionSelector");
            copyStable(source, stable, "entrySnapshotElementCount");
            copyStable(source, stable, "outputElementCount");
            copyStable(source, stable, "runtimeSymbolizationAuthority");
            copyStable(source, stable, "projectionEvidenceAuthority");
            copyStable(source, stable, "outputValidationMode");
            stable.addProperty("complete", bool(source, "complete", false));
            bindings.add(alphaCanonical(stripVolatileIdentity(stable),
                    alpha));
        }
        Collections.sort(bindings);
        return canonical(GSON.toJsonTree(bindings));
    }

    private static String stableRuntimeBindings(JsonObject summary,
                                                AlphaNormalizer alpha) {
        return stableDynamicBindings(summary, alpha) + "\n"
                + stableEngineArrayBindings(summary, alpha);
    }

    /**
     * Retains the semantic input/engine-array bijection while erasing the
     * activation-local array id and object token allocated by one replay.
     * The id is alpha-renamed through the same table as path-condition
     * {@code _arr_str} values so a bridge remains joined to its exact load.
     */
    private static String stableEngineArrayBindings(JsonObject summary,
                                                    AlphaNormalizer alpha) {
        List<String> bindings = new ArrayList<>();
        List<JsonElement> ordered = new ArrayList<>();
        for (JsonElement element : array(summary,
                "engineArrayInputBindings")) {
            ordered.add(element);
        }
        Collections.sort(ordered, new Comparator<JsonElement>() {
            @Override
            public int compare(JsonElement left, JsonElement right) {
                if (!left.isJsonObject() || !right.isJsonObject()) {
                    return canonical(left).compareTo(canonical(right));
                }
                JsonObject l = left.getAsJsonObject();
                JsonObject r = right.getAsJsonObject();
                int port = string(l, "inputPort").compareTo(
                        string(r, "inputPort"));
                return port != 0 ? port : string(l, "inputCell").compareTo(
                        string(r, "inputCell"));
            }
        });
        for (JsonElement element : ordered) {
            if (!element.isJsonObject()) {
                bindings.add(alphaCanonical(element, alpha));
                continue;
            }
            JsonObject source = element.getAsJsonObject();
            JsonObject stable = new JsonObject();
            stable.addProperty("schemaVersion", integer(source,
                    "schemaVersion", -1));
            stable.addProperty("kind", string(source, "kind"));
            stable.addProperty("inputPort", string(source, "inputPort"));
            stable.addProperty("inputCell", string(source, "inputCell"));
            stable.addProperty("inputJavaType", string(source,
                    "inputJavaType"));
            stable.addProperty("inputJavaTypeDescriptor", string(source,
                    "inputJavaTypeDescriptor"));
            stable.addProperty("symbolizationPrefix", string(source,
                    "symbolizationPrefix"));
            stable.addProperty("symbolizationMode", string(source,
                    "symbolizationMode"));
            stable.addProperty("engineArrayId", alpha.array(string(source,
                    "engineArrayId")));
            stable.addProperty("engineArrayIdAuthority", string(source,
                    "engineArrayIdAuthority"));
            stable.addProperty("objectTokenAuthority", string(source,
                    "objectTokenAuthority"));
            stable.addProperty("symbolizationIdentityAuthority",
                    string(source, "symbolizationIdentityAuthority"));
            stable.addProperty("sameArrayObjectTokenVerified", bool(source,
                    "sameArrayObjectTokenVerified", false));
            stable.addProperty("captureAuthority", string(source,
                    "captureAuthority"));
            stable.addProperty("complete", bool(source, "complete", false));
            bindings.add(alphaCanonical(stable, alpha));
        }
        Collections.sort(bindings);
        return canonical(GSON.toJsonTree(bindings));
    }

    private static void copyStable(JsonObject from, JsonObject to,
                                   String field) {
        JsonElement value = from.get(field);
        if (value != null) to.add(field, value.deepCopy());
    }

    private static JsonElement stripVolatileIdentity(JsonElement value) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return value == null ? JsonNull.INSTANCE : value.deepCopy();
        }
        if (value.isJsonArray()) {
            JsonArray result = new JsonArray();
            for (JsonElement element : value.getAsJsonArray()) {
                result.add(stripVolatileIdentity(element));
            }
            return result;
        }
        JsonObject result = new JsonObject();
        for (Map.Entry<String, JsonElement> entry
                : value.getAsJsonObject().entrySet()) {
            String key = entry.getKey().toLowerCase();
            if (key.contains("objecttoken")
                    || key.endsWith("activationid")
                    || "entryreadobservationid".equals(key)) continue;
            result.add(entry.getKey(), stripVolatileIdentity(
                    entry.getValue()));
        }
        return result;
    }

    /**
     * Canonicalizes engine IR modulo names allocated by one JVM execution.
     * Canonical region ports remain literal because they are the formal
     * parameters/results that intentionally connect paths and regions.
     */
    private static String alphaCanonical(JsonElement value,
                                         AlphaNormalizer alpha) {
        if (value == null || value.isJsonNull()) return "null";
        if (value.isJsonPrimitive()) {
            return GSON.toJson(value.getAsJsonPrimitive());
        }
        if (value.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement element : value.getAsJsonArray()) {
                if (!first) result.append(',');
                first = false;
                result.append(alphaCanonical(element, alpha));
            }
            return result.append(']').toString();
        }

        JsonObject object = value.getAsJsonObject();
        String type = string(object, "_type");
        StringBuilder result = new StringBuilder("{");
        boolean first = true;
        for (String key : new TreeSet<>(object.keySet())) {
            if (!first) result.append(',');
            first = false;
            result.append(GSON.toJson(key)).append(':');
            JsonElement field = object.get(key);
            if ("_exp".equals(key)
                    && ("SymbolExpression".equals(type)
                    || "ConSymbolExp".equals(type))
                    && field != null && field.isJsonPrimitive()) {
                result.append(GSON.toJson(alpha.symbol(
                        field.getAsString())));
            } else if ("_count".equals(key)
                    && "PlaceholderExpression".equals(type)
                    && field != null && field.isJsonPrimitive()) {
                result.append(GSON.toJson(alpha.placeholder(
                        string(object, "_place_holder_func"),
                        field.getAsString())));
            } else if ("_arr_str".equals(key)
                    && "_array_expr".equals(type)
                    && field != null && field.isJsonPrimitive()) {
                result.append(GSON.toJson(alpha.array(
                        field.getAsString())));
            } else {
                result.append(alphaCanonical(field, alpha));
            }
        }
        return result.append('}').toString();
    }

    private static final class AlphaNormalizer {
        private final Set<String> canonicalPorts = new LinkedHashSet<>();
        private final Map<String, String> symbols = new LinkedHashMap<>();
        private final Map<String, String> placeholders = new LinkedHashMap<>();
        private final Map<String, String> arrays = new LinkedHashMap<>();

        private AlphaNormalizer(JsonObject summary) {
            collectPortArray(summary.get("symbolicInputs"));
            collectPortObject(summary.get("requestedOutput"));
            JsonElement outputs = summary.get("outputExpressions");
            if (outputs != null && outputs.isJsonObject()) {
                for (String port : outputs.getAsJsonObject().keySet()) {
                    addPort(port);
                }
            }
            for (JsonElement element : RegionPathWorklist.array(summary,
                    "heapEffects")) {
                if (!element.isJsonObject()) continue;
                JsonObject effect = element.getAsJsonObject();
                addPort(string(effect, "inputPort"));
                addPort(string(effect, "outputPort"));
            }
            for (JsonElement element : RegionPathWorklist.array(summary,
                    "heapStateInitializers")) {
                if (!element.isJsonObject()) continue;
                JsonObject initializer = element.getAsJsonObject();
                addPort(string(initializer, "statePort"));
                addPort(string(initializer, "requestedOutputPort"));
            }
            for (JsonElement element : RegionPathWorklist.array(summary,
                    "engineArrayInputBindings")) {
                if (element.isJsonObject()) {
                    addPort(string(element.getAsJsonObject(), "inputPort"));
                }
            }
            for (JsonElement element : RegionPathWorklist.array(summary,
                    "dynamicFieldBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject selector = RegionPathWorklist.object(
                        element.getAsJsonObject(),
                        "mapProjectionSelector");
                addPort(string(selector, "mapInputPort"));
                addPort(string(selector, "outputPort"));
            }
        }

        private void collectPortArray(JsonElement value) {
            if (value == null || !value.isJsonArray()) return;
            for (JsonElement element : value.getAsJsonArray()) {
                if (element.isJsonPrimitive()) {
                    addPort(element.getAsString());
                } else if (element.isJsonObject()) {
                    collectPortObject(element);
                }
            }
        }

        private void collectPortObject(JsonElement value) {
            if (value == null || !value.isJsonObject()) return;
            JsonObject object = value.getAsJsonObject();
            addPort(string(object, "portId"));
            addPort(string(object, "symbol"));
            addPort(string(object, "inputPort"));
            addPort(string(object, "outputPort"));
        }

        private void addPort(String candidate) {
            if (looksLikeCanonicalPort(candidate)) {
                canonicalPorts.add(candidate);
            }
        }

        private String symbol(String raw) {
            if (containsCanonicalPort(raw)) return raw;
            return alpha(symbols, raw, "@symbol.");
        }

        private String placeholder(String function, String count) {
            return alpha(placeholders, firstNonBlank(function, "unknown")
                    + "\u0000" + firstNonBlank(count, "0"),
                    "@placeholder.");
        }

        private String array(String raw) {
            return alpha(arrays, raw, "@array.");
        }

        private boolean containsCanonicalPort(String raw) {
            if (looksLikeCanonicalPort(raw)) return true;
            for (String port : canonicalPorts) {
                int start = raw.indexOf(port);
                while (start >= 0) {
                    int end = start + port.length();
                    boolean left = start == 0 || raw.charAt(start - 1) == '_';
                    boolean right = end == raw.length()
                            || raw.charAt(end) == '_';
                    if (left && right) return true;
                    start = raw.indexOf(port, start + 1);
                }
            }
            return false;
        }

        private static String alpha(Map<String, String> values, String raw,
                                    String prefix) {
            String existing = values.get(raw);
            if (existing != null) return existing;
            String normalized = prefix + values.size();
            values.put(raw, normalized);
            return normalized;
        }

        private static boolean looksLikeCanonicalPort(String value) {
            String candidate = firstNonBlank(value);
            return candidate.startsWith("REGION.")
                    && (candidate.contains(".in.")
                    || candidate.contains(".out."));
        }
    }

    private static void component(StringBuilder output, String value) {
        String safe = value == null ? "" : value;
        output.append(safe.length()).append(':').append(safe).append('|');
    }

    private static String sha256(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(value.getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte current : bytes) {
                result.append(String.format("%02x", current & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException exception) {
            throw new IllegalStateException(exception);
        }
    }

    private static void increment(Map<String, Integer> values, String key) {
        Integer previous = values.get(key);
        values.put(key, previous == null ? 1 : previous + 1);
    }

    private static List<JsonObject> safe(List<JsonObject> values) {
        return values == null ? Collections.<JsonObject>emptyList() : values;
    }

    private static JsonObject object(JsonObject parent, String name) {
        if (parent == null) return new JsonObject();
        JsonElement value = parent.get(name);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static JsonArray array(JsonObject parent, String name) {
        if (parent == null) return new JsonArray();
        JsonElement value = parent.get(name);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static String string(JsonObject object, String name) {
        if (object == null) return "";
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject object, String name,
                                boolean fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject object, String name, int fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static JsonElement copy(JsonElement value, JsonElement fallback) {
        return value == null || value.isJsonNull()
                ? fallback.deepCopy() : value.deepCopy();
    }

    private static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }
}
