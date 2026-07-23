package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
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

    public enum State {
        NOT_STARTED,
        PENDING,
        CLOSED,
        GAPPED
    }

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

    private static String stableFlipKey(String regionId,
                                        String outputScopeIdentity,
                                        String siteId,
                                        int occurrence,
                                        boolean desiredOutcome,
                                        String prefixIdentity,
                                        String dynamicBindingIdentity) {
        StringBuilder value = new StringBuilder();
        component(value, regionId);
        component(value, outputScopeIdentity);
        component(value, prefixIdentity);
        component(value, siteId);
        component(value, String.valueOf(occurrence));
        component(value, String.valueOf(desiredOutcome));
        component(value, dynamicBindingIdentity);
        return sha256(value.toString());
    }

    /**
     * Content identity of one canonical output-closure path, independent of
     * activation ids.
     */
    public static String stablePathKey(JsonObject summary) {
        return stablePathKey(summary, OutputScope.from(summary, null));
    }

    private static String stablePathKey(JsonObject summary,
                                        OutputScope outputScope) {
        AlphaNormalizer alpha = new AlphaNormalizer(summary);
        StringBuilder value = new StringBuilder();
        component(value, string(summary, "regionId"));
        component(value, outputScope.identity);
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
        private final Set<String> observedFlipKeys = new LinkedHashSet<>();
        private final Set<String> witnessedBranchPositions =
                new LinkedHashSet<>();
        private final Map<String, Integer> pathCountByRegion =
                new LinkedHashMap<>();
        private final Map<JsonObject, List<SummaryBranchMapping>>
                branchMappings = new IdentityHashMap<>();
        private final Map<JsonObject, String> branchMappingIssues =
                new IdentityHashMap<>();

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
            for (JsonObject summary : safe(summaries)) {
                if (RegionCaptureGoal.from(summary).isOutputClosure()) {
                    this.summaries.add(summary);
                }
            }
            for (JsonObject summary : this.summaries) {
                try {
                    branchMappings.put(summary,
                            SummaryBranchMapping.fromSummary(summary));
                } catch (IllegalArgumentException malformed) {
                    branchMappingIssues.put(summary,
                            malformed.getMessage());
                }
            }
            Collections.sort(this.summaries, Comparator.comparing(value ->
                    string(value, "regionId") + "\n"
                            + stablePathKey(value)));
        }

        private Result run() {
            indexWitnessedBranchPositions();
            indexObservedFlipCoverage();
            Set<String> seenPaths = new LinkedHashSet<>();
            Set<String> observedRegions = new TreeSet<>();
            Map<String, OutputScope> observedClosureScopes =
                    new LinkedHashMap<>();
            for (JsonObject activation : activations.values()) {
                if (RegionCaptureGoal.from(activation).isOutputClosure()) {
                    OutputScope scope = OutputScope.from(null, activation);
                    observedClosureScopes.put(scope.identity, scope);
                }
            }
            for (JsonObject summary : summaries) {
                String region = string(summary, "regionId");
                if (region.isEmpty()) continue;
                JsonObject activation = activations.get(string(summary,
                        "activationId"));
                RegionCaptureGoal goal = RegionCaptureGoal.from(
                        activation == null ? summary : activation);
                if (!goal.isOutputClosure()) continue;
                OutputScope outputScope = OutputScope.from(summary,
                        activation);

                String pathKey = stablePathKey(summary, outputScope);
                if (!seenPaths.add(region + "\n" + pathKey)) continue;
                observedRegions.add(region);
                observedClosureScopes.put(outputScope.identity,
                        outputScope);
                increment(pathCountByRegion, region);
                String branchMappingIssue = branchMappingIssues.get(summary);
                if (branchMappingIssue != null) {
                    gap("INVALID_BRANCH_MAPPING_SCHEMA",
                            branchMappingIssue, region, pathKey, "", -1);
                    continue;
                }
                if (!bool(summary, "relationallyComplete", false)) {
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
                    gap("BOUND_REACHED", "MAX_WALL_CLOCK", region,
                            pathKey, "", -1);
                    break;
                }
                planSummary(summary, activation, outputScope, pathKey,
                        branchMappings.get(summary));
                if (tasks.size() >= bounds.maxTasks) break;
            }

            JsonObject manifest = manifest(seenPaths.size(),
                    observedRegions, observedClosureScopes);
            return new Result(tasks, manifest);
        }

        private void planSummary(
                JsonObject summary, JsonObject activation,
                OutputScope outputScope, String pathKey,
                List<SummaryBranchMapping> mappings) {
            JsonArray conditions = array(summary, "pathCondition");
            List<SummaryBranchMapping> candidates = new ArrayList<>();
            for (SummaryBranchMapping mapping : mappings) {
                String site = mapping.siteId();
                if (!outputScope.branchSites.contains(site)) {
                    continue;
                }
                if (mapping.isConcreteObservation()) {
                    if (!mapping.isExplore()
                            || coveredConcreteObservation(
                            outputScope, mapping)) {
                        continue;
                    }
                    gap("UNMAPPED_BRANCH", "NO_NORMALIZED_CONDITION",
                            string(summary, "regionId"), pathKey, site,
                            mapping.occurrence());
                    continue;
                }
                if (!mapping.isExplore()) continue;
                candidates.add(mapping);
            }
            // Classic depth-first concolic order: flip the latest relevant
            // decision first, then progressively shorter prefixes.
            Collections.sort(candidates, (left, right) -> {
                int byIndex = Integer.compare(right.summaryPcIndex(),
                        left.summaryPcIndex());
                if (byIndex != 0) return byIndex;
                int bySite = left.siteId().compareTo(right.siteId());
                if (bySite != 0) return bySite;
                return Integer.compare(left.occurrence(),
                        right.occurrence());
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
                emitTask(summary, activation, outputScope, pathKey, conditions,
                        mappings, candidates.get(index));
            }
        }

        private void emitTask(
                JsonObject summary, JsonObject activation,
                OutputScope outputScope, String pathKey,
                JsonArray conditions, List<SummaryBranchMapping> mappings,
                SummaryBranchMapping mapping) {
            int conditionIndex = mapping.summaryPcIndex();
            BranchReplayPlan replay;
            try {
                replay = BranchReplayPlan.fromSummary(summary, mappings,
                        mapping);
            } catch (IllegalArgumentException incompleteWitness) {
                gap("INVALID_BRANCH_WITNESS_PREFIX",
                        "BRANCH_WITNESS_OR_NON_BRANCH_CONTEXT_DOES_NOT_"
                                + "PARTITION_SUMMARY_PC_PREFIX",
                        string(summary, "regionId"), pathKey,
                        mapping.siteId(), mapping.occurrence());
                return;
            }
            JsonArray prefix = new JsonArray();
            for (int index = 0; index < conditionIndex; index++) {
                prefix.add(conditions.get(index).deepCopy());
            }
            BranchReplayContract replayContract = replay.replayContract();
            boolean desired = replayContract.requiredTakenOutcome();
            String region = string(summary, "regionId");
            String site = replayContract.source().siteId();
            int occurrence = replayContract.source().occurrence();
            AlphaNormalizer alpha = new AlphaNormalizer(summary);
            String key = stableFlipKey(region, outputScope.identity, site,
                    occurrence, desired, alphaCanonical(prefix, alpha),
                    stableRuntimeBindings(summary, alpha));

            JsonObject previous = records.get(key);
            if (previous != null && terminal(previous)) {
                if (gapStatus(previous)) {
                    gap("EXPLORATION_GAP", firstNonBlank(string(previous,
                                    "reason"), string(previous, "status")),
                            region, pathKey, site, occurrence);
                }
                return;
            }
            if (observedFlipKeys.contains(key)) {
                // The task constrains only the retained prefix plus the
                // selected edge (DROP_OLD_SUFFIX).  A complete admitted
                // summary with the same canonical prefix, requested output,
                // runtime bindings, site, occurrence, and desired outcome is
                // therefore direct evidence that this exact flip frontier
                // has already been executed.  Later suffix decisions remain
                // independently enumerable from that observed summary.
                return;
            }
            if (!emitted.add(key)) {
                return;
            }

            JsonObject task = new JsonObject();
            task.addProperty("schemaVersion", 3);
            task.addProperty("kind", "REGION_PATH_FLIP");
            task.addProperty("queryKey", key);
            task.addProperty("regionId", region);
            task.add("captureGoal",
                    RegionCaptureGoal.outputClosure().toJson());
            task.addProperty("sourceSummaryId", string(summary, "summaryId"));
            task.addProperty("sourcePathKey", pathKey);
            task.addProperty("sourceActivationId", string(summary,
                    "activationId"));
            task.addProperty("rootMethod", firstNonBlank(string(summary,
                    "rootMethod"), string(activation, "rootMethod")));
            task.add(OutputClosureContract.FIELD,
                    outputScope.contract.toJson());
            task.addProperty("regionInstanceId",
                    outputScope.contract.producer().regionInstanceId());
            task.addProperty("rootCallId",
                    outputScope.contract.producer().rootCallId());
            task.addProperty("outputDemandKey",
                    outputScope.demandKey);
            task.addProperty("outputClosureFingerprint",
                    outputScope.fingerprint);
            task.add("replayContract", replayContract.toJson());
            task.add("solverPathContext",
                    replay.solverPathContext().toJson());
            task.add("dynamicFieldBindings", array(summary,
                    "dynamicFieldBindings").deepCopy());
            task.add("engineArrayInputBindings", array(summary,
                    "engineArrayInputBindings").deepCopy());
            task.addProperty("status", "PENDING_SOLVE");
            task.addProperty("dynamicIdsExcludedFromQueryKey", true);
            tasks.add(task);
        }

        /**
         * Indexes only predicates whose immutable witness is an exact member
         * of an admitted summary path condition.  This is later used to
         * distinguish a genuine missing symbolic frontier from a VM-attested
         * concrete occurrence of an already modeled static branch position.
         */
        private void indexWitnessedBranchPositions() {
            for (JsonObject summary : summaries) {
                if (!bool(summary, "relationallyComplete", false)) {
                    continue;
                }
                JsonObject activation = activations.get(string(summary,
                        "activationId"));
                RegionCaptureGoal goal = RegionCaptureGoal.from(
                        activation == null ? summary : activation);
                if (!goal.isOutputClosure()) continue;
                OutputScope outputScope = OutputScope.from(summary,
                        activation);
                List<SummaryBranchMapping> mappings =
                        branchMappings.get(summary);
                if (mappings == null) continue;
                for (SummaryBranchMapping mapping : mappings) {
                    if (!mapping.isWitnessed()) continue;
                    witnessedBranchPositions.add(branchPosition(
                            outputScope, mapping));
                }
            }
        }

        /**
         * A concrete VM branch has no solver predicate and therefore is not
         * itself flippable.  It is safe to omit from the worklist only when
         * the same binary branch position has an immutable witnessed
         * predicate on another admitted path.  No predicate is
         * copied or synthesized; an otherwise unmapped branch remains a gap.
         */
        private boolean coveredConcreteObservation(
                OutputScope outputScope, SummaryBranchMapping mapping) {
            if (!mapping.isConcreteObservation()) return false;
            return witnessedBranchPositions.contains(branchPosition(
                    outputScope, mapping));
        }

        private String branchPosition(OutputScope outputScope,
                                      SummaryBranchMapping mapping) {
            return outputScope.identity + "\n" + mapping.siteId()
                    + "\n" + mapping.occurrence();
        }

        /**
         * Indexes exact branch frontiers already represented by complete
         * output-closure summaries.  This avoids replaying the reverse edge
         * after both sides of a branch have already been observed, while the
         * full stable flip identity prevents cross-prefix or cross-object
         * guesses.
         */
        private void indexObservedFlipCoverage() {
            for (JsonObject summary : summaries) {
                if (!bool(summary, "relationallyComplete", false)) {
                    continue;
                }
                String region = string(summary, "regionId");
                if (region.isEmpty()) continue;
                JsonObject activation = activations.get(string(summary,
                        "activationId"));
                RegionCaptureGoal goal = RegionCaptureGoal.from(
                        activation == null ? summary : activation);
                if (!goal.isOutputClosure()) continue;
                OutputScope outputScope = OutputScope.from(summary,
                        activation);

                JsonArray conditions = array(summary, "pathCondition");
                List<SummaryBranchMapping> mappings =
                        branchMappings.get(summary);
                if (mappings == null) continue;
                AlphaNormalizer alpha = new AlphaNormalizer(summary);
                for (SummaryBranchMapping mapping : mappings) {
                    if (!mapping.isWitnessed()
                            || !mapping.isExplore()) continue;
                    String site = mapping.siteId();
                    if (!outputScope.branchSites.contains(site)) {
                        continue;
                    }
                    int occurrence = mapping.occurrence();
                    int conditionIndex = mapping.summaryPcIndex();
                    JsonArray prefix = new JsonArray();
                    for (int index = 0; index < conditionIndex; index++) {
                        prefix.add(conditions.get(index).deepCopy());
                    }
                    observedFlipKeys.add(stableFlipKey(region,
                            outputScope.identity, site, occurrence,
                            mapping.sourceTakenOutcome(),
                            alphaCanonical(prefix, alpha),
                            stableRuntimeBindings(summary, alpha)));
                }
            }
        }

        private JsonObject manifest(int observedPathCount,
                                    Set<String> observedRegions,
                                    Map<String, OutputScope> closureScopes) {
            String regionId = manifestRegionId(observedRegions);
            if (observedRegions.size() > 1) {
                gap("MULTIPLE_REGION_SCOPE",
                        "REGION_PATH_WORKLIST_REQUIRES_ONE_REGION",
                        "", "", "", -1);
            }
            if (observedPathCount == 0) {
                gap("NO_OBSERVED_PATH_SEED",
                        "OUTPUT_CLOSURE_SEED_REQUIRED",
                        regionId, "", "", -1);
            }
            if (closureScopes.size() > 1) {
                gap("MULTIPLE_OUTPUT_CLOSURE_SCOPE",
                        "REGION_PATH_WORKLIST_REQUIRES_ONE_OUTPUT_CLOSURE",
                        regionId, "", "", -1);
            }

            State state = observedPathCount == 0
                    ? State.NOT_STARTED
                    : !gaps.isEmpty()
                    ? State.GAPPED
                    : tasks.isEmpty() ? State.CLOSED : State.PENDING;
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind", "REGION_PATH_WORKLIST");
            result.addProperty("regionId", regionId);
            result.addProperty("state", state.name());
            result.add("bounds", bounds.toJson());
            result.addProperty("observedPathCount", observedPathCount);
            result.addProperty("pendingTaskCount", tasks.size());
            if (closureScopes.size() == 1) {
                OutputScope scope = closureScopes.values().iterator().next();
                result.addProperty("outputDemandKey", scope.demandKey);
                result.addProperty("outputClosureFingerprint",
                        scope.fingerprint);
            }
            result.add("gaps", GSON.toJsonTree(gaps));
            return result;
        }

        private String manifestRegionId(Set<String> observedRegions) {
            if (observedRegions.size() == 1) {
                return observedRegions.iterator().next();
            }
            if (!observedRegions.isEmpty()) return "";

            Set<String> inputRegions = new TreeSet<>();
            for (JsonObject summary : summaries) {
                String region = string(summary, "regionId");
                if (!region.isEmpty()) inputRegions.add(region);
            }
            for (JsonObject activation : activations.values()) {
                String region = string(activation, "regionId");
                if (!region.isEmpty()) inputRegions.add(region);
            }
            return inputRegions.size() == 1
                    ? inputRegions.iterator().next() : "";
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

    private static final class OutputScope {
        private final OutputClosureContract contract;
        private final Set<String> branchSites;
        private final String identity;
        private final String demandKey;
        private final String fingerprint;

        private OutputScope(OutputClosureContract contract,
                            Set<String> branchSites,
                            String identity,
                            String demandKey,
                            String fingerprint) {
            this.contract = contract;
            this.branchSites = branchSites;
            this.identity = identity;
            this.demandKey = demandKey;
            this.fingerprint = fingerprint;
        }

        private static OutputScope from(JsonObject summary,
                                        JsonObject activation) {
            OutputClosureContract summaryContract = decode(summary);
            OutputClosureContract activationContract =
                    decode(activation);
            if (summaryContract != null && activationContract != null
                    && (!summaryContract.demandKey().equals(
                    activationContract.demandKey())
                    || !summaryContract.closureFingerprint().equals(
                    activationContract.closureFingerprint()))) {
                throw new IllegalArgumentException(
                        "summary and activation outputClosure conflict");
            }
            OutputClosureContract contract = summaryContract != null
                    ? summaryContract : activationContract;
            if (contract == null) {
                throw new IllegalArgumentException(
                        "canonical outputClosure is required");
            }
            Set<String> sites = new LinkedHashSet<>(
                    contract.executionScope().branchSites());
            String demand = contract.demandKey();
            String fingerprint = contract.closureFingerprint();
            return new OutputScope(contract, sites,
                    "OUTPUT_CLOSURE_V1\n" + demand + "\n" + fingerprint,
                    demand, fingerprint);
        }

        private static OutputClosureContract decode(JsonObject value) {
            if (value == null) return null;
            return OutputClosureCodec.decode(value);
        }
    }

    private static boolean terminal(JsonObject record) {
        String status = string(record, "status");
        return "UNSAT".equals(status)
                || "TRANSITION_VALIDATED".equals(status)
                || "NO_RUNTIME_TRANSITION_EVIDENCE".equals(status)
                || "EXECUTED_NEW_PATH".equals(status)
                || "EXECUTED_DUPLICATE_PATH".equals(status)
                || "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY".equals(status)
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
