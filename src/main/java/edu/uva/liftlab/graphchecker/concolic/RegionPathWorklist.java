package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

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
                              List<JsonObject> executionTasks,
                              List<JsonObject> explorationRecords,
                              Bounds bounds) {
        Bounds effective = bounds == null ? Bounds.defaults() : bounds;
        return new Planner(summaries, executionTasks, explorationRecords,
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
     * execution task ids.
     */
    public static String stablePathKey(JsonObject summary) {
        ExplorationScope scope = ExplorationScope.from(summary, null);
        AlphaNormalizer alpha = new AlphaNormalizer(summary);
        return stablePathKey(summary, scope, alpha,
                stableRuntimeBindings(summary, alpha));
    }

    private static String stablePathKey(JsonObject summary,
                                        ExplorationScope scope,
                                        AlphaNormalizer alpha,
                                        String runtimeBindings) {
        StringBuilder value = new StringBuilder();
        component(value, string(summary, "regionId"));
        component(value, scope.identity);
        component(value, alphaCanonical(summary.get("pathCondition"), alpha));
        component(value, alphaCanonical(summary.get("outputExpressions"), alpha));
        component(value, alphaCanonical(summary.get("heapEffects"), alpha));
        component(value, runtimeBindings);
        component(value, string(summary, "normalExit"));
        component(value, string(summary, "exceptionType"));
        return sha256(value.toString());
    }

    /** Canonical, once-decoded view consumed by every worklist phase. */
    private static final class SummaryPath {
        private final JsonObject summary;
        private final String region;
        private final ExplorationScope scope;
        private final AlphaNormalizer alpha;
        private final String runtimeBindings;
        private final String pathKey;
        private final List<SummaryBranchMapping> mappings;
        private final String mappingIssue;

        private SummaryPath(JsonObject summary, ExplorationScope scope,
                            AlphaNormalizer alpha, String runtimeBindings,
                            String pathKey,
                            List<SummaryBranchMapping> mappings,
                            String mappingIssue) {
            this.summary = summary;
            this.region = string(summary, "regionId");
            this.scope = scope;
            this.alpha = alpha;
            this.runtimeBindings = runtimeBindings;
            this.pathKey = pathKey;
            this.mappings = mappings;
            this.mappingIssue = mappingIssue;
        }

        private static SummaryPath from(JsonObject summary, JsonObject task) {
            ExplorationScope scope = ExplorationScope.from(summary, task);
            AlphaNormalizer alpha = new AlphaNormalizer(summary);
            String bindings = stableRuntimeBindings(summary, alpha);
            String pathKey = stablePathKey(summary, scope, alpha, bindings);
            List<SummaryBranchMapping> mappings = Collections.emptyList();
            String issue = "";
            try {
                mappings = SummaryBranchMapping.fromSummary(summary);
            } catch (IllegalArgumentException malformed) {
                issue = firstNonBlank(malformed.getMessage(), "UNKNOWN");
            }
            return new SummaryPath(summary, scope, alpha, bindings, pathKey,
                    mappings, issue);
        }

        private JsonArray prefixBefore(int conditionIndex) {
            JsonArray prefix = new JsonArray();
            JsonArray conditions = array(summary, "pathCondition");
            for (int index = 0; index < conditionIndex; index++) {
                prefix.add(conditions.get(index).deepCopy());
            }
            return prefix;
        }

        private String flipKey(SummaryBranchMapping mapping,
                               boolean desiredOutcome) {
            return stableFlipKey(region, scope.identity, mapping.siteId(),
                    mapping.occurrence(), desiredOutcome,
                    alphaCanonical(prefixBefore(mapping.summaryPcIndex()),
                            alpha),
                    runtimeBindings);
        }
    }

    private static final class Planner {
        private final Bounds bounds;
        private final Map<String, JsonObject> taskById =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> records = new LinkedHashMap<>();
        private final List<SummaryPath> paths = new ArrayList<>();
        private final List<JsonObject> tasks = new ArrayList<>();
        private final List<JsonObject> gaps = new ArrayList<>();
        private final List<JsonObject> deferredObservations =
                new ArrayList<>();
        private final Set<String> gapKeys = new LinkedHashSet<>();
        private final Set<String> deferredObservationKeys =
                new LinkedHashSet<>();
        private final Set<String> emitted = new LinkedHashSet<>();
        private final Set<String> observedFlipKeys = new LinkedHashSet<>();
        private final Set<String> witnessedBranchPositions =
                new LinkedHashSet<>();
        private final Map<String, Integer> pathCountByRegion =
                new LinkedHashMap<>();
        private Planner(List<JsonObject> summaries,
                        List<JsonObject> executionTasks,
                        List<JsonObject> explorationRecords,
                        Bounds bounds) {
            this.bounds = bounds;
            for (JsonObject task : safe(executionTasks)) {
                String id = string(task, "taskId");
                if (!id.isEmpty()) this.taskById.put(id, task);
            }
            for (JsonObject record : safe(explorationRecords)) {
                String key = string(record, "queryKey");
                if (!key.isEmpty()) this.records.put(key, record);
            }
            for (JsonObject summary : safe(summaries)) {
                paths.add(SummaryPath.from(summary, taskById.get(
                        string(summary, "taskId"))));
            }
            Collections.sort(paths, Comparator.comparing(value ->
                    value.region + "\n" + value.pathKey));
        }

        private Result run() {
            indexObservedCoverage();
            Set<String> seenPaths = new LinkedHashSet<>();
            Set<String> observedRegions = new TreeSet<>();
            Map<String, ExplorationScope> observedScopes =
                    new LinkedHashMap<>();
            for (JsonObject task : taskById.values()) {
                ClosureGoalKind.fromTask(task);
                ExplorationScope scope = ExplorationScope.from(null,
                        task);
                observedScopes.put(scope.identity, scope);
            }
            for (SummaryPath path : paths) {
                JsonObject summary = path.summary;
                String region = path.region;
                if (region.isEmpty()) continue;
                String pathKey = path.pathKey;
                if (!seenPaths.add(region + "\n" + pathKey)) continue;
                observedRegions.add(region);
                observedScopes.put(path.scope.identity, path.scope);
                increment(pathCountByRegion, region);
                if (!path.mappingIssue.isEmpty()) {
                    gap("INVALID_BRANCH_MAPPING_SCHEMA",
                            path.mappingIssue, region, pathKey, "", -1);
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
                planSummary(path);
                if (tasks.size() >= bounds.maxTasks) break;
            }

            int remainingPathSlots = bounds.maxPathsPerRegion
                    - seenPaths.size();
            if (!tasks.isEmpty() && remainingPathSlots <= 0) {
                gap("BOUND_REACHED", "MAX_PATHS_PER_REGION",
                        manifestRegionId(observedRegions),
                        "", "", -1);
            } else if (tasks.size() > remainingPathSlots) {
                tasks.subList(remainingPathSlots, tasks.size()).clear();
            }

            JsonObject manifest = manifest(!seenPaths.isEmpty(),
                    observedRegions, observedScopes);
            List<JsonObject> relations = new ArrayList<>();
            if (State.CLOSED.name().equals(string(manifest, "state"))) {
                relations.addAll(closedRelations(observedScopes));
                if (!gaps.isEmpty()) {
                    relations.clear();
                    manifest = manifest(!seenPaths.isEmpty(),
                            observedRegions, observedScopes);
                }
            }
            return new Result(tasks, manifest, relations);
        }

        private List<JsonObject> closedRelations(
                Map<String, ExplorationScope> observedScopes) {
            if (observedScopes.size() != 1) {
                return Collections.emptyList();
            }
            ExplorationScope scope =
                    observedScopes.values().iterator().next();
            if (!scope.goalKind.capturesOutputRelation()) {
                return Collections.emptyList();
            }
            if (scope.contract == null) {
                gap("INVALID_OUTPUT_CLOSURE",
                        "CANONICAL_OUTPUT_CLOSURE_REQUIRED",
                        "", "", "", -1);
                return Collections.emptyList();
            }

            String region = scope.contract.producer().regionId();
            String outputIdentity = CanonicalJson.render(
                    scope.contract.toJson());
            Map<String, String> payloadByPath = new LinkedHashMap<>();
            Map<String, JsonObject> caseByPath = new LinkedHashMap<>();
            Map<String, JsonObject> bindingsByKey = new LinkedHashMap<>();
            for (SummaryPath path : paths) {
                JsonObject summary = path.summary;
                if (!path.scope.goalKind.capturesOutputRelation()) {
                    continue;
                }
                OutputClosureContract contract = path.scope.contract;
                if (!outputIdentity.equals(CanonicalJson.render(
                        contract.toJson()))) {
                    gap("OUTPUT_CLOSURE_SCOPE_MISMATCH",
                            "CLOSED_PATHS_HAVE_DIFFERENT_OUTPUT_CLOSURES",
                            path.region, "", "", -1);
                    continue;
                }

                String pathKey = path.pathKey;
                String payload = stableCasePayload(summary);
                String previous = payloadByPath.putIfAbsent(pathKey, payload);
                if (previous != null) {
                    if (!previous.equals(payload)) {
                        gap("CONFLICTING_DUPLICATE_PATH_PAYLOAD",
                                "PATH_CERTIFICATES_DISAGREE",
                                region, pathKey, "", -1);
                    }
                } else if (contract.members().size() > 1
                        && !exactOutputExpressions(summary,
                        contract.outputPorts())) {
                    gap("JOINT_OUTPUT_EXPRESSION_SET_MISMATCH",
                            "OUTPUT_EXPRESSION_SET_DOES_NOT_MATCH_DEMAND",
                            region, pathKey, "", -1);
                } else {
                    caseByPath.put(pathKey, pathCase(summary, pathKey));
                }
                for (JsonElement element : array(summary, "edgeBindings")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    bindingsByKey.put(CanonicalJson.render(binding),
                            binding.deepCopy());
                }
            }
            if (!gaps.isEmpty()) {
                return Collections.emptyList();
            }
            if (caseByPath.isEmpty()) {
                gap("NO_VALID_OUTPUT_CLOSURE_RELATIONS",
                        "CLOSED_OUTPUT_SCOPE_HAS_NO_CASES",
                        region, "", "", -1);
                return Collections.emptyList();
            }

            JsonArray cases = new JsonArray();
            List<String> pathKeys = new ArrayList<>(caseByPath.keySet());
            Collections.sort(pathKeys);
            for (String pathKey : pathKeys) {
                cases.add(caseByPath.get(pathKey));
            }
            JsonArray mergedBindings = new JsonArray();
            List<String> bindingKeys =
                    new ArrayList<>(bindingsByKey.keySet());
            Collections.sort(bindingKeys);
            for (String key : bindingKeys) {
                mergedBindings.add(bindingsByKey.get(key));
            }

            JsonObject relation = new JsonObject();
            relation.addProperty("schemaVersion", 1);
            relation.addProperty("kind", "GUARDED_PATH_MERGE");
            relation.add("cases", cases);
            String relationHash = sha256(region + "\n"
                    + outputIdentity + "\n"
                    + CanonicalJson.render(cases));
            JsonObject merged = new JsonObject();
            merged.addProperty("schemaVersion", 1);
            merged.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
            merged.addProperty("summaryId", "SUMMARY." + region
                    + ".MERGED." + relationHash);
            merged.addProperty("regionId", region);
            merged.addProperty("goalId", scope.goalId);
            scope.goalKind.writeToTask(merged);
            OutputClosureCodec.writeTo(merged, scope.contract);
            merged.add("edgeBindings", mergedBindings);
            merged.add("regionRelation", relation);
            merged.addProperty("relationallyComplete", true);
            return Collections.singletonList(merged);
        }

        private JsonObject pathCase(JsonObject summary, String pathKey) {
            JsonObject item = new JsonObject();
            item.addProperty("caseId", "CASE." + pathKey);
            JsonObject guard = new JsonObject();
            guard.addProperty("kind", "PATH_CONDITION");
            guard.add("conditions", array(summary,
                    "pathCondition").deepCopy());
            item.add("guard", guard);
            item.add("outputExpressions", object(summary,
                    "outputExpressions").deepCopy());
            for (String field : new String[]{"heapStateInitializers",
                    "heapObservations", "finiteMapSnapshots",
                    "dynamicFieldBindings", "engineArrayInputBindings",
                    "vmIntrinsicPlaceholderBindings",
                    "unforcedEnvironmentValidationRequirements",
                    "heapEffects"}) {
                item.add(field, array(summary, field).deepCopy());
            }
            item.addProperty("sourceTaskId", string(summary, "taskId"));
            return item;
        }

        private String stableCasePayload(JsonObject summary) {
            JsonObject stable = new JsonObject();
            for (String field : new String[]{"heapStateInitializers",
                    "heapObservations", "finiteMapSnapshots",
                    "vmIntrinsicPlaceholderBindings",
                    "unforcedEnvironmentValidationRequirements"}) {
                stable.add(field, array(summary, field).deepCopy());
            }
            return CanonicalJson.render(stable);
        }

        private boolean exactOutputExpressions(
                JsonObject summary, Set<String> outputPorts) {
            JsonElement encoded = summary.get("outputExpressions");
            return encoded != null && encoded.isJsonObject()
                    && new TreeSet<>(encoded.getAsJsonObject().keySet())
                    .equals(new TreeSet<>(outputPorts));
        }

        private void planSummary(SummaryPath path) {
            List<SummaryBranchMapping> candidates = new ArrayList<>();
            for (SummaryBranchMapping mapping : path.mappings) {
                String site = mapping.siteId();
                if (!path.scope.branchSites.contains(site)) {
                    continue;
                }
                if (mapping.isConcreteObservation()) {
                    if (!mapping.isExplore()
                            || coveredConcreteObservation(
                            path.scope, mapping)) {
                        continue;
                    }
                    deferObservation("UNMAPPED_BRANCH",
                            "NO_NORMALIZED_CONDITION",
                            path.region, path.pathKey, site,
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
                gap("BOUND_REACHED", "MAX_FLIPS_PER_PATH", path.region,
                        path.pathKey, "", -1);
            }
            for (int index = 0; index < limit; index++) {
                if (tasks.size() >= bounds.maxTasks) {
                    gap("BOUND_REACHED", "MAX_TASKS", path.region,
                            path.pathKey, "", -1);
                    return;
                }
                emitTask(path, candidates.get(index));
            }
        }

        private void emitTask(SummaryPath path,
                              SummaryBranchMapping mapping) {
            JsonObject summary = path.summary;
            BranchReplayContract replay;
            try {
                replay = BranchReplayContract.fromSummary(summary,
                        path.mappings,
                        mapping);
            } catch (IllegalArgumentException incompleteWitness) {
                gap("INVALID_BRANCH_WITNESS_PREFIX",
                        "BRANCH_WITNESS_OR_NON_BRANCH_CONTEXT_DOES_NOT_"
                                + "PARTITION_SUMMARY_PC_PREFIX",
                        path.region, path.pathKey,
                        mapping.siteId(), mapping.occurrence());
                return;
            }
            boolean desired = replay.requiredTakenOutcome();
            String key = path.flipKey(mapping, desired);

            JsonObject previous = records.get(key);
            if (previous != null && terminal(previous)) {
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
            task.addProperty("regionId", path.region);
            task.addProperty("goalId", string(summary, "goalId"));
            path.scope.goalKind.writeToTask(task);
            task.addProperty("sourceSummaryId", string(summary, "summaryId"));
            task.addProperty("sourcePathKey", path.pathKey);
            task.addProperty("sourceTaskId", string(summary, "taskId"));
            if (path.scope.contract != null) {
                task.add(OutputClosureContract.FIELD,
                        path.scope.contract.toJson());
            }
            replay.addTo(task);
            task.add("dynamicFieldBindings", array(summary,
                    "dynamicFieldBindings").deepCopy());
            tasks.add(task);
        }

        /** Indexes exact witnessed positions and already explored frontiers. */
        private void indexObservedCoverage() {
            for (SummaryPath path : paths) {
                if (!bool(path.summary, "relationallyComplete", false)) {
                    continue;
                }
                for (SummaryBranchMapping mapping : path.mappings) {
                    if (!mapping.isWitnessed() || !mapping.isExplore()) {
                        continue;
                    }
                    witnessedBranchPositions.add(branchPosition(
                            path.scope, mapping));
                    if (!path.region.isEmpty()
                            && path.scope.branchSites.contains(
                            mapping.siteId())) {
                        observedFlipKeys.add(path.flipKey(mapping,
                                mapping.sourceTakenOutcome()));
                    }
                }
            }
        }

        private boolean coveredConcreteObservation(
                ExplorationScope scope, SummaryBranchMapping mapping) {
            return mapping.isConcreteObservation()
                    && witnessedBranchPositions.contains(branchPosition(
                    scope, mapping));
        }

        private String branchPosition(ExplorationScope scope,
                                      SummaryBranchMapping mapping) {
            return scope.identity + "\n" + mapping.siteId()
                    + "\n" + mapping.occurrence();
        }

        private JsonObject manifest(boolean hasObservedPath,
                                    Set<String> observedRegions,
                                    Map<String, ExplorationScope> scopes) {
            String regionId = manifestRegionId(observedRegions);
            if (observedRegions.size() > 1) {
                gap("MULTIPLE_REGION_SCOPE",
                        "REGION_PATH_WORKLIST_REQUIRES_ONE_REGION",
                        "", "", "", -1);
            }
            if (!hasObservedPath) {
                gap("NO_OBSERVED_PATH_SEED",
                        "REGION_PATH_SEED_REQUIRED",
                        regionId, "", "", -1);
            }
            if (scopes.size() > 1) {
                gap("MULTIPLE_EXPLORATION_SCOPE",
                        "REGION_PATH_WORKLIST_REQUIRES_ONE_SCOPE",
                        regionId, "", "", -1);
            }
            if (tasks.isEmpty()) {
                for (JsonObject observation : deferredObservations) {
                    gap(string(observation, "kind"),
                            string(observation, "reason"),
                            string(observation, "regionId"),
                            string(observation, "pathKey"),
                            string(observation, "siteId"),
                            integer(observation, "occurrence", -1));
                }
            }

            State state = !hasObservedPath
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
            if (scopes.size() == 1) {
                ExplorationScope scope = scopes.values().iterator().next();
                result.addProperty("goalId", scope.goalId);
                scope.goalKind.writeToTask(result);
                if (scope.contract != null) {
                    result.add(OutputClosureContract.FIELD,
                            scope.contract.toJson());
                }
            }
            result.add("gaps", GSON.toJsonTree(gaps));
            if (!tasks.isEmpty() && !deferredObservations.isEmpty()) {
                result.add("deferredObservations",
                        GSON.toJsonTree(deferredObservations));
            }
            return result;
        }

        private String manifestRegionId(Set<String> observedRegions) {
            if (observedRegions.size() == 1) {
                return observedRegions.iterator().next();
            }
            if (!observedRegions.isEmpty()) return "";

            Set<String> inputRegions = new TreeSet<>();
            for (SummaryPath path : paths) {
                if (!path.region.isEmpty()) inputRegions.add(path.region);
            }
            for (JsonObject task : taskById.values()) {
                String region = string(task, "regionId");
                if (!region.isEmpty()) inputRegions.add(region);
            }
            return inputRegions.size() == 1
                    ? inputRegions.iterator().next() : "";
        }

        private void gap(String kind, String reason, String region,
                         String pathKey, String site, int occurrence) {
            addIssue(gaps, gapKeys, kind, reason, region, pathKey, site,
                    occurrence);
        }

        private void deferObservation(String kind, String reason,
                                      String region, String pathKey,
                                      String site, int occurrence) {
            addIssue(deferredObservations, deferredObservationKeys, kind,
                    reason, region, pathKey, site, occurrence);
        }

        private void addIssue(List<JsonObject> destination, Set<String> keys,
                              String kind, String reason, String region,
                              String pathKey, String site, int occurrence) {
            String key = kind + "\n" + reason + "\n" + region + "\n"
                    + pathKey + "\n" + site + "\n" + occurrence;
            if (!keys.add(key)) return;
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("reason", reason);
            gap.addProperty("regionId", region);
            gap.addProperty("pathKey", pathKey);
            gap.addProperty("siteId", site);
            gap.addProperty("occurrence", occurrence);
            destination.add(gap);
        }

    }

    public static final class Bounds {
        public final int maxPathsPerRegion;
        public final int maxFlipsPerPath;
        public final int maxTasks;

        public Bounds(int maxPathsPerRegion, int maxFlipsPerPath,
                      int maxTasks) {
            this.maxPathsPerRegion = Math.max(1, maxPathsPerRegion);
            this.maxFlipsPerPath = Math.max(1, maxFlipsPerPath);
            this.maxTasks = Math.max(1, maxTasks);
        }

        public static Bounds defaults() {
            return new Bounds(64, 32, 256);
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("maxPathsPerRegion", maxPathsPerRegion);
            result.addProperty("maxFlipsPerPath", maxFlipsPerPath);
            result.addProperty("maxTasks", maxTasks);
            return result;
        }
    }

    public static final class Result {
        public final List<JsonObject> tasks;
        public final JsonObject manifest;
        public final List<JsonObject> relations;

        private Result(List<JsonObject> tasks, JsonObject manifest,
                       List<JsonObject> relations) {
            this.tasks = tasks;
            this.manifest = manifest;
            this.relations = relations;
        }
    }

    private static final class ExplorationScope {
        private final ClosureGoalKind goalKind;
        private final String goalId;
        private final OutputClosureContract contract;
        private final Set<String> branchSites;
        private final String identity;

        private ExplorationScope(ClosureGoalKind goalKind, String goalId,
                                 OutputClosureContract contract,
                                 Set<String> branchSites,
                                 String identity) {
            this.goalKind = goalKind;
            this.goalId = goalId;
            this.contract = contract;
            this.branchSites = branchSites;
            this.identity = identity;
        }

        private static ExplorationScope from(JsonObject summary,
                                             JsonObject executionTask) {
            JsonObject canonical = summary != null ? summary : executionTask;
            if (canonical == null) {
                throw new IllegalArgumentException(
                        "closure goal is required");
            }
            ClosureGoalKind goalKind = ClosureGoalKind.fromTask(canonical);
            String goalId = string(canonical, "goalId");
            if (goalId.isEmpty()) throw new IllegalArgumentException(
                    "closure goal is required");
            if (goalKind.capturesTargetReach()) {
                JsonObject source = executionTask != null
                        ? executionTask : canonical;
                Set<String> sites = new LinkedHashSet<>();
                String targetMethod = string(source, "targetMethod");
                for (JsonElement element : array(source, "branches")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject branch = element.getAsJsonObject();
                    if (!"EXPLORE".equals(string(branch, "policy"))) {
                        continue;
                    }
                    String site = string(branch, "siteId");
                    if (!site.isEmpty()
                            && (targetMethod.isEmpty()
                            || site.startsWith(targetMethod + "#"))) {
                        sites.add(site);
                    }
                }
                String region = firstNonBlank(string(source, "regionId"),
                        string(canonical, "regionId"));
                String instance = firstNonBlank(string(source,
                        "regionInstanceId"), string(canonical,
                        "regionInstanceId"));
                return new ExplorationScope(goalKind, goalId, null, sites,
                        "TARGET_REACH_CLOSURE_V1\n" + goalId + "\n"
                                + region + "\n" + instance + "\n"
                                + targetMethod);
            }
            OutputClosureContract contract = OutputClosureCodec.decode(
                    canonical);
            Set<String> sites = new LinkedHashSet<>(
                    contract.executionScope().branchSites());
            String demand = contract.demandKey();
            String fingerprint = contract.closureFingerprint();
            return new ExplorationScope(goalKind, goalId, contract, sites,
                    "OUTPUT_RELATION_CLOSURE_V1\n" + goalId + "\n"
                            + demand + "\n" + fingerprint);
        }
    }

    private static boolean terminal(JsonObject record) {
        String status = string(record, "status");
        return "UNSAT".equals(status)
                || "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY".equals(status)
                || "VALIDATED_FRESH_TARGET_PATH_FLIP_REPLAY".equals(status);
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
            copyStable(source, stable, "runtimeSymbolizationAuthority");
            copyStable(source, stable, "projectionEvidenceAuthority");
            copyStable(source, stable, "outputValidationMode");
            stable.addProperty("complete", bool(source, "complete", false));
            bindings.add(alphaCanonical(stripVolatileIdentity(stable),
                    alpha));
        }
        Collections.sort(bindings);
        return CanonicalJson.render(GSON.toJsonTree(bindings));
    }

    private static String stableRuntimeBindings(JsonObject summary,
                                                AlphaNormalizer alpha) {
        return stableDynamicBindings(summary, alpha) + "\n"
                + stableEngineArrayBindings(summary, alpha);
    }

    /**
     * Retains the semantic input/engine-array bijection while erasing the
     * task-local array id and object token allocated by one replay.
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
        Collections.sort(ordered, (left, right) -> {
            if (!left.isJsonObject() || !right.isJsonObject()) {
                return CanonicalJson.render(left).compareTo(
                        CanonicalJson.render(right));
            }
            JsonObject l = left.getAsJsonObject();
            JsonObject r = right.getAsJsonObject();
            int port = string(l, "inputPort").compareTo(
                    string(r, "inputPort"));
            return port != 0 ? port : string(l, "inputCell").compareTo(
                    string(r, "inputCell"));
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
            stable.addProperty("inputJavaTypeDescriptor", string(source,
                    "inputJavaTypeDescriptor"));
            stable.addProperty("engineArrayId", alpha.array(string(source,
                    "engineArrayId")));
            bindings.add(alphaCanonical(stable, alpha));
        }
        Collections.sort(bindings);
        return CanonicalJson.render(GSON.toJsonTree(bindings));
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
            for (JsonElement element : JsonFields.array(summary,
                    "heapEffects")) {
                if (!element.isJsonObject()) continue;
                JsonObject effect = element.getAsJsonObject();
                addPort(string(effect, "inputPort"));
                addPort(string(effect, "outputPort"));
            }
            for (JsonElement element : JsonFields.array(summary,
                    "heapStateInitializers")) {
                if (!element.isJsonObject()) continue;
                JsonObject initializer = element.getAsJsonObject();
                addPort(string(initializer, "statePort"));
                addPort(string(initializer, "requestedOutputPort"));
            }
            for (JsonElement element : JsonFields.array(summary,
                    "engineArrayInputBindings")) {
                if (element.isJsonObject()) {
                    addPort(string(element.getAsJsonObject(), "inputPort"));
                }
            }
            for (JsonElement element : JsonFields.array(summary,
                    "dynamicFieldBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject selector = object(
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

    private static void increment(Map<String, Integer> values, String key) {
        Integer previous = values.get(key);
        values.put(key, previous == null ? 1 : previous + 1);
    }

    private static List<JsonObject> safe(List<JsonObject> values) {
        return values == null ? Collections.<JsonObject>emptyList() : values;
    }

}
