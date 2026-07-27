package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Builds bounded branch-flip work for one region closure. */
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
        return new Planner(summaries, executionTasks, explorationRecords,
                bounds).run();
    }

    private static final class Planner {
        private final Bounds bounds;
        private final Map<String, JsonObject> taskById =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> records = new LinkedHashMap<>();
        private final List<PathObservation> paths = new ArrayList<>();
        private final List<JsonObject> tasks = new ArrayList<>();
        private final List<JsonObject> gaps = new ArrayList<>();
        private final Set<String> gapKeys = new LinkedHashSet<>();
        private final Set<String> emitted = new LinkedHashSet<>();
        private final Set<String> observedFlipKeys = new LinkedHashSet<>();
        private final Map<String, Integer> pathCountByRegion =
                new LinkedHashMap<>();
        private Planner(List<JsonObject> summaries,
                        List<JsonObject> executionTasks,
                        List<JsonObject> explorationRecords,
                        Bounds bounds) {
            this.bounds = bounds;
            for (JsonObject task : executionTasks) {
                String id = string(task, "taskId");
                if (!id.isEmpty()) this.taskById.put(id, task);
            }
            for (JsonObject record : explorationRecords) {
                String key = string(record, "queryKey");
                if (!key.isEmpty()) this.records.put(key, record);
            }
            for (JsonObject summary : summaries) {
                paths.add(PathObservation.decode(summary, taskById.get(
                        string(summary, "taskId"))));
            }
            Collections.sort(paths, Comparator.comparing(value ->
                    value.regionId() + "\n" + value.pathKey()));
        }

        private Result run() {
            indexObservedCoverage();
            Set<String> seenPaths = new LinkedHashSet<>();
            Set<String> observedRegions = new TreeSet<>();
            Map<String, PathObservation.Scope> observedScopes =
                    new LinkedHashMap<>();
            for (JsonObject task : taskById.values()) {
                PathObservation.Scope scope = PathObservation.Scope.decode(null,
                        task);
                observedScopes.put(scope.identity(), scope);
            }
            for (PathObservation path : paths) {
                String region = path.regionId();
                if (region.isEmpty()) continue;
                String pathKey = path.pathKey();
                if (!seenPaths.add(region + "\n" + pathKey)) continue;
                observedRegions.add(region);
                observedScopes.put(path.scope().identity(), path.scope());
                pathCountByRegion.merge(region, 1, Integer::sum);
                if (!path.branchMappingIssue().isEmpty()) {
                    gap("INVALID_BRANCH_MAPPING_SCHEMA",
                            path.branchMappingIssue(), region, pathKey, "", -1);
                    continue;
                }
                if (!path.relationallyComplete()) {
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
                    manifest.addProperty("state", State.GAPPED.name());
                    manifest.add("gaps", GSON.toJsonTree(gaps));
                }
            }
            return new Result(tasks, manifest, relations);
        }

        private List<JsonObject> closedRelations(
                Map<String, PathObservation.Scope> observedScopes) {
            if (observedScopes.size() != 1) {
                return Collections.emptyList();
            }
            PathObservation.Scope scope =
                    observedScopes.values().iterator().next();
            if (!scope.goalKind().capturesOutputRelation()) {
                return Collections.emptyList();
            }
            if (scope.outputClosure() == null) {
                gap("INVALID_OUTPUT_CLOSURE",
                        "CANONICAL_OUTPUT_CLOSURE_REQUIRED",
                        "", "", "", -1);
                return Collections.emptyList();
            }

            String region = scope.outputClosure().producer().regionId();
            String outputIdentity = scope.outputClosureIdentity();
            Map<String, PathObservation> caseByPath =
                    new LinkedHashMap<>();
            List<JsonObject> bindings = new ArrayList<>();
            for (PathObservation path : paths) {
                if (!path.scope().goalKind().capturesOutputRelation()) {
                    continue;
                }
                OutputClosureContract contract =
                        path.scope().outputClosure();
                if (!outputIdentity.equals(
                        path.scope().outputClosureIdentity())) {
                    gap("OUTPUT_CLOSURE_SCOPE_MISMATCH",
                            "CLOSED_PATHS_HAVE_DIFFERENT_OUTPUT_CLOSURES",
                            path.regionId(), "", "", -1);
                    continue;
                }

                String pathKey = path.pathKey();
                PathObservation previous = caseByPath.get(pathKey);
                if (previous != null) {
                    continue;
                }
                if (contract.members().size() > 1
                        && !path.hasExactOutputSet(
                        contract.outputPorts())) {
                    gap("JOINT_OUTPUT_EXPRESSION_SET_MISMATCH",
                            "OUTPUT_EXPRESSION_SET_DOES_NOT_MATCH_DEMAND",
                            region, pathKey, "", -1);
                } else {
                    caseByPath.put(pathKey, path);
                }
                for (JsonElement element : path.edgeBindings()) {
                    if (!element.isJsonObject()) continue;
                    bindings.add(element.getAsJsonObject());
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

            RelationSummary merged = RelationSummary.guardedPathMerge(
                    scope.outputClosure(),
                    caseByPath.values(), bindings);
            return Collections.singletonList(merged.toJson());
        }

        private void planSummary(PathObservation path) {
            List<SummaryBranchMapping> candidates = new ArrayList<>();
            for (SummaryBranchMapping mapping : path.branchMappings()) {
                String site = mapping.siteId();
                if (!path.scope().branchSites().contains(site)) {
                    continue;
                }
                if (mapping.isConcreteObservation()) {
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
                gap("BOUND_REACHED", "MAX_FLIPS_PER_PATH", path.regionId(),
                        path.pathKey(), "", -1);
            }
            for (int index = 0; index < limit; index++) {
                if (tasks.size() >= bounds.maxTasks) {
                    gap("BOUND_REACHED", "MAX_TASKS", path.regionId(),
                            path.pathKey(), "", -1);
                    return;
                }
                emitTask(path, candidates.get(index));
            }
        }

        private void emitTask(PathObservation path,
                              SummaryBranchMapping mapping) {
            BranchReplayContract replay = BranchReplayContract.fromSummary(
                    path.replayPayload(), path.branchMappings(), mapping);
            boolean desired = replay.requiredTakenOutcome();
            String key = path.flipKey(mapping, desired);

            JsonObject previous = records.get(key);
            if (previous != null && terminal(previous)) {
                return;
            }
            if (observedFlipKeys.contains(key)) {
                return;
            }
            if (!emitted.add(key)) {
                return;
            }

            JsonObject task = new JsonObject();
            task.addProperty("schemaVersion", 3);
            task.addProperty("kind", "REGION_PATH_FLIP");
            task.addProperty("queryKey", key);
            task.addProperty("regionId", path.regionId());
            task.addProperty("goalId", path.scope().goalId());
            path.scope().goalKind().writeToTask(task);
            task.addProperty("sourceTaskId", path.sourceTaskId());
            if (path.scope().outputClosure() != null) {
                task.add(OutputClosureContract.FIELD,
                        path.scope().outputClosure().toJson());
            }
            replay.addTo(task);
            tasks.add(task);
        }

        private void indexObservedCoverage() {
            for (PathObservation path : paths) {
                if (!path.relationallyComplete()) {
                    continue;
                }
                for (SummaryBranchMapping mapping : path.branchMappings()) {
                    if (!mapping.isWitnessed() || !mapping.isExplore()) {
                        continue;
                    }
                    if (!path.regionId().isEmpty()
                            && path.scope().branchSites().contains(
                            mapping.siteId())) {
                        observedFlipKeys.add(path.flipKey(mapping,
                                mapping.sourceTakenOutcome()));
                    }
                }
            }
        }

        private JsonObject manifest(boolean hasObservedPath,
                                    Set<String> observedRegions,
                                    Map<String, PathObservation.Scope> scopes) {
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
            State state = !hasObservedPath
                    ? State.NOT_STARTED
                    : !gaps.isEmpty()
                    ? State.GAPPED
                    : tasks.isEmpty() ? State.CLOSED : State.PENDING;
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 1);
            result.addProperty("kind", "REGION_PATH_WORKLIST");
            result.addProperty("state", state.name());
            if (scopes.size() != 1 || scopes.values().iterator().next()
                    .outputClosure() == null) {
                result.addProperty("regionId", regionId);
            }
            if (scopes.size() == 1) {
                PathObservation.Scope scope = scopes.values().iterator().next();
                if (scope.outputClosure() != null) {
                    result.add(OutputClosureContract.FIELD,
                            scope.outputClosure().toJson());
                } else {
                    result.addProperty("goalId", scope.goalId());
                    scope.goalKind().writeToTask(result);
                }
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
            for (PathObservation path : paths) {
                if (!path.regionId().isEmpty()) inputRegions.add(path.regionId());
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

    private static boolean terminal(JsonObject record) {
        String status = string(record, "status");
        return "UNSAT".equals(status)
                || "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY".equals(status)
                || "VALIDATED_FRESH_TARGET_PATH_FLIP_REPLAY".equals(status);
    }

}
