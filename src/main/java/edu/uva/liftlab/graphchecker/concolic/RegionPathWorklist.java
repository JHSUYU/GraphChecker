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

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
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
        private final List<JsonObject> abandonedFlips = new ArrayList<>();
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
            List<JsonObject> observedRelations = new ArrayList<>();
            if (State.PENDING.name().equals(string(manifest, "state"))) {
                observedRelations.addAll(outputRelations(observedScopes,
                        true));
            }
            if (State.CLOSED.name().equals(string(manifest, "state"))) {
                relations.addAll(outputRelations(observedScopes, false));
            }
            if (!gaps.isEmpty()) {
                tasks.clear();
                relations.clear();
                observedRelations.clear();
                manifest.addProperty("state", State.GAPPED.name());
                manifest.add("gaps", GSON.toJsonTree(gaps));
            }
            return new Result(tasks, manifest, relations,
                    observedRelations);
        }

        private List<JsonObject> outputRelations(
                Map<String, PathObservation.Scope> observedScopes,
                boolean observedOnly) {
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
            List<PathObservation> validPaths = new ArrayList<>();
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

                if (contract.members().size() > 1
                        && !path.hasExactOutputSet(
                        contract.outputPorts())) {
                    gap("JOINT_OUTPUT_EXPRESSION_SET_MISMATCH",
                            "OUTPUT_EXPRESSION_SET_DOES_NOT_MATCH_DEMAND",
                            region, path.pathKey(), "", -1);
                } else {
                    validPaths.add(path);
                }
                for (JsonElement element : path.edgeBindings()) {
                    if (!element.isJsonObject()) continue;
                    bindings.add(element.getAsJsonObject());
                }
            }
            if (!gaps.isEmpty()) {
                return Collections.emptyList();
            }
            boolean projectRelationGuards = true;
            {
                Map<String, String> relationByGuard = new LinkedHashMap<>();
                for (PathObservation path : validPaths) {
                    String prior = relationByGuard.putIfAbsent(
                            path.relationGuardKey(), path.relationKey());
                    if (prior != null && !prior.equals(path.relationKey())) {
                        projectRelationGuards = false;
                        break;
                    }
                }
            }
            Map<String, PathObservation> caseByPath = new LinkedHashMap<>();
            for (PathObservation path : validPaths) {
                String key = projectRelationGuards
                        ? path.relationKey() : path.pathKey();
                caseByPath.putIfAbsent(key, path);
            }
            if (caseByPath.isEmpty()) {
                gap("NO_VALID_OUTPUT_CLOSURE_RELATIONS",
                        "CLOSED_OUTPUT_SCOPE_HAS_NO_CASES",
                        region, "", "", -1);
                return Collections.emptyList();
            }

            RelationSummary merged = observedOnly
                    ? RelationSummary.observedPathMerge(
                    scope.outputClosure(), caseByPath.values(), bindings,
                    State.PENDING.name(), projectRelationGuards)
                    : RelationSummary.guardedPathMerge(
                    scope.outputClosure(), caseByPath.values(), bindings,
                    projectRelationGuards);
            return Collections.singletonList(merged.toJson());
        }

        private void planSummary(PathObservation path) {
            List<SummaryBranchMapping> candidates = new ArrayList<>();
            JsonObject task = taskById.get(path.sourceTaskId());
            Set<String> explicitFaultSymbols = explicitFaultSymbols(task);
            for (SummaryBranchMapping mapping : path.branchMappings()) {
                String site = mapping.siteId();
                if (!path.scope().branchSites().contains(site)) {
                    continue;
                }
                if (mapping.isConcreteObservation()) {
                    continue;
                }
                if (!mapping.isExplore()) continue;
                if (isSelectedTargetDecision(path, task, mapping)) {
                    continue;
                }
                if (!explicitFaultSymbols.isEmpty()
                        && !dependsOnAny(mapping.witness()
                        .sourceSatisfiedPredicate(),
                        explicitFaultSymbols)) {
                    continue;
                }
                if (abandonsDemandedOutputSite(path, task, mapping)) {
                    continue;
                }
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

        /**
         * The exact selected target decision is kept symbolic by the fatal
         * reach query.  A witnessed required successor is used directly; an
         * opposite witness contributes its decided prefix plus the symbolic
         * complement.  Replaying this sibling therefore adds no target path
         * and may mutate an earlier activation before its prefix is known.
         */
        private boolean isSelectedTargetDecision(
                PathObservation path, JsonObject task,
                SummaryBranchMapping mapping) {
            if (!path.scope().goalKind().capturesTargetReach()
                    || task == null) {
                return false;
            }
            for (JsonElement element : array(task, "branches")) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!mapping.siteId().equals(string(branch, "siteId"))
                        || !bool(branch, "failureTarget", false)
                        || integer(branch, "selectedOccurrence", -1)
                        != mapping.occurrence()) {
                    continue;
                }
                JsonElement required = branch.get("requiredOutcome");
                return required != null && required.isJsonPrimitive()
                        && required.getAsJsonPrimitive().isBoolean();
            }
            return false;
        }

        /**
         * A task with a named fault input explores that controlled fault and
         * keeps the rest of the producer path at its witnessed values.  This
         * is the experiment's explicit degree of freedom; flipping unrelated
         * service/configuration guards would create alternative causes that
         * hide whether the requested RPC failure is load-bearing.
         */
        private Set<String> explicitFaultSymbols(JsonObject task) {
            Set<String> result = new LinkedHashSet<>();
            for (JsonElement element : array(task, "inputActions")) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                if (!"SYMBOLIC".equals(string(action, "mode"))
                        || !"EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1".equals(
                        string(action, "authority"))) {
                    continue;
                }
                String symbol = string(action, "symbol");
                if (!symbol.isEmpty()) result.add(symbol);
            }
            return result;
        }

        private boolean dependsOnAny(JsonElement predicate,
                                     Set<String> symbols) {
            String encoded = CanonicalJson.render(predicate);
            for (String symbol : symbols) {
                if (encoded.contains(symbol)) return true;
            }
            return false;
        }

        /**
         * True when the flipped successor provably cannot reach a site the
         * demanded outputs are published at.  Such a flip walks a fresh path
         * and then ends with the port never written, so the whole replay is
         * spent to learn nothing; the runtime still fails closed on it
         * ({@code OUTPUT_CAPTURE_COUNT:<port>:0}), which is what makes it
         * cost a replay rather than a wrong answer.
         *
         * <p>Only the outcome the static analyzer proved is required to reach
         * that exact site decides this.  A site with no proof, a branch with
         * no recorded control dependence, and a demand published at no site
         * at all all keep the candidate.</p>
         */
        private boolean abandonsDemandedOutputSite(
                PathObservation path, JsonObject task,
                SummaryBranchMapping mapping) {
            OutputClosureContract closure = path.scope().outputClosure();
            if (closure == null || task == null) return false;
            Set<String> demanded =
                    closure.executionScope().outputSites();
            if (demanded.isEmpty()) return false;
            boolean desired = !mapping.sourceTakenOutcome();
            for (JsonElement element : array(task, "branches")) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!mapping.siteId().equals(string(branch, "siteId"))) {
                    continue;
                }
                for (JsonElement row
                        : array(branch, "guardedSiteOutcomes")) {
                    if (!row.isJsonObject()) continue;
                    JsonObject guarded = row.getAsJsonObject();
                    if (!demanded.contains(string(guarded, "siteId"))) {
                        continue;
                    }
                    JsonElement outcome = guarded.get("requiredOutcome");
                    if (outcome != null && outcome.isJsonPrimitive()
                            && outcome.getAsJsonPrimitive().isBoolean()
                            && outcome.getAsBoolean() != desired) {
                        return true;
                    }
                }
            }
            return false;
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
            // A contract that contradicts the seed it must be replayed
            // against is refused by admission on static grounds alone, so
            // proposing it buys a solve and a full replay whose only possible
            // outcome is that refusal.  Ask now, and name the flip that never
            // ran; the answer is the admission check itself, so the early and
            // the late verdict are the same verdict.
            String conflict = ConcolicSummaryImporter.plannedReplaySeedConflict(
                    taskById.get(path.sourceTaskId()), replay);
            if (!conflict.isEmpty()) {
                abandoned("PATH_FLIP_CONTRACT_SEED_CONFLICT", key, conflict);
                return;
            }

            JsonObject task = new JsonObject();
            task.addProperty("schemaVersion", 3);
            task.addProperty("kind", "REGION_PATH_FLIP");
            task.addProperty("queryKey", key);
            task.addProperty("regionId", path.regionId());
            task.addProperty("goalId", path.scope().goalId());
            path.scope().loopBound().writeTo(task);
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
                scope.loopBound().writeTo(result);
                if (scope.outputClosure() != null) {
                    result.add(OutputClosureContract.FIELD,
                            scope.outputClosure().toJson());
                } else {
                    result.addProperty("goalId", scope.goalId());
                    scope.goalKind().writeToTask(result);
                }
            }
            // Downstream reach-query construction attests that its seed
            // query and this closure describe the same canonical replay
            // activation, so a uniquely observed instance is named here.
            Set<String> observedInstances = new LinkedHashSet<>();
            for (PathObservation path : paths) {
                String instance = path.regionInstanceId();
                if (!instance.isEmpty()) observedInstances.add(instance);
            }
            if (observedInstances.size() == 1) {
                result.addProperty("regionInstanceId",
                        observedInstances.iterator().next());
            }
            result.add("gaps", GSON.toJsonTree(gaps));
            // A flip the exploration could not carry through is an
            // explored-and-abandoned proposal, not a planning failure: the
            // flip solver only proposes fresh paths, while the fatal branch
            // condition itself stays symbolic for the reach stage.  That
            // covers a query the flip encoder cannot lower and a flip whose
            // bounded replay reached no output relation, which the importer
            // rightly refuses.  Naming each such flip keeps the closure
            // auditable without blocking candidates/compose/reach.
            List<JsonObject> explorationGaps = new ArrayList<>();
            for (JsonObject record : records.values()) {
                String kind = explorationGapKind(string(record, "status"));
                if (kind.isEmpty()) continue;
                JsonObject gap = new JsonObject();
                gap.addProperty("kind", kind);
                gap.addProperty("queryKey", string(record, "queryKey"));
                gap.addProperty("reason", string(record, "reason"));
                if (record.get("unsupported") != null) {
                    gap.add("unsupported", record.get("unsupported"));
                }
                explorationGaps.add(gap);
            }
            explorationGaps.addAll(abandonedFlips);
            result.add("explorationGaps", GSON.toJsonTree(explorationGaps));
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

        /**
         * Names a flip this planner refuses to propose.  It joins the flips
         * an execution explored and abandoned rather than the planning gaps,
         * because it is charged to itself: the closure stays auditable and
         * the run proceeds.
         */
        private void abandoned(String kind, String queryKey, String reason) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("queryKey", queryKey);
            gap.addProperty("reason", reason);
            abandonedFlips.add(gap);
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
        public final List<JsonObject> observedRelations;

        private Result(List<JsonObject> tasks, JsonObject manifest,
                       List<JsonObject> relations,
                       List<JsonObject> observedRelations) {
            this.tasks = tasks;
            this.manifest = manifest;
            this.relations = relations;
            this.observedRelations = observedRelations;
        }
    }

    private static boolean terminal(JsonObject record) {
        String status = string(record, "status");
        return "UNSAT".equals(status)
                || !explorationGapKind(status).isEmpty()
                || "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY".equals(status)
                || "VALIDATED_FRESH_TARGET_PATH_FLIP_REPLAY".equals(status);
    }

    /** Names an abandoned flip, or empty when the record is not one. */
    private static String explorationGapKind(String status) {
        if ("UNSUPPORTED".equals(status)) return "UNSUPPORTED_PATH_FLIP";
        if ("REPLAY_NOT_ADMITTED".equals(status)) {
            return "PATH_FLIP_REPLAY_NOT_ADMITTED";
        }
        // A flip whose replay never obtained the single symbolic engine was
        // not refuted; it was never explored.  Charging it to the same gap as
        // a replay that ran and missed the relation would make a scheduling
        // outcome indistinguishable from an infeasible path.
        if ("REPLAY_ENGINE_UNAVAILABLE".equals(status)) {
            return "PATH_FLIP_REPLAY_ENGINE_UNAVAILABLE";
        }
        // A replay is bounded in the paths it may walk, not in what those
        // paths cost to keep resident, so one can end before publishing a
        // result.  That flip is abandoned like any other, and the gap says so.
        if ("REPLAY_PRODUCED_NO_RESULT".equals(status)) {
            return "PATH_FLIP_REPLAY_PRODUCED_NO_RESULT";
        }
        return "";
    }

}
