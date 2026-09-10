package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

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

    /** Plans the next obligations from the admitted local cases of one
     * topology.
     *
     * <p>README "Delta ownership is also singular" makes this the consumer of
     * the importer's admitted cases: a path whose own occurrence the delta
     * classified as {@code TOPOLOGY_DIVERGENCE} belongs to the next
     * iteration's plan, so no branch-flip obligation may be built across
     * it.</p> */
    static Result plan(List<JsonObject> summaries,
                       List<JsonObject> executionTasks,
                       List<JsonObject> explorationRecords,
                       Bounds bounds,
                       List<JsonObject> topologyDelta,
                       String familySnapshotDigest) {
        return new Planner(summaries, executionTasks, explorationRecords,
                bounds, topologyDelta, familySnapshotDigest).run();
    }

    private static final class Planner {
        private final Bounds bounds;
        private final String familySnapshotDigest;
        private final Set<String> divergentTasks = new LinkedHashSet<>();
        private final Set<String> divergentOccurrences =
                new LinkedHashSet<>();
        private final Map<String, JsonObject> taskById =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> records = new LinkedHashMap<>();
        private final List<PathObservation> paths = new ArrayList<>();
        private final List<JsonObject> tasks = new ArrayList<>();
        private final List<JsonObject> gaps = new ArrayList<>();
        private final Set<String> gapKeys = new LinkedHashSet<>();
        private final List<JsonObject> coverageGaps = new ArrayList<>();
        private final Set<String> coverageGapKeys = new LinkedHashSet<>();
        private final Set<String> emitted = new LinkedHashSet<>();
        private final Set<String> observedFlipKeys = new LinkedHashSet<>();
        /** Activation-exact local paths already explored. */
        private final Set<String> plannedActivationPaths =
                new LinkedHashSet<>();
        private final Map<String, Integer> pathCountByRegion =
                new LinkedHashMap<>();
        private Planner(List<JsonObject> summaries,
                        List<JsonObject> executionTasks,
                        List<JsonObject> explorationRecords,
                        Bounds bounds,
                        List<JsonObject> topologyDelta,
                        String familySnapshotDigest) {
            this.bounds = bounds;
            this.familySnapshotDigest = familySnapshotDigest;
            for (JsonObject row : topologyDelta) {
                if (!TopologyDelta.TOPOLOGY_DIVERGENCE.equals(
                        string(row, "deltaKind"))) {
                    continue;
                }
                String taskId = string(row, "taskId");
                if (!taskId.isEmpty()) divergentTasks.add(taskId);
                divergentOccurrences.add(occurrenceKey(
                        string(row, "sourceKey"),
                        string(row, "occurrenceId")));
            }
            for (JsonObject task : executionTasks) {
                String id = string(task, "taskId");
                if (!id.isEmpty()) this.taskById.put(id, task);
            }
            for (JsonObject record : explorationRecords) {
                String key = string(record, "queryKey");
                if (!key.isEmpty()) this.records.put(key, record);
            }
            for (JsonObject summary : summaries) {
                PathObservation path = PathObservation.decode(summary,
                        taskById.get(string(summary, "taskId")));
                paths.add(path);
                collectAlignmentGaps(summary);
            }
            Collections.sort(paths, Comparator.comparing(value ->
                    value.regionId() + "\n" + value.pathKey() + "\n"
                            + string(value.replayPayload(), "summaryId")));
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
                if (divergedTopology(path)) {
                    coverageGap(TopologyDelta.TOPOLOGY_DIVERGENCE,
                            "OBLIGATION_BELONGS_TO_THE_NEXT_ITERATION",
                            region, pathKey, "", -1);
                    continue;
                }
                if (!path.branchMappingIssue().isEmpty()) {
                    gap("INVALID_BRANCH_MAPPING_SCHEMA",
                            path.branchMappingIssue(), region, pathKey, "", -1);
                    continue;
                }
                // A case is a local path condition plus its normalized
                // consumer anchors.  Output capture completeness is not an
                // exploration contract: the VM-propagated value has already
                // reached the consumer expression, and later family arms are
                // admitted as their own local cases.
                // One bounded region activation owns one local PC.  Keep
                // distinct activations separate: their loop/access ordinals
                // and VM read-from/order evidence can differ even when the
                // branch predicates alpha-normalize to the same text.  Loop
                // iterations inside this activation remain part of this one
                // path; pathKey does not turn them into standalone cases.
                boolean plansObligations = plannedActivationPaths.add(
                        region + "\n" + path.pathKey());
                if (plansObligations) {
                    pathCountByRegion.merge(region, 1, Integer::sum);
                }
                if (!plansObligations) continue;
                if (pathCountByRegion.get(region) > bounds.maxPathsPerRegion) {
                    coverageGap("BOUND_REACHED", "MAX_PATHS_PER_REGION", region,
                            pathKey, "", -1);
                    continue;
                }
                planSummary(path);
                if (campaignTaskCount() >= bounds.maxTasks) break;
            }

            enforcePathBounds();

            JsonObject manifest = manifest(!seenPaths.isEmpty(),
                    observedRegions, observedScopes);
            if (!gaps.isEmpty()) {
                tasks.clear();
                manifest.addProperty("state", State.GAPPED.name());
                manifest.addProperty("coverageState",
                        hasReplayPath() ? "PARTIAL" : "SEED_ONLY");
                manifest.add("gaps", GSON.toJsonTree(gaps));
            }
            return new Result(tasks, manifest);
        }

        /** Keeps only flips that can still discover a path in their region. */
        private void enforcePathBounds() {
            Map<String, Integer> retainedByRegion = new LinkedHashMap<>();
            Set<String> truncatedRegions = new LinkedHashSet<>();
            List<JsonObject> retained = new ArrayList<>();
            for (JsonObject task : tasks) {
                String region = string(task, "regionId");
                int observed = pathCountByRegion.getOrDefault(region, 0);
                int remaining = Math.max(0,
                        bounds.maxPathsPerRegion - observed);
                int retainedCount = retainedByRegion.getOrDefault(region, 0);
                if (retainedCount >= remaining) {
                    truncatedRegions.add(region);
                    continue;
                }
                retained.add(task);
                retainedByRegion.put(region, retainedCount + 1);
            }
            if (retained.size() == tasks.size()) return;
            tasks.clear();
            tasks.addAll(retained);
            for (String region : truncatedRegions) {
                coverageGap("BOUND_REACHED", "MAX_PATHS_PER_REGION",
                        region, "", "", -1);
            }
        }

        /** Whether the delta classified this path's own occurrence changed.
         *
         * <p>OCC-1: the delta names the planned address of the task it
         * classified, because that is the only occurrence identity a frozen
         * plan states; a summary names the activation that ran.  The two are
         * matched on the address, exactly as the target reach query and the
         * scheduler match them.  Comparing the activation string instead
         * left this half of the rule unable to fire at all, so a diverged
         * occurrence was excluded only when its whole task was.</p> */
        private boolean divergedTopology(PathObservation path) {
            return divergentTasks.contains(path.sourceTaskId())
                    || divergentOccurrences.contains(occurrenceKey(
                    path.sourceKey(), path.plannedOccurrenceId()));
        }

        private void planSummary(PathObservation path) {
            List<SummaryBranchMapping> candidates = new ArrayList<>();
            JsonObject task = taskById.get(path.sourceTaskId());
            if (path.scope().goalKind().capturesTargetReach()) {
                candidates.addAll(targetPrefixCandidates(path, task));
            } else {
                regionPathCandidates(path, task, candidates);
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
                coverageGap("BOUND_REACHED", "MAX_FLIPS_PER_PATH",
                        path.regionId(),
                        path.pathKey(), "", -1);
            }
            for (int index = 0; index < limit; index++) {
                // path_exploration_records.jsonl is cumulative for this
                // member.
                if (campaignTaskCount() >= bounds.maxTasks) {
                    coverageGap("BOUND_REACHED", "MAX_TASKS",
                            path.regionId(),
                            path.pathKey(), "", -1);
                    return;
                }
                emitTask(path, candidates.get(index));
            }
        }

        private void regionPathCandidates(
                PathObservation path, JsonObject task,
                List<SummaryBranchMapping> candidates) {
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
                if (!explicitFaultSymbols.isEmpty()
                        && !dependsOnAny(mapping.witness()
                        .sourceSatisfiedPredicateView(),
                        explicitFaultSymbols)) {
                    continue;
                }
                candidates.add(mapping);
            }
        }

        /** Selects local predecessor decisions and a non-terminal target
         * frontier. */
        private List<SummaryBranchMapping> targetPrefixCandidates(
                PathObservation path, JsonObject task) {
            List<SummaryBranchMapping> result = new ArrayList<>();
            if (task == null) {
                gap("TARGET_PREFIX_TASK_MISSING",
                        "TARGET_PREFIX_REQUIRES_SOURCE_TASK",
                        path.regionId(), path.pathKey(), "", -1);
                return result;
            }
            JsonObject target = task.has("targetBranch")
                    && task.get("targetBranch").isJsonObject()
                    ? task.getAsJsonObject("targetBranch")
                    : new JsonObject();
            String targetSite = string(target, "siteId");
            int targetOccurrence = integer(target, "occurrence", -1);
            List<SummaryBranchMapping> fatalMappings = new ArrayList<>();
            for (SummaryBranchMapping mapping : path.branchMappings()) {
                if (mapping.isExplore()
                        && targetSite.equals(mapping.siteId())
                        && targetOccurrence == mapping.occurrence()) {
                    fatalMappings.add(mapping);
                }
            }
            if (targetSite.isEmpty() || targetOccurrence < 1
                    || fatalMappings.size() != 1) {
                gap("TARGET_PREFIX_FATAL_MAPPING_INVALID",
                        "TARGET_PREFIX_REQUIRES_ONE_EXACT_FATAL_MAPPING",
                        path.regionId(), path.pathKey(), targetSite,
                        targetOccurrence);
                return result;
            }
            SummaryBranchMapping fatal = fatalMappings.get(0);
            PathObservation.TargetReachEvent reach = null;
            try {
                reach = path.targetReachEvent();
            } catch (IllegalArgumentException malformed) {
                // A malformed event is an absent one: the exact reach event
                // is the only witness this prefix has of its fatal site.
            }
            if (reach == null || !reach.matches(fatal.siteId(),
                    fatal.occurrence(), fatal.sourceTakenOutcome())) {
                gap("TARGET_PREFIX_FATAL_EVENT_INVALID",
                        "TARGET_PREFIX_REQUIRES_EXACT_TARGET_REACH_EVENT",
                        path.regionId(), path.pathKey(), targetSite,
                        targetOccurrence);
                return result;
            }
            Boolean required = requiredTargetOutcome(task, fatal.siteId());
            if (fatal.isConcreteObservation()) {
                if (required == null
                        || fatal.sourceTakenOutcome() != required) {
                    gap("TARGET_PREFIX_CONCRETE_OUTCOME_MISMATCH",
                            "TARGET_CONCRETE_DECISION_CANNOT_BE_FLIPPED",
                            path.regionId(), path.pathKey(), targetSite,
                            targetOccurrence);
                }
                // A matching exact concrete target event is already the
                // existential reach witness. It has no predicate to flip.
                return result;
            }
            int fatalPc = fatal.summaryPcIndex();
            // The exact selected fatal guard is itself an obligation.  A
            // following guarded fatal site exists only for a nested throw;
            // requiring one here made a terminal one-guard throw look CLOSED
            // while its observed outcome still contradicted the required
            // failure outcome.
            if (required != null
                    && fatal.sourceTakenOutcome() != required) {
                result.add(fatal);
            }
            for (SummaryBranchMapping mapping : path.branchMappings()) {
                if (!mapping.isWitnessed()
                        || mapping.witness().isPcPredicateDecision()
                        || mapping.policy()
                        != SummaryBranchMapping.Policy.PATH_ASSUMPTION
                        || mapping.summaryPcIndex() >= fatalPc
                        || !declaredTargetPrefix(task, mapping)) {
                    continue;
                }
                result.add(mapping);
            }
            return result;
        }

        /** The next not-yet-selected guard of this annotated throw. */
        private JsonObject nextTargetGuard(JsonObject task,
                                           String currentSite) {
            JsonArray branches = array(task, "branches");
            int current = -1;
            JsonObject currentBranch = null;
            for (int index = 0; index < branches.size(); index++) {
                if (!branches.get(index).isJsonObject()) continue;
                JsonObject branch = branches.get(index).getAsJsonObject();
                if (currentSite.equals(string(branch, "siteId"))) {
                    if (current >= 0) return null;
                    current = index;
                    currentBranch = branch;
                }
            }
            if (current < 0 || currentBranch == null) return null;
            Set<String> corridor = TargetReachPathQueryBuilder
                    .guardedTargetIdentities(currentBranch);
            if (corridor.isEmpty()) return null;
            for (int index = current + 1; index < branches.size(); index++) {
                if (!branches.get(index).isJsonObject()) continue;
                JsonObject candidate = branches.get(index).getAsJsonObject();
                if (!bool(candidate, "failureTarget", false)
                        || TargetReachPathQueryBuilder
                        .requiredOutcome(candidate) == null
                        || Collections.disjoint(corridor,
                        TargetReachPathQueryBuilder
                                .guardedTargetIdentities(candidate))) {
                    continue;
                }
                return candidate;
            }
            return null;
        }


        private Boolean requiredTargetOutcome(JsonObject task,
                                              String siteId) {
            Boolean result = null;
            for (JsonElement element : array(task, "branches")) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!siteId.equals(string(branch, "siteId"))) continue;
                Boolean value = TargetReachPathQueryBuilder
                        .requiredOutcome(branch);
                if (value == null || result != null && !result.equals(value)) {
                    return null;
                }
                result = value;
            }
            return result;
        }

        private boolean declaredTargetPrefix(
                JsonObject task, SummaryBranchMapping mapping) {
            int matches = 0;
            for (JsonElement element : array(task, "branches")) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (mapping.siteId().equals(string(branch, "siteId"))
                        && "PATH_ASSUMPTION".equals(
                        string(branch, "policy"))) {
                    int selectedOccurrence = integer(branch,
                            "selectedOccurrence", mapping.occurrence());
                    if (selectedOccurrence == mapping.occurrence()) {
                        matches++;
                    }
                }
            }
            return matches == 1;
        }

        private int campaignTaskCount() {
            return records.size() + tasks.size();
        }

        /** A task with a named fault input explores that controlled fault and
         * keeps the rest of its local prefix at witnessed values. */
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
            if (predicate == null || symbols.isEmpty()) return false;
            java.util.Deque<JsonElement> pending = new java.util.ArrayDeque<>();
            Set<JsonElement> visited = Collections.newSetFromMap(
                    new java.util.IdentityHashMap<JsonElement, Boolean>());
            pending.push(predicate);
            while (!pending.isEmpty()) {
                JsonElement value = pending.pop();
                if (value == null || value.isJsonNull()) continue;
                if (value.isJsonPrimitive()) {
                    if (value.getAsJsonPrimitive().isString()) {
                        String text = value.getAsString();
                        for (String symbol : symbols) {
                            if (text.contains(symbol)) return true;
                        }
                    }
                    continue;
                }
                if (!visited.add(value)) continue;
                if (value.isJsonArray()) {
                    for (JsonElement child : value.getAsJsonArray()) {
                        if (child != null) pending.push(child);
                    }
                } else {
                    for (Map.Entry<String, JsonElement> field
                            : value.getAsJsonObject().entrySet()) {
                        if (field.getValue() != null) {
                            pending.push(field.getValue());
                        }
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
            String semanticKey = path.flipKey(mapping, desired);

            // A local branch is one semantic obligation regardless of which
            // upstream anchor arm supplied its current payload.  A solver
            // verdict, however, is valid only for the receiver-family
            // snapshot it saw: a newly discovered upstream arm can turn a
            // previously UNSAT flip into a replayable one.
            String key = CanonicalJson.sha256(semanticKey + "\n"
                    + familySnapshotDigest);

            JsonObject previous = records.get(key);
            if (previous != null && terminal(previous)) {
                return;
            }
            if (observedFlipKeys.contains(semanticKey)) {
                return;
            }
            if (!emitted.add(key)) {
                return;
            }
            JsonObject task = new JsonObject();
            task.addProperty("schemaVersion", 3);
            task.addProperty("kind", "REGION_PATH_FLIP");
            task.addProperty("queryKey", key);
            task.addProperty("semanticFlipKey", semanticKey);
            task.addProperty(LinkedReplayBundle.FAMILY_DIGEST_FIELD,
                    familySnapshotDigest);
            task.addProperty("regionId", path.regionId());
            task.addProperty("goalId", path.scope().goalId());
            path.scope().loopBound().writeTo(task);
            path.scope().goalKind().writeToTask(task);
            task.addProperty("sourceTaskId", path.sourceTaskId());
            task.addProperty("sourceSummaryId",
                    string(path.replayPayload(), "summaryId"));
            task.addProperty("sourcePathKey", path.pathKey());
            task.addProperty("sourceActivationOccurrenceId",
                    path.occurrenceId());
            task.addProperty("sourceActivationOrdinal",
                    path.activationOrdinal());
            replay.addTo(task);
            if (path.scope().goalKind().capturesTargetReach()) {
                VmHandoffEvidence.writeTo(task, path.vmHandoffEvents());
                JsonArray bindings = path.edgeBindings();
                if (bindings.size() > 0) {
                    task.add("edgeBindings", bindings);
                }
                JsonObject sourceTask = taskById.get(path.sourceTaskId());
                JsonObject selected = sourceTask == null
                        ? new JsonObject()
                        : sourceTask.has("targetBranch")
                        && sourceTask.get("targetBranch").isJsonObject()
                        ? sourceTask.getAsJsonObject("targetBranch")
                        : new JsonObject();
                if (mapping.siteId().equals(string(selected, "siteId"))) {
                    JsonObject next = nextTargetGuard(sourceTask,
                            mapping.siteId());
                    if (next != null) {
                        JsonObject target = new JsonObject();
                        target.addProperty("siteId",
                                string(next, "siteId"));
                        int occurrence = integer(next,
                                "selectedOccurrence", -1);
                        target.addProperty("occurrence",
                                occurrence > 0 ? occurrence : 1);
                        task.add("targetBranch", target);
                    }
                }
            }
            tasks.add(task);
        }

        private void indexObservedCoverage() {
            for (PathObservation path : paths) {
                Set<String> observedTargetPrefixes = new LinkedHashSet<>();
                if (path.scope().goalKind().capturesTargetReach()) {
                    for (SummaryBranchMapping prefix
                            : targetPrefixCandidates(path,
                            taskById.get(path.sourceTaskId()))) {
                        observedTargetPrefixes.add(
                                prefix.decisionIdentity());
                    }
                }
                for (SummaryBranchMapping mapping : path.branchMappings()) {
                    if (!mapping.isWitnessed()) {
                        continue;
                    }
                    boolean localExplore = mapping.isExplore()
                            && !path.regionId().isEmpty()
                            && path.scope().branchSites().contains(
                            mapping.siteId());
                    boolean targetPrefix = observedTargetPrefixes.contains(
                            mapping.decisionIdentity());
                    if (localExplore || targetPrefix) {
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
            Set<String> sources = new TreeSet<>();
            Set<String> occurrences = new TreeSet<>();
            for (PathObservation path : paths) {
                if (!path.sourceKey().isEmpty()) {
                    sources.add(path.sourceKey());
                }
                // OCC-1: the worklist addresses one planned occurrence; its
                // activations are cases inside it, so the manifest keeps
                // naming the address the campaign scheduled.
                if (!path.plannedOccurrenceId().isEmpty()) {
                    occurrences.add(path.plannedOccurrenceId());
                }
            }
            if (sources.size() == 1) {
                result.addProperty("sourceKey", sources.iterator().next());
            }
            if (occurrences.size() == 1) {
                result.addProperty("occurrenceId",
                        occurrences.iterator().next());
            }
            result.addProperty("regionId", regionId);
            if (scopes.size() == 1) {
                PathObservation.Scope scope = scopes.values().iterator().next();
                scope.loopBound().writeTo(result);
                result.addProperty("goalId", scope.goalId());
                scope.goalKind().writeToTask(result);
            }
            result.add("gaps", GSON.toJsonTree(gaps));
            List<JsonObject> pathCoverageGaps = new ArrayList<>();
            for (JsonObject record : records.values()) {
                collectAlignmentGaps(record);
                String kind = explorationGapKind(string(record, "status"));
                if (kind.isEmpty()) continue;
                JsonObject gap = new JsonObject();
                gap.addProperty("kind", kind);
                gap.addProperty("queryKey", string(record, "queryKey"));
                gap.addProperty("reason", string(record, "reason"));
                if (record.has("unsupported")) {
                    gap.add("unsupported", record.get("unsupported"));
                }
                pathCoverageGaps.add(gap);
            }
            coverageGaps.addAll(pathCoverageGaps);
            result.add("coverageGaps", GSON.toJsonTree(coverageGaps));
            result.addProperty("coverageState",
                    state == State.CLOSED && coverageGaps.isEmpty()
                            ? "CLOSED" : campaignBoundReached()
                            || hasReplayPath()
                            ? "PARTIAL" : "SEED_ONLY");
            return result;
        }

        private boolean campaignBoundReached() {
            for (JsonObject gap : coverageGaps) {
                if ("BOUND_REACHED".equals(string(gap, "kind"))) {
                    return true;
                }
            }
            return false;
        }

        private boolean hasReplayPath() {
            for (PathObservation path : paths) {
                JsonObject task = taskById.get(path.sourceTaskId());
                if (!string(task, "pathQueryKey").isEmpty()) return true;
            }
            return false;
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

        /** Names a flip this planner refuses to propose. */
        private void gap(String kind, String reason, String region,
                         String pathKey, String site, int occurrence) {
            addIssue(gaps, gapKeys, kind, reason, region, pathKey, site,
                    occurrence);
        }

        private void coverageGap(String kind, String reason, String region,
                                 String pathKey, String site,
                                 int occurrence) {
            addIssue(coverageGaps, coverageGapKeys, kind, reason, region,
                    pathKey, site, occurrence);
        }

        /** Forwards an imported summary's alignment gaps into the coverage
         * gaps. */
        private void collectAlignmentGaps(JsonObject source) {
            for (JsonElement element : array(source, "alignmentGaps")) {
                if (!element.isJsonObject()) continue;
                JsonObject imported = element.getAsJsonObject().deepCopy();
                String kind = string(imported, "kind");
                if (!RpcExpressionHandoff.GAP_KIND.equals(kind)
                        && !SharedStateEvidence.GAP_KIND.equals(kind)
                        && !CoverageDivergence.isDivergence(imported)) {
                    continue;
                }
                String key = CanonicalJson.render(imported);
                if (coverageGapKeys.add(key)) {
                    coverageGaps.add(imported);
                }
            }
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

    /** The canonical region occurrence, as both stages key it. */
    private static String occurrenceKey(String sourceKey,
                                        String occurrenceId) {
        return sourceKey + "\n" + occurrenceId;
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

        private Result(List<JsonObject> tasks, JsonObject manifest) {
            this.tasks = tasks;
            this.manifest = manifest;
        }
    }

    private static boolean terminal(JsonObject record) {
        String status = string(record, "status");
        return "UNSAT".equals(status)
                || !explorationGapKind(status).isEmpty()
                || "VALIDATED_FRESH_REGION_PATH_FLIP_REPLAY".equals(status);
    }

    /** Names an abandoned flip, or empty when the record is not one. */
    private static String explorationGapKind(String status) {
        if ("UNSUPPORTED".equals(status)) return "UNSUPPORTED_PATH_FLIP";
        if ("REPLAY_NOT_ADMITTED".equals(status)) {
            return "PATH_FLIP_REPLAY_NOT_ADMITTED";
        }
        // A flip whose replay never obtained the single symbolic engine was
        // not refuted; it was never explored.
        if ("REPLAY_ENGINE_UNAVAILABLE".equals(status)) {
            return "PATH_FLIP_REPLAY_ENGINE_UNAVAILABLE";
        }
        // A replay is bounded in the paths it may walk, not in what those
        // paths cost to keep resident, so one can end before publishing a
        // result.  That flip is abandoned like any other, and the gap says so.
        if ("REPLAY_PRODUCED_NO_RESULT".equals(status)) {
            return "PATH_FLIP_REPLAY_PRODUCED_NO_RESULT";
        }
        // The solver reached a verdict and it was "this flip cannot be
        // materialized".
        if ("MATERIALIZATION_GAP".equals(status)) {
            return "PATH_FLIP_MATERIALIZATION_GAP";
        }
        if ("BUNDLE_TOPOLOGY_DIVERGENCE".equals(status)) {
            return "LINKED_REPLAY_LEFT_TOPOLOGY_EPOCH";
        }
        return "";
    }

}
