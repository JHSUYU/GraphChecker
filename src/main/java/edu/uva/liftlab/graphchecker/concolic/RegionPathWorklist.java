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
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

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
     * <p>README "Delta ownership is also singular": divergence is the
     * campaign's decision, not this planner's.  The driver quarantines a
     * diverged worker's summaries and defers a whole wave whose seed replay
     * left the epoch, so every path this planner sees belongs to the frozen
     * topology.</p> */
    static Result plan(List<JsonObject> summaries,
                       List<JsonObject> executionTasks,
                       List<JsonObject> explorationRecords,
                       Bounds bounds,
                       String familySnapshotDigest) {
        return plan(summaries, executionTasks, explorationRecords, bounds,
                familySnapshotDigest, SymbolicRootInventory.disabled());
    }

    /**
     * Plans one member against the wave's declared roots.
     *
     * <p>A branch whose condition names no root cannot move: the campaign
     * varies its roots and nothing else, so every other value in the
     * condition is the one the recording produced. Such an obligation is
     * closed here, by the recording, instead of being handed to a solver and
     * then to a replay. See {@link SymbolicRootInventory} for when that
     * judgement is withheld.</p>
     */
    static Result plan(List<JsonObject> summaries,
                       List<JsonObject> executionTasks,
                       List<JsonObject> explorationRecords,
                       Bounds bounds,
                       String familySnapshotDigest,
                       SymbolicRootInventory roots) {
        return new Planner(summaries, executionTasks, explorationRecords,
                bounds, familySnapshotDigest, roots).run();
    }

    /** Telemetry kind for an obligation the recording already decided. */
    static final String CLOSED_BY_CONSTANT = "OBLIGATION_CLOSED_BY_CONSTANT";
    /** Telemetry kind for a wave that planned more than its roots justify. */
    static final String OBLIGATIONS_EXCEED_ROOT_SITES =
            "EXPLORE_OBLIGATIONS_EXCEED_ROOT_SITES";
    /** Manifest field carrying this member's root-slice telemetry. */
    static final String ROOT_SLICE_FIELD = "rootSliceTelemetry";

    private static final class Planner {
        private final Bounds bounds;
        private final String familySnapshotDigest;
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
        /** The wave's declared roots; see {@link SymbolicRootInventory}. */
        private final SymbolicRootInventory roots;
        /** One row per obligation the recording already decided. */
        private final List<JsonObject> closedByConstant = new ArrayList<>();
        private final Set<String> closedByConstantKeys =
                new LinkedHashSet<>();
        /** Branch sites whose condition does name a root. */
        private final Set<String> rootDependentSites = new TreeSet<>();

        private Planner(List<JsonObject> summaries,
                        List<JsonObject> executionTasks,
                        List<JsonObject> explorationRecords,
                        Bounds bounds,
                        String familySnapshotDigest,
                        SymbolicRootInventory roots) {
            this.bounds = bounds;
            this.familySnapshotDigest = familySnapshotDigest;
            this.roots = roots == null
                    ? SymbolicRootInventory.disabled() : roots;
            for (JsonObject task : executionTasks) {
                String id = optionalString(task, "taskId");
                if (!id.isEmpty()) this.taskById.put(id, task);
            }
            for (JsonObject record : explorationRecords) {
                String key = optionalString(record, "queryKey");
                if (!key.isEmpty()) this.records.put(key, record);
            }
            for (JsonObject summary : summaries) {
                PathObservation path = PathObservation.decode(summary,
                        taskById.get(optionalString(summary, "taskId")));
                paths.add(path);
                collectAlignmentGaps(summary);
            }
            Collections.sort(paths, Comparator.comparing(value ->
                    value.regionId() + "\n" + value.pathKey() + "\n"
                            + optionalString(value.replayPayload(), "summaryId")));
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
                // The task ceiling stops the walk over observed paths. Every
                // path after this one is unplanned, so the ceiling is named
                // here for the same reason planSummary names it: a truncated
                // walk that published no gap let coverageState read CLOSED
                // on a campaign that simply ran out of budget.
                if (campaignTaskCount() >= bounds.maxTasks) {
                    coverageGap("BOUND_REACHED", "MAX_TASKS", region,
                            pathKey, "", -1);
                    break;
                }
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
                String region = optionalString(task, "regionId");
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
                if (closedByRecording(path, mapping)) continue;
                candidates.add(mapping);
            }
        }

        /**
         * Whether the recording already decided this branch.
         *
         * <p>The judgement is about the campaign's search space, not about
         * this one query: the campaign may vary its declared roots and
         * nothing else, so a condition whose expression DAG names no root
         * evaluates to the value the recording observed under every
         * admissible replay. Proposing its opposite costs a solver call and,
         * when the solver finds some arm assignment that satisfies it, a
         * whole workload replay that cannot be admitted.</p>
         *
         * <p>Three things make this safe rather than merely fast:</p>
         *
         * <ul>
         *   <li>{@link BranchPredicateAlgebra#symbolicSupport} walks the
         *       whole DAG, guarded-read candidate arms included, so a
         *       condition that reaches a root only through a writer arm is
         *       still seen as root-dependent.</li>
         *   <li>A predicate still holding an unexpanded shared-expression
         *       reference carries leaves this walk cannot see, so it is never
         *       closed. Dependency information that is not complete is a
         *       reason to keep solving.</li>
         *   <li>An inventory that is not {@link
         *       SymbolicRootInventory#usable()} answers "root-dependent" to
         *       everything, which disables this entirely.</li>
         * </ul>
         */
        private boolean closedByRecording(PathObservation path,
                                          SummaryBranchMapping mapping) {
            if (!roots.usable()) return false;
            JsonElement predicate =
                    mapping.witness().sourceSatisfiedPredicateView();
            if (BranchPredicateAlgebra.hasUnexpandedReference(predicate)) {
                return false;
            }
            if (roots.namesRoot(
                    BranchPredicateAlgebra.symbolicSupport(predicate))) {
                rootDependentSites.add(mapping.siteId());
                return false;
            }
            recordClosedByConstant(path, mapping);
            return true;
        }

        private void recordClosedByConstant(PathObservation path,
                                            SummaryBranchMapping mapping) {
            String key = path.regionId() + "\n" + path.pathKey() + "\n"
                    + mapping.siteId() + "\n" + mapping.occurrence();
            if (!closedByConstantKeys.add(key)) return;
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", CLOSED_BY_CONSTANT);
            row.addProperty("authority", "ROOT_FORWARD_SLICE_V1");
            row.addProperty("regionId", path.regionId());
            row.addProperty("pathKey", path.pathKey());
            row.addProperty("siteId", mapping.siteId());
            row.addProperty("method", mapping.witness().method());
            row.addProperty("unitIndex", mapping.witness().unitIndex());
            row.addProperty("occurrence", mapping.occurrence());
            row.addProperty("summaryPcIndex", mapping.summaryPcIndex());
            // The constant: the outcome the recording took, which is now the
            // only outcome this branch has.
            row.addProperty("recordedOutcome", mapping.sourceTakenOutcome());
            row.addProperty("symbolicSupportDigest",
                    mapping.witness().symbolicSupportDigest());
            closedByConstant.add(row);
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
            String targetSite = optionalString(target, "siteId");
            int targetOccurrence = optionalInteger(target, "occurrence", -1);
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
                if (currentSite.equals(optionalString(branch, "siteId"))) {
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
                if (!optionalBool(candidate, "failureTarget", false)
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
                if (!siteId.equals(optionalString(branch, "siteId"))) continue;
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
                if (mapping.siteId().equals(optionalString(branch, "siteId"))
                        && "PATH_ASSUMPTION".equals(
                        optionalString(branch, "policy"))) {
                    int selectedOccurrence = optionalInteger(branch,
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
                if (!"SYMBOLIC".equals(optionalString(action, "mode"))
                        || !"EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1".equals(
                        optionalString(action, "authority"))) {
                    continue;
                }
                String symbol = optionalString(action, "symbol");
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
            // upstream anchor arm supplied its current payload, and
            // regardless of how large the wave's corpus has grown around it.
            // The identity is therefore the semantic flip key alone: the
            // planned occurrence and goal, the branch site, its decision
            // polarity and a digest of the path-prefix DECISIONS -- all of
            // which a later wave reproduces exactly.
            //
            // Mixing the receiver-family snapshot digest in here made the
            // identity of an obligation a function of the whole corpus.  A
            // discharged flip re-replays its own case, that case grows the
            // family snapshot, the grown snapshot renames every obligation,
            // and the next wave no longer recognises the record it just
            // wrote: the closure loop had no fixed point.  The snapshot the
            // solver saw stays on the record below as evidence.
            String key = semanticKey;

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
            task.addProperty(LinkedReplayBundle.FAMILY_DIGEST_FIELD,
                    familySnapshotDigest);
            task.addProperty("regionId", path.regionId());
            task.addProperty("goalId", path.scope().goalId());
            path.scope().loopBound().writeTo(task);
            path.scope().goalKind().writeToTask(task);
            task.addProperty("sourceTaskId", path.sourceTaskId());
            task.addProperty("sourceSummaryId",
                    optionalString(path.replayPayload(), "summaryId"));
            task.addProperty("sourcePathKey", path.pathKey());
            task.addProperty("sourceActivationOccurrenceId",
                    path.occurrenceId());
            replay.addTo(task);
            if (path.scope().goalKind().capturesTargetReach()) {
                VmHandoffEvidence.writeTo(task, path.vmHandoffEvents());
                JsonObject sourceTask = taskById.get(path.sourceTaskId());
                JsonObject selected = sourceTask == null
                        ? new JsonObject()
                        : sourceTask.has("targetBranch")
                        && sourceTask.get("targetBranch").isJsonObject()
                        ? sourceTask.getAsJsonObject("targetBranch")
                        : new JsonObject();
                if (mapping.siteId().equals(optionalString(selected, "siteId"))) {
                    JsonObject next = nextTargetGuard(sourceTask,
                            mapping.siteId());
                    if (next != null) {
                        JsonObject target = new JsonObject();
                        target.addProperty("siteId",
                                optionalString(next, "siteId"));
                        int occurrence = optionalInteger(next,
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
                String kind = explorationGapKind(optionalString(record, "status"));
                if (kind.isEmpty()) continue;
                JsonObject gap = new JsonObject();
                gap.addProperty("kind", kind);
                gap.addProperty("queryKey", optionalString(record, "queryKey"));
                gap.addProperty("reason", optionalString(record, "reason"));
                if (record.has("unsupported")) {
                    gap.add("unsupported", record.get("unsupported"));
                }
                pathCoverageGaps.add(gap);
            }
            coverageGaps.addAll(pathCoverageGaps);
            result.add("coverageGaps", GSON.toJsonTree(coverageGaps));
            result.add(ROOT_SLICE_FIELD, rootSliceTelemetry());
            result.addProperty("coverageState",
                    state == State.CLOSED && coverageGaps.isEmpty()
                            ? "CLOSED" : campaignBoundReached()
                            || hasReplayPath()
                            ? "PARTIAL" : "SEED_ONLY");
            return result;
        }

        /**
         * What the root slice decided here, as telemetry and never a gap.
         *
         * <p>Deliberately not a coverage gap: an obligation the recording
         * already decided is closed, not open, and folding it into
         * {@code coverageGaps} would turn a CLOSED worklist into a PARTIAL
         * one and keep the campaign iterating over work it has proved is
         * pointless. What this does have to do is make the decision visible,
         * so that the next time a wave plans more obligations than its roots
         * justify, the ratio is in the artifact rather than in a profiler.</p>
         */
        private JsonObject rootSliceTelemetry() {
            JsonObject telemetry = new JsonObject();
            telemetry.addProperty("schemaVersion", 1);
            telemetry.addProperty("kind", "REGION_PATH_ROOT_SLICE");
            telemetry.addProperty("authority", "ROOT_FORWARD_SLICE_V1");
            telemetry.addProperty("rootSliceApplied", roots.usable());
            if (!roots.usable()) {
                telemetry.addProperty("withheldReason",
                        roots.incompleteReason());
            }
            telemetry.addProperty("declaredRootLeaves", roots.leaves().size());
            telemetry.addProperty("plannedObligations", tasks.size());
            telemetry.addProperty("closedByConstant", closedByConstant.size());
            telemetry.add("rootDependentSites",
                    GSON.toJsonTree(rootDependentSites));
            telemetry.add("closedByConstantRows",
                    GSON.toJsonTree(closedByConstant));
            if (roots.usable()
                    && tasks.size() > rootDependentSites.size()) {
                JsonObject excess = new JsonObject();
                excess.addProperty("kind", OBLIGATIONS_EXCEED_ROOT_SITES);
                excess.addProperty("plannedObligations", tasks.size());
                excess.addProperty("rootDependentSites",
                        rootDependentSites.size());
                telemetry.add("notice", excess);
            }
            return telemetry;
        }

        private boolean campaignBoundReached() {
            for (JsonObject gap : coverageGaps) {
                if ("BOUND_REACHED".equals(optionalString(gap, "kind"))) {
                    return true;
                }
            }
            return false;
        }

        private boolean hasReplayPath() {
            for (PathObservation path : paths) {
                JsonObject task = taskById.get(path.sourceTaskId());
                if (!optionalString(task, "pathQueryKey").isEmpty()) return true;
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
                String region = optionalString(task, "regionId");
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
                String kind = optionalString(imported, "kind");
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
        String status = optionalString(record, "status");
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
        // The solver reached a verdict and it was "this flip cannot be
        // materialized".
        if ("MATERIALIZATION_GAP".equals(status)) {
            return "PATH_FLIP_MATERIALIZATION_GAP";
        }
        if ("BUNDLE_TOPOLOGY_DIVERGENCE".equals(status)) {
            return "LINKED_REPLAY_LEFT_TOPOLOGY_EPOCH";
        }
        // The solver reached no verdict inside its budget.  The sibling path
        // stays unexplored, so the obligation is an open coverage gap rather
        // than a flip to propose again in this same snapshot.
        if (ConcolicPathFlipSolver.SOLVER_TIMEOUT.equals(status)) {
            return "PATH_FLIP_SOLVER_TIMEOUT";
        }
        return "";
    }

}
