package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
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

    /** Plans the next obligations from the admitted local cases of one
     * topology.
     *
     * <p>README "Delta ownership is also singular" makes this the consumer of
     * the importer's admitted cases: a path whose own occurrence the delta
     * classified as {@code TOPOLOGY_DIVERGENCE} belongs to the next
     * iteration's plan, so no branch-flip obligation may be built across
     * it.</p> */
    public static Result plan(List<JsonObject> summaries,
                              List<JsonObject> executionTasks,
                              List<JsonObject> explorationRecords,
                              Bounds bounds,
                              List<JsonObject> topologyDelta) {
        return new Planner(summaries, executionTasks, explorationRecords,
                bounds, topologyDelta).run();
    }

    private static final class Planner {
        private final Bounds bounds;
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
        /** Activation-independent semantic paths already explored. */
        private final Set<String> plannedSemanticPaths =
                new LinkedHashSet<>();
        /** OCC-1: tasks with at least one boundary-complete activation. */
        private final Set<String> completeActivations = new LinkedHashSet<>();
        /** OCC-1: path keys of activations carried as partial cases. */
        private final Set<String> partialActivations = new LinkedHashSet<>();
        private final Map<String, Integer> pathCountByRegion =
                new LinkedHashMap<>();
        private Planner(List<JsonObject> summaries,
                        List<JsonObject> executionTasks,
                        List<JsonObject> explorationRecords,
                        Bounds bounds,
                        List<JsonObject> topologyDelta) {
            this.bounds = bounds;
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
                    value.regionId() + "\n" + value.pathKey()));
        }

        private Result run() {
            indexObservedCoverage();
            for (PathObservation path : paths) {
                if (path.relationallyComplete()) {
                    completeActivations.add(path.sourceTaskId());
                }
            }
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
                if (!path.relationallyComplete()) {
                    // OCC-1: a task publishes one observation per activation
                    // of its address.  One activation that missed part of the
                    // boundary does not make the task's relation incomplete
                    // as long as another activation satisfied it -- it is one
                    // partial occurrence, carried as its own case and named
                    // here.  A task no activation of which is complete is the
                    // pre-OCC-1 case and stays a hard gap.
                    if (completeActivations.contains(path.sourceTaskId())) {
                        coverageGap("INCOMPLETE_ACTIVATION",
                                "ACTIVATION_BOUNDARY_NOT_COMPLETE",
                                region, pathKey, "", -1);
                        partialActivations.add(pathKey);
                        continue;
                    }
                    gap("INCOMPLETE_REGION_SUMMARY",
                            "RELATIONAL_INPUT_OUTPUT_SUMMARY_NOT_COMPLETE",
                            region, pathKey, "", -1);
                    continue;
                }
                // Keep every activation as a relation case, but plan only
                // once for the activation-independent semantic path. Invalid
                // or partial cases never consume the valid path's allowance.
                boolean plansObligations = plannedSemanticPaths.add(
                        region + "\n" + path.semanticPathKey());
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

            int remainingPathSlots = bounds.maxPathsPerRegion
                    - plannedSemanticPaths.size();
            if (!tasks.isEmpty() && remainingPathSlots <= 0) {
                coverageGap("BOUND_REACHED", "MAX_PATHS_PER_REGION",
                        manifestRegionId(observedRegions),
                        "", "", -1);
                tasks.clear();
            } else if (tasks.size() > remainingPathSlots) {
                coverageGap("BOUND_REACHED", "MAX_PATHS_PER_REGION",
                        manifestRegionId(observedRegions),
                        "", "", -1);
                tasks.subList(remainingPathSlots, tasks.size()).clear();
            }

            JsonObject manifest = manifest(!seenPaths.isEmpty(),
                    observedRegions, observedScopes);
            String coverageState = string(manifest, "coverageState");
            String worklistState = string(manifest, "state");
            // One relation artifact for both coverage states.
            List<JsonObject> relations = new ArrayList<>();
            if (State.CLOSED.name().equals(worklistState)
                    && "CLOSED".equals(coverageState)) {
                relations.addAll(outputRelations(observedScopes,
                        false, coverageState));
            } else if (State.PENDING.name().equals(worklistState)
                    || State.CLOSED.name().equals(worklistState)) {
                relations.addAll(outputRelations(observedScopes,
                        true, coverageState));
            }
            if (!gaps.isEmpty()) {
                tasks.clear();
                relations.clear();
                manifest.addProperty("state", State.GAPPED.name());
                // Relations discovered a gap after the manifest was built,
                // so the coverage it reported is no longer closed.
                manifest.addProperty("coverageState",
                        hasReplayPath() ? "PARTIAL" : "SEED_ONLY");
                manifest.add("gaps", GSON.toJsonTree(gaps));
            }
            return new Result(tasks, manifest, relations);
        }

        private List<JsonObject> outputRelations(
                Map<String, PathObservation.Scope> observedScopes,
                boolean observedOnly, String coverageState) {
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
            // The contract's own statement of which demanded ports are
            // produced only by instance-scoped once-only heap writes, read
            // once for the whole closure.  Empty for every closure the rule
            // never fired on, so the demand below is unchanged there.
            Set<String> onceOnlyPorts = scope.outputClosure()
                    .onceOnlyInstanceScopedPorts();
            List<PathObservation> validPaths = new ArrayList<>();
            for (PathObservation path : paths) {
                if (!path.scope().goalKind().capturesOutputRelation()) {
                    continue;
                }
                OutputClosureContract contract = path.scope().outputClosure();
                if (!outputIdentity.equals(
                        path.scope().outputClosureIdentity())) {
                    gap("OUTPUT_CLOSURE_SCOPE_MISMATCH",
                            "CLOSED_PATHS_HAVE_DIFFERENT_OUTPUT_CLOSURES",
                            path.regionId(), "", "", -1);
                    continue;
                }
                if (!path.hasExactOutputSet(contract.outputPorts())) {
                    // OCC-1: a partial activation is expected to carry fewer
                    // members than the demand -- that is what makes it
                    // partial.  It becomes a case of exactly what it captured
                    // and is already named as an INCOMPLETE_ACTIVATION
                    // coverage gap.  A complete path that misses a demanded
                    // port is still the hard mismatch it always was.
                    if (partialActivations.contains(path.pathKey())) {
                        validPaths.add(path);
                        continue;
                    }
                    // Once-only-root rule
                    // (OutputCaptureSpec#INSTANCE_SCOPED_PRODUCER) -- the same
                    // completeness question the recorder answers in
                    // ConcolicRegionRuntime#completeExactOutputBoundary and
                    // the importer answers in its output-capture count.  A
                    // field belongs to the object, not to the seventh loop
                    // iteration: an instance-scoped heap write's recorded
                    // version is decided once at instance scope, so an
                    // occurrence that never sampled the once-entered write
                    // owes no per-occurrence production of that port and its
                    // expression set is not a mismatch with the demand.  The
                    // planner is the third owner of this check and must not
                    // disagree with the other two.
                    if (onlyOnceOnlyPortsMissing(path,
                            contract.outputPorts(), onceOnlyPorts)) {
                        validPaths.add(path);
                        continue;
                    }
                    gap("OUTPUT_EXPRESSION_SET_MISMATCH",
                            "OUTPUT_EXPRESSION_SET_DOES_NOT_MATCH_DEMAND",
                            region, path.pathKey(), "", -1);
                } else {
                    validPaths.add(path);
                }
                // README CASE-1: a path's edge bindings travel with the path
                // and are stated by the case its observation becomes.
            }
            if (!gaps.isEmpty()) {
                return Collections.emptyList();
            }
            // Two paths whose projected guards are equal and whose relations
            // are not are two cases the relation guard cannot tell apart, so
            // the merged summary's "exactly one case selector" would hold of
            // neither.
            Map<String, String> relationByGuard = new LinkedHashMap<>();
            Map<String, PathObservation> caseByPath = new LinkedHashMap<>();
            for (PathObservation path : validPaths) {
                // OCC-1: two activations of one address are two occurrences
                // that both happened, not two alternatives one guard has to
                // tell apart.  Equal guards across occurrences are normal --
                // the same code ran twice.  Within one occurrence the
                // separation requirement is unchanged.
                String prior = relationByGuard.putIfAbsent(
                        path.occurrenceId() + "\n" + path.relationGuardKey(),
                        path.relationKey());
                if (prior != null && !prior.equals(path.relationKey())) {
                    gap("RELATION_GUARD_DOES_NOT_SEPARATE_CASES",
                            "TWO_RELATIONS_SHARE_ONE_PROJECTED_GUARD",
                            region, path.relationKey(), "", -1);
                    continue;
                }
                caseByPath.putIfAbsent(path.relationKey(), path);
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

            RelationSummary merged = observedOnly
                    ? RelationSummary.observedPathMerge(
                    scope.outputClosure(), caseByPath.values(),
                    coverageState)
                    : RelationSummary.guardedPathMerge(
                    scope.outputClosure(), caseByPath.values());
            return Collections.singletonList(merged.toJson());
        }

        /**
         * Whether the only demanded ports this path did not produce are
         * once-only instance-scoped heap writes.
         *
         * <p>Fail-closed: a path that produced a port outside the demand, or
         * that is missing any port the contract does not name once-only, is
         * the hard set mismatch it has always been.  A port that did produce
         * an expression is never relaxed -- it is simply present on both
         * sides.  {@code onceOnlyPorts} is empty for every closure with no
         * such capture, which makes this exactly the old set equality.</p>
         */
        private static boolean onlyOnceOnlyPortsMissing(
                PathObservation path, Set<String> demanded,
                Set<String> onceOnlyPorts) {
            if (onceOnlyPorts.isEmpty()) return false;
            Set<String> produced = path.producedOutputPorts();
            if (!demanded.containsAll(produced)) return false;
            Set<String> missing = new TreeSet<>(demanded);
            missing.removeAll(produced);
            return !missing.isEmpty() && onceOnlyPorts.containsAll(missing);
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
                outputRelationCandidates(path, task, candidates);
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

        private void outputRelationCandidates(
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
                        .sourceSatisfiedPredicate(),
                        explicitFaultSymbols)) {
                    continue;
                }
                if (abandonsDemandedOutputSite(path, task, mapping)) {
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
                    && fatal.sourceTakenOutcome() != required
                    && ConcolicConstraintSolver
                    .hasLocallyWritableReplayRoot(
                            fatal.witness().sourceSatisfiedPredicate(),
                            task)) {
                result.add(fatal);
            }
            for (SummaryBranchMapping mapping : path.branchMappings()) {
                if (!mapping.isWitnessed()
                        || mapping.policy()
                        != SummaryBranchMapping.Policy.PATH_ASSUMPTION
                        || mapping.summaryPcIndex() >= fatalPc
                        || !declaredTargetPrefix(task, mapping)) {
                    continue;
                }
                if (!ConcolicConstraintSolver
                        .hasLocallyWritableReplayRoot(
                                mapping.witness()
                                        .sourceSatisfiedPredicate(), task)) {
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
         * keeps the rest of the producer path at its witnessed values. */
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

        /** True when the flipped successor provably cannot reach a site the
         * demanded outputs are published at. */
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
                Boolean required = TargetReachPathQueryBuilder
                        .requiredOutcome(branch);
                if (!bool(branch, "failureTarget", false)
                        && required != null && required != desired) {
                    return true;
                }
                for (JsonElement row
                        : array(branch, "guardedSiteOutcomes")) {
                    if (!row.isJsonObject()) continue;
                    JsonObject guarded = row.getAsJsonObject();
                    if (!demanded.contains(string(guarded, "siteId"))) {
                        continue;
                    }
                    Boolean outcome = TargetReachPathQueryBuilder
                            .requiredOutcome(guarded);
                    if (outcome != null && outcome != desired) return true;
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
            attachRecordedReadCut(path, replay, task);
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

        /** Carries this path's recorded guarded reads into the query. */
        private void attachRecordedReadCut(PathObservation path,
                                           BranchReplayContract replay,
                                           JsonObject task) {
            JsonObject recorded = path.recordedSharedState();
            if (recorded.size() == 0) return;
            JsonObject row = new JsonObject();
            row.add(SharedStateEvidence.RECORDED_FIELD, recorded);
            JsonObject payload = RecordedSessionModel.of(
                    Collections.singletonList(row),
                    replay.requiredSatisfiedPredicate(),
                    path.regionId()).queryPayload();
            if (payload.size() > 0) {
                task.add(RecordedSessionModel.QUERY_FIELD, payload);
            }
        }

        private void indexObservedCoverage() {
            for (PathObservation path : paths) {
                if (!path.relationallyComplete()) {
                    continue;
                }
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
                    boolean outputExplore = mapping.isExplore()
                            && !path.regionId().isEmpty()
                            && path.scope().branchSites().contains(
                            mapping.siteId());
                    boolean targetPrefix = observedTargetPrefixes.contains(
                            mapping.decisionIdentity());
                    if (outputExplore || targetPrefix) {
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
                        && !SparseReadCutGate.GAP_KIND.equals(kind)
                        && !"OUTPUT_VERSION_ALIGNMENT_GAP".equals(kind)) {
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
        return "";
    }

}
