package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan.Goal;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/** Builds graph-directed concolic jobs from static regions and concrete
 * runtime-selected region instance plans. */
public final class ConcolicScheduler {
    private static final Pattern LOCAL_CELL = Pattern.compile(
            "^(<.+>)::([^#]+)(?:#.*)?$");
    private ConcolicScheduler() {
    }

    public static void main(String[] args) throws Exception {
        scheduleTargetFirst(Arguments.parse(args));
    }

    private static LoadedInputs loadInputs(Arguments arguments)
            throws IOException {
        requireFile(arguments.regionPlan, "region plan");
        requireFile(arguments.refinedGraph, "runtime-refined graph");
        Files.createDirectories(arguments.outputDirectory);

        JsonObject regionPlanIdentity = artifactIdentity(
                arguments.regionPlan);
        JsonObject refinedGraphIdentity = artifactIdentity(
                arguments.refinedGraph);
        JsonObject symbolicInputsIdentity = arguments.symbolicInputs == null
                ? null : artifactIdentity(arguments.symbolicInputs);
        RuntimePlanArtifact runtimePlan = RuntimePlanArtifact.read(
                arguments.regionPlan);
        List<JsonObject> regions = runtimePlan.regions();
        if (regions.isEmpty()) {
            throw new IOException("runtime plan has no region port catalog: "
                    + arguments.regionPlan);
        }
        List<RegionInstancePlan> regionPlans = runtimePlan.regionPlans();
        if (regionPlans.isEmpty()) {
            throw new IOException("runtime plan contains no region plans: "
                    + arguments.regionPlan);
        }
        List<JsonObject> summaries = arguments.summaries == null
                ? Collections.<JsonObject>emptyList()
                : SharedExpressionTable.expandAll(
                        ArtifactIO.readJsonl(arguments.summaries));
        List<JsonObject> refinedGraph = ArtifactIO.readJsonl(
                arguments.refinedGraph);
        requireRefinedGraph(refinedGraph);
        DefinitionIndex definitions = DefinitionIndex.from(refinedGraph);
        SymbolicInputSelection symbolicInputs =
                SymbolicInputSelection.read(arguments.symbolicInputs,
                        regions);
        Map<String, Region> regionIndex = regionIndex(regions);
        // The identities recorded here are verified once, against the same
        // files, at the point the schedule index commits them.
        return new LoadedInputs(regionPlans, summaries, regionIndex,
                definitions, regionPlanIdentity, refinedGraphIdentity,
                symbolicInputsIdentity, symbolicInputs);
    }

    private static Result scheduleLoaded(
            Arguments arguments, LoadedInputs loaded)
            throws IOException {
        List<Candidate> candidates = candidates(arguments,
                loaded.regionPlans, loaded.regionIndex,
                loaded.definitions);
        Collections.sort(candidates, Candidate.ORDER);

        LoopBoundPolicy loopBound = declaredLoopBounds(
                arguments.maxLoopIterations, loaded.regionPlans);
        Result result = new Result();
        for (Candidate candidate : candidates) {
            JsonArray edgeBindings = objectRows(
                    candidate.goal.edgeBindings());
            if (candidate.targetEdgeBindings != null) {
                edgeBindings = candidate.targetEdgeBindings.deepCopy();
            }
            edgeBindings = deduplicateTopologyEdges(edgeBindings);
            JsonArray taskInputActions = candidate.inputActions;
            JsonArray selectedInputs = loaded.symbolicInputs.select(
                    candidate.goal.plan().regionId(), taskInputActions);
            selectedInputs = removeInboundProtocolHandoffInputs(
                    selectedInputs, edgeBindings,
                    candidate.queryOccurrenceId,
                    CommunicationHandoffSpec.decode(
                            candidate.goal.plan().json()));
            String taskId = candidate.seedTaskId(selectedInputs);
            JsonObject taskQueryOccurrence = queryOccurrenceWithInputs(
                    candidate.queryOccurrence, selectedInputs);
            JsonObject captured = candidate.goal.kind().capturesTargetReach()
                    ? exactTargetSummary(candidate, loaded.summaries) : null;
            // A summary is evidence a previous replay already produced; making
            // its solver query consumes no replay-job slot.
            if (captured != null) {
                result.queries.add(branchQuery(candidate, captured,
                        taskId, taskQueryOccurrence));
            }
            if (result.executionTasks.size() >= arguments.maxJobs) {
                continue;
            }
            ExecutionTask scheduled = ExecutionTask.create(candidate.goal,
                    taskId, selectedInputs,
                    candidate.branches, edgeBindings,
                    loopBound, candidate.ready);
            // json() is the live row by decision (contract/PlanRow): the
            // scheduler annotates the task it has just created, and no typed
            // member it already decoded is derived from these carriers.
            JsonObject executionTask = scheduled.json();
            if (candidate.goal.kind().capturesTargetReach()) {
                // The branch event this occurrence must decide.
                JsonObject target = new JsonObject();
                target.addProperty("siteId", candidate.target.siteId);
                target.addProperty("occurrence",
                        candidate.target.selectedOccurrence);
                executionTask.add("targetBranch", target);
            }

            result.executionTasks.add(scheduled);
        }
        return result;
    }

    /**
     * A selected receive gets its symbolic value from the VM handoff.  A
     * local action for the same exact port would mint a temporary second root
     * before attach, so it is not part of the frozen task.
     */
    static JsonArray removeInboundProtocolHandoffInputs(
            JsonArray actions, JsonArray edgeBindings,
            String occurrenceId,
            Iterable<CommunicationHandoffSpec> declaredHandoffs) {
        Set<String> declaredInboundPorts = new LinkedHashSet<>();
        if (declaredHandoffs != null) {
            for (CommunicationHandoffSpec handoff : declaredHandoffs) {
                if (handoff != null && !handoff.outgoing()) {
                    declaredInboundPorts.add(handoff.portId());
                }
            }
        }
        String receiver = OccurrenceId.parse(occurrenceId).planned();
        Set<String> suppliedPorts = new LinkedHashSet<>();
        for (JsonElement element : edgeBindings == null
                ? new JsonArray() : edgeBindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!AutomaticRegionEdge.tracedExchangeCandidate(binding)
                    || !receiver.equals(OccurrenceId.parse(
                    optionalString(binding, "toOccurrenceId")).planned())) {
                continue;
            }
            String port = optionalString(binding, "toInputPort");
            if (declaredInboundPorts.contains(port)) {
                suppliedPorts.add(port);
            }
        }
        JsonArray retained = new JsonArray();
        for (JsonElement element : actions == null
                ? new JsonArray() : actions) {
            if (!element.isJsonObject()) {
                retained.add(element.deepCopy());
                continue;
            }
            JsonObject action = element.getAsJsonObject();
            if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                    optionalString(action, "mode"))
                    && suppliedPorts.contains(optionalString(action, "symbol"))) {
                continue;
            }
            retained.add(action.deepCopy());
        }
        return retained;
    }

    static Result scheduleTargetFirst(Arguments arguments)
            throws IOException {
        LoadedInputs loaded = loadInputs(arguments);
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                arguments.closureMode == ClosureMode.ACTIVE_OBSERVED
                ? RuntimeWorkflowDiscovery.rankedWorkflow(
                        loaded.regionPlans, loaded.summaries)
                : arguments.closureMode == ClosureMode.SEED_REPLAY
                ? RuntimeWorkflowDiscovery.seedReplayWorkflow(
                        loaded.regionPlans)
                : RuntimeWorkflowDiscovery.rankedWorkflow(
                        loaded.regionPlans);
        if (workflow.scheduledTaskCount() > arguments.maxJobs) {
            throw new IOException("selected exact closure exceeds max jobs: "
                    + workflow.scheduledTaskCount() + " > "
                    + arguments.maxJobs);
        }

        List<Result> scheduled = scheduleSelections(arguments, loaded,
                workflow);

        Map<String, ExecutionTask> tasks = new LinkedHashMap<>();
        Map<String, JsonObject> queries = new LinkedHashMap<>();
        for (int index = 0; index < scheduled.size(); index++) {
            RuntimeWorkflowDiscovery.Selection selection =
                    workflow.selections().get(index);
            Result selected = scheduled.get(index);
            if (selected.executionTasks.size() != 1) {
                throw new IOException("target-first selection emitted "
                        + selected.executionTasks.size()
                        + " execution tasks; campaign="
                        + selection.campaignId);
            }
            ExecutionTask task = selected.executionTasks.get(0);
            ExecutionTask prior = tasks.putIfAbsent(task.taskId(), task);
            if (prior != null && !prior.json().equals(task.json())) {
                throw new IOException("conflicting scheduled taskId: "
                        + task.taskId());
            }
            for (JsonObject query : selected.queries) {
                indexTargetQuery(queries, query);
            }
        }
        Result result = new Result();
        result.executionTasks.addAll(sortedValues(tasks));
        result.queries.addAll(sortedValues(queries));
        Path taskPlan = arguments.outputDirectory.resolve(
                "execution_task_plan.jsonl");
        List<JsonObject> taskRows = new ArrayList<>();
        for (ExecutionTask task : result.executionTasks) {
            taskRows.add(task.json());
        }
        ArtifactIO.replaceJsonl(taskPlan, taskRows);
        ArtifactIO.replaceJsonl(arguments.outputDirectory.resolve(
                "branch_queries.jsonl"), result.queries);
        JsonObject taskPlanIdentity = artifactIdentity(taskPlan);
        JsonObject index = workflow.scheduleIndex(result.executionTasks,
                loaded.regionPlanIdentity, taskPlanIdentity);
        requireArtifactIdentity(arguments.regionPlan,
                loaded.regionPlanIdentity,
                "region plan changed while scheduling");
        requireArtifactIdentity(arguments.refinedGraph,
                loaded.refinedGraphIdentity,
                "runtime-refined graph changed while scheduling");
        if (arguments.symbolicInputs != null) {
            requireArtifactIdentity(arguments.symbolicInputs,
                    loaded.symbolicInputsIdentity,
                    "symbolic input selection changed while scheduling");
        }
        requireArtifactIdentity(taskPlan, taskPlanIdentity,
                "execution task plan changed before index publication");
        // The integrity-checked index is the commit record.
        ArtifactIO.replace(arguments.outputDirectory.resolve(
                        "runtime_workflow_schedule_index.json"),
                CanonicalJson.render(index) + "\n");
        if (result.executionTasks.isEmpty()) {
            // Diagnosed from the plan this run already loaded, not from a
            // second read of the same file.
            throw new IllegalStateException(noCandidateDiagnostic(
                    arguments, loaded.regionPlans));
        }
        return result;
    }

    private static List<Result> scheduleSelections(
            Arguments arguments, LoadedInputs loaded,
            RuntimeWorkflowDiscovery.RankedWorkflow workflow)
            throws IOException {
        List<Result> result = new ArrayList<>();
        for (RuntimeWorkflowDiscovery.Selection selection
                : workflow.selections()) {
            try {
                result.add(scheduleLoaded(arguments.forSelection(selection),
                        loaded));
            } catch (IllegalArgumentException failure) {
                throw new IOException("target-first selection is not "
                        + "executable: campaign=" + selection.campaignId
                        + " occurrence=" + selection.occurrenceId, failure);
            }
        }
        return result;
    }

    private static JsonObject artifactIdentity(Path path)
            throws IOException {
        JsonObject result = new JsonObject();
        result.addProperty("sha256", ArtifactIO.sha256(path));
        result.addProperty("sizeBytes", Files.size(path));
        return result;
    }

    private static void requireArtifactIdentity(
            Path path, JsonObject expected, String message)
            throws IOException {
        JsonObject actual = artifactIdentity(path);
        if (expected == null || !expected.equals(actual)) {
            throw new IOException(message + ": " + path);
        }
    }

    /** The exact target-query aggregation seam used by target-first. */
    static void indexTargetQuery(Map<String, JsonObject> queries,
                                 JsonObject query) throws IOException {
        String key = JsonFields.optionalString(query, "queryKey");
        if (key.isEmpty()) {
            throw new IOException("scheduled row has no queryKey");
        }
        JsonObject prior = queries.putIfAbsent(key, query);
        if (prior != null && !prior.equals(query)) {
            throw new IOException("conflicting scheduled queryKey: " + key);
        }
    }

    private static <T> List<T> sortedValues(Map<String, T> values) {
        List<String> keys = new ArrayList<>(values.keySet());
        Collections.sort(keys);
        List<T> result = new ArrayList<>();
        for (String key : keys) result.add(values.get(key));
        return result;
    }

    /** One causal edge can be represented by a refined runtime row and by a
     * compact closure row. */
    private static JsonArray objectRows(JsonArray source) {
        JsonArray result = new JsonArray();
        for (JsonElement element : source) {
            if (element.isJsonObject()) {
                result.add(element.deepCopy());
            }
        }
        return result;
    }

    private static JsonArray deduplicateTopologyEdges(JsonArray bindings)
            throws IOException {
        Map<String, JsonObject> rows = new LinkedHashMap<>();
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) {
                throw new IOException("edge binding must be an object");
            }
            JsonObject row = element.getAsJsonObject();
            String edgeId = optionalString(row, "edgeId");
            if (edgeId.isEmpty()) {
                throw new IOException("edge binding has no edgeId");
            }
            JsonObject merged = rows.get(edgeId);
            if (merged == null) {
                rows.put(edgeId, row.deepCopy());
                continue;
            }
            for (Map.Entry<String, JsonElement> field : row.entrySet()) {
                JsonElement prior = merged.get(field.getKey());
                if (prior == null) {
                    merged.add(field.getKey(), field.getValue().deepCopy());
                } else if (!prior.equals(field.getValue())) {
                    throw new IOException("conflicting edge binding "
                            + edgeId + " field " + field.getKey());
                }
            }
        }
        JsonArray result = new JsonArray();
        for (JsonObject row : rows.values()) result.add(row.deepCopy());
        return result;
    }

    private static List<Candidate> candidates(Arguments arguments,
                                              List<RegionInstancePlan>
                                                      regionPlans,
                                              Map<String, Region> regions,
                                              DefinitionIndex definitions)
            throws IOException {
        List<Candidate> result = new ArrayList<>();
        for (RegionInstancePlan plan : regionPlans) {
            // Target-first scheduling selects one exact occurrence at a time.
            if (!arguments.occurrenceId.isEmpty()
                    && !arguments.occurrenceId.equals(plan.occurrenceId())) {
                continue;
            }
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(plan.regionId())) {
                continue;
            }
            Region region = regions.get(plan.regionId());
            if (region == null) {
                continue;
            }
            for (Goal goal : plan.goals()) {
                if (!arguments.goalId.isEmpty()
                        && !arguments.goalId.equals(goal.goalId())) {
                    continue;
                }
                if (!goal.replayable()) {
                    continue;
                }
                appendGoalCandidates(arguments, result, goal,
                        definitions);
            }
        }
        return result;
    }

    /** The per-loop {@code K_L} values declared by the region plan. Explicit
     * declarations remain authoritative even when they equal the inherited
     * bound, so their loop sites do not become undeclared. */
    static LoopBoundPolicy declaredLoopBounds(
            int inheritedBound, List<RegionInstancePlan> regionPlans) {
        Map<String, Integer> declared = new TreeMap<>();
        for (RegionInstancePlan plan : regionPlans) {
            for (JsonElement element : array(plan.json(),
                    BoundedLoopComposition.PLAN_FIELD)) {
                if (!element.isJsonObject()) continue;
                JsonObject loop = element.getAsJsonObject();
                String loopSiteId = optionalString(loop,
                        LoopBoundPolicy.LOOP_SITE_ID);
                int bound = optionalInteger(loop, LoopBoundPolicy.LOOP_BODY_BOUND, 0);
                if (loopSiteId.isEmpty() || bound < 1) continue;
                Integer held = declared.put(loopSiteId, bound);
                if (held != null && held.intValue() != bound) {
                    throw new IllegalStateException(
                            BoundedLoopComposition.LOOP_BODY_BOUND_DISAGREES
                                    + ": loop " + loopSiteId + " is planned"
                                    + " under K_L=" + held + " and K_L="
                                    + bound + "; one loop has one prefix");
                }
            }
        }
        return LoopBoundPolicy.cfgBackedges(inheritedBound, declared);
    }

    private static void appendGoalCandidates(
            Arguments arguments, List<Candidate> result, Goal goal,
            DefinitionIndex definitions)
            throws IOException {
            Set<String> definitionMethods =
                    goal.runtimeDefinitionMethods();
            if (goal.kind().capturesRegionPath()) {
                JsonArray branches = goal.branches();
                JsonArray inputActions = materializationPlan(
                        goal, goal.symbolize(), definitions, definitionMethods,
                        branches);
                result.add(new Candidate(goal, branches,
                        TargetBranch.regionPath(), true,
                        inputActions, true,
                        goal.plan().occurrenceId(),
                        new JsonObject(), null));
                return;
            }
            JsonArray branches = goal.branches();
            int eligibleFailureTargets = 0;
            Set<String> guardedTargets = new LinkedHashSet<>();
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!eligibleFailureTarget(branch)) continue;
                eligibleFailureTargets++;
                for (JsonElement cell : array(branch,
                        RuntimeSelectedRegionFinalizer
                                .FAILURE_TARGET_CELLS)) {
                    if (cell.isJsonPrimitive()) {
                        guardedTargets.add(cell.getAsString());
                    }
                }
            }
            // What may not be ambiguous is the failure this occurrence is
            // planned for, not how many conditional sites decide it.
            if (eligibleFailureTargets == 0 || guardedTargets.size() > 1) {
                throw new IllegalArgumentException(
                        "UNSUPPORTED_AMBIGUOUS_TARGET_PATH: expected one "
                                + "guarded failure target; found "
                                + (guardedTargets.size() > 1
                                ? guardedTargets.size()
                                + " guarded failure targets"
                                : eligibleFailureTargets
                                + " eligible failure targets"));
            }
            String queryInstance = targetQueryInstance(arguments, goal);
            // One target task drives the bounded path worklist for the whole
            // guarded throw.
            JsonArray targetSourceFrontier = materializationPlan(goal,
                    goal.symbolize(), definitions, definitionMethods,
                    branches);
            for (int index = 0; index < branches.size(); index++) {
                JsonElement element = branches.get(index);
                if (!element.isJsonObject()) {
                    continue;
                }
                JsonObject branch = element.getAsJsonObject();
                String siteId = optionalString(branch, "siteId");
                if (!optionalBool(branch, "failureTarget", false)) {
                    continue;
                }
                if (!optionalBool(branch, "observed", false)
                        || !branch.has("requiredOutcome")
                        || branch.get("requiredOutcome").isJsonNull()) {
                    continue;
                }
                boolean required = optionalBool(branch, "requiredOutcome", false);
                TargetBranch target = TargetBranch.select(
                        siteId, array(branch, "occurrences"), required);
                if (target == null) {
                    continue;
                }
                boolean hasWitness = target.observedOutcome == required;
                boolean explore = "EXPLORE".equals(optionalString(branch, "policy"));
                if (hasWitness && !explore) {
                    continue;
                }
                // A target task explores exactly one branch; the rest of the
                // slice is replayed prefix.
                JsonArray reachSlice = targetReachBranchSlice(branches,
                        target);
                JsonArray inputActions = materializationPlan(goal,
                        goal.symbolize(), definitions,
                        definitionMethods, reachSlice);
                inputActions = targetSymbolicFrontier(inputActions);
                inputActions = mergeSymbolicFrontier(inputActions,
                        targetSourceFrontier);
                JsonArray targetBindings = targetInputBindings(goal,
                        queryInstance);
                result.add(new Candidate(goal,
                        reachSlice, target,
                        hasWitness, inputActions, true,
                        queryInstance,
                        targetQueryOccurrence(arguments, goal,
                                inputActions, targetBindings),
                        targetBindings));
            }
    }

    private static boolean eligibleFailureTarget(JsonObject branch) {
        if (!optionalBool(branch, "failureTarget", false)
                || optionalBool(branch, "loopControlGuard", false)
                || !optionalBool(branch, "observed", false)
                || !branch.has("requiredOutcome")
                || branch.get("requiredOutcome").isJsonNull()) {
            return false;
        }
        return TargetBranch.select(optionalString(branch, "siteId"),
                array(branch, "occurrences"),
                optionalBool(branch, "requiredOutcome", false)) != null;
    }

    private static String targetQueryInstance(
            Arguments arguments, Goal goal) {
        return arguments.occurrenceId.isEmpty()
                ? goal.plan().occurrenceId()
                : arguments.occurrenceId;
    }

    private static JsonObject targetQueryOccurrence(
            Arguments arguments, Goal goal, JsonArray actions,
            JsonArray bindings) {
        String selected = targetQueryInstance(arguments, goal);
        if (!selected.equals(goal.plan().occurrenceId())) {
            throw new IllegalArgumentException(
                    "target goal does not match selected occurrence "
                            + selected);
        }
        JsonObject result = new JsonObject();
        result.addProperty("occurrenceId", selected);
        Set<String> selectedPorts = new LinkedHashSet<>();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) continue;
            String port = optionalString(element.getAsJsonObject(), "symbol");
            if (!port.isEmpty()) selectedPorts.add(port);
        }
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            String port = optionalString(element.getAsJsonObject(), "toInputPort");
            if (!port.isEmpty()) selectedPorts.add(port);
        }
        JsonArray ports = new JsonArray();
        for (String port : selectedPorts) ports.add(port);
        result.add("inputPorts", ports);
        return result;
    }

    /** A target VM job has no reason to materialize a concrete owner merely
     * because the backward slice traversed through it. */
    private static JsonArray targetSymbolicFrontier(JsonArray actions) {
        JsonArray result = new JsonArray();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!InputActionCatalog.Mode.SYMBOLIC.name().equals(
                    optionalString(action, "mode"))) {
                continue;
            }
            result.add(action.deepCopy());
        }
        return result;
    }

    /** Adds every symbolic carrier needed by another guard of the same throw. */
    private static JsonArray mergeSymbolicFrontier(
            JsonArray branchActions, JsonArray guardedTargetActions) {
        JsonArray result = branchActions == null
                ? new JsonArray() : branchActions.deepCopy();
        Set<String> represented = new LinkedHashSet<>();
        for (JsonElement element : result) {
            if (element.isJsonObject()) {
                represented.add(optionalString(element.getAsJsonObject(), "symbol"));
            }
        }
        for (JsonElement element : guardedTargetActions == null
                ? new JsonArray() : guardedTargetActions) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String symbol = optionalString(action, "symbol");
            if (!symbol.isEmpty() && represented.add(symbol)
                    && InputActionCatalog.Mode.SYMBOLIC.name().equals(
                    optionalString(action, "mode"))) {
                result.add(action.deepCopy());
            }
        }
        return result;
    }

    /** Package-visible for the focused target-component admission contract. */
    static JsonArray targetInputBindings(
            Goal goal, String queryInstance) {
        JsonArray result = new JsonArray();
        for (JsonElement element : goal.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (queryInstance.equals(optionalString(binding,
                    "toOccurrenceId"))
                    && AutomaticRegionEdge
                    .tracedExchangeCandidate(binding)) {
                result.add(binding.deepCopy());
            }
        }
        return result;
    }

    /** A target task solves one failure-directed branch. */
    private static JsonArray targetReachBranchSlice(
            JsonArray branches, TargetBranch target) {
        JsonArray result = new JsonArray();
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject().deepCopy();
            if (target.siteId.equals(optionalString(branch, "siteId"))) {
                branch.addProperty("policy", "EXPLORE");
                branch.addProperty("policyReason",
                        "TARGET_REACH_SELECTED_FAILURE_BRANCH");
            } else if ("EXPLORE".equals(optionalString(branch, "policy"))) {
                branch.addProperty("policy", "PATH_ASSUMPTION");
                branch.addProperty("policyReason",
                        "TARGET_REACH_PREFIX_CONTEXT");
            }
            result.add(branch);
        }
        return result;
    }

    /** Bounded control metadata needed to distinguish a terminal exception
     * guard from an observed frontier leading to a still-unobserved guard. */
    private static JsonArray targetGuardCatalog(JsonArray branches) {
        JsonArray result = new JsonArray();
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (!optionalBool(branch, "failureTarget", false)) continue;
            JsonObject compact = new JsonObject();
            for (String field : new String[]{
                    "siteId", "failureTarget", "requiredOutcome",
                    RuntimeSelectedRegionFinalizer.FAILURE_TARGET_CELLS,
                    "guardedSiteOutcomes"}) {
                JsonElement value = branch.get(field);
                if (value != null && !value.isJsonNull()) {
                    compact.add(field, value.deepCopy());
                }
            }
            result.add(compact);
        }
        return result;
    }

    private static JsonArray materializationPlan(
            Goal goal, JsonArray sourceActions,
            DefinitionIndex definitions,
            Set<String> regionMethods,
            JsonArray demandedBranches) {
        JsonArray result = new JsonArray();
        Set<String> represented = new LinkedHashSet<>();
        // The frame the root-entry hooks are injected into.
        String planRootMethod = optionalString(object(goal.plan().json(),
                "rootSelector"), "method");
        Set<String> guardDependent = definitions.guardDependentCells(
                exploredGuardOperands(demandedBranches));
        for (JsonElement element : sourceActions) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject action = element.getAsJsonObject();
            JsonObject binding = action.deepCopy();
            String location = optionalString(action, "location");
            String cell = optionalString(action, "cell");
            String dependencyRole = DependencyRole.normalize(
                    action.get("dependencyRole"));
            // A container type describes how an admitted value frontier is
            // materialized; it is not authority to turn a structural owner
            // into a fresh symbolic input.  Consumer-side structural
            // receivers keep their concrete container identity while the
            // propagated element expressions remain symbolic.  Explicit
            // VALUE_FRONTIER containers still use the bounded model.
            if (DependencyRole.VALUE_FRONTIER.equals(dependencyRole)
                    && JavaContainerTypes.shape(optionalString(action, "javaType"))
                    != JavaContainerTypes.Shape.NONE) {
                binding.addProperty("symbolicDemand",
                        "BOUNDED_CONTAINER_STATE");
            }
            if (concreteOnlyInput(binding)
                    || !DependencyRole.VALUE_FRONTIER.equals(
                    dependencyRole)) {
                addConcreteInputAction(result, represented, binding,
                        concreteOnlyInputReason(action, dependencyRole));
                continue;
            }
            boolean boundedContainerState =
                    supportedBoundedContainerState(binding, location);
            String unsupportedLeaf = boundedContainerState ? ""
                    : unsupportedSymbolicLeafReason(action, location, cell);
            if (!unsupportedLeaf.isEmpty()) {
                addConcreteInputAction(result, represented, binding,
                        unsupportedLeaf);
                continue;
            }
            if (staticSyntheticConstant(action)) {
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_STATIC_SYNTHETIC_CONSTANT");
                continue;
            }
            String structureControl = structureControlReason(action);
            if (!structureControl.isEmpty()) {
                // These values describe the concrete execution structure
                // selected for replay.
                binding.addProperty("structureControlReason",
                        structureControl);
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_STRUCTURE_CONTROL");
                continue;
            }
            if (unguardedPayloadLeaf(action, definitions,
                    guardDependent)) {
                // Symbolic freedom is only worth its cost when some explored
                // decision can read the value.
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_UNGUARDED_PAYLOAD");
                continue;
            }
            if (action.has("observed")
                    && !optionalBool(action, "observed", false)) {
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_UNOBSERVED_INPUT");
                continue;
            }
            if ("ARGUMENT".equals(location)
                    || "ARGUMENT_FIELD".equals(location)
                    || "RECEIVER_FIELD".equals(location)) {
                String argumentMethod = optionalString(action, "method");
                int argumentIndex = optionalInteger(action, "index", -1);
                if ("ARGUMENT".equals(location)
                        && !argumentMethod.isEmpty()
                        && !argumentMethod.equals(planRootMethod)
                        && argumentIndex >= 0) {
                    // The value is an argument of a frame that is not this
                    // plan's root, so the root-entry hook cannot see it: that
                    // hook is injected at the root and matches by position
                    // alone, and the root of a server fragment is the serving
                    // thread's own entry, which has no arguments at all.
                    binding.addProperty("bindingMode", "METHOD_ARGUMENT");
                    binding.addProperty("method", argumentMethod);
                    binding.addProperty("index", argumentIndex);
                } else {
                    binding.addProperty("bindingMode", "ROOT_ENTRY");
                }
            } else if ("ARGUMENT_FIELD_PATH".equals(location)) {
                if (FieldPathSpec.hasNonEmptyPaths(action, "fieldPaths")) {
                    binding.addProperty("bindingMode", "ROOT_ENTRY");
                } else {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_UNRESOLVED_ARGUMENT_FIELD_PATH");
                    continue;
                }
            } else if ("CALL_RETURN".equals(location)) {
                if (!boundedContainerState
                        && JavaPrimitiveBoxing.deterministicValueOfReturn(
                        cell)) {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_DETERMINISTIC_BOXING_RETURN");
                    continue;
                }
                if (!boundedContainerState
                        && JavaContainerTypes.symbolicResultReturn(cell)) {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_CONTAINER_RESULT_RETURN");
                    continue;
                }
                String returnCell = cell;
                String sourceKind = optionalString(action, "sourceKind");
                if (RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                        .equals(sourceKind)
                        || RuntimeSelectedRegionFinalizer.EXTERNAL_CALL_RETURN
                        .equals(sourceKind)) {
                    String callee = optionalString(action, "declaredCallee");
                    if (!callee.isEmpty()) returnCell = callee + ".return";
                }
                JsonArray sites = definitions.returnSites(returnCell,
                        regionMethods);
                sites = exactCallReturnSite(action, sites);
                if (sites.size() == 0) {
                    addConcreteInputAction(result, represented, binding,
                            "CONCRETE_NO_RESOLVED_RETURN_SITE");
                    continue;
                }
                for (JsonElement siteElement : sites) {
                    JsonObject site = siteElement.getAsJsonObject();
                    JsonObject localBinding = binding.deepCopy();
                    localBinding.addProperty("bindingMode",
                            "LOCAL_DEFINITION");
                    localBinding.addProperty("method",
                            optionalString(site, "method"));
                    localBinding.addProperty("local",
                            optionalString(site, "local"));
                    JsonArray oneSite = new JsonArray();
                    oneSite.add(site.deepCopy());
                    localBinding.add("definitionSites", oneSite);
                    addInputAction(result, represented, localBinding,
                            InputActionCatalog.Mode.SYMBOLIC);
                }
                continue;
            } else if ("HEAP_OBJECT_FIELD".equals(location)) {
                binding.addProperty("bindingMode", "FIELD_ACCESS");
            } else {
                addConcreteInputAction(result, represented, binding,
                        "CONCRETE_UNSUPPORTED_INPUT_LOCATION");
                continue;
            }
            addInputAction(result, represented, binding,
                    InputActionCatalog.Mode.SYMBOLIC);
        }
        for (JsonElement element : sourceActions) {
            if (!element.isJsonObject()
                    || represented.contains(optionalString(
                    element.getAsJsonObject(), "symbol"))) {
                continue;
            }
            addInputAction(result, represented,
                    element.getAsJsonObject().deepCopy(),
                    InputActionCatalog.Mode.DECLARATION_ONLY);
        }
        return result;
    }

    static JsonArray exactCallReturnSite(
            JsonObject action, JsonArray sites) {
        String sourceKind = optionalString(action, "sourceKind");
        if (!RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT.equals(
                sourceKind)
                && !RuntimeSelectedRegionFinalizer.EXTERNAL_CALL_RETURN
                .equals(sourceKind)) {
            return sites;
        }
        String caller = optionalString(action, "callerMethod");
        int unitIndex = optionalInteger(action, "unitIndex", -1);
        JsonArray exact = new JsonArray();
        if (caller.isEmpty() || unitIndex < 0) return exact;
        for (JsonElement element : sites) {
            if (!element.isJsonObject()) continue;
            JsonObject site = element.getAsJsonObject();
            if (caller.equals(optionalString(site, "method"))
                    && unitIndex == optionalInteger(site, "unitIndex", -1)) {
                exact.add(site.deepCopy());
            }
        }
        return exact;
    }

    /** Operands of the decisions this task actually reopens. */
    private static Set<String> exploredGuardOperands(JsonArray branches) {
        Set<String> result = new LinkedHashSet<>();
        if (branches == null) {
            return result;
        }
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (!"EXPLORE".equals(optionalString(branch, "policy"))) continue;
            for (JsonElement operand : array(branch, "operandCells")) {
                String cell = operand.isJsonPrimitive()
                        ? operand.getAsString().trim() : "";
                if (!cell.isEmpty()) result.add(cell);
            }
        }
        return result;
    }

    /** R1: a leaf earns a solver dimension only by being able to move some
     * explored decision. */
    private static boolean unguardedPayloadLeaf(
            JsonObject action, DefinitionIndex definitions,
            Set<String> guardDependent) {
        if (guardDependent.isEmpty()) {
            return false;
        }
        boolean represented = false;
        for (String cell : dependenceOrigins(action)) {
            if (guardDependent.contains(cell)) {
                return false;
            }
            represented |= definitions.knownCell(cell);
        }
        return represented;
    }

    private static List<String> dependenceOrigins(JsonObject action) {
        List<String> result = new ArrayList<>();
        for (JsonElement element : array(action, "dependencyCells")) {
            if (element.isJsonPrimitive()) {
                result.add(element.getAsString().trim());
            }
        }
        String cell = optionalString(action, "cell");
        if (!cell.isEmpty() && !result.contains(cell)) {
            result.add(cell);
        }
        return result;
    }

    private static boolean concreteOnlyInput(JsonObject action) {
        String demand = optionalString(action, "symbolicDemand");
        return optionalBool(action, "captureRootOnly", false)
                || optionalBool(action, "loopControlOnly", false)
                || optionalBool(action, "controlOnly", false)
                || optionalBool(action, "pathAssumptionOnly", false)
                || demand.startsWith("CONCRETE_");
    }

    /** Admits only values for which the current VM/SMT contract has a compact
     * scalar representation. */
    static String unsupportedSymbolicLeafReason(
            JsonObject action, String location, String cell) {
        String javaType = optionalString(action, "javaType");
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                javaType);
        boolean supportedScalar = (descriptor.length() == 1
                && "ZBCSIJFD".contains(descriptor))
                || "Ljava/lang/String;".equals(descriptor);
        boolean supportedPrimitiveArray = false;
        int component = 0;
        while (component < descriptor.length()
                && descriptor.charAt(component) == '[') {
            component++;
        }
        if (component > 0 && component + 1 == descriptor.length()) {
            supportedPrimitiveArray = "ZBCSIJFD".indexOf(
                    descriptor.charAt(component)) >= 0;
        }
        if (!supportedScalar && !supportedPrimitiveArray) {
            return "CONCRETE_UNSUPPORTED_LEAF_TYPE";
        }

        if (!("RECEIVER_FIELD".equals(location)
                || "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)
                || "HEAP_OBJECT_FIELD".equals(location))) {
            return "";
        }

        List<String> path = exactActionFieldPath(action, cell);
        if (path.isEmpty()) {
            return "CONCRETE_AMBIGUOUS_FIELD_PATH";
        }
        FieldPathSpec.DeclaredField leaf = declaredLeaf(action, cell);
        if (leaf == null) {
            return "CONCRETE_UNDECLARED_FIELD_LEAF";
        }
        if (!leaf.name().equals(path.get(path.size() - 1))) {
            return "CONCRETE_FIELD_LEAF_NAME_MISMATCH";
        }
        if (!descriptor.equals(
                JavaPrimitiveSmtSemantics.javaTypeDescriptor(leaf.type()))) {
            return "CONCRETE_FIELD_LEAF_TYPE_MISMATCH";
        }
        return "";
    }

    /** Admits a container identity only as a bounded relational state port. */
    private static boolean supportedBoundedContainerState(
            JsonObject action, String location) {
        if (!"BOUNDED_CONTAINER_STATE".equals(
                optionalString(action, "symbolicDemand"))) {
            return false;
        }
        String javaType = optionalString(action, "javaType");
        if (JavaContainerTypes.shape(javaType)
                == JavaContainerTypes.Shape.NONE) {
            return false;
        }
        return "ARGUMENT".equals(location)
                || "RECEIVER_FIELD".equals(location)
                || "ARGUMENT_FIELD".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location)
                || "HEAP_OBJECT_FIELD".equals(location)
                || "CALL_RETURN".equals(location);
    }

    private static List<String> exactActionFieldPath(
            JsonObject action, String cell) {
        List<List<String>> paths = FieldPathSpec.paths(action, "fieldPaths");
        if (action.has("fieldPaths")) {
            return paths.size() == 1
                    ? paths.get(0) : Collections.<String>emptyList();
        }
        List<String> path = FieldPathSpec.stringArray(action, "fieldPath");
        if (action.has("fieldPath")) return path;
        return FieldPathSpec.path(cell);
    }

    private static FieldPathSpec.DeclaredField declaredLeaf(
            JsonObject action, String cell) {
        // The declared field path states the leaf exactly; the root signature
        // is the leaf only when the path is one hop.  Order says so.
        for (String signature : new String[]{
                pathLeafFieldSignature(action, cell),
                firstNonBlank(optionalString(action, "accessFieldSignature"),
                        optionalString(action, "leafFieldSignature")), cell}) {
            FieldPathSpec.DeclaredField declared =
                    FieldPathSpec.declaredField(signature);
            if (declared != null) return declared;
        }
        return null;
    }

    /** The declaration of the last hop of a receiver/heap field path. */
    private static String pathLeafFieldSignature(JsonObject action,
                                                 String cell) {
        JsonArray declarations = array(action, "fieldPathDeclarations");
        List<String> path = exactActionFieldPath(action, cell);
        if (declarations.size() == 0 || declarations.size() != path.size()) {
            return "";
        }
        JsonElement last = declarations.get(declarations.size() - 1);
        return last != null && last.isJsonPrimitive()
                ? last.getAsString() : "";
    }

    private static boolean staticSyntheticConstant(JsonObject action) {
        if ("CONSTANT".equals(optionalString(action, "sourceKind"))) {
            return true;
        }
        List<String> path = exactActionFieldPath(action,
                optionalString(action, "cell"));
        return !path.isEmpty()
                && "$assertionsDisabled".equals(
                path.get(path.size() - 1));
    }

    /** Classifies compiler/runtime structure projections, not application
     * values. */
    private static String structureControlReason(JsonObject action) {
        List<String> path = exactActionFieldPath(action,
                optionalString(action, "cell"));
        String leaf = path.isEmpty() ? "" : path.get(path.size() - 1);
        if (compilerSwitchDispatchTable(leaf)) {
            return "COMPILER_SWITCH_DISPATCH_TABLE";
        }
        if (enumOrdinalProjection(action)) {
            return "ENUM_DISPATCH_ORDINAL";
        }
        if (structuralContainerCardinality(action, leaf)) {
            return "FIXED_CONTAINER_CARDINALITY";
        }
        return "";
    }

    private static boolean compilerSwitchDispatchTable(String leaf) {
        return SharedFieldFlow.compilerSwitchDispatchField(leaf);
    }

    private static boolean enumOrdinalProjection(JsonObject action) {
        for (String signature : accessorSignatures(action)) {
            if ("<java.lang.Enum: int ordinal()>".equals(signature)) {
                return true;
            }
        }
        return false;
    }

    private static boolean structuralContainerCardinality(
            JsonObject action, String leaf) {
        for (String signature : accessorSignatures(action)) {
            if (JavaContainerTypes.structuralCardinalityOperation(
                    signature)) {
                return true;
            }
            // Custom collection implementations commonly expose their exact
            // backing cardinality through a direct size() accessor.
            if ("size".equals(leaf)
                    && signature.matches("^<[^:>]+: int size\\(\\)>$")) {
                return true;
            }
        }
        if (!"size".equals(leaf)
                || !"I".equals(JavaPrimitiveSmtSemantics
                .javaTypeDescriptor(optionalString(action, "javaType")))) {
            return false;
        }
        // A direct read of an owner's exact `int size` backing field is the
        // same cardinality projection even when no accessor call is present.
        FieldPathSpec.DeclaredField declared = declaredLeaf(action,
                optionalString(action, "cell"));
        return declared != null && "size".equals(declared.name())
                && "I".equals(JavaPrimitiveSmtSemantics
                .javaTypeDescriptor(declared.type()));
    }

    private static List<String> accessorSignatures(JsonObject action) {
        List<String> result = new ArrayList<>();
        for (String field : new String[]{"declaredCallee",
                "accessorDeclaredCallee", "implementationMethod",
                "accessorImplementationMethod"}) {
            String signature = optionalString(action, field);
            if (!signature.isEmpty() && !result.contains(signature)) {
                result.add(signature);
            }
        }
        JsonObject materialization = object(action, "materialization");
        for (String field : new String[]{"declaredCallee",
                "implementationMethod"}) {
            String signature = optionalString(materialization, field);
            if (!signature.isEmpty() && !result.contains(signature)) {
                result.add(signature);
            }
        }
        return result;
    }

    private static void addInputAction(
            JsonArray result, Set<String> represented,
            JsonObject action, InputActionCatalog.Mode mode) {
        action.addProperty("mode", mode.name());
        represented.add(optionalString(action, "symbol"));
        result.add(action);
    }

    /** The only way an input leaves {@link #materializationPlan} concrete. */
    static void addConcreteInputAction(
            JsonArray result, Set<String> represented,
            JsonObject binding, String reason) {
        binding.addProperty("symbolicDemand",
                reason == null || reason.trim().isEmpty()
                        ? "CONCRETE_UNNAMED_REFUSAL" : reason.trim());
        addInputAction(result, represented, binding,
                InputActionCatalog.Mode.CONCRETE);
    }

    /** Names why an action was concrete before any leaf support was examined:
     * either the producing stage already declared it concrete-only, or its
     * dependency role is not a value frontier at all. */
    static String concreteOnlyInputReason(
            JsonObject action, String dependencyRole) {
        String authored = optionalString(action, "symbolicDemand");
        if (authored.startsWith("CONCRETE_")) {
            return authored;
        }
        if (optionalBool(action, "captureRootOnly", false)) {
            return "CONCRETE_CAPTURE_ROOT_ONLY";
        }
        if (optionalBool(action, "loopControlOnly", false)) {
            return "CONCRETE_LOOP_CONTROL_ONLY";
        }
        if (optionalBool(action, "controlOnly", false)) {
            return "CONCRETE_CONTROL_ONLY";
        }
        if (optionalBool(action, "pathAssumptionOnly", false)) {
            return "CONCRETE_PATH_ASSUMPTION_ONLY";
        }
        return "CONCRETE_NON_VALUE_FRONTIER_ROLE:"
                + (dependencyRole == null || dependencyRole.isEmpty()
                ? "NONE" : dependencyRole);
    }

    /** The region port catalog of one campaign, keyed by region id. */
    private static Map<String, Region> regionIndex(List<JsonObject> regions) {
        Map<String, Region> index = new LinkedHashMap<>();
        for (JsonObject row : regions) {
            Region region = new Region(row);
            if (!region.regionId.isEmpty()) {
                index.put(region.regionId, region);
            }
        }
        return index;
    }

    private static JsonObject branchQuery(Candidate candidate,
                                          JsonObject summary,
                                          String seedTaskId,
                                          JsonObject queryOccurrence) {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 1);
        query.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        // scheduleTargetFirst indexes every selected query by this stable
        // semantic identity before the builder consumes its fields.
        query.addProperty("queryKey",
                targetBranchQueryKey(seedTaskId));
        query.addProperty("goalId", candidate.goal.goalId());
        query.addProperty("regionId", candidate.goal.plan().regionId());
        query.addProperty("sourceKey", candidate.goal.plan().sourceKey());
        query.addProperty("occurrenceId",
                candidate.queryOccurrenceId);
        query.add("selectedTargetOccurrence",
                queryOccurrence.deepCopy());
        query.addProperty("targetSiteId", candidate.target.siteId);
        query.addProperty("fatalRequiredTakenOutcome",
                candidate.target.requiredOutcome);
        query.add("targetGuardCatalog",
                targetGuardCatalog(candidate.branches));
        // The query is the target relation consumed by composition.
        LoopBoundPolicy.decode(summary).writeTo(query);
        try {
            SummaryBranchMapping concrete = directConcreteTarget(
                    candidate, summary);
            if (concrete != null) {
                query.add(TargetReachPathQueryBuilder
                                .TARGET_CONCRETE_OBSERVATION,
                        concrete.concreteObservation().toJson());
            } else {
                BranchReplayContract contract;
                try {
                    contract = BranchReplayContract.fromSummary(summary,
                        candidate.target.siteId,
                        candidate.target.selectedOccurrence);
                    if (contract.source().isPcPredicateDecision()
                            || contract.source().sourceTakenOutcome()
                            != candidate.target.observedOutcome
                            || contract.requiredTakenOutcome()
                            != candidate.target.desiredOutcome) {
                        throw new IllegalArgumentException(
                                "captured branch polarity differs from selection");
                    }
                } catch (IllegalArgumentException noDirectTargetWitness) {
                    contract = latestTargetSeedDecision(candidate, summary);
                }
                // This artifact is consumed by the target path-set builder,
                // not by the local path-flip solver.
                // The scheduler loaded summaries through one expression-DAG
                // decoder.  Keep that sharing until this query is compacted;
                // the public defensive view expands a long propagated
                // predicate into a JSON tree before the artifact boundary.
                query.add("replayContract",
                        contract.toImmutableJsonView());
            }
            query.addProperty("readyForSolver", true);
        } catch (IllegalArgumentException incompleteWitness) {
            query.addProperty("readyForSolver", false);
            query.addProperty("blocker", incompleteWitness.getMessage());
        }
        JsonObject symbolicContext = new JsonObject();
        symbolicContext.addProperty("occurrenceId",
                candidate.queryOccurrenceId);
        query.add("symbolicContext", symbolicContext);
        return SharedExpressionTable.compact(query);
    }

    /** An exact required target event needs no branch flip. */
    private static SummaryBranchMapping directConcreteTarget(
            Candidate candidate, JsonObject summary) {
        SummaryBranchMapping selected = null;
        for (SummaryBranchMapping mapping
                : SummaryBranchMapping.fromSummary(summary)) {
            if (candidate.target.siteId.equals(mapping.siteId())
                    && candidate.target.selectedOccurrence
                    == mapping.occurrence()) {
                selected = mapping;
                break;
            }
        }
        if (selected == null || !selected.isConcreteObservation()
                || selected.sourceTakenOutcome()
                != candidate.target.requiredOutcome) {
            return null;
        }
        if (selected.concreteObservation().isMultiwaySwitch()) {
            throw new IllegalArgumentException(
                    "multiway concrete target requires an exact successor, "
                            + "but target policy states only a Boolean outcome");
        }
        JsonElement encoded = summary.get(
                PathObservation.TargetReachEvent.FIELD);
        if (encoded == null) {
            throw new IllegalArgumentException(
                    "concrete target branch has no target reach event");
        }
        PathObservation.TargetReachEvent event =
                PathObservation.TargetReachEvent.decode(encoded);
        if (!event.matches(selected.siteId(), selected.occurrence(),
                selected.sourceTakenOutcome())) {
            throw new IllegalArgumentException(
                    "concrete target branch and target reach event differ");
        }
        return selected;
    }

    /** The solver query names every input frozen into the effective task. */
    private static JsonObject queryOccurrenceWithInputs(
            JsonObject encoded, JsonArray taskInputActions) {
        JsonObject result = encoded == null
                ? new JsonObject() : encoded.deepCopy();
        Set<String> inputs = new java.util.TreeSet<>();
        for (JsonElement element : array(result, "inputPorts")) {
            if (element.isJsonPrimitive()
                    && !element.getAsString().trim().isEmpty()) {
                inputs.add(element.getAsString());
            }
        }
        for (JsonElement element : taskInputActions == null
                ? new JsonArray() : taskInputActions) {
            if (!element.isJsonObject()) continue;
            String input = firstNonBlank(optionalString(
                    element.getAsJsonObject(), "symbol"),
                    optionalString(element.getAsJsonObject(), "portId"));
            if (!input.isEmpty()) inputs.add(input);
        }
        JsonArray ports = new JsonArray();
        for (String input : inputs) ports.add(input);
        result.add("inputPorts", ports);
        return result;
    }

    /** Stable identity shared by target query publication and aggregation. */
    static String targetBranchQueryKey(String seedTaskId) {
        String task = seedTaskId == null ? "" : seedTaskId.trim();
        if (task.isEmpty()) {
            throw new IllegalArgumentException(
                    "target branch query requires a seed task identity");
        }
        return task + "/target-branch";
    }

    /** Target closure starts from the imported seed path, not from one
     * privileged Jimple branch. */
    private static BranchReplayContract latestTargetSeedDecision(
            Candidate candidate, JsonObject summary) {
        Set<String> sites = new LinkedHashSet<>();
        for (JsonElement element : candidate.branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if ("EXPLORE".equals(optionalString(branch, "policy"))) {
                sites.add(optionalString(branch, "siteId"));
            }
        }
        List<SummaryBranchMapping> mappings =
                SummaryBranchMapping.fromSummary(summary);
        SummaryBranchMapping selected = null;
        for (SummaryBranchMapping mapping : mappings) {
            if (!mapping.isWitnessed() || !mapping.isExplore()
                    || !sites.contains(mapping.siteId())) {
                continue;
            }
            if (selected == null || mapping.summaryPcIndex()
                    > selected.summaryPcIndex()) {
                selected = mapping;
            }
        }
        if (selected == null) {
            throw new IllegalArgumentException(
                    "target seed path has no solver decision");
        }
        return BranchReplayContract.fromSummary(summary, mappings, selected);
    }

    /** Selects target-PC provenance only from the exact runtime region
     * instance and closure goal. */
    private static JsonObject exactTargetSummary(
            Candidate candidate, List<JsonObject> summaries) {
        String expectedInstance = candidate.goal.plan().occurrenceId();
        if (expectedInstance.isEmpty()) return null;
        // OCC-1: one target address publishes one summary per activation,
        // named <address>#a<ordinal>.  The candidate is keyed on the planned
        // address, so the seed is matched on the address and not on any one
        // activation of it.
        //
        // The seed's replay contract is a FLIP base: it names a branch the
        // replay took one way and requires the other way (the failure).  So
        // the seed is a non-failing sibling of the throw -- an activation
        // that did NOT reach the target, whose target branch flips to the
        // required failure outcome.  The throw activation itself is consumed
        // downstream by the reach-query builder as the direct failure
        // witness (directRequiredWitness), which is where the studied
        // exceptional exit actually enters the query; seeding the flip from
        // the throw would require the branch to flip to a polarity the throw
        // already took and the builder rejects it.
        JsonObject flipSeed = null;
        JsonObject anyComplete = null;
        for (JsonObject summary : summaries) {
            if (!candidate.goal.goalId().equals(optionalString(summary, "goalId"))
                    || !candidate.goal.plan().regionId().equals(
                    optionalString(summary, "regionId"))
                    || !expectedInstance.equals(
                    OccurrenceId.parse(
                            optionalString(summary, "occurrenceId")).planned())
                    || !ClosureGoalKind.fromTask(summary)
                    .capturesTargetReach()
                    || optionalString(summary, "summaryId").isEmpty()) {
                continue;
            }
            if (anyComplete == null) anyComplete = summary;
            if (flipSeed == null
                    && !optionalBool(summary, PathObservation.TARGET_REACHED,
                    false)) {
                flipSeed = summary;
            }
        }
        // Prefer the non-failing flip base.  When every activation of the
        // address reached the target -- no sibling to flip from -- fall back
        // to a complete target summary so a query is still published; the
        // reach-query builder is the one authority that refuses a target
        // with no attested flip.
        return flipSeed != null ? flipSeed : anyComplete;
    }

    /** The one option scan of this entry point: {@code --key value} pairs,
     *  a bare {@code --flag} reading "true", and no unknown key. */
    static Map<String, String> parseArgs(String[] args, String... known) {
        Set<String> options = new LinkedHashSet<>(Arrays.asList(known));
        Map<String, String> values = new LinkedHashMap<>();
        for (int index = 0; args != null && index < args.length; index++) {
            String value = args[index];
            if (!value.startsWith("--")) {
                throw new IllegalArgumentException(
                        "Unexpected scheduler argument: " + value);
            }
            String key = value.substring(2);
            if (!options.contains(key)) {
                throw new IllegalArgumentException(
                        "Unknown scheduler option --" + key);
            }
            boolean hasNext = index + 1 < args.length
                    && !args[index + 1].startsWith("--");
            values.put(key, hasNext ? args[++index] : "true");
        }
        return values;
    }

    private static void requireFile(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

    private static void requireRefinedGraph(List<JsonObject> rows) {
        if (rows.isEmpty()) {
            throw new IllegalArgumentException(
                    "runtime-refined graph must not be empty");
        }
        for (JsonObject row : rows) {
            if (optionalInteger(row, "schemaVersion", -1) != 3
                    || optionalInteger(row, "refinementSchemaVersion", -1) != 1
                    || !"RUNTIME_REFINED_DATAFLOW".equals(
                    optionalString(row, "graphKind"))) {
                throw new IllegalArgumentException(
                        "scheduler accepts only the runtime-refined graph");
            }
        }
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    /** Exact Jimple definitions for live-in locals, recovered from the static graph. */
    private static final class DefinitionIndex {
        private final Map<String, List<JsonObject>> byCallReturn =
                new LinkedHashMap<>();
        private final Map<String, List<String>> transferSources =
                new LinkedHashMap<>();
        private final Set<String> transferCells = new LinkedHashSet<>();
        private static DefinitionIndex from(List<JsonObject> edges) {
            DefinitionIndex result = new DefinitionIndex();
            Set<String> seenCallReturns = new LinkedHashSet<>();
            for (JsonObject edge : edges) {
                String source = optionalString(edge, "fromCell");
                if (!"GUARD".equals(optionalString(edge, "transferKind"))) {
                    String target = optionalString(edge, "toCell");
                    if (!source.isEmpty() && !target.isEmpty()) {
                        result.transferSources.computeIfAbsent(target,
                                ignored -> new ArrayList<>()).add(source);
                        result.transferCells.add(source);
                        result.transferCells.add(target);
                    }
                }
                String cell = optionalString(edge, "toCell");
                Matcher localCell = LOCAL_CELL.matcher(cell);
                if (!localCell.matches()) {
                    continue;
                }
                String method = optionalString(edge, "method");
                int unitIndex = optionalInteger(edge, "unitIndex", -1);
                if (!localCell.group(1).equals(method) || unitIndex < 0
                        || !optionalBool(edge, "definitionSite", false)) {
                    continue;
                }
                JsonObject site = new JsonObject();
                site.addProperty("method", method);
                site.addProperty("local", localCell.group(2));
                site.addProperty("unitIndex", unitIndex);
                if (source.contains(">.return")) {
                    String returnKey = source + "\n" + method + "#u"
                            + unitIndex + "\n" + localCell.group(2);
                    if (seenCallReturns.add(returnKey)) {
                        result.byCallReturn.computeIfAbsent(source,
                                ignored -> new ArrayList<>())
                                .add(site.deepCopy());
                    }
                }
            }
            return result;
        }

        private boolean knownCell(String cell) {
            return transferCells.contains(cell);
        }

        /** Cells from which one of the given guard operands is still
         * reachable. */
        private Set<String> guardDependentCells(Collection<String> operands) {
            Set<String> result = new LinkedHashSet<>();
            Deque<String> work = new ArrayDeque<>(operands);
            while (!work.isEmpty()) {
                String cell = work.removeFirst();
                if (!result.add(cell)) continue;
                work.addAll(transferSources.getOrDefault(cell,
                        Collections.<String>emptyList()));
            }
            return result;
        }

        private JsonArray returnSites(String callReturnCell,
                                      Set<String> allowedMethods) {
            return filteredSites(byCallReturn.get(callReturnCell),
                    allowedMethods);
        }

        private JsonArray filteredSites(
                List<JsonObject> sites, Set<String> allowedMethods) {
            JsonArray result = new JsonArray();
            if (sites == null) {
                return result;
            }
            for (JsonObject site : sites) {
                String method = optionalString(site, "method");
                if (!allowedMethods.contains(method)) {
                    continue;
                }
                result.add(site.deepCopy());
            }
            return result;
        }

    }

    private static final class Region {
        private static final int STATIC_REGION_SCHEMA_VERSION = 3;
        private final String regionId;

        private Region(JsonObject row) {
            int schemaVersion = optionalInteger(row, "schemaVersion", -1);
            if (schemaVersion != STATIC_REGION_SCHEMA_VERSION) {
                throw new IllegalArgumentException(
                        "symbolic region requires schemaVersion "
                                + STATIC_REGION_SCHEMA_VERSION);
            }
            this.regionId = optionalString(row, "regionId");
        }

    }

    private static final class TargetBranch {
        private final String siteId;
        private final int selectedOccurrence;
        private final long runtimeEventSeq;
        private final boolean observedOutcome;
        private final boolean requiredOutcome;
        private final boolean desiredOutcome;

        private TargetBranch(String siteId, int selectedOccurrence,
                             long runtimeEventSeq,
                             boolean observedOutcome,
                             boolean requiredOutcome,
                             boolean desiredOutcome) {
            this.siteId = safe(siteId);
            this.selectedOccurrence = Math.max(1, selectedOccurrence);
            this.runtimeEventSeq = runtimeEventSeq;
            this.observedOutcome = observedOutcome;
            this.requiredOutcome = requiredOutcome;
            this.desiredOutcome = desiredOutcome;
        }

        private static TargetBranch regionPath() {
            return new TargetBranch("", 1, -1L,
                    false, false, false);
        }

        private static TargetBranch select(
                String siteId, JsonArray occurrences, boolean required) {
            TargetBranch mismatch = null;
            for (int index = 0; index < occurrences.size(); index++) {
                JsonElement element = occurrences.get(index);
                if (!element.isJsonObject()) continue;
                JsonObject occurrence = element.getAsJsonObject();
                boolean observed = optionalBool(occurrence, "outcome", false);
                int ordinal = optionalInteger(occurrence, "occurrence", index + 1);
                TargetBranch selected = new TargetBranch(siteId, ordinal,
                        optionalLongInteger(occurrence, "eventSeq", -1L),
                        observed, required,
                        observed == required ? !observed : required);
                if (observed == required) return selected;
                if (mismatch == null) mismatch = selected;
            }
            return mismatch;
        }

    }

    private static final class Candidate {
        private static final Comparator<Candidate> ORDER =
                Comparator.comparing((Candidate value) -> !value.directed)
                        .thenComparing(value -> !value.ready)
                        .thenComparing(Comparator.comparingLong(
                                (Candidate value) ->
                                        value.target.runtimeEventSeq)
                                .reversed())
                        .thenComparing(value -> value.target.siteId)
                        .thenComparing(value ->
                                value.goal.plan().occurrenceId())
                        .thenComparing(value -> value.goal.goalId());

        private final Goal goal;
        private final JsonArray branches;
        private final TargetBranch target;
        private final boolean directed;
        private final JsonArray inputActions;
        private final boolean ready;
        private final String queryOccurrenceId;
        private final JsonObject queryOccurrence;
        private final JsonArray targetEdgeBindings;

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions, boolean ready,
                          String queryOccurrenceId,
                          JsonObject queryOccurrence,
                          JsonArray targetEdgeBindings) {
            this.goal = goal;
            this.branches = branches;
            this.target = target;
            this.directed = goal.kind().capturesRegionPath()
                    || !hasRequiredWitness;
            this.inputActions = inputActions;
            this.ready = ready;
            this.queryOccurrenceId = firstNonBlank(
                    queryOccurrenceId,
                    goal.plan().occurrenceId());
            this.queryOccurrence = queryOccurrence == null
                    ? new JsonObject() : queryOccurrence.deepCopy();
            this.targetEdgeBindings = targetEdgeBindings == null
                    ? null : targetEdgeBindings.deepCopy();
        }

        /** Stable task identity: source occurrence x relation content x exact
         * port set (x target predicate for reach goals). */
        private String seedTaskId(JsonArray taskInputActions) {
            StringBuilder identity = new StringBuilder(
                    "TASK.SEED.SEMANTIC.V3");
            identity.append('\n').append(goal.plan().sourceKey());
            identity.append('\n').append(goal.plan().occurrenceId());
            identity.append('\n').append(goal.plan().regionId());
            identity.append('\n').append(goal.kind().name());
            identity.append('\n').append(regionContentHash());
            identity.append('\n').append(portSetHash(taskInputActions));
            identity.append('\n').append(target.siteId)
                    .append('\n').append(target.selectedOccurrence)
                    .append('\n').append(target.observedOutcome)
                    .append('\n').append(target.requiredOutcome)
                    .append('\n').append(target.desiredOutcome);
            return "TASK.SEED." + ArtifactIO.sha256(identity.toString());
        }

        /** Sorted definition methods and explored branch sites. */
        private String regionContentHash() {
            java.util.TreeSet<String> methods = new java.util.TreeSet<>(
                    goal.runtimeDefinitionMethods());
            java.util.TreeSet<String> sites = new java.util.TreeSet<>();
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                String site = optionalString(element.getAsJsonObject(), "siteId");
                if (!site.isEmpty()) sites.add(site);
            }
            return ArtifactIO.sha256(String.join("\n", methods)
                    + "\n--BRANCH-SITES--\n" + String.join("\n", sites));
        }

        /** Canonical ordinal-free descriptors for the local symbolic roots. */
        private String portSetHash(JsonArray taskInputActions) {
            java.util.TreeSet<String> descriptors = new java.util.TreeSet<>();
            for (JsonElement element : taskInputActions) {
                if (!element.isJsonObject()) continue;
                descriptors.add("IN\n" + semanticPortDescriptor(
                        element.getAsJsonObject()));
            }
            return ArtifactIO.sha256(String.join(
                    "\n==PORT==\n", descriptors));
        }

        /** Static, replay-stable fields of one port/capture row. */
        private static final String[] SEMANTIC_PORT_FIELDS = {
                "accessFieldSignature", "accessSites", "argumentIndex",
                "cell",
                "containerCapacity", "declaredCallee", "definitionMethod",
                "definitionUnitIndex", "dependencyRole", "fieldPath",
                "fieldPathDeclarations", "fieldPaths", "fieldSignature",
                "helperActivationBoundedOccurrence", "javaType",
                "location", "protocolDirection",
                "replayOccurrence", "rootKind", "rootMethod", "siteId",
                "sourceKind", "symbolicDemand"};

        private static String semanticPortDescriptor(JsonObject row) {
            JsonObject filtered = new JsonObject();
            for (String field : SEMANTIC_PORT_FIELDS) {
                JsonElement value = row.get(field);
                if (value != null && !value.isJsonNull()) {
                    filtered.add(field, value);
                }
            }
            return CanonicalJson.render(filtered);
        }
    }

    /** Describes the existing selection/admission decision without adding one.
     */
    static String noCandidateDiagnostic(
            Arguments arguments, List<RegionInstancePlan> rows) {
        RegionInstancePlan selected = null;
        Goal selectedGoal = null;
        boolean regionFound = false;
        for (RegionInstancePlan plan : rows) {
            if (!arguments.regionId.isEmpty()
                    && !arguments.regionId.equals(plan.regionId())) continue;
            regionFound = true;
            if (!arguments.occurrenceId.isEmpty()
                    && !plan.occurrenceId().equals(
                    arguments.occurrenceId.trim())) continue;
            if (selected == null) {
                // Remembered only so an unmatched goal still reports which
                // fragments were searched.
                selected = plan;
            }
            Goal found = null;
            for (Goal goal : plan.goals()) {
                if (!arguments.goalId.isEmpty()
                        && !arguments.goalId.equals(goal.goalId())) continue;
                found = goal;
                break;
            }
            if (found == null) continue;
            selected = plan;
            selectedGoal = found;
            break;
        }
        String reason;
        if (!regionFound) {
            reason = "REGION_NOT_FOUND";
        } else if (selected == null) {
            reason = "REGION_INSTANCE_NOT_FOUND";
        } else if (selectedGoal == null) {
            reason = "GOAL_NOT_FOUND";
        } else {
            reason = !selectedGoal.replayable() ? "GOAL_NOT_REPLAYABLE"
                    : "NO_ELIGIBLE_CANDIDATE";
        }
        String targetMethod = selected == null ? ""
                : optionalString(selected.json(), "targetMethod");
        JsonObject root = selected == null ? new JsonObject()
                : object(selected.json(), "rootSelector");
        String state = selectedGoal == null ? ""
                : selectedGoal.admissionState();
        String blockers = selectedGoal == null ? ""
                : selectedGoal.admissionBlockers().toString();
        return "component=SCHEDULER reason=" + reason
                + " region=" + display(arguments.regionId)
                + " instance=" + display(arguments.occurrenceId)
                + " goal=" + display(arguments.goalId)
                + " targetMethod=" + display(targetMethod)
                + " root=" + display(root.size() == 0 ? ""
                : CanonicalJson.render(root))
                + " admissionState=" + display(state)
                + " blockers=" + display(blockers)
                + " artifacts={runtimePlan=" + artifact(arguments.regionPlan)
                + ",refinedGraph=" + artifact(arguments.refinedGraph)
                + ",summaries=" + artifact(arguments.summaries) + "}";
    }

    private static String display(String value) {
        return safe(value).isEmpty() ? "<none>" : value;
    }

    private static String artifact(Path path) {
        return path == null ? "<none>"
                : path.toAbsolutePath().normalize().toString();
    }

    public static final class Result {
        public final List<ExecutionTask> executionTasks = new ArrayList<>();
        public final List<JsonObject> queries = new ArrayList<>();
    }

    /**
     * Optional experiment-owned allowlist of symbolic roots.
     *
     * <p>Wave 3: the only surviving job is turning declared FIELD signatures
     * into SYMBOLIC materialization actions and everything else CONCRETE.
     * Which symbol reaches which read is decided at replay -- the VM's
     * propagated expression is the authority -- so no selector, selected
     * phase, producer version or output-version boundary is predicted here.
     * </p>
     */
    static final class SymbolicInputSelection {
        private final boolean configured;
        /** regionId -> the field signatures, port ids and cells it admits. */
        private final Map<String, Set<String>> admitted;
        /** regionId -> sourceId -> the one field that hook site mints. */
        private final Map<String, Map<String, String>> minted;

        private SymbolicInputSelection(
                boolean configured, Map<String, Set<String>> admitted,
                Map<String, Map<String, String>> minted) {
            this.configured = configured;
            this.admitted = admitted;
            this.minted = minted;
        }

        /** One pass over the static hook declarations and, when the campaign
         *  configured one, over the declared field/port/cell rows. */
        static SymbolicInputSelection read(
                Path path, List<JsonObject> regionCatalog)
                throws IOException {
            Map<String, Map<String, String>> minted = new LinkedHashMap<>();
            Set<String> catalogRegions = new LinkedHashSet<>();
            for (JsonObject region : regionCatalog == null
                    ? Collections.<JsonObject>emptyList() : regionCatalog) {
                String regionId = optionalString(region, "regionId");
                if (!regionId.isEmpty()) catalogRegions.add(regionId);
                for (JsonElement element : array(region,
                        StaticSymbolicSourceDeclaration.FIELD)) {
                    if (!element.isJsonObject() || regionId.isEmpty()) {
                        throw new IOException("static symbolic source has no "
                                + "declaring region");
                    }
                    declareMintSite(minted.computeIfAbsent(regionId,
                            ignored -> new LinkedHashMap<>()),
                            element.getAsJsonObject());
                }
            }
            Map<String, Set<String>> admitted = new LinkedHashMap<>();
            if (path == null) {
                return new SymbolicInputSelection(!minted.isEmpty(),
                        admitted, minted);
            }
            requireFile(path, "symbolic input selection");
            for (JsonObject row : ArtifactIO.readJsonl(path)) {
                String regionId = firstNonBlank(optionalString(row, "regionId"));
                if (regionId.isEmpty()) {
                    throw new IOException("symbolic input selection row has "
                            + "no regionId: " + row);
                }
                if (!catalogRegions.contains(regionId)) {
                    throw new IOException("symbolic input selection names "
                            + "an unknown static region: " + regionId);
                }
                Set<String> names = admitted.computeIfAbsent(regionId,
                        ignored -> new LinkedHashSet<>());
                for (String field : new String[]{
                        "fieldSignatures", "portIds", "cells"}) {
                    addDeclaredNames(names, row, field);
                }
            }
            return new SymbolicInputSelection(true, admitted, minted);
        }

        /** An explicit source hook is itself the allowlist authority. */
        private static void declareMintSite(
                Map<String, String> sites, JsonObject row) throws IOException {
            String sourceId = firstNonBlank(optionalString(row, "sourceId"));
            String field = firstNonBlank(optionalString(row, "fieldSignature"));
            if (JsonFields.exactInteger(row, "schemaVersion", -1)
                    != StaticSymbolicSourceDeclaration.SCHEMA_VERSION
                    || !StaticSymbolicSourceDeclaration.KIND.equals(
                    optionalString(row, "kind"))
                    || !StaticSymbolicSourceDeclaration.AUTHORITY.equals(
                    optionalString(row, "authority"))
                    || sourceId.isEmpty() || field.isEmpty()) {
                throw new IOException("malformed static symbolic source "
                        + "declaration");
            }
            if (optionalString(row, "declarationMethod").isEmpty()
                    || JsonFields.exactInteger(row,
                    "declarationUnitIndex", -1) < 0) {
                throw new IOException("malformed static symbolic source "
                        + "declaration location");
            }
            String prior = sites.putIfAbsent(sourceId, field);
            if (prior != null && !prior.equals(field)) {
                throw new IOException("static symbolic source declaration "
                        + "gives one sourceId two fields: " + sourceId);
            }
        }

        private static void addDeclaredNames(
                Set<String> output, JsonObject row, String field)
                throws IOException {
            JsonElement encoded = row.get(field);
            if (encoded == null) return;
            if (!encoded.isJsonArray()) {
                throw new IOException("symbolic input selection " + field
                        + " must be an array");
            }
            for (JsonElement element : encoded.getAsJsonArray()) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isString()
                        || firstNonBlank(element.getAsString()).isEmpty()) {
                    throw new IOException("symbolic input selection " + field
                            + " entries must be non-empty strings");
                }
                output.add(firstNonBlank(element.getAsString()));
            }
        }

        JsonArray select(String regionId, JsonArray actions) {
            if (!configured) return actions.deepCopy();
            JsonArray selected = new JsonArray();
            for (JsonElement element : actions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                JsonObject retained = action.deepCopy();
                // Every input remains declared because concrete topology may
                // use it as an instrumentation anchor.
                if ("SYMBOLIC".equals(optionalString(action, "mode"))) {
                    if (minted(regionId, action)) {
                        // The Java hook mints this exact root once.
                        retained.addProperty("mode", "CONCRETE");
                        retained.addProperty("symbolicDemand",
                                "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED");
                    } else if (!admits(regionId, action)) {
                        retained.addProperty("mode", "CONCRETE");
                        retained.addProperty("symbolicDemand",
                                "CONFIGURED_SYMBOLIC_INPUT_UNSELECTED");
                    }
                }
                selected.add(retained);
            }
            return selected;
        }

        /** Whether a declaring hook site of this region mints the action's
         *  field: one field is one root, and the hook owns it. */
        private boolean minted(String regionId, JsonObject action) {
            String field = actionField(action);
            return !field.isEmpty() && minted.getOrDefault(safe(regionId),
                    Collections.<String, String>emptyMap())
                    .containsValue(field);
        }

        private boolean admits(String regionId, JsonObject action) {
            Set<String> names = admitted.get(safe(regionId));
            return names != null
                    && (names.contains(actionField(action))
                    || names.contains(actionPort(action))
                    || names.contains(optionalString(action, "cell")));
        }

        private static String actionField(JsonObject action) {
            return firstNonBlank(optionalString(action, "accessFieldSignature"),
                    optionalString(action, "declaredFieldSignature"));
        }

        private static String actionPort(JsonObject action) {
            return firstNonBlank(optionalString(action, "portId"),
                    optionalString(action, "symbol"));
        }
    }

    private static final class LoadedInputs {
        private final List<RegionInstancePlan> regionPlans;
        private final List<JsonObject> summaries;
        private final Map<String, Region> regionIndex;
        private final DefinitionIndex definitions;
        private final JsonObject regionPlanIdentity;
        private final JsonObject refinedGraphIdentity;
        private final JsonObject symbolicInputsIdentity;
        private final SymbolicInputSelection symbolicInputs;

        private LoadedInputs(List<RegionInstancePlan> regionPlans,
                             List<JsonObject> summaries,
                             Map<String, Region> regionIndex,
                             DefinitionIndex definitions,
                             JsonObject regionPlanIdentity,
                             JsonObject refinedGraphIdentity,
                             JsonObject symbolicInputsIdentity,
                             SymbolicInputSelection symbolicInputs) {
            this.regionPlans = regionPlans;
            this.summaries = summaries;
            this.regionIndex = regionIndex;
            this.definitions = definitions;
            this.regionPlanIdentity = regionPlanIdentity;
            this.refinedGraphIdentity = refinedGraphIdentity;
            this.symbolicInputsIdentity = symbolicInputsIdentity;
            this.symbolicInputs = symbolicInputs;
        }
    }

    /**
     * Which closure the schedule is drawn from.  Exactly one of the three
     * answers the question "which region occurrences are in scope", so the
     * caller states it once rather than leaving two independent flags to
     * contradict each other.
     */
    public enum ClosureMode {
        /** Every candidate occurrence the frozen region plan declares. */
        CANDIDATE("candidate"),
        /** Only the occurrences a seed activation can replay. */
        SEED_REPLAY("seed-replay"),
        /** Only the occurrences this iteration's summaries observed. */
        ACTIVE_OBSERVED("active-observed");

        private final String option;

        ClosureMode(String option) {
            this.option = option;
        }

        static ClosureMode parse(String value) {
            String requested = value == null || value.trim().isEmpty()
                    ? CANDIDATE.option : value.trim();
            for (ClosureMode mode : values()) {
                if (mode.option.equals(requested)) return mode;
            }
            throw new IllegalArgumentException("--closure-mode must be one "
                    + "of candidate|seed-replay|active-observed, not: "
                    + requested);
        }
    }

    public static final class Arguments {
        public final Path regionPlan;
        public final Path refinedGraph;
        public final Path summaries;
        public final Path outputDirectory;
        public final String regionId;
        public final String occurrenceId;
        public final String goalId;
        public final int maxJobs;
        public final int maxLoopIterations;
        public final Path symbolicInputs;
        private final ClosureMode closureMode;

        private Arguments(Path regionPlan, Path refinedGraph, Path summaries,
                          Path outputDirectory, String regionId,
                          String occurrenceId, String goalId,
                          int maxJobs, int maxLoopIterations,
                          Path symbolicInputs, ClosureMode closureMode) {
            this.regionPlan = regionPlan;
            this.refinedGraph = refinedGraph;
            this.summaries = summaries;
            this.outputDirectory = outputDirectory;
            this.regionId = safe(regionId);
            this.occurrenceId = safe(occurrenceId);
            this.goalId = safe(goalId);
            this.maxJobs = Math.max(1, maxJobs);
            this.maxLoopIterations = maxLoopIterations;
            this.symbolicInputs = symbolicInputs;
            this.closureMode = closureMode;
        }

        public static Arguments parse(String[] args) {
            Map<String, String> values = parseArgs(args, "region-plan",
                    "refined-graph", "summaries", "output-dir", "max-jobs",
                    "symbolic-inputs", "max-loop-iterations",
                    "closure-mode");
            Path regionPlan = requiredPath(values, "region-plan");
            Path output = Paths.get(firstNonBlank(values.get("output-dir"),
                    ArtifactIO.sibling(regionPlan,
                            "concolic-schedule").toString()));
            Path refinedGraph = requiredPath(values, "refined-graph");
            Path summaries = optionalPath(values.get("summaries"));
            Path symbolicInputs = optionalPath(
                    values.get("symbolic-inputs"));
            ClosureMode closureMode = ClosureMode.parse(
                    values.get("closure-mode"));
            return new Arguments(regionPlan, refinedGraph,
                    summaries, output, "", "", "",
                    parseInt(values.get("max-jobs"), 1),
                    positiveInt(values.get("max-loop-iterations"),
                            LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                            "max-loop-iterations"),
                    symbolicInputs, closureMode);
        }

        private static Path requiredPath(Map<String, String> values,
                                         String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }

        private static Path optionalPath(String value) {
            return value == null || value.trim().isEmpty()
                    ? null : Paths.get(value);
        }

        private static int parseInt(String value, int fallback) {
            try {
                return value == null ? fallback : Integer.parseInt(value);
            } catch (RuntimeException ignored) {
                return fallback;
            }
        }

        private static int positiveInt(String value, int fallback,
                                       String option) {
            int parsed;
            try {
                parsed = value == null ? fallback : Integer.parseInt(value);
            } catch (RuntimeException malformed) {
                throw new IllegalArgumentException("--" + option
                        + " requires a positive integer", malformed);
            }
            if (parsed < 1) {
                throw new IllegalArgumentException("--" + option
                        + " requires a positive integer");
            }
            return parsed;
        }

        private Arguments forSelection(
                RuntimeWorkflowDiscovery.Selection selection) {
            return new Arguments(regionPlan, refinedGraph,
                    summaries, outputDirectory,
                    selection.regionId, selection.occurrenceId,
                    selection.goalId, 1, maxLoopIterations,
                    symbolicInputs, closureMode);
        }

    }
}
