package edu.uva.liftlab.graphchecker.d3.plan;

import edu.uva.liftlab.graphchecker.d3.plan.BranchReplayContract;
import edu.uva.liftlab.graphchecker.d3.plan.SharedExpressionTable;
import edu.uva.liftlab.graphchecker.d3.plan.SummaryBranchMapping;

import edu.uva.liftlab.graphchecker.d3.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.d3.smt.CanonicalJson;

import edu.uva.liftlab.graphchecker.d3.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.d3.smt.JsonFields;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.d3.plan.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.d3.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.d3.plan.DependencyRole;
import edu.uva.liftlab.graphchecker.d3.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.d3.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.d3.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.d3.smt.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.d3.smt.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.d3.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.d3.plan.PathObservation;
import edu.uva.liftlab.graphchecker.d3.plan.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.d3.plan.RegionInstancePlan.Goal;
import edu.uva.liftlab.graphchecker.d3.plan.RuntimePlanArtifact;
import edu.uva.liftlab.graphchecker.d3.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.d3.plan.SiteId;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.AbstractMap;
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
import java.util.function.Predicate;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/** Builds graph-directed concolic jobs from static regions and concrete
 * runtime-selected region instance plans. */
public final class ConcolicScheduler {
    /**
     * The member a branch query publishes a concretely observed target under.
     *
     * <p>The anchor took its arm without a symbolic decision, so the path set
     * states the arm rather than a predicate over it.</p>
     */
    static final String TARGET_CONCRETE_OBSERVATION =
            "targetConcreteObservation";
    /** Telemetry artifact naming what the selection file refused. */
    static final String ROOT_POLICY_ARTIFACT = "symbolic_root_policy.jsonl";
    /** Row kind of {@link #ROOT_POLICY_ARTIFACT}. */
    static final String SYMBOLIC_ROOT_POLICY = "SYMBOLIC_ROOT_POLICY";
    /** A manual root still declared by a planner-minted region hash. */
    static final String REGION_ID_DECLARATION =
            "SYMBOLIC_INPUT_REGION_ID_DECLARATION";
    /** Row kind of one refused automatic root candidate. */
    static final String SUPPRESSED_ROOT_CANDIDATE =
            "SUPPRESSED_ROOT_CANDIDATE";
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
                        regions, regionPlans);
        Map<String, Region> regionIndex = regionIndex(regions);
        // The identities recorded here are verified once, against the same
        // files, at the point the schedule index commits them.
        return new LoadedInputs(regionPlans, summaries, regionIndex,
                definitions, refinedGraph, regionPlanIdentity,
                refinedGraphIdentity, symbolicInputsIdentity,
                symbolicInputs);
    }

    private static Result scheduleLoaded(
            Arguments arguments, LoadedInputs loaded)
            throws IOException {
        // One slice for the whole schedule: which locations this campaign's
        // manual roots can still reach.  Seeded from the raw proposals, so
        // it is already answerable when materializationPlan asks whether a
        // structure carrier is on the root's forward slice -- and every
        // region afterwards narrows against the same answer.
        loaded.symbolicInputs.seedCarrierSlice(loaded.refinedGraph,
                rawProposals(loaded.regionPlans));
        List<Candidate> candidates = candidates(arguments,
                loaded.regionPlans, loaded.regionIndex,
                loaded.definitions, loaded.symbolicInputs.carrierSlice());
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
                    candidate.branches, edgeBindings, loopBound);
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
        String receiver = occurrenceId;
        Set<String> suppliedPorts = new LinkedHashSet<>();
        for (JsonElement element : edgeBindings == null
                ? new JsonArray() : edgeBindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!AutomaticRegionEdge.tracedExchangeCandidate(binding)
                    || !receiver.equals(optionalString(binding, "toOccurrenceId"))) {
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
                        loaded.regionPlans, loaded.summaries,
                        arguments.targetOccurrence)
                : arguments.closureMode == ClosureMode.SEED_REPLAY
                ? RuntimeWorkflowDiscovery.seedReplayWorkflow(
                        loaded.regionPlans, arguments.targetOccurrence)
                : RuntimeWorkflowDiscovery.candidateWorkflow(
                        loaded.regionPlans, arguments.targetOccurrence);
        // The root-dependence slice scopes instrumentation and flips; it
        // does not decide which occurrences are scheduled.  A replay task
        // set is the anchor's closure, and an occurrence outside it runs
        // concretely rather than being pruned from the plan.
        loaded.symbolicInputs.seedCarrierSlice(loaded.refinedGraph,
                rawProposals(loaded.regionPlans));
        if (workflow.scheduledTaskCount() > arguments.maxJobs) {
            // A bare count says only that the campaign is too big; what a
            // reader needs is which admission rule bought the rows, so the
            // next step is either raising --max-jobs or tightening that rule.
            throw new IOException("selected exact closure exceeds max jobs: "
                    + workflow.scheduledTaskCount() + " > "
                    + arguments.maxJobs + "; "
                    + closureAdmissionSummary(loaded.regionPlans));
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
        if (arguments.closureMode == ClosureMode.SEED_REPLAY) {
            taskRows = withSeedReplayGroup(taskRows);
        }
        ArtifactIO.replaceJsonl(taskPlan, taskRows);
        ArtifactIO.replaceJsonl(arguments.outputDirectory.resolve(
                "branch_queries.jsonl"), result.queries);
        // A root the selection file refused is invisible downstream: the
        // task simply carries a CONCRETE action.  Publishing the refusals
        // makes "why is there no clock root" answerable from one file.
        ArtifactIO.replaceJsonl(arguments.outputDirectory.resolve(
                        ROOT_POLICY_ARTIFACT),
                rootPolicyRows(arguments.symbolicInputs,
                        loaded.symbolicInputs));
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

    /**
     * Names the propagation ledger of the seed replay.
     *
     * <p>Every task replayed in one workload JVM shares one ledger, and the
     * ledger's identity is what a reader joins two runs on.  A flip replay
     * already carries that identity from {@link PathReplayTaskFactory}; the
     * seed replay comes from no earlier bundle, so nothing has named its
     * ledger yet.  It is minted here, in the same spelling and from the same
     * authority, so one side -- this scheduler and that factory -- names
     * every replay group and no caller has to derive one.</p>
     *
     * <p>The seed is the plan itself, which makes the identity stable across
     * iterations and campaign roots: the same tasks replayed again are the
     * same ledger.</p>
     */
    private static List<JsonObject> withSeedReplayGroup(
            List<JsonObject> taskRows) {
        StringBuilder seed = new StringBuilder();
        for (JsonObject row : taskRows) {
            seed.append(CanonicalJson.render(row)).append('\n');
        }
        String groupId = "REPLAY.GROUP."
                + ArtifactIO.sha256(seed.toString());
        List<JsonObject> named = new ArrayList<>(taskRows.size());
        for (JsonObject row : taskRows) {
            JsonObject stamped = row.deepCopy();
            stamped.addProperty("replayGroupId", groupId);
            named.add(stamped);
        }
        return named;
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

    /**
     * The object rows of {@code source} that {@code keep} admits, each as
     * its own copy.  A non-object element is not a row and is dropped.
     */
    private static JsonArray copyMatching(JsonArray source,
                                          Predicate<JsonObject> keep) {
        JsonArray result = new JsonArray();
        for (JsonElement element : source == null ? new JsonArray() : source) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (keep.test(row)) result.add(row.deepCopy());
        }
        return result;
    }

    /** One causal edge can be represented by a refined runtime row and by a
     * compact closure row. */
    private static JsonArray objectRows(JsonArray source) {
        return copyMatching(source, row -> true);
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

    /** Every action the region plan proposes, before materialization
     *  narrows any of them, keyed by the region that proposes it. */
    private static List<Map.Entry<String, JsonArray>> rawProposals(
            List<RegionInstancePlan> regionPlans) {
        List<Map.Entry<String, JsonArray>> proposals = new ArrayList<>();
        for (RegionInstancePlan plan : regionPlans) {
            for (Goal goal : plan.goals()) {
                proposals.add(new AbstractMap.SimpleImmutableEntry<>(
                        plan.regionId(), goal.symbolize()));
            }
        }
        return proposals;
    }

    private static List<Candidate> candidates(Arguments arguments,
                                              List<RegionInstancePlan>
                                                      regionPlans,
                                              Map<String, Region> regions,
                                              DefinitionIndex definitions,
                                              RootDependenceSlice slice)
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
                        definitions, slice);
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
            DefinitionIndex definitions, RootDependenceSlice slice)
            throws IOException {
            Set<String> definitionMethods =
                    goal.runtimeDefinitionMethods();
            if (goal.kind().capturesRegionPath()) {
                JsonArray branches = goal.branches();
                JsonArray inputActions = materializationPlan(
                        goal, goal.symbolize(), definitions, definitionMethods,
                        branches, slice);
                result.add(new Candidate(goal, branches,
                        TargetBranch.regionPath(), true,
                        inputActions,
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
                    branches, slice);
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
                        definitionMethods, reachSlice, slice);
                inputActions = targetSymbolicFrontier(inputActions);
                inputActions = mergeSymbolicFrontier(inputActions,
                        targetSourceFrontier);
                JsonArray targetBindings = targetInputBindings(goal,
                        queryInstance);
                result.add(new Candidate(goal,
                        reachSlice, target,
                        hasWitness, inputActions,
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
        return copyMatching(actions,
                action -> InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        optionalString(action, "mode")));
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
        return copyMatching(goal.edgeBindings(),
                binding -> queryInstance.equals(optionalString(binding,
                        "toOccurrenceId"))
                        && AutomaticRegionEdge.tracedExchangeCandidate(
                        binding));
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

    /** Package-visible for the structure-carrier admission contract. */
    static JsonArray materializationPlan(
            Goal goal, JsonArray sourceActions,
            DefinitionIndex definitions,
            Set<String> regionMethods,
            JsonArray demandedBranches,
            RootDependenceSlice slice) {
        JsonArray result = new JsonArray();
        Set<String> represented = new LinkedHashSet<>();
        // The frame the root-entry hooks are injected into.
        String planRootMethod = optionalString(object(goal.plan().json(),
                "rootSelector"), "method");
        Set<String> guardDependent = definitions.guardDependentCells(
                exploredGuardOperands(demandedBranches));
        Set<String> declaredCarriers = declaredCarrierLocations(goal);
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
            // A CONCRETE_STRUCTURE_CARRIER role says "this port names a
            // structural owner, not a value the solver moves".  That is the
            // right default and the wrong answer inside the root slice: the
            // reference itself is then shared state whose writers a root
            // decides, and the read arms over which of them wrote it.  In
            // HDFS-17899 bug3 the wire key id is currentKey.keyId read at
            // BlockTokenSecretManager:538 on the source DataNode, and
            // currentKey's writers (updateKeys / setKeys) are root-dependent,
            // so refusing the role outright loses that guarded read.  Outside
            // the slice the role still decides, because a structural owner no
            // root reaches is a constant for this failure.
            boolean rootDependentStructureCarrier =
                    !DependencyRole.VALUE_FRONTIER.equals(dependencyRole)
                            && slice != null && slice.usable()
                            && slice.carries(action);
            if (concreteOnlyInput(binding)
                    || (!DependencyRole.VALUE_FRONTIER.equals(dependencyRole)
                    && !rootDependentStructureCarrier)) {
                addConcreteInputAction(result, represented, binding,
                        concreteOnlyInputReason(action, dependencyRole));
                continue;
            }
            if (rootDependentStructureCarrier) {
                binding.addProperty("rootDependentStructureCarrier", true);
            }
            boolean boundedContainerState =
                    supportedBoundedContainerState(binding, location);
            // A reference-typed location on the root-dependence slice is
            // shared state too: its writers install object identities a root
            // decides between, and a read through it must arm over those
            // identities instead of stopping at the scalar leaf contract.
            boolean referenceCarrier = !boundedContainerState
                    && slice != null && slice.usable()
                    && slice.carries(action)
                    && supportedReferenceCarrier(binding, location)
                    && declaredReferenceCarrier(declaredCarriers, slice,
                    action, cell);
            if (referenceCarrier) {
                binding.addProperty("symbolicDemand",
                        REFERENCE_CARRIER_DEMAND);
            }
            String unsupportedLeaf = boundedContainerState ? ""
                    : referenceCarrier
                    ? unsupportedFieldLeafPathReason(action, location, cell)
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
        return unsupportedFieldLeafPathReason(action, location, cell);
    }

    /**
     * The exact-field-path half of the leaf contract: a field port must name
     * one declared leaf whose name and type agree with the access.  Stated
     * separately so a reference carrier, which is exempt from the scalar
     * type gate, still has to satisfy it.
     */
    static String unsupportedFieldLeafPathReason(
            JsonObject action, String location, String cell) {
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                optionalString(action, "javaType"));
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

    /** The {@code owner#field} keys one goal declares as shared carriers. */
    private static Set<String> declaredCarrierLocations(Goal goal) {
        Set<String> locations = new LinkedHashSet<>();
        for (JsonElement element : goal.sharedCarriers()) {
            if (!element.isJsonObject()) continue;
            JsonObject carrier = element.getAsJsonObject();
            String location = SharedFieldFlow.fieldKey(
                    optionalString(carrier, "declaringClass"),
                    optionalString(carrier, "fieldName"));
            if (!location.isEmpty()) locations.add(location);
        }
        return locations;
    }

    /**
     * Whether the replay will actually track this reference.
     *
     * <p>A reference port is tracked and never minted, which makes the
     * carrier declaration the whole of its materialization: with no
     * declaration the replay has nothing to select, the getfield resolves no
     * writer, and the port would reach the runtime as a SYMBOLIC input it
     * cannot serve.  The plan therefore admits the demand only where the
     * planner declared the location and root dependence reaches it.  A
     * plan frozen before references were declared keeps its old concrete
     * answer rather than gaining a port with no carrier behind it.</p>
     */
    private static boolean declaredReferenceCarrier(
            Set<String> declaredCarriers, RootDependenceSlice slice,
            JsonObject action, String cell) {
        FieldPathSpec.DeclaredField leaf = declaredLeaf(action, cell);
        if (leaf == null) return false;
        String location = SharedFieldFlow.fieldKey(leaf.owner(), leaf.name());
        return !location.isEmpty() && declaredCarriers.contains(location)
                && slice.reachesLocation(location, null);
    }

    /**
     * The demand a reference-typed shared location carries when its object
     * identity is the value the solver arms over.  The VM versions the field
     * as identities (INITIAL: the referent at selection; REF_WRITE: the
     * installed object), and a read through it resolves a dependent field of
     * the selected object rather than of the recorded one.
     */
    public static final String REFERENCE_CARRIER_DEMAND = "REFERENCE_CARRIER";

    /**
     * Admits a plain object reference as an identity carrier.  The type
     * contract is {@link JavaPrimitiveSmtSemantics#referenceIdentityCarrier},
     * which is also what declares the location a shared carrier one stage
     * earlier, so plan and runtime cannot disagree about which references
     * are versioned.  Only a heap field access qualifies here: the runtime
     * selects such a carrier at the exact getfield without minting, whereas
     * receiver-entry and argument bindings would symbolize the object.
     */
    static boolean supportedReferenceCarrier(JsonObject action,
                                             String location) {
        return "HEAP_OBJECT_FIELD".equals(location)
                && JavaPrimitiveSmtSemantics.referenceIdentityCarrier(
                optionalString(action, "javaType"));
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
                query.add(TARGET_CONCRETE_OBSERVATION,
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
                    optionalString(summary, "occurrenceId"))
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
    static final class DefinitionIndex {
        private final Map<String, List<JsonObject>> byCallReturn =
                new LinkedHashMap<>();
        private final Map<String, List<String>> transferSources =
                new LinkedHashMap<>();
        private final Set<String> transferCells = new LinkedHashSet<>();
        static DefinitionIndex from(List<JsonObject> edges) {
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
                    String returnKey = source + "\n"
                            + SiteId.of(method, unitIndex)
                            + "\n" + localCell.group(2);
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
            JsonArray source = new JsonArray();
            for (JsonObject site : sites == null
                    ? Collections.<JsonObject>emptyList() : sites) {
                source.add(site);
            }
            return copyMatching(source, site -> allowedMethods.contains(
                    optionalString(site, "method")));
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
        private final String queryOccurrenceId;
        private final JsonObject queryOccurrence;
        private final JsonArray targetEdgeBindings;

        private Candidate(Goal goal, JsonArray branches,
                          TargetBranch target,
                          boolean hasRequiredWitness,
                          JsonArray inputActions,
                          String queryOccurrenceId,
                          JsonObject queryOccurrence,
                          JsonArray targetEdgeBindings) {
            this.goal = goal;
            this.branches = branches;
            this.target = target;
            this.directed = goal.kind().capturesRegionPath()
                    || !hasRequiredWitness;
            this.inputActions = inputActions;
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

    /**
     * How the plan rows of an over-sized closure were admitted.  Counted by
     * admission basis, then by demand depth, then by the region anchors that
     * contributed most, so the cap failure names its own top contributors
     * instead of sending a reader back to the plan artifact.
     */
    static String closureAdmissionSummary(List<RegionInstancePlan> rows) {
        Map<String, Integer> byBasis = new TreeMap<>();
        Map<String, Integer> byDepth = new TreeMap<>();
        Map<String, Integer> byAnchor = new LinkedHashMap<>();
        for (RegionInstancePlan plan : rows) {
            String basis = optionalString(plan.json(), "admissionBasis");
            byBasis.merge(basis.isEmpty()
                    ? "TARGET_REACHABLE" : basis, 1, Integer::sum);
            int depth = optionalInteger(plan.json(), "demandDepth", -1);
            byDepth.merge(depth < 0 ? "-" : String.valueOf(depth),
                    1, Integer::sum);
            String anchor = optionalString(plan.json(), "targetMethod");
            if (!anchor.isEmpty()) {
                byAnchor.merge(anchor, 1, Integer::sum);
            }
        }
        StringBuilder summary = new StringBuilder();
        summary.append("admissionBasis=").append(byBasis)
                .append(" demandDepth=").append(byDepth)
                .append(" topAnchors=[");
        List<Map.Entry<String, Integer>> anchors =
                new ArrayList<>(byAnchor.entrySet());
        anchors.sort(Comparator.<Map.Entry<String, Integer>>comparingInt(
                Map.Entry::getValue).reversed()
                .thenComparing(Map.Entry::getKey));
        for (int index = 0; index < anchors.size() && index < 5; index++) {
            if (index > 0) summary.append(", ");
            summary.append(anchors.get(index).getValue()).append("x ")
                    .append(anchors.get(index).getKey());
        }
        return summary.append(']').toString();
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

    /** One row: which file decided the root set and what it refused. */
    static JsonObject rootPolicyTelemetry(
            Path declarations, SymbolicInputSelection selection) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", SYMBOLIC_ROOT_POLICY);
        row.addProperty("declarations",
                declarations == null ? "" : declarations.toString());
        JsonArray suppressed = selection.suppressedRootCandidates();
        row.addProperty("suppressedRootCandidateCount", suppressed.size());
        row.add("suppressedRootCandidates", suppressed);
        JsonArray decisions = selection.rootDecisions();
        int tracked = 0;
        int mintEligible = 0;
        int declared = 0;
        for (JsonElement element : decisions) {
            JsonObject decision = element.getAsJsonObject();
            if (optionalBool(decision,
                    SymbolicInputSelection.TRACKED, false)) tracked++;
            if (optionalBool(decision,
                    SymbolicInputSelection.MINT_ELIGIBLE, false)) {
                mintEligible++;
            }
            if (optionalBool(decision, "declared", false)) declared++;
        }
        row.addProperty("decidedActionCount", decisions.size());
        row.addProperty("trackedActionCount", tracked);
        row.addProperty("mintEligibleActionCount", mintEligible);
        row.addProperty("declaredActionCount", declared);
        RootDependenceSlice slice = selection.carrierSlice();
        row.addProperty("carrierSliceApplied", slice.usable());
        row.addProperty("carrierSliceReason", slice.usable()
                ? "ROOT_DEPENDENT_CARRIERS" : "NO_ROOT_CELL_IN_REFINED_GRAPH");
        row.addProperty("rootCellCount", slice.rootCellCount());
        row.addProperty("rootDependentCellCount", slice.reachableCellCount());
        JsonArray carriers = selection.carrierLocations();
        row.addProperty("carrierLocationCount", carriers.size());
        row.add("carrierLocations", carriers);
        return row;
    }

    /** The policy artifact: one summary row, then one verdict per action. */
    static List<JsonObject> rootPolicyRows(
            Path declarations, SymbolicInputSelection selection) {
        List<JsonObject> rows = new ArrayList<>();
        rows.add(rootPolicyTelemetry(declarations, selection));
        rows.addAll(selection.declarationDiagnostics());
        for (JsonElement element : selection.rootDecisions()) {
            rows.add(element.getAsJsonObject());
        }
        return rows;
    }

    public static final class Result {
        public final List<ExecutionTask> executionTasks = new ArrayList<>();
        public final List<JsonObject> queries = new ArrayList<>();
    }

    /**
     * Which shared locations the manual roots can still reach.
     *
     * <p>A carrier is not something an experiment declares and not "every
     * read the recording made".  It is a location whose value this
     * campaign's roots can still change, and the runtime-refined dataflow
     * graph already states that relation on both of its halves:</p>
     *
     * <ul>
     *   <li><b>data dependence</b> -- a value edge ({@code field_write},
     *   {@code field_mutation}, {@code call_return}, {@code local_def_use},
     *   {@code caller_argument}, the wire {@code handoff} kinds) carries a
     *   root-dependent value into the cell it targets, so that cell is
     *   root-dependent too;</li>
     *   <li><b>control dependence</b> -- a {@code GUARD} edge
     *   ({@code path_guard_dependency}, {@code heap_mutation_path_guard},
     *   {@code receiver_field_effect_path_guard}) runs from the guard's
     *   operand to the definition the guard controls, so a write whose case
     *   partition a root decides is reached by exactly the same forward
     *   walk.</li>
     * </ul>
     *
     * <p>So one transitive forward closure from the root cells over
     * <em>all</em> edges answers both, and the fixed point is what the
     * design calls the carrier set: a read of a carrier that feeds another
     * store lands on that store's cell on the next hop.</p>
     *
     * <p><b>Static final fields can never be carriers</b>, and that is a
     * property of the walk rather than a case in it: a field nothing ever
     * writes appears only as a {@code fromCell}, is the target of no edge,
     * and is therefore unreachable from any root unless it is one.
     * {@code aFieldNothingWritesIsNeverACarrier} pins it.</p>
     *
     * <p>The slice is <b>withheld</b> -- {@link #usable()} false, nothing
     * narrowed -- when no declared root resolves to a cell of this graph.
     * A campaign whose roots the graph does not name has no forward
     * dependence to measure, and narrowing on an empty seed would concrete
     * every read and delete the evidence rather than the waste (the
     * measured HDFS-17960 collapse: 46 guarded reads to 0).</p>
     */
    static final class RootDependenceSlice {
        /** Every cell a root can still reach, roots included. */
        private final Set<String> reachable;
        /** The root cells this graph actually named. */
        private final Set<String> roots;
        /**
         * Location keys ({@code owner#field}) admitted beside the reachable
         * cells: the fields of the proposed actions the slice carries.
         *
         * <p>A library leaf such as {@code AtomicInteger#value} is a source
         * cell of its own and meets its receiver's field only at the local
         * the accessor's value lands in, so it is on the slice as an action
         * ({@link #carries}) without its field ever being a reachable cell.
         * A location decision -- which shared carriers a task declares,
         * which flows carry root dependence -- must give the same answer as
         * the action decision, so those fields are admitted here.</p>
         */
        private final Set<String> admittedLocations;

        private RootDependenceSlice(Set<String> reachable, Set<String> roots) {
            this(reachable, roots, Collections.<String>emptySet());
        }

        private RootDependenceSlice(Set<String> reachable, Set<String> roots,
                                    Set<String> admittedLocations) {
            this.reachable = reachable;
            this.roots = roots;
            this.admittedLocations = admittedLocations;
        }

        /** The withheld slice: it narrows nothing. */
        static RootDependenceSlice withheld() {
            return new RootDependenceSlice(Collections.<String>emptySet(),
                    Collections.<String>emptySet());
        }

        /**
         * This slice with the locations of the carried actions admitted.
         *
         * <p>Every action in {@code proposals} that {@link #carries} or that
         * {@code root} calls a root contributes the fields it names -- the
         * declared, access and leaf signatures, the last field-path
         * declaration and the Atomic value leaf behind a declared atomic
         * mutator -- as {@code owner#field} keys.  A withheld slice stays
         * withheld.</p>
         */
        RootDependenceSlice admittingActionLocations(
                Iterable<Map.Entry<String, JsonArray>> proposals,
                java.util.function.BiPredicate<String, JsonObject> root) {
            if (!usable()) return this;
            Set<String> admitted = new LinkedHashSet<>(admittedLocations);
            for (Map.Entry<String, JsonArray> proposal : proposals == null
                    ? Collections.<Map.Entry<String, JsonArray>>emptyList()
                    : proposals) {
                for (JsonElement element : proposal.getValue()) {
                    if (!element.isJsonObject()) continue;
                    JsonObject action = element.getAsJsonObject();
                    if (!carries(action)
                            && !root.test(proposal.getKey(), action)) {
                        continue;
                    }
                    admitted.addAll(actionLocations(action));
                }
            }
            return new RootDependenceSlice(reachable, roots, admitted);
        }

        /**
         * The {@code owner#field} keys of every field one action names,
         * spelled as the planner spells a shared carrier.
         */
        static Set<String> actionLocations(JsonObject action) {
            Set<String> keys = new LinkedHashSet<>();
            List<String> declarations = new ArrayList<>();
            for (String member : new String[]{"declaredFieldSignature",
                    "accessFieldSignature", "leafFieldSignature"}) {
                String value = optionalString(action, member);
                if (!value.isEmpty()) declarations.add(value);
            }
            JsonArray paths = array(action, "fieldPathDeclarations");
            if (paths.size() > 0
                    && paths.get(paths.size() - 1).isJsonPrimitive()) {
                declarations.add(
                        paths.get(paths.size() - 1).getAsString().trim());
            }
            String callee = optionalString(action, "declaredCallee");
            for (String declaration : declarations) {
                FieldPathSpec.DeclaredField field =
                        FieldPathSpec.declaredField(declaration);
                if (field == null) continue;
                String key = SharedFieldFlow.fieldKey(field.owner(),
                        field.name());
                if (!key.isEmpty()) keys.add(key);
                FieldPathSpec.DeclaredField atomic = FieldPathSpec
                        .declaredField(SharedFieldFlow.atomicValueField(
                                field.signature(), callee));
                if (atomic != null) {
                    keys.add(SharedFieldFlow.fieldKey(atomic.owner(),
                            atomic.name()));
                }
            }
            return keys;
        }

        /**
         * This slice narrowed to what the failing read can still consume.
         *
         * <p>The forward closure says which cells a root can move; it does
         * not say which of them the failure ever looks at.  A location the
         * roots reach but the fatal read's backward slice does not is a
         * constant <em>for this failure</em>: the recording fixed it, every
         * replay arm writes the value it observed, and versioning it grows
         * the campaign without adding an arm.  Intersecting the two is what
         * makes "carries a root" mean "carries a root <em>to the read that
         * throws</em>".</p>
         *
         * <p>The admitted action locations survive the narrowing: they are
         * the fields of the actions this slice already carries, named as
         * {@code owner#field} keys rather than as cells, so the backward
         * walk over cells has no opinion about them and refusing them here
         * would narrow by an absence of evidence.  A withheld slice and an
         * unnamed fatal read both leave the slice exactly as it was.</p>
         */
        RootDependenceSlice reachingFatalRead(
                List<JsonObject> refinedGraph, Set<String> fatalCells) {
            if (!usable() || fatalCells == null || fatalCells.isEmpty()) {
                return this;
            }
            Map<String, Set<String>> backward = new LinkedHashMap<>();
            Set<String> known = new LinkedHashSet<>();
            for (JsonObject edge : refinedGraph == null
                    ? Collections.<JsonObject>emptyList() : refinedGraph) {
                String from = optionalString(edge, "fromCell");
                String to = optionalString(edge, "toCell");
                if (from.isEmpty() || to.isEmpty()) continue;
                backward.computeIfAbsent(to,
                        ignored -> new LinkedHashSet<>()).add(from);
                known.add(from);
                known.add(to);
            }
            Set<String> seeds = new LinkedHashSet<>();
            for (String cell : fatalCells) {
                if (known.contains(cell)) seeds.add(cell);
            }
            // A fatal read the graph has no cell for states nothing about
            // what reaches it, so it narrows nothing rather than everything.
            if (seeds.isEmpty()) return this;
            Set<String> consumed = new LinkedHashSet<>(seeds);
            Deque<String> pending = new ArrayDeque<>(seeds);
            while (!pending.isEmpty()) {
                for (String next : backward.getOrDefault(pending.removeFirst(),
                        Collections.<String>emptySet())) {
                    if (consumed.add(next)) pending.addLast(next);
                }
            }
            Set<String> narrowed = new LinkedHashSet<>(reachable);
            narrowed.retainAll(consumed);
            // The roots themselves stay on the slice: a root the failure
            // reads only through a cell the graph did not resolve is still
            // this campaign's root.
            narrowed.addAll(roots);
            return new RootDependenceSlice(narrowed, roots,
                    admittedLocations);
        }

        /**
         * The forward closure of {@code rootCells} over the refined graph.
         *
         * <p>Seeds the graph does not name are dropped rather than kept as
         * lone members: a root the dataflow graph has no cell for cannot
         * state what it reaches, and keeping it would make the slice claim
         * the root's own read is the whole of its influence.</p>
         *
         * <p><b>Every edge kind is walked, control edges included.</b>  The
         * refined graph states a container mutation's guard as an edge from
         * the deciding value to the mutated <em>location</em> -- a
         * {@code heap_mutation_path_guard} or
         * {@code receiver_field_effect_path_guard} whose {@code toCell} is
         * the field and whose {@code guardedMutations} /
         * {@code guardedEffects} name the mutating site.  Walking it here,
         * and backwards in {@link #reachingFatalRead}, is what puts a value
         * that decides whether a container is mutated on the chain of every
         * read of that container: {@code removeExpiredKeys}'s
         * {@code key.getExpiryDate() &lt; now} reaches
         * {@code BlockTokenSecretManager#allKeys} over exactly such an edge,
         * and the map's readers reach the expiry date back over it.  No edge
         * kind is filtered, so a guard the refined graph states is never a
         * guard this slice drops.</p>
         *
         * <p><b>And no edge is filtered by what the recording executed.</b>
         * The refined graph is the static candidate graph annotated with one
         * execution's bindings, not narrowed by them: a site the run never
         * reached keeps its edges and is stamped
         * {@code runtimeObserved: false}.  This walk reads {@code fromCell}
         * and {@code toCell} only, so root dependence is what the
         * <em>program</em> lets a root reach, not what one recording
         * happened to take -- which is what lets a campaign be recorded on a
         * healthy configuration and still plan the carriers of the branch a
         * flipped root will take.  Consulting {@code runtimeObserved} here
         * would make the plan a function of the recording's luck.</p>
         */
        static RootDependenceSlice forward(
                List<JsonObject> refinedGraph, Set<String> rootCells) {
            Map<String, Set<String>> forward = new LinkedHashMap<>();
            Set<String> known = new LinkedHashSet<>();
            for (JsonObject edge : refinedGraph == null
                    ? Collections.<JsonObject>emptyList() : refinedGraph) {
                String from = optionalString(edge, "fromCell");
                String to = optionalString(edge, "toCell");
                if (from.isEmpty() || to.isEmpty()) continue;
                forward.computeIfAbsent(from,
                        ignored -> new LinkedHashSet<>()).add(to);
                known.add(from);
                known.add(to);
            }
            Set<String> seeds = new LinkedHashSet<>();
            for (String cell : rootCells) {
                if (known.contains(cell)) seeds.add(cell);
            }
            if (seeds.isEmpty()) return withheld();
            Set<String> reachable = new LinkedHashSet<>(seeds);
            Deque<String> pending = new ArrayDeque<>(seeds);
            while (!pending.isEmpty()) {
                for (String next : forward.getOrDefault(pending.removeFirst(),
                        Collections.<String>emptySet())) {
                    if (reachable.add(next)) pending.addLast(next);
                }
            }
            return new RootDependenceSlice(reachable, seeds);
        }

        /** False when no root resolved: the caller must narrow nothing. */
        boolean usable() {
            return !roots.isEmpty();
        }

        /** Whether a root can still reach the location this action reads. */
        boolean carries(JsonObject action) {
            for (String cell : actionCells(action)) {
                if (reachable.contains(cell)) return true;
            }
            return false;
        }

        /**
         * Whether a root can still reach one shared location.
         *
         * <p>A plan edge names its location twice: as the declared field
         * signatures it flows through, which are graph cells, and as the
         * {@code owner#field} key the runtime matched on.  Either naming a
         * reachable cell is enough.</p>
         */
        boolean reachesLocation(String location,
                                Iterable<JsonElement> fieldSignatures) {
            for (JsonElement element : fieldSignatures == null
                    ? Collections.<JsonElement>emptyList() : fieldSignatures) {
                if (element.isJsonPrimitive()
                        && reachable.contains(element.getAsString().trim())) {
                    return true;
                }
            }
            return location != null && !location.isEmpty()
                    && reachableLocations().contains(location);
        }

        private Set<String> locations;

        /**
         * Every location a root can still reach, as {@code owner#field}
         * keys: the reachable cells that are declared fields, and the
         * locations admitted for the carried actions.
         */
        Set<String> reachableLocations() {
            if (locations == null) {
                Set<String> keys = new LinkedHashSet<>();
                for (String cell : reachable) {
                    FieldPathSpec.DeclaredField field =
                            FieldPathSpec.declaredField(cell);
                    if (field == null) continue;
                    String key = SharedFieldFlow.fieldKey(field.owner(),
                            field.name());
                    if (!key.isEmpty()) keys.add(key);
                }
                keys.addAll(admittedLocations);
                locations = Collections.unmodifiableSet(keys);
            }
            return locations;
        }

        int rootCellCount() {
            return roots.size();
        }

        int reachableCellCount() {
            return reachable.size();
        }

        /**
         * Every dataflow cell one proposed input action names.
         *
         * <p>The read's own cell is the location for a field or a call
         * return; {@code dependencyCells} is the local the value lands in,
         * which is the only cell an accessor read shares with the graph --
         * a library field like {@code AtomicInteger#value} is a source cell
         * of its own and converges with its receiver's field read only at
         * that local.  Both are consulted so
         * {@code SnapshotManager#numSnapshots} selects the
         * {@code AtomicInteger#value} port the experiment used to have to
         * name by hand.</p>
         */
        static Set<String> actionCells(JsonObject action) {
            Set<String> cells = new LinkedHashSet<>();
            for (String member : new String[]{"cell", "declaredFieldSignature",
                    "accessFieldSignature", "leafFieldSignature"}) {
                String value = optionalString(action, member);
                if (!value.isEmpty()) cells.add(value);
            }
            for (String member : new String[]{
                    "dependencyCells", "fieldPathDeclarations"}) {
                for (JsonElement element : array(action, member)) {
                    if (!element.isJsonPrimitive()) continue;
                    String value = element.getAsString().trim();
                    if (!value.isEmpty()) cells.add(value);
                }
            }
            return cells;
        }
    }

    /**
     * Optional experiment-owned declaration of which inputs may mint a root.
     *
     * <p>Two orthogonal decisions are taken about every proposed input
     * action, and this file governs only the second.</p>
     *
     * <dl>
     *   <dt>TRACK</dt>
     *   <dd>Keep the action {@code SYMBOLIC}, so the replay symbolizes the
     *       read and the VM publishes its {@code ReadFrom} candidates and
     *       container versions.  Every carrier is tracked: instance-field
     *       reads, bounded container states, declared communication cut
     *       ports and accessor returns.  Concretizing a carrier removes no
     *       root -- it deletes the evidence the composition reconstructs
     *       shared state from, because a read the plan never symbolizes
     *       publishes no candidates for the composer to admit.</dd>
     *   <dt>MINT</dt>
     *   <dd>Permission to become a <em>fresh</em> root: a free symbol the
     *       solver may move.  Three authorities carry it and nothing else
     *       does -- an {@code EXPLICIT_SYMBOLIC_FAULT} marker the workload
     *       wrote into its own program text, a field a
     *       {@code CausynthSymbolicSource} hook site owns, and a name this
     *       file declares through {@code fieldSignatures},
     *       {@code portIds} or {@code cells} for the action's own
     *       region.</dd>
     * </dl>
     *
     * <p>One input kind cannot be tracked without minting:
     * {@code EXTERNAL_CALL_RETURN} (a {@code Timer.now()} return, say).
     * Nothing inside the replayed process wrote that value, so there is no
     * carrier expression for the read to reuse and symbolizing it <em>is</em>
     * minting.  An undeclared one is therefore concrete.</p>
     *
     * <p>Wave 3: which symbol reaches which read is decided at replay -- the
     * VM's propagated expression is the authority -- so no selector,
     * selected phase, producer version or output-version boundary is
     * predicted here.</p>
     */
    static final class SymbolicInputSelection {
        /** Decision-row member: the plan symbolizes this read. */
        static final String TRACKED = "tracked";
        /** Action and decision-row member: may become a fresh root. */
        static final String MINT_ELIGIBLE = "mintEligible";
        /** Row kind of one per-action verdict. */
        static final String ROOT_DECISION = "SYMBOLIC_ROOT_DECISION";
        /** Verdict and demand of a read no root can reach. */
        static final String NOT_ROOT_DEPENDENT = "NOT_ROOT_DEPENDENT";
        private final boolean configured;
        /** regionId -> the field signatures, port ids and cells it admits. */
        private final Map<String, Set<String>> admitted;
        /** regionId -> sourceId -> the one field that hook site mints. */
        private final Map<String, Map<String, String>> minted;
        /** Every automatic candidate this selection refused, first-seen order. */
        private final Set<JsonObject> suppressed = new LinkedHashSet<>();
        /** One verdict per decided action, deduplicated, first-seen order. */
        private final Set<JsonObject> decisions = new LinkedHashSet<>();
        /** What the roots can still reach; withheld until seeded. */
        private RootDependenceSlice slice = RootDependenceSlice.withheld();
        /** The locations this run kept as carriers, first-seen order. */
        private final Set<String> carrierLocations = new LinkedHashSet<>();

        /** What each declaration row asked the campaign to change. */
        private final List<JsonObject> declarationDiagnostics;

        private SymbolicInputSelection(
                boolean configured, Map<String, Set<String>> admitted,
                Map<String, Map<String, String>> minted,
                List<JsonObject> declarationDiagnostics) {
            this.configured = configured;
            this.admitted = admitted;
            this.minted = minted;
            this.declarationDiagnostics = declarationDiagnostics;
        }

        List<JsonObject> declarationDiagnostics() {
            return declarationDiagnostics;
        }

        /** One pass over the static hook declarations and, when the campaign
         *  configured one, over the declared field/port/cell rows. */
        static SymbolicInputSelection read(
                Path path, List<JsonObject> regionCatalog,
                List<RegionInstancePlan> regionPlans)
                throws IOException {
            List<JsonObject> diagnostics = new ArrayList<>();
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
                        admitted, minted, diagnostics);
            }
            requireFile(path, "symbolic input selection");
            for (JsonObject row : ArtifactIO.readJsonl(path)) {
                for (String regionId : declaredRegions(row, catalogRegions,
                        regionPlans, diagnostics)) {
                    Set<String> names = admitted.computeIfAbsent(regionId,
                            ignored -> new LinkedHashSet<>());
                    for (String field : new String[]{
                            "fieldSignatures", "portIds", "cells"}) {
                        addDeclaredNames(names, row, field);
                    }
                }
            }
            return new SymbolicInputSelection(true, admitted, minted,
                    diagnostics);
        }

        /**
         * Which planned regions one declaration row admits its names in.
         *
         * <p>A manual root belongs to a <em>site</em> -- the class and method
         * the cell is read in -- not to a region.  A region id is a hash the
         * planner mints from what the recording selected, so it moves when
         * the selection moves, and a campaign that spells one has to be
         * re-derived by hand every time: that is what refused bug3's clock
         * declaration at PLAN when the retained region set changed
         * underneath it.  A site is what the experiment actually knows, and
         * it is resolved here, against the plan that names each region's
         * {@code targetMethod}.</p>
         *
         * <p>A site that matches no planned region is a hard error naming the
         * site: the campaign asked for a root the plan cannot carry, and
         * running on without it would silently drop the root.  A site that
         * matches several regions declares the root in each of them -- the
         * same Java method planned on two nodes is two regions and the
         * declaration means both -- unless it scopes itself to a node or an
         * epoch.  The region-id form is still read, and asks in the policy
         * artifact to be rewritten as a site.</p>
         */
        private static List<String> declaredRegions(
                JsonObject row, Set<String> catalogRegions,
                List<RegionInstancePlan> regionPlans,
                Collection<JsonObject> diagnostics) throws IOException {
            String regionId = firstNonBlank(optionalString(row, "regionId"));
            if (!regionId.isEmpty()) {
                if (!catalogRegions.contains(regionId)) {
                    throw new IOException("symbolic input selection names "
                            + "an unknown static region: " + regionId);
                }
                if (diagnostics != null) {
                    diagnostics.add(regionIdDeclarationDiagnostic(regionId));
                }
                return Collections.singletonList(regionId);
            }
            String method = declaredMethod(row);
            if (method.isEmpty()) {
                throw new IOException("symbolic input selection row declares "
                        + "neither a regionId nor a static site "
                        + "(class + method): " + row);
            }
            String node = firstNonBlank(optionalString(row, "node"));
            String epoch = firstNonBlank(optionalString(row, "epoch"));
            List<String> resolved = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();
            for (RegionInstancePlan plan : regionPlans == null
                    ? Collections.<RegionInstancePlan>emptyList()
                    : regionPlans) {
                if (!method.equals(optionalString(plan.json(),
                        "targetMethod"))
                        || !scopeAdmits(plan.sourceKey(), node, epoch)
                        || !catalogRegions.contains(plan.regionId())) {
                    continue;
                }
                if (seen.add(plan.regionId())) resolved.add(plan.regionId());
            }
            if (resolved.isEmpty()) {
                throw new IOException("symbolic input selection names a "
                        + "static site no planned region covers: " + method
                        + (node.isEmpty() ? "" : " on node " + node)
                        + (epoch.isEmpty() ? "" : " at epoch " + epoch));
            }
            return resolved;
        }

        /**
         * The canonical signature a site declaration names.
         *
         * <p>Either spelling is read: the whole Soot signature in
         * {@code method}, or {@code class} plus the method's own
         * {@code returnType name(argumentTypes)} half.</p>
         */
        static String declaredMethod(JsonObject row) throws IOException {
            String method = firstNonBlank(optionalString(row, "method"));
            if (method.isEmpty()) return "";
            if (method.startsWith("<")) {
                if (!method.endsWith(">") || !method.contains(": ")) {
                    throw new IOException("symbolic input selection method "
                            + "is not a signature: " + method);
                }
                return method;
            }
            String declaring = firstNonBlank(optionalString(row, "class"));
            if (declaring.isEmpty()) {
                throw new IOException("symbolic input selection names a "
                        + "method with no declaring class: " + method);
            }
            return "<" + declaring + ": " + method + ">";
        }

        /**
         * Whether one planned region's source key is inside the declared
         * scope.  {@code sourceKey} reads {@code <workload>/<node>#epoch<n>};
         * an undeclared node or epoch admits every one of them.
         */
        static boolean scopeAdmits(String sourceKey, String node,
                                   String epoch) {
            if (node.isEmpty() && epoch.isEmpty()) return true;
            String key = safe(sourceKey);
            int slash = key.indexOf('/');
            String address = slash < 0 ? key : key.substring(slash + 1);
            int hash = address.indexOf('#');
            String actualNode = hash < 0 ? address
                    : address.substring(0, hash);
            String actualEpoch = hash < 0 ? "" : address.substring(hash + 1);
            if (actualEpoch.startsWith("epoch")) {
                actualEpoch = actualEpoch.substring("epoch".length());
            }
            return (node.isEmpty() || node.equals(actualNode))
                    && (epoch.isEmpty() || epoch.equals(actualEpoch));
        }

        /** Asks, once per row, for the site form the plan can resolve. */
        private static JsonObject regionIdDeclarationDiagnostic(
                String regionId) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", "CONCOLIC_PLAN_DIAGNOSTIC");
            row.addProperty("stage", "PLAN");
            row.addProperty("source", "SYMBOLIC_INPUT_SELECTION");
            row.addProperty("code", REGION_ID_DECLARATION);
            row.addProperty("subject", regionId);
            row.addProperty("detail", "this manual root is declared by a "
                    + "planner-minted region hash, which moves when the "
                    + "selection moves; declare it by its static site "
                    + "(class + method, optionally node/epoch) instead");
            return row;
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

        /**
         * Seeds the carrier slice from this campaign's manual roots.
         *
         * <p>The roots are the three authorities {@code decide} already
         * recognises and nothing else: a field a {@code
         * CausynthSymbolicSource} hook owns, an {@code
         * EXPLICIT_SYMBOLIC_FAULT} marker the workload wrote, and a name
         * this file declares.  Their cells are read off the declarations
         * <em>and</em> off the proposed actions, because a row that
         * declares a {@code portId} names no dataflow cell of its own --
         * only the action it selects does.</p>
         *
         * <p>Called once, before any {@code select}, so every region
         * narrows against the same slice.</p>
         */
        void seedCarrierSlice(
                List<JsonObject> refinedGraph,
                List<Map.Entry<String, JsonArray>> proposals) {
            Set<String> rootCells = new LinkedHashSet<>();
            for (Map<String, String> sites : minted.values()) {
                rootCells.addAll(sites.values());
            }
            for (Set<String> names : admitted.values()) {
                rootCells.addAll(names);
            }
            for (Map.Entry<String, JsonArray> proposal : proposals == null
                    ? Collections.<Map.Entry<String, JsonArray>>emptyList()
                    : proposals) {
                String regionId = proposal.getKey();
                for (JsonElement element : proposal.getValue()) {
                    if (!element.isJsonObject()) continue;
                    JsonObject action = element.getAsJsonObject();
                    if (!minted(regionId, action)
                            && !admits(regionId, action)
                            && !workloadOwnedSymbol(action)) {
                        continue;
                    }
                    rootCells.addAll(
                            RootDependenceSlice.actionCells(action));
                }
            }
            slice = RootDependenceSlice.forward(refinedGraph, rootCells)
                    .admittingActionLocations(proposals, this::rootAction);
        }

        /** What the roots reach, for the policy artifact. */
        RootDependenceSlice carrierSlice() {
            return slice;
        }

        /**
         * Whether {@code decide} would call this action a root: hook-owned,
         * declared for its region, or a marker the workload wrote.  The
         * same three authorities seed the carrier slice, so an occurrence
         * that contains one is a root site by construction.
         */
        boolean rootAction(String regionId, JsonObject action) {
            return minted(regionId, action) || admits(regionId, action)
                    || workloadOwnedSymbol(action);
        }

        /** The distinct locations this run kept, in first-seen order. */
        JsonArray carrierLocations() {
            JsonArray rows = new JsonArray();
            for (String location : carrierLocations) rows.add(location);
            return rows;
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
                    decide(regionId, action, retained);
                }
                selected.add(retained);
            }
            return selected;
        }

        /**
         * Stamps one proposed input with its TRACK and MINT verdicts.
         *
         * <p>The authored {@code symbolicDemand} survives a tracked action
         * untouched: it is what tells the replay that a
         * {@code BOUNDED_CONTAINER_STATE} port models a whole container
         * rather than a scalar, and overwriting it with this file's verdict
         * would silently downgrade the carrier the verdict just kept.</p>
         */
        private void decide(
                String regionId, JsonObject action, JsonObject retained) {
            if (minted(regionId, action)) {
                // The Java hook mints this exact root once, at its own call
                // site; a second action for the same location would add a
                // free root beside it.
                retained.addProperty("mode", "CONCRETE");
                retained.addProperty("symbolicDemand",
                        "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED");
                record(regionId, action, false, false, true,
                        "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED");
                return;
            }
            if (declaredCutPort(action)) {
                // Tracked, and never mint-eligible.  The value this port
                // names is produced on the other side of the wire and
                // installed at the consumer by attachCommunicationLeaf, so
                // the consumer's copy carries the producer's expression and
                // starts no search of its own.  Naming the port in the
                // selection file cannot change that -- a root minted here is
                // a free variable the attach immediately overwrites, which
                // is how HDFS-17899 bug3 acquired four existential roots on
                // PBHelper.convert(BlockKeyProto) -- so the declaration is
                // not allowed to reach it.
                retained.addProperty(MINT_ELIGIBLE, false);
                String port = firstNonBlank(actionField(action),
                        optionalString(action, "cell"));
                if (!port.isEmpty()) carrierLocations.add(port);
                record(regionId, action, true, false, false,
                        InputActionCatalog.DECLARED_COMMUNICATION_CUT_PORT);
                return;
            }
            boolean declared = admits(regionId, action);
            // The workload wrote this symbol into its own program text; that
            // is a declaration in the same sense a hook call is one, so an
            // allowlist over the automatic candidates must not delete it.
            boolean workloadOwned = workloadOwnedSymbol(action);
            if (!declared && !workloadOwned && mintsWithoutACarrier(action)) {
                retained.addProperty("mode", "CONCRETE");
                retained.addProperty("symbolicDemand",
                        "CONFIGURED_SYMBOLIC_INPUT_UNSELECTED");
                suppressed.add(suppressedCandidate(regionId, action));
                record(regionId, action, false, false, false,
                        "CONFIGURED_SYMBOLIC_INPUT_UNSELECTED");
                return;
            }
            if (!declared && !workloadOwned && slice.usable()
                    && !slice.carries(action)) {
                // No root reaches this location, so every replay arm writes
                // the value the recording observed: it is a constant for
                // this failure, and publishing ReadFrom candidates and
                // container versions for it buys no behaviour.
                retained.addProperty("mode", "CONCRETE");
                retained.addProperty("symbolicDemand", NOT_ROOT_DEPENDENT);
                record(regionId, action, false, false, false,
                        NOT_ROOT_DEPENDENT);
                return;
            }
            if (!declared && !workloadOwned) {
                String location = firstNonBlank(actionField(action),
                        optionalString(action, "cell"));
                if (!location.isEmpty()) carrierLocations.add(location);
            }
            // TRACK is already stated by the surviving SYMBOLIC mode; the
            // row carries only the verdict the replay cannot infer.
            retained.addProperty(MINT_ELIGIBLE, declared || workloadOwned);
            if (declared) {
                // Named by hand: the replay mints here rather than reusing
                // whatever carrier happens to wrap the read.
                retained.addProperty(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT, true);
            }
            record(regionId, action, true, declared || workloadOwned,
                    declared, declared ? "DECLARED_SYMBOLIC_ROOT"
                            : workloadOwned ? "WORKLOAD_DECLARED_SYMBOLIC_FAULT"
                            : "TRACKED_CARRIER");
        }

        /**
         * A port declared by {@code communication-mappings.jsonl}.
         *
         * <p>It is a handoff, not a mint: the consumer reuses the producer's
         * already-propagated expression.  {@code ConcolicRegionRuntime
         * .declaredCommunicationCutPort} answers the same question at
         * replay, off the same {@code sourceKind}, so the two stages agree
         * without the plan carrying a second marker.</p>
         */
        private static boolean declaredCutPort(JsonObject action) {
            return RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                    .equals(optionalString(action, "sourceKind"));
        }

        /** An explicit {@code Debug.makeSymbolicBoolean} marker: the fault
         *  symbol is written in the workload's own source, so it needs no
         *  row in the selection file to survive it. */
        private static boolean workloadOwnedSymbol(JsonObject action) {
            return RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                    .equals(optionalString(action, "sourceKind"));
        }

        /**
         * Whether symbolizing this input can only mint.
         *
         * <p>A carrier read observes a value some store inside the replayed
         * process already holds, so the VM has an expression to hand back
         * and tracking it costs no root.  An {@code EXTERNAL_CALL_RETURN}
         * has no such writer -- the value enters from outside the recording
         * -- so there is nothing to carry and a symbolic one is a free root
         * by construction.  Undeclared, it stays at its recorded value.</p>
         */
        private static boolean mintsWithoutACarrier(JsonObject action) {
            return RuntimeSelectedRegionFinalizer.EXTERNAL_CALL_RETURN
                    .equals(optionalString(action, "sourceKind"));
        }

        /** Names one automatic candidate the selection file refused, so a
         *  root that is missing downstream can be traced to this decision
         *  rather than to the mechanism that proposed it. */
        private static JsonObject suppressedCandidate(
                String regionId, JsonObject action) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", SUPPRESSED_ROOT_CANDIDATE);
            row.addProperty("regionId", safe(regionId));
            row.addProperty("sourceKind",
                    optionalString(action, "sourceKind"));
            row.addProperty("siteId", firstNonBlank(
                    optionalString(action, "siteId"),
                    optionalString(action, "staticAccessSiteId")));
            row.addProperty("declaredCallee",
                    optionalString(action, "declaredCallee"));
            row.addProperty("fieldSignature", actionField(action));
            row.addProperty("cell", optionalString(action, "cell"));
            row.addProperty("portId", actionPort(action));
            row.addProperty("reason",
                    "CONFIGURED_SYMBOLIC_INPUT_UNSELECTED");
            return row;
        }

        /** Both verdicts for one action, so "why is this read concrete" and
         *  "why did this read mint" are answerable from one file. */
        private void record(String regionId, JsonObject action,
                            boolean tracked, boolean mintEligible,
                            boolean declared, String verdict) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", ROOT_DECISION);
            row.addProperty("regionId", safe(regionId));
            row.addProperty("sourceKind",
                    optionalString(action, "sourceKind"));
            row.addProperty("symbolicDemand",
                    optionalString(action, "symbolicDemand"));
            row.addProperty("siteId", firstNonBlank(
                    optionalString(action, "siteId"),
                    optionalString(action, "staticAccessSiteId")));
            row.addProperty("fieldSignature", actionField(action));
            row.addProperty("cell", optionalString(action, "cell"));
            row.addProperty("portId", actionPort(action));
            row.addProperty(TRACKED, tracked);
            row.addProperty(MINT_ELIGIBLE, mintEligible);
            row.addProperty("declared", declared);
            row.addProperty("verdict", verdict);
            decisions.add(row);
        }

        /** The refused candidates of this run, deduplicated, in first-seen
         *  order; empty when no selection file narrowed anything. */
        JsonArray suppressedRootCandidates() {
            JsonArray rows = new JsonArray();
            for (JsonObject row : suppressed) rows.add(row.deepCopy());
            return rows;
        }

        /** One row per distinct action this file decided. */
        JsonArray rootDecisions() {
            JsonArray rows = new JsonArray();
            for (JsonObject row : decisions) rows.add(row.deepCopy());
            return rows;
        }

        /** Whether a declaring hook site of this region mints the action's
         *  field: one field is one root, and the hook owns it. */
        private boolean minted(String regionId, JsonObject action) {
            String field = actionField(action);
            return !field.isEmpty() && minted.getOrDefault(safe(regionId),
                    Collections.<String, String>emptyMap())
                    .containsValue(field);
        }

        /** Whether one region admits one declared name, for tests. */
        boolean declares(String regionId, String name) {
            Set<String> names = admitted.get(safe(regionId));
            return names != null && names.contains(name);
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
        private final List<JsonObject> refinedGraph;
        private final JsonObject regionPlanIdentity;
        private final JsonObject refinedGraphIdentity;
        private final JsonObject symbolicInputsIdentity;
        private final SymbolicInputSelection symbolicInputs;

        private LoadedInputs(List<RegionInstancePlan> regionPlans,
                             List<JsonObject> summaries,
                             Map<String, Region> regionIndex,
                             DefinitionIndex definitions,
                             List<JsonObject> refinedGraph,
                             JsonObject regionPlanIdentity,
                             JsonObject refinedGraphIdentity,
                             JsonObject symbolicInputsIdentity,
                             SymbolicInputSelection symbolicInputs) {
            this.regionPlans = regionPlans;
            this.summaries = summaries;
            this.regionIndex = regionIndex;
            this.definitions = definitions;
            this.refinedGraph = refinedGraph;
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
        /** The occurrence of the annotated site the case declares, or "". */
        public final String targetOccurrence;
        private final ClosureMode closureMode;

        private Arguments(Path regionPlan, Path refinedGraph, Path summaries,
                          Path outputDirectory, String regionId,
                          String occurrenceId, String goalId,
                          int maxJobs, int maxLoopIterations,
                          Path symbolicInputs, ClosureMode closureMode,
                          String targetOccurrence) {
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
            this.targetOccurrence = safe(targetOccurrence);
        }

        public static Arguments parse(String[] args) {
            Map<String, String> values = parseArgs(args, "region-plan",
                    "refined-graph", "summaries", "output-dir", "max-jobs",
                    "symbolic-inputs", "max-loop-iterations",
                    "closure-mode", "target-occurrence");
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
                    symbolicInputs, closureMode,
                    values.get("target-occurrence"));
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
                    symbolicInputs, closureMode, targetOccurrence);
        }

    }
}
