package edu.uva.liftlab.graphchecker.plan;


import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.plan.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.plan.RegionInstancePlan.Goal;
import edu.uva.liftlab.graphchecker.plan.RuntimePlanArtifact;
import edu.uva.liftlab.graphchecker.plan.StaticSymbolicSourceDeclaration;
import edu.uva.liftlab.graphchecker.plan.SiteId;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.AbstractMap;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** Builds graph-directed concolic jobs from static regions and concrete
 * runtime-selected region instance plans. */
public final class ConcolicScheduler {
    private ConcolicScheduler() {
    }

    public static void main(String[] args) throws Exception {
        scheduleTargetFirst(Arguments.parse(args));
    }

    private static LoadedInputs loadInputs(Arguments arguments)
            throws IOException {
        requireFile(arguments.regionPlan, "region plan");
        requireFile(arguments.candidateGraph, "candidate data-flow graph");
        requireFile(arguments.staticScopeMap, "static scope map");
        Files.createDirectories(arguments.outputDirectory);

        JsonObject regionPlanIdentity = artifactIdentity(
                arguments.regionPlan);
        JsonObject candidateGraphIdentity = artifactIdentity(
                arguments.candidateGraph);
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
        List<JsonObject> candidateGraph = ArtifactIO.readJsonl(
                arguments.candidateGraph);
        requireCandidateGraph(candidateGraph);
        SymbolicInputSelection symbolicInputs =
                SymbolicInputSelection.read(arguments.symbolicInputs,
                        regions, regionPlans);
        Set<String> regionIndex = regionIndex(regions);
        StaticScopeMap staticScopeMap = StaticScopeMap.read(
                arguments.staticScopeMap);
        if (!staticScopeMap.stated()) {
            throw new IOException("static scope map states no site: "
                    + arguments.staticScopeMap);
        }
        // The identities recorded here are verified once, against the same
        // files, at the point the schedule index commits them.
        return new LoadedInputs(regionPlans, regionIndex,
                candidateGraph, staticScopeMap,
                regionPlanIdentity,
                candidateGraphIdentity, symbolicInputsIdentity,
                symbolicInputs);
    }

    private static Result scheduleLoaded(
            Arguments arguments, LoadedInputs loaded)
            throws IOException {
        // A declaration names a value and the graph names that value once
        // per local it is copied into, so the declared names are resolved
        // over Soot's exact-copy edges once, before any region selects.
        loaded.symbolicInputs.resolveDeclaredNames(loaded.candidateGraph);
        List<Candidate> candidates = candidates(arguments,
                loaded.regionPlans, loaded.regionIndex,
                loaded.staticScopeMap);
        Collections.sort(candidates, Candidate.ORDER);

        LoopBoundPolicy loopBound = declaredLoopBounds(
                LoopBoundPolicy.declaredDefault(), loaded.regionPlans);
        Result result = new Result();
        for (Candidate candidate : candidates) {
            JsonArray taskInputActions = candidate.inputActions;
            JsonArray selectedInputs = loaded.symbolicInputs.select(
                    candidate.goal.plan().regionId(), taskInputActions);
            selectedInputs = removeInboundProtocolHandoffInputs(
                    selectedInputs,
                    CommunicationHandoffSpec.decode(
                            candidate.goal.plan().json()));
            String taskId = candidate.seedTaskId(selectedInputs);
            if (result.executionTasks.size() >= arguments.maxJobs) {
                continue;
            }
            ExecutionTask scheduled = ExecutionTask.create(candidate.goal,
                    taskId, selectedInputs,
                    branchMethods(candidate.branches), loopBound);
            // json() is the live row by decision (contract/PlanRow): the
            // scheduler annotates the task it has just created, and no typed
            // member it already decoded is derived from these carriers.
            JsonObject executionTask = scheduled.json();
            if (candidate.goal.kind().capturesTargetReach()) {
                // The branch event this occurrence must decide, and the arm
                // that reaches the annotated throw -- phi's fatal polarity,
                // stated by the one guard authority
                // (static_scope_map's TARGET_SITE row) and carried here so
                // no later stage re-derives it.
                JsonObject target = new JsonObject();
                target.addProperty("siteId", candidate.targetSiteId);
                target.addProperty("occurrence",
                        candidate.targetOccurrence);
                target.addProperty("requiredOutcome",
                        candidate.targetRequiredOutcome);
                executionTask.add("targetBranch", target);
            }

            result.executionTasks.add(scheduled);
        }
        // Which stores of a declared input's cell the replay must observe:
        // one campaign-wide answer, computed from the same refined graph the
        // root-dependence slice is computed from, and annotated onto every
        // task because a location is shared and the first write of it in
        // the window is what starts its log -- whichever occurrence makes
        // it.  json() is the live row by decision (PlanRow).
        JsonArray writeSites = loaded.staticScopeMap.writeSitesOf(
                declaredInputCells(result.executionTasks));
        if (writeSites.size() > 0) {
            for (ExecutionTask task : result.executionTasks) {
                task.json().add(ExecutionTask.OBSERVED_WRITE_SITES,
                        writeSites.deepCopy());
            }
        }
        return result;
    }

    /**
     * The exact cells this campaign's DECLARED region inputs name.
     *
     * <p>Only a declared input: the experiment said "the search starts at
     * this cell", and the write sites of anything else are not this
     * campaign's business.</p>
     */
    static Set<String> declaredInputCells(Iterable<ExecutionTask> tasks) {
        Set<String> cells = new LinkedHashSet<>();
        for (ExecutionTask task : tasks == null
                ? Collections.<ExecutionTask>emptyList() : tasks) {
            for (JsonElement element : task.inputActions().all()) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                if (!optionalBool(action,
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT, false)) {
                    continue;
                }
                for (String member : new String[]{"leafFieldSignature",
                        "accessFieldSignature", "cell"}) {
                    String signature = optionalString(action, member);
                    if (FieldPathSpec.declaredField(signature) != null) {
                        cells.add(signature);
                    }
                }
            }
        }
        return cells;
    }

    /**
     * A selected receive gets its symbolic value from the VM handoff.  A
     * local action for the same exact port would mint a temporary second root
     * before attach, so it is not part of the frozen task.
     *
     * <p>The rule reads the DECLARED handoff spec: an IN site is where this
     * occurrence attaches, which is its own declaration and not something an
     * edge row grants it.  It used to additionally require a correlated
     * exchange binding naming the port -- a second authority over the same
     * declaration.  Measured on both kept corpora the two sets are equal
     * (hdfs-11741: 48 declared IN ports, 48 supplied; hdfs-17960: 0 and 0)
     * and neither rule suppresses any action, so no task changes.</p>
     */
    static JsonArray removeInboundProtocolHandoffInputs(
            JsonArray actions,
            Iterable<CommunicationHandoffSpec> declaredHandoffs) {
        Set<String> suppliedPorts = new LinkedHashSet<>();
        if (declaredHandoffs != null) {
            for (CommunicationHandoffSpec handoff : declaredHandoffs) {
                if (handoff != null && !handoff.outgoing()) {
                    suppliedPorts.add(handoff.portId());
                }
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

    /**
     * The methods whose conditional branches this task's weave covers.
     *
     * <p>The plan names methods, not sites: INSTRUMENT weaves
     * {@code markConcolicBranch} at every conditional branch of every method
     * it instruments, so the site list the region plan carries is the
     * scheduler's own scope answer and not a per-branch selection anything
     * downstream has to honour.</p>
     */
    private static JsonArray branchMethods(JsonArray branches) {
        java.util.TreeSet<String> methods = new java.util.TreeSet<>();
        for (JsonElement element : branches == null
                ? new JsonArray() : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            String method = firstNonBlank(
                    optionalString(branch, "method"),
                    SiteId.methodOf(optionalString(branch, "siteId")));
            if (!method.isEmpty()) methods.add(method);
        }
        JsonArray result = new JsonArray();
        for (String method : methods) result.add(method);
        return result;
    }

    /**
     * The arm of one branch site that reaches the annotated target.
     *
     * <p>The one guard authority, {@code causynth.SiteControlDependence},
     * computed this in ANALYZE and published it on the TARGET_SITE row of
     * {@code static_scope_map.jsonl}: post-dominance keeps a branch exactly
     * when one arm makes the throw unavoidable, so the kept branch names
     * that arm.  {@code null} means this map states no arm for the site,
     * which is a refusal at the caller and never a default.</p>
     */
    static Boolean fatalArm(StaticScopeMap map, String guardSiteId) {
        Boolean found = null;
        for (StaticScopeMap.Site target : map.targetSites()) {
            Boolean arm = target.outcomeOf(guardSiteId);
            if (arm == null) continue;
            if (found != null && !found.equals(arm)) {
                throw new IllegalArgumentException(
                        "AMBIGUOUS_FATAL_ARM: " + guardSiteId + " reaches "
                                + "the annotated target on both arms");
            }
            found = arm;
        }
        return found;
    }

    static Result scheduleTargetFirst(Arguments arguments)
            throws IOException {
        LoadedInputs loaded = loadInputs(arguments);
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.workflow(loaded.regionPlans,
                        arguments.targetOccurrence);
        requireRetainedRegions(arguments.retainRegions, workflow);
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
        }
        Result result = new Result();
        result.executionTasks.addAll(sortedValues(tasks));
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
        JsonObject taskPlanIdentity = artifactIdentity(taskPlan);
        JsonObject index = workflow.scheduleIndex(result.executionTasks,
                loaded.regionPlanIdentity, taskPlanIdentity);
        requireArtifactIdentity(arguments.regionPlan,
                loaded.regionPlanIdentity,
                "region plan changed while scheduling");
        requireArtifactIdentity(arguments.candidateGraph,
                loaded.candidateGraphIdentity,
                "candidate data-flow graph changed while scheduling");
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

    private static <T> List<T> sortedValues(Map<String, T> values) {
        List<String> keys = new ArrayList<>(values.keySet());
        Collections.sort(keys);
        List<T> result = new ArrayList<>();
        for (String key : keys) result.add(values.get(key));
        return result;
    }

    private static List<Candidate> candidates(Arguments arguments,
                                              List<RegionInstancePlan>
                                                      regionPlans,
                                              Set<String> regions,
                                              StaticScopeMap scopeMap)
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
            if (!regions.contains(plan.regionId())) {
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
                appendGoalCandidates(arguments, result, goal, scopeMap);
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
                    LoopBoundPolicy.PLAN_FIELD)) {
                if (!element.isJsonObject()) continue;
                JsonObject loop = element.getAsJsonObject();
                String loopSiteId = optionalString(loop,
                        LoopBoundPolicy.LOOP_SITE_ID);
                int bound = optionalInteger(loop, LoopBoundPolicy.LOOP_BODY_BOUND, 0);
                if (loopSiteId.isEmpty() || bound < 1) continue;
                Integer held = declared.put(loopSiteId, bound);
                if (held != null && held.intValue() != bound) {
                    throw new IllegalStateException(
                            LoopBoundPolicy.LOOP_BODY_BOUND_DISAGREES
                                    + ": loop " + loopSiteId + " is planned"
                                    + " under K_L=" + held + " and K_L="
                                    + bound + "; one loop has one prefix");
                }
            }
        }
        return LoopBoundPolicy.cfgBackedges(inheritedBound, declared);
    }

    /**
     * The one candidate of one replayable goal.
     *
     * <p>A region-path goal replays its own occurrence.  A target-reach goal
     * additionally names the branch event it must decide: the branch the ONE
     * guard authority named as a guard of the annotated throw, at the
     * occurrence the recording decided it, on the arm that reaches the
     * throw.  Nothing here searches for a path, ranks a branch or elects an
     * occurrence: a case that states no target occurrence is refused by name
     * in {@link RuntimeWorkflowDiscovery}, and one with no guarded failure
     * branch is refused below.</p>
     */
    private static void appendGoalCandidates(
            Arguments arguments, List<Candidate> result, Goal goal,
            StaticScopeMap scopeMap)
            throws IOException {
        Set<String> definitionMethods = goal.runtimeDefinitionMethods();
        JsonArray branches = goal.branches();
        JsonArray inputActions = materializationPlan(goal, goal.symbolize(),
                scopeMap, definitionMethods);
        if (goal.kind().capturesRegionPath()) {
            result.add(new Candidate(goal, branches, "", 1, false,
                    inputActions, goal.plan().occurrenceId()));
            return;
        }
        JsonObject fatal = fatalBranch(branches, scopeMap);
        result.add(new Candidate(goal, branches,
                optionalString(fatal, "siteId"),
                Math.max(1, optionalInteger(fatal, "selectedOccurrence", 1)),
                fatalArm(scopeMap, optionalString(fatal, "siteId"))
                        .booleanValue(),
                inputActions,
                targetQueryInstance(arguments, goal)));
    }

    /**
     * The one branch of this region the annotated throw is guarded by.
     *
     * <p>Guarded means what {@code static_scope_map}'s TARGET_SITE row says
     * it means, so a branch is a candidate here only if the map named it and
     * the recording decided it.  Two of them, or none, is a named refusal:
     * phi has one polarity and the anchor one site, and choosing between
     * them is the offline path planning this replaced.</p>
     */
    private static JsonObject fatalBranch(JsonArray branches,
                                          StaticScopeMap scopeMap)
            throws IOException {
        Map<String, JsonObject> bySite = new LinkedHashMap<>();
        Set<String> guardedTargets = new LinkedHashSet<>();
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            String siteId = optionalString(branch, "siteId");
            if (!optionalBool(branch, "failureTarget", false)
                    || !optionalBool(branch, "observed", false)
                    || fatalArm(scopeMap, siteId) == null) {
                continue;
            }
            for (JsonElement cell : array(branch,
                    RuntimeSelectedRegionFinalizer.FAILURE_TARGET_CELLS)) {
                if (cell.isJsonPrimitive()) {
                    guardedTargets.add(cell.getAsString());
                }
            }
            bySite.put(siteId, branch);
        }
        if (bySite.size() != 1 || guardedTargets.size() > 1) {
            throw new IOException("UNSUPPORTED_AMBIGUOUS_TARGET_PATH: "
                    + "expected one guarded failure target and one guard of "
                    + "it; found " + guardedTargets.size()
                    + " guarded failure target(s) and " + bySite.size()
                    + " guard(s) the static scope map names: "
                    + bySite.keySet());
        }
        return bySite.values().iterator().next();
    }

    private static String targetQueryInstance(
            Arguments arguments, Goal goal) {
        String selected = arguments.occurrenceId.isEmpty()
                ? goal.plan().occurrenceId() : arguments.occurrenceId;
        if (!selected.equals(goal.plan().occurrenceId())) {
            throw new IllegalArgumentException(
                    "target goal does not match selected occurrence "
                            + selected);
        }
        return selected;
    }

    /**
     * The binding mode of each proposed input: how the VM would present that
     * location as a symbol, or the one reason it cannot.
     *
     * <p>No admission decision is made here.  {@code
     * SymbolicInputSelection.decide} is the ONE admission rule -- declared,
     * workload-owned, hook-minted or a declared cut port, and
     * UNDECLARED_SYMBOLIC_INPUT otherwise -- and this used to run a
     * fourteen-name refusal taxonomy in front of it: a cost heuristic
     * ("symbolic freedom is only worth its cost when some explored decision
     * can read the value"), a structure-carrier role test, an enum-ordinal
     * and container-cardinality classifier, a JDK-name test, a regex, and an
     * unobserved-input rule.  Measured on the 17960 seed, the taxonomy
     * changed no action's mode -- all 106 rows it labelled were undeclared
     * anyway -- while it could and did drop a DECLARED cell before the one
     * rule saw the declaration.</p>
     *
     * <p>The two refusals that remain are not policy.  A location the VM has
     * no presentation for cannot carry a symbol however it is declared, and
     * neither can a value whose type the SMT layer has no term for.</p>
     */
    static JsonArray materializationPlan(
            Goal goal, JsonArray sourceActions,
            StaticScopeMap scopeMap,
            Set<String> regionMethods) {
        JsonArray result = new JsonArray();
        Set<String> represented = new LinkedHashSet<>();
        // The frame the root-entry hooks are injected into.
        String planRootMethod = optionalString(object(goal.plan().json(),
                "rootSelector"), "method");
        for (JsonElement element : sourceActions) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject action = element.getAsJsonObject();
            JsonObject binding = action.deepCopy();
            String location = optionalString(action, "location");
            String cell = optionalString(action, "cell");
            if (!supportedSymbolicLeafType(action)) {
                addConcreteInputAction(result, represented, binding,
                        UNSUPPORTED_LEAF_TYPE);
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
                if (!FieldPathSpec.hasNonEmptyPaths(action, "fieldPaths")) {
                    addConcreteInputAction(result, represented, binding,
                            NO_BINDING_MODE);
                    continue;
                }
                binding.addProperty("bindingMode", "ROOT_ENTRY");
            } else if ("CALL_RETURN".equals(location)) {
                String returnCell = cell;
                String sourceKind = optionalString(action, "sourceKind");
                if (RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                        .equals(sourceKind)
                        || RuntimeSelectedRegionFinalizer.EXTERNAL_CALL_RETURN
                        .equals(sourceKind)) {
                    String callee = optionalString(action, "declaredCallee");
                    if (!callee.isEmpty()) returnCell = callee + ".return";
                }
                JsonArray sites = exactCallReturnSite(action,
                        scopeMap.rootSitesOf(returnCell, regionMethods));
                if (sites.size() == 0) {
                    addConcreteInputAction(result, represented, binding,
                            NO_BINDING_MODE);
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
                        NO_BINDING_MODE);
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

    /** The VM can present no symbol for this location, however declared. */
    static final String NO_BINDING_MODE = "NO_SYMBOLIC_BINDING_MODE";
    /** The SMT layer has no term for a value of this type. */
    static final String UNSUPPORTED_LEAF_TYPE =
            "UNSUPPORTED_SYMBOLIC_LEAF_TYPE";

    /**
     * Whether the SMT layer has a term for this value: a primitive, a
     * String, or an array of primitives.
     *
     * <p>A mechanism fact and the whole of what is left of the leaf
     * contract.  The four field-path spellings it used to check after this
     * -- ambiguous path, undeclared leaf, leaf name mismatch, leaf type
     * mismatch -- named four ways for one plan row to be malformed and
     * demoted a declared cell for each of them.</p>
     */
    private static boolean supportedSymbolicLeafType(JsonObject action) {
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                optionalString(action, "javaType"));
        if (descriptor.length() == 1 && "ZBCSIJFD".contains(descriptor)) {
            return true;
        }
        if ("Ljava/lang/String;".equals(descriptor)) {
            return true;
        }
        int component = 0;
        while (component < descriptor.length()
                && descriptor.charAt(component) == '[') {
            component++;
        }
        return component > 0 && component + 1 == descriptor.length()
                && "ZBCSIJFD".indexOf(descriptor.charAt(component)) >= 0;
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
        binding.addProperty("symbolicDemand", reason);
        addInputAction(result, represented, binding,
                InputActionCatalog.Mode.CONCRETE);
    }

    /** The static region schema version this build reads. */
    private static final int STATIC_REGION_SCHEMA_VERSION = 3;

    /**
     * The region ids of one campaign's port catalog.
     *
     * <p>Every row states the schema version it was written under and a row
     * stating another is refused rather than partly read.  This used to be a
     * {@code Region} class holding exactly that check and the id.</p>
     */
    private static Set<String> regionIndex(List<JsonObject> regions) {
        Set<String> index = new LinkedHashSet<>();
        for (JsonObject row : regions) {
            if (optionalInteger(row, "schemaVersion", -1)
                    != STATIC_REGION_SCHEMA_VERSION) {
                throw new IllegalArgumentException(
                        "symbolic region requires schemaVersion "
                                + STATIC_REGION_SCHEMA_VERSION);
            }
            String regionId = optionalString(row, "regionId");
            if (!regionId.isEmpty()) index.add(regionId);
        }
        return index;
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

    /**
     * The static candidate graph, which the scheduler reads for exactly one
     * thing: the exact-copy relation a declaration is renamed over.
     *
     * <p>It used to read the runtime-refined graph, for four things.  Three
     * of them were static facts of this same graph or of the static scope
     * map -- the declared cells' write sites, a root cell's definition
     * sites, and the guard-dependent cells of the deleted cost heuristic --
     * so PLAN no longer takes a runtime artifact for any of them.</p>
     */
    private static void requireCandidateGraph(List<JsonObject> rows) {
        if (rows.isEmpty()) {
            throw new IllegalArgumentException(
                    "candidate data-flow graph must not be empty");
        }
        for (JsonObject row : rows) {
            if (optionalInteger(row, "schemaVersion", -1) != 3) {
                throw new IllegalArgumentException(
                        "scheduler accepts only the schema-3 candidate graph");
            }
        }
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    private static final class Candidate {
        /**
         * Name order, not rank order.
         *
         * <p>It used to lead with "directed", then with the highest recorded
         * event sequence of the target branch -- an evidence ranking over
         * candidates, which is the offline path planning this file no longer
         * does.  One selection produces one candidate, so this is only a
         * stable order.</p>
         */
        private static final Comparator<Candidate> ORDER =
                Comparator.comparing((Candidate value) -> value.targetSiteId)
                        .thenComparing(value ->
                                value.goal.plan().occurrenceId())
                        .thenComparing(value -> value.goal.goalId());

        private final Goal goal;
        private final JsonArray branches;
        /** The branch event a target task must decide; "" for region path. */
        private final String targetSiteId;
        private final int targetOccurrence;
        private final boolean targetRequiredOutcome;
        private final JsonArray inputActions;
        private final String queryOccurrenceId;

        private Candidate(Goal goal, JsonArray branches,
                          String targetSiteId, int targetOccurrence,
                          boolean targetRequiredOutcome,
                          JsonArray inputActions,
                          String queryOccurrenceId) {
            this.goal = goal;
            this.branches = branches;
            this.targetSiteId = safe(targetSiteId);
            this.targetOccurrence = Math.max(1, targetOccurrence);
            this.targetRequiredOutcome = targetRequiredOutcome;
            this.inputActions = inputActions;
            this.queryOccurrenceId = firstNonBlank(
                    queryOccurrenceId,
                    goal.plan().occurrenceId());
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
            identity.append('\n').append(targetSiteId)
                    .append('\n').append(targetOccurrence)
                    .append('\n').append(targetRequiredOutcome);
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
                "cell", "declaredCallee", "definitionMethod",
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
                + ",candidateGraph=" + artifact(arguments.candidateGraph)
                + "}";
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


    /**
     * The experiment's declaration of which inputs are symbolic at all.
     *
     * <p>One decision per proposed input action, and one authority for it:
     * a symbol enters the run only where the campaign said so.  Four
     * declarations say so, and nothing else does.</p>
     *
     * <ul>
     *   <li>a cell, port or field signature this file names for the
     *   action's own region -- the case declaration.  It mints: the read
     *   is where the search starts;</li>
     *   <li>an {@code EXPLICIT_SYMBOLIC_FAULT} marker the workload wrote
     *   into its own program text, which is a declaration in the same
     *   sense.  It mints;</li>
     *   <li>a field a {@code CausynthSymbolicSource} hook site owns: the
     *   hook mints at its own call site, so the action itself stands
     *   down and stays concrete;</li>
     *   <li>a {@code COMMUNICATION_SITE_PORT} the communication catalog
     *   declared -- a wire attach point.  It is tracked and never mints:
     *   the value is produced on the other side and installed here.</li>
     * </ul>
     *
     * <p>Every other proposed read is concrete.  A read no declaration
     * names is not a carrier to be versioned: the expression a value
     * carries rides with the value in the VM, so a read that observes a
     * root-derived store gets that expression whether or not the plan
     * named the location, and a read that observes nothing symbolic has
     * nothing to publish.  Which branches the exploration flips is what
     * finds the relations; a region-entry symbol for an undeclared cell
     * only invents an input the case never declared.</p>
     *
     * <p>Which symbol reaches which read is decided at replay -- the VM's
     * propagated expression is the authority -- so no selector, selected
     * phase, producer version or output-version boundary is predicted
     * here.</p>
     */
    static final class SymbolicInputSelection {
        /** Verdict of a read no declaration names. */
        static final String UNDECLARED = "UNDECLARED_SYMBOLIC_INPUT";
        /** regionId -> the field signatures, port ids and cells it admits. */
        private final Map<String, Set<String>> admitted;
        /** The subset of {@link #admitted} the case declared to be clocks. */
        private final Map<String, Set<String>> clocks;
        /** regionId -> sourceId -> the one field that hook site mints. */
        private final Map<String, Map<String, String>> minted;
        private SymbolicInputSelection(
                Map<String, Set<String>> admitted,
                Map<String, Set<String>> clocks,
                Map<String, Map<String, String>> minted) {
            this.admitted = admitted;
            this.clocks = clocks;
            this.minted = minted;
        }

        /** One pass over the static hook declarations and, when the campaign
         *  configured one, over the declared field/port/cell rows. */
        static SymbolicInputSelection read(
                Path path, List<JsonObject> regionCatalog,
                List<RegionInstancePlan> regionPlans)
                throws IOException {
            Map<String, Map<String, String>> minted = new LinkedHashMap<>();
            Set<String> catalogRegions = new LinkedHashSet<>();
            // The declaration this plan was built under, published on the
            // region rows by the finalizer that honoured it: declared
            // method -> the regions it roots.  It is both halves of the
            // rule.  It resolves the declaration the way the rule states
            // it -- a declared method is a region root -- and a declared
            // method missing from it says the plan never saw the
            // declaration, which is a different fault from a site the
            // recording never entered, and nothing else can tell the two
            // apart.
            Map<String, Set<String>> declaredRootRegions =
                    new LinkedHashMap<>();
            for (JsonObject region : regionCatalog == null
                    ? Collections.<JsonObject>emptyList() : regionCatalog) {
                String regionId = optionalString(region, "regionId");
                if (!regionId.isEmpty()) catalogRegions.add(regionId);
                if (!regionId.isEmpty() && optionalBool(region,
                        DeclaredSymbolicInputs.ROOT_FIELD, false)) {
                    declaredRootRegions.computeIfAbsent(
                            optionalString(region, "rootMethod"),
                            ignored -> new LinkedHashSet<>()).add(regionId);
                }
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
            Map<String, Set<String>> clocks = new LinkedHashMap<>();
            if (path == null) {
                return new SymbolicInputSelection(admitted, clocks, minted);
            }
            requireFile(path, "symbolic input selection");
            for (JsonObject row : ArtifactIO.readJsonl(path)) {
                // A row that declares itself a clock declares every name on
                // it a clock: the case states which of its reads is a wall
                // clock, and the planner never decides that from a callee.
                // ONE statement, two spellings the file may use for it --
                // the cell form's `clock: true` and the callee form's
                // `kind: CLOCK` -- exactly as declaredMethod accepts a whole
                // signature or a class plus a method half.
                String callee = DeclaredSymbolicInputs.declaredCallee(row);
                boolean clock = optionalBool(
                        row, InputActionCatalog.DECLARED_WALL_CLOCK, false)
                        || DeclaredSymbolicInputs.CLOCK_KIND.equals(
                        firstNonBlank(optionalString(row, "kind")));
                for (String regionId : declaredRegions(row, catalogRegions,
                        regionPlans, declaredRootRegions)) {
                    Set<String> names = admitted.computeIfAbsent(regionId,
                            ignored -> new LinkedHashSet<>());
                    Set<String> clockNames = clock
                            ? clocks.computeIfAbsent(regionId,
                                    ignored -> new LinkedHashSet<>())
                            : null;
                    for (String field : new String[]{
                            "fieldSignatures", "portIds", "cells"}) {
                        addDeclaredNames(names, row, field);
                        if (clockNames != null) {
                            addDeclaredNames(clockNames, row, field);
                        }
                    }
                    // A callee declaration's name is its RETURN cell, which
                    // is the cell every external-call-return port of it
                    // carries: one name, so the admission test and the clock
                    // test are the same tests they were.
                    if (!callee.isEmpty()) {
                        String cell = DeclaredSymbolicInputs
                                .returnCell(callee);
                        names.add(cell);
                        if (clockNames != null) clockNames.add(cell);
                    }
                }
            }
            return new SymbolicInputSelection(admitted, clocks, minted);
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
         * <p>Resolution is the rule of {@link DeclaredSymbolicInputs}: a
         * declared method is a region root by declaration, so it names every
         * planned region it roots, and -- since a region opens on the anchor
         * the recording selected, which need not be the root -- every region
         * it anchors as well.  A site that matches several regions declares
         * the root in each of them: the same Java method planned on two
         * nodes is two regions and the declaration means both, unless it
         * scopes itself to a node or an epoch.  The region-id form is still
         * read.</p>
         *
         * <p>A site that matches nothing is a hard error naming the site.
         * Under the rule it can mean only one thing -- this plan was built
         * without the declaration -- because a declared root the recording
         * never entered is refused at aggregation, by name and with its
         * activation count.</p>
         */
        private static List<String> declaredRegions(
                JsonObject row, Set<String> catalogRegions,
                List<RegionInstancePlan> regionPlans,
                Map<String, Set<String>> declaredRootRegions)
                throws IOException {
            String regionId = firstNonBlank(optionalString(row, "regionId"));
            if (!regionId.isEmpty()) {
                if (!catalogRegions.contains(regionId)) {
                    throw new IOException("symbolic input selection names "
                            + "an unknown static region: " + regionId);
                }
                return Collections.singletonList(regionId);
            }
            String method = DeclaredSymbolicInputs.declaredMethod(row);
            if (method.isEmpty()) {
                // A CALLEE declaration names no site of its own: it is
                // about every call of that method in the application scope,
                // and WHICH regions actually call it is answered by the
                // port walk over the recording
                // (RuntimeSelectedRegionFinalizer
                // #semanticExternalCallReturnEdges), not here.  So it
                // admits its name in every planned region of its declared
                // scope, and a region that never calls the callee carries
                // the name and no port.
                if (!DeclaredSymbolicInputs.declaredCallee(row).isEmpty()) {
                    return everyPlannedRegion(row, catalogRegions,
                            regionPlans);
                }
                throw new IOException("symbolic input selection row declares "
                        + "neither a regionId nor a static site "
                        + "(class + method) nor a callee: " + row);
            }
            String node = firstNonBlank(optionalString(row, "node"));
            String epoch = firstNonBlank(optionalString(row, "epoch"));
            List<String> resolved = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();
            // The regions this method roots by declaration, plus the ones
            // it anchors.  Both are the same site seen from two sides: the
            // declaration names a method, the plan names each region's
            // anchor, and a declared root whose region opens on some other
            // anchor is still the region the declaration meant.
            Set<String> rooted = declaredRootRegions == null
                    ? Collections.<String>emptySet()
                    : declaredRootRegions.getOrDefault(method,
                    Collections.<String>emptySet());
            for (RegionInstancePlan plan : regionPlans == null
                    ? Collections.<RegionInstancePlan>emptyList()
                    : regionPlans) {
                boolean names = method.equals(optionalString(plan.json(),
                        "targetMethod")) || rooted.contains(plan.regionId());
                if (!names
                        || !scopeAdmits(plan.sourceKey(), node, epoch)
                        || !catalogRegions.contains(plan.regionId())) {
                    continue;
                }
                if (seen.add(plan.regionId())) resolved.add(plan.regionId());
            }
            if (resolved.isEmpty()) {
                // A declared method is a region root by declaration, and the
                // finalizer publishes one region row per honoured
                // declaration and refuses DECLARED_INPUT_NEVER_ACTIVATED for
                // a declared root the recording never entered.  So an empty
                // resolution here is not "the site is not causal": it is a
                // plan that was built without this declaration -- a stale
                // plan, or a PLAN stage the case file never reached -- and
                // saying so is the only way the reader knows to re-plan
                // rather than to edit the case.
                String scope = (node.isEmpty() ? "" : " on node " + node)
                        + (epoch.isEmpty() ? "" : " at epoch " + epoch);
                throw new IOException("DECLARED_INPUT_NOT_PLANNED: symbolic "
                        + "input selection names " + method + scope
                        + ", which this runtime region plan carries no "
                        + "region for; the plan honoured the declared "
                        + "roots " + declaredRootRegions.keySet() + ", so "
                        + "it was planned without this declaration and must "
                        + "be re-planned with it");
            }
            return resolved;
        }

        /**
         * Every planned region of one declaration's scope, for a callee.
         *
         * <p>Empty is legal and is not an error: a callee declaration that
         * resolves to no region says the plan retained none in that scope,
         * which the case's own target declaration already refuses if it
         * matters.  The method form's DECLARED_INPUT_NOT_PLANNED refusal is
         * about a SITE the plan must carry a region for, and a callee names
         * no site.</p>
         */
        private static List<String> everyPlannedRegion(
                JsonObject row, Set<String> catalogRegions,
                List<RegionInstancePlan> regionPlans) {
            String node = firstNonBlank(optionalString(row, "node"));
            String epoch = firstNonBlank(optionalString(row, "epoch"));
            List<String> resolved = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();
            for (RegionInstancePlan plan : regionPlans == null
                    ? Collections.<RegionInstancePlan>emptyList()
                    : regionPlans) {
                if (!scopeAdmits(plan.sourceKey(), node, epoch)
                        || !catalogRegions.contains(plan.regionId())) {
                    continue;
                }
                if (seen.add(plan.regionId())) resolved.add(plan.regionId());
            }
            return resolved;
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
         * Resolves every declared name onto the cells it is a proven exact
         * copy of.  Called once, before any {@code select}, so every region
         * decides against the same declarations.
         */
        void resolveDeclaredNames(List<JsonObject> candidateGraph) {
            renameDeclaredNames(candidateGraph);
        }

        JsonArray select(String regionId, JsonArray actions) {
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
         * Stamps one proposed input with the verdict of its declaration.
         *
         * <p>Four declarations make a read symbolic and nothing else does,
         * so there is no third state between "declared" and "concrete": a
         * read the campaign never named publishes no port, mints no
         * symbol and opens no version log of its own.</p>
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
                return;
            }
            boolean declared = admits(regionId, action);
            // The workload wrote this symbol into its own program text; that
            // is a declaration in the same sense a hook call is one.
            boolean workloadOwned = workloadOwnedSymbol(action);
            if (!declared && !workloadOwned) {
                // No declaration names this read, so it is not an input of
                // this campaign.  It observes whatever the run put in the
                // location, and the expression of a root-derived store
                // rides with that value inside the VM: a plan-side port
                // here would invent a symbol the case never declared, and
                // its region-entry mint would hide the real writer behind
                // a fresh root.
                retained.addProperty("mode", "CONCRETE");
                retained.addProperty("symbolicDemand", UNDECLARED);
                return;
            }
            if (declared) {
                // Named by hand: the replay mints here, which is what
                // "the search starts at this cell" means.
                retained.addProperty(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT, true);
                if (names(clocks, regionId, action)) {
                    retained.addProperty(
                            InputActionCatalog.DECLARED_WALL_CLOCK, true);
                }
            }
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

        /**
         * Whether one region admits one proposed action.
         *
         * <p>A declaration names the action's port or one of its dataflow
         * cells, and {@link ConcolicScheduler#actionCells} is already the
         * one answer to "which cells does this action name": the read's own
         * location <em>and</em> the local the value lands in, which is the
         * only cell an accessor read shares with the graph.  Asking the
         * narrower question here -- the access signature, the port, the
         * cell -- is what refused hdfs-17960's declared region input, whose
         * port names the {@code AtomicInteger.value} leaf while the case
         * names the accessor's return.</p>
         */
        private boolean admits(String regionId, JsonObject action) {
            return names(admitted, regionId, action);
        }

        /** Whether one declared name set covers this action's port or cells. */
        private static boolean names(Map<String, Set<String>> declared,
                                     String regionId, JsonObject action) {
            Set<String> names = declared.get(safe(regionId));
            if (names == null || names.isEmpty()) return false;
            if (names.contains(actionPort(action))) return true;
            for (String cell : actionCells(action)) {
                if (names.contains(cell)) return true;
            }
            return false;
        }

        /** Soot's own proofs that one dataflow edge is a pure rename. */
        private static final Set<String> EXACT_VALUE_COPY_AUTHORITIES =
                Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                        "SOOT_EXACT_LOCAL_DIRECT_COPY_V1",
                        "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1")));

        /**
         * Adds to every declared name the cells it is a proven exact copy of.
         *
         * <p>A declaration names a <em>value</em>; the graph names the same
         * value once per Jimple local it is copied into, and a method's
         * {@code .return} cell is one of those names -- the return statement
         * is a rename of the local it returns.  Soot proves which edges are
         * exact JVM value copies and stamps {@code valueFlowAuthority} on
         * them, so walking <em>only</em> those edges backwards renames the
         * declaration without inferring any dataflow: nothing upstream of
         * the copy chain is reached, so an upstream carrier never becomes a
         * declared root.</p>
         *
         * <p>This is what lets hdfs-17960 declare
         * {@code <SnapshotManager: int getNumSnapshots()>.return} and select
         * the accessor-return port that already names
         * {@code <SnapshotManager: int getNumSnapshots()>::$i0} in its
         * {@code dependencyCells}.  Idempotent, and a graph with no such
         * edge leaves every declaration exactly as the case wrote it.</p>
         */
        private void renameDeclaredNames(List<JsonObject> candidateGraph) {
            if (admitted.isEmpty()) return;
            // Both name sets are renamed: a declared clock cell and the
            // exact copies of it are the same read under different Jimple
            // names, so the flag travels with the declaration.

            Map<String, Set<String>> copies = new LinkedHashMap<>();
            for (JsonObject edge : candidateGraph == null
                    ? Collections.<JsonObject>emptyList() : candidateGraph) {
                if (!EXACT_VALUE_COPY_AUTHORITIES.contains(
                        optionalString(edge, "valueFlowAuthority"))) {
                    continue;
                }
                String from = optionalString(edge, "fromCell");
                String to = optionalString(edge, "toCell");
                if (from.isEmpty() || to.isEmpty()) continue;
                copies.computeIfAbsent(to,
                        ignored -> new LinkedHashSet<>()).add(from);
            }
            if (copies.isEmpty()) return;
            for (Map<String, Set<String>> declared
                    : Arrays.asList(admitted, clocks)) {
                for (Set<String> names : declared.values()) {
                    Set<String> renamed = new LinkedHashSet<>(names);
                    Deque<String> pending = new ArrayDeque<>(names);
                    while (!pending.isEmpty()) {
                        for (String copied : copies.getOrDefault(
                                pending.removeFirst(),
                                Collections.<String>emptySet())) {
                            if (renamed.add(copied)) pending.addLast(copied);
                        }
                    }
                    names.addAll(renamed);
                }
            }
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
        private final Set<String> regionIndex;
        private final List<JsonObject> candidateGraph;
        private final StaticScopeMap staticScopeMap;
        private final JsonObject regionPlanIdentity;
        private final JsonObject candidateGraphIdentity;
        private final JsonObject symbolicInputsIdentity;
        private final SymbolicInputSelection symbolicInputs;

        private LoadedInputs(List<RegionInstancePlan> regionPlans,

                             Set<String> regionIndex,
                             List<JsonObject> candidateGraph,
                             StaticScopeMap staticScopeMap,
                             JsonObject regionPlanIdentity,
                             JsonObject candidateGraphIdentity,
                             JsonObject symbolicInputsIdentity,
                             SymbolicInputSelection symbolicInputs) {
            this.regionPlans = regionPlans;
            this.regionIndex = regionIndex;
            this.candidateGraph = candidateGraph;
            this.staticScopeMap = staticScopeMap;
            this.regionPlanIdentity = regionPlanIdentity;
            this.candidateGraphIdentity = candidateGraphIdentity;
            this.symbolicInputsIdentity = symbolicInputsIdentity;
            this.symbolicInputs = symbolicInputs;
        }
    }

    /**
     * Which closure the schedule is drawn from.  It names the scope once, so
     * two independent flags cannot contradict each other; it is read by
     * {@link #withSeedReplayGroup}, which is the one thing the seed replay
     * does differently.
     */
    public enum ClosureMode {
        /** Every candidate occurrence the frozen region plan declares. */
        CANDIDATE("candidate"),
        /** Only the occurrences a seed activation can replay. */
        SEED_REPLAY("seed-replay");

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
            throw new IllegalArgumentException("--closure-mode must be "
                    + "candidate or seed-replay, not: " + requested);
        }
    }

    /**
     * Every region a previous epoch's divergence said the retained set must
     * grow to include (INTERACTION-ID section 8, case 2).
     *
     * <p>A flipped path reached a region the workload never retained -- only
     * lightweight entry hooks ran there, so it published activations and no
     * decisions.  The next epoch has to instrument it, and INSTRUMENT
     * instruments the regions this plan names, so the plan has to name it.
     * If no candidate of this recording carries the region, the epoch cannot
     * grow the way the divergence asked and says so here rather than
     * instrumenting the same set again and diverging identically.</p>
     */
    private static void requireRetainedRegions(
            java.util.Set<String> required,
            RuntimeWorkflowDiscovery.RankedWorkflow workflow) {
        if (required.isEmpty()) return;
        java.util.Set<String> planned = new LinkedHashSet<>();
        for (RuntimeWorkflowDiscovery.Selection selection
                : workflow.selections()) {
            planned.add(selection.regionId);
        }
        List<String> missing = new ArrayList<>();
        for (String regionId : required) {
            if (!planned.contains(regionId)) missing.add(regionId);
        }
        if (!missing.isEmpty()) {
            throw new IllegalArgumentException(
                    "RETAINED_SET_CANNOT_GROW: this epoch was asked to retain "
                            + missing + ", and no candidate of this recording"
                            + " carries them; instrumenting the same set again"
                            + " would diverge identically");
        }
    }

    public static final class Arguments {
        public final Path regionPlan;
        public final Path candidateGraph;
        /** The static scope map: the one guard authority's publication. */
        public final Path staticScopeMap;
        public final Path outputDirectory;
        public final String regionId;
        public final String occurrenceId;
        public final String goalId;
        public final int maxJobs;
        public final Path symbolicInputs;
        /** The occurrence of the annotated site the case declares, or "". */
        public final String targetOccurrence;
        /** Regions a previous epoch's divergence requires this plan to keep. */
        public final java.util.Set<String> retainRegions;
        private final ClosureMode closureMode;

        private Arguments(Path regionPlan, Path candidateGraph,
                          Path staticScopeMap,
                          Path outputDirectory, String regionId,
                          String occurrenceId, String goalId,
                          int maxJobs,
                          Path symbolicInputs, ClosureMode closureMode,
                          String targetOccurrence,
                          java.util.Set<String> retainRegions) {
            this.retainRegions = retainRegions == null
                    ? java.util.Collections.<String>emptySet()
                    : java.util.Collections.unmodifiableSet(
                            new LinkedHashSet<>(retainRegions));
            this.regionPlan = regionPlan;
            this.candidateGraph = candidateGraph;
            this.staticScopeMap = staticScopeMap;
            this.outputDirectory = outputDirectory;
            this.regionId = safe(regionId);
            this.occurrenceId = safe(occurrenceId);
            this.goalId = safe(goalId);
            this.maxJobs = Math.max(1, maxJobs);
            this.symbolicInputs = symbolicInputs;
            this.closureMode = closureMode;
            this.targetOccurrence = safe(targetOccurrence);
        }

        public static Arguments parse(String[] args) {
            // "retain-regions" was missing from this list while
            // run_engine.sh passed it on every epoch after the first, so the
            // scheduler died with "Unknown scheduler option
            // --retain-regions" the moment a divergence asked for a grown
            // retained set.  Every option the shell passes is declared here.
            Map<String, String> values = parseArgs(args, "region-plan",
                    "candidate-graph", "static-scope-map", "output-dir",
                    "max-jobs", "symbolic-inputs", "retain-regions",
                    "closure-mode", "target-occurrence");
            Path regionPlan = requiredPath(values, "region-plan");
            Path output = Paths.get(firstNonBlank(values.get("output-dir"),
                    ArtifactIO.sibling(regionPlan,
                            "concolic-schedule").toString()));
            Path candidateGraph = requiredPath(values, "candidate-graph");
            Path staticScopeMap = requiredPath(values, "static-scope-map");
            Path symbolicInputs = optionalPath(
                    values.get("symbolic-inputs"));
            ClosureMode closureMode = ClosureMode.parse(
                    values.get("closure-mode"));
            return new Arguments(regionPlan, candidateGraph, staticScopeMap,
                    output, "", "", "",
                    parseInt(values.get("max-jobs"), 1),
                    symbolicInputs, closureMode,
                    values.get("target-occurrence"),
                    splitRegions(values.get("retain-regions")));
        }

        /** {@code --retain-regions a,b,c}, or an empty set. */
        private static java.util.Set<String> splitRegions(String value) {
            java.util.Set<String> regions = new LinkedHashSet<>();
            for (String part : (value == null ? "" : value).split(",")) {
                String regionId = part.trim();
                if (!regionId.isEmpty()) regions.add(regionId);
            }
            return regions;
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
            return new Arguments(regionPlan, candidateGraph, staticScopeMap,
                    outputDirectory,
                    selection.regionId, selection.occurrenceId,
                    selection.goalId, 1,
                    symbolicInputs, closureMode, targetOccurrence,
                    retainRegions);
        }

    }
}
