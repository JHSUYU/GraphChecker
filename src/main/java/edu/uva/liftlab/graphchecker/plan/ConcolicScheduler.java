package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.plan.RegionInstancePlan.Goal;

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
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.strings;

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
        Set<String> regionIndex = regionIndex(regions);
        StaticScopeMap staticScopeMap = StaticScopeMap.read(
                arguments.staticScopeMap);
        if (!staticScopeMap.stated()) {
            throw new IOException("static scope map states no site: "
                    + arguments.staticScopeMap);
        }
        SymbolicInputSelection symbolicInputs =
                SymbolicInputSelection.read(staticScopeMap, regions);
        // These identities are re-verified when the schedule index commits.
        return new LoadedInputs(regionPlans, regionIndex,
                candidateGraph, staticScopeMap,
                regionPlanIdentity, candidateGraphIdentity, symbolicInputs);
    }

    private static List<ExecutionTask> scheduleLoaded(
            Arguments arguments, LoadedInputs loaded)
            throws IOException {
        // Resolve declared names over Soot's exact-copy edges before any region
        // selects.
        loaded.symbolicInputs.resolveDeclaredNames(loaded.candidateGraph);
        List<Candidate> candidates = candidates(arguments,
                loaded.regionPlans, loaded.regionIndex,
                loaded.staticScopeMap, loaded.symbolicInputs);
        Collections.sort(candidates, Candidate.ORDER);

        LoopBoundPolicy loopBound = declaredLoopBounds(
                LoopBoundPolicy.declaredDefault(), loaded.regionPlans);
        List<ExecutionTask> result = new ArrayList<>();
        for (Candidate candidate : candidates) {
            if (result.size() >= arguments.maxJobs) {
                throw overMaxJobs(candidates.size(), arguments.maxJobs,
                        loaded.regionPlans);
            }
            ExecutionTask scheduled = task(candidate,
                    branchMethods(candidate.branches), loopBound,
                    loaded.symbolicInputs);
            // json() is the live row (PlanRow): the scheduler annotates its own
            // new task.
            JsonObject executionTask = scheduled.json();
            if (candidate.goal.kind().capturesTargetReach()) {
                // The branch event this occurrence must decide and phi's fatal
                // arm, from the TARGET_SITE guards, so no later stage
                // re-derives it.
                JsonObject target = new JsonObject();
                target.addProperty("siteId", candidate.targetSiteId);
                target.addProperty("occurrence",
                        candidate.targetOccurrence);
                target.addProperty("requiredOutcome",
                        candidate.targetRequiredOutcome);
                if (!candidate.targetDeciders.isEmpty()) {
                    target.add("decidedBy", StaticScopeMap.guardsJson(
                            candidate.targetDeciders));
                }
                if (!candidate.targetGuards.isEmpty()) {
                    JsonArray guards = new JsonArray();
                    for (StaticScopeMap.Guard guard : candidate.targetGuards) {
                        JsonObject row = new JsonObject();
                        row.addProperty("siteId", guard.siteId());
                        row.addProperty("requiredOutcome", guard.outcome());
                        guards.add(row);
                    }
                    target.add("guards", guards);
                }
                executionTask.add("targetBranch", target);
            }

            result.add(scheduled);
        }
        // Accesses of tracked cells the replay must observe: campaign-wide,
        // on every task, since whichever occurrence reaches a cell first
        // starts its log.
        JsonArray observed = loaded.staticScopeMap.observedSites();
        if (observed.size() > 0) {
            for (ExecutionTask task : result) {
                task.json().add(ExecutionTask.OBSERVED_SITES,
                        observed.deepCopy());
            }
        }
        return result;
    }

    /** A region-path task with caller-stated inputs, for an exposed occurrence
     *  ({@code ExposedRegionPlanMain}). */
    static ExecutionTask regionPathTask(
            Goal goal, JsonArray inputActions, JsonArray branchMethods,
            LoopBoundPolicy loopBound, SymbolicInputSelection symbolicInputs) {
        return task(new Candidate(goal, new JsonArray(), "", 1, false,
                inputActions), branchMethods, loopBound, symbolicInputs);
    }

    /** One candidate's task: its declared inputs, its identity, its row. */
    private static ExecutionTask task(
            Candidate candidate, JsonArray branchMethods,
            LoopBoundPolicy loopBound, SymbolicInputSelection symbolicInputs) {
        RegionInstancePlan plan = candidate.goal.plan();
        JsonArray selected = symbolicInputs.select(plan.regionId(),
                candidate.inputActions);
        selected = removeInboundProtocolHandoffInputs(selected,
                CommunicationHandoffSpec.decode(plan.json()));
        ExecutionTask task = ExecutionTask.create(candidate.goal,
                candidate.seedTaskId(selected), selected, branchMethods,
                loopBound);
        List<String> regions = new ArrayList<>(strings(plan.json(),
                RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS));
        regions.add(plan.regionId());
        if (symbolicInputs.readsTrackedState(regions)) {
            task.json().addProperty(ExecutionTask.READS_TRACKED_STATE, true);
        }
        return task;
    }

    /** The ONE cap rule's refusal: not even the target's own demand level
     *  fits {@code --max-jobs} ({@link RuntimeWorkflowDiscovery.Workflow
     *  #nearest} keeps the nearest levels that fit whole and names the
     *  rest), refused by name with its admission summary. */
    private static IOException overMaxJobs(
            int selected, int maxJobs, List<RegionInstancePlan> regionPlans) {
        return new IOException("selected exact closure exceeds max jobs: "
                + selected + " > " + maxJobs + "; "
                + closureAdmissionSummary(regionPlans));
    }

    /** Drops local SYMBOLIC actions for ports this occurrence attaches
     *  (declared IN handoffs): the VM handoff supplies that value, and a local
     *  action would mint a second root before attach. */
    private static JsonArray removeInboundProtocolHandoffInputs(
            JsonArray actions,
            List<CommunicationHandoffSpec> declaredHandoffs) {
        Set<String> suppliedPorts = new LinkedHashSet<>();
        for (CommunicationHandoffSpec handoff : declaredHandoffs) {
            if (!handoff.outgoing()) suppliedPorts.add(handoff.portId());
        }
        JsonArray retained = new JsonArray();
        for (JsonElement element : actions) {
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

    /** Methods whose branches the weave covers (INSTRUMENT weaves every branch
     *  of a method). */
    private static JsonArray branchMethods(JsonArray branches) {
        TreeSet<String> methods = new TreeSet<>();
        for (JsonElement element : branches) {
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
     * Every test of the guard {@code site} belongs to, as its TARGET_SITE row
     * states it, when there are several: a replay may reach the throw
     * through a disjunct the recording never evaluated.  SOLR-18406's
     * {@code (commit != null && commit.isDeleted()) || (commit == null &&
     * generation < latest)} was recorded on the first; the flipped replay
     * threw through the second, and a plan naming only the recorded test
     * stated that occurrence as never reaching its anchor.
     */
    static List<StaticScopeMap.Guard> targetGuards(StaticScopeMap map,
                                                   String site) {
        List<StaticScopeMap.Guard> guards = new ArrayList<>();
        for (StaticScopeMap.Site target : map.targetSites()) {
            if (target.guards.size() < 2 || !target.guards.contains(site)) {
                continue;
            }
            for (String guard : target.guards) {
                guards.add(new StaticScopeMap.Guard(guard,
                        map.fatalArm(guard)));
            }
            return guards;
        }
        return guards;
    }

    /** The helper branch arms deciding the target guard {@code
     *  guardSiteId}, as the TARGET_SITE rows state them; empty for none. */
    static List<StaticScopeMap.Guard> fatalDeciders(StaticScopeMap map,
                                                    String guardSiteId) {
        for (StaticScopeMap.Site target : map.targetSites()) {
            List<StaticScopeMap.Guard> deciders =
                    target.guardDeciders.get(guardSiteId);
            if (deciders != null) return deciders;
        }
        return Collections.<StaticScopeMap.Guard>emptyList();
    }

    private static void scheduleTargetFirst(Arguments arguments)
            throws IOException {
        LoadedInputs loaded = loadInputs(arguments);
        RuntimeWorkflowDiscovery.Workflow closure =
                RuntimeWorkflowDiscovery.workflow(loaded.regionPlans,
                        arguments.targetOccurrence);
        RuntimeWorkflowDiscovery.Workflow workflow =
                closure.nearest(arguments.maxJobs);
        Map<String, Map<String, Integer>> notCrossed =
                new LinkedHashMap<>();
        for (String[] member : WRITERS_NOT_CROSSED) {
            Map<String, Integer> fields = writersNotCrossed(
                    loaded.regionPlans, member[1]);
            if (fields.isEmpty()) continue;
            notCrossed.put(member[1], fields);
            System.err.println(member[0] + " " + member[2] + ": by owner"
                    + " class " + byOwnerClass(fields) + ", by field "
                    + fields);
        }
        if (workflow == null) {
            throw overMaxJobs(closure.scheduledTaskCount(),
                    arguments.maxJobs, loaded.regionPlans);
        }
        if (workflow.cutCount() > 0) {
            System.err.println("closure cut at demand depth "
                    + workflow.keptDepth() + ": " + workflow.cutCount()
                    + " of " + closure.scheduledTaskCount()
                    + " occurrences not planned (max jobs "
                    + arguments.maxJobs + "); "
                    + closureAdmissionSummary(loaded.regionPlans));
        } else {
            String classes = deciderClasses(loaded.regionPlans);
            if (!classes.isEmpty()) System.err.println(classes.trim());
        }

        List<List<ExecutionTask>> scheduled = scheduleSelections(arguments,
                loaded, workflow);

        Map<String, ExecutionTask> tasks = new LinkedHashMap<>();
        for (int index = 0; index < scheduled.size(); index++) {
            RuntimeWorkflowDiscovery.Selection selection =
                    workflow.selections().get(index);
            List<ExecutionTask> selected = scheduled.get(index);
            if (selected.size() != 1) {
                throw new IOException("target-first selection emitted "
                        + selected.size() + " execution tasks; campaign="
                        + selection.campaignId);
            }
            ExecutionTask task = selected.get(0);
            ExecutionTask prior = tasks.putIfAbsent(task.taskId(), task);
            if (prior != null && !prior.json().equals(task.json())) {
                throw new IOException("conflicting scheduled taskId: "
                        + task.taskId());
            }
        }
        List<ExecutionTask> result = sortedValues(tasks);
        Path taskPlan = arguments.outputDirectory.resolve(
                "execution_task_plan.jsonl");
        List<JsonObject> taskRows = new ArrayList<>();
        for (ExecutionTask task : result) {
            taskRows.add(task.json());
        }
        ArtifactIO.replaceJsonl(taskPlan, withSeedReplayGroup(taskRows));
        JsonObject taskPlanIdentity = artifactIdentity(taskPlan);
        JsonObject index = workflow.scheduleIndex(result,
                loaded.regionPlanIdentity, taskPlanIdentity);
        for (Map.Entry<String, Map<String, Integer>> member
                : notCrossed.entrySet()) {
            stateWritersNotCrossed(index, member.getKey(), member.getValue());
        }
        requireArtifactIdentity(arguments.regionPlan,
                loaded.regionPlanIdentity,
                "region plan changed while scheduling");
        requireArtifactIdentity(arguments.candidateGraph,
                loaded.candidateGraphIdentity,
                "candidate data-flow graph changed while scheduling");
        requireArtifactIdentity(taskPlan, taskPlanIdentity,
                "execution task plan changed before index publication");
        // The integrity-checked index is the commit record.
        ArtifactIO.replace(arguments.outputDirectory.resolve(
                        "runtime_workflow_schedule_index.json"),
                CanonicalJson.render(index) + "\n");
        if (result.isEmpty()) {
            throw new IllegalStateException(noCandidateDiagnostic(
                    arguments, loaded.regionPlans));
        }
    }

    private static List<List<ExecutionTask>> scheduleSelections(
            Arguments arguments, LoadedInputs loaded,
            RuntimeWorkflowDiscovery.Workflow workflow)
            throws IOException {
        List<List<ExecutionTask>> result = new ArrayList<>();
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

    /** The member every task row names its replay ledger by. */
    static final String REPLAY_GROUP_ID = "replayGroupId";

    /** Stamps the replay ledger id: a hash of the plan, so the same tasks are
     *  the same ledger across iterations; flip replays link the same plan and
     *  group. */
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
            stamped.addProperty(REPLAY_GROUP_ID, groupId);
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
                                              StaticScopeMap scopeMap,
                                              SymbolicInputSelection
                                                      symbolicInputs)
            throws IOException {
        List<Candidate> result = new ArrayList<>();
        for (RegionInstancePlan plan : regionPlans) {
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
            Goal goal = plan.goal();
            if (!arguments.goalId.isEmpty()
                    && !arguments.goalId.equals(goal.goalId())) {
                continue;
            }
            if (!goal.replayable()) {
                continue;
            }
            appendGoalCandidates(arguments, result, goal, scopeMap,
                    symbolicInputs);
        }
        return result;
    }

    /** Per-loop {@code K_L} the plan declares; kept even when equal to the
     *  inherited bound. */
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

    /** The one candidate of one replayable goal. A target-reach goal also names
     *  the branch it must decide: the recorded guard of the declared throw, on
     *  the arm that reaches it. No path search, ranking or election here. */
    private static void appendGoalCandidates(
            Arguments arguments, List<Candidate> result, Goal goal,
            StaticScopeMap scopeMap, SymbolicInputSelection symbolicInputs)
            throws IOException {
        Set<String> definitionMethods = goal.runtimeDefinitionMethods();
        JsonArray branches = goal.branches();
        JsonArray inputActions = materializationPlan(goal,
                withDeclaredPorts(goal.symbolize(),
                        symbolicInputs.declaredPorts(goal.plan(), scopeMap,
                                definitionMethods)),
                scopeMap, definitionMethods);
        if (goal.kind().capturesRegionPath()) {
            result.add(new Candidate(goal, branches, "", 1, false,
                    inputActions));
            return;
        }
        requireSelectedOccurrence(arguments, goal);
        JsonObject fatal = fatalBranch(branches, scopeMap);
        String site = optionalString(fatal, "siteId");
        List<StaticScopeMap.Guard> guards = targetGuards(scopeMap, site);
        result.add(new Candidate(goal, branches, site,
                optionalInteger(fatal, "selectedOccurrence", 1),
                scopeMap.fatalArm(site).booleanValue(),
                guards.isEmpty() ? fatalDeciders(scopeMap, site)
                        : Collections.<StaticScopeMap.Guard>emptyList(),
                guards, inputActions));
    }

    /**
     * The recorded branch where the target stands: of the ones the scope map
     * names as guards of the declared throw, the first in unit order -- one
     * for a conjunction ({@code a && b} jumps to the throw from its last
     * test only), the first test the recording evaluated of a disjunction
     * ({@code a || b} jumps to it from each; {@link #targetGuards} names
     * them all).  None, or guards of two throws, is a named refusal.
     */
    private static JsonObject fatalBranch(JsonArray branches,
                                          StaticScopeMap scopeMap)
            throws IOException {
        // An occurrence whose path left before the throw -- it took a chain
        // decision and no deciding guard (StaticScopeMap.Site#chain) --
        // stands at the deciding guard it never reached.
        boolean reached = false;
        boolean left = false;
        Set<String> chain = new LinkedHashSet<>();
        for (StaticScopeMap.Site target : scopeMap.targetSites()) {
            chain.addAll(target.pathSites());
            chain.removeAll(target.guards);
        }
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (!optionalBool(branch, "observed", false)) continue;
            String siteId = optionalString(branch, "siteId");
            reached |= scopeMap.fatalArm(siteId) != null;
            left |= chain.contains(siteId);
        }
        boolean unreached = !reached && left;
        Map<String, JsonObject> bySite = new LinkedHashMap<>();
        Set<String> guardedTargets = new LinkedHashSet<>();
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            String siteId = optionalString(branch, "siteId");
            if (!optionalBool(branch, "failureTarget", false)
                    || !(unreached || optionalBool(branch, "observed", false))
                    || scopeMap.fatalArm(siteId) == null) {
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
        if (bySite.isEmpty() || guardedTargets.size() > 1) {
            throw new IOException("UNSUPPORTED_AMBIGUOUS_TARGET_PATH: "
                    + "expected one guarded failure target and a guard of "
                    + "it; found " + guardedTargets.size()
                    + " guarded failure target(s) and " + bySite.size()
                    + " guard(s) the static scope map names: "
                    + bySite.keySet());
        }
        // The first test the recording evaluated is where the target stands.
        return Collections.min(bySite.values(), Comparator.comparingInt(
                branch -> SiteId.unitIndexOf(optionalString(branch,
                        "siteId"))));
    }

    /** A target goal is the occurrence the arguments selected, if any. */
    private static void requireSelectedOccurrence(Arguments arguments,
                                                  Goal goal) {
        if (!arguments.occurrenceId.isEmpty()
                && !arguments.occurrenceId.equals(
                goal.plan().occurrenceId())) {
            throw new IllegalArgumentException(
                    "target goal does not match selected occurrence "
                            + arguments.occurrenceId);
        }
    }

    /** Proposed inputs with the minted declared ports: a minted port replaces
     *  the region row's port of the same symbol (same port, built from the
     *  publishing artifacts), and is appended otherwise. */
    static JsonArray withDeclaredPorts(JsonArray proposed, JsonArray minted) {
        if (minted.size() == 0) return proposed;
        Map<String, JsonObject> bySymbol = new LinkedHashMap<>();
        for (JsonElement element : minted) {
            JsonObject port = element.getAsJsonObject();
            bySymbol.put(optionalString(port, "symbol"), port);
        }
        JsonArray result = new JsonArray();
        for (JsonElement element : proposed) {
            if (!element.isJsonObject()) {
                result.add(element);
                continue;
            }
            JsonObject action = element.getAsJsonObject();
            JsonObject port = bySymbol.remove(
                    optionalString(action, "symbol"));
            result.add(port == null ? action : port);
        }
        for (JsonObject port : bySymbol.values()) result.add(port);
        return result;
    }

    /**
     * The binding mode of each proposed input, or why the VM cannot present it.
     *
     * <p>No admission here: {@code SymbolicInputSelection.decide} is the ONE
     * rule. Trap: a refusal taxonomy in front of it would drop DECLARED cells
     * before the rule sees them. The only refusals are mechanism facts: no VM
     * presentation, or no SMT term for the type.</p>
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
                    // Argument of a non-root frame: the root-entry hook matches
                    // by position at the root only (a server fragment's root
                    // has no arguments).
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
    private static final String NO_BINDING_MODE = "NO_SYMBOLIC_BINDING_MODE";
    /** The SMT layer has no term for a value of this type. */
    private static final String UNSUPPORTED_LEAF_TYPE =
            "UNSUPPORTED_SYMBOLIC_LEAF_TYPE";

    /** Whether the SMT layer has a term for this value: primitive, String, or
     *  primitive array. */
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

    private static JsonArray exactCallReturnSite(
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
    private static void addConcreteInputAction(
            JsonArray result, Set<String> represented,
            JsonObject binding, String reason) {
        binding.addProperty("symbolicDemand", reason);
        addInputAction(result, represented, binding,
                InputActionCatalog.Mode.CONCRETE);
    }

    /** The static region schema version this build reads. */
    private static final int STATIC_REGION_SCHEMA_VERSION = 3;

    /** Region ids of the port catalog; a row of another schema version is
     *  refused. */
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

    /** The one option scan: {@code --key value}, bare {@code --flag} = "true",
     *  no unknown key. */
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

    /** One required path option; missing is refused by name. */
    static Path requiredPath(Map<String, String> values, String key) {
        String value = values.get(key);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException("Missing --" + key);
        }
        return Paths.get(value);
    }

    private static void requireFile(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

    /** The static candidate graph, read only for the exact-copy relation
     *  declarations are renamed over. */
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

    private static final class Candidate {
        /** Name order for stability only; never a rank (one selection, one
         *  candidate). */
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
        /** The helper branch arms that decide the target branch, each with
         *  its own (causynth.BooleanReturns); empty for none. */
        private final List<StaticScopeMap.Guard> targetDeciders;
        /** Every test of a disjunctive guard with its fatal arm, first the
         *  target branch; empty for one guard. */
        private final List<StaticScopeMap.Guard> targetGuards;
        private final JsonArray inputActions;

        private Candidate(Goal goal, JsonArray branches,
                          String targetSiteId, int targetOccurrence,
                          boolean targetRequiredOutcome,
                          JsonArray inputActions) {
            this(goal, branches, targetSiteId, targetOccurrence,
                    targetRequiredOutcome,
                    Collections.<StaticScopeMap.Guard>emptyList(),
                    Collections.<StaticScopeMap.Guard>emptyList(),
                    inputActions);
        }

        private Candidate(Goal goal, JsonArray branches,
                          String targetSiteId, int targetOccurrence,
                          boolean targetRequiredOutcome,
                          List<StaticScopeMap.Guard> targetDeciders,
                          List<StaticScopeMap.Guard> targetGuards,
                          JsonArray inputActions) {
            this.goal = goal;
            this.targetDeciders = targetDeciders;
            this.targetGuards = targetGuards;
            this.branches = branches;
            this.targetSiteId = nonNull(targetSiteId);
            this.targetOccurrence = Math.max(1, targetOccurrence);
            this.targetRequiredOutcome = targetRequiredOutcome;
            this.inputActions = inputActions;
        }

        /** Stable task identity: occurrence x region content x port set (x
         *  target for reach goals). */
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
            TreeSet<String> methods = new TreeSet<>(
                    goal.runtimeDefinitionMethods());
            TreeSet<String> sites = new TreeSet<>();
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                String site = optionalString(element.getAsJsonObject(), "siteId");
                if (!site.isEmpty()) sites.add(site);
            }
            return ArtifactIO.sha256(String.join("\n", methods)
                    + "\n--BRANCH-SITES--\n" + String.join("\n", sites));
        }

        /** Ordinal-free descriptors of the local symbolic roots. */
        private String portSetHash(JsonArray taskInputActions) {
            TreeSet<String> descriptors = new TreeSet<>();
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

    /** How an over-sized closure's rows were admitted (by basis, depth, top
     *  anchors), for the cap refusal. */
    private static String closureAdmissionSummary(List<RegionInstancePlan> rows) {
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
        return summary.append(']').append(deciderClasses(rows)).toString();
    }

    /**
     * The writers a reader that never touched a field was not crossed to,
     * and those it was crossed to only for a mention: the log's name, the
     * plan row's and index's member, what it means
     * ({@code RuntimeSelectedRegionFinalizer}'s {@code DemandWalk
     * #holdsOthersOnly}).
     */
    private static final String[][] WRITERS_NOT_CROSSED = {
        {"CONFINED", RuntimeSelectedRegionFinalizer.CONFINED_WRITERS,
            "writers not crossed to, every object they wrote the field on,"
                + " with its recorded holders, mentioned by their own"
                + " occurrence alone, the reader not inside it"},
        {"THREAD_CONFINED",
            RuntimeSelectedRegionFinalizer.THREAD_CONFINED_WRITERS,
            "writers not crossed to, every object they wrote the field on,"
                + " with its recorded holders, mentioned inside one"
                + " occurrence tree on one thread, not the reader's"},
        {"ESCAPED", RuntimeSelectedRegionFinalizer.ESCAPED_WRITERS,
            "writers crossed to only because an object they wrote the field"
                + " on, reachable from nothing the reader names, or a holder"
                + " of it, was mentioned in a second occurrence tree, on a"
                + " second thread or the reader's, or under no occurrence"}};

    /** Per field's owner class, the sum. */
    private static Map<String, Integer> byOwnerClass(
            Map<String, Integer> fields) {
        Map<String, Integer> classes = new TreeMap<>();
        for (Map.Entry<String, Integer> field : fields.entrySet()) {
            classes.merge(RuntimeSelectedRegionFinalizer.ownerClass(
                    field.getKey()), field.getValue(), Integer::sum);
        }
        return classes;
    }

    /** The index's {@code member}: per field, the count; none for none. */
    private static void stateWritersNotCrossed(JsonObject index,
                                               String member,
                                               Map<String, Integer> counts) {
        if (counts.isEmpty()) return;
        JsonObject fields = new JsonObject();
        for (Map.Entry<String, Integer> field : counts.entrySet()) {
            fields.addProperty(field.getKey(), field.getValue());
        }
        index.add(member, fields);
    }

    /** Per field, the writers the plan rows' readers did not cross to,
     *  or crossed to only for a mention, as their {@code member} states
     *  them ({@link RuntimeSelectedRegionFinalizer#CONFINED_WRITERS} and
     *  its kin), summed; empty for none. */
    private static Map<String, Integer> writersNotCrossed(
            List<RegionInstancePlan> rows, String member) {
        Map<String, Integer> fields = new TreeMap<>();
        for (RegionInstancePlan plan : rows) {
            JsonElement held = plan.json().get(member);
            if (held == null || !held.isJsonObject()) continue;
            for (Map.Entry<String, JsonElement> field
                    : held.getAsJsonObject().entrySet()) {
                fields.merge(field.getKey(), field.getValue().getAsInt(),
                        Integer::sum);
            }
        }
        return fields;
    }

    /** The classes of equivalent deciders the plan rows stand for ({@link
     *  RuntimeSelectedRegionFinalizer#DECIDER_CLASS}): how many, the
     *  occurrences they stand for, and the largest three with their first
     *  and last addresses; empty for none. */
    private static String deciderClasses(List<RegionInstancePlan> rows) {
        List<JsonObject> classes = new ArrayList<>();
        int members = 0;
        for (RegionInstancePlan plan : rows) {
            JsonElement held = plan.json().get(
                    RuntimeSelectedRegionFinalizer.DECIDER_CLASS);
            if (held == null || !held.isJsonObject()) continue;
            classes.add(held.getAsJsonObject());
            members += optionalInteger(held.getAsJsonObject(), "members", 0);
        }
        if (classes.isEmpty()) return "";
        classes.sort(Comparator.<JsonObject>comparingInt(held ->
                optionalInteger(held, "members", 0)).reversed());
        StringBuilder text = new StringBuilder(" deciderClasses=")
                .append(classes.size()).append(" planned once each for ")
                .append(members).append(" equivalent decider occurrence(s) [");
        for (int index = 0; index < classes.size() && index < 3; index++) {
            JsonObject held = classes.get(index);
            if (index > 0) text.append(", ");
            text.append(optionalInteger(held, "members", 0)).append("x ")
                    .append(optionalString(held, "first")).append(" .. ")
                    .append(optionalString(held, "last"));
        }
        return text.append(']').toString();
    }

    /** Describes the existing selection/admission decision without adding one.
     */
    private static String noCandidateDiagnostic(
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
                // Kept so an unmatched goal still reports what was searched.
                selected = plan;
            }
            if (!arguments.goalId.isEmpty()
                    && !arguments.goalId.equals(plan.goal().goalId())) continue;
            selected = plan;
            selectedGoal = plan.goal();
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
        return nonNull(value).isEmpty() ? "<none>" : value;
    }

    private static String artifact(Path path) {
        return path == null ? "<none>"
                : path.toAbsolutePath().normalize().toString();
    }

    /** Every dataflow cell one proposed action names: its own cell plus {@code
     *  dependencyCells} (the local it lands in), since an accessor's library
     *  field (e.g. {@code AtomicInteger#value}) meets its receiver's field only
     *  at that local. */
    private static Set<String> actionCells(JsonObject action) {
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
     * Which inputs are symbolic: one decision per proposed input, one
     * authority, the categories the static scope map states. Four exist:
     *
     * <ul>
     *   <li>a clock's return, or a READ placeholder's own site ({@link
     * StaticScopeMap#clocks}, {@link StaticScopeMap#readSites}):
     * mints;</li>
     *   <li>a configuration getter's return (its {@link
     * InputActionCatalog#DECLARED_CONFIG_SOURCE}, from a {@code CONFIG}
     * DECLARED_SITE): mints, one symbol per key;</li>
     *   <li>an {@code EXPLICIT_SYMBOLIC_FAULT} marker: mints;</li>
     *   <li>a field a configured source of the region mints (a {@code
     * CausynthSymbolicSource} hook, or the engine's configuration read): the
     * source mints, the action stays concrete;</li>
     *   <li>a declared {@code COMMUNICATION_SITE_PORT}: tracked, never minted
     * (the value is installed from the other side).</li>
     * </ul>
     *
     * <p>Everything else is concrete: expressions ride with values in the VM,
     * so an undeclared entry symbol would only invent an input. Which symbol
     * reaches which read is decided at replay, never predicted here.</p>
     */
    static final class SymbolicInputSelection {
        /** Verdict of a read no declaration names. */
        static final String UNDECLARED = "UNDECLARED_SYMBOLIC_INPUT";
        /** Every clock's return cell, whatever region reads it, with its
         *  clock (the JVM clock it wraps, its tick). */
        private final Map<String, Clock> clocks;
        /** The READ placeholders ({@link StaticScopeMap#readSites}). */
        private final Set<String> reads;
        /** regionId -> sourceId -> the one field that hook site mints. */
        private final Map<String, Map<String, String>> minted;
        /** The regions reading a tracked cell (SYMBOL-SCOPE F2). */
        private final Set<String> trackedRegions;
        private SymbolicInputSelection(
                Map<String, Clock> clocks, Set<String> reads,
                Map<String, Map<String, String>> minted,
                Set<String> trackedRegions) {
            this.clocks = clocks;
            this.reads = reads;
            this.minted = minted;
            this.trackedRegions = trackedRegions;
        }

        /** Whether an occurrence of these regions (one and those folded into
         *  it) decides on tracked state, so it observes its branches from
         *  entry. */
        boolean readsTrackedState(Collection<String> regionIds) {
            for (String regionId : regionIds) {
                if (trackedRegions.contains(regionId)) return true;
            }
            return false;
        }

        /** The roots the scope map states ({@link StaticScopeMap#clocks},
         *  {@link StaticScopeMap#readSites}) and the hook declarations of the
         *  region catalog. */
        static SymbolicInputSelection read(StaticScopeMap scopeMap,
                                           List<JsonObject> regionCatalog)
                throws IOException {
            Map<String, Map<String, String>> minted = new LinkedHashMap<>();
            for (JsonObject region : regionCatalog == null
                    ? Collections.<JsonObject>emptyList() : regionCatalog) {
                String regionId = optionalString(region, "regionId");
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
            Map<String, Clock> clocks = new LinkedHashMap<>();
            for (Map.Entry<String, Clock> clock
                    : scopeMap.clocks().entrySet()) {
                clocks.put(clock.getKey() + ".return", clock.getValue());
            }
            return new SymbolicInputSelection(clocks, scopeMap.readSites(),
                    minted, scopeMap.trackedRegions());
        }

        /** A configured source's mint site is itself the allowlist
         *  authority. */
        private static void declareMintSite(
                Map<String, String> sites, JsonObject row) throws IOException {
            String sourceId = firstNonBlank(optionalString(row, "sourceId"));
            String field = firstNonBlank(optionalString(row, "fieldSignature"));
            if (JsonFields.exactInteger(row, "schemaVersion", -1)
                    != StaticSymbolicSourceDeclaration.SCHEMA_VERSION
                    || !StaticSymbolicSourceDeclaration.KIND.equals(
                    optionalString(row, "kind"))
                    || !StaticSymbolicSourceDeclaration.authority(
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

        /**
         * Ports one occurrence's DECLARED sites mint: scope-map static half
         * joined with the recording's captures, for sites this rule admits
         * (undeclared sites mint nothing). Static half from the map, dynamic
         * from the recording, region from the PLAN. An accessor declaration at
         * a site wins: the VM already propagates the field's expression through
         * the getter, so a call-result symbol would be a second authority.
         */
        JsonArray declaredPorts(RegionInstancePlan plan,
                                StaticScopeMap scopeMap,
                                Set<String> regionMethods) {
            List<JsonObject> ports = new ArrayList<>();
            for (DeclaredSiteCapture capture
                    : DeclaredSiteCapture.decode(plan.json())) {
                // The region's own text must hold the site.
                if (!regionMethods.contains(
                        SiteId.methodOf(capture.siteId()))) {
                    continue;
                }
                for (StaticScopeMap.Site site : accessorFirst(
                        scopeMap.declaredSitesAt(capture.siteId(),
                                capture.declaredCallee()))) {
                    ports.add(capture.port(plan, site));
                }
            }
            return admittedPorts(ports);
        }

        /** The same rule for an exposed occurrence (PIPELINE §7.8): one
         *  static port per CALL_RETURN declared site its text holds; no
         *  accessor returns. */
        JsonArray declaredSitePorts(RegionInstancePlan plan,
                                    StaticScopeMap scopeMap,
                                    Set<String> regionMethods) {
            List<JsonObject> ports = new ArrayList<>();
            for (StaticScopeMap.Site site : scopeMap.declaredSites()) {
                if (regionMethods.contains(SiteId.methodOf(site.siteId))
                        && StaticScopeMap.CALL_RETURN.equals(
                        site.declared.kind)) {
                    ports.add(DeclaredSiteCapture.declaredPort(plan, site));
                }
            }
            return admittedPorts(ports);
        }

        /** The ports this rule declares, first of each port id. */
        private JsonArray admittedPorts(List<JsonObject> ports) {
            Map<String, JsonObject> byId = new LinkedHashMap<>();
            for (JsonObject port : ports) {
                if (declares(port)) {
                    byId.putIfAbsent(optionalString(port, "portId"), port);
                }
            }
            JsonArray minted = new JsonArray();
            for (JsonObject port : byId.values()) minted.add(port);
            return minted;
        }

        /** A root the scope map states, or a fault marker. */
        private boolean declares(JsonObject action) {
            return clockOf(action) != null || readsAPlaceholder(action)
                    || !optionalString(action,
                    InputActionCatalog.DECLARED_CONFIG_SOURCE).isEmpty()
                    || workloadOwnedSymbol(action);
        }

        /** Whether the action is a READ placeholder's own site. */
        private boolean readsAPlaceholder(JsonObject action) {
            String site = optionalString(action, SiteId.MEMBER);
            for (String cell : actionCells(action)) {
                if (reads.contains(StaticScopeMap.readKey(site, cell))) {
                    return true;
                }
            }
            return false;
        }

        /** The accessor declarations of one site, or all of them when it has
         *  none. */
        private static List<StaticScopeMap.Site> accessorFirst(
                List<StaticScopeMap.Site> declarations) {
            List<StaticScopeMap.Site> accessors = new ArrayList<>();
            for (StaticScopeMap.Site site : declarations) {
                if (StaticScopeMap.ACCESSOR_RETURN.equals(
                        site.declared.kind)) {
                    accessors.add(site);
                }
            }
            return accessors.isEmpty() ? declarations : accessors;
        }

        JsonArray select(String regionId, JsonArray actions) {
            JsonArray selected = new JsonArray();
            for (JsonElement element : actions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                JsonObject retained = action.deepCopy();
                // Every input stays listed: concrete topology may anchor
                // instrumentation on it.
                if ("SYMBOLIC".equals(optionalString(action, "mode"))) {
                    decide(regionId, action, retained);
                }
                selected.add(retained);
            }
            return selected;
        }

        /** Stamps one proposed input with its declaration's verdict: declared
         *  or concrete, no third state. */
        private void decide(
                String regionId, JsonObject action, JsonObject retained) {
            if (minted(regionId, action)) {
                // The hook mints this root at its own call site; a second
                // action would add a free root.
                retained.addProperty("mode", "CONCRETE");
                retained.addProperty("symbolicDemand",
                        "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED");
                return;
            }
            if (declaredCutPort(action)) {
                // Tracked, never minted, even if named: the value is installed
                // from the other side (attachCommunicationLeaf), so a root
                // minted here is a free variable the attach overwrites.
                return;
            }
            if (!declares(action)) {
                // Undeclared: concrete. Its root-derived expression still rides
                // with the value; a plan-side mint would hide the real writer
                // behind a fresh root.
                retained.addProperty("mode", "CONCRETE");
                retained.addProperty("symbolicDemand", UNDECLARED);
                return;
            }
            // Declared: the replay mints here.
            retained.addProperty(
                    InputActionCatalog.DECLARED_SYMBOLIC_ROOT, true);
            Clock clock = clockOf(action);
            if (clock != null) {
                retained.addProperty(
                        InputActionCatalog.DECLARED_WALL_CLOCK, clock.nanos());
                if (!clock.source().isEmpty()) {
                    retained.addProperty(
                            InputActionCatalog.DECLARED_CLOCK_SOURCE,
                            clock.source());
                }
            }
        }

        /** A port declared by {@code communication-mappings.jsonl}: a handoff,
         *  not a mint. {@code
         *  RootMint.declaredCommunicationCutPort} asks the same
         *  {@code sourceKind} at replay. */
        private static boolean declaredCutPort(JsonObject action) {
            return RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                    .equals(optionalString(action, "sourceKind"));
        }

        /** A {@code Debug.makeSymbolicBoolean} fault marker: declared by the
         *  workload's own text. */
        private static boolean workloadOwnedSymbol(JsonObject action) {
            return RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                    .equals(optionalString(action, "sourceKind"));
        }

        /** Whether a hook site of this region mints the action's field (the
         *  hook owns it). */
        private boolean minted(String regionId, JsonObject action) {
            String field = actionField(action);
            return !field.isEmpty() && minted.getOrDefault(nonNull(regionId),
                    Collections.<String, String>emptyMap())
                    .containsValue(field);
        }

        /** The clock whose cell this action names -- its port or any of
         *  {@link ConcolicScheduler#actionCells} --,
         *  or null when it names none. */
        private Clock clockOf(JsonObject action) {
            Clock clock = clocks.get(actionPort(action));
            for (String cell : actionCells(action)) {
                if (clock != null) break;
                clock = clocks.get(cell);
            }
            return clock;
        }

        /** Soot's own proofs that one dataflow edge is a pure rename. */
        private static final Set<String> EXACT_VALUE_COPY_AUTHORITIES =
                Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                        "SOOT_EXACT_LOCAL_DIRECT_COPY_V1",
                        "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1")));

        /**
         * Adds to every declared name the cells it is a proven exact copy of.
         *
         * <p>A declaration names a value; the graph names it once per local it
         * is copied into (a {@code .return} cell included). Walking only
         * Soot-proven exact-copy edges ({@code valueFlowAuthority}) renames
         * without inferring dataflow, so no upstream carrier becomes a root.
         * Idempotent; done before any {@code select}.</p>
         */
        void resolveDeclaredNames(List<JsonObject> candidateGraph) {
            if (clocks.isEmpty()) return;
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
            Deque<String> pending = new ArrayDeque<>(clocks.keySet());
            while (!pending.isEmpty()) {
                String named = pending.removeFirst();
                for (String copied : copies.getOrDefault(named,
                        Collections.<String>emptySet())) {
                    if (clocks.putIfAbsent(copied, clocks.get(named))
                            == null) {
                        pending.addLast(copied);
                    }
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
        private final SymbolicInputSelection symbolicInputs;

        private LoadedInputs(List<RegionInstancePlan> regionPlans,
                             Set<String> regionIndex,
                             List<JsonObject> candidateGraph,
                             StaticScopeMap staticScopeMap,
                             JsonObject regionPlanIdentity,
                             JsonObject candidateGraphIdentity,
                             SymbolicInputSelection symbolicInputs) {
            this.regionPlans = regionPlans;
            this.regionIndex = regionIndex;
            this.candidateGraph = candidateGraph;
            this.staticScopeMap = staticScopeMap;
            this.regionPlanIdentity = regionPlanIdentity;
            this.candidateGraphIdentity = candidateGraphIdentity;
            this.symbolicInputs = symbolicInputs;
        }
    }

    public static final class Arguments {
        public final Path regionPlan;
        public final Path candidateGraph;
        /** The static scope map (the guard authority's publication). */
        public final Path staticScopeMap;
        public final Path outputDirectory;
        public final String regionId;
        public final String occurrenceId;
        public final String goalId;
        public final int maxJobs;
        /** The occurrence of the target site the case declares, or "". */
        public final String targetOccurrence;

        private Arguments(Path regionPlan, Path candidateGraph,
                          Path staticScopeMap,
                          Path outputDirectory, String regionId,
                          String occurrenceId, String goalId,
                          int maxJobs, String targetOccurrence) {
            this.regionPlan = regionPlan;
            this.candidateGraph = candidateGraph;
            this.staticScopeMap = staticScopeMap;
            this.outputDirectory = outputDirectory;
            this.regionId = nonNull(regionId);
            this.occurrenceId = nonNull(occurrenceId);
            this.goalId = nonNull(goalId);
            this.maxJobs = Math.max(1, maxJobs);
            this.targetOccurrence = nonNull(targetOccurrence);
        }

        public static Arguments parse(String[] args) {
            Map<String, String> values = parseArgs(args, "region-plan",
                    "candidate-graph", "static-scope-map", "output-dir",
                    "max-jobs", "target-occurrence");
            Path regionPlan = requiredPath(values, "region-plan");
            Path output = Paths.get(firstNonBlank(values.get("output-dir"),
                    ArtifactIO.sibling(regionPlan,
                            "concolic-schedule").toString()));
            Path candidateGraph = requiredPath(values, "candidate-graph");
            Path staticScopeMap = requiredPath(values, "static-scope-map");
            return new Arguments(regionPlan, candidateGraph, staticScopeMap,
                    output, "", "", "",
                    positiveInt(values.get("max-jobs"), 1, "max-jobs"),
                    values.get("target-occurrence"));
        }

        /** The one option-integer parse: a mistyped bound is refused, never
         *  replaced by the fallback (which would truncate silently). */
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
                    selection.goalId, 1, targetOccurrence);
        }
    }
}
