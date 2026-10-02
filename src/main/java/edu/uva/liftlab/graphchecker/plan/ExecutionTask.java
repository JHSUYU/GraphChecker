package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** Scheduled work for one causal-skeleton region occurrence. */
public final class ExecutionTask extends PlanRow {
    /** How many tasks one campaign may contain; an unbounded plan is refused,
     *  not started. Here because both the Soot pass and the replay JVM check
     *  it. */
    public static final String MAX_TASKS_PROPERTY =
            "causynth.concolic.campaign.max.tasks";
    public static final int DEFAULT_MAX_TASKS = 64;

    /** The declared campaign bound, or {@link #DEFAULT_MAX_TASKS}. */
    public static int maxCampaignTasks() {
        String configured = System.getProperty(MAX_TASKS_PROPERTY);
        configured = configured == null ? "" : configured.trim();
        if (configured.isEmpty()) return DEFAULT_MAX_TASKS;
        int value;
        try {
            value = Integer.parseInt(configured);
        } catch (NumberFormatException malformed) {
            throw new IllegalStateException("malformed plan: "
                    + MAX_TASKS_PROPERTY + " must be a number");
        }
        if (value <= 0) {
            throw new IllegalStateException("malformed plan: "
                    + MAX_TASKS_PROPERTY + " must be positive");
        }
        return value;
    }

    /** Accesses of a tracked cell the replay observes before they run. */
    public static final String OBSERVED_SITES = "observedSites";
    /** Set when the task's region reads a tracked cell: its occurrence
     *  observes branches from entry (SYMBOL-SCOPE F2). */
    public static final String READS_TRACKED_STATE = "readsTrackedState";
    private final InputActionCatalog inputActions;
    private final LoopBoundPolicy loopBound;
    private final String rootLoopMethod;
    private final int rootLoopHeaderUnitIndex;
    private final int rootLoopDemandedUnitIndex;
    private final String rootLoopSiteId;
    private final Set<String> rootLoopControlSites;
    private final Set<String> fixedCountLoopSites;

    /** {@code bound}/{@code phases}: what {@link #create} just encoded; null =
     *  parse the wire. */
    private ExecutionTask(JsonObject source, LoopBoundPolicy bound,
                          List<ConfiguredSourcePhaseContract.Occurrence>
                                  phases) {
        super(source, "execution task", phases);
        require(taskId(), "taskId");
        require(goalId(), "goalId");
        inputActions = InputActionCatalog.decode(encoded);
        loopBound = bound == null ? LoopBoundPolicy.decode(encoded) : bound;
        // Once-only root: a region rooted on a service loop is entered once per
        // iteration, at the body.
        JsonObject rootLoop = loopBodyRoot()
                ? object(encoded, LoopBoundPolicy.ROOT_LOOP) : new JsonObject();
        rootLoopMethod = optionalString(rootLoop, LoopBoundPolicy.ROOT_LOOP_METHOD);
        rootLoopHeaderUnitIndex = rootLoopMethod.isEmpty() ? -1
                : optionalInteger(rootLoop, LoopBoundPolicy.HEADER_UNIT_INDEX, -1);
        rootLoopDemandedUnitIndex = rootLoopMethod.isEmpty() ? -1
                : optionalInteger(rootLoop, LoopBoundPolicy.DEMANDED_UNIT_INDEX, -1);
        if (!rootLoopMethod.isEmpty() && rootLoopHeaderUnitIndex < 0) {
            throw new IllegalArgumentException("execution task " + taskId()
                    + " roots a region at a loop body with no "
                    + LoopBoundPolicy.HEADER_UNIT_INDEX);
        }
        if (!rootLoopMethod.isEmpty() && rootLoopDemandedUnitIndex < 0) {
            throw new IllegalArgumentException("execution task " + taskId()
                    + " roots a region at a loop body with no "
                    + LoopBoundPolicy.DEMANDED_UNIT_INDEX);
        }
        rootLoopControlSites = textSet(rootLoop,
                LoopBoundPolicy.LOOP_CONTROL_SITE_IDS);
        rootLoopSiteId = optionalString(rootLoop, LoopBoundPolicy.LOOP_SITE_ID);
        fixedCountLoopSites = fixedCountLoopSites(encoded);
    }

    public static ExecutionTask decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException("execution task is required");
        }
        return new ExecutionTask(encoded.deepCopy(), null, null);
    }

    /** The methods whose conditional branches this task has woven. */
    public static final String BRANCH_METHODS = "branchMethods";

    /** Creates the one task for a scheduler-selected occurrence union. */
    public static ExecutionTask create(
            RegionInstancePlan.Goal goal,
            String taskId,
            JsonArray inputActions,
            JsonArray branchMethods,
            LoopBoundPolicy loopBound) {
        if (goal == null || inputActions == null || branchMethods == null
                || loopBound == null) {
            throw new IllegalArgumentException(
                    "goal and task contract values are required");
        }
        JsonObject task = new JsonObject();
        goal.plan().writeTaskIdentityTo(task);
        goal.writeTaskPayloadTo(task);
        task.addProperty("taskId", taskId);
        goal.kind().writeToTask(task);
        task.add(InputActionCatalog.FIELD, compactInputActions(inputActions));
        task.add(BRANCH_METHODS, branchMethods.deepCopy());
        loopBound.writeTo(task);
        // Executable by construction; still written because a decoded row is
        // externally authored.
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return new ExecutionTask(task, loopBound,
                goal.plan().configuredSourcePhases());
    }

    /** Drops planner-only access histories after the replay site is chosen. */
    private static JsonArray compactInputActions(JsonArray actions) {
        JsonArray result = new JsonArray();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) {
                result.add(element.deepCopy());
                continue;
            }
            JsonObject action = element.getAsJsonObject().deepCopy();
            action.remove("runtimeAccesses");
            JsonArray path = array(action, "fieldPath");
            JsonArray paths = array(action, "fieldPaths");
            if (path.size() > 0 && paths.size() == 1
                    && paths.get(0).isJsonArray()
                    && path.equals(paths.get(0).getAsJsonArray())) {
                action.remove("fieldPaths");
            }
            result.add(action);
        }
        return result;
    }

    public String goalId() { return optionalString(encoded, "goalId"); }

    public String taskId() { return optionalString(encoded, "taskId"); }

    /**
     * THE ROOT HOOK this row's region opens at: its region and root method,
     * and for a loop-body root that loop.  INSTRUMENT weaves ONE entry per
     * group, however many planned occurrences share it, and a replay offers
     * each invocation of it to every task of the group
     * ({@code runtime.ConcolicTaskPlan#select}).  Woven once per row, sweep
     * a40h2's 763 occurrences of {@code Configuration.get(String)} put 758
     * entries in one body (15,980 units), which the woven-body verifier did
     * not finish in 40 minutes.
     */
    public String rootHookGroup() {
        boolean loop = loopBodyRoot();
        return (loop ? "LOOP\n" : "METHOD\n") + regionId() + "\n"
                + rootMethod() + (loop ? "\n" + rootLoopMethod + "\n"
                + rootLoopHeaderUnitIndex : "");
    }

    /**
     * The enclosing method entry a loop-body root's iterations are addressed
     * under (its root method), woven once for every loop-body row rooted
     * there; "" for any other row.
     */
    public String loopRootHookGroup() {
        return loopBodyRoot() ? rootMethod() : "";
    }

    /** Whether this region is rooted at a service loop's body
     *  ({@link LoopBoundPolicy#LOOP_BODY_ROOT}). */
    public boolean loopBodyRoot() {
        return LoopBoundPolicy.LOOP_BODY_ROOT.equals(rootAuthority());
    }

    public ClosureGoalKind goalKind() {
        return ClosureGoalKind.fromTask(encoded);
    }

    public boolean executable() {
        return "EXECUTABLE".equals(
                optionalString(object(encoded, "admission"), "state"));
    }

    public String rootMethod() {
        return optionalString(object(encoded, "rootSelector"), "method");
    }

    public String targetMethod() { return optionalString(encoded, "targetMethod"); }

    /** {@link LoopBoundPolicy#LOOP_BODY_ROOT}: rooted at a service loop's body
     *  (one iteration per activation). */
    public String rootAuthority() {
        return optionalString(encoded, LoopBoundPolicy.ROOT_AUTHORITY);
    }

    public String rootLoopMethod() { return rootLoopMethod; }

    /** Unit indices of the root loop's dominance-proved header and demanded
     *  unit. */
    public int rootLoopHeaderUnitIndex() { return rootLoopHeaderUnitIndex; }

    public int rootLoopDemandedUnitIndex() {
        return rootLoopDemandedUnitIndex;
    }

    /** Iteration-control sites the region's exits are installed on. */
    public Set<String> rootLoopControlSites() { return rootLoopControlSites; }

    /** The root loop's {@code loopSiteId} (its {@code K_L} key in {@link
     *  #loopBound()}), else "". */
    public String rootLoopSiteId() { return rootLoopSiteId; }

    /** Retained loops whose concrete cardinality is exact, not a {@code K_L}. */
    public Set<String> fixedCountLoopSites() { return fixedCountLoopSites; }

    /** Exact retained-loop catalog carried unchanged from static analysis. */
    public JsonArray retainedLoops() {
        return array(encoded, "retainedLoops").deepCopy();
    }

    private static Set<String> fixedCountLoopSites(JsonObject task) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(task, "retainedLoops")) {
            if (!element.isJsonObject()) continue;
            JsonObject loop = element.getAsJsonObject();
            if (!LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(optionalString(loop,
                    LoopBoundPolicy.LOOP_CLASSIFICATION))) {
                continue;
            }
            String primary = optionalString(loop, LoopBoundPolicy.LOOP_SITE_ID);
            if (!primary.isEmpty()) result.add(primary);
            result.addAll(textSet(loop,
                    LoopBoundPolicy.LOOP_CONTROL_SITE_IDS));
        }
        return Collections.unmodifiableSet(result);
    }

    /** Non-blank strings of a JSON array member, in wire order. */
    static Set<String> textSet(JsonObject row, String field) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(row, field)) {
            if (!element.isJsonPrimitive()) continue;
            String value = element.getAsString().trim();
            if (!value.isEmpty()) result.add(value);
        }
        return Collections.unmodifiableSet(result);
    }

    public JsonObject rootSelector() {
        return object(encoded, "rootSelector").deepCopy();
    }

    public InputActionCatalog inputActions() { return inputActions; }

    /** The methods whose conditional branches INSTRUMENT weaves; which branches
     *  is the Soot bodies' answer (every symbolic-operand
     *  decision is recorded, so there is no per-branch selection). */
    public JsonArray branchMethods() {
        return array(encoded, BRANCH_METHODS).deepCopy();
    }

    public LoopBoundPolicy loopBound() { return loopBound; }

    /** Where this occurrence exports or attaches a declared communication port.
     *  Only declares where propagation happens; the VM's {@code VALUE_HANDOFF}
     *  edge is the value relation, never a pairing from here. */
    public List<CommunicationHandoffSpec> communicationHandoffs() {
        return CommunicationHandoffSpec.decode(encoded);
    }

    /** Accesses of a tracked cell the replay must OBSERVE: a cell nothing
     *  symbolic reached keeps no version log, so the concrete value becomes
     *  its first expression, later writes are versions a reader can join to,
     *  and a read states the version it saw ({@link
     *  StaticScopeMap#observedSites}). */
    public JsonArray observedSites() {
        return array(encoded, OBSERVED_SITES).deepCopy();
    }
}
