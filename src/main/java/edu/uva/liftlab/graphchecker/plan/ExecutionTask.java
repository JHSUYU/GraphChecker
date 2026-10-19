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

public final class ExecutionTask extends PlanRow {
    public static final String MAX_TASKS_PROPERTY =
            "causynth.concolic.campaign.max.tasks";
    public static final int DEFAULT_MAX_TASKS = 64;

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

    public static final String READS_TRACKED_STATE = "readsTrackedState";
    private final InputActionCatalog inputActions;
    private final LoopBoundPolicy loopBound;
    private final String rootLoopMethod;
    private final int rootLoopHeaderUnitIndex;
    private final int rootLoopDemandedUnitIndex;
    private final String rootLoopSiteId;
    private final Set<String> rootLoopControlSites;
    private final Set<String> fixedCountLoopSites;

    private ExecutionTask(JsonObject source, LoopBoundPolicy bound,
                          List<ConfiguredSourcePhaseContract.Occurrence>
                                  phases) {
        super(source, "execution task", phases);
        require(taskId(), "taskId");
        require(goalId(), "goalId");
        inputActions = InputActionCatalog.decode(encoded);
        loopBound = bound == null ? LoopBoundPolicy.decode(encoded) : bound;
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

    public static final String BRANCH_METHODS = "branchMethods";

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
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return new ExecutionTask(task, loopBound,
                goal.plan().configuredSourcePhases());
    }

    private static JsonArray compactInputActions(JsonArray actions) {
        JsonArray result = new JsonArray();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) {
                result.add(element.deepCopy());
                continue;
            }
            JsonObject action = element.getAsJsonObject().deepCopy();
            JsonArray path = array(action, "fieldPath");
            JsonArray paths = array(action, "fieldPaths");
            if (path.size() > 0 && paths.size() == 1
                    && paths.get(0).isJsonArray()
                    && path.equals(paths.get(0).getAsJsonArray())) {
                action.remove("fieldPaths");
            }
            result.add(InputActionCatalog.stamp(action));
        }
        return result;
    }

    public String goalId() { return optionalString(encoded, "goalId"); }

    public String taskId() { return optionalString(encoded, "taskId"); }

    public String rootHookGroup() {
        boolean loop = loopBodyRoot();
        return (loop ? "LOOP\n" : "METHOD\n") + regionId() + "\n"
                + rootMethod() + (loop ? "\n" + rootLoopMethod + "\n"
                + rootLoopHeaderUnitIndex : "");
    }

    public String loopRootHookGroup() {
        return loopBodyRoot() ? rootMethod() : "";
    }

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

    public String rootAuthority() {
        return optionalString(encoded, LoopBoundPolicy.ROOT_AUTHORITY);
    }

    public String rootLoopMethod() { return rootLoopMethod; }

    public int rootLoopHeaderUnitIndex() { return rootLoopHeaderUnitIndex; }

    public int rootLoopDemandedUnitIndex() {
        return rootLoopDemandedUnitIndex;
    }

    public Set<String> rootLoopControlSites() { return rootLoopControlSites; }

    public String rootLoopSiteId() { return rootLoopSiteId; }

    public Set<String> fixedCountLoopSites() { return fixedCountLoopSites; }

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

    public JsonArray branchMethods() {
        return array(encoded, BRANCH_METHODS).deepCopy();
    }

    public LoopBoundPolicy loopBound() { return loopBound; }

    public List<CommunicationHandoffSpec> communicationHandoffs() {
        return CommunicationHandoffSpec.decode(encoded);
    }
}
