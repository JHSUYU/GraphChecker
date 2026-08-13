package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Scheduled work for one causal-skeleton occurrence and one relation. */
public final class ExecutionTask {
    private static final String[] RETIRED_FIELDS = {
            "regionInstanceId", "rootCallId", "logicalRegionId",
            "logicalInstanceCount", "summaryReuseKey",
            "occurrenceInstantiationCatalog", "executionOccurrence",
            "producerProjection"
    };

    private final JsonObject encoded;
    private final InputActionCatalog inputActions;
    private final LoopBoundPolicy loopBound;
    private final OutputClosureContract outputClosure;
    private final List<OutputCaptureSpec> outputCaptures;

    private ExecutionTask(JsonObject source) {
        encoded = source.deepCopy();
        rejectRetired(encoded);
        require(taskId(), "taskId");
        require(goalId(), "goalId");
        require(sourceKey(), "sourceKey");
        require(occurrenceId(), "occurrenceId");
        require(relationKey(), "relationKey");
        require(relationContractHash(), "relationContractHash");
        require(regionId(), "regionId");

        inputActions = InputActionCatalog.decode(encoded);
        loopBound = LoopBoundPolicy.decode(encoded);
        outputClosure = encoded.has(OutputClosureContract.FIELD)
                ? OutputClosureCodec.decode(encoded) : null;
        outputCaptures = outputClosure == null
                ? Collections.emptyList()
                : OutputClosureCodec.captureSpecs(outputClosure);
        if (goalKind().capturesOutputRelation() != (outputClosure != null)) {
            throw new IllegalArgumentException(
                    "execution task goalKind and outputClosure disagree");
        }
    }

    public static ExecutionTask decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException("execution task is required");
        }
        return new ExecutionTask(encoded);
    }

    public static ExecutionTask create(
            RegionInstancePlan.Goal goal,
            String taskId,
            JsonArray inputActions,
            JsonArray branches,
            JsonArray edgeBindings,
            LoopBoundPolicy loopBound,
            boolean ready) {
        return create(goal, taskId, inputActions, branches, edgeBindings,
                loopBound, ready, goal.outputClosure());
    }

    /** Creates a task with a scheduler-selected subset of the goal closure. */
    public static ExecutionTask create(
            RegionInstancePlan.Goal goal,
            String taskId,
            JsonArray inputActions,
            JsonArray branches,
            JsonArray edgeBindings,
            LoopBoundPolicy loopBound,
            boolean ready,
            OutputClosureContract selectedClosure) {
        if (goal == null || inputActions == null || branches == null
                || edgeBindings == null || loopBound == null) {
            throw new IllegalArgumentException(
                    "goal and task contract values are required");
        }
        if (goal.kind().capturesOutputRelation()
                != (selectedClosure != null)) {
            throw new IllegalArgumentException(
                    "goal kind and selected output closure disagree");
        }
        JsonObject task = new JsonObject();
        goal.writeTaskIdentityTo(task);
        goal.writeTaskPayloadTo(task);
        if (selectedClosure != null) {
            task.add(OutputClosureContract.FIELD,
                    selectedClosure.toJson());
        }
        task.addProperty("taskId", taskId);
        goal.kind().writeToTask(task);
        task.add(InputActionCatalog.FIELD, compactInputActions(inputActions));
        task.add("branches", branches.deepCopy());
        bindPathSeedToBranches(task);
        loopBound.writeTo(task);
        if (edgeBindings.size() > 0) {
            task.add("edgeBindings", edgeBindings.deepCopy());
        }
        JsonObject admission = new JsonObject();
        admission.addProperty("state", ready ? "EXECUTABLE" : "BLOCKED");
        task.add("admission", admission);
        return new ExecutionTask(task);
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

    private static void bindPathSeedToBranches(JsonObject task) {
        if (string(task, "pathSeedKey").isEmpty()) return;
        task.addProperty("pathSeedKey",
                BoundedPathSeed.key(array(task, "branches")));
    }

    public JsonObject json() { return encoded; }

    public String goalId() { return string(encoded, "goalId"); }

    public String taskId() { return string(encoded, "taskId"); }

    public String sourceKey() { return string(encoded, "sourceKey"); }

    public String occurrenceId() { return string(encoded, "occurrenceId"); }

    public String relationKey() { return string(encoded, "relationKey"); }

    public String relationContractHash() {
        return string(encoded, "relationContractHash");
    }

    public String regionId() { return string(encoded, "regionId"); }

    public ClosureGoalKind goalKind() {
        return ClosureGoalKind.fromTask(encoded);
    }

    public boolean executable() {
        return "EXECUTABLE".equals(
                string(object(encoded, "admission"), "state"));
    }

    public String rootMethod() {
        return string(object(encoded, "rootSelector"), "method");
    }

    public String targetMethod() { return string(encoded, "targetMethod"); }

    public JsonObject rootSelector() {
        return object(encoded, "rootSelector").deepCopy();
    }

    public InputActionCatalog inputActions() { return inputActions; }

    public JsonArray branches() {
        return array(encoded, "branches").deepCopy();
    }

    public LoopBoundPolicy loopBound() { return loopBound; }

    public JsonArray modelAssignments() {
        return array(encoded, "modelAssignments").deepCopy();
    }

    public JsonArray edgeBindings() {
        return array(encoded, "edgeBindings").deepCopy();
    }

    public String pathSeedKey() { return string(encoded, "pathSeedKey"); }

    public JsonElement replayContract() {
        JsonElement contract = encoded.get("replayContract");
        return contract == null ? null : contract.deepCopy();
    }

    public OutputClosureContract outputClosure() { return outputClosure; }

    public List<OutputCaptureSpec> outputCaptures() {
        return outputCaptures;
    }

    private static void rejectRetired(JsonObject value) {
        for (String field : RETIRED_FIELDS) {
            if (value.has(field)) {
                throw new IllegalArgumentException(
                        "execution task contains retired field " + field);
            }
        }
    }

    private static String require(String value, String field) {
        String result = value == null ? "" : value.trim();
        if (result.isEmpty()) {
            throw new IllegalArgumentException(
                    "execution task requires " + field);
        }
        return result;
    }
}
