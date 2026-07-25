package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.ClosureGoalKind;

import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Canonical scheduled task emitted from one typed region goal. */
public final class ExecutionTask {
    private final JsonObject encoded;
    private final String goalId;
    private final String taskId;
    private final String regionInstanceId;
    private final String regionId;
    private final String test;
    private final String pathQueryKey;
    private final String executionPhase;
    private final ClosureGoalKind goalKind;
    private final JsonObject rootSelector;
    private final boolean executable;
    private final InputActionCatalog inputActions;
    private final OutputClosureContract outputClosure;
    private final List<OutputCaptureSpec> outputCaptures;

    private ExecutionTask(JsonObject encoded) {
        this.encoded = encoded;
        goalId = string(encoded, "goalId");
        taskId = string(encoded, "taskId");
        regionInstanceId = string(encoded, "regionInstanceId");
        regionId = string(encoded, "regionId");
        test = string(encoded, "test");
        pathQueryKey = string(encoded, "pathQueryKey");
        executionPhase = string(encoded, "executionPhase");
        goalKind = ClosureGoalKind.fromTask(encoded);
        rootSelector = object(encoded, "rootSelector").deepCopy();
        executable = "EXECUTABLE".equals(
                string(object(encoded, "admission"), "state"));
        if (taskId.isEmpty() || goalId.isEmpty()
                || regionId.isEmpty() || regionInstanceId.isEmpty()) {
            throw new IllegalArgumentException(
                    "execution task requires taskId, goalId, regionId and "
                            + "regionInstanceId");
        }
        inputActions = InputActionCatalog.decode(encoded);
        outputClosure = encoded.has(OutputClosureContract.FIELD)
                ? OutputClosureCodec.decode(encoded) : null;
        outputCaptures = outputClosure == null
                ? Collections.emptyList()
                : OutputClosureCodec.captureSpecs(outputClosure);
        if (goalKind.capturesOutputRelation() != (outputClosure != null)) {
            throw new IllegalArgumentException(
                    "execution task goalKind and outputClosure disagree");
        }
    }

    public static ExecutionTask decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException("execution task is required");
        }
        return new ExecutionTask(encoded.deepCopy());
    }

    public static ExecutionTask create(
            RegionInstancePlan.Goal goal,
            String taskId,
            String executionPhase,
            JsonArray inputActions,
            JsonArray branches,
        JsonArray edgeBindings,
        boolean ready) {
        JsonObject task = new JsonObject();
        goal.plan().writeTaskIdentityTo(task);
        goal.writeTaskPayloadTo(task);
        task.addProperty("taskId", taskId);
        task.addProperty("goalKind", goal.kind().name());
        task.addProperty("executionPhase", executionPhase);
        task.add(InputActionCatalog.FIELD, inputActions.deepCopy());
        task.add("branches", branches.deepCopy());
        if (edgeBindings.size() > 0) {
            task.add("edgeBindings", edgeBindings.deepCopy());
        }
        JsonObject admission = new JsonObject();
        admission.addProperty("state", ready ? "EXECUTABLE" : "BLOCKED");
        task.add("admission", admission);
        return new ExecutionTask(task);
    }

    public JsonObject json() {
        return encoded;
    }

    public String goalId() {
        return goalId;
    }

    public String taskId() {
        return taskId;
    }

    public String regionInstanceId() {
        return regionInstanceId;
    }

    public String regionId() {
        return regionId;
    }

    public String test() {
        return test;
    }

    public String pathQueryKey() {
        return pathQueryKey;
    }

    public String executionPhase() {
        return executionPhase;
    }

    public ClosureGoalKind goalKind() {
        return goalKind;
    }

    public boolean executable() {
        return executable;
    }

    public String rootMethod() {
        return string(rootSelector, "method");
    }

    public int rootOrdinal() {
        return integer(rootSelector, "ordinal", 1);
    }

    public JsonObject rootSelector() {
        return rootSelector.deepCopy();
    }

    public InputActionCatalog inputActions() {
        return inputActions;
    }

    public JsonArray branches() {
        return array(encoded, "branches").deepCopy();
    }

    public JsonArray modelAssignments() {
        return array(encoded, "modelAssignments").deepCopy();
    }

    public JsonArray containerElementFieldBindings() {
        return array(encoded, "containerElementFieldBindings").deepCopy();
    }

    public JsonArray mapValueElementFieldProjections() {
        return array(encoded, "mapValueElementFieldProjections").deepCopy();
    }

    public JsonArray edgeBindings() {
        return array(encoded, "edgeBindings").deepCopy();
    }

    public JsonArray heapStateBindings() {
        return array(encoded, "heapStateBindings").deepCopy();
    }

    public JsonElement replayContract() {
        JsonElement contract = encoded.get("replayContract");
        return contract == null ? null : contract.deepCopy();
    }

    public OutputClosureContract outputClosure() {
        return outputClosure;
    }

    public List<OutputCaptureSpec> outputCaptures() {
        return outputCaptures;
    }
}
