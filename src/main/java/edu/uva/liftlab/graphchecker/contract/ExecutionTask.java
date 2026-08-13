package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Canonical scheduled task emitted from one typed region goal. */
public final class ExecutionTask {
    private final JsonObject encoded;
    private final InputActionCatalog inputActions;
    private final LoopBoundPolicy loopBound;
    private final OutputClosureContract outputClosure;
    private final List<OutputCaptureSpec> outputCaptures;

    private ExecutionTask(JsonObject encoded) {
        this.encoded = encoded;
        if (taskId().isEmpty() || goalId().isEmpty()
                || regionId().isEmpty() || regionInstanceId().isEmpty()) {
            throw new IllegalArgumentException(
                    "execution task requires taskId, goalId, regionId and "
                            + "regionInstanceId");
        }
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
        return new ExecutionTask(encoded.deepCopy());
    }

    public static ExecutionTask create(
            RegionInstancePlan.Goal goal,
            String taskId,
            JsonArray inputActions,
            JsonArray branches,
            JsonArray edgeBindings,
            LoopBoundPolicy loopBound,
            boolean ready) {
        JsonObject task = new JsonObject();
        goal.writeTaskIdentityTo(task);
        goal.writeTaskPayloadTo(task);
        task.add(RegionInstancePlan.OCCURRENCE_CATALOG,
                goal.occurrenceInstantiationCatalog());
        task.addProperty("taskId", taskId);
        task.addProperty("goalKind", goal.kind().name());
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

    /** Drops planner-only access histories after the exact replay site wins. */
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

    public static ExecutionTask createProjectedOutput(
            RegionInstancePlan.Goal goal,
            String taskId,
            JsonArray inputActions,
            JsonArray branches,
            JsonArray edgeBindings,
            LoopBoundPolicy loopBound,
            boolean ready,
            OutputClosureContract outputClosure,
            JsonObject occurrenceCatalog,
            JsonObject producerProjection) {
        if (goal == null || !goal.kind().capturesOutputRelation()
                || outputClosure == null || occurrenceCatalog == null
                || producerProjection == null) {
            throw new IllegalArgumentException("projected output task "
                    + "requires goal, closure, occurrence catalog and "
                    + "producer projection");
        }
        JsonObject task = create(goal, taskId, inputActions, branches,
                edgeBindings, loopBound, ready).json();
        task.add(OutputClosureContract.FIELD, outputClosure.toJson());
        task.add(RegionInstancePlan.OCCURRENCE_CATALOG,
                occurrenceCatalog.deepCopy());
        task.add("producerProjection", producerProjection.deepCopy());
        return new ExecutionTask(task);
    }

    /**
     * Renames the bounded path after the branch contract this task publishes.
     *
     * <p>A goal's key names the goal's whole branch list, but a task may carry
     * a narrower one: projecting a producer onto a subset of its output ports
     * keeps only the guards that sub-closure names.  Carrying the goal's key
     * beside the projected contract publishes a name for a path the task does
     * not describe -- two tasks whose contracts are byte-identical then claim
     * to be different paths, and a valuation solved under one name has no
     * standing on the other even though the decisions are the same.</p>
     *
     * <p>A task with no seed contract at all keeps none: an empty key is how
     * a caller says there is no bounded path to attest, and inventing the
     * key of an empty branch list would claim one.</p>
     */
    private static void bindPathSeedToBranches(JsonObject task) {
        if (string(task, "pathSeedKey").isEmpty()) return;
        task.addProperty("pathSeedKey",
                BoundedPathSeed.key(array(task, "branches")));
    }

    public JsonObject json() {
        return encoded;
    }

    public String goalId() {
        return string(encoded, "goalId");
    }

    public String taskId() {
        return string(encoded, "taskId");
    }

    public String regionInstanceId() {
        return string(encoded, "regionInstanceId");
    }

    public String regionId() {
        return string(encoded, "regionId");
    }

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

    public String targetMethod() {
        return string(encoded, "targetMethod");
    }

    public JsonObject rootSelector() {
        return object(encoded, "rootSelector").deepCopy();
    }

    public InputActionCatalog inputActions() {
        return inputActions;
    }

    public JsonArray branches() {
        return array(encoded, "branches").deepCopy();
    }

    public LoopBoundPolicy loopBound() {
        return loopBound;
    }

    public JsonArray modelAssignments() {
        return array(encoded, "modelAssignments").deepCopy();
    }

    public JsonArray edgeBindings() {
        return array(encoded, "edgeBindings").deepCopy();
    }

    public String logicalRegionId() {
        return string(encoded, "logicalRegionId");
    }

    public String summaryReuseKey() {
        return string(encoded, "summaryReuseKey");
    }

    public String pathSeedKey() {
        return string(encoded, "pathSeedKey");
    }

    public JsonObject occurrenceInstantiationCatalog() {
        return object(encoded, RegionInstancePlan.OCCURRENCE_CATALOG)
                .deepCopy();
    }

    public JsonObject producerProjection() {
        return object(encoded, "producerProjection").deepCopy();
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
