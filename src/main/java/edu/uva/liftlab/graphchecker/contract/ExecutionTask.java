package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Scheduled work for one causal-skeleton occurrence and one relation. */
public final class ExecutionTask {
    /** Planner-selected function entry for one concrete interaction corridor. */
    public static final String REPLAY_ENTRY = "replayEntry";

    private final JsonObject encoded;
    private final InputActionCatalog inputActions;
    private final LoopBoundPolicy loopBound;
    private final OutputClosureContract outputClosure;
    private final List<OutputCaptureSpec> outputCaptures;

    private ExecutionTask(JsonObject source) {
        encoded = source.deepCopy();
        require(taskId(), "taskId");
        require(goalId(), "goalId");
        require(sourceKey(), "sourceKey");
        require(occurrenceId(), "occurrenceId");
        require(relationKey(), "relationKey");
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

    /** Creates the one task for a scheduler-selected occurrence union. */
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
        loopBound.writeTo(task);
        if (edgeBindings.size() > 0) {
            task.add("edgeBindings", edgeBindings.deepCopy());
        }
        retainSelectedCommunicationHandoffs(task, inputActions,
                edgeBindings, selectedClosure);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", ready ? "EXECUTABLE" : "BLOCKED");
        task.add("admission", admission);
        return new ExecutionTask(task);
    }

    /**
     * Keeps only cut ports the selected task actually consumes or produces.
     * A region occurrence can observe many RPC parameters, but copying all of
     * them into every task instruments unrelated payload and lets concrete
     * service traffic grow the VM expression session.  The selected edge and
     * closure are already the task's complete interaction frontier.
     */
    private static void retainSelectedCommunicationHandoffs(
            JsonObject task, JsonArray inputActions, JsonArray edgeBindings,
            OutputClosureContract selectedClosure) {
        JsonArray declared = array(task, CommunicationHandoffSpec.FIELD);
        if (declared.size() == 0) return;

        Set<String> selectedPorts = new LinkedHashSet<>();
        for (JsonElement element : edgeBindings) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            addPort(selectedPorts, string(edge, "fromOutputPort"));
            addPort(selectedPorts, string(edge, "toInputPort"));
        }
        for (JsonElement element : inputActions) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            addPort(selectedPorts, string(action, "symbol"));
            addPort(selectedPorts, string(action, "portId"));
        }
        if (selectedClosure != null) {
            for (OutputClosureContract.Member member
                    : selectedClosure.members()) {
                addPort(selectedPorts, member.portId());
                for (JsonElement element
                        : array(member.slice(), "inputPorts")) {
                    if (element.isJsonPrimitive()) {
                        addPort(selectedPorts, element.getAsString());
                    }
                }
            }
        }

        JsonArray retained = new JsonArray();
        for (JsonElement element : declared) {
            if (!element.isJsonObject()) continue;
            JsonObject handoff = element.getAsJsonObject();
            String portId = string(handoff,
                    CommunicationCatalogContract.PORT_ID);
            String componentOf = string(handoff,
                    CommunicationCatalogContract.PORT_COMPONENT_OF);
            if (selectedPorts.contains(portId)
                    || !componentOf.isEmpty()
                    && selectedPorts.contains(componentOf)) {
                retained.add(handoff.deepCopy());
            }
        }
        if (retained.size() == 0) {
            task.remove(CommunicationHandoffSpec.FIELD);
        } else {
            task.add(CommunicationHandoffSpec.FIELD, retained);
        }
    }

    private static void addPort(Set<String> ports, String port) {
        if (port != null && !port.isEmpty()) ports.add(port);
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

    public JsonObject json() { return encoded; }

    public String goalId() { return string(encoded, "goalId"); }

    public String taskId() { return string(encoded, "taskId"); }

    public String sourceKey() { return string(encoded, "sourceKey"); }

    public String occurrenceId() { return string(encoded, "occurrenceId"); }

    public String relationKey() { return string(encoded, "relationKey"); }

    public String regionId() { return string(encoded, "regionId"); }

    /**
     * Stable identity of the instrumentation owned by this plan row.
     *
     * <p>A replay gets a new task id, while the occurrence remains the same.
     * Goal ids and capture alternatives are case-obligation labels inside the
     * one coarse result, so neither may create another injected root hook.</p>
     */
    public String instrumentationSelector() {
        StringBuilder selector = new StringBuilder();
        appendSelectorPart(selector, regionId());
        appendSelectorPart(selector, occurrenceId());
        return selector.toString();
    }

    private static void appendSelectorPart(StringBuilder selector,
                                           String value) {
        String part = value == null ? "" : value;
        selector.append(part.length()).append(':').append(part);
    }

    public ClosureGoalKind goalKind() {
        return ClosureGoalKind.fromTask(encoded);
    }

    public boolean executable() {
        return "EXECUTABLE".equals(
                string(object(encoded, "admission"), "state"));
    }

    public String rootMethod() {
        String replay = string(object(encoded, REPLAY_ENTRY), "method");
        return replay.isEmpty()
                ? string(object(encoded, "rootSelector"), "method")
                : replay;
    }

    public String targetMethod() { return string(encoded, "targetMethod"); }

    public JsonObject rootSelector() {
        JsonObject selector = object(encoded, "rootSelector").deepCopy();
        JsonObject replay = object(encoded, REPLAY_ENTRY);
        if (replay.size() > 0) {
            String method = require(string(replay, "method"),
                    REPLAY_ENTRY + ".method");
            String receiverClass = require(string(replay, "receiverClass"),
                    REPLAY_ENTRY + ".receiverClass");
            selector.addProperty("method", method);
            selector.addProperty("receiverClass", receiverClass);
        }
        return selector;
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

    /** Member a scheduler declares this task's symbolic carriers in. */
    public static final String SHARED_CARRIERS = "sharedCarriers";

    /**
     * Shared locations this task asks the runtime to select at region entry.
     *
     * <p>Selection is what makes a location's writes publish versions and its
     * reads resolve to a writer, and it is deliberately bounded: nothing is
     * versioned until a task names it. The list is carried verbatim and
     * unparsed, exactly like a read-cut plan - the runtime owns what a carrier
     * declaration means, and rebuilding it here would let the two disagree.
     * An absent or empty list means this task selects nothing, which is the
     * honest default and never an invitation to guess a carrier.</p>
     */
    /**
     * Where this occurrence hands a declared communication port to the VM.
     *
     * <p>An export site sends the port's live expression; an attach site
     * takes it.  The VM's successful attach and its {@code VALUE_HANDOFF}
     * edge are the whole value relation across the cut, so these sites are
     * declarations of where the propagation happens and never a pairing.</p>
     */
    public List<CommunicationHandoffSpec> communicationHandoffs() {
        return CommunicationHandoffSpec.decode(encoded);
    }

    public JsonArray sharedCarriers() {
        return array(encoded, SHARED_CARRIERS).deepCopy();
    }

    public JsonElement replayContract() {
        JsonElement contract = encoded.get("replayContract");
        return contract == null ? null : contract.deepCopy();
    }

    public OutputClosureContract outputClosure() { return outputClosure; }

    public List<OutputCaptureSpec> outputCaptures() {
        return outputCaptures;
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
