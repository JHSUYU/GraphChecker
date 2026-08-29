package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Scheduled work for one causal-skeleton occurrence and one relation. */
public final class ExecutionTask extends PlanRow {
    /** Planner-selected function entry for one concrete interaction corridor. */
    public static final String REPLAY_ENTRY = "replayEntry";
    /** Member a scheduler declares this task's symbolic carriers in. */
    public static final String SHARED_CARRIERS = "sharedCarriers";

    private final InputActionCatalog inputActions;
    private final LoopBoundPolicy loopBound;
    private final OutputClosureContract outputClosure;
    private final List<OutputCaptureSpec> outputCaptures;
    private final String rootLoopMethod;
    private final int rootLoopHeaderUnitIndex;
    private final String rootLoopSiteId;
    private final Set<String> rootLoopControlSites;
    private final Set<String> fixedCountLoopSites;

    /** {@code bound}, {@code closure} and {@code phases} are the values
     *  {@link #create} just encoded; a decoder passes null and the wire is
     *  parsed instead. */
    private ExecutionTask(JsonObject source, LoopBoundPolicy bound,
                          OutputClosureContract closure,
                          List<ConfiguredSourcePhaseContract.Occurrence>
                                  phases) {
        super(source, "execution task", false, phases);
        require(taskId(), "taskId");
        require(goalId(), "goalId");
        inputActions = InputActionCatalog.decode(encoded);
        loopBound = bound == null ? LoopBoundPolicy.decode(encoded) : bound;
        outputClosure = closure != null ? closure
                : encoded.has(OutputClosureContract.FIELD)
                ? OutputClosureCodec.decode(encoded) : null;
        outputCaptures = outputClosure == null
                ? Collections.<OutputCaptureSpec>emptyList()
                : OutputClosureCodec.captureSpecs(outputClosure);
        if (goalKind().capturesOutputRelation() != (outputClosure != null)) {
            throw new IllegalArgumentException(
                    "execution task goalKind and outputClosure disagree");
        }
        // The once-only-root rule: a region rooted on a service loop is
        // entered once per iteration, at the loop body rather than at the
        // frame above it.
        JsonObject rootLoop = LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                rootAuthority()) ? object(encoded, LoopBoundPolicy.ROOT_LOOP)
                : new JsonObject();
        rootLoopMethod = string(rootLoop, LoopBoundPolicy.ROOT_LOOP_METHOD);
        rootLoopHeaderUnitIndex = rootLoopMethod.isEmpty() ? -1
                : integer(rootLoop, LoopBoundPolicy.HEADER_UNIT_INDEX, -1);
        if (!rootLoopMethod.isEmpty() && rootLoopHeaderUnitIndex < 0) {
            throw new IllegalArgumentException("execution task " + taskId()
                    + " roots a region at a loop body with no "
                    + LoopBoundPolicy.HEADER_UNIT_INDEX);
        }
        rootLoopControlSites = textSet(rootLoop,
                LoopBoundPolicy.LOOP_CONTROL_SITE_IDS);
        rootLoopSiteId = string(rootLoop, LoopBoundPolicy.LOOP_SITE_ID);
        fixedCountLoopSites = fixedCountLoopSites(encoded);
    }

    public static ExecutionTask decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException("execution task is required");
        }
        return new ExecutionTask(encoded.deepCopy(), null, null, null);
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
        JsonObject task = new JsonObject();
        goal.plan().writeTaskIdentityTo(task);
        goal.writeTaskPayloadTo(task);
        if (selectedClosure != null) {
            // Also the producer-against-task-scope check the decode would run.
            OutputClosureCodec.writeTo(task, selectedClosure);
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
        demoteNestedLoopRootOutsideSelectedContinuation(task,
                selectedClosure);
        promoteSelectedReplayEntry(task, selectedClosure);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", ready ? "EXECUTABLE" : "BLOCKED");
        task.add("admission", admission);
        return new ExecutionTask(task, loopBound, selectedClosure,
                goal.plan().configuredSourcePhases());
    }

    /**
     * Keeps a selected output that ran beside, rather than inside, a nested
     * service loop from being replayed after it.
     *
     * <p>The region-level once-only-root rule follows the failure anchor.  A
     * coarse activation can also contain an earlier producer phase: HDFS-11741
     * registers the DataNode before {@code offerService()}, while its target
     * heartbeat is inside that service loop.  Once output projection proves
     * every demanded member shares the earlier {@code register} continuation,
     * a loop-body root at {@code offerService} can never execute the selected
     * response cut or heap writes.  In that exact nested-loop shape, remove
     * the provisional loop root and let the existing continuation promotion
     * root the task at the selected producer phase.</p>
     *
     * <p>A loop in the root method itself is unchanged.  So are closures with
     * a missing or conflicting continuation: neither provides authority to
     * move the task.</p>
     */
    private static void demoteNestedLoopRootOutsideSelectedContinuation(
            JsonObject task, OutputClosureContract closure) {
        if (closure == null || !LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                string(task, LoopBoundPolicy.ROOT_AUTHORITY))) {
            return;
        }
        JsonObject rootLoop = object(task, LoopBoundPolicy.ROOT_LOOP);
        String loopMethod = string(rootLoop,
                LoopBoundPolicy.ROOT_LOOP_METHOD);
        String coarseRoot = string(object(task, "rootSelector"), "method");
        if (loopMethod.isEmpty() || coarseRoot.isEmpty()
                || loopMethod.equals(coarseRoot)) {
            return;
        }
        JsonObject selected = null;
        for (OutputClosureContract.Member member : closure.members()) {
            JsonObject entry = object(member.slice(), REPLAY_ENTRY);
            if (string(entry, "method").isEmpty()
                    || string(entry, "receiverClass").isEmpty()) {
                return;
            }
            if (selected == null) {
                selected = entry;
            } else if (!selected.equals(entry)) {
                return;
            }
        }
        if (selected == null
                || loopMethod.equals(string(selected, "method"))) {
            return;
        }
        task.remove(LoopBoundPolicy.ROOT_AUTHORITY);
        task.remove(LoopBoundPolicy.ROOT_LOOP);
    }

    /** Promotes the one exact continuation shared by the selected output
     *  members, and re-addresses the accessor reads it re-bases. */
    private static void promoteSelectedReplayEntry(
            JsonObject task, OutputClosureContract closure) {
        if (closure == null) return;
        // A loop-body root replays one iteration of the service loop, so
        // every selected member of that body shares that continuation; the
        // per-member call continuations are not promoted (they would name
        // different calls of one body) and nothing is re-based.
        if (LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                string(task, LoopBoundPolicy.ROOT_AUTHORITY))) {
            return;
        }
        JsonObject selected = null;
        boolean missing = false;
        boolean conflicting = false;
        for (OutputClosureContract.Member member : closure.members()) {
            JsonObject entry = object(member.slice(), REPLAY_ENTRY);
            if (entry.size() == 0) {
                missing = true;
                continue;
            }
            if (string(entry, "method").isEmpty()
                    || string(entry, "receiverClass").isEmpty()) {
                throw new IllegalArgumentException(
                        "selected output replay entry is incomplete: "
                                + member.portId());
            }
            if (selected == null) {
                selected = entry.deepCopy();
            } else if (!selected.equals(entry)) {
                conflicting = true;
            }
        }
        if (selected == null) return;
        // One coarse occurrence may publish its selected outputs from several
        // frames of one activation -- a cached value written in the frame
        // that minted it and a wire leaf exported further down the same
        // dispatch. There is then no continuation the members share, so none
        // is promoted and nothing is re-based: the task replays from its own
        // root, exactly as a loop-body root already does above. Promoting one
        // member's frame would enter the occurrence past the others.
        if (conflicting || missing) return;
        JsonObject held = object(task, REPLAY_ENTRY);
        if (held.size() > 0 && !held.equals(selected)) {
            throw new IllegalArgumentException(
                    "selected output continuation conflicts with goal "
                            + "replay entry");
        }
        task.add(REPLAY_ENTRY, selected);
        // Repeated accessor reads are re-addressed from that continuation.
        for (JsonElement element : array(task, InputActionCatalog.FIELD)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            int localOccurrence = integer(action,
                    "helperActivationBoundedOccurrence", -1);
            if (localOccurrence > 0
                    && "SYMBOLIC".equals(string(action, "mode"))
                    && "FIELD_ACCESS".equals(string(action, "bindingMode"))
                    && !string(action, "accessorCallerMethod").isEmpty()
                    && !string(action,
                            "accessorImplementationMethod").isEmpty()) {
                action.addProperty("replayOccurrence", localOccurrence);
            }
        }
    }

    /**
     * Keeps only cut ports the selected task actually consumes or produces.
     * Copying every observed RPC parameter into every task instruments
     * unrelated payload and lets concrete service traffic grow the VM
     * expression session; the selected edge and closure are already the
     * task's complete interaction frontier.
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

    public String goalId() { return string(encoded, "goalId"); }

    public String taskId() { return string(encoded, "taskId"); }

    /**
     * Stable identity of the instrumentation owned by this plan row.  A
     * replay gets a new task id while the occurrence remains the same; goal
     * ids and capture alternatives are case-obligation labels inside the one
     * coarse result, so neither may create another injected root hook.
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

    /**
     * Which activation this task's region is rooted on. {@link
     * LoopBoundPolicy#LOOP_BODY_ROOT} names a region re-rooted at a service
     * loop's body, whose activation is one iteration rather than the one
     * entry above it; anything else leaves the root method's own entry.
     */
    public String rootAuthority() {
        return string(encoded, LoopBoundPolicy.ROOT_AUTHORITY);
    }

    /** True when this region's activation is one loop-body iteration. */
    public boolean loopBodyRoot() { return !rootLoopMethod.isEmpty(); }

    /** The method holding the loop body this region is rooted at, else "". */
    public String rootLoopMethod() { return rootLoopMethod; }

    /** Original unit index of that loop's dominance-proved header. */
    public int rootLoopHeaderUnitIndex() { return rootLoopHeaderUnitIndex; }

    /** Iteration-control sites the region's exits are installed on. */
    public Set<String> rootLoopControlSites() { return rootLoopControlSites; }

    /** The root loop's own {@code loopSiteId} -- the key its declared
     *  {@code K_L} is under in {@link #loopBound()} -- or "" for a
     *  non-loop-body region. */
    public String rootLoopSiteId() { return rootLoopSiteId; }

    /** Retained loops whose concrete cardinality is exact, not a {@code K_L}. */
    public Set<String> fixedCountLoopSites() { return fixedCountLoopSites; }

    private static Set<String> fixedCountLoopSites(JsonObject task) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(task, "retainedLoops")) {
            if (!element.isJsonObject()) continue;
            JsonObject loop = element.getAsJsonObject();
            if (!LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED.equals(string(loop,
                    LoopBoundPolicy.LOOP_CLASSIFICATION))) {
                continue;
            }
            String primary = string(loop, LoopBoundPolicy.LOOP_SITE_ID);
            if (!primary.isEmpty()) result.add(primary);
            result.addAll(textSet(loop,
                    LoopBoundPolicy.LOOP_CONTROL_SITE_IDS));
        }
        return Collections.unmodifiableSet(result);
    }

    /** Non-blank strings of a JSON array member, in wire order. */
    private static Set<String> textSet(JsonObject row, String field) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement element : array(row, field)) {
            if (!element.isJsonPrimitive()) continue;
            String value = element.getAsString().trim();
            if (!value.isEmpty()) result.add(value);
        }
        return Collections.unmodifiableSet(result);
    }

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

    /**
     * Where this occurrence hands a declared communication port to the VM.
     * An export site sends the port's live expression; an attach site takes
     * it.  The VM's successful attach and its {@code VALUE_HANDOFF} edge are
     * the whole value relation across the cut, so these sites declare where
     * the propagation happens and are never a pairing.
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

    public List<OutputCaptureSpec> outputCaptures() { return outputCaptures; }
}
