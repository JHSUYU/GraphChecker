package edu.uva.liftlab.graphchecker.d3.plan;


import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.plan.BranchReplayContract;
import edu.uva.liftlab.graphchecker.d3.plan.SharedExpressionTable;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/** Scheduled work for one causal-skeleton region occurrence. */
public final class ExecutionTask extends PlanRow {
    /**
     * How many tasks one campaign may contain.
     *
     * <p>A campaign has to be bounded to be a campaign: the instrumentation
     * pass rewrites every row and the runtime admits every row, so an
     * unbounded plan is a runaway workload rather than an experiment, and it
     * is refused by name instead of being started.</p>
     *
     * <p>The bound lives here because both ends of the plan check it -- the
     * Soot pass before the workload runs and the replay JVM as it loads the
     * same file -- and they were checking two copies of one constant against
     * one property name, with two copies of the parse.</p>
     */
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

    /** Write sites of a declared input's cell the replay must observe. */
    public static final String OBSERVED_WRITE_SITES = "observedWriteSites";
    /** Solver-selected concrete values for exact guarded primitive reads. */
    public static final String GUARDED_READ_ASSIGNMENTS =
            "guardedReadAssignments";

    private final InputActionCatalog inputActions;
    private final LoopBoundPolicy loopBound;
    private final String rootLoopMethod;
    private final int rootLoopHeaderUnitIndex;
    private final int rootLoopDemandedUnitIndex;
    private final String rootLoopSiteId;
    private final Set<String> rootLoopControlSites;
    private final Set<String> fixedCountLoopSites;
    private final Map<String, List<String>> exportConsumerOccurrences;
    private JsonElement expandedReplayContract;

    /** {@code bound} and {@code phases} are the values
     *  {@link #create} just encoded; a decoder passes null and the wire is
     *  parsed instead. */
    private ExecutionTask(JsonObject source, LoopBoundPolicy bound,
                          List<ConfiguredSourcePhaseContract.Occurrence>
                                  phases) {
        super(source, "execution task", false, phases);
        require(taskId(), "taskId");
        require(goalId(), "goalId");
        inputActions = InputActionCatalog.decode(encoded);
        loopBound = bound == null ? LoopBoundPolicy.decode(encoded) : bound;
        // The once-only-root rule: a region rooted on a service loop is
        // entered once per iteration, at the loop body rather than at the
        // frame above it.
        JsonObject rootLoop = LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                rootAuthority()) ? object(encoded, LoopBoundPolicy.ROOT_LOOP)
                : new JsonObject();
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
        exportConsumerOccurrences = exportConsumerOccurrences(this);
    }

    /**
     * The planned consumer occurrences of each outgoing communication port,
     * in the order the plan's edges name them.
     *
     * <p>A producer occurrence rooted at a loop body exports one value per
     * iteration onto one message, so one outgoing port legitimately has as
     * many planned consumer occurrences as the delivery carries values --
     * one per-element consumer occurrence on the receiving side.  What is
     * <em>not</em> legitimate is a port whose consumers sit on more than one
     * execution source: one message is sent to one peer, so a second source
     * means the plan has merged two deliveries into one export and neither
     * the envelope nor the attach could say which value belongs to which.
     * That is refused here, in the one decode both the PLAN stage
     * ({@link #create}) and the replay JVM ({@link #decode}) pass through,
     * so a plan the runtime could not execute never reaches REPLAY.</p>
     */
    private static Map<String, List<String>> exportConsumerOccurrences(
            ExecutionTask task) {
        Set<String> outgoing = new LinkedHashSet<>();
        for (CommunicationHandoffSpec site : task.communicationHandoffs()) {
            if (site.outgoing()) outgoing.add(site.portId());
        }
        if (outgoing.isEmpty()) {
            return Collections.emptyMap();
        }
        String producer = task.occurrenceId();
        Map<String, List<String>> byPort = new LinkedHashMap<>();
        for (JsonElement element : task.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String portId = optionalString(binding, "fromOutputPort");
            if (!"RUNTIME_PROTOCOL_FLOW".equals(
                    optionalString(binding, "kind"))
                    || !outgoing.contains(portId)
                    || !producer.equals(optionalString(
                            binding, "fromOccurrenceId"))) {
                continue;
            }
            String consumer = optionalString(binding, "toOccurrenceId");
            if (consumer.isEmpty()) continue;
            List<String> consumers = byPort.computeIfAbsent(portId,
                    ignored -> new ArrayList<String>());
            if (!consumers.contains(consumer)) {
                consumers.add(consumer);
            }
        }
        for (Map.Entry<String, List<String>> port : byPort.entrySet()) {
            Set<String> sources = new LinkedHashSet<>();
            for (String consumer : port.getValue()) {
                sources.add(sourceKeyOf(consumer));
            }
            if (sources.size() > 1) {
                throw new IllegalArgumentException(
                        "communication export port has consumer occurrences "
                                + "on more than one source in "
                                + task.taskId() + ": " + port.getKey() + " "
                                + sources);
            }
            port.setValue(Collections.unmodifiableList(port.getValue()));
        }
        return Collections.unmodifiableMap(byPort);
    }

    /**
     * The planned consumer occurrences of one outgoing port, empty when the
     * plan binds none.
     */
    public List<String> exportConsumerOccurrences(String portId) {
        List<String> consumers = exportConsumerOccurrences.get(
                portId == null ? "" : portId);
        return consumers == null ? Collections.<String>emptyList() : consumers;
    }

    public static ExecutionTask decode(JsonObject encoded) {
        if (encoded == null) {
            throw new IllegalArgumentException("execution task is required");
        }
        JsonObject portable = encoded.has(SharedExpressionTable.FIELD)
                ? SharedExpressionTable.compact(encoded)
                : encoded.deepCopy();
        return new ExecutionTask(portable, null, null);
    }

    /** Creates the one task for a scheduler-selected occurrence union. */
    public static ExecutionTask create(
            RegionInstancePlan.Goal goal,
            String taskId,
            JsonArray inputActions,
            JsonArray branches,
            JsonArray edgeBindings,
            LoopBoundPolicy loopBound) {
        if (goal == null || inputActions == null || branches == null
                || edgeBindings == null || loopBound == null) {
            throw new IllegalArgumentException(
                    "goal and task contract values are required");
        }
        JsonObject task = new JsonObject();
        goal.plan().writeTaskIdentityTo(task);
        goal.writeTaskPayloadTo(task);
        task.addProperty("taskId", taskId);
        goal.kind().writeToTask(task);
        task.add(InputActionCatalog.FIELD, compactInputActions(inputActions));
        task.add("branches", branches.deepCopy());
        loopBound.writeTo(task);
        if (edgeBindings.size() > 0) {
            task.add("edgeBindings", edgeBindings.deepCopy());
        }
        retainSelectedCommunicationHandoffs(task, edgeBindings);
        // A scheduled task is executable by construction: the scheduler
        // publishes the occurrences it selected, never ones it decided
        // against.  The state is still written, and still read back on
        // decode, because a decoded row is externally authored.
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return new ExecutionTask(task, loopBound,
                goal.plan().configuredSourcePhases());
    }

    /**
     * Keeps only cut ports the selected task actually consumes or produces.
     * Copying every observed RPC parameter into every task instruments
     * unrelated payload and lets concrete service traffic grow the VM
     * expression session; the selected edge and closure are already the
     * task's complete interaction frontier.
     */
    static void retainSelectedCommunicationHandoffs(
            JsonObject task, JsonArray edgeBindings) {
        JsonArray declared = array(task, CommunicationHandoffSpec.FIELD);
        if (declared.size() == 0) return;

        Set<String> selectedPorts = new LinkedHashSet<>();
        for (JsonElement element : edgeBindings) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            addPort(selectedPorts, optionalString(edge, "fromOutputPort"));
            addPort(selectedPorts, optionalString(edge, "toInputPort"));
        }
        JsonArray retained = new JsonArray();
        for (JsonElement element : declared) {
            if (!element.isJsonObject()) continue;
            JsonObject handoff = element.getAsJsonObject();
            String portId = optionalString(handoff,
                    CommunicationCatalogContract.PORT_ID);
            // An IN site is where this occurrence ATTACHES a value, which is
            // its own act and its own frontier whether or not a field-flow
            // edge happens to name the port.  The filter intersected
            // communication ports with edgeBindings' fromOutputPort /
            // toInputPort, which are field-flow ports, so a consumer's
            // attach sites were dropped: on hdfs-17899 bug3 the DataNode
            // task for REGION.16ba41cf declared resp.block-key-id with
            // side IN in its region plan and carried zero handoffs in its
            // execution task, so the attach it performed was read as an
            // UNPLANNED_HANDOFF fifteen times.
            if (selectedPorts.contains(portId)
                    || "IN".equals(optionalString(handoff, "side"))) {
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

    public String goalId() { return optionalString(encoded, "goalId"); }

    public String taskId() { return optionalString(encoded, "taskId"); }

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
                optionalString(object(encoded, "admission"), "state"));
    }

    public String rootMethod() {
        return optionalString(object(encoded, "rootSelector"), "method");
    }

    public String targetMethod() { return optionalString(encoded, "targetMethod"); }

    /**
     * Which activation this task's region is rooted on. {@link
     * LoopBoundPolicy#LOOP_BODY_ROOT} names a region re-rooted at a service
     * loop's body, whose activation is one iteration rather than the one
     * entry above it; anything else leaves the root method's own entry.
     */
    public String rootAuthority() {
        return optionalString(encoded, LoopBoundPolicy.ROOT_AUTHORITY);
    }

    /** The method holding the loop body this region is rooted at, else "". */
    public String rootLoopMethod() { return rootLoopMethod; }

    /** Original unit index of that loop's dominance-proved header. */
    public int rootLoopHeaderUnitIndex() { return rootLoopHeaderUnitIndex; }

    /** Original unit index the rooted loop body must reach. */
    public int rootLoopDemandedUnitIndex() {
        return rootLoopDemandedUnitIndex;
    }

    /** Iteration-control sites the region's exits are installed on. */
    public Set<String> rootLoopControlSites() { return rootLoopControlSites; }

    /** The root loop's own {@code loopSiteId} -- the key its declared
     *  {@code K_L} is under in {@link #loopBound()} -- or "" for a
     *  non-loop-body region. */
    public String rootLoopSiteId() { return rootLoopSiteId; }

    /** Retained loops whose concrete cardinality is exact, not a {@code K_L}. */
    public Set<String> fixedCountLoopSites() { return fixedCountLoopSites; }

    /** Exact retained-loop catalog carried unchanged from static analysis. */
    public JsonArray retainedLoops() {
        return array(encoded, "retainedLoops").deepCopy();
    }

    /** Loop-exit sites captured as boundary evidence even without an SMT PC. */
    public Set<String> loopExitSites() {
        Set<String> result = new LinkedHashSet<>();
        for (JsonElement encodedLoop : array(encoded, "retainedLoops")) {
            if (encodedLoop == null || !encodedLoop.isJsonObject()) continue;
            for (JsonElement encodedExit : array(
                    encodedLoop.getAsJsonObject(),
                    LoopBoundPolicy.LOOP_EXIT_DECISIONS)) {
                if (encodedExit != null && encodedExit.isJsonObject()) {
                    String site = optionalString(encodedExit.getAsJsonObject(),
                            "siteId");
                    if (!site.isEmpty()) result.add(site);
                }
            }
        }
        return Collections.unmodifiableSet(result);
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

    public JsonArray guardedReadAssignments() {
        return array(encoded, GUARDED_READ_ASSIGNMENTS).deepCopy();
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

    /**
     * The write sites of a declared region input's cell.
     *
     * <p>Scoping, not value: the VM retains a location by value, so a cell
     * nothing symbolic has reached yet keeps no version log and its stores
     * publish nothing.  These are the stores the replay must OBSERVE -- the
     * concrete value the field already holds becomes the location's first
     * expression -- so that every later write of it is a version a reader
     * can join to.  Each entry names a bytecode site and the cell it
     * writes; what the write did is the runtime's to state.</p>
     */
    public JsonArray observedWriteSites() {
        return array(encoded, OBSERVED_WRITE_SITES).deepCopy();
    }

    /** Concrete replay decisions, decoded without expanding predicates. */
    public BranchReplayContract.RuntimeSchedule replaySchedule() {
        JsonElement contract = encoded.get("replayContract");
        if (contract == null) return null;
        if (!contract.isJsonObject()) {
            throw new IllegalArgumentException(
                    "replayContract must be an object");
        }
        return BranchReplayContract.runtimeScheduleFromJson(
                contract.getAsJsonObject(), array(encoded,
                        "retainedLoops"));
    }

    /**
     * The component an occurrence id names: everything before its region.
     *
     * <p>One message is sent to one peer, so the component is what decides
     * whether two occurrences can be two consumers of one delivery. Read off
     * the id here rather than through an identity type, because the only
     * thing this asks of the id is where its region segment starts -- and
     * both the v1 and the v3 spelling put the component before it.</p>
     */
    private static String sourceKeyOf(String occurrenceId) {
        int region = occurrenceId.indexOf("/region/");
        return region <= 0 ? "" : occurrenceId.substring(0, region);
    }

}
