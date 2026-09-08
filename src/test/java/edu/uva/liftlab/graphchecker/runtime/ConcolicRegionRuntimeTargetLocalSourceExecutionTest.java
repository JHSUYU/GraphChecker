package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** Executes the combined target-local source and remote-attach replay shape. */
public class ConcolicRegionRuntimeTargetLocalSourceExecutionTest {
    private static final String TASK = "TASK.target-local-replay";
    private static final String OCCURRENCE =
            "test/client#epoch0/region/TARGET#1";
    private static final String VALUE_SOURCE_ID = "TARGET.LOCAL.VALUE";
    private static final String GATE_SOURCE_ID = "TARGET.LOCAL.GATE";
    private static final String ELEMENT_SOURCE_ID = "TARGET.LOCAL.ELEMENT";
    private static final String MAP_ELEMENT_SOURCE_ID =
            "TARGET.LOCAL.MAP_ELEMENT";
    private static final String VALUE_PORT = "TARGET.in.localValue";
    private static final String GATE_PORT = "TARGET.in.localGate";
    private static final String ELEMENT_PORT = "TARGET.in.elementValue";
    private static final String MAP_ELEMENT_PORT =
            "TARGET.in.mapElementValue";
    private static final String RPC_PORT = "XCH.remote.resp";
    private static final String ROOT = "<" + TargetState.class.getName()
            + ": void run()>";
    private static final String VALUE_FIELD = "<"
            + TargetState.class.getName() + ": int localValue>";
    private static final String GATE_FIELD = "<"
            + TargetState.class.getName() + ": int localGate>";
    private static final String ELEMENT_FIELD = "<"
            + ElementState.class.getName() + ": int value>";
    private static final String SOURCE_HOOK_CALLEE =
            "<example.SourceHook: boolean symbolize()>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private String previousPlan;
    private String previousTasks;
    private String previousResults;

    @Before
    public void rememberProperties() throws Exception {
        previousPlan = System.getProperty("causynth.concolic.task.plan");
        previousTasks = System.getProperty("causynth.concolic.task.id");
        previousResults = System.getProperty("causynth.concolic.results");
        ConcolicRegionRuntime.resetForTests();
        FakeVm.reset();
        installFakeEngine();
    }

    @After
    public void restoreProperties() {
        ConcolicRegionRuntime.resetForTests();
        restore("causynth.concolic.task.plan", previousPlan);
        restore("causynth.concolic.task.id", previousTasks);
        restore("causynth.concolic.results", previousResults);
    }

    @Test
    public void targetReplayAppliesLocalModelAndKeepsRemoteAttach()
            throws Exception {
        JsonObject task = task();
        Path plan = folder.newFile("target-local-plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("results.jsonl").toString());
        assertEquals(Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());

        TargetState receiver = new TargetState();
        Object active = activate(receiver, 71L);
        assertTrue(symbolize(
                VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        assertTrue(symbolize(
                GATE_SOURCE_ID, receiver, GATE_FIELD));
        assertTrue(symbolize(
                ELEMENT_SOURCE_ID, receiver.elements[0], ELEMENT_FIELD));
        // Wave 3: the second element is a second occurrence of the same
        // declared field, so it is its own symbolic variable.  The solver
        // model belongs to the first entry and is applied exactly once.
        assertTrue(symbolize(
                ELEMENT_SOURCE_ID, receiver.elements[1], ELEMENT_FIELD));
        assertEquals(9, receiver.localValue);
        assertEquals(4, receiver.localGate);
        assertEquals(6, receiver.elements[0].value);
        assertEquals(8, receiver.elements[1].value);

        acceptRemote(active, symbol("REMOTE.VALUE"));

        assertEquals(4, symbolicSources(active).size());
        assertEquals(1, vmHandoffs(active).size());
        assertEquals(RPC_PORT, vmHandoffs(active).get(0)
                .get("portId").getAsString());
        assertTrue(pathRecordingStarted(active));
        assertEquals(2, BranchReplayContract.fromJson(task.getAsJsonObject(
                "replayContract")).requiredPathPredicates().size());
    }

                                @Test
    public void appliedConfiguredModelsPassReplayTerminalGate()
            throws Exception {
        JsonObject task = task();
        Path plan = folder.newFile("target-local-applied-plan.jsonl")
                .toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        Path results = folder.getRoot().toPath().resolve(
                "applied-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());

        TargetState receiver = new TargetState();
        Object active = activate(receiver, 77L);
        ConcolicRegionRuntime.observeCausalSource("test/client#epoch0");
        assertTrue(symbolize(
                VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        assertTrue(symbolize(
                GATE_SOURCE_ID, receiver, GATE_FIELD));
        assertTrue(symbolize(
                ELEMENT_SOURCE_ID, receiver.elements[0], ELEMENT_FIELD));
        acceptRemote(active, symbol("REMOTE.VALUE"));
        completeReplayProgress(active, task);

        ConcolicRegionRuntime.exitRegion(77L, null, "");
        ConcolicRegionRuntime.awaitSelectedResultPublications();

        List<String> lines = Files.readAllLines(results,
                StandardCharsets.UTF_8);
        assertEquals(1, lines.size());
        JsonObject result = new JsonParser().parse(lines.get(0))
                .getAsJsonObject();
        assertEquals("CONCOLIC_REGION_RESULT",
                result.get("event").getAsString());
        assertFalse(result.has("skipKind"));
        assertEquals(3, SymbolicSourceEvidence.eventsOf(result).size());
    }

    @Test
    public void selectedMapValueFieldUsesOneExactOwnerAtTerminal()
            throws Exception {
        JsonObject task = taskWithMapSource();
        Path plan = folder.newFile("map-selected-plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        Path results = folder.getRoot().toPath().resolve(
                "map-selected-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());

        TargetState receiver = new TargetState();
        Object active = activate(receiver, 81L);
        ConcolicRegionRuntime.observeCausalSource("test/client#epoch0");
        assertTrue(symbolize(
                VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        assertTrue(symbolize(
                GATE_SOURCE_ID, receiver, GATE_FIELD));
        assertTrue(symbolize(
                ELEMENT_SOURCE_ID, receiver.elements[0], ELEMENT_FIELD));
        ElementState selected = receiver.elementsByKey.get("selected");
        ElementState other = receiver.elementsByKey.get("other");
        assertTrue(symbolize(
                MAP_ELEMENT_SOURCE_ID, selected, ELEMENT_FIELD));
        assertTrue(symbolize(
                MAP_ELEMENT_SOURCE_ID, other, ELEMENT_FIELD));
        assertEquals(11, selected.value);
        assertEquals(13, other.value);
        acceptRemote(active, symbol("REMOTE.VALUE"));
        completeReplayProgress(active, task);

        ConcolicRegionRuntime.exitRegion(81L, null, "");
        ConcolicRegionRuntime.awaitSelectedResultPublications();

        JsonObject result = new JsonParser().parse(Files.readAllLines(results,
                StandardCharsets.UTF_8).get(0)).getAsJsonObject();
        assertFalse(result.has("skipKind"));
        assertEquals(5, SymbolicSourceEvidence.eventsOf(result).size());
        assertTrue(result.toString(), result.toString().contains(
                MAP_ELEMENT_SOURCE_ID));
    }

    @Test
    public void absentInstanceScopedOutputNeedsCompletedCleanReplay()
            throws Exception {
        OutputCaptureSpec onceOnly = outputCapture(true);
        assertTrue(ConcolicRegionRuntime
                .replayAdmitsAbsentInstanceScopedOutput(onceOnly,
                        true, true, false, 0, false, false));
        assertFalse(ConcolicRegionRuntime
                .replayAdmitsAbsentInstanceScopedOutput(onceOnly,
                        false, true, false, 0, false, false));
        assertFalse(ConcolicRegionRuntime
                .replayAdmitsAbsentInstanceScopedOutput(onceOnly,
                        true, false, false, 0, false, false));
        assertFalse(ConcolicRegionRuntime
                .replayAdmitsAbsentInstanceScopedOutput(onceOnly,
                        true, true, true, 0, false, false));
        assertFalse(ConcolicRegionRuntime
                .replayAdmitsAbsentInstanceScopedOutput(onceOnly,
                        true, true, false, 1, false, false));
        assertFalse(ConcolicRegionRuntime
                .replayAdmitsAbsentInstanceScopedOutput(onceOnly,
                        true, true, false, 0, true, false));
        assertFalse(ConcolicRegionRuntime
                .replayAdmitsAbsentInstanceScopedOutput(onceOnly,
                        true, true, false, 0, false, true));
        assertFalse(ConcolicRegionRuntime
                .replayAdmitsAbsentInstanceScopedOutput(outputCapture(false),
                        true, true, false, 0, false, false));
    }

    @Test
    public void accessCarrierUsesOnlyTheFinalClaimantsReceiverLocator()
            throws Exception {
        JsonObject enteredPlan = task(false);
        JsonObject siblingPlan = task(false);
        siblingPlan.addProperty("taskId", "TASK.sibling-carrier");
        for (JsonElement element
                : siblingPlan.getAsJsonArray("inputActions")) {
            JsonObject action = element.getAsJsonObject();
            if (VALUE_FIELD.equals(action.has("accessFieldSignature")
                    ? action.get("accessFieldSignature").getAsString()
                    : "")) {
                action.addProperty("fieldReceiverObjectId", 916L);
            }
        }
        JsonObject declaration = new JsonObject();
        declaration.addProperty("kind", "INSTANCE_FIELD");
        declaration.addProperty("sourceKind",
                "ACTIVATION_FIELD_RECEIVER");
        declaration.addProperty("declaringClass",
                TargetState.class.getName());
        declaration.addProperty("fieldName", "localValue");
        declaration.addProperty("descriptor", "I");
        JsonArray carriers = new JsonArray();
        carriers.add(declaration);
        siblingPlan.add(ExecutionTask.SHARED_CARRIERS, carriers);

        Object entered = runtimeTask(enteredPlan);
        Object sibling = runtimeTask(siblingPlan);
        TargetState receiver = new TargetState();
        Object active = activate(receiver, 91L, entered);
        Field siblings = active.getClass().getDeclaredField(
                "siblingClaimants");
        siblings.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Object> siblingClaimants = (List<Object>) siblings.get(active);
        siblingClaimants.add(sibling);

        ConcolicRegionRuntime.selectFieldWriteCarrier(receiver, VALUE_FIELD);

        Field selected = active.getClass().getDeclaredField("sharedCarriers");
        selected.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<String, Object> selectedCarriers =
                (Map<String, Object>) selected.get(active);
        assertEquals(1, selectedCarriers.size());
        Object carrier = selectedCarriers.values().iterator().next();
        Field locator = carrier.getClass().getDeclaredField(
                "plannedReceiverObjectId");
        locator.setAccessible(true);
        assertEquals(916L, locator.getLong(carrier));

        Method bindFinal = ConcolicRegionRuntime.class.getDeclaredMethod(
                "bindSharedCarrierToFinalClaimant", active.getClass(),
                carrier.getClass());
        bindFinal.setAccessible(true);
        assertFalse((Boolean) bindFinal.invoke(null, active, carrier));
        assertEquals(0L, locator.getLong(carrier));

        Field activation = active.getClass().getDeclaredField("activation");
        activation.setAccessible(true);
        activation.set(active, sibling);
        assertTrue((Boolean) bindFinal.invoke(null, active, carrier));
        assertEquals(916L, locator.getLong(carrier));
    }

    private static OutputCaptureSpec outputCapture(boolean instanceScoped)
            throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("captureBindingId", "CAPTURE.once-only");
        encoded.addProperty("captureKind",
                OutputCaptureSpec.FIELD_WRITE_STATE);
        encoded.addProperty("outputPort", "TARGET.out.state");
        encoded.addProperty("outputCell", VALUE_FIELD);
        encoded.addProperty("fieldSignature", VALUE_FIELD);
        encoded.add("fieldPath", new JsonArray());
        encoded.addProperty("javaType", "int");
        encoded.addProperty("definitionMethod", ROOT);
        encoded.addProperty("definitionUnitIndex", 7);
        encoded.addProperty("outputSiteId", "FIELD_WRITE:" + ROOT + "#u7");
        encoded.addProperty("outputOccurrence", 1);
        encoded.addProperty("occurrenceScope",
                OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
        encoded.addProperty(OutputCaptureSpec.INSTANCE_SCOPED_PRODUCER,
                instanceScoped);
        Constructor<OutputCaptureSpec> constructor = OutputCaptureSpec.class
                .getDeclaredConstructor(JsonObject.class);
        constructor.setAccessible(true);
        return constructor.newInstance(encoded);
    }

    private static JsonObject task() {
        return task(true);
    }

    private static JsonObject task(boolean replay) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", TASK);
        task.addProperty("goalId", "GOAL.target-local-replay");
        task.addProperty("sourceKey", "test/client#epoch0");
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "RELATION.TARGET");
        task.addProperty("regionId", "TARGET");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", ROOT);
        selector.addProperty("receiverClass", TargetState.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "test/client#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);

        JsonObject local = new JsonObject();
        local.addProperty("mode", "CONCRETE");
        local.addProperty("portId", VALUE_PORT);
        local.addProperty("symbol", VALUE_PORT);
        local.addProperty("location", "HEAP_OBJECT_FIELD");
        local.addProperty("bindingMode", "FIELD_ACCESS");
        local.addProperty("javaType", "int");
        local.addProperty("accessFieldSignature", VALUE_FIELD);
        JsonObject gate = new JsonObject();
        gate.addProperty("mode", "CONCRETE");
        gate.addProperty("portId", GATE_PORT);
        gate.addProperty("symbol", GATE_PORT);
        gate.addProperty("location", "HEAP_OBJECT_FIELD");
        gate.addProperty("bindingMode", "FIELD_ACCESS");
        gate.addProperty("javaType", "int");
        gate.addProperty("accessFieldSignature", GATE_FIELD);
        JsonObject element = new JsonObject();
        element.addProperty("mode", "CONCRETE");
        element.addProperty("portId", ELEMENT_PORT);
        element.addProperty("symbol", ELEMENT_PORT);
        element.addProperty("location", "HEAP_OBJECT_FIELD");
        element.addProperty("bindingMode", "FIELD_ACCESS");
        element.addProperty("javaType", "int");
        element.addProperty("accessFieldSignature", ELEMENT_FIELD);
        JsonObject remote = new JsonObject();
        remote.addProperty("mode", "CONCRETE");
        remote.addProperty("portId", RPC_PORT);
        remote.addProperty("symbol", RPC_PORT);
        remote.addProperty("location", "CALL_RETURN");
        remote.addProperty("bindingMode", "LOCAL_DEFINITION");
        remote.addProperty("javaType", "int");
        remote.addProperty("symbolicDemand",
                "EXACT_INCOMING_COMPOSITION");
        remote.addProperty("selectedIncomingEdgeId", "EDGE.remote");
        JsonArray actions = new JsonArray();
        actions.add(local);
        actions.add(remote);
        actions.add(gate);
        actions.add(element);
        task.add("inputActions", actions);

        // Wave 3: mint SITES only; no selected-source rows travel with them.
        JsonArray sourcePhases = sourcePhases(VALUE_SOURCE_ID,
                GATE_SOURCE_ID, ELEMENT_SOURCE_ID);
        sourcePhases.add(sourcePhase(ELEMENT_SOURCE_ID, 2,
                sourceUnit(ELEMENT_SOURCE_ID) + 1L));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, sourcePhases);

        JsonArray assignments = new JsonArray();
        assignments.add(assignment(VALUE_SOURCE_ID, VALUE_FIELD, "9"));
        assignments.add(assignment(GATE_SOURCE_ID, GATE_FIELD, "4"));
        assignments.add(assignment(ELEMENT_SOURCE_ID, ELEMENT_FIELD, "6"));
        task.add("modelAssignments", assignments);

        JsonArray handoffs = new JsonArray();
        handoffs.add(responseAttach());
        task.add(CommunicationHandoffSpec.FIELD, handoffs);
        task.add("edgeBindings", new JsonArray());
        task.add("branches", new JsonArray());
        BranchWitness remotePrefix = witness("SITE.remote", 0,
                symbol("REMOTE.VALUE"));
        BranchWitness localPrefix = witness("SITE.local", 1,
                symbol("LOCAL.VALUE"));
        if (replay) {
            task.add("replayContract", BranchReplayContract.flip(
                    Collections.singletonList(remotePrefix), localPrefix)
                    .toJson());
        }
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return task;
    }

    private static JsonObject taskWithMapSource() {
        JsonObject task = task();
        JsonObject input = new JsonObject();
        input.addProperty("mode", "CONCRETE");
        input.addProperty("portId", MAP_ELEMENT_PORT);
        input.addProperty("symbol", MAP_ELEMENT_PORT);
        input.addProperty("location", "HEAP_OBJECT_FIELD");
        input.addProperty("bindingMode", "FIELD_ACCESS");
        input.addProperty("javaType", "int");
        input.addProperty("accessFieldSignature", ELEMENT_FIELD);
        task.getAsJsonArray("inputActions").add(input);
        task.getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD).add(
                sourcePhase(MAP_ELEMENT_SOURCE_ID));
        task.getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD).add(
                sourcePhase(MAP_ELEMENT_SOURCE_ID, 2,
                        sourceUnit(MAP_ELEMENT_SOURCE_ID) + 1L));
        task.getAsJsonArray("modelAssignments").add(assignment(
                MAP_ELEMENT_SOURCE_ID, ELEMENT_FIELD, "11"));
        return task;
    }

        private static JsonObject assignment(String sourceId,
                                         String fieldSignature,
                                         String value) {
        return assignment(sourceId, fieldSignature, value,
                sourcePhaseId(sourceId));
    }

    private static JsonObject assignment(String sourceId,
                                         String fieldSignature,
                                         String value,
                                         String sourcePhaseId) {
        int ownerEnd = fieldSignature.indexOf(": ");
        String owner = fieldSignature.substring(1, ownerEnd)
                .replace('.', '/');
        JsonObject assignment = new JsonObject();
        assignment.addProperty("modelAssignmentKey", "MODEL." + sourceId);
        assignment.addProperty("engineSymbol", "M_I_field_"
                + SymbolicSourceEvidence.engineLabelForPhase(
                sourcePhaseId, sourceId)
                + "_" + owner);
        assignment.addProperty("inputSymbol", "SOURCE_PHASE:"
                + sourcePhaseId);
        assignment.addProperty("configuredSourcePhaseId",
                sourcePhaseId);
        assignment.addProperty("configuredSourceId", sourceId);
        assignment.addProperty("configuredSourceFieldSignature",
                fieldSignature);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", value);
        return assignment;
    }

    private static JsonArray sourcePhases(String... sourceIds) {
        JsonArray result = new JsonArray();
        for (String sourceId : sourceIds) result.add(sourcePhase(sourceId));
        return result;
    }

    private static JsonObject sourcePhase(String sourceId) {
        return sourcePhase(sourceId, 1, sourceUnit(sourceId));
    }

    private static JsonObject sourcePhase(String sourceId, int ordinal,
                                          long eventSeq) {
        String field = MAP_ELEMENT_SOURCE_ID.equals(sourceId)
                || ELEMENT_SOURCE_ID.equals(sourceId)
                ? ELEMENT_FIELD
                : VALUE_SOURCE_ID.equals(sourceId) ? VALUE_FIELD : GATE_FIELD;
        JsonArray declared = new JsonArray();
        declared.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                sourceId, field, ROOT, sourceUnit(sourceId)));
        ConfiguredSourcePhaseContract.Declaration declaration =
                ConfiguredSourcePhaseContract.declarationsOf(declared).get(0);
        return ConfiguredSourcePhaseContract.occurrence(
                declaration, OCCURRENCE, ordinal, eventSeq, 1L,
                sourceUnit(sourceId) * 10L + ordinal, SOURCE_HOOK_CALLEE,
                Collections.singletonList(1L));
    }

    private static String sourcePhaseId(String sourceId) {
        return ConfiguredSourcePhaseContract.phaseId(OCCURRENCE,
                ROOT + "#u" + sourceUnit(sourceId),
                ConfiguredSourcePhaseContract.Phase.PUBLISH, 1);
    }

    private static int sourceUnit(String sourceId) {
        if (VALUE_SOURCE_ID.equals(sourceId)) return 10;
        if (GATE_SOURCE_ID.equals(sourceId)) return 20;
        if (ELEMENT_SOURCE_ID.equals(sourceId)) return 30;
        if (MAP_ELEMENT_SOURCE_ID.equals(sourceId)) return 40;
        throw new IllegalArgumentException("unknown source " + sourceId);
    }

    private static boolean symbolize(String sourceId, Object owner,
                                     String fieldSignature) {
        long call = CausynthTraceRecorder.enterMethod(ROOT, owner);
        long invocation = CausynthTraceRecorder.beginCall(call, ROOT,
                sourceUnit(sourceId), SOURCE_HOOK_CALLEE, null);
        try {
            return ConcolicRegionRuntime.symbolizeConfiguredSourceField(
                    sourceId, owner, fieldSignature);
        } finally {
            CausynthTraceRecorder.endCall(invocation, null, "");
            CausynthTraceRecorder.exitMethod(call, null, "");
        }
    }

    private static BranchWitness witness(
            String site, int index, JsonObject predicate) {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", index + 1L);
        event.addProperty("contextId", 7L);
        event.addProperty("predicateNormalization", "IDENTITY");
        return BranchWitness.vmPc(site, ROOT, index, 1, true,
                predicate, index, event);
    }

    private static JsonObject symbol(String raw) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", raw);
        return expression;
    }

    private static JsonObject responseAttach() {
        JsonObject site = new JsonObject();
        site.addProperty(CommunicationHandoffSpec.SIDE,
                CommunicationHandoffSpec.IN);
        site.addProperty(CommunicationHandoffSpec.CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_RETURN);
        site.addProperty("portId", RPC_PORT);
        site.addProperty("handoffLeafPath", "response/value");
        site.addProperty("direction", "RESPONSE");
        site.addProperty("javaType", "int");
        site.addProperty("definitionMethod", ROOT);
        site.addProperty("definitionUnitIndex", 50);
        site.addProperty("declaredCallee", SOURCE_HOOK_CALLEE);
        return site;
    }

    private static Object activate(TargetState receiver, long token)
            throws Exception {
        Field configurationField = ConcolicRegionRuntime.class
                .getDeclaredField("configuration");
        configurationField.setAccessible(true);
        Object configuration = configurationField.get(null);
        Method taskById = configuration.getClass().getDeclaredMethod(
                "taskById", String.class);
        taskById.setAccessible(true);
        Object task = taskById.invoke(configuration, TASK);
        return activate(receiver, token, task);
    }

    private static Object runtimeTask(JsonObject encoded) throws Exception {
        Class<?> taskType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$RuntimeTask");
        Constructor<?> constructor = taskType.getDeclaredConstructor(
                ExecutionTask.class);
        constructor.setAccessible(true);
        return constructor.newInstance(ExecutionTask.decode(encoded));
    }

    private static Object activate(TargetState receiver, long token,
                                   Object task) throws Exception {
        Class<?> activeType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$ActiveRegion");
        Constructor<?> constructor = activeType.getDeclaredConstructor(
                long.class, task.getClass(), Object.class, Thread.class);
        constructor.setAccessible(true);
        Object active = constructor.newInstance(token, task, receiver,
                Thread.currentThread());
        Field activeRegions = ConcolicRegionRuntime.class.getDeclaredField(
                "ACTIVE");
        activeRegions.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<Long, Object> regions =
                (Map<Long, Object>) activeRegions.get(null);
        regions.put(token, active);
        currentToken().set(token);
        ConcolicRegionRuntime.beginLiveSelectedRegion();
        return active;
    }

    @SuppressWarnings("unchecked")
    private static ThreadLocal<Long> currentToken() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField(
                "CURRENT_TOKEN");
        field.setAccessible(true);
        return (ThreadLocal<Long>) field.get(null);
    }

    private static CommunicationHandoffSpec communicationHandoff(
            Object active) throws Exception {
        Field activation = active.getClass().getDeclaredField("activation");
        activation.setAccessible(true);
        Object task = activation.get(active);
        Method lookup = task.getClass().getDeclaredMethod(
                "communicationHandoff", String.class, boolean.class);
        lookup.setAccessible(true);
        return (CommunicationHandoffSpec) lookup.invoke(task, RPC_PORT,
                false);
    }

    private static void acceptRemote(Object active, JsonElement expression)
            throws Exception {
        // README RPC-1: both endpoints of the VALUE_HANDOFF edge, as the
        // VM reported them on the one attach call.
        Method accept = ConcolicRegionRuntime.class.getDeclaredMethod(
                "acceptVmHandoffExpression", active.getClass(),
                CommunicationHandoffSpec.class, long.class, long.class,
                JsonElement.class, String.class, String.class);
        accept.setAccessible(true);
        accept.invoke(null, active, communicationHandoff(active), 41L, 42L,
                expression, "TASK.remote-producer",
                "test/server#epoch0/region/PRODUCER#1");
    }

    private static void completeReplayProgress(Object active, JsonObject task)
            throws Exception {
        Field replayProgress = active.getClass().getDeclaredField(
                "replayProgress");
        replayProgress.setAccessible(true);
        Object progress = replayProgress.get(active);
        Method observe = progress.getClass().getDeclaredMethod(
                "observe", String.class, int.class, boolean.class);
        observe.setAccessible(true);
        BranchReplayContract contract = BranchReplayContract.fromJson(
                task.getAsJsonObject("replayContract"));
        for (BranchWitness prefix : contract.orderedPrefix()) {
            assertFalse((Boolean) observe.invoke(progress, prefix.siteId(),
                    prefix.occurrence(), prefix.sourceTakenOutcome()));
        }
        BranchWitness source = contract.source();
        assertTrue((Boolean) observe.invoke(progress, source.siteId(),
                source.occurrence(), contract.requiredTakenOutcome()));
    }

    @SuppressWarnings("unchecked")
    private static Map<String, JsonObject> symbolicSources(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("symbolicSources");
        field.setAccessible(true);
        return (Map<String, JsonObject>) field.get(active);
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> vmHandoffs(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("vmHandoffEvents");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    private static boolean pathRecordingStarted(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField(
                "pathRecordingStarted");
        field.setAccessible(true);
        return field.getBoolean(active);
    }

    private static void installFakeEngine() throws Exception {
        Object engine = fakeEngineWithoutSharedState();
        bind(engine, "selectField", FakeVm.class.getDeclaredMethod(
                "selectSharedFieldCarrier", Object.class, String.class,
                String.class, String.class));
        bind(engine, "selectElement", FakeVm.class.getDeclaredMethod(
                "selectSharedElementCarrier", Object.class, int.class));
        bind(engine, "fieldVersions", FakeVm.class.getDeclaredMethod(
                "sharedFieldVersions", Object.class, String.class,
                String.class, String.class));
        bind(engine, "elementVersions", FakeVm.class.getDeclaredMethod(
                "sharedElementVersions", Object.class, int.class));
        bind(engine, "eventLedger", FakeVm.class.getDeclaredMethod(
                "eventLedger"));
        bind(engine, "activate", FakeVm.class.getDeclaredMethod(
                "activateEventLedger"));
        install(engine);
    }

    private static Object fakeEngineWithoutSharedState() throws Exception {
        Object engine = newEngine();
        bind(engine, "symbolizeExactField", FakeVm.class.getDeclaredMethod(
                "symbolizeExactField", Object.class, String.class,
                String.class, String.class, String.class));
        bind(engine, "getFieldExpression", FakeVm.class.getDeclaredMethod(
                "fieldExpression", Object.class, String.class, String.class,
                String.class, Object.class));
        bind(engine, "finishRegion", FakeVm.class.getDeclaredMethod("finish"));
        bind(engine, "pausePathCondition",
                FakeVm.class.getDeclaredMethod("pause"));
        bind(engine, "resumePathCondition",
                FakeVm.class.getDeclaredMethod("resume"));
        return engine;
    }

    /** A stock EngineApi with every VM method absent, for selective binding. */
    private static Object newEngine() throws Exception {
        Constructor<?> constructor = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$EngineApi")
                .getDeclaredConstructor();
        constructor.setAccessible(true);
        return constructor.newInstance();
    }

    private static void bind(Object engine, String name, Method target)
            throws Exception {
        Field field = engine.getClass().getDeclaredField(name);
        field.setAccessible(true);
        field.set(engine, target);
    }

    private static void install(Object engine) throws Exception {
        Field engineApi = ConcolicRegionRuntime.class.getDeclaredField(
                "engineApi");
        engineApi.setAccessible(true);
        engineApi.set(null, engine);
    }

    private static void restore(String property, String value) {
        if (value == null) {
            System.clearProperty(property);
        } else {
            System.setProperty(property, value);
        }
    }

    public static final class FakeVm {
        private static final Map<Object, Map<String, String>> LABELS =
                new IdentityHashMap<>();
        private static String refusedField = "";
        private static String malformedExpressionField = "";
        private static String compoundExpressionField = "";

        public static synchronized void reset() {
            LABELS.clear();
            refusedField = "";
            malformedExpressionField = "";
            compoundExpressionField = "";
        }

        /**
         * Makes this field read back the way a value COMPUTED from roots
         * elsewhere arrives: a tree with a root leaf inside it, and no bare
         * root of its own.
         */
        public static synchronized void compoundExpressionFor(String field) {
            compoundExpressionField = field;
        }

        public static synchronized void refuseField(String field) {
            refusedField = field;
        }

        public static synchronized void malformedExpressionFor(String field) {
            malformedExpressionField = field;
        }

        public static void pause() { }
        public static void resume() { }
        public static synchronized void symbolizeExactField(
                Object owner, String declaringClass, String field,
                String descriptor, String prefix) {
            if (field.equals(refusedField)) {
                throw new IllegalStateException("VM refused " + field);
            }
            Map<String, String> fields = LABELS.get(owner);
            if (fields == null) {
                fields = new java.util.LinkedHashMap<>();
                LABELS.put(owner, fields);
            }
            fields.put(declaringClass + "\n" + field + "\n" + descriptor,
                    prefix);
        }
        public static synchronized String fieldExpression(
                Object owner, String declaringClass, String field,
                String descriptor, Object value) {
            Map<String, String> fields = LABELS.get(owner);
            String symbol = fields == null ? null : fields.get(
                    declaringClass + "\n" + field + "\n" + descriptor);
            if (symbol == null) {
                throw new IllegalStateException(
                        "field expression requested before symbolization");
            }
            if (field.equals(malformedExpressionField)) {
                return "{\"expression\":{\"_type\":\"ConstExpr\","
                        + "\"_java_type\":\"I\",\"_exp\":\"Y_I_1\"}}";
            }
            String raw = "M_I_field_" + symbol + "_"
                    + declaringClass.replace('.', '/');
            if (field.equals(compoundExpressionField)) {
                return "{\"expression\":{\"_type\":\"BinaryExpression\","
                        + "\"_java_type\":\"I\",\"operation\":\"ADD\","
                        + "\"_left\":{\"_type\":\"SymbolExpression\","
                        + "\"_java_type\":\"I\",\"_exp\":\"" + raw
                        + "\"},\"_right\":{\"_type\":\"ConstExpr\","
                        + "\"_java_type\":\"I\",\"_exp\":\"Y_I_1\"}}}";
            }
            return "{\"expression\":{\"_type\":\"SymbolExpression\","
                    + "\"_java_type\":\"I\",\"_exp\":\"" + raw
                    + "\"}}";
        }
        public static long selectSharedFieldCarrier(
                Object owner, String declaringClass, String field,
                String descriptor) {
            return 1L;
        }
        public static long selectSharedElementCarrier(Object array, int index) {
            return 1L;
        }
        public static String sharedFieldVersions(
                Object owner, String declaringClass, String field,
                String descriptor) {
            long ownerId = (System.identityHashCode(owner) & 0x7fffffffL) + 1L;
            int slot = (field.hashCode() & 0x7fffffff) % 100_000 + 1;
            return versionEnvelope(ownerId, slot, fieldExpression(owner,
                    declaringClass, field, descriptor, Integer.valueOf(0)));
        }
        public static String sharedElementVersions(Object array, int index) {
            long ownerId = (System.identityHashCode(array) & 0x7fffffffL) + 1L;
            return versionEnvelope(ownerId, index + 1,
                    "{\"expression\":{\"_type\":\"ConstExpr\","
                            + "\"_java_type\":\"I\",\"_exp\":\"Y_I_0\"}}");
        }
        private static String versionEnvelope(
                long ownerId, int slot, String expression) {
            JsonObject value = new JsonParser().parse(expression)
                    .getAsJsonObject().getAsJsonObject("expression");
            JsonObject version = new JsonObject();
            version.addProperty("fieldVersionId", 1L);
            version.addProperty("versionKind", "INITIAL");
            version.addProperty("writerContextId", 1L);
            version.addProperty("fingerprintKind", "PRIMITIVE");
            version.addProperty("fingerprint", 0L);
            version.add("expression", value);
            version.add("pathGuard", null);
            JsonArray versions = new JsonArray();
            versions.add(version);
            JsonObject location = new JsonObject();
            location.addProperty("ownerSymRid", ownerId);
            location.addProperty("slot", slot);
            location.addProperty("locationKind", "INSTANCE_FIELD");
            JsonObject envelope = new JsonObject();
            envelope.addProperty("schemaVersion", 1);
            envelope.addProperty("kind", "SHARED_FIELD_VERSIONS");
            envelope.addProperty("selected", true);
            envelope.add("location", location);
            envelope.addProperty("writerSetComplete", true);
            envelope.add("versions", versions);
            envelope.add("reads", new JsonArray());
            return envelope.toString();
        }
        public static String eventLedger() {
            return "{\"schemaVersion\":1,"
                    + "\"kind\":\"SESSION_EVENT_LEDGER\","
                    + "\"open\":true,\"partialOrder\":true,"
                    + "\"acyclic\":true,\"domainSaturated\":false,"
                    + "\"truncated\":false,\"events\":[],\"order\":[]}";
        }
        public static boolean activateEventLedger() { return true; }
        public static String finish() {
            return "{\"schemaVersion\":1,"
                    + "\"kind\":\"CONCOLIC_REGION_SUMMARY\"}";
        }
    }

    private static final class TargetState {
        private int localValue = 1;
        private int localGate = 2;
        private final ElementState[] elements = {
                new ElementState(3), new ElementState(8)};
        private final Map<String, ElementState> elementsByKey =
                new LinkedHashMap<>();
        @SuppressWarnings("unused")
        private int remoteValue = 2;

        private TargetState() {
            elementsByKey.put("selected", new ElementState(5));
            elementsByKey.put("other", new ElementState(13));
        }
    }

    private static final class ElementState {
        private int value;

        private ElementState(int value) {
            this.value = value;
        }
    }
}
