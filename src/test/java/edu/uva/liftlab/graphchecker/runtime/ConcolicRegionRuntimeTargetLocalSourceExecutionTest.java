package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

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
    private static final Gson GSON = new Gson();

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
        assertFalse(symbolize(
                ELEMENT_SOURCE_ID, receiver.elements[1], ELEMENT_FIELD));
        assertEquals(9, receiver.localValue);
        assertEquals(4, receiver.localGate);
        assertEquals(6, receiver.elements[0].value);
        assertEquals(8, receiver.elements[1].value);

        acceptRemote(active, symbol("REMOTE.VALUE"));

        assertEquals(3, symbolicSources(active).size());
        assertEquals(1, vmHandoffs(active).size());
        assertEquals(RPC_PORT, vmHandoffs(active).get(0)
                .get("portId").getAsString());
        assertTrue(pathRecordingStarted(active));
        assertEquals(2, BranchReplayContract.fromJson(task.getAsJsonObject(
                "replayContract")).requiredPathPredicates().size());
    }

    @Test
    public void selectedElementFieldSurvivesIntoTerminalSourceEvidence()
            throws Exception {
        JsonObject task = task(false);
        Path plan = folder.newFile("target-local-terminal-plan.jsonl")
                .toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        Path results = folder.getRoot().toPath().resolve(
                "terminal-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());

        TargetState receiver = new TargetState();
        Object active = activate(receiver, 73L);
        ConcolicRegionRuntime.observeCausalSource("test/client#epoch0");
        assertTrue(symbolize(
                VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        assertTrue(symbolize(
                GATE_SOURCE_ID, receiver, GATE_FIELD));
        assertTrue(symbolize(
                ELEMENT_SOURCE_ID, receiver.elements[0], ELEMENT_FIELD));
        acceptRemote(active, symbol("REMOTE.VALUE"));

        ConcolicRegionRuntime.exitRegion(73L, null, "");
        ConcolicRegionRuntime.awaitSelectedResultPublications();

        List<String> lines = Files.readAllLines(results,
                StandardCharsets.UTF_8);
        assertEquals(1, lines.size());
        JsonObject result = new JsonParser().parse(lines.get(0))
                .getAsJsonObject();
        assertEquals(TASK, result.get("taskId").getAsString());
        assertEquals(0, result.getAsJsonArray("unresolvedInputs").size());
        JsonArray phaseObservations = result.getAsJsonArray(
                ConcolicRegionRuntime.CONFIGURED_SOURCE_PHASE_OBSERVATIONS);
        assertEquals(3, phaseObservations.size());
        assertEquals(sourcePhaseId(VALUE_SOURCE_ID),
                phaseObservations.get(0).getAsJsonObject()
                        .get("matchedPhaseId").getAsString());
        assertEquals(sourcePhaseId(GATE_SOURCE_ID),
                phaseObservations.get(1).getAsJsonObject()
                        .get("matchedPhaseId").getAsString());
        assertEquals(sourcePhaseId(ELEMENT_SOURCE_ID),
                phaseObservations.get(2).getAsJsonObject()
                        .get("matchedPhaseId").getAsString());
        assertEquals(0, result.getAsJsonArray(
                ConcolicRegionRuntime.CONFIGURED_SOURCE_PHASE_GAPS).size());
        List<JsonObject> evidence = SymbolicSourceEvidence.eventsOf(result);
        assertEquals(3, evidence.size());
        Set<String> identities = new LinkedHashSet<>();
        for (JsonObject row : evidence) {
            assertEquals(OCCURRENCE,
                    row.get("sourceOccurrenceId").getAsString());
            assertTrue(row.get("rawSymbol").getAsString()
                    .startsWith("M_I_field_"));
            identities.add(row.get("sourceId").getAsString() + "\n"
                    + row.get("fieldSignature").getAsString());
        }
        assertTrue(identities.contains(VALUE_SOURCE_ID + "\n" + VALUE_FIELD));
        assertTrue(identities.contains(GATE_SOURCE_ID + "\n" + GATE_FIELD));
        assertTrue(identities.contains(
                ELEMENT_SOURCE_ID + "\n" + ELEMENT_FIELD));
        assertEquals(6, receiver.elements[0].value);
        assertEquals(8, receiver.elements[1].value);
    }

    @Test
    public void selectedSecondPublicationUsesCatalogOrdinalAndExtraFails()
            throws Exception {
        JsonObject task = taskWithOnlySecondValuePhase();
        loadTask(task, "selected-second");
        TargetState receiver = new TargetState();
        Object active = activate(receiver, 74L);

        assertFalse("known unselected first phase is a no-op",
                symbolize(VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        assertTrue("selected second phase materializes",
                symbolize(VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        List<JsonObject> observations = phaseObservations(active);
        assertEquals(2, observations.size());
        assertFalse(observations.get(0).get("selectedPhase").getAsBoolean());
        assertTrue(observations.get(1).get("selectedPhase").getAsBoolean());
        assertEquals(secondValuePhaseId(), observations.get(1)
                .get("matchedPhaseId").getAsString());
        assertEquals(0, phaseGaps(active).size());

        assertFalse("third execution is outside the frozen catalog",
                symbolize(VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        assertEquals(1, phaseGaps(active).size());
        assertEquals("EXTRA", phaseGaps(active).get(0)
                .get("gapKind").getAsString());
    }

    @Test
    public void missingSelectedSecondPublicationIsNamedAtTerminalCheck()
            throws Exception {
        JsonObject task = taskWithOnlySecondValuePhase();
        loadTask(task, "missing-second");
        TargetState receiver = new TargetState();
        Object active = activate(receiver, 76L);
        assertFalse(symbolize(VALUE_SOURCE_ID, receiver, VALUE_FIELD));

        Method validate = active.getClass().getDeclaredMethod(
                "validateConfiguredSourcePhases");
        validate.setAccessible(true);
        validate.invoke(active);
        assertEquals(1, phaseGaps(active).size());
        assertEquals("MISSING", phaseGaps(active).get(0)
                .get("gapKind").getAsString());
        assertEquals(secondValuePhaseId(), phaseGaps(active).get(0)
                .get("phaseId").getAsString());
    }

    @Test
    public void reorderedSelectedPublicationsAreRecordedAndFailClosed()
            throws Exception {
        JsonObject task = task(false);
        loadTask(task, "reordered-selected");
        TargetState receiver = new TargetState();
        Object active = activate(receiver, 78L);

        assertTrue(symbolize(GATE_SOURCE_ID, receiver, GATE_FIELD));
        assertTrue(symbolize(VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        assertTrue(symbolize(ELEMENT_SOURCE_ID, receiver.elements[0],
                ELEMENT_FIELD));

        List<JsonObject> observations = phaseObservations(active);
        assertEquals(3, observations.size());
        assertEquals(sourcePhaseId(GATE_SOURCE_ID), observations.get(0)
                .get("matchedPhaseId").getAsString());
        assertFalse(observations.get(0).get("orderMatched").getAsBoolean());
        assertEquals(sourcePhaseId(VALUE_SOURCE_ID), observations.get(1)
                .get("matchedPhaseId").getAsString());
        assertEquals(sourcePhaseId(ELEMENT_SOURCE_ID), observations.get(2)
                .get("matchedPhaseId").getAsString());
        assertEquals(1, phaseGaps(active).size());
        assertEquals("REORDERED", phaseGaps(active).get(0)
                .get("gapKind").getAsString());
    }

    @Test
    public void vmRefusalLeavesConfiguredModelUnappliedAtTerminal()
            throws Exception {
        JsonObject task = task();
        Path plan = folder.newFile("target-local-refusal-plan.jsonl")
                .toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        Path results = folder.getRoot().toPath().resolve(
                "refusal-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());

        TargetState receiver = new TargetState();
        Object active = activate(receiver, 75L);
        ConcolicRegionRuntime.observeCausalSource("test/client#epoch0");
        FakeVm.refuseField("localValue");
        assertFalse(symbolize(
                VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        FakeVm.refuseField("");
        assertTrue(symbolize(
                GATE_SOURCE_ID, receiver, GATE_FIELD));
        assertTrue(symbolize(
                ELEMENT_SOURCE_ID, receiver.elements[0], ELEMENT_FIELD));
        acceptRemote(active, symbol("REMOTE.VALUE"));
        completeReplayProgress(active, task);

        ConcolicRegionRuntime.exitRegion(75L, null, "");
        ConcolicRegionRuntime.awaitSelectedResultPublications();

        List<String> lines = Files.readAllLines(results,
                StandardCharsets.UTF_8);
        assertEquals(1, lines.size());
        JsonObject skipped = new JsonParser().parse(lines.get(0))
                .getAsJsonObject();
        assertEquals(ConcolicRegionRuntime.SKIP_UNAPPLIED_MODEL_ASSIGNMENT,
                skipped.get("skipKind").getAsString());
        assertTrue(skipped.get("reason").getAsString()
                .contains("MODEL." + VALUE_SOURCE_ID));
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
    public void engineSymbolAloneKeysSolverAssignmentsAtRuntime()
            throws Exception {
        JsonObject task = task();
        for (JsonElement element : task.getAsJsonArray("modelAssignments")) {
            element.getAsJsonObject().remove("modelAssignmentKey");
        }
        Path plan = folder.newFile("engine-symbol-plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        Path results = folder.getRoot().toPath().resolve(
                "engine-symbol-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());

        TargetState receiver = new TargetState();
        Object active = activate(receiver, 79L);
        ConcolicRegionRuntime.observeCausalSource("test/client#epoch0");
        assertTrue(symbolize(
                VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        assertTrue(symbolize(
                GATE_SOURCE_ID, receiver, GATE_FIELD));
        assertTrue(symbolize(
                ELEMENT_SOURCE_ID, receiver.elements[0], ELEMENT_FIELD));
        acceptRemote(active, symbol("REMOTE.VALUE"));
        completeReplayProgress(active, task);

        ConcolicRegionRuntime.exitRegion(79L, null, "");
        ConcolicRegionRuntime.awaitSelectedResultPublications();

        List<String> lines = Files.readAllLines(results,
                StandardCharsets.UTF_8);
        assertEquals(1, lines.size());
        JsonObject result = new JsonParser().parse(lines.get(0))
                .getAsJsonObject();
        assertEquals("CONCOLIC_REGION_RESULT",
                result.get("event").getAsString());
        assertEquals(0, result.getAsJsonArray("unresolvedInputs").size());
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
        assertFalse(symbolize(
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
        assertEquals(4, SymbolicSourceEvidence.eventsOf(result).size());
        assertTrue(result.toString(), result.toString().contains(
                MAP_ELEMENT_SOURCE_ID));
    }

    @Test
    public void malformedFieldExpressionLeavesModelUnapplied()
            throws Exception {
        JsonObject task = task();
        Path plan = folder.newFile("malformed-expression-plan.jsonl")
                .toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        Path results = folder.getRoot().toPath().resolve(
                "malformed-expression-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());

        TargetState receiver = new TargetState();
        Object active = activate(receiver, 83L);
        ConcolicRegionRuntime.observeCausalSource("test/client#epoch0");
        FakeVm.malformedExpressionFor("localValue");
        assertFalse(symbolize(
                VALUE_SOURCE_ID, receiver, VALUE_FIELD));
        FakeVm.malformedExpressionFor("");
        assertTrue(symbolize(
                GATE_SOURCE_ID, receiver, GATE_FIELD));
        assertTrue(symbolize(
                ELEMENT_SOURCE_ID, receiver.elements[0], ELEMENT_FIELD));
        acceptRemote(active, symbol("REMOTE.VALUE"));
        completeReplayProgress(active, task);

        ConcolicRegionRuntime.exitRegion(83L, null, "");
        ConcolicRegionRuntime.awaitSelectedResultPublications();

        JsonObject skipped = new JsonParser().parse(Files.readAllLines(results,
                StandardCharsets.UTF_8).get(0)).getAsJsonObject();
        assertEquals(ConcolicRegionRuntime.SKIP_UNAPPLIED_MODEL_ASSIGNMENT,
                skipped.get("skipKind").getAsString());
        assertTrue(skipped.get("reason").getAsString()
                .contains("MODEL." + VALUE_SOURCE_ID));
    }

    @Test
    public void rejectsNonArrayModelAssignmentsWhileLoadingPlan()
            throws Exception {
        JsonObject task = task();
        task.add("modelAssignments", new JsonObject());
        Path plan = folder.newFile("non-array-assignments-plan.jsonl")
                .toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(
                        "non-array-results.jsonl").toString());

        try {
            ConcolicRegionRuntime.campaignTaskIdsForTests();
            fail("non-array modelAssignments was accepted");
        } catch (IllegalStateException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "modelAssignments must be an array"));
        }
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

        JsonArray sources = new JsonArray();
        sources.add(source(VALUE_SOURCE_ID, VALUE_FIELD, VALUE_PORT));
        sources.add(source(GATE_SOURCE_ID, GATE_FIELD, GATE_PORT));
        sources.add(source(ELEMENT_SOURCE_ID, ELEMENT_FIELD, ELEMENT_PORT));
        task.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        JsonArray sourcePhases = sourcePhases(VALUE_SOURCE_ID,
                GATE_SOURCE_ID, ELEMENT_SOURCE_ID);
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, sourcePhases);
        task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD,
                selectedSourcePhases(sourcePhases));

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
        task.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD).add(
                source(MAP_ELEMENT_SOURCE_ID, ELEMENT_FIELD,
                        MAP_ELEMENT_PORT));
        task.getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD).add(
                sourcePhase(MAP_ELEMENT_SOURCE_ID));
        task.getAsJsonArray(
                ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD).add(
                sourcePhaseId(MAP_ELEMENT_SOURCE_ID));
        task.getAsJsonArray("modelAssignments").add(assignment(
                MAP_ELEMENT_SOURCE_ID, ELEMENT_FIELD, "11"));
        return task;
    }

    private JsonObject loadTask(JsonObject task, String name)
            throws Exception {
        Path plan = folder.newFile(name + "-plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(name + "-results.jsonl")
                        .toString());
        assertEquals(Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());
        return task;
    }

    /** Full two-row catalog with only the second source version selected. */
    private static JsonObject taskWithOnlySecondValuePhase() {
        JsonObject task = task(false);
        JsonArray phases = new JsonArray();
        phases.add(sourcePhase(VALUE_SOURCE_ID, 1, 10L));
        phases.add(sourcePhase(VALUE_SOURCE_ID, 2, 11L));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        JsonArray selected = new JsonArray();
        selected.add(secondValuePhaseId());
        task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD, selected);

        JsonObject valueSource = task.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).get(0).getAsJsonObject();
        valueSource.addProperty("sourcePhaseId", secondValuePhaseId());
        JsonArray sources = new JsonArray();
        sources.add(valueSource);
        task.add(SymbolicSourceEvidence.TASK_FIELD, sources);

        JsonObject valueAssignment = assignment(VALUE_SOURCE_ID,
                VALUE_FIELD, "9", secondValuePhaseId());
        JsonArray assignments = new JsonArray();
        assignments.add(valueAssignment);
        task.add("modelAssignments", assignments);
        return task;
    }

    private static JsonObject source(String sourceId, String fieldSignature,
                                     String targetInputPort) {
        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourceId", sourceId);
        source.addProperty("sourcePhaseId", sourcePhaseId(sourceId));
        source.addProperty("fieldSignature", fieldSignature);
        source.addProperty("requiredTargetInputPort", targetInputPort);
        return source;
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

    private static JsonArray selectedSourcePhases(JsonArray phases) {
        JsonArray selected = new JsonArray();
        for (JsonElement phase : phases) {
            selected.add(phase.getAsJsonObject().get("phaseId")
                    .getAsString());
        }
        return selected;
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
        ConfiguredSourcePhaseContract.Declaration declaration =
                ConfiguredSourcePhaseContract.declarationsOf(
                        Collections.singletonList(
                                ConfiguredSourcePhaseContract.declaration(
                                        ConfiguredSourcePhaseContract.Phase
                                                .PUBLISH,
                                        sourceId, field, ROOT,
                                        sourceUnit(sourceId)))).get(0);
        return GSON.toJsonTree(ConfiguredSourcePhaseContract.occurrence(
                declaration, OCCURRENCE, ordinal, eventSeq, 1L,
                sourceUnit(sourceId) * 10L + ordinal, SOURCE_HOOK_CALLEE,
                Collections.singletonList(1L))).getAsJsonObject();
    }

    private static String sourcePhaseId(String sourceId) {
        return ConfiguredSourcePhaseContract.phaseId(OCCURRENCE,
                ROOT + "#u" + sourceUnit(sourceId),
                ConfiguredSourcePhaseContract.Phase.PUBLISH, 1);
    }

    private static String secondValuePhaseId() {
        return ConfiguredSourcePhaseContract.phaseId(OCCURRENCE,
                ROOT + "#u" + sourceUnit(VALUE_SOURCE_ID),
                ConfiguredSourcePhaseContract.Phase.PUBLISH, 2);
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
        site.addProperty("schemaVersion", 1);
        site.addProperty("kind", CommunicationHandoffSpec.KIND);
        site.addProperty("role", CommunicationHandoffSpec.ROLE_ATTACH);
        site.addProperty("portId", RPC_PORT);
        site.addProperty("handoffLeafPath", "response/value");
        site.addProperty("direction", "RESPONSE");
        site.addProperty("javaType", "int");
        site.addProperty("exchangeSiteKey", "XCH.remote");
        site.addProperty("componentOfPortId", "XCH.remote.response");
        site.addProperty("encodingAuthority", "TEST_ENCODING_V1");
        site.addProperty("manualCarrierClass", TargetState.class.getName());
        site.addProperty("manualCarrierField", "remoteValue");
        site.addProperty("manualCarrierDescriptor", "I");
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
        Method accept = ConcolicRegionRuntime.class.getDeclaredMethod(
                "acceptVmHandoffExpression", active.getClass(),
                CommunicationHandoffSpec.class, long.class,
                JsonElement.class, String.class, String.class);
        accept.setAccessible(true);
        accept.invoke(null, active, communicationHandoff(active), 41L,
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

    @SuppressWarnings("unchecked")
    private static List<JsonObject> phaseObservations(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField(
                "configuredSourcePhaseObservations");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> phaseGaps(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField(
                "configuredSourcePhaseGaps");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    private static void installFakeEngine() throws Exception {
        Class<?> type = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$EngineApi");
        Constructor<?> constructor = type.getDeclaredConstructors()[0];
        constructor.setAccessible(true);
        Object[] arguments = new Object[constructor.getParameterCount()];
        arguments[6] = FakeVm.class.getDeclaredMethod("symbolizeExactField",
                Object.class, String.class, String.class, String.class,
                String.class);
        arguments[11] = FakeVm.class.getDeclaredMethod("fieldExpression",
                Object.class, String.class, String.class, String.class,
                Object.class);
        arguments[12] = FakeVm.class.getDeclaredMethod("finish");
        arguments[14] = FakeVm.class.getDeclaredMethod("pause");
        arguments[15] = FakeVm.class.getDeclaredMethod("resume");
        Field engine = ConcolicRegionRuntime.class.getDeclaredField(
                "engineApi");
        engine.setAccessible(true);
        engine.set(null, constructor.newInstance(arguments));
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

        public static synchronized void reset() {
            LABELS.clear();
            refusedField = "";
            malformedExpressionField = "";
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
            return "{\"expression\":{\"_type\":\"SymbolExpression\","
                    + "\"_java_type\":\"I\",\"_exp\":\"" + raw
                    + "\"}}";
        }
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
