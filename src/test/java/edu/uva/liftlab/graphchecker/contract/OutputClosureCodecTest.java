package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

public class OutputClosureCodecTest {
    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    @Test
    public void relationContractRoundTripsWithoutOccurrenceOrEdgeCopies()
            throws Exception {
        JsonObject artifact = artifact(singleton("out", "EDGE.1"));

        OutputClosureContract closure = OutputClosureCodec.decode(artifact);

        assertEquals(3, closure.toJson().get("schemaVersion").getAsInt());
        assertEquals("REL.1", closure.producer().relationKey());
        assertEquals("REGION.1", closure.producer().regionId());
        assertEquals(Arrays.asList("EDGE.1"), Arrays.asList(closure
                .executionScope().causalEdgeIds().toArray(new String[0])));
        assertFalse(closure.toJson().has("causalEdges"));
        assertFalse(closure.toJson().getAsJsonObject("producer")
                .has("regionInstanceId"));
        assertFalse(closure.toJson().getAsJsonObject("producer")
                .has("rootCallId"));

        JsonObject encoded = artifact.deepCopy();
        OutputClosureCodec.writeTo(encoded, closure);
        OutputClosureContract roundTrip = OutputClosureCodec.decode(encoded);
        assertEquals(closure.demandKey(), roundTrip.demandKey());
        assertEquals(closure.closureFingerprint(),
                roundTrip.closureFingerprint());

        JsonObject task = new JsonObject();
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);

        LoopBoundPolicy decodedPolicy = LoopBoundPolicy.decode(task);

        assertEquals(8, decodedPolicy.maxBackedgeTraversals());
        assertEquals("CFG_BACKEDGE:8:CUT_PATH", decodedPolicy.identity());
        // Raised on evidence: a demanded fixed-length container keeps every
        // one of its cells, and the loop bound is a separate contract.
        assertEquals(32,
                LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);

        JsonObject binding = binding("EDGE.1");
        JsonObject edge = binding.deepCopy();

        String encodedPlan = RuntimePlanArtifact.encode(
                Collections.singletonList(compactPlan(binding)),
                Collections.singletonList(edge),
                Collections.<JsonObject>emptyList());
        String[] rows = encodedPlan.trim().split("\\R");
        assertEquals(2, rows.length);
        JsonObject catalog = JsonParser.parseString(rows[0])
                .getAsJsonObject();
        JsonObject storedPlan = JsonParser.parseString(rows[1])
                .getAsJsonObject();
        assertEquals(RuntimePlanArtifact.CATALOG_KIND,
                catalog.get("kind").getAsString());
        assertFalse(storedPlan.has("occurrences"));
        JsonObject storedGoal = storedPlan.getAsJsonArray("closureGoals")
                .get(0).getAsJsonObject();
        assertFalse(storedGoal.has("edgeBindings"));
        assertEquals("EDGE.1", storedGoal
                .getAsJsonArray(RuntimePlanArtifact.EDGE_BINDING_IDS)
                .get(0).getAsString());

        Path file = temporary.newFile("runtime-plan.jsonl").toPath();
        Files.write(file, encodedPlan.getBytes(StandardCharsets.UTF_8));
        RuntimePlanArtifact decoded = RuntimePlanArtifact.read(file);
        JsonObject hydratedGoal = decoded.plans().get(0)
                .getAsJsonArray("closureGoals").get(0).getAsJsonObject();
        assertEquals(binding, hydratedGoal.getAsJsonArray("edgeBindings")
                .get(0).getAsJsonObject());
        assertEquals(1, decoded.edgeValidations().size());
    }

    @Test
    public void selectedOutputProjectionDropsUnrelatedProducerPhase() {
        OutputClosureContract first = singleton(
                "registration", "EDGE.registration",
                "REGION.1.in.registration", "<P: void register()>");
        OutputClosureContract second = singleton(
                "heartbeat", "EDGE.heartbeat",
                "REGION.1.in.heartbeat", "<P: void heartbeat()>");
        OutputClosureContract catalog = OutputClosureCodec.merge(
                Arrays.asList(first, second));

        OutputClosureContract selected = OutputClosureCodec.project(catalog,
                new LinkedHashSet<>(Collections.singletonList(
                        "REGION.1.out.heartbeat")));

        assertEquals(Collections.singleton("REGION.1.out.heartbeat"),
                selected.outputPorts());
        assertEquals(Collections.singleton("REGION.1.in.heartbeat"),
                selected.executionScope().inputPorts());
        assertEquals(Collections.singleton("<P: void heartbeat()>"),
                selected.executionScope().methods());
        assertEquals(Collections.singleton("EDGE.heartbeat"),
                selected.executionScope().causalEdgeIds());
    }

    private static JsonObject artifact(OutputClosureContract closure) {
        JsonObject result = new JsonObject();
        result.addProperty("sourceKey", "nn0#epoch1");
        result.addProperty("occurrenceId", "OCC.1");
        result.addProperty("relationKey", "REL.1");
        result.addProperty("regionId", "REGION.1");
        result.add(OutputClosureContract.FIELD, closure.toJson());
        return result;
    }

    private static OutputClosureContract singleton(
            String field, String edgeId) {
        return singleton(field, edgeId, "REGION.1.in.0",
                "<P: void run()>");
    }

    private static OutputClosureContract singleton(
            String field, String edgeId, String input, String method) {
        String port = "REGION.1.out." + field;
        String cell = "<P: int " + field + ">";
        return OutputClosureCodec.singleton("REL.1", "REGION.1", port, cell, "HEAP_STATE", "int",
                slice(port, cell, edgeId, input, method));
    }

    private static JsonObject slice(
            String port, String cell, String edgeId) {
        return slice(port, cell, edgeId, "REGION.1.in.0",
                "<P: void run()>");
    }

    private static JsonObject slice(
            String port, String cell, String edgeId,
            String input, String method) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", strings(input));
        slice.add("sites", strings(method + "#u1"));
        slice.add("staticSites", new JsonArray());
        slice.add("methods", strings(method));
        slice.add("causalEdgeIds", strings(edgeId));
        slice.add("captureBindingIssues", new JsonArray());

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE." + cell);
        capture.addProperty("captureKind",
                OutputCaptureSpec.REGION_EXIT_FIELD);
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("fieldSignature", cell);
        capture.add("fieldPath", strings(cell.substring(
                cell.lastIndexOf(' ') + 1, cell.length() - 1)));
        capture.addProperty("javaType", "int");
        capture.addProperty("accessRootInputPort", input);
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        return slice;
    }

    private static JsonObject compactPlan(JsonObject binding) {
        JsonObject input = new JsonObject();
        input.addProperty("portId", "REGION.1.in.value");
        input.addProperty("symbol", "REGION.1.in.value");
        input.addProperty("cell", "<T: int value>");
        input.addProperty("javaType", "int");
        input.addProperty("location", "HEAP_OBJECT_FIELD");
        input.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        input.addProperty("dependencyRole", "VALUE_FRONTIER");

        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL.1");
        goal.addProperty("kind", "TARGET_REACH_CLOSURE");
        JsonArray methods = new JsonArray();
        methods.add("<T: void run()>");
        goal.add("runtimeDefinitionMethods", methods);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        admission.add("blockers", new JsonArray());
        goal.add("admission", admission);
        JsonArray inputs = new JsonArray();
        inputs.add(input);
        goal.add("symbolize", inputs);
        goal.add("branches", new JsonArray());
        JsonArray edgeBindings = new JsonArray();
        edgeBindings.add(binding.deepCopy());
        goal.add("edgeBindings", edgeBindings);

        JsonObject plan = new JsonObject();
        plan.addProperty("schemaVersion", 3);
        plan.addProperty("kind", RuntimePlanArtifact.PLAN_KIND);
        plan.addProperty("sourceKey", "TEST_DRIVER/test#epoch0");
        plan.addProperty("occurrenceId", "TEST_DRIVER/test#epoch0/region/REGION.1#1");
        plan.addProperty("relationKey", "test/relation/REGION.1");
        plan.addProperty("regionId", "REGION.1");
        JsonArray goals = new JsonArray();
        goals.add(goal);
        plan.add("closureGoals", goals);
        return plan;
    }

    private static JsonObject binding(String edgeId) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromOccurrenceId", "TEST_DRIVER/test#epoch0/region/REGION.2#1");
        binding.addProperty("fromOutputPort", "REGION.2.out.value");
        binding.addProperty("toOccurrenceId", "TEST_DRIVER/test#epoch0/region/REGION.1#1");
        binding.addProperty("toInputPort", "REGION.1.in.value");
        return binding;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }
}
