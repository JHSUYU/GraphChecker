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
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class RuntimePlanArtifactTest {
    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    @Test
    public void storesOneEdgeCatalogAndHydratesGoalBindings()
            throws Exception {
        JsonObject binding = binding("EDGE.1");
        JsonObject edge = binding.deepCopy();

        String encoded = RuntimePlanArtifact.encode(
                Collections.singletonList(compactPlan(binding)),
                Collections.singletonList(edge));
        String[] rows = encoded.trim().split("\\R");
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
        Files.write(file, encoded.getBytes(StandardCharsets.UTF_8));
        RuntimePlanArtifact decoded = RuntimePlanArtifact.read(file);
        JsonObject hydratedGoal = decoded.plans().get(0)
                .getAsJsonArray("closureGoals").get(0).getAsJsonObject();
        assertEquals(binding, hydratedGoal.getAsJsonArray("edgeBindings")
                .get(0).getAsJsonObject());
        assertEquals(1, decoded.edgeValidations().size());
    }

    @Test
    public void rejectsGoalBindingAbsentFromCatalog() {
        try {
            RuntimePlanArtifact.encode(
                    Collections.singletonList(compactPlan(
                            binding("EDGE.MISSING"))),
                    Collections.<JsonObject>emptyList());
            fail("unknown edge id must fail closed");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("edge catalog"));
        }
    }

    @Test
    public void storesOnlyCompactRegionPorts() throws Exception {
        JsonObject port = new JsonObject();
        port.addProperty("portId", "REGION.1.in.value");
        port.addProperty("cell", "<T: int value>");
        port.addProperty("javaType", "int");
        port.add("runtimeAccesses", new JsonArray());
        port.addProperty("plannerNoise", "drop");
        JsonObject region = new JsonObject();
        region.addProperty("schemaVersion", 3);
        region.addProperty("kind", "SYMBOLIC_REGION");
        region.addProperty("regionId", "REGION.1");
        JsonArray inputs = new JsonArray();
        inputs.add(port);
        region.add("symbolicInputs", inputs);
        region.add("outputs", new JsonArray());
        region.add("branchPolicies", new JsonArray());
        region.add("methods", new JsonArray());

        String encoded = RuntimePlanArtifact.encode(
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList(),
                Collections.singletonList(region));
        Path file = temporary.newFile("region-catalog.jsonl").toPath();
        Files.write(file, encoded.getBytes(StandardCharsets.UTF_8));
        JsonObject stored = RuntimePlanArtifact.read(file).regions().get(0);
        assertFalse(stored.has("branchPolicies"));
        assertFalse(stored.has("methods"));
        JsonObject storedPort = stored.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject();
        assertFalse(storedPort.has("plannerNoise"));
        assertFalse(storedPort.has("runtimeAccesses"));
        assertEquals("REGION.1.in.value",
                storedPort.get("portId").getAsString());
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
        plan.addProperty("regionId", "REGION.1");
        plan.addProperty("regionInstanceId", "REGION.1@test#call1");
        plan.addProperty("rootCallId", 1L);
        JsonArray goals = new JsonArray();
        goals.add(goal);
        plan.add("closureGoals", goals);
        return RegionInstancePlan.compactOccurrences(plan);
    }

    private static JsonObject binding(String edgeId) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromRegionInstance", "REGION.2@test#call2");
        binding.addProperty("fromOutputPort", "REGION.2.out.value");
        binding.addProperty("toRegionInstance", "REGION.1@test#call1");
        binding.addProperty("toInputPort", "REGION.1.in.value");
        return binding;
    }
}
