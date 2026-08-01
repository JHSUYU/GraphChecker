package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class RuntimeRegionPlannerTest {
    private static final Gson GSON = new Gson();
    private static final String ROOT = "<example.Root: void run()>";
    private static final String TARGET = "<example.Target: void fail()>";
    private static final String WRITER = "<example.Writer: void update()>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void firstPassSelectsConcreteActivation() throws Exception {
        File skeletons = jsonl("skeletons.jsonl", skeleton());
        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(skeletons, methods());

        assertEquals(1, result.staticRegionCount);
        assertEquals(1, result.runtimeInstances.size());
        Map<String, Object> activation = result.runtimeInstances.get(0);
        assertEquals(1L, ((Number) activation.get("rootCallId")).longValue());
        assertEquals(Collections.singletonList("REGION.1"),
                activation.get("regionIds"));
        assertTrue(String.valueOf(activation.get("observedMethods"))
                .contains(TARGET));
    }

    @Test
    public void fullPlanningConsumesOnlyRefinedGraph() throws Exception {
        File regions = jsonl("regions.jsonl", fullRegion());
        File edges = jsonl("edges.jsonl");
        File candidate = jsonl("candidate.jsonl", candidateEdge());
        try {
            RuntimeRegionPlanner.plan(regions, edges, candidate, methods(),
                    runtime(), Collections.emptyList());
            fail("candidate graph must be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("runtime-refined"));
        }

        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("refined.jsonl", refined);
        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, methods(), runtime(),
                Collections.emptyList());
        assertEquals(1, result.regionPlans.size());
        Map<String, Object> plan = result.regionPlans.get(0);
        assertEquals(3, plan.get("schemaVersion"));
        assertEquals("CONCOLIC_REGION_PLAN", plan.get("kind"));
        assertTrue(String.valueOf(plan.get("closureGoals"))
                .contains("TARGET_REACH_CLOSURE"));
    }

    @Test
    public void fieldFlowIsBoundToExactRegionActivations() throws Exception {
        Map<String, Object> reader = fullRegion();
        reader.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.value", "cell", "reader",
                "fieldPath", Collections.singletonList("value"))));
        Map<String, Object> writer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.2", "rootMethod", WRITER,
                "anchorMethod", WRITER,
                "methods", Collections.singletonList(WRITER),
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.2.out.value", "cell", "writer",
                        "fieldPath", Collections.singletonList("value"))),
                "branchPolicies", Collections.emptyList());
        File regions = jsonl("flow-regions.jsonl", reader, writer);
        File edges = jsonl("flow-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.1",
                "fromRegion", "REGION.2", "toRegion", "REGION.1",
                "fromPort", "REGION.2.out.value",
                "toPort", "REGION.1.in.value",
                "fromRootCallId", 3, "toRootCallId", 1,
                "receiverObjectId", 77,
                "writerEventSeq", 5, "readerEventSeq", 6,
                "fieldPathDeclarations", Collections.singletonList(
                        "<example.State: int value>")));
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("flow-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = new ArrayList<>();
        events.add(new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                8, WRITER, 30, "example.Writer", 3, 0, 0));
        events.addAll(methods());

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, events, runtime(),
                Collections.emptyList());

        assertEquals(2, result.regionPlans.size());
        assertEquals(1, result.edgeValidations.size());
        Map<String, Object> validation = result.edgeValidations.get(0);
        assertEquals("CONFIRMED_RUNTIME_IDENTITY", validation.get("state"));
        assertTrue(String.valueOf(validation.get("bindings"))
                .contains("REGION.2@test#call3"));
        assertTrue(String.valueOf(validation.get("bindings"))
                .contains("REGION.1@test#call1"));
    }

    private static List<RuntimeRegionPlanner.MethodEvent> methods() {
        return Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0));
    }

    private static List<RuntimeRegionPlanner.RuntimeEvent> runtime() {
        return Collections.singletonList(new RuntimeRegionPlanner.RuntimeEvent(
                3, "BRANCH", TARGET, 2, 0, 0, TARGET + "#u4", -1,
                "", 0, "", true, false));
    }

    private static Map<String, Object> skeleton() {
        return object("schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", ROOT,
                "anchorMethod", TARGET, "methods", Arrays.asList(ROOT, TARGET),
                "selection", "EXCEPTION_COMPONENT");
    }

    private static Map<String, Object> fullRegion() {
        Map<String, Object> branch = object("siteId", TARGET + "#u4",
                "method", TARGET, "unitIndex", 4,
                "requiredOutcome", false, "policy", "EXPLORE");
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.1", "rootMethod", ROOT,
                "anchorMethod", TARGET, "methods", Arrays.asList(ROOT, TARGET),
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.emptyList(),
                "branchPolicies", Collections.singletonList(branch));
    }

    private static Map<String, Object> candidateEdge() {
        return object("schemaVersion", 3, "id", "DF.1",
                "kind", "exception_guard", "transferKind", "GUARD",
                "method", TARGET, "siteId", TARGET + "#u4",
                "fromCell", "guard", "toCell", "exception");
    }

    @SafeVarargs
    private final File jsonl(String name, Map<String, Object>... rows)
            throws Exception {
        List<String> lines = new ArrayList<>();
        for (Map<String, Object> row : rows) {
            lines.add(GSON.toJson(row));
        }
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), lines, StandardCharsets.UTF_8);
        return file;
    }

    private static Map<String, Object> object(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
        return result;
    }
}
