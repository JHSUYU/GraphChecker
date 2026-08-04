package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicSchedulerTest {
    private static final Gson GSON = new Gson();

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void schedulerAcceptsOnlyRuntimeRefinedGraph() throws Exception {
        File regions = write("regions.jsonl", region());
        File plans = write("plans.jsonl", plan());
        File edges = writeEmpty("edges.jsonl");
        File refined = write("refined.jsonl", refinedEdge());
        File output = folder.newFolder("schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));
        assertEquals(1, result.executionTasks.size());

        Map<String, Object> candidate = refinedEdge();
        candidate.remove("refinementSchemaVersion");
        candidate.remove("graphKind");
        File candidateFile = write("candidate.jsonl", candidate);
        try {
            ConcolicScheduler.schedule(arguments(regions, plans, edges,
                    candidateFile, output));
            fail("candidate graph must be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("runtime-refined"));
        }
    }

    @Test
    public void schedulerComposesOnlySchemaThreeRuntimeFieldFlow() {
        Map<String, Object> binding = object(
                "schemaVersion", 3,
                "evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1",
                "fromRegionInstance", "REGION.2@test#call2",
                "toRegionInstance", "REGION.1@test#call1",
                "fromOutputPort", "REGION.2.out.value",
                "toInputPort", "REGION.1.in.value",
                "correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1",
                "receiverObjectId", 77,
                "writerEventSeq", 5,
                "readerEventSeq", 6);
        Map<String, Object> row = object(
                "schemaVersion", 3,
                "kind", "RUNTIME_FIELD_FLOW",
                "edgeId", "RF.1",
                "transportKind", "HEAP",
                "state", "CONFIRMED_RUNTIME_IDENTITY",
                "fromRegion", "REGION.2",
                "toRegion", "REGION.1",
                "fromPort", "REGION.2.out.value",
                "toPort", "REGION.1.in.value",
                "bindings", Collections.singletonList(binding));
        JsonObject edge = GSON.toJsonTree(row).getAsJsonObject();
        assertTrue(AutomaticRegionEdge.composable(edge));

        edge.addProperty("schemaVersion", 2);
        assertTrue(!AutomaticRegionEdge.composable(edge));
    }

    @Test
    public void outputClosureSymbolizesOnlyDemandedInputs() throws Exception {
        File regions = write("output-regions.jsonl", outputRegion());
        File plans = write("output-plans.jsonl", outputPlan());
        File edges = writeEmpty("output-edges.jsonl");
        File refined = write("output-refined.jsonl", refinedEdge());
        File output = folder.newFolder("output-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        assertEquals(1, result.executionTasks.size());
        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.demanded"));
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.unrelated"));
    }

    private ConcolicScheduler.Arguments arguments(
            File regions, File plans, File edges, File graph, File output) {
        return ConcolicScheduler.Arguments.parse(new String[]{
                "--regions", regions.getPath(),
                "--region-plan", plans.getPath(),
                "--edge-validations", edges.getPath(),
                "--refined-graph", graph.getPath(),
                "--output-dir", output.getPath()
        });
    }

    private static Map<String, Object> region() {
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.1",
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.emptyList());
    }

    private static Map<String, Object> outputRegion() {
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.1",
                "symbolicInputs", java.util.Arrays.asList(
                        port("REGION.1.in.demanded", "param0"),
                        port("REGION.1.in.unrelated", "param1")),
                "outputs", Collections.singletonList(
                        port("REGION.1.out.value", "result")));
    }

    private static Map<String, Object> plan() {
        Map<String, Object> occurrence = object("occurrence", 1,
                "outcome", false);
        Map<String, Object> branch = object("siteId", "<T: void f()>#u1",
                "policy", "EXPLORE", "requiredOutcome", false,
                "observed", true, "observedOutcome", false,
                "selectedOccurrence", 1,
                "occurrences", Collections.singletonList(occurrence));
        Map<String, Object> goal = object("goalId", "GOAL.1",
                "kind", "TARGET_REACH_CLOSURE",
                "runtimeDefinitionMethods",
                Collections.singletonList("<T: void f()>"),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", Collections.emptyList(),
                "branches", Collections.singletonList(branch),
                "edgeBindings", Collections.emptyList());
        return object("schemaVersion", 3, "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.1",
                "regionInstanceId", "REGION.1@test#call1",
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<T: void f()>", "ordinal", 1),
                "targetMethod", "<T: void f()>",
                "closureGoals", Collections.singletonList(goal));
    }

    private static Map<String, Object> outputPlan() {
        String method = "<T: void f(int,int)>";
        Map<String, Object> demanded = object(
                "symbol", "REGION.1.in.demanded",
                "cell", method + ".param0:int",
                "location", "ARGUMENT", "index", 0,
                "javaType", "int", "observed", true);
        Map<String, Object> unrelated = object(
                "symbol", "REGION.1.in.unrelated",
                "cell", method + ".param1:int",
                "location", "ARGUMENT", "index", 1,
                "javaType", "int", "observed", true);

        Map<String, Object> slice = object(
                "outputPort", "REGION.1.out.value",
                "outputCell", "result",
                "inputPorts", Collections.singletonList(
                        "REGION.1.in.demanded"),
                "sites", Collections.emptyList(),
                "staticSites", Collections.emptyList(),
                "methods", Collections.singletonList(method),
                "causalEdgeIds", Collections.emptyList(),
                "captureBindings", Collections.emptyList(),
                "captureBindingIssues", Collections.emptyList());
        Map<String, Object> member = object(
                "output", object("portId", "REGION.1.out.value",
                        "cell", "result", "kind", "REGION_OUTPUT",
                        "javaTypeDescriptor", "I"),
                "slice", slice);
        Map<String, Object> closure = object(
                "schemaVersion", 2,
                "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("regionId", "REGION.1",
                        "regionInstanceId", "REGION.1@test#call1",
                        "rootCallId", 1),
                "causalEdges", Collections.emptyList(),
                "members", Collections.singletonList(member));
        Map<String, Object> goal = object(
                "goalId", "GOAL.OUTPUT",
                "kind", "OUTPUT_RELATION_CLOSURE",
                "runtimeDefinitionMethods", Collections.singletonList(method),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", java.util.Arrays.asList(demanded, unrelated),
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.emptyList(),
                "outputClosure", closure);
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.1",
                "regionInstanceId", "REGION.1@test#call1",
                "rootCallId", 1,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", method, "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    private static Map<String, Object> port(String id, String cell) {
        return object("portId", id, "symbol", id, "cell", cell);
    }

    private static String mode(JsonArray actions, String symbol) {
        for (JsonElement element : actions) {
            JsonObject action = element.getAsJsonObject();
            if (symbol.equals(action.get("symbol").getAsString())) {
                return action.get("mode").getAsString();
            }
        }
        fail("missing input action " + symbol);
        return "";
    }

    private static Map<String, Object> refinedEdge() {
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.1", "kind", "exception_guard",
                "transferKind", "GUARD", "method", "<T: void f()>",
                "fromCell", "guard", "toCell", "exception");
    }

    private File write(String name, Map<String, Object> row)
            throws Exception {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), Collections.singletonList(GSON.toJson(row)),
                StandardCharsets.UTF_8);
        return file;
    }

    private File writeEmpty(String name) throws Exception {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), Collections.emptyList(),
                StandardCharsets.UTF_8);
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
