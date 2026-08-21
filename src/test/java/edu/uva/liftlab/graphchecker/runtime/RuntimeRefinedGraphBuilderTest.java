package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeRefinedGraphBuilderTest {
    private static final Gson GSON = new Gson();
    private static final String METHOD = "<example.Root: void run(example.A)>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /**
     * A refined edge is bound to the exact activations that produced it.
     *
     * <p>Inside one activation the binding names the selected access site and
     * the exact receiver object observed there.  It does not reconstruct an
     * arbitrary object path from the region root; the VM attaches state at
     * the selected access itself.</p>
     */
    @Test
    public void refinementBindsEdgesToTheExactActivationsThatRanThem()
            throws Exception {
        File candidate = write("candidate.jsonl", object(
                "schemaVersion", 3, "id", "DF.1",
                "kind", "field_read", "transferKind", "HEAP_READ",
                "method", METHOD, "unitIndex", 5,
                "fromCell", "<example.E: int f>", "toCell", "value"));
        File skeleton = write("skeleton.jsonl", object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", METHOD,
                "anchorMethod", METHOD,
                "methods", Collections.singletonList(METHOD)));
        RuntimeRegionPlanner.MethodEvent root =
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        1, METHOD, 0, "", 11, 0, 0);
        RuntimeRegionPlanner.RuntimeEvent argument =
                new RuntimeRegionPlanner.RuntimeEvent(2, "METHOD_ARGUMENT",
                        METHOD, 11, 0, 0, "", 0, "example.A", 10, "",
                        false, false);
        List<RuntimeRegionPlanner.FieldAccessEvent> fields = Arrays.asList(
                field(3, 1, "<example.A: example.B b>", 10, 20),
                field(4, 2, "<example.B: example.C c>", 20, 30),
                field(5, 3, "<example.C: example.D d>", 30, 40),
                field(6, 4, "<example.D: example.E e>", 40, 50),
                field(7, 5, "<example.E: int f>", 50, 0));
        File output = new File(folder.getRoot(), "refined.jsonl");

        RuntimeRefinedGraphBuilder.Result result =
                RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                        Collections.singletonList(activation("REGION.1", 11,
                                "STATE_CONTEXT", METHOD)),
                        Collections.singletonList(root),
                        Collections.singletonList(argument), fields,
                        Collections.emptyList(),
                        output.toPath());

        assertEquals(1, result.runtimeBoundEdgeCount);
        JsonObject edge = GSON.fromJson(Files.readAllLines(output.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        assertEquals("RUNTIME_REFINED_DATAFLOW",
                edge.get("graphKind").getAsString());
        JsonObject fieldBinding = edge.getAsJsonArray("runtimeFieldBindings")
                .get(0).getAsJsonObject();
        assertEquals(Collections.singletonList("f"),
                Collections.singletonList(
                        fieldBinding.getAsJsonArray("fieldPath").get(0)
                                .getAsString()));
        assertEquals(50, fieldBinding.get("rootObjectId").getAsInt());
        assertEquals(50,
                fieldBinding.get("fieldReceiverObjectId").getAsInt());
        assertEquals("EXACT_RUNTIME_ACTIVATION_FIELD_ACCESS_V1",
                fieldBinding.get("authority").getAsString());
        assertTrue(edge.get("runtimeObserved").getAsBoolean());
        assertFalse(edge.has("fieldPathDepth"));

    }

    private static RuntimeRegionPlanner.FieldAccessEvent field(
            long seq, int unit, String field, int receiver, int value) {
        return new RuntimeRegionPlanner.FieldAccessEvent(seq, "FIELD_READ",
                METHOD, 11, unit, METHOD + "#u" + unit, field, receiver,
                value, "");
    }

    private static Map<String, Object> activation(
            String region, long rootCallId, String selection,
            String method) {
        return object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "regionId", region,
                "rootCallId", rootCallId,
                "rootMethod", method,
                "selection", selection,
                "callIds", Collections.singletonList(rootCallId),
                "observedMethods", Collections.singletonList(method));
    }

    private File write(String name, Map<String, Object> row)
            throws Exception {
        return writeRows(name, row);
    }

    @SafeVarargs
    private final File writeRows(String name, Map<String, Object>... rows)
            throws Exception {
        File file = new File(folder.getRoot(), name);
        List<String> lines = new java.util.ArrayList<>();
        for (Map<String, Object> row : rows) {
            lines.add(GSON.toJson(row));
        }
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
