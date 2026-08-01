package edu.uva.liftlab.graphchecker.causynth;

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
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

public class RuntimeSelectedRegionFinalizerTest {
    private static final Gson GSON = new Gson();
    private static final String METHOD = "<example.Root: void run(example.A)>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void refinedGraphBecomesFullRegionState() throws Exception {
        File skeleton = write("skeleton.jsonl", object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", METHOD,
                "anchorMethod", METHOD,
                "methods", Collections.singletonList(METHOD),
                "selection", "EXCEPTION_COMPONENT"));
        Map<String, Object> binding = object(
                "rootCallId", 11, "rootKind", "PARAMETER",
                "rootCell", METHOD + ".param0:example.A",
                "rootParameterIndex", 0, "rootObjectId", 10,
                "fieldReceiverObjectId", 30, "valueObjectId", 0,
                "eventSeq", 9,
                "fieldPath", Arrays.asList("b", "c", "d"),
                "fieldPathDeclarations", Arrays.asList(
                        "<example.A: example.B b>",
                        "<example.B: example.C c>",
                        "<example.C: int d>"));
        File refined = write("refined.jsonl", object(
                "schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.1", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", METHOD,
                "regionIds", Collections.singletonList("REGION.1"),
                "runtimeFieldBindings", Collections.singletonList(binding)));
        File regions = new File(folder.getRoot(), "regions.jsonl");
        File edges = new File(folder.getRoot(), "edges.jsonl");

        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, edges, Collections.singleton(METHOD));

        JsonObject region = GSON.fromJson(Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        assertEquals(3, region.get("schemaVersion").getAsInt());
        assertEquals("SYMBOLIC_REGION", region.get("kind").getAsString());
        assertEquals(1, region.getAsJsonArray("symbolicInputs").size());
        assertEquals("b", region.getAsJsonArray("symbolicInputs")
                .get(0).getAsJsonObject().getAsJsonArray("fieldPath")
                .get(0).getAsString());
        assertFalse(region.has("planningMode"));
    }

    private File write(String name, Map<String, Object> row)
            throws Exception {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), Collections.singletonList(GSON.toJson(row)),
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
