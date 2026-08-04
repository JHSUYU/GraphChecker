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
import static org.junit.Assert.assertTrue;

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
                "regionId", "REGION.1",
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

    @Test
    public void fieldBindingIsUsedOnlyByItsConcreteRegionActivation()
            throws Exception {
        File skeleton = writeRows("overlap-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.1", "rootMethod", METHOD,
                        "anchorMethod", METHOD,
                        "methods", Collections.singletonList(METHOD)),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.2", "rootMethod", METHOD,
                        "anchorMethod", METHOD,
                        "methods", Collections.singletonList(METHOD)));
        Map<String, Object> binding = object(
                "regionId", "REGION.1", "rootCallId", 11,
                "rootKind", "RECEIVER", "rootCell", METHOD + ".receiver",
                "rootObjectId", 10, "fieldReceiverObjectId", 10,
                "valueObjectId", 20, "eventSeq", 9,
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations", Collections.singletonList(
                        "<example.Root: example.A value>"));
        File refined = write("overlap-refined.jsonl", object(
                "schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.2", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", METHOD,
                "regionIds", Arrays.asList("REGION.1", "REGION.2"),
                "runtimeFieldBindings", Collections.singletonList(binding)));
        File regions = new File(folder.getRoot(), "overlap-regions.jsonl");
        File edges = new File(folder.getRoot(), "overlap-edges.jsonl");

        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, edges, Collections.singleton(METHOD));

        java.util.List<String> rows = Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8);
        JsonObject first = GSON.fromJson(rows.get(0), JsonObject.class);
        JsonObject second = GSON.fromJson(rows.get(1), JsonObject.class);
        assertEquals(1, first.getAsJsonArray("symbolicInputs").size());
        assertEquals(0, second.getAsJsonArray("symbolicInputs").size());
    }

    @Test
    public void freezesIteratorLoopGuardButExploresSemanticBodyGuard()
            throws Exception {
        File skeleton = skeleton("branch-skeleton.jsonl");
        String iterator = METHOD + "::$iterator";
        String hasNext = METHOD + "::$hasNext";
        String comparison = METHOD + "::$comparison";
        String loopSite = METHOD + "#u6";
        String semanticSite = METHOD + "#u14";

        File refined = writeRows("branch-refined.jsonl",
                refinedEdge("DF.iterator", "container_receiver",
                        "MODEL_TRANSFORM", iterator, hasNext,
                        METHOD + "#u5", 5,
                        "$hasNext = interfaceinvoke $iterator."
                                + "<java.util.Iterator: boolean hasNext()>()",
                        "<java.util.Iterator: boolean hasNext()>",
                        null, null, false),
                refinedEdge("DF.loop", "path_guard_dependency", "GUARD",
                        hasNext, hasNext, loopSite, 6,
                        "if $hasNext == 0 goto return", null,
                        loopSite, false, true),
                refinedEdge("DF.loop.consume", "guard_dependency", "GUARD",
                        hasNext, loopSite, loopSite, 6,
                        "if $hasNext == 0 goto return", null,
                        loopSite, null, false),
                refinedEdge("DF.semantic", "guard_dependency", "GUARD",
                        comparison, semanticSite, semanticSite, 14,
                        "if $comparison >= 0 goto branch", null,
                        semanticSite, false, false));
        JsonObject region = finalizeOne(refined, skeleton,
                "branch-regions.jsonl", "branch-edges.jsonl");

        JsonObject loop = branch(region, loopSite);
        assertEquals("PATH_ASSUMPTION",
                loop.get("policy").getAsString());
        assertEquals("FROZEN_LOOP_CONTAINER_STRUCTURE",
                loop.get("policyReason").getAsString());
        assertFalse(loop.get("requiredOutcome").getAsBoolean());

        JsonObject semantic = branch(region, semanticSite);
        assertEquals("EXPLORE", semantic.get("policy").getAsString());
        assertEquals("FAILURE_DIRECTED_SEMANTIC_GUARD",
                semantic.get("policyReason").getAsString());
    }

    @Test
    public void semanticCardinalityCheckOutsideLoopRemainsExplorable()
            throws Exception {
        File skeleton = skeleton("size-skeleton.jsonl");
        String collection = METHOD + "::$collection";
        String size = METHOD + "::$size";
        String site = METHOD + "#u9";
        File refined = writeRows("size-refined.jsonl",
                refinedEdge("DF.size", "container_receiver",
                        "MODEL_TRANSFORM", collection, size,
                        METHOD + "#u8", 8,
                        "$size = interfaceinvoke $collection."
                                + "<java.util.Collection: int size()>()",
                        "<java.util.Collection: int size()>",
                        null, null, false),
                refinedEdge("DF.size.guard", "guard_dependency", "GUARD",
                        size, site, site, 9,
                        "if $size == 0 goto failure", null,
                        site, true, false));
        JsonObject region = finalizeOne(refined, skeleton,
                "size-regions.jsonl", "size-edges.jsonl");

        JsonObject branch = branch(region, site);
        assertEquals("EXPLORE", branch.get("policy").getAsString());
        assertTrue(branch.get("requiredOutcome").getAsBoolean());
    }

    private File skeleton(String name) throws Exception {
        return write(name, object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", METHOD,
                "anchorMethod", METHOD,
                "methods", Collections.singletonList(METHOD),
                "selection", "EXCEPTION_COMPONENT"));
    }

    private JsonObject finalizeOne(File refined, File skeleton,
                                   String regionName, String edgeName)
            throws Exception {
        File regions = new File(folder.getRoot(), regionName);
        File edges = new File(folder.getRoot(), edgeName);
        RuntimeSelectedRegionFinalizer.finalizeRegions(refined, skeleton,
                regions, edges, Collections.singleton(METHOD));
        return GSON.fromJson(Files.readAllLines(regions.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
    }

    private static JsonObject branch(JsonObject region, String site) {
        for (com.google.gson.JsonElement element
                : region.getAsJsonArray("branchPolicies")) {
            JsonObject branch = element.getAsJsonObject();
            if (site.equals(branch.get("siteId").getAsString())) {
                return branch;
            }
        }
        throw new AssertionError("missing branch " + site);
    }

    private static Map<String, Object> refinedEdge(
            String id, String kind, String transfer, String from, String to,
            String site, int unitIndex, String unit, String invoke,
            String guardSite, Boolean requiredOutcome,
            boolean sameCellRedefinition) {
        Map<String, Object> edge = object(
                "schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", id, "kind", kind, "transferKind", transfer,
                "method", METHOD, "regionIds",
                Collections.singletonList("REGION.1"),
                "fromCell", from, "toCell", to, "siteId", site,
                "unitIndex", unitIndex, "unit", unit);
        if (invoke != null) edge.put("invoke", invoke);
        if (guardSite != null) edge.put("guardSiteId", guardSite);
        if (requiredOutcome != null) {
            edge.put("requiredOutcome", requiredOutcome);
        }
        if (sameCellRedefinition) {
            edge.put("sameCellRedefinition", true);
        }
        return edge;
    }

    private File write(String name, Map<String, Object> row)
            throws Exception {
        return writeRows(name, row);
    }

    @SafeVarargs
    private final File writeRows(String name, Map<String, Object>... rows)
            throws Exception {
        File file = new File(folder.getRoot(), name);
        java.util.List<String> encoded = new java.util.ArrayList<>();
        for (Map<String, Object> row : rows) {
            encoded.add(GSON.toJson(row));
        }
        Files.write(file.toPath(), encoded, StandardCharsets.UTF_8);
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
