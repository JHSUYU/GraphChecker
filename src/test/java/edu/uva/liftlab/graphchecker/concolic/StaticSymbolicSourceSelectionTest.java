package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.charset.StandardCharsets;

import static org.junit.Assert.assertEquals;

public class StaticSymbolicSourceSelectionTest {
    private static final List<String> IDS = Arrays.asList(
            "RPC_COMPARE.VALUE", "RPC_COMPARE.ADJUSTMENT",
            "RPC_COMPARE.GUARD_LEFT", "RPC_COMPARE.GUARD_RIGHT",
            "RPC_COMPARE.LOWER_BOUND", "RPC_COMPARE.UPPER_BOUND",
            "RPC_COMPARE.BIAS", "RPC_COMPARE.PIVOT");

    @Test
    public void omittedFileBuildsEightSliceBoundSourcesForEachRpc()
            throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        JsonObject regionB = region("REGION.B", "getCausynthValueB");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Arrays.asList(regionA, regionB));

        List<JsonObject> tasks = new ArrayList<>();
        tasks.add(task(selection, regionA, "OCC.A",
                "XCH.A.resp", "<Node: long getCausynthValueA()>.response"));
        tasks.add(task(selection, regionB, "OCC.B",
                "XCH.B.resp", "<Node: long getCausynthValueB()>.response"));
        selection.validateSourceCoverage(tasks);

        for (JsonObject task : tasks) {
            assertEquals("STATIC_SYMBOLIZE_HOOK_SELECTION_V1",
                    task.getAsJsonObject("symbolicInputSelection")
                            .get("authority").getAsString());
            JsonArray actions = task.getAsJsonArray("selectedActions");
            assertEquals(8, actions.size());
            for (JsonElement element : actions) {
                assertEquals("CONCRETE", element.getAsJsonObject()
                        .get("mode").getAsString());
            }
            JsonArray sources = task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD);
            assertEquals(8, sources.size());
            String output = task.get("expectedOutputCell").getAsString();
            for (int index = 0; index < sources.size(); index++) {
                JsonObject source = sources.get(index).getAsJsonObject();
                assertEquals(IDS.get(index),
                        source.get("sourceId").getAsString());
                assertEquals(output, source.get(
                        "requiredOutputFieldSignature").getAsString());
                assertEquals(SymbolicSourceEvidence.DECLARATION_AUTHORITY,
                        source.get("authority").getAsString());
            }
        }
    }

    @Test
    public void emptyLegacyFileStillUsesStaticHookDeclarations()
            throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        Path empty = Files.createTempFile(
                "causynth-symbolic-inputs", ".jsonl");
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(empty,
                            Collections.singletonList(regionA));
            JsonObject task = task(selection, regionA, "OCC.A",
                    "XCH.A.resp",
                    "<Node: long getCausynthValueA()>.response");
            assertEquals(8, task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD).size());
            assertEquals("CONFIGURED_REGION_SYMBOLIC_INPUTS_V1",
                    task.getAsJsonObject("symbolicInputSelection")
                            .get("authority").getAsString());
        } finally {
            Files.deleteIfExists(empty);
        }
    }

    @Test
    public void explicitAllowlistCannotMintSecondRootForHookField()
            throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        String field = regionA.getAsJsonArray(
                StaticSymbolicSourceDeclaration.FIELD).get(0)
                .getAsJsonObject().get("fieldSignature").getAsString();
        JsonObject configured = new JsonObject();
        configured.addProperty("regionId", "REGION.A");
        JsonArray fields = new JsonArray();
        fields.add(field);
        configured.add("fieldSignatures", fields);
        configured.add("portIds", new JsonArray());
        configured.add("cells", new JsonArray());
        Path selectionFile = Files.createTempFile(
                "causynth-overlapping-symbolic-inputs", ".jsonl");
        try {
            Files.write(selectionFile,
                    (CanonicalJson.render(configured) + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile, Collections.singletonList(regionA));

            JsonObject overlapping = new JsonObject();
            overlapping.addProperty("mode", "SYMBOLIC");
            overlapping.addProperty("accessFieldSignature", field);
            overlapping.addProperty("symbol", "IN.0");
            JsonArray candidates = new JsonArray();
            candidates.add(overlapping);
            JsonObject selected = selection.select("REGION.A", candidates)
                    .get(0).getAsJsonObject();
            assertEquals("CONCRETE", selected.get("mode").getAsString());
            assertEquals("CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED",
                    selected.get("symbolicDemand").getAsString());
            assertEquals(false, selection.selectedForDiscovery(
                    "REGION.A", overlapping));

            JsonObject task = task(selection, regionA, "OCC.A",
                    "XCH.A.resp",
                    "<Node: long getCausynthValueA()>.response");
            assertEquals(8, task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD).size());
            assertEquals(0, task.getAsJsonObject("symbolicInputSelection")
                    .get("selectedSymbolicRootCount").getAsInt());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    private static JsonObject task(
            ConcolicScheduler.SymbolicInputSelection selection,
            JsonObject region, String occurrence, String port,
            String outputCell) throws Exception {
        String regionId = region.get("regionId").getAsString();
        JsonArray candidates = new JsonArray();
        JsonArray demanded = new JsonArray();
        for (JsonElement element : region.getAsJsonArray(
                StaticSymbolicSourceDeclaration.FIELD)) {
            String field = element.getAsJsonObject()
                    .get("fieldSignature").getAsString();
            demanded.add(field);
            JsonObject action = new JsonObject();
            action.addProperty("mode", "SYMBOLIC");
            action.addProperty("accessFieldSignature", field);
            action.addProperty("symbol", "IN." + candidates.size());
            candidates.add(action);
        }
        JsonArray selected = selection.select(regionId, candidates);
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", outputCell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.add("demandedHeapDeclarations", demanded);
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL." + regionId, regionId,
                Collections.singletonList(port), port, outputCell,
                "RETURN", "long", slice);

        JsonObject task = new JsonObject();
        task.addProperty("regionId", regionId);
        task.addProperty("occurrenceId", occurrence);
        task.addProperty("expectedOutputCell", outputCell);
        task.add("selectedActions", selected.deepCopy());
        selection.annotate(task, candidates, selected);
        selection.annotateSources(task, regionId, closure);
        return task;
    }

    private static JsonObject region(String regionId, String method) {
        JsonObject region = new JsonObject();
        region.addProperty("schemaVersion", 3);
        region.addProperty("kind", "SYMBOLIC_REGION");
        region.addProperty("regionId", regionId);
        JsonArray sources = new JsonArray();
        for (int index = 0; index < IDS.size(); index++) {
            JsonObject source = new JsonObject();
            source.addProperty("schemaVersion",
                    StaticSymbolicSourceDeclaration.SCHEMA_VERSION);
            source.addProperty("kind",
                    StaticSymbolicSourceDeclaration.KIND);
            source.addProperty("authority",
                    StaticSymbolicSourceDeclaration.AUTHORITY);
            source.addProperty("sourceId", IDS.get(index));
            source.addProperty("fieldSignature",
                    "<Node: long value" + index + ">");
            source.addProperty("declarationMethod", "<Node: void "
                    + method + "Symbols()>");
            source.addProperty("declarationUnitIndex", index);
            sources.add(source);
        }
        region.add(StaticSymbolicSourceDeclaration.FIELD, sources);
        return region;
    }
}
