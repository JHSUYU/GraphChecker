package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.Gson;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourceSelectorContract;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.charset.StandardCharsets;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class StaticSymbolicSourceSelectionTest {
    private static final Gson GSON = new Gson();
    private static final List<String> IDS = Arrays.asList(
            "RPC_COMPARE.A", "RPC_COMPARE.B", "RPC_COMPARE.C",
            "RPC_COMPARE.D", "RPC_COMPARE.E");

    @Test
    public void omittedFileBuildsFiveSliceBoundSourcesForEachRpc()
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
            assertEquals(5, actions.size());
            for (JsonElement element : actions) {
                assertEquals("CONCRETE", element.getAsJsonObject()
                        .get("mode").getAsString());
            }
            JsonArray sources = task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD);
            assertEquals(5, sources.size());
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
            assertEquals(5, task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD).size());
            assertEquals("CONFIGURED_REGION_SYMBOLIC_INPUTS_V1",
                    task.getAsJsonObject("symbolicInputSelection")
                            .get("authority").getAsString());
        } finally {
            Files.deleteIfExists(empty);
        }
    }

    @Test(expected = java.io.IOException.class)
    public void configuredRegionMustExistInTheFreshStaticCatalog()
            throws Exception {
        Path selectionFile = targetSourceSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection.read(selectionFile,
                    catalog("REGION.DIFFERENT"));
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void malformedExplicitSelectionArraysAreRejected()
            throws Exception {
        List<JsonObject> malformedRows = new ArrayList<>();

        JsonObject nonArrayFields = emptySelectionRow("REGION.CONFIG");
        nonArrayFields.addProperty("fieldSignatures", "not-an-array");
        malformedRows.add(nonArrayFields);

        JsonObject numericPort = emptySelectionRow("REGION.CONFIG");
        numericPort.getAsJsonArray("portIds").add(7);
        malformedRows.add(numericPort);

        JsonObject emptyCell = emptySelectionRow("REGION.CONFIG");
        emptyCell.getAsJsonArray("cells").add("  ");
        malformedRows.add(emptyCell);

        JsonObject nonArraySources = emptySelectionRow("REGION.CONFIG");
        nonArraySources.add(SymbolicSourceEvidence.TASK_FIELD,
                new JsonObject());
        malformedRows.add(nonArraySources);

        for (JsonObject malformed : malformedRows) {
            Path file = Files.createTempFile(
                    "causynth-malformed-symbolic-inputs", ".jsonl");
            try {
                Files.write(file, (CanonicalJson.render(malformed) + "\n")
                        .getBytes(StandardCharsets.UTF_8));
                try {
                    ConcolicScheduler.SymbolicInputSelection.read(file,
                            catalog("REGION.CONFIG"));
                    fail("malformed explicit selection must be rejected: "
                            + malformed);
                } catch (java.io.IOException expected) {
                    // Expected.
                }
            } finally {
                Files.deleteIfExists(file);
            }
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
            assertEquals(5, task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD).size());
            assertEquals(0, task.getAsJsonObject("symbolicInputSelection")
                    .get("selectedSymbolicRootCount").getAsInt());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test(expected = java.io.IOException.class)
    public void oneSourceCannotSilentlySpanTwoOutputTasksInOneOccurrence()
            throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Collections.singletonList(regionA));
        JsonObject first = task(selection, regionA, "OCC.A",
                "XCH.A.resp.one", "<Node: long first()>.response");
        JsonObject second = task(selection, regionA, "OCC.A",
                "XCH.A.resp.two", "<Node: long second()>.response");
        second.addProperty("taskId", "TASK.REGION.A.SECOND");
        selection.validateSourceCoverage(Arrays.asList(first, second));
    }

    @Test
    public void oneSourceMayPublishDistinctPhasesAcrossRepeatedOccurrences()
            throws Exception {
        JsonObject regionA = region("REGION.A", "getCausynthValueA");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Collections.singletonList(regionA));
        JsonObject first = task(selection, regionA, "OCC.A.1",
                "XCH.A.resp.one", "<Node: long first()>.response");
        JsonObject second = task(selection, regionA, "OCC.A.2",
                "XCH.A.resp.two", "<Node: long second()>.response");

        selection.validateSourceCoverage(Arrays.asList(first, second));
        assertFalse(first.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD)
                .get(0).getAsJsonObject().get("sourcePhaseId")
                .getAsString().equals(second.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).get(0).getAsJsonObject()
                .get("sourcePhaseId").getAsString()));
    }

    @Test
    public void discoveredDeclarationMayCrossAnUnrelatedRegionEnvelope()
            throws Exception {
        JsonObject regionA = region("REGION.A", "sharedSymbols");
        JsonObject regionB = region("REGION.B", "sharedSymbols");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Arrays.asList(regionA, regionB));
        JsonObject demanded = task(selection, regionA, "OCC.A",
                "XCH.A.resp", "<Node: long demanded()>.response");
        JsonObject unrelated = task(selection, regionB, "OCC.B",
                "XCH.B.resp", "<Node: long unrelated()>.response", false);

        selection.validateSourceCoverage(Arrays.asList(demanded, unrelated));
        assertEquals(5, demanded.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).size());
        assertEquals(false, unrelated.has(SymbolicSourceEvidence.TASK_FIELD));
    }

    @Test
    public void oneSharedDeclarationMayProduceOncePerDynamicRegion()
            throws Exception {
        JsonObject regionA = region("REGION.A", "sharedSymbols");
        JsonObject regionB = region("REGION.B", "sharedSymbols");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Arrays.asList(regionA, regionB));
        JsonObject taskA = task(selection, regionA, "OCC.A",
                "XCH.A.resp", "<Node: long a()>.response");
        JsonObject taskB = task(selection, regionB, "OCC.B",
                "XCH.B.resp", "<Node: long b()>.response");

        selection.validateSourceCoverage(Arrays.asList(taskA, taskB));
        assertEquals(5, taskA.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).size());
        assertEquals(5, taskB.getAsJsonArray(
                SymbolicSourceEvidence.TASK_FIELD).size());
    }

    @Test
    public void discoveredDeclarationsAbsentFromOutputsRemainConcrete()
            throws Exception {
        JsonObject regionA = region("REGION.A", "sharedSymbols");
        JsonObject regionB = region("REGION.B", "sharedSymbols");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Arrays.asList(regionA, regionB));
        JsonObject taskA = task(selection, regionA, "OCC.A", "XCH.A.resp",
                "<Node: long unrelatedA()>.response", false);
        JsonObject taskB = task(selection, regionB, "OCC.B", "XCH.B.resp",
                "<Node: long unrelatedB()>.response", false);

        selection.validateSourceCoverage(Arrays.asList(taskA, taskB));

        for (JsonObject task : Arrays.asList(taskA, taskB)) {
            assertFalse(task.has(SymbolicSourceEvidence.TASK_FIELD));
            JsonObject policy = task.getAsJsonObject(
                    "symbolicInputSelection");
            assertEquals(5, policy.get("declaredSymbolicSourceCount")
                    .getAsInt());
            assertEquals(0, policy.get("selectedSymbolicSourceCount")
                    .getAsInt());
            assertEquals(5, policy.get("unusedSymbolicSourceCount")
                    .getAsInt());
        }
    }

    /**
     * Ten producer shapes exercise the actual contract behind manual source
     * declarations: a hook makes a field eligible, while the selected output
     * slice decides which eligible fields become roots for this task.  The
     * field's Java type is part of its exact identity and is never assumed to
     * be long or int by source selection.
     */
    @Test
    public void tenSourceCountAndTypeShapesSelectOnlyOutputDependencies()
            throws Exception {
        SourceShape[] shapes = new SourceShape[] {
                shape("one-int", types("int"), 0),
                shape("boolean-guard", types("boolean", "int"), 0),
                shape("long-and-flag",
                        types("long", "boolean", "int"), 0, 1),
                shape("current-a-d",
                        types("int", "int", "int", "int", "int"), 0, 3),
                shape("a-becomes-boolean",
                        types("boolean", "int", "long", "int", "int"),
                        0, 2),
                shape("narrow-integrals",
                        types("byte", "short", "char", "int", "long",
                                "boolean"), 0, 2, 5),
                shape("all-primitives",
                        types("boolean", "byte", "char", "short", "int",
                                "long", "float", "double"),
                        0, 4, 5, 7),
                shape("all-unused",
                        types("boolean", "int", "long", "double")),
                shape("only-last-reaches-output",
                        types("int", "boolean", "short", "long", "char",
                                "float", "double"), 6),
                shape("nested-mixed-guard",
                        types("boolean", "int", "long", "boolean", "byte",
                                "short", "char", "float", "double", "int"),
                        0, 1, 3, 5, 8)
        };
        assertEquals(10, shapes.length);

        for (int shapeIndex = 0; shapeIndex < shapes.length; shapeIndex++) {
            SourceShape shape = shapes[shapeIndex];
            String regionId = "REGION.MATRIX." + shapeIndex;
            JsonObject region = typedRegion(regionId, shape.name,
                    shape.types);
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(null,
                            Collections.singletonList(region));
            JsonObject task = taskDemanding(selection, region,
                    "OCC.MATRIX." + shapeIndex,
                    "XCH.MATRIX." + shapeIndex + ".resp",
                    "<Node: long matrix" + shapeIndex + "()>.response",
                    shape.demanded);

            selection.validateSourceCoverage(
                    Collections.singletonList(task));

            String message = "source shape " + shape.name;
            JsonObject policy = task.getAsJsonObject(
                    "symbolicInputSelection");
            assertEquals(message, shape.types.length,
                    policy.get("declaredSymbolicSourceCount").getAsInt());
            assertEquals(message, shape.demanded.size(),
                    policy.get("selectedSymbolicSourceCount").getAsInt());
            assertEquals(message,
                    shape.types.length - shape.demanded.size(),
                    policy.get("unusedSymbolicSourceCount").getAsInt());

            JsonArray selected = task.has(SymbolicSourceEvidence.TASK_FIELD)
                    ? task.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD)
                    : new JsonArray();
            assertEquals(message, shape.demanded.size(), selected.size());
            Set<String> selectedFields = new LinkedHashSet<>();
            for (JsonElement element : selected) {
                selectedFields.add(element.getAsJsonObject()
                        .get("fieldSignature").getAsString());
            }
            for (int sourceIndex = 0;
                 sourceIndex < shape.types.length; sourceIndex++) {
                String field = typedField(shape.types[sourceIndex],
                        sourceIndex);
                assertEquals(message + " field " + sourceIndex,
                        shape.demanded.contains(sourceIndex),
                        selectedFields.contains(field));
            }
        }
    }

    @Test
    public void configuredTargetSourceSelectsOnlyTheLocalTargetInput()
            throws Exception {
        Path selectionFile = targetSourceSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.TARGET"));
            JsonArray actions = new JsonArray();
            actions.add(targetAction("TARGET.local",
                    "<Target: long localValue>", false));
            actions.add(targetAction("XCH.remote.resp",
                    "<Reply: long remoteValue>", true));

            JsonObject task = targetTask(selection, actions);
            selection.validateSourceCoverage(
                    Collections.singletonList(task));

            JsonArray selected = task.getAsJsonArray("selectedActions");
            assertEquals("CONCRETE", selected.get(0).getAsJsonObject()
                    .get("mode").getAsString());
            assertEquals("CONCRETE", selected.get(1).getAsJsonObject()
                    .get("mode").getAsString());
            JsonArray sources = task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD);
            assertEquals(1, sources.size());
            JsonObject source = sources.get(0).getAsJsonObject();
            assertEquals("TARGET.LOCAL",
                    source.get("sourceId").getAsString());
            assertEquals("TARGET_REACH",
                    source.get("sourceRole").getAsString());
            assertEquals("TARGET.local",
                    source.get("requiredTargetInputPort").getAsString());
            assertFalse(source.has("requiredOutputFieldSignature"));
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void targetMayDeclareSeveralLocalSourcesBesideRemoteAttach()
            throws Exception {
        Path selectionFile = targetSourceSelection(
                targetSource("TARGET.LEFT", "<Target: long left>",
                        "TARGET.left"),
                targetSource("TARGET.GATE", "<Target: int gate>",
                        "TARGET.gate"));
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.TARGET"));
            JsonArray actions = new JsonArray();
            actions.add(targetAction("TARGET.left",
                    "<Target: long left>", false));
            actions.add(targetAction("XCH.remote.resp",
                    "<Reply: long remoteValue>", true));
            actions.add(targetAction("TARGET.gate",
                    "<Target: int gate>", false));

            JsonObject task = targetTask(selection, actions);
            selection.validateSourceCoverage(
                    Collections.singletonList(task));

            JsonArray sources = task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD);
            assertEquals(2, sources.size());
            assertEquals("TARGET.LEFT", sources.get(0).getAsJsonObject()
                    .get("sourceId").getAsString());
            assertEquals("TARGET.left", sources.get(0).getAsJsonObject()
                    .get("requiredTargetInputPort").getAsString());
            assertEquals("TARGET.GATE", sources.get(1).getAsJsonObject()
                    .get("sourceId").getAsString());
            assertEquals("TARGET.gate", sources.get(1).getAsJsonObject()
                    .get("requiredTargetInputPort").getAsString());
            for (JsonElement element : sources) {
                assertEquals("TARGET_REACH", element.getAsJsonObject()
                        .get("sourceRole").getAsString());
                assertFalse(element.getAsJsonObject().has(
                        "requiredOutputFieldSignature"));
                assertFalse(element.getAsJsonObject().get(
                        "requiredTargetInputPort").getAsString()
                        .equals("XCH.remote.resp"));
            }
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void targetSeedKeepsManualSourcesFromDeeperFatalGuards()
            throws Exception {
        Path selectionFile = targetSourceSelection(
                targetSource("TARGET.GATE", "<Target: long gate>",
                        "TARGET.gate"),
                targetSource("TARGET.OFFSET", "<Target: long offset>",
                        "TARGET.offset"));
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile, catalog("REGION.TARGET"));
            JsonArray branchFrontier = new JsonArray();
            branchFrontier.add(targetAction("TARGET.gate",
                    "<Target: long gate>", false));
            JsonArray guardedFatalFrontier = branchFrontier.deepCopy();
            guardedFatalFrontier.add(targetAction("TARGET.offset",
                    "<Target: long offset>", false));
            guardedFatalFrontier.add(targetAction("TARGET.unrelated",
                    "<Target: long unrelated>", false));

            JsonArray merged = selection.includeTargetSourceFrontier(
                    "REGION.TARGET", branchFrontier,
                    guardedFatalFrontier);

            assertEquals(2, merged.size());
            assertEquals("TARGET.gate", merged.get(0).getAsJsonObject()
                    .get("symbol").getAsString());
            assertEquals("TARGET.offset", merged.get(1).getAsJsonObject()
                    .get("symbol").getAsString());
            JsonObject task = targetTask(selection, merged);
            selection.validateSourceCoverage(
                    Collections.singletonList(task));
            assertEquals(2, task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD).size());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void targetEvidenceDoesNotSelectUnusedProducerDeclarations()
            throws Exception {
        JsonObject producerRegion = region("REGION.PRODUCER", "shared");
        JsonObject targetRegion = region("REGION.TARGET", "shared");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Arrays.asList(producerRegion, targetRegion));
        JsonObject producer = task(selection, producerRegion,
                "OCC.PRODUCER", "REGION.PRODUCER.out.value",
                "<Node: long unrelated()>.response", false);
        JsonObject target = discoveredTargetTask(selection, targetRegion);

        selection.validateSourceCoverage(Arrays.asList(producer, target));

        assertFalse(producer.has(SymbolicSourceEvidence.TASK_FIELD));
        assertTrue(target.has(SymbolicSourceEvidence.TASK_FIELD));
        JsonObject producerPolicy = producer.getAsJsonObject(
                "symbolicInputSelection");
        assertEquals(0, producerPolicy.get("selectedSymbolicSourceCount")
                .getAsInt());
        assertEquals(5, producerPolicy.get("unusedSymbolicSourceCount")
                .getAsInt());
    }

    @Test
    public void sourceRoleMustAgreeWithBoundaryAndTaskKind()
            throws Exception {
        JsonObject targetRegion = region("REGION.TARGET", "target");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Collections.singletonList(targetRegion));
        JsonObject target = discoveredTargetTask(selection, targetRegion);
        target.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD)
                .get(0).getAsJsonObject().addProperty("sourceRole",
                        "OUTPUT_RELATION");

        try {
            selection.validateSourceCoverage(
                    Collections.singletonList(target));
            fail("declared role must not override the target boundary");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains("boundary/task role mismatch"));
        }
    }

    @Test
    public void ownedTargetActionRequiresExactSourceEvidence()
            throws Exception {
        JsonObject targetRegion = region("REGION.TARGET", "target");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null,
                        Collections.singletonList(targetRegion));
        JsonObject target = discoveredTargetTask(selection, targetRegion);
        target.remove(SymbolicSourceEvidence.TASK_FIELD);

        try {
            selection.validateSourceCoverage(
                    Collections.singletonList(target));
            fail("owned target action must have exact source evidence");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains("target-local source frontier"));
        }
    }

    @Test
    public void latestPublicationBeforeTargetShadowsEarlierSameSourcePhase()
            throws Exception {
        Path selectionFile = targetSourceSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile, catalog("REGION.TARGET"));
            JsonArray actions = new JsonArray();
            actions.add(targetAction("TARGET.local",
                    "<Target: long localValue>", false));

            JsonObject task = targetTask(selection, actions, true);
            JsonArray catalog = task.getAsJsonArray(
                    ConfiguredSourcePhaseContract.PLAN_FIELD);
            JsonArray selected = task.getAsJsonArray(
                    ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD);
            assertEquals(2, catalog.size());
            assertEquals(1, selected.size());
            String latest = catalog.get(1).getAsJsonObject()
                    .get("phaseId").getAsString();
            assertEquals(latest, selected.get(0).getAsString());
            assertEquals(latest, task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD).get(0)
                    .getAsJsonObject().get("sourcePhaseId").getAsString());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test(expected = java.io.IOException.class)
    public void relationBoundTargetInputCannotDischargeLocalSourceCoverage()
            throws Exception {
        Path selectionFile = targetSourceSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.TARGET"));
            JsonArray actions = new JsonArray();
            actions.add(targetAction("TARGET.local",
                    "<Target: long localValue>", true));
            JsonObject task = targetTask(selection, actions);
            selection.validateSourceCoverage(
                    Collections.singletonList(task));
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void exactSourceSelectorBindsOccurrenceButNotSeedTaskId()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject producer = selectorProducer("TASK.REPLAY.source",
                    "OCC.SOURCE");
            JsonObject consumer = selectorConsumer("TASK.selector.consumer",
                    "OCC.CONSUMER", selectorEdge(producer, "OCC.CONSUMER",
                            "EDGE.source.consumer"));

            selection.bindSourceSelectors(Arrays.asList(producer, consumer));

            JsonObject selector = consumer.getAsJsonArray(
                    ConfiguredSourceSelectorContract.TASK_FIELD)
                    .get(0).getAsJsonObject();
            assertEquals("OCC.SOURCE",
                    selector.get("sourceOccurrenceId").getAsString());
            assertEquals("SELECTOR.SOURCE",
                    selector.get("sourceId").getAsString());
            assertFalse(selector.has("sourceTaskId"));
            assertFalse(selector.has("selectedIntValue"));
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void fieldlessConsumeSelectsDependentPublicationInSameCall()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject task = new JsonObject();
            task.addProperty("taskId", "TASK.consumer.output");
            task.addProperty("regionId", "REGION.SELECTOR.CONSUMER");
            task.addProperty("occurrenceId", "OCC.CONSUMER");
            JsonObject consume = sourcePhase("SELECTOR.SOURCE", "",
                    "OCC.CONSUMER",
                    ConfiguredSourcePhaseContract.Phase.CONSUME,
                    "<example.Dependent: void rotate()>", 0, 20L, 301L);
            JsonObject publish = sourcePhase("SELECTOR.DEPENDENT",
                    "<example.Dependent: long expiry>", "OCC.CONSUMER",
                    ConfiguredSourcePhaseContract.Phase.PUBLISH,
                    "<example.Dependent: void rotate()>", 1, 30L, 301L);
            JsonArray phases = new JsonArray();
            phases.add(consume);
            phases.add(publish);
            task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
            JsonObject slice = new JsonObject();
            slice.addProperty("outputPort", "SELECTOR.out.expiry");
            slice.addProperty("outputCell", "SELECTOR.out.expiry");
            slice.add("inputPorts", new JsonArray());
            slice.add("causalEdgeIds", new JsonArray());
            slice.add("sites", new JsonArray());
            slice.add("staticSites", new JsonArray());
            slice.add("methods", new JsonArray());
            slice.add("captureBindings", new JsonArray());
            slice.add("captureBindingIssues", new JsonArray());
            JsonArray demanded = new JsonArray();
            demanded.add("<example.Dependent: long expiry>");
            slice.add("demandedHeapDeclarations", demanded);
            slice.addProperty("selectedRuntimeCallId", 301L);
            slice.addProperty("selectedRuntimeEventSeq", 40L);
            slice.addProperty("definitionCompletionSeq", 40L);
            OutputClosureContract closure = OutputClosureCodec.singleton(
                    "REL.consumer", "REGION.SELECTOR.CONSUMER",
                    Collections.singletonList("SELECTOR.out.expiry"),
                    "SELECTOR.out.expiry", "SELECTOR.out.expiry", "RETURN",
                    "long", slice);

            selection.annotateSources(task, "REGION.SELECTOR.CONSUMER",
                    closure, new JsonArray());

            assertEquals(1, task.getAsJsonArray(
                    SymbolicSourceEvidence.TASK_FIELD).size());
            assertEquals(publish.get("phaseId").getAsString(),
                    task.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD)
                            .get(0).getAsJsonObject().get("sourcePhaseId")
                            .getAsString());
            JsonArray selected = task.getAsJsonArray(
                    ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD);
            assertEquals(2, selected.size());
            assertEquals(consume.get("phaseId").getAsString(),
                    selected.get(0).getAsString());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void duplicateEdgeOwnerRowsBindOneSourceVersion()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject producer = selectorProducer("TASK.source",
                    "OCC.SOURCE");
            JsonObject consumer = selectorConsumer("TASK.consumer",
                    "OCC.CONSUMER", selectorEdge(producer, "OCC.CONSUMER",
                            "EDGE.source.consumer"));
            producer.getAsJsonArray("edgeBindings").add(
                    consumer.getAsJsonArray("edgeBindings").get(0)
                            .getAsJsonObject().deepCopy());

            selection.bindSourceSelectors(Arrays.asList(producer, consumer));

            assertEquals(1, consumer.getAsJsonArray(
                    ConfiguredSourceSelectorContract.TASK_FIELD).size());
            assertEquals("OCC.SOURCE", consumer.getAsJsonArray(
                    ConfiguredSourceSelectorContract.TASK_FIELD).get(0)
                    .getAsJsonObject().get("sourceOccurrenceId")
                    .getAsString());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void selectorBindsOnlyTheTaskThatDeclaresItsDependentSource()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject publisher = selectorProducer("TASK.publisher",
                    "OCC.PUBLISHER");
            publisher.addProperty("regionId",
                    "REGION.SELECTOR.CONSUMER");
            JsonObject unrelated = selectorUnrelated("TASK.unrelated",
                    "OCC.UNRELATED", selectorEdge(publisher,
                            "OCC.UNRELATED", "EDGE.publisher.unrelated"));
            JsonObject consumer = selectorConsumer("TASK.consumer",
                    "OCC.CONSUMER", selectorEdge(publisher,
                            "OCC.CONSUMER", "EDGE.publisher.consumer"));

            selection.bindSourceSelectors(Arrays.asList(
                    publisher, unrelated, consumer));

            assertFalse(publisher.has(
                    ConfiguredSourceSelectorContract.TASK_FIELD));
            assertFalse(unrelated.has(
                    ConfiguredSourceSelectorContract.TASK_FIELD));
            assertEquals(1, consumer.getAsJsonArray(
                    ConfiguredSourceSelectorContract.TASK_FIELD).size());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void sameOccurrenceDifferentTasksCanBindExactSourceVersion()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject producer = selectorProducer("TASK.publisher",
                    "OCC.SHARED");
            JsonObject consumer = selectorConsumer("TASK.consumer",
                    "OCC.SHARED", selectorEdge(producer, "OCC.SHARED",
                            "EDGE.shared.phase"));

            selection.bindSourceSelectors(Arrays.asList(producer, consumer));

            assertEquals("OCC.SHARED", consumer.getAsJsonArray(
                    ConfiguredSourceSelectorContract.TASK_FIELD).get(0)
                    .getAsJsonObject().get("sourceOccurrenceId")
                    .getAsString());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void sameTaskSelfLoopIsRejectedWithExactConsumerDiagnostic()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject self = selectorProducer("TASK.self", "OCC.SELF");
            self.addProperty("regionId", "REGION.SELECTOR.CONSUMER");
            addSelectorDependentSource(self);
            self.getAsJsonArray("edgeBindings").add(selectorEdge(
                    self, "OCC.SELF", "EDGE.self"));

            try {
                selection.bindSourceSelectors(
                        Collections.singletonList(self));
                fail("same task must not consume its own source version");
            } catch (java.io.IOException expected) {
                assertTrue(expected.getMessage(), expected.getMessage()
                        .contains("consumer task TASK.self@OCC.SELF"));
                assertTrue(expected.getMessage(), expected.getMessage()
                        .contains("found 0 candidates []"));
            }
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void ambiguousVersionsNameEveryCandidateInDiagnostic()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject first = selectorProducer("TASK.first", "OCC.FIRST");
            JsonObject second = selectorProducer("TASK.second", "OCC.SECOND");
            JsonObject consumer = selectorConsumer("TASK.consumer",
                    "OCC.CONSUMER", selectorEdge(first, "OCC.CONSUMER",
                            "EDGE.first.consumer"));
            consumer.getAsJsonArray("edgeBindings").add(selectorEdge(
                    second, "OCC.CONSUMER", "EDGE.second.consumer"));

            try {
                selection.bindSourceSelectors(Arrays.asList(
                        first, second, consumer));
                fail("ambiguous exact producers must be rejected");
            } catch (java.io.IOException expected) {
                assertTrue(expected.getMessage(), expected.getMessage()
                        .contains("found 2 candidates"));
                assertTrue(expected.getMessage(), expected.getMessage()
                        .contains("TASK.first@OCC.FIRST"));
                assertTrue(expected.getMessage(), expected.getMessage()
                        .contains("TASK.second@OCC.SECOND"));
            }
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test(expected = java.io.IOException.class)
    public void sameEdgeIdCannotNameConflictingEndpoints()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject producer = selectorProducer("TASK.source",
                    "OCC.SOURCE");
            JsonObject consumer = selectorConsumer("TASK.consumer",
                    "OCC.CONSUMER", selectorEdge(producer, "OCC.CONSUMER",
                            "EDGE.source.consumer"));
            JsonObject conflicting = consumer.getAsJsonArray("edgeBindings")
                    .get(0).getAsJsonObject().deepCopy();
            conflicting.addProperty("toInputPort",
                    "SELECTOR.in.conflicting-keyId");
            producer.getAsJsonArray("edgeBindings").add(conflicting);

            selection.bindSourceSelectors(Arrays.asList(producer, consumer));
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void repeatedSourceBindsPreviousVersionAndNeverConsumesItself()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject rotationN = selectorProducer(
                    "TASK.source.rotation.n", "OCC.SOURCE.N");
            JsonObject rotationN1 = selectorProducer(
                    "TASK.source.rotation.n1", "OCC.SOURCE.N1");
            rotationN1.addProperty("regionId",
                    "REGION.SELECTOR.CONSUMER");
            addSelectorDependentSource(rotationN1);
            JsonArray firstEdge = new JsonArray();
            firstEdge.add(selectorEdge(rotationN, "OCC.SOURCE.N1",
                    "EDGE.rotation.n.n1"));
            rotationN1.add("edgeBindings", firstEdge);
            JsonObject rotationN2 = selectorConsumer(
                    "TASK.selector.rotation.n2", "OCC.SOURCE.N2",
                    selectorEdge(rotationN1, "OCC.SOURCE.N2",
                            "EDGE.rotation.n1.n2"));

            selection.bindSourceSelectors(Arrays.asList(
                    rotationN, rotationN1, rotationN2));

            assertEquals("OCC.SOURCE.N", rotationN1.getAsJsonArray(
                    ConfiguredSourceSelectorContract.TASK_FIELD).get(0)
                    .getAsJsonObject().get("sourceOccurrenceId")
                    .getAsString());
            assertEquals("OCC.SOURCE.N1", rotationN2.getAsJsonArray(
                    ConfiguredSourceSelectorContract.TASK_FIELD).get(0)
                    .getAsJsonObject().get("sourceOccurrenceId")
                    .getAsString());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void repeatedConsumePhasesBindLatestPriorArrivals()
            throws Exception {
        Path selectionFile = selectorSelection();
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject first = selectorProducer("TASK.first", "OCC.FIRST");
            JsonObject second = selectorProducer("TASK.second", "OCC.SECOND");
            JsonObject consumer = selectorConsumer("TASK.consumer",
                    "OCC.CONSUMER", selectorEdge(first, "OCC.CONSUMER",
                            "EDGE.first.consumer", 15L));
            consumer.getAsJsonArray("edgeBindings").add(selectorEdge(
                    second, "OCC.CONSUMER", "EDGE.second.consumer", 35L));
            JsonObject secondConsume = sourcePhase("SELECTOR.SOURCE", "",
                    "OCC.CONSUMER",
                    ConfiguredSourcePhaseContract.Phase.CONSUME,
                    "<example.Dependent: void rotate()>", 0, 2, 40L, 301L);
            JsonObject secondPublish = sourcePhase("SELECTOR.DEPENDENT",
                    "<example.Dependent: long expiry>", "OCC.CONSUMER",
                    ConfiguredSourcePhaseContract.Phase.PUBLISH,
                    "<example.Dependent: void rotate()>", 1, 2, 50L, 301L);
            consumer.getAsJsonArray(
                    ConfiguredSourcePhaseContract.PLAN_FIELD)
                    .add(secondConsume);
            consumer.getAsJsonArray(
                    ConfiguredSourcePhaseContract.PLAN_FIELD)
                    .add(secondPublish);
            consumer.getAsJsonArray(
                    ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD)
                    .add(secondConsume.get("phaseId").getAsString());
            consumer.getAsJsonArray(
                    ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD)
                    .add(secondPublish.get("phaseId").getAsString());

            selection.bindSourceSelectors(Arrays.asList(
                    first, second, consumer));

            JsonArray selectors = consumer.getAsJsonArray(
                    ConfiguredSourceSelectorContract.TASK_FIELD);
            assertEquals(2, selectors.size());
            assertEquals("OCC.FIRST", selectors.get(0).getAsJsonObject()
                    .get("sourceOccurrenceId").getAsString());
            assertEquals("OCC.SECOND", selectors.get(1).getAsJsonObject()
                    .get("sourceOccurrenceId").getAsString());
        } finally {
            Files.deleteIfExists(selectionFile);
        }
    }

    @Test
    public void obsoleteDebugPropertyCannotBypassExactSelectorAdmission()
            throws Exception {
        Path selectionFile = selectorSelection();
        String property = "causynth.debug.skipSourceSelectorBinding";
        String prior = System.getProperty(property);
        try {
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(
                            selectionFile,
                            catalog("REGION.SELECTOR.CONSUMER"));
            JsonObject consumer = selectorConsumer("TASK.consumer",
                    "OCC.CONSUMER", new JsonObject());
            consumer.add("edgeBindings", new JsonArray());
            System.setProperty(property, "true");
            try {
                selection.bindSourceSelectors(
                        Collections.singletonList(consumer));
                fail("obsolete debug property must not disable admission");
            } catch (java.io.IOException expected) {
                assertTrue(expected.getMessage(), expected.getMessage()
                        .contains("requires one exact upstream source"));
            }
        } finally {
            if (prior == null) {
                System.clearProperty(property);
            } else {
                System.setProperty(property, prior);
            }
            Files.deleteIfExists(selectionFile);
        }
    }

    private static JsonObject task(
            ConcolicScheduler.SymbolicInputSelection selection,
            JsonObject region, String occurrence, String port,
            String outputCell) throws Exception {
        return task(selection, region, occurrence, port, outputCell, true);
    }

    private static JsonObject task(
            ConcolicScheduler.SymbolicInputSelection selection,
            JsonObject region, String occurrence, String port,
            String outputCell, boolean demandSources) throws Exception {
        Set<Integer> demandedIndexes = new LinkedHashSet<>();
        if (demandSources) {
            int count = region.getAsJsonArray(
                    StaticSymbolicSourceDeclaration.FIELD).size();
            for (int index = 0; index < count; index++) {
                demandedIndexes.add(index);
            }
        }
        return taskDemanding(selection, region, occurrence, port,
                outputCell, demandedIndexes);
    }

    private static JsonObject taskDemanding(
            ConcolicScheduler.SymbolicInputSelection selection,
            JsonObject region, String occurrence, String port,
            String outputCell, Set<Integer> demandedIndexes)
            throws Exception {
        String regionId = region.get("regionId").getAsString();
        JsonArray candidates = new JsonArray();
        JsonArray demanded = new JsonArray();
        int sourceIndex = 0;
        for (JsonElement element : region.getAsJsonArray(
                StaticSymbolicSourceDeclaration.FIELD)) {
            String field = element.getAsJsonObject()
                    .get("fieldSignature").getAsString();
            if (demandedIndexes.contains(sourceIndex)) demanded.add(field);
            JsonObject action = new JsonObject();
            action.addProperty("mode", "SYMBOLIC");
            action.addProperty("accessFieldSignature", field);
            action.addProperty("symbol", "IN." + candidates.size());
            candidates.add(action);
            sourceIndex++;
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
        slice.addProperty("selectedRuntimeCallId", 101L);
        slice.addProperty("selectedRuntimeEventSeq", 1_000L);
        slice.addProperty("definitionCompletionSeq", 1_000L);
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL." + regionId, regionId,
                Collections.singletonList(port), port, outputCell,
                "RETURN", "long", slice);

        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK." + regionId + "." + occurrence);
        task.addProperty("regionId", regionId);
        task.addProperty("occurrenceId", occurrence);
        task.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE.name());
        task.addProperty("expectedOutputCell", outputCell);
        task.add("selectedActions", selected.deepCopy());
        addRegionPublishPhases(task, region, occurrence);
        selection.annotate(task, candidates, selected);
        selection.annotateSources(task, regionId, closure, candidates);
        return task;
    }

    private static List<JsonObject> catalog(String... regionIds) {
        List<JsonObject> result = new ArrayList<>();
        for (String regionId : regionIds) {
            JsonObject region = new JsonObject();
            region.addProperty("regionId", regionId);
            result.add(region);
        }
        return result;
    }

    private static JsonObject emptySelectionRow(String regionId) {
        JsonObject row = new JsonObject();
        row.addProperty("regionId", regionId);
        row.add("fieldSignatures", new JsonArray());
        row.add("portIds", new JsonArray());
        row.add("cells", new JsonArray());
        return row;
    }

    private static Path targetSourceSelection() throws Exception {
        return targetSourceSelection(targetSource("TARGET.LOCAL",
                "<Target: long localValue>", "TARGET.local"));
    }

    private static JsonObject targetSource(
            String sourceId, String field, String inputPort) {
        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourceId", sourceId);
        source.addProperty("fieldSignature", field);
        source.addProperty("requiredTargetInputPort", inputPort);
        return source;
    }

    private static Path targetSourceSelection(JsonObject... declarations)
            throws Exception {
        JsonObject row = new JsonObject();
        row.addProperty("regionId", "REGION.TARGET");
        JsonArray sources = new JsonArray();
        for (JsonObject declaration : declarations) {
            sources.add(declaration);
        }
        row.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        Path path = Files.createTempFile(
                "causynth-target-symbolic-source", ".jsonl");
        Files.write(path, (CanonicalJson.render(row) + "\n").getBytes(
                StandardCharsets.UTF_8));
        return path;
    }

    private static JsonObject targetAction(
            String port, String field, boolean relationBound) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("portId", port);
        action.addProperty("symbol", port);
        action.addProperty("accessFieldSignature", field);
        if (relationBound) {
            action.addProperty("symbolicDemand",
                    "EXACT_INCOMING_COMPOSITION");
            action.addProperty("selectedIncomingEdgeId", "EDGE.remote");
        }
        return action;
    }

    private static JsonObject targetTask(
            ConcolicScheduler.SymbolicInputSelection selection,
            JsonArray candidates) throws Exception {
        return targetTask(selection, candidates, false);
    }

    private static JsonObject targetTask(
            ConcolicScheduler.SymbolicInputSelection selection,
            JsonArray candidates, boolean repeatLocalPublish)
            throws Exception {
        JsonArray selected = selection.select("REGION.TARGET", candidates);
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.REGION.TARGET.OCC.TARGET");
        task.addProperty("regionId", "REGION.TARGET");
        task.addProperty("occurrenceId", "OCC.TARGET");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        task.add("selectedActions", selected.deepCopy());
        JsonArray phases = new JsonArray();
        int unit = 0;
        long event = 10L;
        for (JsonElement element : candidates) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String port = action.get("portId").getAsString();
            if (port.startsWith("XCH.")) continue;
            String sourceId = "TARGET." + port.substring(
                    port.indexOf('.') + 1).toUpperCase(
                    java.util.Locale.ROOT);
            if (repeatLocalPublish && "TARGET.LOCAL".equals(sourceId)) {
                phases.add(sourcePhase(sourceId,
                        action.get("accessFieldSignature").getAsString(),
                        "OCC.TARGET",
                        ConfiguredSourcePhaseContract.Phase.PUBLISH,
                        "<Target: void compare()>", unit, 1, 5L, 201L));
            }
            phases.add(sourcePhase(sourceId,
                    action.get("accessFieldSignature").getAsString(),
                    "OCC.TARGET", ConfiguredSourcePhaseContract.Phase.PUBLISH,
                    "<Target: void compare()>", unit++,
                    repeatLocalPublish && "TARGET.LOCAL".equals(sourceId)
                            ? 2 : 1,
                    event++, 201L));
        }
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("failureTarget", true);
        targetBranch.addProperty("selectedCallId", 201L);
        targetBranch.addProperty("selectedRuntimeEventSeq", 1_000L);
        JsonArray branches = new JsonArray();
        branches.add(targetBranch);
        task.add("branches", branches);
        selection.annotate(task, candidates, selected);
        selection.annotateSources(task, "REGION.TARGET", null,
                candidates);
        return task;
    }

    private static JsonObject discoveredTargetTask(
            ConcolicScheduler.SymbolicInputSelection selection,
            JsonObject region) throws Exception {
        JsonObject source = region.getAsJsonArray(
                StaticSymbolicSourceDeclaration.FIELD).get(0)
                .getAsJsonObject();
        JsonArray candidates = new JsonArray();
        candidates.add(targetAction("TARGET.local",
                source.get("fieldSignature").getAsString(), false));
        JsonArray selected = selection.select(
                region.get("regionId").getAsString(), candidates);
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.DISCOVERED.TARGET");
        task.addProperty("regionId",
                region.get("regionId").getAsString());
        task.addProperty("occurrenceId", "OCC.TARGET");
        task.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        task.add(InputActionCatalog.FIELD, selected.deepCopy());
        task.add("selectedActions", selected.deepCopy());
        addRegionPublishPhases(task, region, "OCC.TARGET");
        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("failureTarget", true);
        targetBranch.addProperty("selectedCallId", 101L);
        targetBranch.addProperty("selectedRuntimeEventSeq", 1_000L);
        JsonArray branches = new JsonArray();
        branches.add(targetBranch);
        task.add("branches", branches);
        selection.annotate(task, candidates, selected);
        selection.annotateSources(task,
                region.get("regionId").getAsString(), null, candidates);
        return task;
    }

    private static Path selectorSelection() throws Exception {
        JsonObject row = new JsonObject();
        row.addProperty("regionId", "REGION.SELECTOR.CONSUMER");
        row.add("fieldSignatures", new JsonArray());
        row.add("portIds", new JsonArray());
        row.add("cells", new JsonArray());
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourceSelectorContract.intDeclaration(
                "SELECTOR.SOURCE", "<example.Key: int keyId>",
                Collections.singletonList("SELECTOR.DEPENDENT")));
        row.add(ConfiguredSourceSelectorContract.CONFIG_FIELD, declarations);
        JsonObject dependent = new JsonObject();
        dependent.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        dependent.addProperty("sourceId", "SELECTOR.DEPENDENT");
        dependent.addProperty("fieldSignature",
                "<example.Dependent: long expiry>");
        dependent.addProperty("requiredOutputFieldSignature",
                "SELECTOR.out.expiry");
        JsonArray sources = new JsonArray();
        sources.add(dependent);
        row.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        Path path = Files.createTempFile(
                "causynth-configured-source-selector", ".jsonl");
        Files.write(path, (CanonicalJson.render(row) + "\n").getBytes(
                StandardCharsets.UTF_8));
        return path;
    }

    private static JsonObject selectorProducer(
            String taskId, String occurrenceId) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", taskId);
        task.addProperty("regionId", "REGION.SELECTOR.PRODUCER");
        task.addProperty("occurrenceId", occurrenceId);
        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourceId", "SELECTOR.SOURCE");
        source.addProperty("fieldSignature", "<example.Key: int keyId>");
        source.addProperty("requiredOutputFieldSignature",
                "SELECTOR.out.keyId");
        JsonArray sources = new JsonArray();
        JsonObject phase = sourcePhase("SELECTOR.SOURCE",
                "<example.Key: int keyId>", occurrenceId,
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "<example.Key: void publish()>", 0, 10L, 301L);
        source.addProperty("sourcePhaseId",
                phase.get("phaseId").getAsString());
        sources.add(source);
        task.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        JsonArray phases = new JsonArray();
        phases.add(phase);
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        JsonArray selectedPhases = new JsonArray();
        selectedPhases.add(phase.get("phaseId").getAsString());
        task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD,
                selectedPhases);
        task.add("outputClosure", selectorOutputClosure(taskId));
        task.add("edgeBindings", new JsonArray());
        return task;
    }

    private static JsonObject selectorConsumer(
            String taskId, String occurrenceId, JsonObject edge) {
        JsonObject task = selectorUnrelated(taskId, occurrenceId, edge);
        addSelectorDependentSource(task);
        return task;
    }

    private static JsonObject selectorUnrelated(
            String taskId, String occurrenceId, JsonObject edge) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", taskId);
        task.addProperty("regionId", "REGION.SELECTOR.CONSUMER");
        task.addProperty("occurrenceId", occurrenceId);
        JsonArray edges = new JsonArray();
        edges.add(edge);
        task.add("edgeBindings", edges);
        return task;
    }

    private static void addSelectorDependentSource(JsonObject task) {
        JsonArray sources = task.has(SymbolicSourceEvidence.TASK_FIELD)
                ? task.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD)
                : new JsonArray();
        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourceId", "SELECTOR.DEPENDENT");
        source.addProperty("fieldSignature",
                "<example.Dependent: long expiry>");
        JsonArray phases = task.has(ConfiguredSourcePhaseContract.PLAN_FIELD)
                ? task.getAsJsonArray(
                ConfiguredSourcePhaseContract.PLAN_FIELD)
                : new JsonArray();
        String occurrence = task.get("occurrenceId").getAsString();
        JsonObject consume = sourcePhase("SELECTOR.SOURCE", "", occurrence,
                ConfiguredSourcePhaseContract.Phase.CONSUME,
                "<example.Dependent: void rotate()>", 0, 20L, 301L);
        JsonObject publish = sourcePhase("SELECTOR.DEPENDENT",
                "<example.Dependent: long expiry>", occurrence,
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "<example.Dependent: void rotate()>", 1, 30L, 301L);
        source.addProperty("sourcePhaseId",
                publish.get("phaseId").getAsString());
        phases.add(consume);
        phases.add(publish);
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        JsonArray selectedPhases = task.has(
                ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD)
                ? task.getAsJsonArray(
                ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD)
                : new JsonArray();
        selectedPhases.add(consume.get("phaseId").getAsString());
        selectedPhases.add(publish.get("phaseId").getAsString());
        task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD,
                selectedPhases);
        sources.add(source);
        task.add(SymbolicSourceEvidence.TASK_FIELD, sources);
    }

    private static JsonObject selectorEdge(
            JsonObject producer, String consumerOccurrence, String edgeId) {
        return selectorEdge(producer, consumerOccurrence, edgeId, 15L);
    }

    private static JsonObject selectorEdge(
            JsonObject producer, String consumerOccurrence, String edgeId,
            long readerEventSeq) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("fromOccurrenceId",
                producer.get("occurrenceId").getAsString());
        edge.addProperty("fromOutputPort", selectorOutputPort(producer));
        edge.addProperty("toOccurrenceId", consumerOccurrence);
        edge.addProperty("toInputPort", "SELECTOR.in.keyId");
        edge.addProperty("readerEventSeq", readerEventSeq);
        producer.getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice").getAsJsonArray("causalEdgeIds")
                .add(edgeId);
        return edge;
    }

    private static JsonObject selectorOutputClosure(String taskId) {
        JsonObject output = new JsonObject();
        output.addProperty("portId", "SELECTOR.out." + taskId);
        output.addProperty("cell", "SELECTOR.out.keyId");
        JsonObject slice = new JsonObject();
        slice.add("inputPorts", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        JsonArray members = new JsonArray();
        members.add(member);
        JsonObject closure = new JsonObject();
        closure.add("members", members);
        return closure;
    }

    private static String selectorOutputPort(JsonObject producer) {
        return producer.getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("output").get("portId").getAsString();
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

    private static JsonObject typedRegion(
            String regionId, String method, String[] fieldTypes) {
        JsonObject region = new JsonObject();
        region.addProperty("schemaVersion", 3);
        region.addProperty("kind", "SYMBOLIC_REGION");
        region.addProperty("regionId", regionId);
        JsonArray sources = new JsonArray();
        for (int index = 0; index < fieldTypes.length; index++) {
            JsonObject source = new JsonObject();
            source.addProperty("schemaVersion",
                    StaticSymbolicSourceDeclaration.SCHEMA_VERSION);
            source.addProperty("kind", StaticSymbolicSourceDeclaration.KIND);
            source.addProperty("authority",
                    StaticSymbolicSourceDeclaration.AUTHORITY);
            source.addProperty("sourceId", "MATRIX." + method + "." + index);
            source.addProperty("fieldSignature",
                    typedField(fieldTypes[index], index));
            source.addProperty("declarationMethod", "<Node: void "
                    + method + "Symbols()>");
            source.addProperty("declarationUnitIndex", index);
            sources.add(source);
        }
        region.add(StaticSymbolicSourceDeclaration.FIELD, sources);
        return region;
    }

    private static String typedField(String type, int index) {
        return "<Node: " + type + " value" + index + ">";
    }

    private static String[] types(String... types) {
        return types;
    }

    private static SourceShape shape(
            String name, String[] types, int... demanded) {
        Set<Integer> indexes = new LinkedHashSet<>();
        for (int index : demanded) indexes.add(index);
        return new SourceShape(name, types, indexes);
    }

    private static final class SourceShape {
        private final String name;
        private final String[] types;
        private final Set<Integer> demanded;

        private SourceShape(String name, String[] types,
                            Set<Integer> demanded) {
            this.name = name;
            this.types = types;
            this.demanded = demanded;
        }
    }

    private static void addRegionPublishPhases(
            JsonObject task, JsonObject region, String occurrence) {
        JsonArray phases = new JsonArray();
        long event = 10L;
        for (JsonElement element : region.getAsJsonArray(
                StaticSymbolicSourceDeclaration.FIELD)) {
            JsonObject source = element.getAsJsonObject();
            phases.add(sourcePhase(source.get("sourceId").getAsString(),
                    source.get("fieldSignature").getAsString(), occurrence,
                    ConfiguredSourcePhaseContract.Phase.PUBLISH,
                    source.get("declarationMethod").getAsString(),
                    source.get("declarationUnitIndex").getAsInt(),
                    event++, 101L));
        }
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
    }

    private static JsonObject sourcePhase(
            String sourceId, String field, String occurrence,
            ConfiguredSourcePhaseContract.Phase phase, String method,
            int unit, long event, long callId) {
        return sourcePhase(sourceId, field, occurrence, phase, method,
                unit, 1, event, callId);
    }

    private static JsonObject sourcePhase(
            String sourceId, String field, String occurrence,
            ConfiguredSourcePhaseContract.Phase phase, String method,
            int unit, int ordinal, long event, long callId) {
        java.util.Map<String, Object> declaration =
                ConfiguredSourcePhaseContract.declaration(
                        phase, sourceId, field, method, unit);
        ConfiguredSourcePhaseContract.Declaration decoded =
                ConfiguredSourcePhaseContract.declarationsOf(
                        Collections.singletonList(declaration)).get(0);
        java.util.Map<String, Object> encoded =
                ConfiguredSourcePhaseContract.occurrence(decoded,
                        occurrence, ordinal, event, callId, event,
                        method, Collections.singletonList(callId));
        return GSON.toJsonTree(encoded).getAsJsonObject();
    }
}
