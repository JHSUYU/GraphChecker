package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

public class RuntimeRegionPlannerTest {
    private static final Gson GSON = new Gson();
    private static final String MAIN =
            "<test.ConstructorProducer: void main(java.lang.String[])>";
    private static final String CONSTRUCTOR =
            "<test.ConstructorProducer$Value: void <init>(int)>";
    private static final String FIELD =
            "<test.ConstructorProducer$Value: int value>";
    private static final String OTHER_FIELD =
            "<test.ConstructorProducer$Value: int decoy>";
    private static final String CONSTRUCTOR_PARAMETER =
            CONSTRUCTOR + ".param0:int";
    private static final String OUTER =
            "<test.ConstructorProducer: void build(int)>";
    private static final String OUTER_PARAMETER = OUTER + ".param0:int";
    private static final String TARGET =
            CONSTRUCTOR + "#u8#exception:test.Target";
    private static final int RECEIVER = 41;
    private static final String SLICE_PRODUCER =
            "<test.SliceProducer: void compute(int,int)>";
    private static final String SLICE_CONSUMER =
            "<test.SliceConsumer: void consume()>";
    private static final String SLICE_INPUT_A =
            SLICE_PRODUCER + ".param0:int";
    private static final String SLICE_INPUT_B =
            SLICE_PRODUCER + ".param1:int";
    private static final String BUS_VALUE =
            "<test.SliceBus: int value>";
    private static final String SLICE_TARGET =
            SLICE_CONSUMER + "#u5#exception:test.Target";

    @Test
    public void exactConstructorFieldWriterBecomesRuntimeRoot()
            throws Exception {
        RuntimeRegionPlanner.Result result = plan(Collections.singletonList(
                fieldWrite(4, FIELD, RECEIVER)));

        assertEquals(1, result.regionPlans.size());
        assertFalse(result.regionPlans.get(0).containsKey("test"));
        Map<String, Object> selector = map(
                result.regionPlans.get(0).get("rootSelector"));
        assertEquals(CONSTRUCTOR, selector.get("method"));
        assertTrue(String.valueOf(result.regionPlans.get(0).get(
                "regionInstanceId")).endsWith("#call2"));
        List<Map<String, Object>> symbolize = symbolize(
                result.regionPlans.get(0));
        assertEquals(1, symbolize.size());
        assertEquals(CONSTRUCTOR_PARAMETER,
                symbolize.get(0).get("cell"));
        assertEquals("ROOT_ARGUMENT",
                symbolize.get(0).get("sourceKind"));
        assertEquals("ARGUMENT", symbolize.get(0).get("location"));
        assertCanonicalInputAction(symbolize.get(0));
    }

    @Test
    public void inventoryModeSlicesInputsAfterRuntimeRootSelection()
            throws Exception {
        Path directory = Files.createTempDirectory(
                "runtime-region-input-inventory");
        Path regions = directory.resolve("symbolic_regions.jsonl");
        Files.write(regions, Collections.singleton(inventoryRegionJson()),
                StandardCharsets.UTF_8);
        RuntimeRegionPlanner.MethodEvent main =
                new RuntimeRegionPlanner.MethodEvent(
                        1L, "inventory-root", "test-process", "main",
                        1L, MAIN, 0, "", 1L, 0L, 0L);
        RuntimeRegionPlanner.MethodEvent constructor =
                new RuntimeRegionPlanner.MethodEvent(
                        2L, "inventory-root", "test-process", "main",
                        1L, CONSTRUCTOR, RECEIVER,
                        "test.ConstructorProducer$Value",
                        2L, 1L, 1L);

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planInventory(regions.toFile(),
                        Arrays.asList(main, constructor),
                        Collections.<RuntimeRegionPlanner.RuntimeEvent>
                                emptyList(),
                        Arrays.asList(fieldWrite(4, FIELD, RECEIVER),
                                fieldRead(5, FIELD, RECEIVER)));

        assertTrue(result.regionPlans.isEmpty());
        assertTrue(result.edgeValidations.isEmpty());
        assertEquals(1, result.runtimeInstances.size());
        assertEquals(3, result.staticInputCandidateCount);
        assertEquals(3, result.runtimeInputCandidateOccurrenceCount);
        assertEquals(2, result.runtimeRegionInputCount);
        assertEquals(1, result.runtimePrunedInputCandidateCount);
        Map<String, Object> inventory = result.runtimeInstances.get(0);
        assertEquals(true, inventory.get("inventoryOnly"));
        assertEquals(false, inventory.get("executable"));
        assertEquals(CONSTRUCTOR, inventory.get("concreteRootMethod"));
        assertEquals("POST_RUNTIME_SELECTION",
                inventory.get("regionInputAnalysisPhase"));
        assertEquals(3, inventory.get("staticInputCandidateCount"));
        assertEquals(1, inventory.get("runtimeRootArgumentInputCount"));
        assertEquals(1, inventory.get("runtimeObservedFieldInputCount"));
        assertEquals(1, inventory.get(
                "runtimePrunedInputCandidateCount"));
        assertEquals(2, inventory.get("regionInCount"));
        assertEquals(1, inventory.get("staticMethodCount"));
        assertEquals(1, inventory.get("observedMethodCount"));
        assertFalse(inventory.containsKey("staticMethods"));
        assertFalse(inventory.containsKey("observedMethods"));
        assertEquals(CONSTRUCTOR_PARAMETER,
                rows(inventory.get("regionInputs")).get(0).get("cell"));
        assertEquals(FIELD,
                rows(inventory.get("regionInputs")).get(1).get("cell"));
        assertEquals("NOT_COMPUTED_IN_INVENTORY_MODE",
                inventory.get("materializationStatus"));
    }

    @Test
    public void skeletonGraphUsesNearestSameThreadRegionAncestor()
            throws Exception {
        Path directory = Files.createTempDirectory(
                "runtime-region-skeleton");
        Path regions = directory.resolve("symbolic_regions.jsonl");
        Files.write(regions, Arrays.asList(
                skeletonRegionJson("REGION.MAIN", MAIN),
                skeletonRegionJson("REGION.OUTER", OUTER),
                skeletonRegionJson("REGION.CTOR", CONSTRUCTOR),
                skeletonRegionJson("REGION.CTOR.ALIAS", CONSTRUCTOR),
                skeletonRegionJson("REGION.LOOP", MAIN, CONSTRUCTOR,
                        Arrays.asList(MAIN, OUTER, CONSTRUCTOR))),
                StandardCharsets.UTF_8);
        String helper = "<test.Helper: void bridge()>";
        RuntimeRegionPlanner.MethodEvent main =
                new RuntimeRegionPlanner.MethodEvent(
                        1L, "skeleton", "process", "main", 1L,
                        MAIN, 0, "", 1L, 0L, 0L);
        RuntimeRegionPlanner.MethodEvent helperCall =
                new RuntimeRegionPlanner.MethodEvent(
                        2L, "skeleton", "process", "main", 1L,
                        helper, 0, "", 2L, 1L, 0L);
        RuntimeRegionPlanner.MethodEvent outer =
                new RuntimeRegionPlanner.MethodEvent(
                        3L, "skeleton", "process", "main", 1L,
                        OUTER, 0, "", 3L, 2L, 0L);
        RuntimeRegionPlanner.MethodEvent constructor =
                new RuntimeRegionPlanner.MethodEvent(
                        4L, "skeleton", "process", "main", 1L,
                        CONSTRUCTOR, RECEIVER,
                        "test.ConstructorProducer$Value",
                        4L, 3L, 0L);
        RuntimeRegionPlanner.MethodEvent crossThread =
                new RuntimeRegionPlanner.MethodEvent(
                        5L, "skeleton", "process", "worker", 2L,
                        CONSTRUCTOR, RECEIVER,
                        "test.ConstructorProducer$Value",
                        5L, 4L, 0L);
        RuntimeRegionPlanner.MethodEvent secondEpoch =
                new RuntimeRegionPlanner.MethodEvent(
                        6L, "skeleton", "process", "main", 1L,
                        CONSTRUCTOR, RECEIVER,
                        "test.ConstructorProducer$Value",
                        6L, 3L, 0L);

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(regions.toFile(),
                        Arrays.asList(main, helperCall, outer, constructor,
                                crossThread, secondEpoch));

        assertEquals(5, result.runtimeInstances.size());
        assertEquals(3, result.runtimeGraphEdges.size());
        Map<String, Object> activation = result.runtimeInstances.get(0);
        assertEquals("RUNTIME_PHYSICAL_REGION_ACTIVATION",
                activation.get("kind"));
        assertEquals(Arrays.asList("REGION.LOOP", "REGION.MAIN"),
                activation.get("regionIds"));
        assertEquals(Arrays.asList("CARRIER", "STEP"),
                activation.get("roles"));
        assertEquals("DEFERRED",
                activation.get("regionInputAnalysisPhase"));
        assertFalse(activation.containsKey("regionInputs"));
        assertFalse(activation.containsKey("regionOutputs"));

        Map<String, Object> first = result.runtimeGraphEdges.get(0);
        assertEquals("SAME_THREAD_CALL_ANCESTRY", first.get("kind"));
        assertEquals(1L, first.get("fromRootCallId"));
        assertEquals(3L, first.get("toRootCallId"));
        Map<String, Object> second = result.runtimeGraphEdges.get(1);
        assertEquals(3L, second.get("fromRootCallId"));
        assertEquals(4L, second.get("toRootCallId"));
        Map<String, Object> epoch = result.runtimeInstances.get(2);
        assertEquals(Arrays.asList("REGION.CTOR", "REGION.CTOR.ALIAS",
                        "REGION.LOOP"), epoch.get("regionIds"));
        assertEquals(Arrays.asList("REGION.CTOR", "REGION.CTOR.ALIAS"),
                epoch.get("carrierRegionIds"));
        assertEquals(Arrays.asList("REGION.CTOR", "REGION.CTOR.ALIAS",
                        "REGION.LOOP"), epoch.get("stepRegionIds"));
        List<?> epochRoots = (List<?>) epoch.get("staticRootMethods");
        List<?> crossThreadRoots = (List<?>) result.runtimeInstances.get(3)
                .get("staticRootMethods");
        assertSame(epochRoots.get(0), crossThreadRoots.get(0));
        for (Map<String, Object> edge : result.runtimeGraphEdges) {
            assertFalse(edge.get("fromActivationId").equals(
                    edge.get("toActivationId")));
            assertFalse(Long.valueOf(5L).equals(edge.get("toRootCallId")));
        }
    }

    @Test
    public void skeletonAuthorityCacheMatchesUncachedRootSelection()
            throws Exception {
        Path directory = Files.createTempDirectory(
                "runtime-region-skeleton-authority-cache");
        Path regions = directory.resolve("symbolic_regions.jsonl");
        Path fullRegions = directory.resolve("full_regions.jsonl");
        String anchor = "<test.Cache: void anchor()>";
        String exactRoot = "<test.Cache: void exactRoot()>";
        String exclusiveRoot = "<test.Cache: void unobservedRoot()>";
        String exclusiveBridge = "<test.Cache: void exclusiveBridge()>";
        List<String> rows = new ArrayList<>();
        List<String> fullRows = new ArrayList<>();
        String exactRow = skeletonRegionJson("REGION.EXACT", exactRoot,
                anchor, Arrays.asList(exactRoot, anchor));
        rows.add(exactRow);
        fullRows.add(fullRegionJson(exactRow));
        String exclusiveRow = skeletonRegionJson(
                "REGION.EXCLUSIVE", exclusiveRoot,
                anchor, Arrays.asList(exclusiveRoot, exclusiveBridge,
                        anchor));
        rows.add(exclusiveRow);
        fullRows.add(fullRegionJson(exclusiveRow));
        for (int index = 0; index < 256; index++) {
            String decoy = "<test.Cache: void decoy" + index + "()>";
            String decoyRow = skeletonRegionJson(
                    "REGION.DECOY." + index, decoy, anchor,
                    Arrays.asList(decoy, anchor));
            rows.add(decoyRow);
            fullRows.add(fullRegionJson(decoyRow));
        }
        Files.write(regions, rows, StandardCharsets.UTF_8);
        Files.write(fullRegions, fullRows, StandardCharsets.UTF_8);

        RuntimeRegionPlanner.MethodEvent main =
                new RuntimeRegionPlanner.MethodEvent(
                        1L, "authority-cache", "process", "main", 1L,
                        MAIN, 0, "", 1L, 0L, 0L);
        RuntimeRegionPlanner.MethodEvent exact =
                new RuntimeRegionPlanner.MethodEvent(
                        2L, "authority-cache", "process", "main", 1L,
                        exactRoot, 0, "", 2L, 1L, 0L);
        RuntimeRegionPlanner.MethodEvent exactAnchor =
                new RuntimeRegionPlanner.MethodEvent(
                        3L, "authority-cache", "process", "main", 1L,
                        anchor, 0, "", 3L, 2L, 0L);
        RuntimeRegionPlanner.MethodEvent bridge =
                new RuntimeRegionPlanner.MethodEvent(
                        4L, "authority-cache", "process", "main", 1L,
                        exclusiveBridge, 0, "", 4L, 1L, 0L);
        RuntimeRegionPlanner.MethodEvent exclusiveAnchor =
                new RuntimeRegionPlanner.MethodEvent(
                        5L, "authority-cache", "process", "main", 1L,
                        anchor, 0, "", 5L, 4L, 0L);
        List<RuntimeRegionPlanner.MethodEvent> trace = Arrays.asList(
                main, exact, exactAnchor, bridge, exclusiveAnchor);

        RuntimeRegionPlanner.Result uncached =
                RuntimeRegionPlanner.planInventory(fullRegions.toFile(),
                        trace,
                        Collections.<RuntimeRegionPlanner.RuntimeEvent>
                                emptyList(),
                        Collections.<RuntimeRegionPlanner.FieldAccessEvent>
                                emptyList());
        RuntimeRegionPlanner.Result cached =
                RuntimeRegionPlanner.planSkeletonGraph(
                        regions.toFile(), trace);

        Map<String, Long> uncachedRoots = new LinkedHashMap<>();
        for (Map<String, Object> instance : uncached.runtimeInstances) {
            uncachedRoots.put(String.valueOf(instance.get("regionId")),
                    ((Number) instance.get("rootCallId")).longValue());
        }
        Map<String, Long> cachedRoots = new LinkedHashMap<>();
        for (Map<String, Object> activation : cached.runtimeInstances) {
            for (Object region : (List<?>) activation.get(
                    "carrierRegionIds")) {
                cachedRoots.put(String.valueOf(region),
                        ((Number) activation.get("rootCallId")).longValue());
            }
        }
        assertEquals(uncachedRoots, cachedRoots);
        assertEquals(Long.valueOf(2L), cachedRoots.get("REGION.EXACT"));
        assertEquals(Long.valueOf(4L),
                cachedRoots.get("REGION.EXCLUSIVE"));
        assertEquals(2, cachedRoots.size());
    }

    @Test
    public void malformedUnobservedSkeletonRowsFailClosed()
            throws Exception {
        Path directory = Files.createTempDirectory(
                "runtime-region-malformed-skeleton");
        Path regions = directory.resolve("symbolic_regions.jsonl");
        String unobserved = "<test.Unobserved: void run()>";
        String valid = skeletonRegionJson("REGION.BAD", unobserved);
        List<String> malformed = Arrays.asList(
                valid.replace("\"kind\":\"REGION_SKELETON\"",
                        "\"kind\":\"WRONG\""),
                valid.replace("\"regionId\":\"REGION.BAD\"",
                        "\"regionId\":\"\""),
                valid.replace("\"rootMethod\":\"" + unobserved + "\"",
                        "\"rootMethod\":\"\""),
                valid.replace("\"anchorMethod\":\"" + unobserved + "\"",
                        "\"anchorMethod\":\"\""),
                valid.replace("\"methods\":[\"" + unobserved + "\"]",
                        "\"methods\":[]"),
                skeletonRegionJson("REGION.BAD", unobserved, MAIN,
                        Collections.singletonList(MAIN)),
                skeletonRegionJson("REGION.BAD", MAIN, unobserved,
                        Collections.singletonList(MAIN)));
        RuntimeRegionPlanner.MethodEvent observed =
                new RuntimeRegionPlanner.MethodEvent(
                        1L, "malformed", "process", "main", 1L,
                        MAIN, 0, "", 1L, 0L, 0L);

        for (String row : malformed) {
            Files.write(regions, Collections.singleton(row),
                    StandardCharsets.UTF_8);
            try {
                RuntimeRegionPlanner.planSkeletonGraph(regions.toFile(),
                        Collections.singletonList(observed));
                throw new AssertionError(
                        "malformed unobserved row was silently skipped: "
                                + row);
            } catch (IllegalArgumentException expected) {
                assertTrue(expected.getMessage().contains("symbolic region"));
            }
        }

        Files.write(regions, Arrays.asList(valid, valid),
                StandardCharsets.UTF_8);
        try {
            RuntimeRegionPlanner.planSkeletonGraph(regions.toFile(),
                    Collections.singletonList(observed));
            throw new AssertionError(
                    "duplicate unobserved region id was silently skipped");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains(
                    "duplicate symbolic region id"));
        }
    }

    @Test
    public void regionReadersRejectTheOtherArtifactKind() throws Exception {
        Path directory = Files.createTempDirectory(
                "runtime-region-artifact-kind");
        Path regions = directory.resolve("symbolic_regions.jsonl");
        RuntimeRegionPlanner.MethodEvent observed =
                new RuntimeRegionPlanner.MethodEvent(
                        1L, "kind", "process", "main", 1L,
                        MAIN, 0, "", 1L, 0L, 0L);

        Files.write(regions, Collections.singleton(
                skeletonRegionJson("REGION.SKELETON", MAIN)),
                StandardCharsets.UTF_8);
        try {
            RuntimeRegionPlanner.planInventory(regions.toFile(),
                    Collections.singletonList(observed),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Collections.<RuntimeRegionPlanner.FieldAccessEvent>
                            emptyList());
            throw new AssertionError(
                    "normal reader accepted a skeleton artifact");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains(
                    "unsupported symbolic region kind"));
        }

        Files.write(regions, Collections.singleton(regionJson()),
                StandardCharsets.UTF_8);
        try {
            RuntimeRegionPlanner.planSkeletonGraph(regions.toFile(),
                    Collections.singletonList(observed));
            throw new AssertionError(
                    "skeleton reader accepted a full artifact");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains(
                    "unsupported symbolic region kind"));
        }
    }

    @Test
    public void fullSchemaTwoRegionKeepsOptionalAnchorCompatibility()
            throws Exception {
        Path directory = Files.createTempDirectory(
                "runtime-region-optional-anchor");
        Path regions = directory.resolve("symbolic_regions.jsonl");
        Files.write(regions, Collections.singleton(regionJson().replace(
                "\"anchorMethod\":\"" + CONSTRUCTOR + "\"",
                "\"anchorMethod\":\"\"")), StandardCharsets.UTF_8);

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planInventory(regions.toFile(),
                        Collections.<RuntimeRegionPlanner.MethodEvent>
                                emptyList(),
                        Collections.<RuntimeRegionPlanner.RuntimeEvent>
                                emptyList(),
                        Collections.<RuntimeRegionPlanner.FieldAccessEvent>
                                emptyList());

        assertEquals(1, result.staticRegionCount);
    }

    @Test
    public void inexactConstructorWritesDoNotFallBackToMain()
            throws Exception {
        assertNoPlan(Collections.singletonList(
                fieldWrite(5, FIELD, RECEIVER)));
        assertNoPlan(Collections.singletonList(
                fieldWrite(4, OTHER_FIELD, RECEIVER)));
        assertNoPlan(Collections.singletonList(
                fieldWrite(4, FIELD, RECEIVER + 1)));
        assertNoPlan(Collections.<RuntimeRegionPlanner.FieldAccessEvent>
                emptyList());
    }

    @Test
    public void outerReplayDoesNotSymbolizeNestedConstructorFormal()
            throws Exception {
        RuntimeRegionPlanner.Result result = planOuterReplay();

        assertEquals(1, result.regionPlans.size());
        Map<String, Object> selector = map(
                result.regionPlans.get(0).get("rootSelector"));
        assertEquals(OUTER, selector.get("method"));
        List<Map<String, Object>> symbolize = symbolize(
                result.regionPlans.get(0));
        assertEquals(1, symbolize.size());
        assertEquals(OUTER_PARAMETER, symbolize.get(0).get("cell"));
        assertEquals("ROOT_ARGUMENT",
                symbolize.get(0).get("sourceKind"));
    }

    @Test
    public void parameterFieldProjectionIsNotAFormalRootArgument() {
        assertTrue(RuntimeRegionPlanner.exactRootParameter(
                CONSTRUCTOR, CONSTRUCTOR_PARAMETER));
        assertTrue(!RuntimeRegionPlanner.exactRootParameter(
                CONSTRUCTOR, CONSTRUCTOR_PARAMETER + "#field:value"));
        assertTrue(!RuntimeRegionPlanner.exactRootParameter(
                OUTER, CONSTRUCTOR_PARAMETER));
    }

    @Test
    public void outputSliceKeepsAlternateInputAndRejectsIncidentalBranch()
            throws Exception {
        RuntimeRegionPlanner.Result result = planOutputSlice();
        Map<String, Object> producer = regionPlan(result, "REGION.PRODUCER");
        Map<String, Object> goal = goal(producer,
                "OUTPUT_RELATION_CLOSURE");
        assertTrue(String.valueOf(goal),
                goal.containsKey(OutputClosureContract.FIELD));
        OutputClosureContract closure = OutputClosureCodec.decode(
                GSON.toJsonTree(goal).getAsJsonObject());

        assertEquals(new LinkedHashSet<>(Arrays.asList(
                        "REGION.PRODUCER.in.0",
                        "REGION.PRODUCER.in.1")),
                closure.executionScope().inputPorts());
        assertEquals(Collections.singleton(
                        SLICE_PRODUCER + "#u10"),
                closure.executionScope().branchSites());
        assertEquals(2, rows(goal.get("symbolize")).size());
        for (Map<String, Object> action : rows(goal.get("symbolize"))) {
            assertCanonicalInputAction(action);
        }
    }

    @Test
    public void latestSequentialWriterAloneSuppliesTheDownstreamRead()
            throws Exception {
        RuntimeRegionPlanner.Result result = planSequentialWriters();
        List<Map<String, Object>> producers = new java.util.ArrayList<>();
        for (Map<String, Object> plan : result.regionPlans) {
            if ("REGION.PRODUCER".equals(plan.get("regionId"))) {
                producers.add(plan);
            }
        }

        assertEquals(String.valueOf(result.regionPlans), 1,
                producers.size());
        assertEquals(2, map(producers.get(0).get(
                "rootSelector")).get("ordinal"));
        Map<String, Object> output = goal(producers.get(0),
                "OUTPUT_RELATION_CLOSURE");
        List<Map<String, Object>> bindings = rows(
                output.get("edgeBindings"));
        assertEquals(String.valueOf(output), 1, bindings.size());
        assertEquals(12L, bindings.get(0).get("writerEventSeq"));
        assertEquals(15L, bindings.get(0).get("readerEventSeq"));
    }

    private static void assertNoPlan(
            List<RuntimeRegionPlanner.FieldAccessEvent> writes)
            throws Exception {
        assertTrue(plan(writes).regionPlans.isEmpty());
    }

    private static void assertCanonicalInputAction(
            Map<String, Object> action) {
        for (String retired : Arrays.asList(
                "fieldEventSeq", "accessKind",
                "accessorInvocationId", "accessorRuntimeType",
                "objectId", "runtimeType", "primitiveValue",
                "bindingMode")) {
            assertFalse(retired + " leaked into " + action,
                    action.containsKey(retired));
        }
    }

    private static RuntimeRegionPlanner.Result plan(
            List<RuntimeRegionPlanner.FieldAccessEvent> writes)
            throws Exception {
        Path directory = Files.createTempDirectory(
                "runtime-constructor-root");
        Path regions = directory.resolve("symbolic_regions.jsonl");
        Path graph = directory.resolve("static_dataflow_edges.jsonl");
        Files.write(regions, Collections.singleton(regionJson()),
                StandardCharsets.UTF_8);
        Files.write(graph, Collections.singleton(constructorGraphJson()),
                StandardCharsets.UTF_8);

        RuntimeRegionPlanner.MethodEvent main =
                new RuntimeRegionPlanner.MethodEvent(
                        1L, "constructor-root", "test-process", "main",
                        1L, MAIN, 0, "", 1L, 0L, 0L);
        RuntimeRegionPlanner.MethodEvent constructor =
                new RuntimeRegionPlanner.MethodEvent(
                        2L, "constructor-root", "test-process", "main",
                        1L, CONSTRUCTOR, RECEIVER,
                        "test.ConstructorProducer$Value",
                        2L, 1L, 1L);
        return RuntimeRegionPlanner.plan(regions.toFile(), null,
                graph.toFile(), Arrays.asList(main, constructor),
                Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                writes);
    }

    private static RuntimeRegionPlanner.Result planOuterReplay()
            throws Exception {
        Path directory = Files.createTempDirectory(
                "runtime-outer-parameter-root");
        Path regions = directory.resolve("symbolic_regions.jsonl");
        Path graph = directory.resolve("static_dataflow_edges.jsonl");
        Files.write(regions, Collections.singleton(outerRegionJson()),
                StandardCharsets.UTF_8);
        Files.write(graph, Arrays.asList(outerArgumentGraphJson(),
                constructorGuardGraphJson()), StandardCharsets.UTF_8);

        RuntimeRegionPlanner.MethodEvent outer =
                new RuntimeRegionPlanner.MethodEvent(
                        1L, "outer-root", "test-process", "main", 1L,
                        OUTER, 0, "", 1L, 0L, 0L);
        RuntimeRegionPlanner.MethodEvent constructor =
                new RuntimeRegionPlanner.MethodEvent(
                        2L, "outer-root", "test-process", "main", 1L,
                        CONSTRUCTOR, RECEIVER,
                        "test.ConstructorProducer$Value",
                        2L, 1L, 1L);
        return RuntimeRegionPlanner.plan(regions.toFile(), null,
                graph.toFile(), Arrays.asList(outer, constructor),
                Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                Collections.<RuntimeRegionPlanner.FieldAccessEvent>
                        emptyList());
    }

    private static RuntimeRegionPlanner.Result planOutputSlice()
            throws Exception {
        RuntimeRegionPlanner.MethodEvent producer =
                new RuntimeRegionPlanner.MethodEvent(
                        1L, "slice-authority", "test-process",
                        "producer", 1L, SLICE_PRODUCER, 71,
                        "test.SliceProducer", 1L, 0L, 0L);
        RuntimeRegionPlanner.MethodEvent consumer =
                new RuntimeRegionPlanner.MethodEvent(
                        8L, "slice-authority", "test-process",
                        "consumer", 2L, SLICE_CONSUMER, 72,
                        "test.SliceConsumer", 2L, 0L, 0L);
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                runtimeArgument(2L, 0, "3"),
                runtimeArgument(3L, 1, "9"),
                runtimeBranch(4L, SLICE_PRODUCER, 1L,
                        SLICE_PRODUCER + "#u10"),
                runtimeBranch(5L, SLICE_PRODUCER, 1L,
                        SLICE_PRODUCER + "#u99"),
                runtimeBranch(10L, SLICE_CONSUMER, 2L,
                        SLICE_CONSUMER + "#u5"));
        List<RuntimeRegionPlanner.FieldAccessEvent> fields = Arrays.asList(
                new RuntimeRegionPlanner.FieldAccessEvent(
                        6L, "FIELD_WRITE", SLICE_PRODUCER, 1L,
                        20, "", BUS_VALUE, 90, 0, "3", "", false),
                new RuntimeRegionPlanner.FieldAccessEvent(
                        9L, "FIELD_READ", SLICE_CONSUMER, 2L,
                        4, "", BUS_VALUE, 90, 0, "3", "", false));
        return planOutputSlice(
                Arrays.asList(producer, consumer), runtime, fields);
    }

    private static RuntimeRegionPlanner.Result planSequentialWriters()
            throws Exception {
        RuntimeRegionPlanner.MethodEvent first =
                new RuntimeRegionPlanner.MethodEvent(
                        1L, "slice-authority", "test-process",
                        "producer", 1L, SLICE_PRODUCER, 71,
                        "test.SliceProducer", 1L, 0L, 0L);
        RuntimeRegionPlanner.MethodEvent second =
                new RuntimeRegionPlanner.MethodEvent(
                        7L, "slice-authority", "test-process",
                        "producer", 1L, SLICE_PRODUCER, 71,
                        "test.SliceProducer", 2L, 0L, 0L);
        RuntimeRegionPlanner.MethodEvent consumer =
                new RuntimeRegionPlanner.MethodEvent(
                        14L, "slice-authority", "test-process",
                        "consumer", 2L, SLICE_CONSUMER, 72,
                        "test.SliceConsumer", 3L, 0L, 0L);
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                runtimeArgument(2L, 1L, 0, "3"),
                runtimeArgument(3L, 1L, 1, "4"),
                runtimeBranch(4L, SLICE_PRODUCER, 1L,
                        SLICE_PRODUCER + "#u10"),
                runtimeArgument(8L, 2L, 0, "9"),
                runtimeArgument(9L, 2L, 1, "10"),
                runtimeBranch(10L, SLICE_PRODUCER, 2L,
                        SLICE_PRODUCER + "#u10"),
                runtimeBranch(16L, SLICE_CONSUMER, 3L,
                        SLICE_CONSUMER + "#u5"));
        List<RuntimeRegionPlanner.FieldAccessEvent> fields = Arrays.asList(
                new RuntimeRegionPlanner.FieldAccessEvent(
                        6L, "FIELD_WRITE", SLICE_PRODUCER, 1L,
                        20, "", BUS_VALUE, 90, 0, "3", "", false),
                new RuntimeRegionPlanner.FieldAccessEvent(
                        12L, "FIELD_WRITE", SLICE_PRODUCER, 2L,
                        20, "", BUS_VALUE, 90, 0, "9", "", false),
                new RuntimeRegionPlanner.FieldAccessEvent(
                        15L, "FIELD_READ", SLICE_CONSUMER, 3L,
                        4, "", BUS_VALUE, 90, 0, "9", "", false));
        return planOutputSlice(Arrays.asList(first, second, consumer),
                runtime, fields);
    }

    private static RuntimeRegionPlanner.Result planOutputSlice(
            List<RuntimeRegionPlanner.MethodEvent> methods,
            List<RuntimeRegionPlanner.RuntimeEvent> runtime,
            List<RuntimeRegionPlanner.FieldAccessEvent> fields)
            throws Exception {
        Path directory = Files.createTempDirectory(
                "runtime-output-slice-authority");
        Path regions = directory.resolve("symbolic_regions.jsonl");
        Path regionEdges = directory.resolve("region_edges.jsonl");
        Path graph = directory.resolve("static_dataflow_edges.jsonl");
        Files.write(regions, Arrays.asList(producerSliceRegionJson(),
                consumerSliceRegionJson()), StandardCharsets.UTF_8);
        Files.write(regionEdges, Collections.singleton(
                sliceRegionEdgeJson()), StandardCharsets.UTF_8);
        Files.write(graph, Arrays.asList(producerInputGraphJson(
                        "DF.SLICE.A", SLICE_INPUT_A, "value_flow", 20),
                producerInputGraphJson("DF.SLICE.B", SLICE_INPUT_B,
                        "alternate_path_value_flow", 21),
                consumerGuardGraphJson()), StandardCharsets.UTF_8);
        return RuntimeRegionPlanner.plan(regions.toFile(),
                regionEdges.toFile(), graph.toFile(), methods, runtime,
                fields);
    }

    private static RuntimeRegionPlanner.RuntimeEvent runtimeArgument(
            long seq, int index, String value) {
        return runtimeArgument(seq, 1L, index, value);
    }

    private static RuntimeRegionPlanner.RuntimeEvent runtimeArgument(
            long seq, long callId, int index, String value) {
        return new RuntimeRegionPlanner.RuntimeEvent(
                seq, "METHOD_ARGUMENT", SLICE_PRODUCER, callId,
                0L, 0L, "", index, "int", 0, value, false, false);
    }

    private static RuntimeRegionPlanner.RuntimeEvent runtimeBranch(
            long seq, String method, long callId, String site) {
        return new RuntimeRegionPlanner.RuntimeEvent(
                seq, "BRANCH", method, callId, 0L, 0L, site,
                -1, "", 0, "", true, true);
    }

    private static RuntimeRegionPlanner.FieldAccessEvent fieldWrite(
            int unitIndex, String field, int receiver) {
        return new RuntimeRegionPlanner.FieldAccessEvent(
                3L, "FIELD_WRITE", CONSTRUCTOR, 2L, unitIndex, "",
                field, receiver, 0, "7", "", false);
    }

    private static RuntimeRegionPlanner.FieldAccessEvent fieldRead(
            int unitIndex, String field, int receiver) {
        return new RuntimeRegionPlanner.FieldAccessEvent(
                4L, "FIELD_READ", CONSTRUCTOR, 2L, unitIndex, "",
                field, receiver, 0, "7", "", false);
    }

    private static String inventoryRegionJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"regionId\":\"REGION.CTOR\","
                + "\"rootMethod\":\"" + CONSTRUCTOR + "\","
                + "\"anchorMethod\":\"" + CONSTRUCTOR + "\","
                + "\"selection\":\"INVENTORY_SEED_ONLY_STATIC_FRONTIER\","
                + "\"methods\":[\"" + CONSTRUCTOR + "\"],"
                + "\"symbolicInputs\":[{"
                + "\"portId\":\"REGION.CTOR.in.0\","
                + "\"cell\":\"" + CONSTRUCTOR_PARAMETER + "\","
                + "\"javaType\":\"int\","
                + "\"sourceKind\":\"REGION_LIVE_IN\","
                + "\"projection\":\"value\"},{"
                + "\"portId\":\"REGION.CTOR.in.1\","
                + "\"cell\":\"" + FIELD + "\","
                + "\"javaType\":\"int\","
                + "\"sourceKind\":\"SHARED_HEAP\","
                + "\"projection\":\"value\"},{"
                + "\"portId\":\"REGION.CTOR.in.2\","
                + "\"cell\":\"" + OTHER_FIELD + "\","
                + "\"javaType\":\"int\","
                + "\"sourceKind\":\"SHARED_HEAP\","
                + "\"projection\":\"value\"}],"
                + "\"inputSelectionComplete\":false,"
                + "\"unresolvedInputs\":[{\"reason\":\"CHEAP\"}],"
                + "\"outputs\":[{"
                + "\"portId\":\"REGION.CTOR.out.0\","
                + "\"cell\":\"" + FIELD + "\","
                + "\"javaType\":\"int\","
                + "\"kind\":\"HEAP_STATE\"}],"
                + "\"outputSlices\":[],"
                + "\"branchPolicies\":[]"
                + "}";
    }

    private static String skeletonRegionJson(String id, String method) {
        return skeletonRegionJson(id, method, method,
                Collections.singletonList(method));
    }

    private static String skeletonRegionJson(
            String id, String root, String anchor, List<String> methods) {
        StringBuilder encodedMethods = new StringBuilder();
        for (String method : methods) {
            if (encodedMethods.length() > 0) encodedMethods.append(',');
            encodedMethods.append('\"').append(method).append('\"');
        }
        return "{"
                + "\"schemaVersion\":2,"
                + "\"kind\":\"REGION_SKELETON\","
                + "\"regionId\":\"" + id + "\","
                + "\"rootMethod\":\"" + root + "\","
                + "\"anchorMethod\":\"" + anchor + "\","
                + "\"selection\":\"REGION_SKELETON_ONLY\","
                + "\"methods\":[" + encodedMethods + "],"
                + "\"symbolicInputs\":[],"
                + "\"outputs\":[],"
                + "\"outputSlices\":[],"
                + "\"branchPolicies\":[]"
                + "}";
    }

    private static String fullRegionJson(String skeletonRow) {
        return skeletonRow.replace(
                "\"kind\":\"REGION_SKELETON\",", "")
                .replace("\"selection\":\"REGION_SKELETON_ONLY\",",
                        "\"selection\":\"STATIC_OVER_APPROXIMATION\",");
    }

    private static String regionJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"regionId\":\"REGION.CTOR\","
                + "\"rootMethod\":\"" + MAIN + "\","
                + "\"anchorMethod\":\"" + CONSTRUCTOR + "\","
                + "\"selection\":\"EXCEPTION_BACKWARD_CAUSAL_CLOSURE\","
                + "\"methods\":[\"" + MAIN + "\",\"" + CONSTRUCTOR + "\"],"
                + "\"symbolicInputs\":[{"
                + "\"portId\":\"REGION.CTOR.in.0\","
                + "\"cell\":\"" + CONSTRUCTOR_PARAMETER + "\","
                + "\"javaType\":\"int\","
                + "\"sourceKind\":\"REGION_LIVE_IN\","
                + "\"projection\":\"value\"}],"
                + "\"inputSelectionComplete\":true,"
                + "\"outputs\":[{"
                + "\"portId\":\"REGION.CTOR.out.0\","
                + "\"cell\":\"" + FIELD + "\","
                + "\"javaType\":\"int\","
                + "\"kind\":\"HEAP_STATE\"}],"
                + "\"outputSlices\":[{"
                + "\"outputPort\":\"REGION.CTOR.out.0\","
                + "\"outputCell\":\"" + FIELD + "\","
                + "\"inputPorts\":[\"REGION.CTOR.in.0\"],"
                + "\"inputBindings\":[{"
                + "\"dependencyCell\":\"" + CONSTRUCTOR_PARAMETER + "\","
                + "\"inputPort\":\"REGION.CTOR.in.0\","
                + "\"bindingAuthority\":\"OUTPUT_SLICE_FRONTIER_PROMOTION\","
                + "\"dependencyMethods\":[\"" + CONSTRUCTOR + "\"]}],"
                + "\"methods\":[\"" + CONSTRUCTOR + "\"],"
                + "\"sites\":[\"" + CONSTRUCTOR + "#u4\"],"
                + "\"causalEdgeIds\":[],"
                + "\"captureBindings\":[],"
                + "\"captureBindingIssues\":[],"
                + "\"inputGaps\":[],"
                + "\"truncationReasons\":[]}],"
                + "\"branchPolicies\":[]"
                + "}";
    }

    private static String constructorGraphJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"id\":\"DF.TEST\","
                + "\"kind\":\"field_write\","
                + "\"transferKind\":\"HEAP_WRITE\","
                + "\"semanticMode\":\"ASSERTABLE\","
                + "\"relation\":\"value_flow\","
                + "\"fromCell\":\"" + CONSTRUCTOR_PARAMETER + "\","
                + "\"toCell\":\"" + FIELD + "\","
                + "\"method\":\"" + CONSTRUCTOR + "\","
                + "\"siteId\":\"" + CONSTRUCTOR + "#u4\","
                + "\"unitIndex\":4"
                + "}";
    }

    private static String outerRegionJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"regionId\":\"REGION.OUTER\","
                + "\"rootMethod\":\"" + OUTER + "\","
                + "\"anchorMethod\":\"" + CONSTRUCTOR + "\","
                + "\"selection\":\"EXCEPTION_BACKWARD_CAUSAL_CLOSURE\","
                + "\"methods\":[\"" + OUTER + "\",\"" + CONSTRUCTOR + "\"],"
                + "\"symbolicInputs\":[{"
                + "\"portId\":\"REGION.OUTER.in.0\","
                + "\"cell\":\"" + OUTER_PARAMETER + "\","
                + "\"javaType\":\"int\","
                + "\"sourceKind\":\"ROOT_ARGUMENT\","
                + "\"projection\":\"value\"},{"
                + "\"portId\":\"REGION.OUTER.in.1\","
                + "\"cell\":\"" + CONSTRUCTOR_PARAMETER + "\","
                + "\"javaType\":\"int\","
                + "\"sourceKind\":\"REGION_LIVE_IN\","
                + "\"projection\":\"value\"}],"
                + "\"inputSelectionComplete\":true,"
                + "\"outputs\":[{"
                + "\"portId\":\"REGION.OUTER.out.0\","
                + "\"cell\":\"" + TARGET + "\","
                + "\"javaType\":\"boolean\","
                + "\"kind\":\"FAILURE_PREDICATE\"}],"
                + "\"outputSlices\":[],"
                + "\"branchPolicies\":[{"
                + "\"siteId\":\"" + CONSTRUCTOR + "#u8\","
                + "\"policy\":\"EXPLORE\","
                + "\"guard\":\"p0 > 0\"}]"
                + "}";
    }

    private static String outerArgumentGraphJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"id\":\"DF.ARG\","
                + "\"kind\":\"call_argument\","
                + "\"transferKind\":\"ARGUMENT_BINDING\","
                + "\"semanticMode\":\"ASSERTABLE\","
                + "\"relation\":\"value_flow\","
                + "\"fromCell\":\"" + OUTER_PARAMETER + "\","
                + "\"toCell\":\"" + CONSTRUCTOR_PARAMETER + "\","
                + "\"method\":\"" + OUTER + "\","
                + "\"siteId\":\"" + OUTER + "#u2\","
                + "\"unitIndex\":2"
                + "}";
    }

    private static String constructorGuardGraphJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"id\":\"DF.GUARD\","
                + "\"kind\":\"guard_dependency\","
                + "\"transferKind\":\"GUARD\","
                + "\"semanticMode\":\"ASSERTABLE\","
                + "\"relation\":\"control_depends_on\","
                + "\"fromCell\":\"" + CONSTRUCTOR_PARAMETER + "\","
                + "\"toCell\":\"" + TARGET + "\","
                + "\"method\":\"" + CONSTRUCTOR + "\","
                + "\"siteId\":\"" + CONSTRUCTOR + "#u8\","
                + "\"unitIndex\":8"
                + "}";
    }

    private static String producerSliceRegionJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"regionId\":\"REGION.PRODUCER\","
                + "\"rootMethod\":\"" + SLICE_PRODUCER + "\","
                + "\"anchorMethod\":\"" + SLICE_PRODUCER + "\","
                + "\"selection\":\"DATAFLOW_REGION\","
                + "\"methods\":[\"" + SLICE_PRODUCER + "\"],"
                + "\"symbolicInputs\":["
                + sliceInputJson("REGION.PRODUCER.in.0", SLICE_INPUT_A)
                + ","
                + sliceInputJson("REGION.PRODUCER.in.1", SLICE_INPUT_B)
                + "],"
                + "\"inputSelectionComplete\":true,"
                + "\"outputs\":[{"
                + "\"portId\":\"REGION.PRODUCER.out.0\","
                + "\"cell\":\"" + BUS_VALUE + "\","
                + "\"javaType\":\"int\","
                + "\"kind\":\"HEAP_STATE\"}],"
                + "\"outputSlices\":[{"
                + "\"outputPort\":\"REGION.PRODUCER.out.0\","
                + "\"outputCell\":\"" + BUS_VALUE + "\","
                + "\"inputPorts\":[\"REGION.PRODUCER.in.0\","
                + "\"REGION.PRODUCER.in.1\"],"
                + "\"inputBindings\":["
                + sliceBindingJson("REGION.PRODUCER.in.0",
                SLICE_INPUT_A)
                + ","
                + sliceBindingJson("REGION.PRODUCER.in.1",
                SLICE_INPUT_B)
                + "],"
                + "\"methods\":[\"" + SLICE_PRODUCER + "\"],"
                + "\"sites\":[\"" + SLICE_PRODUCER + "#u10\"],"
                + "\"causalEdgeIds\":[\"DF.SLICE.A\",\"DF.SLICE.B\"],"
                + "\"captureBindings\":[],"
                + "\"captureBindingIssues\":[],"
                + "\"inputGaps\":[],"
                + "\"truncationReasons\":[]}],"
                + "\"branchPolicies\":["
                + branchPolicyJson(SLICE_PRODUCER + "#u10")
                + ","
                + branchPolicyJson(SLICE_PRODUCER + "#u99")
                + "]"
                + "}";
    }

    private static String consumerSliceRegionJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"regionId\":\"REGION.CONSUMER\","
                + "\"rootMethod\":\"" + SLICE_CONSUMER + "\","
                + "\"anchorMethod\":\"" + SLICE_CONSUMER + "\","
                + "\"selection\":\"EXCEPTION_BACKWARD_CAUSAL_CLOSURE\","
                + "\"methods\":[\"" + SLICE_CONSUMER + "\"],"
                + "\"symbolicInputs\":[{"
                + "\"portId\":\"REGION.CONSUMER.in.0\","
                + "\"cell\":\"" + BUS_VALUE + "\","
                + "\"javaType\":\"int\","
                + "\"sourceKind\":\"SHARED_HEAP\","
                + "\"projection\":\"value\"}],"
                + "\"inputSelectionComplete\":true,"
                + "\"outputs\":[{"
                + "\"portId\":\"REGION.CONSUMER.out.0\","
                + "\"cell\":\"" + SLICE_TARGET + "\","
                + "\"javaType\":\"boolean\","
                + "\"kind\":\"FAILURE_PREDICATE\"}],"
                + "\"outputSlices\":[],"
                + "\"branchPolicies\":["
                + branchPolicyJson(SLICE_CONSUMER + "#u5")
                + "]"
                + "}";
    }

    private static String sliceInputJson(String port, String cell) {
        return "{"
                + "\"portId\":\"" + port + "\","
                + "\"cell\":\"" + cell + "\","
                + "\"javaType\":\"int\","
                + "\"sourceKind\":\"ROOT_ARGUMENT\","
                + "\"projection\":\"value\""
                + "}";
    }

    private static String sliceBindingJson(String port, String cell) {
        return "{"
                + "\"dependencyCell\":\"" + cell + "\","
                + "\"inputPort\":\"" + port + "\","
                + "\"bindingAuthority\":\"OUTPUT_SLICE_FRONTIER_PROMOTION\","
                + "\"dependencyMethods\":[\"" + SLICE_PRODUCER + "\"]"
                + "}";
    }

    private static String branchPolicyJson(String site) {
        return "{"
                + "\"siteId\":\"" + site + "\","
                + "\"policy\":\"EXPLORE\","
                + "\"guard\":\"input > 0\""
                + "}";
    }

    private static String producerInputGraphJson(
            String id, String input, String relation, int unit) {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"id\":\"" + id + "\","
                + "\"kind\":\"local_value\","
                + "\"transferKind\":\"LOCAL\","
                + "\"semanticMode\":\"ASSERTABLE\","
                + "\"relation\":\"" + relation + "\","
                + "\"fromCell\":\"" + input + "\","
                + "\"toCell\":\"" + BUS_VALUE + "\","
                + "\"method\":\"" + SLICE_PRODUCER + "\","
                + "\"siteId\":\"" + SLICE_PRODUCER + "#u" + unit + "\","
                + "\"unitIndex\":" + unit
                + "}";
    }

    private static String consumerGuardGraphJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"id\":\"DF.SLICE.CONSUMER\","
                + "\"kind\":\"guard_dependency\","
                + "\"transferKind\":\"GUARD\","
                + "\"semanticMode\":\"ASSERTABLE\","
                + "\"relation\":\"control_depends_on\","
                + "\"fromCell\":\"" + BUS_VALUE + "\","
                + "\"toCell\":\"" + SLICE_TARGET + "\","
                + "\"method\":\"" + SLICE_CONSUMER + "\","
                + "\"siteId\":\"" + SLICE_CONSUMER + "#u5\","
                + "\"unitIndex\":5"
                + "}";
    }

    private static String sliceRegionEdgeJson() {
        return "{"
                + "\"schemaVersion\":2,"
                + "\"edgeId\":\"REGION_EDGE.SLICE\","
                + "\"fromRegion\":\"REGION.PRODUCER\","
                + "\"toRegion\":\"REGION.CONSUMER\","
                + "\"fromPort\":\"" + BUS_VALUE + "\","
                + "\"toPort\":\"" + BUS_VALUE + "\","
                + "\"kind\":\"SHARED_STATE\","
                + "\"siteId\":\"" + SLICE_CONSUMER + "#u5\""
                + "}";
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> symbolize(
            Map<String, Object> plan) {
        List<Map<String, Object>> goals =
                (List<Map<String, Object>>) plan.get("closureGoals");
        return (List<Map<String, Object>>) goals.get(0).get("symbolize");
    }

    private static Map<String, Object> regionPlan(
            RuntimeRegionPlanner.Result result, String regionId) {
        for (Map<String, Object> plan : result.regionPlans) {
            if (regionId.equals(plan.get("regionId"))) {
                return plan;
            }
        }
        throw new AssertionError("missing plan for " + regionId);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> goal(
            Map<String, Object> plan, String kind) {
        for (Map<String, Object> goal
                : (List<Map<String, Object>>) plan.get("closureGoals")) {
            if (kind.equals(goal.get("kind"))) {
                return goal;
            }
        }
        throw new AssertionError("missing goal " + kind);
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        return (List<Map<String, Object>>) value;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> map(Object value) {
        return (Map<String, Object>) value;
    }
}
