package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeRegionPlannerTest {
    private static final String HANDLE = "<example.Handler: void handle(java.lang.Object[])>";
    private static final String IDENTIFIER = "<example.Handler: example.Token getIdentifier(java.lang.String)>";
    private static final String PASSWORD = "<example.Handler: char[] getPassword(example.Token)>";
    private static final String RETRIEVE = "<example.Manager: byte[] retrievePassword(example.Token)>";
    private static final String SASL_CLIENT =
            "<example.SaslClient: void doSaslHandshake(java.lang.String)>";
    private static final String SASL_SERVER =
            "<example.SaslServerCallbackHandler: void handle(java.lang.Object[])>";
    private static final String NAME_CALLBACK_DEFAULT =
            "<javax.security.auth.callback.NameCallback: java.lang.String getDefaultName()>";

    @Test
    public void hotPathRegexesArePrecompiledAndPreserveCellParsing()
            throws Exception {
        for (String name : Arrays.asList("PARAMETER_TYPE",
                "PARAMETER_FIELD_PROJECTION", "UNIT_SITE_SUFFIX",
                "UNSAFE_TOKEN_CHARACTERS", "JSON_QUOTED_STRING")) {
            java.lang.reflect.Field field = RuntimeRegionPlanner.class
                    .getDeclaredField(name);
            int modifiers = field.getModifiers();
            assertTrue(java.lang.reflect.Modifier.isStatic(modifiers));
            assertTrue(java.lang.reflect.Modifier.isFinal(modifiers));
            assertEquals(java.util.regex.Pattern.class, field.getType());
        }

        java.lang.reflect.Method declaredJavaType = RuntimeRegionPlanner.class
                .getDeclaredMethod("declaredJavaType", String.class);
        declaredJavaType.setAccessible(true);
        String parameterProjection = HANDLE
                + ".param0:example.Payload#field:entries";
        assertEquals("example.Payload", declaredJavaType.invoke(null,
                parameterProjection));
        assertEquals("java.util.Map", declaredJavaType.invoke(null,
                "<example.State: java.util.Map allKeys>"));

        java.lang.reflect.Method fieldCell = RuntimeRegionPlanner.class
                .getDeclaredMethod("fieldCell", String.class);
        fieldCell.setAccessible(true);
        Object parsed = fieldCell.invoke(null, parameterProjection);
        java.lang.reflect.Field owner = parsed.getClass().getDeclaredField(
                "owner");
        java.lang.reflect.Field name = parsed.getClass().getDeclaredField(
                "name");
        owner.setAccessible(true);
        name.setAccessible(true);
        assertEquals("example.Payload", owner.get(parsed));
        assertEquals("entries", name.get(parsed));
    }

    @Test
    public void activationCarriesStableReceiverAndThreadContextOrdinal()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String root = "<example.WorkerThread: void run()>";
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Files.write(regions, region("REGION.WORKER", root).getBytes(
                    StandardCharsets.UTF_8));
            List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                    rootContextMethod(1, root, 1, "producer-a",
                            "example.ProducerAThread", 21L),
                    rootContextMethod(2, root, 2, "consumer",
                            "example.ConsumerThread", 99L),
                    rootContextMethod(3, root, 3, "producer-b",
                            "example.ProducerBThread", 22L),
                    rootContextMethod(4, root, 4, "consumer",
                            "example.ConsumerThread", 1234L));

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), methods, Collections.emptyList(),
                    Collections.emptyList());

            Map<String, Object> firstConsumer = null;
            Map<String, Object> secondConsumer = null;
            for (Map<String, Object> activation : result.activations) {
                if (Long.valueOf(2L).equals(activation.get("rootCallId"))) {
                    firstConsumer = activation;
                } else if (Long.valueOf(4L).equals(
                        activation.get("rootCallId"))) {
                    secondConsumer = activation;
                }
            }
            assertTrue(firstConsumer != null);
            assertTrue(secondConsumer != null);
            assertEquals("example.ConsumerThread",
                    firstConsumer.get("receiverRuntimeClass"));
            assertEquals("consumer", firstConsumer.get("threadName"));
            assertEquals(1,
                    firstConsumer.get("invocationOrdinalWithinContext"));
            assertEquals(2,
                    secondConsumer.get("invocationOrdinalWithinContext"));
            assertEquals(RuntimeRegionPlanner
                            .ROOT_CONTEXT_SELECTION_AUTHORITY,
                    firstConsumer.get("rootContextSelectionAuthority"));
            assertEquals(Boolean.FALSE,
                    firstConsumer.get("threadIdSelectionUsed"));
            assertFalse("unstable tid must not enter the activation selector",
                    firstConsumer.containsKey("threadId"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void hdfsDataXceiverDynamicNamesUseReceiverOrdinalAndStableRole()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String root = "<org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager: byte[] retrievePassword("
                    + "org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenIdentifier)>";
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Files.write(regions, region("REGION.HDFS.TARGET", root).getBytes(
                    StandardCharsets.UTF_8));
            String firstName = "DataXceiver for client /127.0.0.1:47722 "
                    + "[Replacing block BP-1:blk_1 from dn-1]";
            String secondName = "DataXceiver for client /127.0.0.1:59381 "
                    + "[Replacing block BP-2:blk_9 from dn-2]";
            String manager = "org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager";
            String identifier =
                    "org.apache.hadoop.hdfs.security.token.block."
                            + "BlockTokenIdentifier";
            List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                    rootContextMethod(1, root, 1, firstName, manager, 1307L),
                    rootContextMethod(3, root, 2, secondName, manager, 1441L));
            List<RuntimeRegionPlanner.RuntimeEvent> events = Arrays.asList(
                    methodArgument(2, root, 1, 0, identifier),
                    methodArgument(4, root, 2, 0, identifier));

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), methods, events,
                    Collections.emptyList());

            Map<String, Object> second = result.activations.get(1);
            assertFalse("ephemeral DataXceiver name must not enter replay "
                    + "identity", second.containsKey("threadName"));
            assertEquals("DataXceiver:ReplacingBlock",
                    second.get("rootContextThreadRole"));
            assertEquals(Boolean.TRUE,
                    second.get("rootContextThreadNameOmitted"));
            assertEquals(RuntimeRegionPlanner
                            .HDFS_DATAXCEIVER_CONTEXT_NORMALIZATION_AUTHORITY,
                    second.get("rootContextNormalizationAuthority"));
            assertEquals("dynamic names share one receiver-class context",
                    2, second.get("invocationOrdinalWithinContext"));
            @SuppressWarnings("unchecked")
            Map<String, Object> selector = (Map<String, Object>) second.get(
                    "runtimeRootArgumentSelector");
            assertEquals(2, selector.get("receiverOrdinal"));
            assertEquals(1, selector.get("matchOrdinalWithinReceiver"));

            Map<String, Object> instance = result.instances.get(1);
            assertEquals("instance rows retain the raw observation",
                    secondName, instance.get("threadName"));
            assertEquals(secondName, instance.get("observedThreadName"));
            assertEquals("DataXceiver:ReplacingBlock",
                    instance.get("threadRole"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rootArgumentParameterIndexAfterPrimitiveIsNotDropped()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String root = "<example.Actor: void process(int,example.Command)>";
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Files.write(regions, region("REGION.PARAMETERS", root).getBytes(
                    StandardCharsets.UTF_8));
            RuntimeRegionPlanner.MethodEvent method = methodWithReceiver(
                    1, root, 1, 101);
            RuntimeRegionPlanner.RuntimeEvent command = methodArgument(
                    2, root, 1, 1, "example.KeyUpdateCommand");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(method),
                    Collections.singletonList(command),
                    Collections.emptyList());

            @SuppressWarnings("unchecked")
            Map<String, Object> selector = (Map<String, Object>) result
                    .activations.get(0).get("runtimeRootArgumentSelector");
            assertTrue(selector != null);
            @SuppressWarnings("unchecked")
            List<Map<String, Object>> predicates =
                    (List<Map<String, Object>>) selector.get("predicates");
            assertEquals(1, predicates.size());
            assertEquals(1, predicates.get(0).get("argumentIndex"));
            assertEquals("example.KeyUpdateCommand",
                    predicates.get(0).get("runtimeType"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rootArgumentTypeIndexIsLinearAndPreservesAmbiguity() {
        String root = "<example.Actor: void process(example.Command,"
                + "example.Service)>";
        String other = "<example.OtherActor: void process(example.Command)>";
        List<RuntimeRegionPlanner.RuntimeEvent> events = new ArrayList<>();
        for (int index = 0; index < 30000; index++) {
            events.add(new RuntimeRegionPlanner.RuntimeEvent(index + 1L,
                    "BRANCH", "<example.Noise: void run()>",
                    1000L + index, 0L, 0L, "noise#u1", -1, "", 0,
                    "", true, false));
        }
        events.add(methodArgument(30001, root, 41, 0,
                "example.KeyUpdateCommand"));
        events.add(methodArgument(30002, root, 41, 0,
                "example.KeyUpdateCommand"));
        events.add(methodArgument(30003, root, 41, 1,
                "example.Service"));
        events.add(methodArgument(30004, root, 42, 0,
                "example.OtherCommand"));
        events.add(methodArgument(30005, other, 41, 0,
                "example.UnrelatedCommand"));
        events.add(methodArgument(30006, root, 43, 0,
                "example.FirstCommand"));
        events.add(methodArgument(30007, root, 43, 0,
                "example.SecondCommand"));
        events.add(methodArgument(30008, root, 43, 0,
                "example.FirstCommand"));
        events.add(methodArgument(30009, root, 43, 1,
                "example.Service"));

        RuntimeRegionPlanner.RootArgumentRuntimeTypeIndex index =
                RuntimeRegionPlanner.RootArgumentRuntimeTypeIndex.build(
                        events);
        RuntimeRegionPlanner.MethodEvent target = methodWithReceiver(
                1, root, 41, 101);
        Map<Integer, String> exact = index.typesFor(target);
        assertEquals("example.KeyUpdateCommand", exact.get(0));
        assertEquals("example.Service", exact.get(1));

        Map<Integer, String> ambiguous = index.typesFor(methodWithReceiver(
                2, root, 43, 102));
        assertFalse("a conflicting argument index remains ambiguous even if "
                + "a later row repeats the first type",
                ambiguous.containsKey(0));
        assertEquals("example.Service", ambiguous.get(1));
        assertEquals(events.size(), index.scannedEventCount());
        assertEquals(9, index.indexedArgumentEventCount());
        assertEquals(4, index.indexedCallCount());

        for (int lookup = 0; lookup < 10000; lookup++) {
            assertEquals(exact, index.typesFor(target));
        }
        assertEquals("lookups do not rescan the large runtime event list",
                events.size(), index.scannedEventCount());
    }

    @Test
    public void argumentSelectorOrdinalsAreRelativeToStableRootContext()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String root = "<example.WorkerThread: void run(java.lang.Object)>";
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Files.write(regions, region("REGION.WORKER.ARG", root).getBytes(
                    StandardCharsets.UTF_8));
            List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                    rootContextMethod(1, root, 1, "producer",
                            "example.ProducerThread", 31L),
                    rootContextMethod(3, root, 2, "consumer",
                            "example.ConsumerThread", 32L));
            List<RuntimeRegionPlanner.RuntimeEvent> events = Arrays.asList(
                    methodArgument(2, root, 1, 0, "example.Command"),
                    methodArgument(4, root, 2, 0, "example.Command"));

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), methods, events,
                    Collections.emptyList());
            Map<String, Object> consumer = null;
            for (Map<String, Object> activation : result.activations) {
                if (Long.valueOf(2L).equals(activation.get("rootCallId"))) {
                    consumer = activation;
                }
            }
            assertTrue(consumer != null);
            assertEquals(1, consumer.get(
                    "invocationOrdinalWithinContext"));
            @SuppressWarnings("unchecked")
            Map<String, Object> selector = (Map<String, Object>) consumer.get(
                    "runtimeRootArgumentSelector");
            assertEquals("other receiver/thread contexts must not shift the "
                            + "argument selector",
                    1, selector.get("receiverOrdinal"));
            assertEquals(1, selector.get("matchOrdinalWithinReceiver"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rootArgumentSelectorUsesExactTypesAndReceiverRelativeOrdinal()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String root = "<example.Actor: void process(example.Command,"
                    + "example.Service,int)>";
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Files.write(regions, region("REGION.SELECTOR", root).getBytes(
                    StandardCharsets.UTF_8));

            List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                    methodWithReceiver(1, root, 1, 101),
                    methodWithReceiver(10, root, 2, 201),
                    methodWithReceiver(20, root, 3, 301),
                    methodWithReceiver(30, root, 4, 401));
            List<RuntimeRegionPlanner.RuntimeEvent> events = Arrays.asList(
                    methodArgument(2, root, 1, 0, "example.NullCommand"),
                    methodArgument(3, root, 1, 1, "example.Service"),
                    methodArgument(11, root, 2, 0, "example.KeyUpdateCommand"),
                    methodArgument(12, root, 2, 1, "example.Service"),
                    methodArgument(21, root, 3, 0, "example.KeyUpdateCommand"),
                    methodArgument(22, root, 3, 1, "example.OtherService"),
                    methodArgument(31, root, 4, 0, "example.KeyUpdateCommand"),
                    methodArgument(32, root, 4, 1, "example.Service"));

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), methods, events,
                    Collections.emptyList());

            Map<String, Object> selected = null;
            for (Map<String, Object> activation : result.activations) {
                if (Long.valueOf(4L).equals(activation.get("rootCallId"))) {
                    selected = activation;
                }
            }
            assertTrue(selected != null);
            assertEquals(4, selected.get("invocationOrdinal"));
            @SuppressWarnings("unchecked")
            Map<String, Object> selector = (Map<String, Object>) selected.get(
                    "runtimeRootArgumentSelector");
            assertEquals(RuntimeRegionPlanner.ROOT_ARGUMENT_SELECTOR_SCHEMA,
                    selector.get("schema"));
            assertEquals(RuntimeRegionPlanner.ROOT_ARGUMENT_SELECTOR_AUTHORITY,
                    selector.get("authority"));
            assertEquals(2, selector.get("receiverOrdinal"));
            assertEquals(1, selector.get("matchOrdinalWithinReceiver"));
            @SuppressWarnings("unchecked")
            List<Map<String, Object>> predicates =
                    (List<Map<String, Object>>) selector.get("predicates");
            assertEquals(2, predicates.size());
            assertEquals(0, predicates.get(0).get("argumentIndex"));
            assertEquals("example.KeyUpdateCommand",
                    predicates.get(0).get("runtimeType"));
            assertEquals(1, predicates.get(1).get("argumentIndex"));
            assertEquals("example.Service",
                    predicates.get(1).get("runtimeType"));

            Map<String, Object> selectedInstance = null;
            for (Map<String, Object> instance : result.instances) {
                if (Long.valueOf(4L).equals(instance.get("rootCallId"))) {
                    selectedInstance = instance;
                }
            }
            assertTrue(selectedInstance != null);
            assertEquals(selector,
                    selectedInstance.get("runtimeRootArgumentSelector"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void instantiatesRegionFromConcreteCallTreeAndBuildsActivation() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            String row = "{"
                    + "\"regionId\":\"REGION.0\","
                    + "\"rootMethod\":\"" + HANDLE + "\","
                    + "\"anchorMethod\":\"" + RETRIEVE + "\","
                    + "\"methods\":[\"" + HANDLE + "\",\"" + IDENTIFIER
                    + "\",\"" + PASSWORD + "\",\"" + RETRIEVE + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":\"REGION.0.in.0\","
                    + "\"cell\":\"" + HANDLE + ".param0:callbacks\","
                    + "\"sourceKind\":\"ROOT_ARGUMENT\",\"projection\":\"argument[0]\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.0.out.0\","
                    + "\"cell\":\"failure:key == null\","
                    + "\"kind\":\"FAILURE_PREDICATE\"}],"
                    + "\"branchPolicies\":[{\"siteId\":\"" + RETRIEVE
                    + "#u8\",\"policy\":\"EXPLORE\",\"guard\":\"key == null\","
                    + "\"requiredOutcome\":false,"
                    + "\"role\":\"REACHABILITY\"}],"
                    + "\"models\":[\"symbolic_map\"]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent handle = method(1, HANDLE, 1, 0, 0);
            RuntimeRegionPlanner.MethodEvent identifier = method(3, IDENTIFIER, 2, 1, 2);
            RuntimeRegionPlanner.MethodEvent password = method(5, PASSWORD, 3, 1, 4);
            RuntimeRegionPlanner.MethodEvent retrieve = method(7, RETRIEVE, 4, 3, 6);
            RuntimeRegionPlanner.RuntimeEvent argument = new RuntimeRegionPlanner.RuntimeEvent(
                    2, "METHOD_ARGUMENT", HANDLE, 1, 0, 0,
                    HANDLE + "#entry", 0, "[Ljava.lang.Object;", 99,
                    "", false, false);
            RuntimeRegionPlanner.RuntimeEvent branch = new RuntimeRegionPlanner.RuntimeEvent(
                    8, "BRANCH", RETRIEVE, 4, 0, 0,
                    RETRIEVE + "#u8", -1, "", 0, "", true, true);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(),
                    Arrays.asList(handle, identifier, password, retrieve),
                    Arrays.asList(argument, branch), Collections.emptyList());

            assertEquals(1, result.instances.size());
            assertEquals(1, result.activations.size());
            assertEquals(HANDLE, result.instances.get(0).get("observedRootMethod"));
            assertEquals(true, result.instances.get(0).get("fullyObserved"));
            assertEquals("VALIDATED_PATH",
                    result.instances.get(0).get("validationStatus"));
            assertEquals(true, result.instances.get(0).get("symbolicReady"));
            assertEquals(true, result.activations.get(0).get("replayable"));
            String instances = result.instancesJsonl();
            String activations = result.activationsJsonl();
            assertTrue(instances.contains("" + RETRIEVE + "#u8=true"));
            assertTrue(activations.contains("\"location\":\"ARGUMENT\""));
            assertTrue(activations.contains("\"action\":\"ALLOW_NEGATION\""));
            assertTrue(activations.contains("\"requiredOutcome\":false"));
            assertTrue(activations.contains(
                    "\"matchesRequiredOutcome\":false"));
            assertTrue(activations.contains("\"role\":\"REACHABILITY\""));
            assertTrue(activations.contains("\"requiredModels\":[\"symbolic_map\"]"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void unresolvedStaticFrontierBlocksSymbolicReadiness()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"inputSelectionComplete\":false,"
                    + "\"unresolvedInputs\":[\"opaque local result\"],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, HANDLE, 1, 0, 0)),
                    Collections.emptyList(), Collections.emptyList());

            assertEquals(true, result.activations.get(0).get("replayable"));
            assertEquals(false, result.activations.get(0).get("symbolicReady"));
            assertEquals(false, result.activations.get(0).get(
                    "staticInputSelectionComplete"));
            assertTrue(String.valueOf(result.activations.get(0).get(
                    "staticUnresolvedInputs")).contains("opaque local result"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void exactVmTimeAndOpaqueCallReturnDeferToAuthoritativeGates()
            throws Exception {
        assertDeferredInputReady(
                "<java.lang.System: long currentTimeMillis()>.return",
                "ENVIRONMENT", "ENVIRONMENT_MODEL",
                "EXACT_VM_INTRINSIC_PLACEHOLDER_"
                        + "SCHEDULER_VALIDATION_V1");
        assertDeferredInputReady(
                "<org.apache.hadoop.util.Time: long now()>.return",
                "ENVIRONMENT", "ENVIRONMENT_MODEL",
                "EXACT_VM_INTRINSIC_PLACEHOLDER_"
                        + "SCHEDULER_VALIDATION_V1");
        assertDeferredInputReady(
                HANDLE + "::$z0",
                "OPAQUE_CALL", "CALL_RETURN",
                "AUTHORITATIVE_SCHEDULER_DEFINITION_INDEX_REQUIRED_V1");
    }

    @Test
    public void unmodeledEnvironmentInputRemainsFailClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String cell = "<example.Clock: long nanoTime()>.return";
            String row = "{\"regionId\":\"REGION.ENV\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.ENV.in.0\",\"cell\":\"" + cell
                    + "\",\"sourceKind\":\"ENVIRONMENT\","
                    + "\"projection\":\"value\"}],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, HANDLE, 1, 0, 0)),
                    Collections.emptyList(), Collections.emptyList());
            assertEquals(Boolean.FALSE,
                    result.activations.get(0).get("symbolicReady"));
            @SuppressWarnings("unchecked")
            Map<String, Object> action = ((List<Map<String, Object>>)
                    result.activations.get(0).get("symbolize")).get(0);
            assertEquals("ENVIRONMENT_MODEL", action.get("location"));
            assertFalse(action.containsKey("deferredResolution"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void emptyUnresolvedDependencyProvenanceCannotBeExcluded()
            throws Exception {
        String diagnostic = "<example.Alternative: int value>"
                + " [output slice input has no region port]";
        String raw = "{\"outputPort\":\"REGION.X.out.0\","
                + "\"outputCell\":\"<example.State: int value>\","
                + "\"methods\":[\"<example.Alternative: void run()>\"],"
                + "\"causalEdgeIds\":[\"DF.1\"],"
                + "\"causalEdges\":[{\"edgeId\":\"DF.1\","
                + "\"method\":\"<example.Alternative: void run()>\"}],"
                + "\"unresolvedInputs\":[\"" + diagnostic + "\"],"
                + "\"unresolvedInputDetails\":[{\"dependencyCell\":"
                + "\"<example.Alternative: int value>\","
                + "\"dependencyMethods\":[],"
                + "\"reason\":\"OUTPUT_SLICE_INPUT_HAS_NO_REGION_PORT\","
                + "\"diagnostic\":\"" + diagnostic + "\","
                + "\"provenanceAuthority\":"
                + "\"STATIC_EXACT_DEPENDENCY_METHOD_"
                + "CONSUMER_SET_V1\"}]}";

        Class<?> type = Class.forName(RuntimeRegionPlanner.class.getName()
                + "$StaticOutputSlice");
        java.lang.reflect.Method fromJson = type.getDeclaredMethod(
                "fromJson", String.class);
        fromJson.setAccessible(true);
        Object source = fromJson.invoke(null, raw);
        java.lang.reflect.Constructor<?> constructor =
                type.getDeclaredConstructor();
        constructor.setAccessible(true);
        Object refined = constructor.newInstance();
        java.lang.reflect.Method refine = type.getDeclaredMethod(
                "refineUnresolvedInputs", java.util.Set.class, type);
        refine.setAccessible(true);
        refine.invoke(source, Collections.emptySet(), refined);

        java.lang.reflect.Field unresolved = type.getDeclaredField(
                "unresolvedInputs");
        unresolved.setAccessible(true);
        assertEquals(Collections.singletonList(diagnostic),
                unresolved.get(refined));
        java.lang.reflect.Field provenance = type.getDeclaredField(
                "unresolvedInputProvenanceComplete");
        provenance.setAccessible(true);
        assertEquals(Boolean.FALSE, provenance.get(refined));
        java.lang.reflect.Field complete = type.getDeclaredField(
                "runtimeRefinementComplete");
        complete.setAccessible(true);
        assertEquals(Boolean.FALSE, complete.get(refined));
    }

    private static void assertDeferredInputReady(
            String cell, String sourceKind, String location,
            String authority) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String row = "{\"regionId\":\"REGION.DEFER\","
                    + "\"rootMethod\":\"" + HANDLE
                    + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.DEFER.in.0\",\"cell\":\"" + cell
                    + "\",\"sourceKind\":\"" + sourceKind
                    + "\",\"projection\":\"value\"}],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, HANDLE, 1, 0, 0)),
                    Collections.emptyList(), Collections.emptyList());
            assertEquals(Boolean.TRUE,
                    result.activations.get(0).get("symbolicReady"));
            @SuppressWarnings("unchecked")
            Map<String, Object> action = ((List<Map<String, Object>>)
                    result.activations.get(0).get("symbolize")).get(0);
            assertEquals(location, action.get("location"));
            assertEquals(Boolean.TRUE, action.get("deferredResolution"));
            assertEquals(authority,
                    action.get("deferredResolutionAuthority"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void exactSingletonArrayFieldReadEmitsConsumedSiteAuthority()
            throws Exception {
        RuntimeRegionPlanner.Result result = planArrayFieldRead(false,
                false);
        Map<String, Object> activation = result.activations.get(0);
        @SuppressWarnings("unchecked")
        Map<String, Object> action = ((List<Map<String, Object>>)
                activation.get("symbolize")).get(0);

        assertEquals(Boolean.TRUE, activation.get("symbolicReady"));
        assertEquals(Boolean.TRUE, action.get(
                "consumedFieldBindingComplete"));
        assertEquals("<example.ArrayReader: void run()>#u7",
                action.get("consumedFieldSiteId"));
        assertEquals(7, action.get("consumedFieldUnitIndex"));
        assertEquals("RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_"
                        + "OWNER_WITHIN_REGION_INSTANCE_V1",
                action.get("consumedFieldSiteAuthority"));
        assertEquals("DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1",
                action.get("consumedFieldRootAuthority"));
        assertEquals("example.Value[]", action.get("javaType"));
    }

    @Test
    public void repeatedArrayFieldReadFailsClosedInsteadOfChoosingOccurrence()
            throws Exception {
        RuntimeRegionPlanner.Result result = planArrayFieldRead(true,
                false);
        Map<String, Object> activation = result.activations.get(0);
        @SuppressWarnings("unchecked")
        Map<String, Object> action = ((List<Map<String, Object>>)
                activation.get("symbolize")).get(0);

        assertEquals(Boolean.FALSE, activation.get("symbolicReady"));
        assertEquals(Boolean.FALSE, activation.get("boundaryReady"));
        assertEquals(Boolean.FALSE, action.get(
                "consumedFieldBindingComplete"));
        assertTrue(String.valueOf(action.get("consumedFieldBindingIssue"))
                .contains("REPEATED_OR_AMBIGUOUS_RUNTIME_FIELD_READ:2"));
        assertFalse(action.containsKey("consumedFieldSiteId"));
    }

    @Test
    public void heapArrayReadOnEntryReceiverUsesReceiverRootAuthority()
            throws Exception {
        RuntimeRegionPlanner.Result result = planArrayFieldRead(false,
                true);
        @SuppressWarnings("unchecked")
        Map<String, Object> action = ((List<Map<String, Object>>)
                result.activations.get(0).get("symbolize")).get(0);
        assertEquals("ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_"
                        + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY",
                action.get("consumedFieldRootAuthority"));
    }

    @Test
    public void localArrayLeafRetainsSiteEvidencePendingDefinitionIndex()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String method = "<example.LocalArrayReader: void run()>";
            String local = method + "::$r0";
            String leaf = "<example.ArrayState: example.Value[] values>";
            String row = "{\"regionId\":\"REGION.LOCAL.ARRAY\","
                    + "\"rootMethod\":\"" + method + "\","
                    + "\"anchorMethod\":\"" + method + "\","
                    + "\"methods\":[\"" + method + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.LOCAL.ARRAY.in.0\",\"cell\":\""
                    + local + "\",\"sourceKind\":\"PROTOCOL_INPUT\","
                    + "\"projection\":\"value\","
                    + "\"javaType\":\"example.Value[]\","
                    + "\"leafFieldSignature\":\"" + leaf + "\","
                    + "\"fieldPath\":[\"values\"]}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            methodContext(1, method, 1, "PROCESS", "reader",
                                    55L)),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Collections.singletonList(exactFieldRead(2, method, 1,
                            7, leaf, 91, 701)));
            @SuppressWarnings("unchecked")
            Map<String, Object> action = ((List<Map<String, Object>>)
                    result.activations.get(0).get("symbolize")).get(0);
            assertEquals(method + "#u7",
                    action.get("consumedFieldSiteId"));
            assertEquals("LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                            + "SCHEDULER_DEFINITION_INDEX_V1",
                    action.get("consumedFieldRootAuthority"));
            assertEquals(Boolean.TRUE,
                    action.get("consumedFieldSiteBindingComplete"));
            assertEquals(Boolean.FALSE,
                    action.get("consumedFieldBindingComplete"));
            assertEquals(Boolean.FALSE,
                    result.activations.get(0).get("symbolicReady"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void uniqueContainedProtocolFieldReadMaterializesItsExactSite()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String root = "<example.DataXceiver: void run()>";
            String decoder = "<example.Protocol: void decode()>";
            String field = "<example.Transport: example.Manager manager>";
            String wrong = "<example.Unrelated: example.Manager manager>";
            String row = "{\"regionId\":\"REGION.PROTOCOL\","
                    + "\"rootMethod\":\"" + root + "\","
                    + "\"anchorMethod\":\"" + decoder + "\","
                    + "\"methods\":[\"" + root + "\",\""
                    + decoder + "\"],\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.PROTOCOL.in.0\","
                    + "\"cell\":\"" + field + "#field:map\","
                    + "\"sourceKind\":\"PROTOCOL_INPUT\","
                    + "\"projection\":\"field:map\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent rootCall = methodContext(1,
                    root, 1, "DATANODE", "DataXceiver", 55L);
            RuntimeRegionPlanner.MethodEvent decoderCall =
                    new RuntimeRegionPlanner.MethodEvent(2, "testHandle",
                            "DATANODE", "DataXceiver", 55L, decoder, 73,
                            "example.Protocol", 2, 1, 0, 200L);
            RuntimeRegionPlanner.FieldAccessEvent wrongOwner = exactFieldRead(
                    3, decoder, 2, 6, wrong, 901, 902);
            RuntimeRegionPlanner.FieldAccessEvent exact = exactFieldRead(
                    4, decoder, 2, 7, field, 273814159, 128017166);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Arrays.asList(rootCall, decoderCall),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(wrongOwner, exact));
            @SuppressWarnings("unchecked")
            Map<String, Object> action = ((List<Map<String, Object>>)
                    result.activations.get(0).get("symbolize")).get(0);

            assertEquals(Boolean.TRUE, action.get("observed"));
            assertEquals("HEAP_OBJECT_FIELD", action.get("location"));
            assertEquals("FIELD_ACCESS", action.get("bindingMode"));
            assertEquals("example.Transport", action.get("accessOwnerClass"));
            assertEquals("example.Manager", action.get("accessFieldType"));
            assertEquals("manager", action.get("accessField"));
            assertEquals(field, action.get("accessFieldSignature"));
            assertEquals(decoder, action.get("accessMethod"));
            assertEquals(7, action.get("accessUnitIndex"));
            assertEquals(decoder + "#u7", action.get("accessSiteId"));
            assertEquals(RuntimeRegionPlanner
                            .RUNTIME_UNIQUE_EXACT_FIELD_READ_SITE_AUTHORITY,
                    action.get("accessSiteAuthority"));
            assertEquals(273814159,
                    action.get("fieldReceiverObjectId"));
            assertFalse(result.activationsJsonl().contains(wrong));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void repeatedContainedProtocolFieldReadRemainsDeferred()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String root = "<example.DataXceiver: void run()>";
            String decoder = "<example.Protocol: void decode()>";
            String field = "<example.Transport: example.Manager manager>";
            String row = "{\"regionId\":\"REGION.PROTOCOL\","
                    + "\"rootMethod\":\"" + root + "\","
                    + "\"anchorMethod\":\"" + decoder + "\","
                    + "\"methods\":[\"" + root + "\",\""
                    + decoder + "\"],\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.PROTOCOL.in.0\","
                    + "\"cell\":\"" + field + "#field:map\","
                    + "\"sourceKind\":\"PROTOCOL_INPUT\","
                    + "\"projection\":\"field:map\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));
            RuntimeRegionPlanner.MethodEvent rootCall = methodContext(1,
                    root, 1, "DATANODE", "DataXceiver", 55L);
            RuntimeRegionPlanner.MethodEvent decoderCall =
                    new RuntimeRegionPlanner.MethodEvent(2, "testHandle",
                            "DATANODE", "DataXceiver", 55L, decoder, 73,
                            "example.Protocol", 2, 1, 0, 200L);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Arrays.asList(rootCall, decoderCall),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(exactFieldRead(3, decoder, 2, 7, field,
                            91, 701), exactFieldRead(4, decoder, 2, 8,
                            field, 92, 702)));
            @SuppressWarnings("unchecked")
            Map<String, Object> action = ((List<Map<String, Object>>)
                    result.activations.get(0).get("symbolize")).get(0);

            assertEquals(Boolean.FALSE, action.get("observed"));
            assertEquals("REGION_LIVE_IN", action.get("location"));
            assertEquals(Boolean.TRUE, action.get("deferredResolution"));
            assertEquals("MISSING_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE",
                    action.get("fieldBindingGap"));
            assertFalse(action.containsKey("accessSiteAuthority"));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result planArrayFieldRead(
            boolean repeated, boolean receiverIsRoot) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String method = "<example.ArrayReader: void run()>";
            String field = "<example.ArrayState: example.Value[] allKeys>";
            String row = "{\"regionId\":\"REGION.ARRAY\","
                    + "\"rootMethod\":\"" + method + "\","
                    + "\"anchorMethod\":\"" + method + "\","
                    + "\"methods\":[\"" + method + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.ARRAY.in.0\",\"cell\":\"" + field
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));
            int receiver = receiverIsRoot ? 42 : 91;
            List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                    new ArrayList<>();
            fields.add(exactFieldRead(2, method, 1, 7, field, receiver,
                    701));
            if (repeated) {
                fields.add(exactFieldRead(3, method, 1, 7, field, receiver,
                        701));
            }
            return RuntimeRegionPlanner.plan(regions.toFile(),
                    Collections.singletonList(methodContext(1, method, 1,
                            "PROCESS", "reader", 55L)),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    fields);
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.FieldAccessEvent exactFieldRead(
            long seq, String method, long callId, int unitIndex,
            String field, int receiverObjectId, int valueObjectId) {
        return new RuntimeRegionPlanner.FieldAccessEvent(seq,
                "FIELD_READ", method, callId, unitIndex,
                method + "#u" + unitIndex, field, receiverObjectId,
                valueObjectId, "", "fp", true, 1, "");
    }

    @Test
    public void retainsRepeatedBranchOccurrencesAndSelectsPathWitness()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String site = HANDLE + "#u7";
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[{\"siteId\":\"" + site
                    + "\",\"policy\":\"PATH_ASSUMPTION\","
                    + "\"guard\":\"loop exit\",\"requiredOutcome\":false,"
                    + "\"role\":\"REACHABILITY\"}],\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent root = method(1, HANDLE, 1, 0, 0);
            RuntimeRegionPlanner.RuntimeEvent body =
                    new RuntimeRegionPlanner.RuntimeEvent(2, "BRANCH", HANDLE,
                            1, 0, 0, site, -1, "", 0, "", true, false);
            RuntimeRegionPlanner.RuntimeEvent exit =
                    new RuntimeRegionPlanner.RuntimeEvent(3, "BRANCH", HANDLE,
                            1, 0, 0, site, -1, "", 0, "", true, true);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(root),
                    Arrays.asList(body, exit), Collections.emptyList());

            String activation = result.activationsJsonl();
            assertTrue(activation.contains("\"occurrenceCount\":2"));
            assertTrue(activation.contains("\"selectedOccurrence\":1"));
            assertTrue(activation.contains("\"observedOutcome\":false"));
            assertTrue(activation.contains(
                    "\"matchesRequiredOutcome\":true"));
            assertTrue(activation.contains("\"occurrence\":2"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void containedCallLimitFailsClosedWithExplicitRuntimeGap()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE + "\",\""
                    + IDENTIFIER + "\"],\"symbolicInputs\":[],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            List<RuntimeRegionPlanner.MethodEvent> methods = new ArrayList<>();
            methods.add(method(1, HANDLE, 1, 0, 0));
            // Root plus 10,000 descendants exceeds the exact per-instance
            // call-tree bound by one.
            for (int index = 0; index < 10000; index++) {
                long callId = index + 2L;
                methods.add(method(index + 2L, IDENTIFIER, callId, 1, 0));
            }

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), methods, Collections.emptyList(),
                    Collections.emptyList());

            assertEquals(true, result.summary.get("truncated"));
            assertEquals(1, result.summary.get(
                    "truncatedCallTreeInstanceCount"));
            assertEquals(1L, result.summary.get("skippedContainedCallCount"));
            Map<String, Object> instance = result.instances.get(0);
            assertEquals(true, instance.get("containedCallTreeTruncated"));
            assertEquals(false, instance.get("runtimePathEvidenceComplete"));
            assertEquals("TRUNCATED_RUNTIME_PATH",
                    instance.get("validationStatus"));
            assertTrue(String.valueOf(instance.get("runtimeGaps")).contains(
                    "CONTAINED_CALL_TREE_LIMIT_EXCEEDED"));
            assertEquals(false, result.activations.get(0).get("replayable"));
            assertEquals(false, result.activations.get(0).get("symbolicReady"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void pathSignatureLimitFailsClosedWithExplicitRuntimeGap()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Files.write(regions, region("REGION.0", HANDLE).getBytes(
                    StandardCharsets.UTF_8));
            List<RuntimeRegionPlanner.RuntimeEvent> branches = new ArrayList<>();
            for (int index = 0; index < 513; index++) {
                branches.add(new RuntimeRegionPlanner.RuntimeEvent(index + 2L,
                        "BRANCH", HANDLE, 1, 0, 0,
                        HANDLE + "#u" + index, -1, "", 0, "", true,
                        (index & 1) == 0));
            }

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, HANDLE, 1, 0, 0)), branches,
                    Collections.emptyList());

            assertEquals(true, result.summary.get("truncated"));
            assertEquals(1, result.summary.get(
                    "truncatedPathSignatureInstanceCount"));
            assertEquals(1L, result.summary.get(
                    "skippedPathSignatureEventCount"));
            Map<String, Object> instance = result.instances.get(0);
            assertEquals(513, instance.get("pathSignatureEventCount"));
            assertEquals(512, ((List<?>) instance.get("pathSignature")).size());
            assertEquals(true, instance.get("pathSignatureTruncated"));
            assertEquals(false, instance.get("runtimePathEvidenceComplete"));
            assertTrue(String.valueOf(instance.get("runtimeGaps")).contains(
                    "PATH_SIGNATURE_LIMIT_EXCEEDED"));
            assertEquals(false, result.activations.get(0).get("replayable"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void confirmsSharedStateRegionEdgeWithReceiverIdentityAndOrder()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String updater = "<example.Updater: void run()>";
            String reader = "<example.Reader: void handle()>";
            String field = "<example.State: int currentKey>";
            Files.write(regions, (region("REGION.W", updater)
                    + region("REGION.R", reader)).getBytes(StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.0\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + field + "\","
                    + "\"toPort\":\"" + field + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true,\"siteId\":\"\"}\n";
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1, updater,
                    1, "DATANODE", "KeyUpdater", 11L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(4, reader,
                    4, "DATANODE", "DataXceiver", 12L);
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(2, "FIELD_WRITE",
                            updater, 1, field, 77, 88, "10");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(5, "FIELD_READ",
                            reader, 4, field, 77, 88, "10");
            // The updater is long-lived and can execute again after this
            // consumer read.  Region-level lastSeq order is therefore false,
            // while the concrete write/read pair above is still ordered.
            RuntimeRegionPlanner.FieldAccessEvent trailingUpdaterAccess =
                    new RuntimeRegionPlanner.FieldAccessEvent(6, "FIELD_READ",
                            updater, 1, "<example.State: int noise>",
                            77, 0, "0");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(writeRoot, readRoot), Collections.emptyList(),
                    Arrays.asList(write, read, trailingUpdaterAccess));

            assertEquals(1, result.edgeValidations.size());
            assertEquals("CONFIRMED_READ_FROM",
                    result.edgeValidations.get(0).get("status"));
            assertEquals(1,
                    result.edgeValidations.get(0).get("confirmedReadFromPairCount"));
            assertEquals("READ_FROM",
                    result.edgeValidations.get(0).get("relation"));
            assertEquals("READ_FROM_CANDIDATE",
                    result.edgeValidations.get(0).get("candidateRelation"));
            assertEquals("READ_FROM",
                    result.edgeValidations.get(0).get("validatedRelation"));
            assertEquals(true,
                    result.edgeValidations.get(0).get("requiresObjectIdentity"));
            assertEquals(true,
                    result.edgeValidations.get(0).get("composable"));
            assertEquals(1,
                    result.edgeValidations.get(0).get("orderedPairCount"));
            assertEquals(true, result.edgeValidations.get(0).get(
                    "eligibleForRecursiveDiscovery"));
            assertEquals(1, result.edgeValidations.get(0).get(
                    "validatedBindingCount"));
            assertEquals(1, ((List<?>) result.edgeValidations.get(0).get(
                    "validatedBindings")).size());
            assertTrue(result.edgeValidationsJsonl().contains(
                    "\"fromProcess\":\"DATANODE\""));
            assertTrue(result.edgeValidationsJsonl().contains(
                    "\"fromThreadId\":11"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void confirmsCompletedContainedMapMutationAcrossTruncatedLoopPath()
            throws Exception {
        RuntimeRegionPlanner.Result result = containerMutationReadFromResult(
                true, 128017166);
        Map<String, Object> validation = result.edgeValidations.get(0);
        assertEquals("CONFIRMED_READ_FROM", validation.get("status"));
        assertEquals(1, validation.get("confirmedReadFromPairCount"));
        assertTrue(String.valueOf(validation.get("readFromAuthorities"))
                .contains(RuntimeRegionPlanner
                        .CONTAINER_MUTATION_READ_FROM_AUTHORITY));
        assertTrue(String.valueOf(validation.get("readFromAssumptions"))
                .contains(RuntimeRegionPlanner
                        .TRUNCATED_PATH_READ_FROM_ASSUMPTION));

        @SuppressWarnings("unchecked")
        Map<String, Object> binding = ((List<Map<String, Object>>)
                validation.get("validatedBindings")).get(0);
        assertEquals("FIELD_CONTAINER_MUTATION",
                binding.get("writeEvidenceKind"));
        assertEquals(5197L, binding.get("writerFieldReadSeq"));
        assertEquals(5207L, binding.get("mutatorEnterSeq"));
        assertEquals(5211L, binding.get("mutationCompletionSeq"));
        assertEquals(5211L, binding.get("writeSeq"));
        assertEquals(5207L, binding.get("mutationInvocationId"));
        assertEquals(128017166, binding.get("valueObjectId"));
        assertEquals(128017166, binding.get("readerValueObjectId"));
        assertEquals(Boolean.TRUE,
                binding.get("fieldReceiverIdentityConfirmed"));
        assertEquals(Boolean.TRUE,
                binding.get("containerIdentityConfirmed"));
        assertEquals(RuntimeRegionPlanner
                        .CONTAINER_MUTATOR_CONTRACT_AUTHORITY,
                binding.get("mutationContractAuthority"));
        assertEquals(RuntimeRegionPlanner.TRACE_ORDER_AUTHORITY,
                binding.get("orderAuthority"));
        assertEquals(RuntimeRegionPlanner
                        .CONTAINER_MUTATION_SEMANTIC_ASSUMPTION,
                binding.get("containerMutationSemanticAssumption"));

        Map<String, Object> derived = null;
        for (Map<String, Object> activation : result.activations) {
            if (String.valueOf(activation.get("activationId"))
                    .startsWith("ACT.UPSTREAM.")) {
                derived = activation;
                break;
            }
        }
        assertTrue(derived != null);
        assertEquals(Boolean.FALSE, derived.get("replayable"));
        assertEquals(Boolean.TRUE, derived.get("readFromWitnessOnly"));
        assertEquals("RUNTIME_READ_FROM_WITNESS_ONLY_PATH_TRUNCATED",
                derived.get("replayMode"));
        assertEquals(Boolean.FALSE, derived.get("symbolicReady"));
    }

    @Test
    public void containerMutationReadFromRequiresReturnAndSameContainer()
            throws Exception {
        RuntimeRegionPlanner.Result missingReturn =
                containerMutationReadFromResult(false, 128017166);
        assertEquals(0, missingReturn.edgeValidations.get(0).get(
                "confirmedReadFromPairCount"));
        assertFalse("CONFIRMED_READ_FROM".equals(
                missingReturn.edgeValidations.get(0).get("status")));

        RuntimeRegionPlanner.Result differentContainer =
                containerMutationReadFromResult(true, 128017167);
        assertEquals(0, differentContainer.edgeValidations.get(0).get(
                "confirmedReadFromPairCount"));
        assertFalse("CONFIRMED_READ_FROM".equals(
                differentContainer.edgeValidations.get(0).get("status")));
    }

    @Test
    public void keepsRawEndpointForReadFromButSelectsCanonicalOutput()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String updater = "<example.Updater: void publish()>";
            String reader = "<example.Reader: void handle()>";
            String rawField = "<example.Wire: int allKeys>";
            String canonicalField = "<example.Keys: int[] allKeys>";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + updater + "\","
                    + "\"anchorMethod\":\"" + updater + "\","
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"symbolicInputs\":[],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + canonicalField + "\","
                    + "\"kind\":\"HEAP_STATE\"},{"
                    + "\"portId\":\"REGION.W.out.raw\","
                    + "\"cell\":\"" + rawField + "\","
                    + "\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + canonicalField + "\","
                    + "\"inputPorts\":[],\"inputBindings\":[],"
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"sites\":[],\"causalEdgeIds\":[],"
                    + "\"causalEdges\":[],"
                    + "\"captureBindingsRequired\":false,"
                    + "\"captureBindingsComplete\":true,"
                    + "\"complete\":true,"
                    + "\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"},{"
                    + "\"outputPort\":\"REGION.W.out.raw\","
                    + "\"outputCell\":\"" + rawField + "\","
                    + "\"inputPorts\":[],\"inputBindings\":[],"
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"sites\":[],\"causalEdgeIds\":[],"
                    + "\"causalEdges\":[],"
                    + "\"captureBindingsRequired\":false,"
                    + "\"captureBindingsComplete\":true,"
                    + "\"complete\":true,"
                    + "\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}"
                    + System.lineSeparator();
            Files.write(regions, (writerRegion
                    + region("REGION.R", reader)).getBytes(
                    StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.CANONICAL\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + rawField + "\","
                    + "\"fromOutputPort\":\"REGION.W.out.0\","
                    + "\"fromOutputCell\":\"" + canonicalField + "\","
                    + "\"aliasProofEdgeIds\":[\"DF.1\",\"DF.2\"],"
                    + "\"aliasProofAuthority\":"
                    + "\"STATIC_EXACT_PROJECTED_RETURN_VALUE_FLOW_"
                    + "AND_DECLARED_RETURN_FIELD\","
                    + "\"aliasProofComplete\":true,"
                    + "\"toPort\":\"" + rawField + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}"
                    + System.lineSeparator();
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(4,
                    reader, 22, "PROCESS", "reader", 202L);
            // Runtime correlation must use the raw edge endpoint.  There are
            // deliberately no field events for the canonical summary cell.
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_WRITE", updater, 11, rawField,
                            77, 88, "digest");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(5,
                            "FIELD_READ", reader, 22, rawField,
                            77, 88, "digest");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(write, read));

            assertEquals("CONFIRMED_READ_FROM",
                    result.edgeValidations.get(0).get("status"));
            assertEquals(rawField,
                    result.edgeValidations.get(0).get("fromPort"));
            assertEquals("REGION.W.out.0",
                    result.edgeValidations.get(0).get("fromOutputPort"));
            assertEquals(canonicalField,
                    result.edgeValidations.get(0).get("fromOutputCell"));
            assertEquals(Arrays.asList("DF.1", "DF.2"),
                    result.edgeValidations.get(0).get("aliasProofEdgeIds"));
            assertEquals(Boolean.TRUE,
                    result.edgeValidations.get(0).get("aliasProofComplete"));
            assertEquals(3, result.activations.size());
            Map<String, Object> upstream = result.activations.get(2);
            @SuppressWarnings("unchecked")
            Map<String, Object> requested = (Map<String, Object>) upstream
                    .get("requestedOutput");
            assertEquals("REGION.W.out.0", requested.get("portId"));
            assertEquals(canonicalField, requested.get("cell"));
            @SuppressWarnings("unchecked")
            Map<String, Object> binding = ((List<Map<String, Object>>)
                    upstream.get("edgeBindings")).get(0);
            assertEquals(rawField, binding.get("rawFromPort"));
            assertEquals(canonicalField, binding.get("fromOutputCell"));
            assertEquals(Boolean.TRUE,
                    binding.get("canonicalOutputAliasUsed"));
            assertEquals(Arrays.asList("DF.1", "DF.2"),
                    binding.get("aliasProofEdgeIds"));

            // Once any canonical schema field is present, a partial record
            // must not fall back to the otherwise valid raw output endpoint.
            String partial = edge.replace(
                    "\"aliasProofEdgeIds\":[\"DF.1\",\"DF.2\"],", "");
            Files.write(edges, partial.getBytes(StandardCharsets.UTF_8));
            RuntimeRegionPlanner.Result rejected = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(write, read));
            assertEquals("CONFIRMED_READ_FROM",
                    rejected.edgeValidations.get(0).get("status"));
            assertEquals(2, rejected.activations.size());
            assertEquals(0, rejected.summary.get("upstreamActivationCount"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void refinesUniqueMethodReturnCaptureToExactRuntimeOccurrence()
            throws Exception {
        String method =
                "<example.Producer: int compute(java.lang.Boolean)>";
        String publisher = "<example.RpcBus: void publish(int)>";
        String returnCell = method + "::$i0";
        String returnExpression = "$i0";
        RuntimeRegionPlanner.Result result =
                methodReturnCaptureRefinementResult(1);

        assertEquals("CONFIRMED_READ_FROM",
                result.edgeValidations.get(0).get("status"));
        Map<String, Object> upstream = requestedOutputActivation(result);
        assertEquals(Boolean.TRUE,
                upstream.get("requestedOutputCaptureRequired"));
        assertEquals(Boolean.TRUE,
                upstream.get("requestedOutputCaptureComplete"));
        assertEquals(String.valueOf(upstream.get("requestedOutputSlice")),
                Boolean.TRUE,
                upstream.get("requestedOutputSliceRefinementComplete"));
        assertEquals(Boolean.TRUE,
                upstream.get("requestedOutputSliceComplete"));
        assertEquals(Boolean.TRUE, upstream.get("symbolicReady"));
        @SuppressWarnings("unchecked")
        Map<String, Object> refinedSlice = (Map<String, Object>) upstream.get(
                "requestedOutputSlice");
        assertFalse(refinedSlice.containsKey(
                "runtimeObservedMethodsOutsideStaticSlice"));
        assertFalse(refinedSlice.containsKey(
                "runtimeObservedDownstreamMethodsExcluded"));
        assertFalse(((List<?>) refinedSlice.get("methods"))
                .contains(publisher));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> captures =
                (List<Map<String, Object>>) upstream.get(
                        "requestedOutputCapture");
        assertEquals(1, captures.size());
        Map<String, Object> capture = captures.get(0);
        assertEquals("METHOD_RETURN_VALUE", capture.get("captureKind"));
        assertEquals(method, capture.get("method"));
        assertEquals(method + "#u8", capture.get("siteId"));
        assertEquals(8, capture.get("unitIndex"));
        assertEquals(1, capture.get("occurrence"));
        assertEquals("RUNTIME_EXACT_METHOD_RETURN_OCCURRENCE",
                capture.get("occurrenceAuthority"));
        assertEquals(12L, capture.get("runtimeCallId"));
        assertEquals(4L, capture.get("runtimeEventSeq"));
        assertEquals(returnExpression, capture.get("returnExpression"));
        assertEquals(returnCell, capture.get("returnCell"));

        @SuppressWarnings("unchecked")
        Map<String, Object> slice = (Map<String, Object>) upstream.get(
                "requestedOutputSlice");
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> retained =
                (List<Map<String, Object>>) slice.get("captureBindings");
        assertEquals(1, retained.size());
        assertEquals(returnExpression,
                retained.get(0).get("returnExpression"));
        assertEquals(returnCell, retained.get(0).get("returnCell"));
    }

    @Test
    public void multipleNormalExitsForMethodReturnCaptureFailClosed()
            throws Exception {
        String method =
                "<example.Producer: int compute(java.lang.Boolean)>";
        RuntimeRegionPlanner.Result result =
                methodReturnCaptureRefinementResult(2);

        assertEquals("CONFIRMED_READ_FROM",
                result.edgeValidations.get(0).get("status"));
        Map<String, Object> upstream = requestedOutputActivation(result);
        assertEquals(Boolean.TRUE,
                upstream.get("requestedOutputCaptureRequired"));
        assertEquals(Boolean.FALSE,
                upstream.get("requestedOutputCaptureComplete"));
        assertEquals(Boolean.FALSE,
                upstream.get("requestedOutputSliceRefinementComplete"));
        assertEquals(Boolean.FALSE,
                upstream.get("requestedOutputSliceComplete"));
        assertEquals(Boolean.FALSE, upstream.get("boundaryReady"));
        assertEquals(Boolean.FALSE, upstream.get("symbolicReady"));
        assertTrue(((List<?>) upstream.get("requestedOutputCapture"))
                .isEmpty());

        @SuppressWarnings("unchecked")
        Map<String, Object> slice = (Map<String, Object>) upstream.get(
                "requestedOutputSlice");
        assertTrue(((List<?>) slice.get("captureBindings")).isEmpty());
        String issues = String.valueOf(slice.get("captureBindingIssues"));
        assertTrue(issues, issues.contains(
                "RUNTIME_METHOD_RETURN_OCCURRENCE_AMBIGUOUS:"
                        + method + ":2"));
        assertTrue(issues, issues.contains(
                "NO_RUNTIME_EXACT_METHOD_RETURN_MATCH"));
    }

    @Test
    public void derivesOutputClosureActivationFromConfirmedReadFrom()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String updater = "<example.Updater: void run()>";
            String reader = "<example.Reader: void handle()>";
            String absentAnchor = "<example.Updater: void fatalAnchor()>";
            String field = "<example.State: java.util.Map entries>";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + updater + "\","
                    + "\"anchorMethod\":\"" + absentAnchor + "\","
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.W.in.0\","
                    + "\"cell\":\"" + field + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:entries\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + field + "\","
                    + "\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + field + "\","
                    + "\"inputPorts\":[\"REGION.W.in.0\"],"
                    + "\"inputBindings\":[{"
                    + "\"dependencyCell\":\"<example.Request: int key>\","
                    + "\"inputPort\":\"REGION.W.in.0\","
                    + "\"bindingAuthority\":"
                    + "\"UNIQUE_ROOT_ARGUMENT_CARRIER\","
                    + "\"requestedStateTransformerSinkSites\":[\""
                    + updater + "#u15\"],"
                    + "\"requestedStateTransformerGuardSites\":[\""
                    + updater + "#u14\"],"
                    + "\"requestedStateTransformerSinkClosureComplete\":true,"
                    + "\"requestedStateTransformerSinkExclusive\":true,"
                    + "\"requestedStateTransformerUnclassifiedEdgeIds\":[],"
                    + "\"requestedStateTransformerSinkAuthority\":"
                    + "\"STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_REQUESTED_STATE_TRANSFORMERS\"}],"
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"sites\":[],\"causalEdgeIds\":[\"DF.1\","
                    + "\"DF.WRITE\"],"
                    + "\"causalEdges\":[{"
                    + "\"edgeId\":\"DF.1\","
                    + "\"method\":\"" + updater + "\","
                    + "\"siteId\":\"" + updater + "#u6\","
                    + "\"transferKind\":\"GUARD\","
                    + "\"kind\":\"heap_mutation_path_guard\","
                    + "\"guardSiteId\":\"" + updater + "#u6\","
                    + "\"guardedMutationSiteId\":\"" + updater + "#u15\","
                    + "\"requiredOutcome\":false,"
                    + "\"guardedMutationCount\":1,"
                    + "\"guardedMutationsAuthority\":\"STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE\","
                    + "\"guardedMutations\":[{"
                    + "\"guardSiteId\":\"" + updater + "#u6\","
                    + "\"guardedMutationSiteId\":\"" + updater + "#u15\","
                    + "\"method\":\"" + updater + "\","
                    + "\"unitIndex\":15,"
                    + "\"requiredOutcome\":false}]},{"
                    + "\"edgeId\":\"DF.WRITE\","
                    + "\"method\":\"" + updater + "\","
                    + "\"siteId\":\"" + updater + "#u15\","
                    + "\"fromCell\":\"" + updater + "::key\","
                    + "\"toCell\":\"" + field + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\"}],"
                    + "\"requestedStateTransformerContractVersion\":1,"
                    + "\"requestedStateTransformerContractApplicable\":true,"
                    + "\"requestedStateTransformerContractOutputPort\":"
                    + "\"REGION.W.out.0\","
                    + "\"requestedStateTransformerContractOutputCell\":"
                    + "\"" + field + "\","
                    + "\"requestedStateTransformerObligations\":[{"
                    + "\"siteId\":\"" + updater + "#u15\","
                    + "\"method\":\"" + updater + "\","
                    + "\"targetCell\":\"" + field + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\","
                    + "\"causalEdgeIds\":[\"DF.WRITE\"],"
                    + "\"authority\":\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL\"}],"
                    + "\"requestedStateTransformerObligationCount\":1,"
                    + "\"requestedStateTransformerContractIssues\":[],"
                    + "\"requestedStateTransformerContractComplete\":true,"
                    + "\"requestedStateTransformerContractAuthority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1\","
                    + "\"heapInitializers\":[{"
                    + "\"initializerId\":\"STATIC_INIT.REGION.W.0\","
                    + "\"kind\":\"FRESH_DEFAULT_CONSTRUCTED_OBJECT\","
                    + "\"allocatedType\":\"java.util.HashMap\","
                    + "\"constructorArgumentCount\":0,"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + field + "\","
                    + "\"proofEdgeIds\":[\"DF.1\"],"
                    + "\"proofComplete\":true}],"
                    + "\"captureBindingsRequired\":true,"
                    + "\"captureBindingsComplete\":true,"
                    + "\"captureBindings\":[{"
                    + "\"captureKind\":\"FIELD_ASSIGNMENT_RHS\","
                    + "\"captureBindingId\":\"REGION.W.out.0.capture.0\","
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + field + "\","
                    + "\"method\":\"" + updater + "\","
                    + "\"siteId\":\"" + updater + "#u15\","
                    + "\"unitIndex\":15,"
                    + "\"unit\":\"r0." + field + " = key\","
                    + "\"fieldSignature\":\"" + field + "\","
                    + "\"fieldOwnerExpression\":\"r0\","
                    + "\"fieldOwnerCell\":\"" + updater + "::r0\","
                    + "\"fieldOwnerDeclaredType\":\"example.State\","
                    + "\"fieldOwnerBindingKind\":\"INSTANCE_FIELD_LHS_BASE\","
                    + "\"fieldOwnerBindingAuthority\":\"STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_LHS\","
                    + "\"rhsExpression\":\"key\","
                    + "\"rhsCell\":\"" + updater + "::key\","
                    + "\"rhsCausalEdgeId\":\"DF.WRITE\","
                    + "\"rhsRelation\":\"value_flow\","
                    + "\"rhsRelationComplete\":true,"
                    + "\"rhsRelationAuthority\":\"STATIC_EXACT_HEAP_WRITE_VALUE_FLOW\","
                    + "\"causalEdgeId\":\"DF.WRITE\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"bindingKind\":\"field_write\","
                    + "\"bindingAuthority\":\"STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS\","
                    + "\"occurrence\":0}],"
                    + "\"complete\":true,"
                    + "\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}"
                    + System.lineSeparator();
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.R.in.0\","
                    + "\"cell\":\"" + field + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:entries\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}"
                    + System.lineSeparator();
            Files.write(regions, (writerRegion + readerRegion)
                    .getBytes(StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.PRODUCER\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + field + "\","
                    + "\"toPort\":\"" + field + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}"
                    + System.lineSeparator();
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(4,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(2, "FIELD_WRITE",
                            updater, 11, field, 77, 88, "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(5, "FIELD_READ",
                            reader, 22, field, 77, 88, "");
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(write, read));

            assertEquals(3, result.activations.size());
            Map<String, Object> upstream = result.activations.get(2);
            Map<String, Object> captureGoal = (Map<String, Object>)
                    upstream.get("captureGoal");
            assertEquals("OUTPUT_CLOSURE", captureGoal.get("kind"));
            assertEquals("FIELD_RECEIVER_IDENTITY_AND_WRITE_BEFORE_READ",
                    upstream.get("upstreamSelectionAuthority"));
            assertEquals(false, upstream.get("anchorRequired"));
            assertEquals(true, upstream.get("replayable"));
            assertEquals(true, upstream.get("symbolicReady"));
            assertEquals(true, upstream.get("requestedOutputSliceComplete"));
            assertEquals("REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE",
                    upstream.get("requestedOutputSlicePolicy"));
            assertEquals(11L, upstream.get("rootCallId"));
            assertEquals(1, upstream.get("edgeBindingCount"));
            assertEquals(1, ((java.util.List<?>) upstream.get("outputs")).size());
            assertEquals(1, ((java.util.List<?>) upstream.get(
                    "heapStateBindings")).size());
            assertEquals(1, ((java.util.List<?>) upstream.get(
                    "symbolize")).size());
            assertEquals(true,
                    upstream.get("requestedOutputCaptureComplete"));
            @SuppressWarnings("unchecked")
            List<Map<String, Object>> outputCaptures =
                    (List<Map<String, Object>>) upstream.get(
                            "requestedOutputCapture");
            assertEquals(1, outputCaptures.size());
            assertEquals(1, outputCaptures.get(0).get("occurrence"));
            assertEquals("FIELD_ASSIGNMENT_RHS",
                    outputCaptures.get(0).get("captureKind"));
            assertEquals(updater + "#u15",
                    outputCaptures.get(0).get("siteId"));
            assertEquals(field,
                    outputCaptures.get(0).get("fieldSignature"));
            assertEquals(77,
                    outputCaptures.get(0).get(
                            "runtimeFieldOwnerObjectId"));
            assertEquals("RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_"
                            + "SITE_LAST_WRITE_OCCURRENCE",
                    outputCaptures.get(0).get("occurrenceAuthority"));
            assertEquals(Boolean.TRUE,
                    outputCaptures.get(0).get("rhsRelationComplete"));
            assertEquals(Collections.singletonList(updater), upstream.get(
                    "requestedOutputMethods"));
            @SuppressWarnings("unchecked")
            Map<String, Object> retainedSlice = (Map<String, Object>) upstream
                    .get("requestedOutputSlice");
            assertTrue(String.valueOf(retainedSlice.get("inputBindings"))
                    .contains("UNIQUE_ROOT_ARGUMENT_CARRIER"));
            assertTrue(String.valueOf(retainedSlice.get("heapInitializers"))
                    .contains("FRESH_DEFAULT_CONSTRUCTED_OBJECT"));
            assertEquals(2, retainedSlice.get("causalEdgeCount"));
            assertEquals(1, retainedSlice.get(
                    "requestedStateTransformerContractVersion"));
            assertEquals(true, retainedSlice.get(
                    "requestedStateTransformerContractComplete"));
            assertEquals(1, retainedSlice.get(
                    "requestedStateTransformerObligationCount"));
            assertTrue(String.valueOf(retainedSlice.get(
                    "requestedStateTransformerObligations")).contains(
                    updater + "#u15"));
            assertTrue(String.valueOf(retainedSlice.get("inputBindings"))
                    .contains("requestedStateTransformerSinkSites=["
                            + updater + "#u15]"));
            assertTrue(String.valueOf(retainedSlice.get("inputBindings"))
                    .contains("requestedStateTransformerGuardSites=["
                            + updater + "#u14]"));
            assertTrue(String.valueOf(retainedSlice.get("causalEdges"))
                    .contains("STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE"));
            assertTrue(String.valueOf(retainedSlice.get("causalEdges"))
                    .contains("guardedMutationSiteId=" + updater + "#u15"));
            assertTrue(result.activationsJsonl().contains(
                    "\"fromOutputPort\":\"REGION.W.out.0\""));
            assertTrue(result.activationsJsonl().contains(
                    "\"toInputPort\":\"REGION.R.in.0\""));
            assertTrue(result.activationsJsonl().contains(
                    "\"writerEventSeq\":2"));
            assertEquals(1, result.summary.get("upstreamActivationCount"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void refinesOutputClosureToObservedRuntimeAlternative()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String constructor = "<example.State: void <init>()>";
            String updater = "<example.State: void merge(example.Payload)>";
            String reader = "<example.Reader: void consume()>";
            String state = "<example.State: java.util.Map allKeys>";
            String payload =
                    "<example.Payload: java.lang.Object allKeys>";
            String alternative =
                    "<example.ConstructorSeed: java.lang.Object allKeys>";
            String unresolvedAlternative = alternative
                    + " [output slice input has no region port]";
            String updaterSite = updater + "#u3";
            String runtimeBranch = updater + "#u4";
            String unobservedBranch = updater + "#u15";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + constructor + "\","
                    + "\"anchorMethod\":\"" + updater + "\","
                    + "\"methods\":[\"" + constructor + "\",\""
                    + updater + "\"],\"symbolicInputs\":["
                    + "{\"portId\":\"REGION.W.in.0\",\"cell\":\""
                    + state + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"},"
                    + "{\"portId\":\"REGION.W.in.1\",\"cell\":\""
                    + payload + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"},"
                    + "{\"portId\":\"REGION.W.in.2\",\"cell\":\""
                    + alternative
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"inputPorts\":[\"REGION.W.in.0\","
                    + "\"REGION.W.in.1\",\"REGION.W.in.2\"],"
                    + "\"inputBindings\":["
                    + sliceBinding(state, "REGION.W.in.0", updater) + ","
                    + sliceBinding(payload, "REGION.W.in.1", updater) + ","
                    + sliceBinding(alternative, "REGION.W.in.2",
                    constructor) + "],"
                    + "\"methods\":[\"" + constructor + "\",\""
                    + updater + "\"],\"sites\":[\"" + constructor
                    + "#u1\",\"" + updaterSite + "\",\""
                    + unobservedBranch + "\"],"
                    + "\"causalEdgeIds\":[\"DF.C\",\"DF.U\"],"
                    + "\"causalEdges\":["
                    + causalReference("DF.C", constructor,
                    constructor + "#u1") + ","
                    + causalReference("DF.U", updater, updaterSite) + "],"
                    + "\"structuralComplete\":true,"
                    // Broad-region truncation is diagnostic once the output
                    // slice was independently rebuilt within its own budget.
                    + "\"regionTruncated\":true,"
                    + "\"unresolvedInputs\":[\""
                    + unresolvedAlternative + "\"],"
                    + "\"unresolvedInputDetails\":[{"
                    + "\"dependencyCell\":\"" + alternative + "\","
                    + "\"dependencyMethods\":[\"" + constructor + "\"],"
                    + "\"reason\":\"OUTPUT_SLICE_INPUT_HAS_NO_REGION_PORT\","
                    + "\"diagnostic\":\"" + unresolvedAlternative + "\","
                    + "\"provenanceAuthority\":"
                    + "\"STATIC_EXACT_DEPENDENCY_METHOD_"
                    + "CONSUMER_SET_V1\"}],"
                    + "\"requestedStateTransformerContractVersion\":1,"
                    + "\"requestedStateTransformerContractApplicable\":true,"
                    + "\"requestedStateTransformerContractOutputPort\":"
                    + "\"REGION.W.out.0\","
                    + "\"requestedStateTransformerContractOutputCell\":"
                    + "\"" + state + "\","
                    + "\"requestedStateTransformerObligations\":[{"
                    + "\"siteId\":\"" + constructor + "#u1\","
                    + "\"method\":\"" + constructor + "\","
                    + "\"targetCell\":\"" + state + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\","
                    + "\"causalEdgeIds\":[\"DF.C\"],"
                    + "\"authority\":\"STATIC_EXACT_REQUESTED_"
                    + "OUTPUT_TARGET_CELL\"},{"
                    + "\"siteId\":\"" + updaterSite + "\","
                    + "\"method\":\"" + updater + "\","
                    + "\"targetCell\":\"" + state + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\","
                    + "\"causalEdgeIds\":[\"DF.U\"],"
                    + "\"authority\":\"STATIC_EXACT_REQUESTED_"
                    + "OUTPUT_TARGET_CELL\"}],"
                    + "\"requestedStateTransformerObligationCount\":2,"
                    + "\"requestedStateTransformerContractIssues\":[],"
                    + "\"requestedStateTransformerContractComplete\":true,"
                    + "\"requestedStateTransformerContractAuthority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1\","
                    + "\"captureBindingsRequired\":true,"
                    + "\"captureBindingsComplete\":false,"
                    + "\"captureBindings\":[],"
                    + "\"captureBindingIssues\":["
                    + "\"REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_"
                    + "ASSIGNMENT_RHS:" + constructor + "#u1\","
                    + "\"REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_"
                    + "ASSIGNMENT_RHS:" + updaterSite + "\"],"
                    + "\"heapInitializers\":[{"
                    + "\"initializerId\":\"STATIC_INIT.C\","
                    + "\"kind\":\"FRESH_DEFAULT_CONSTRUCTED_OBJECT\","
                    + "\"allocatedType\":\"java.util.HashMap\","
                    + "\"allocationMethod\":\"" + constructor + "\","
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"proofComplete\":true}],\"complete\":false,"
                    + "\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[{\"siteId\":\""
                    + runtimeBranch + "\",\"policy\":\"PIN\","
                    + "\"guard\":\"runtime\",\"role\":"
                    + "\"OUTPUT_RELATION\"},{\"siteId\":\""
                    + unobservedBranch + "\",\"policy\":\"PIN\","
                    + "\"guard\":\"alternative\",\"role\":"
                    + "\"OUTPUT_RELATION\"}],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + state
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.RUNTIME.PATH\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent updateRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent payloadRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_READ", updater, 11, payload, 99, 66, "");
            RuntimeRegionPlanner.FieldAccessEvent stateRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(3,
                            "FIELD_READ", updater, 11, state, 42, 88, "");
            RuntimeRegionPlanner.RuntimeEvent mutation =
                    new RuntimeRegionPlanner.RuntimeEvent(4,
                            "CALL_SITE_ENTER", updater, 11, 40, 0,
                            updaterSite,
                            "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                            -1, "java.util.Map", 88, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent mutationReturn =
                    new RuntimeRegionPlanner.RuntimeEvent(5,
                            "CALL_SITE_RETURN", updater, 11, 40, 0,
                            updaterSite, -1, "", 0, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent branch =
                    new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH",
                            updater, 11, 0, 0, runtimeBranch, -1, "", 0,
                            "", true, true);
            RuntimeRegionPlanner.FieldAccessEvent downstreamRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 42, 88, "");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(updateRoot, readRoot),
                    Arrays.asList(mutation, mutationReturn, branch),
                    Arrays.asList(payloadRead, stateRead, downstreamRead));

            assertEquals(3, result.activations.size());
            @SuppressWarnings("unchecked")
            Map<String, Object> output = result.activations.get(2);
            assertEquals(true, output.get("requestedOutputSliceComplete"));
            assertEquals(true, output.get(
                    "requestedOutputSliceRefinementComplete"));
            assertEquals(false, output.get(
                    "requestedOutputCaptureRequired"));
            assertEquals(true, output.get(
                    "requestedOutputCaptureComplete"));
            assertEquals(Collections.singletonList(updater), output.get(
                    "requestedOutputMethods"));
            assertEquals(2, ((java.util.List<?>) output.get("symbolize"))
                    .size());
            assertEquals(1, ((java.util.List<?>) output.get(
                    "heapStateBindings")).size());
            @SuppressWarnings("unchecked")
            Map<String, Object> slice = (Map<String, Object>) output.get(
                    "requestedOutputSlice");
            assertEquals(Arrays.asList("REGION.W.in.0", "REGION.W.in.1"),
                    slice.get("inputPorts"));
            assertTrue(String.valueOf(slice.get("sites")).contains(
                    runtimeBranch));
            assertFalse(String.valueOf(slice.get("sites")).contains(
                    constructor + "#u1"));
            assertFalse(String.valueOf(slice.get("sites")).contains(
                    unobservedBranch));
            assertTrue(String.valueOf(slice.get(
                    "excludedPathAlternativeSites")).contains(
                    unobservedBranch));
            assertEquals(Collections.singletonList("DF.U"),
                    slice.get("causalEdgeIds"));
            assertTrue(((java.util.List<?>) slice.get("heapInitializers"))
                    .isEmpty());
            assertEquals(Boolean.TRUE, slice.get(
                    "captureDischargedByHeapEffectTransformer"));
            assertEquals("REGION.W.in.0", slice.get(
                    "captureDischargeInputPort"));
            assertEquals("HEAP_EFFECT_STATE_TRANSFORMER", slice.get(
                    "captureDischargeAuthority"));
            assertEquals(Boolean.TRUE, slice.get(
                    "requestedStateTransformerContractComplete"));
            assertEquals(1, slice.get(
                    "requestedStateTransformerObligationCount"));
            assertTrue(((java.util.List<?>) slice.get("captureBindings"))
                    .isEmpty());
            assertTrue(String.valueOf(slice.get(
                    "excludedAlternativeInputPorts")).contains(
                    "REGION.W.in.2"));
            assertTrue(((List<?>) slice.get("unresolvedInputs")).isEmpty());
            assertTrue(String.valueOf(slice.get(
                    "excludedAlternativeUnresolvedInputs")).contains(
                    unresolvedAlternative));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mutationCaptureDischargeRejectsRetainedUnresolvedInput()
            throws Exception {
        RuntimeRegionPlanner.Result result = mutationDischargeGateResult(
                "OBSERVED", "field_mutation", true);
        Map<String, Object> slice = requestedOutputSlice(result);
        assertEquals(Boolean.FALSE, slice.get(
                "captureDischargedByHeapEffectTransformer"));
        assertEquals(Boolean.FALSE, slice.get("complete"));
        assertFalse(((List<?>) slice.get("unresolvedInputs")).isEmpty());
    }

    @Test
    public void mutationCaptureDischargeRejectsNonMutationObligation()
            throws Exception {
        RuntimeRegionPlanner.Result result = mutationDischargeGateResult(
                "ALTERNATIVE", "field_write", true);
        Map<String, Object> slice = requestedOutputSlice(result);
        assertEquals(Boolean.FALSE, slice.get(
                "captureDischargedByHeapEffectTransformer"));
        assertEquals(Boolean.FALSE, slice.get("complete"));
        assertEquals(Boolean.TRUE, slice.get(
                "requestedStateTransformerContractComplete"));
    }

    @Test
    public void mutationCaptureDischargeRejectsTransformerContractGap()
            throws Exception {
        RuntimeRegionPlanner.Result result = mutationDischargeGateResult(
                "ALTERNATIVE", "field_mutation", false);
        Map<String, Object> slice = requestedOutputSlice(result);
        assertEquals(Boolean.FALSE, slice.get(
                "captureDischargedByHeapEffectTransformer"));
        assertEquals(Boolean.FALSE, slice.get("complete"));
        assertEquals(Boolean.FALSE, slice.get(
                "requestedStateTransformerContractComplete"));
    }

    @Test
    public void runtimeCallTreeAdmitsObservedHelperMissingFromBaseRegion()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String updater = "<example.KeyState: void addKeys()>";
            String helper = "<example.KeyState: void removeExpiredKeys()>";
            String reader = "<example.Reader: void consume()>";
            String state = "<example.KeyState: java.util.Map allKeys>";
            String helperSite = helper + "#u6";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + updater + "\","
                    + "\"anchorMethod\":\"" + updater + "\","
                    // Deliberately reproduces an incomplete static base
                    // method catalog.  The output slice already knows the
                    // helper and runtime observes its exact child call.
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"symbolicInputs\":[],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"inputPorts\":[],\"inputBindings\":[],"
                    + "\"methods\":[\"" + updater + "\",\""
                    + helper + "\"],"
                    + "\"sites\":[\"" + helperSite + "\"],"
                    + "\"causalEdgeIds\":[\"DF.HELPER\"],"
                    + "\"causalEdges\":["
                    + causalReference("DF.HELPER", helper, helperSite)
                    + "],"
                    + "\"complete\":true,"
                    + "\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[{\"siteId\":\""
                    + helperSite + "\",\"policy\":\"EXPLORE\","
                    + "\"guard\":\"hasNext\",\"role\":"
                    + "\"OUTPUT_RELATION\"}],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + state
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.RUNTIME.HELPER\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent updateRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent helperCall =
                    new RuntimeRegionPlanner.MethodEvent(3, "testHandle",
                            "PROCESS", "writer", 101L, helper, 42,
                            "example.KeyState", 12, 11, 900, 300L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.RuntimeEvent callSite =
                    new RuntimeRegionPlanner.RuntimeEvent(2,
                            "CALL_SITE_ENTER", updater, 11, 900, 0,
                            updater + "#u5", helper, -1,
                            "example.KeyState", 42, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent helperBranch =
                    new RuntimeRegionPlanner.RuntimeEvent(4, "BRANCH",
                            helper, 12, 0, 900, helperSite, -1, "", 0,
                            "", true, false);
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(5,
                            "FIELD_WRITE", helper, 12, state, 77, 88,
                            "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 77, 88,
                            "");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(updateRoot, helperCall, readRoot),
                    Arrays.asList(callSite, helperBranch),
                    Arrays.asList(write, read));

            assertEquals(3, result.activations.size());
            Map<String, Object> writerInstance = result.instances.get(0);
            assertTrue(String.valueOf(writerInstance.get("observedMethods"))
                    .contains(helper));
            assertTrue(String.valueOf(writerInstance.get(
                    "runtimeAdmittedMethods")).contains(helper));
            assertEquals("EXACT_SAME_THREAD_DESCENDANT_CALL_TREE_V1",
                    writerInstance.get("runtimeMethodAdmissionAuthority"));
            Map<String, Object> upstream = result.activations.get(2);
            assertEquals(Boolean.TRUE,
                    upstream.get("requestedOutputSliceComplete"));
            assertTrue(String.valueOf(upstream.get("requestedOutputMethods"))
                    .contains(helper));
            assertTrue(String.valueOf(upstream.get("branches"))
                    .contains(helperSite));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void upstreamCarrierUsesOnlyDeepestRequestedFieldPaths()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String updater = "<example.Updater: void apply(example.Envelope)>";
            String reader = "<example.Reader: void consume()>";
            String argument = updater + ".param0:example.Envelope";
            String state = "<example.State: java.util.Map entries>";
            String payload = "<example.Envelope: example.Payload payload>";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + updater + "\","
                    + "\"anchorMethod\":\"" + updater + "\","
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.W.in.0\","
                    + "\"cell\":\"" + argument + "\","
                    + "\"sourceKind\":\"ROOT_ARGUMENT\","
                    + "\"projection\":\"argument[0]\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state + "\","
                    + "\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"inputPorts\":[\"REGION.W.in.0\"],"
                    + "\"inputBindings\":["
                    + carrierBinding(payload) + ","
                    + carrierBinding(payload + "#field:entries") + ","
                    + carrierBinding(payload
                    + "#field:current#field:id") + "],"
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"sites\":[],\"causalEdgeIds\":[\"DF.1\"],"
                    + "\"causalEdges\":["
                    + causalReference("DF.1", updater, updater + "#u1")
                    + "],"
                    + "\"complete\":true,"
                    + "\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}"
                    + System.lineSeparator();
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.R.in.0\","
                    + "\"cell\":\"" + state + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:entries\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}"
                    + System.lineSeparator();
            Files.write(regions, (writerRegion + readerRegion)
                    .getBytes(StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.PRODUCER\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}"
                    + System.lineSeparator();
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(5,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.RuntimeEvent rootArgument =
                    new RuntimeRegionPlanner.RuntimeEvent(2,
                            "METHOD_ARGUMENT", updater, 11, 0, 0,
                            updater + "#entry", 0, "example.Envelope", 901,
                            "", false, false);
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(3,
                            "FIELD_WRITE", updater, 11, state, 77, 88, "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(6,
                            "FIELD_READ", reader, 22, state, 77, 88, "");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.singletonList(rootArgument),
                    Arrays.asList(write, read));

            @SuppressWarnings("unchecked")
            Map<String, Object> producer = result.activations.get(2);
            @SuppressWarnings("unchecked")
            Map<String, Object> action = (Map<String, Object>)
                    ((java.util.List<?>) producer.get("symbolize")).get(0);
            assertEquals("ARGUMENT_FIELD_PATH", action.get("location"));
            assertEquals("SELECTIVE_FIELD_PATHS",
                    action.get("materializationMode"));
            assertEquals(true, action.get("fieldPathSelectionComplete"));
            assertEquals(Arrays.asList(
                    Arrays.asList("payload", "entries"),
                    Arrays.asList("payload", "current", "id")),
                    action.get("fieldPaths"));
            assertFalse(String.valueOf(action.get("fieldPaths"))
                    .contains("[payload]"));
            assertEquals(true, producer.get("symbolicReady"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void derivedArgumentArrayLeafJoinsExactConsumedFieldRead()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String updater = "<example.ArrayUpdater: void apply(example.Envelope)>";
            String reader = "<example.ArrayReader: void consume()>";
            String argument = updater + ".param0:example.Envelope";
            String state = "<example.State: java.util.Map entries>";
            String payload = "<example.Envelope: example.Payload payload>";
            String leaf = "<example.Payload: example.Value[] values>";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + updater + "\","
                    + "\"anchorMethod\":\"" + updater + "\","
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.W.in.0\",\"cell\":\"" + argument
                    + "\",\"sourceKind\":\"ROOT_ARGUMENT\","
                    + "\"projection\":\"argument[0]\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{\"outputPort\":"
                    + "\"REGION.W.out.0\",\"outputCell\":\"" + state
                    + "\",\"inputPorts\":[\"REGION.W.in.0\"],"
                    + "\"inputBindings\":[{\"dependencyCell\":\""
                    + payload + "#field:values\",\"inputPort\":"
                    + "\"REGION.W.in.0\",\"bindingAuthority\":"
                    + "\"UNIQUE_ROOT_ARGUMENT_CARRIER\","
                    + "\"dependencyMethods\":[\"" + updater + "\"],"
                    + "\"fieldPath\":[\"payload\",\"values\"],"
                    + "\"leafFieldSignature\":\"" + leaf + "\"}],"
                    + "\"methods\":[\"" + updater + "\"],"
                    + "\"sites\":[],\"causalEdgeIds\":[\"DF.ARRAY\"],"
                    + "\"causalEdges\":["
                    + causalReference("DF.ARRAY", updater, updater + "#u1")
                    + "],"
                    + "\"complete\":true,\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + state
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.ARRAY\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.RuntimeEvent rootArgument =
                    new RuntimeRegionPlanner.RuntimeEvent(2,
                            "METHOD_ARGUMENT", updater, 11, 0, 0,
                            updater + "#entry", 0, "example.Envelope", 901,
                            "", false, false);
            RuntimeRegionPlanner.FieldAccessEvent payloadRead =
                    exactFieldRead(3, updater, 11, 4, payload, 901, 902);
            RuntimeRegionPlanner.FieldAccessEvent leafRead =
                    exactFieldRead(4, updater, 11, 7, leaf, 902, 903);
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(5,
                            "FIELD_WRITE", updater, 11, state, 77, 88, "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 77, 88, "");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.singletonList(rootArgument),
                    Arrays.asList(payloadRead, leafRead, write, read));
            @SuppressWarnings("unchecked")
            Map<String, Object> producer = result.activations.get(2);
            @SuppressWarnings("unchecked")
            Map<String, Object> action = ((List<Map<String, Object>>)
                    producer.get("symbolize")).get(0);
            assertEquals(Boolean.TRUE, producer.get("symbolicReady"));
            assertEquals(Arrays.asList("payload", "values"),
                    action.get("fieldPath"));
            assertEquals("example.Value[]", action.get("javaType"));
            assertEquals(updater + "#u7",
                    action.get("consumedFieldSiteId"));
            assertEquals("ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_"
                            + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY",
                    action.get("consumedFieldRootAuthority"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void materializesObservedReceiverFieldAtTheRootReceiver()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            String field = "@this: example.Handler#field:allKeys";
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[{\"portId\":\"REGION.0.in.0\","
                    + "\"cell\":\"" + field
                    + "\",\"sourceKind\":\"RECEIVER_FIELD\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent root = method(1, HANDLE, 1, 0, 0);
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(2, "FIELD_READ",
                            HANDLE, 1, "<example.Handler: java.util.Map allKeys>",
                            42, 77, "");
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(root),
                    Collections.emptyList(), Collections.singletonList(read));

            assertEquals(1, result.activations.size());
            assertTrue(result.activationsJsonl()
                    .contains("\"location\":\"RECEIVER_FIELD\""));
            assertTrue(result.activationsJsonl()
                    .contains("\"receiverObjectId\":42"));
            assertEquals(true, result.instances.get(0).get("symbolicReady"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void doesNotAliasSameNamedFieldsAcrossOwners() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String expected =
                    "<example.Payload: java.lang.Object allKeys>";
            String wrong = "<example.State: java.util.Map allKeys>";
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.0.in.0\",\"cell\":\"" + expected
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.FieldAccessEvent unrelated =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_READ", HANDLE, 1, wrong, 42, 77, "");
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, HANDLE, 1, 0, 0)),
                    Collections.emptyList(),
                    Collections.singletonList(unrelated));

            @SuppressWarnings("unchecked")
            Map<String, Object> action = (Map<String, Object>)
                    ((java.util.List<?>) result.activations.get(0)
                            .get("symbolize")).get(0);
            assertEquals(false, action.get("observed"));
            assertEquals("HEAP_OBJECT_FIELD", action.get("location"));
            assertEquals("example.Payload", action.get("accessOwnerClass"));
            assertEquals("java.lang.Object", action.get("accessFieldType"));
            assertEquals("allKeys", action.get("accessField"));
            assertEquals(expected, action.get("accessFieldSignature"));
            assertEquals("STATIC_CANONICAL_DECLARED_FIELD",
                    action.get("accessFieldAuthority"));
            assertEquals(false, result.instances.get(0).get(
                    "symbolicReady"));
            assertFalse(result.activationsJsonl().contains(
                    "\"field\":\"" + wrong + "\""));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void promotedDeclaredFieldObservesOnlyItsAuthorizedReadSite()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String field = "<example.DelegationKey: long expiryDate>";
            String getter =
                    "<example.DelegationKey: long getExpiryDate()>";
            String site = HANDLE + "#u11";
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.0.in.0\",\"cell\":\"" + field
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\","
                    + "\"bindingMode\":\"FIELD_ACCESS\","
                    + "\"accessFieldSignature\":\"" + field + "\","
                    + "\"accessOwnerClass\":\"example.DelegationKey\","
                    + "\"accessFieldType\":\"long\","
                    + "\"accessField\":\"expiryDate\","
                    + "\"accessorCallerMethod\":\"" + HANDLE + "\","
                    + "\"accessorCallSiteId\":\"" + site + "\","
                    + "\"accessorCallUnitIndex\":11,"
                    + "\"accessorDeclaredCallee\":\"" + getter + "\","
                    + "\"accessorImplementationMethod\":\"" + getter
                    + "\",\"accessorImplementationAuthority\":"
                    + "\"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY\","
                    + "\"accessorCallSiteAuthority\":"
                    + "\"STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                    + "ACCESSOR_CALLSITE_V1\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent root = method(1, HANDLE, 1,
                    0, 0);
            RuntimeRegionPlanner.MethodEvent exactGetter = method(3, getter,
                    2, 1, 20);
            RuntimeRegionPlanner.MethodEvent wrongGetter = method(5, getter,
                    3, 1, 21);
            RuntimeRegionPlanner.RuntimeEvent exactCall =
                    new RuntimeRegionPlanner.RuntimeEvent(2,
                            "CALL_SITE_ENTER", HANDLE, 1, 20, 0,
                            HANDLE + "#u11", getter, -1,
                            "example.DelegationKey", 43, "", false,
                            false);
            RuntimeRegionPlanner.RuntimeEvent wrongCall =
                    new RuntimeRegionPlanner.RuntimeEvent(4,
                            "CALL_SITE_ENTER", HANDLE, 1, 21, 0,
                            HANDLE + "#u12", getter, -1,
                            "example.DelegationKey", 42, "", false,
                            false);
            RuntimeRegionPlanner.FieldAccessEvent wrongSite = exactFieldRead(
                    6, getter, 3, 1, field, 42, 0);
            RuntimeRegionPlanner.FieldAccessEvent exactSite = exactFieldRead(
                    7, getter, 2, 1, field, 43, 0);
            RuntimeRegionPlanner.Result selected = RuntimeRegionPlanner.plan(
                    regions.toFile(), Arrays.asList(root, exactGetter,
                            wrongGetter), Arrays.asList(exactCall, wrongCall),
                    Arrays.asList(wrongSite, exactSite));

            @SuppressWarnings("unchecked")
            Map<String, Object> selectedAction = (Map<String, Object>)
                    ((List<?>) selected.activations.get(0).get(
                            "symbolize")).get(0);
            assertEquals(Boolean.TRUE, selectedAction.get("observed"));
            assertEquals(43, selectedAction.get("fieldReceiverObjectId"));
            assertEquals(HANDLE,
                    selectedAction.get("accessorCallerMethod"));
            assertEquals(site, selectedAction.get("accessorCallSiteId"));
            assertEquals(11,
                    selectedAction.get("accessorCallUnitIndex"));
            assertEquals(getter,
                    selectedAction.get("accessorDeclaredCallee"));

            RuntimeRegionPlanner.Result rejected = RuntimeRegionPlanner.plan(
                    regions.toFile(), Arrays.asList(root, wrongGetter),
                    Collections.singletonList(wrongCall),
                    Collections.singletonList(wrongSite));
            @SuppressWarnings("unchecked")
            Map<String, Object> rejectedAction = (Map<String, Object>)
                    ((List<?>) rejected.activations.get(0).get(
                            "symbolize")).get(0);
            assertEquals(Boolean.FALSE, rejectedAction.get("observed"));
            assertEquals(Boolean.FALSE,
                    rejected.instances.get(0).get("symbolicReady"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void promotedPrimitiveFieldUsesUniqueExactAccessorReturnWhenGetterBodyIsUntraced()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String field = "<example.Command: int action>";
            String getter = "<example.Command: int getAction()>";
            String site = HANDLE + "#u11";
            Files.write(regions, accessorFieldRegion(field, getter, site)
                    .getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.RuntimeEvent enter =
                    new RuntimeRegionPlanner.RuntimeEvent(2,
                            "CALL_SITE_ENTER", HANDLE, 1, 20, 0,
                            site, getter, -1, "example.KeyUpdateCommand",
                            43, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent returned =
                    new RuntimeRegionPlanner.RuntimeEvent(3,
                            "CALL_SITE_RETURN", HANDLE, 1, 20, 0,
                            site, getter, -1, "", 0, "7", false,
                            false);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, HANDLE, 1, 0, 0)),
                    Arrays.asList(enter, returned),
                    Collections.emptyList());

            @SuppressWarnings("unchecked")
            Map<String, Object> action = (Map<String, Object>)
                    ((List<?>) result.activations.get(0).get(
                            "symbolize")).get(0);
            assertEquals(Boolean.TRUE, action.get("observed"));
            assertEquals("HEAP_OBJECT_FIELD", action.get("location"));
            assertEquals(field, action.get("field"));
            assertEquals(43, action.get("fieldReceiverObjectId"));
            assertEquals("7", action.get("primitiveValue"));
            assertEquals("ACCESSOR_RETURN", action.get("accessKind"));
            assertEquals("RUNTIME_EXACT_ACCESSOR_CALL_RETURN_PLUS_"
                            + "STATIC_DIRECT_FIELD_ACCESSOR_V1",
                    action.get("observationAuthority"));
            assertEquals(20L, action.get("accessorInvocationId"));
            assertEquals(Boolean.TRUE,
                    result.instances.get(0).get("symbolicReady"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void ambiguousExactAccessorReturnsDoNotSelectOneFieldInstance()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String field = "<example.Command: int action>";
            String getter = "<example.Command: int getAction()>";
            String site = HANDLE + "#u11";
            Files.write(regions, accessorFieldRegion(field, getter, site)
                    .getBytes(StandardCharsets.UTF_8));

            List<RuntimeRegionPlanner.RuntimeEvent> calls = Arrays.asList(
                    new RuntimeRegionPlanner.RuntimeEvent(2,
                            "CALL_SITE_ENTER", HANDLE, 1, 20, 0,
                            site, getter, -1, "example.Command", 43,
                            "", false, false),
                    new RuntimeRegionPlanner.RuntimeEvent(3,
                            "CALL_SITE_RETURN", HANDLE, 1, 20, 0,
                            site, getter, -1, "", 0, "7", false,
                            false),
                    new RuntimeRegionPlanner.RuntimeEvent(4,
                            "CALL_SITE_ENTER", HANDLE, 1, 21, 0,
                            site, getter, -1, "example.Command", 44,
                            "", false, false),
                    new RuntimeRegionPlanner.RuntimeEvent(5,
                            "CALL_SITE_RETURN", HANDLE, 1, 21, 0,
                            site, getter, -1, "", 0, "7", false,
                            false));
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, HANDLE, 1, 0, 0)), calls,
                    Collections.emptyList());

            @SuppressWarnings("unchecked")
            Map<String, Object> action = (Map<String, Object>)
                    ((List<?>) result.activations.get(0).get(
                            "symbolize")).get(0);
            assertEquals(Boolean.FALSE, action.get("observed"));
            assertEquals(Boolean.FALSE,
                    result.instances.get(0).get("symbolicReady"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void refusesToGuessOwnerForReceiverLocalHeapProjection()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String localProjection = HANDLE + "::$r7#field:expiryDate";
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.0.in.0\",\"cell\":\"" + localProjection
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:expiryDate\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, HANDLE, 1, 0, 0)),
                    Collections.emptyList(), Collections.emptyList());

            @SuppressWarnings("unchecked")
            Map<String, Object> action = (Map<String, Object>)
                    ((java.util.List<?>) result.activations.get(0)
                            .get("symbolize")).get(0);
            assertEquals("REGION_LIVE_IN", action.get("location"));
            assertEquals(true, action.get("deferredResolution"));
            assertEquals("MISSING_CANONICAL_DECLARED_FIELD_SIGNATURE",
                    action.get("fieldBindingGap"));
            assertFalse(action.containsKey("accessOwnerClass"));
            assertFalse(action.containsKey("accessField"));
            assertFalse(action.containsKey("accessFieldType"));
            assertFalse(action.containsKey("accessFieldSignature"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void doesNotRebaseAnotherMethodsArgumentByIndex()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String other = "<example.Updater: void apply(example.Payload)>";
            String cell = other
                    + ".param0:example.Payload#field:entries";
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                    + "\",\"methods\":[\"" + HANDLE
                    + "\"],\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.0.in.0\",\"cell\":\"" + cell
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"argument[0].entries\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent root = method(1, HANDLE,
                    1, 0, 0);
            RuntimeRegionPlanner.RuntimeEvent rootArgument =
                    new RuntimeRegionPlanner.RuntimeEvent(2,
                            "METHOD_ARGUMENT", HANDLE, 1, 0, 0,
                            HANDLE + "#entry", 0, "java.lang.Object[]", 99,
                            "", false, false);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(root),
                    Collections.singletonList(rootArgument),
                    Collections.emptyList());

            @SuppressWarnings("unchecked")
            Map<String, Object> action = (Map<String, Object>)
                    ((java.util.List<?>) result.activations.get(0)
                            .get("symbolize")).get(0);
            assertEquals("REGION_LIVE_IN", action.get("location"));
            assertEquals(false, action.get("observed"));
            assertEquals(true, action.get("deferredResolution"));
            assertEquals(true, action.get("crossMethodArgument"));
            assertEquals(other, action.get("staticInputMethod"));
            assertEquals(HANDLE, action.get("runtimeInputMethod"));
            assertEquals("STATIC_INPUT_METHOD_DIFFERS_FROM_RUNTIME_ROOT",
                    action.get("rebaseRejectedAuthority"));
            assertFalse(action.containsKey("runtimeRebased"));
            assertFalse(action.containsKey("materializationMode"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void narrowsObjectArgumentUsingRecoveredFailurePredicate()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + RETRIEVE + "\",\"anchorMethod\":\"" + RETRIEVE
                    + "\",\"methods\":[\"" + RETRIEVE
                    + "\"],\"symbolicInputs\":[{\"portId\":\"REGION.0.in.0\","
                    + "\"cell\":\"" + RETRIEVE + ".param0:example.Token\","
                    + "\"sourceKind\":\"ROOT_ARGUMENT\","
                    + "\"projection\":\"argument[0]\"}],\"outputs\":[{"
                    + "\"portId\":\"REGION.0.out.0\","
                    + "\"cell\":\"allKeys.get(request.getKeyId()) == null\","
                    + "\"kind\":\"FAILURE_PREDICATE\"}],"
                    + "\"branchPolicies\":[{\"siteId\":\"" + RETRIEVE
                    + "#u8\",\"policy\":\"EXPLORE\","
                    + "\"guard\":\"if r25 != null goto return\"}],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent root = method(1, RETRIEVE, 1, 0, 0);
            RuntimeRegionPlanner.RuntimeEvent argument =
                    new RuntimeRegionPlanner.RuntimeEvent(2, "METHOD_ARGUMENT",
                            RETRIEVE, 1, 0, 0, "", 0,
                            "example.Token", 99, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent getter =
                    new RuntimeRegionPlanner.RuntimeEvent(3, "CALL_SITE_ENTER",
                            RETRIEVE, 1, 3, 0, RETRIEVE + "#u4",
                            "<example.Token: int getKeyId()>", -1,
                            "example.Token", 99, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent branch =
                    new RuntimeRegionPlanner.RuntimeEvent(4, "BRANCH",
                            RETRIEVE, 1, 0, 0, RETRIEVE + "#u8", -1,
                            "", 0, "", true, true);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(root),
                    Arrays.asList(argument, getter, branch),
                    Collections.emptyList());

            String activation = result.activationsJsonl();
            assertTrue(activation.contains("\"location\":\"ARGUMENT_FIELD\""));
            assertTrue(activation.contains("\"fields\":[\"keyId\"]"));
            assertTrue(activation.contains(
                    "\"materializationMode\":\"SELECTIVE_FIELDS\""));
            assertEquals(true, result.instances.get(0).get("symbolicReady"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void includesEarlierPathFieldFromStaticRootContract()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + RETRIEVE + "\",\"anchorMethod\":\"" + RETRIEVE
                    + "\",\"methods\":[\"" + RETRIEVE + "\"],"
                    + "\"argumentPathFields\":[{\"method\":\"" + RETRIEVE
                    + "\",\"argumentIndex\":0,"
                    + "\"fields\":[\"expiryDate\",\"keyId\"],"
                    + "\"branchSites\":[\"" + RETRIEVE + "#u3\",\""
                    + RETRIEVE + "#u8\"],"
                    + "\"authority\":\"STATIC_ROOT_BRANCH_DATAFLOW\"}],"
                    + "\"symbolicInputs\":[{\"portId\":\"REGION.0.in.0\","
                    + "\"cell\":\"" + RETRIEVE + ".param0:example.Token\","
                    + "\"sourceKind\":\"ROOT_ARGUMENT\","
                    + "\"projection\":\"argument[0]\"}],"
                    + "\"outputs\":[],"
                    + "\"branchPolicies\":[{\"siteId\":\"" + RETRIEVE
                    + "#u8\",\"policy\":\"PATH_ASSUMPTION\","
                    + "\"guard\":\"if r25 != null goto return\"}],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent root = method(1, RETRIEVE, 1, 0, 0);
            RuntimeRegionPlanner.RuntimeEvent argument =
                    new RuntimeRegionPlanner.RuntimeEvent(2, "METHOD_ARGUMENT",
                            RETRIEVE, 1, 0, 0, "", 0,
                            "example.Token", 99, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent branch =
                    new RuntimeRegionPlanner.RuntimeEvent(3, "BRANCH",
                            RETRIEVE, 1, 0, 0, RETRIEVE + "#u8", -1,
                            "", 0, "", true, true);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(root),
                    Arrays.asList(argument, branch), Collections.emptyList());

            String activation = result.activationsJsonl();
            assertTrue(activation.contains(
                    "\"fields\":[\"expiryDate\",\"keyId\"]"));
            assertTrue(activation.contains(
                    "\"materializationMode\":\"SELECTIVE_FIELDS\""));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void protocolEdgeRequiresPayloadProbeForValueEquality() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String sender = "<example.Client: void send()>";
            String receiver = "<example.Server: void handle()>";
            Files.write(regions, (region("REGION.S", sender)
                    + region("REGION.D", receiver)).getBytes(StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.1\","
                    + "\"fromRegion\":\"REGION.S\","
                    + "\"toRegion\":\"REGION.D\","
                    + "\"fromPort\":\"sender.userName\","
                    + "\"toPort\":\"server.userName\","
                    + "\"kind\":\"SASL_TRANSFER\","
                    + "\"relation\":\"EQUALITY\","
                    + "\"requiresOrder\":true,\"siteId\":\"synthetic\"}\n";
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent send = methodContext(1, sender, 1,
                    "BALANCER", "Dispatcher", 21L);
            RuntimeRegionPlanner.MethodEvent receive = methodContext(2, receiver, 2,
                    "DATANODE", "DataXceiver", 22L);
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(), Arrays.asList(send, receive),
                    Collections.emptyList(), Collections.emptyList());

            assertEquals("ENDPOINTS_OBSERVED",
                    result.edgeValidations.get(0).get("status"));
            assertEquals("PORT_ORDER_AND_VALUE_EQUALITY_UNPROVEN",
                    result.edgeValidations.get(0).get("validation"));
            assertEquals("",
                    result.edgeValidations.get(0).get("relation"));
            assertEquals("EQUALITY",
                    result.edgeValidations.get(0).get("candidateRelation"));
            assertEquals(true, result.edgeValidations.get(0)
                    .get("payloadEqualityCheckRequired"));
            assertEquals(false,
                    result.edgeValidations.get(0).get("composable"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void staticSaslMappingCannotDeclareAutomaticEquality()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String sender = "<example.HdfsSaslClient: void handshake()>";
            String receiver = "<example.HdfsSaslServer: void handle()>";
            Files.write(regions, (region("REGION.C", sender)
                    + region("REGION.S", receiver)).getBytes(
                    StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.SASL\","
                    + "\"fromRegion\":\"REGION.C\","
                    + "\"toRegion\":\"REGION.S\","
                    + "\"fromPort\":\"" + sender + ".param3:userName\","
                    + "\"toPort\":\"" + receiver + "::$r4\","
                    + "\"kind\":\"SASL_TRANSFER\","
                    + "\"relation\":\"EQUALITY\","
                    + "\"mappingKind\":\"hdfs_sasl_username\","
                    + "\"mappingAuthority\":"
                    + "\"STATIC_HDFS_SASL_CONTRACT\","
                    + "\"payloadEqualityCheckRequired\":false,"
                    + "\"requiresOrder\":true,"
                    + "\"siteId\":\"synthetic:hdfs_sasl_username\"}\n";
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent send = methodContext(1, sender, 1,
                    "BALANCER", "Dispatcher", 21L);
            RuntimeRegionPlanner.MethodEvent receive = methodContext(2, receiver,
                    2, "DATANODE", "DataXceiver", 22L);
            RuntimeRegionPlanner.MethodEvent sendAgain = methodContext(3,
                    sender, 3, "BALANCER", "Dispatcher", 21L);
            RuntimeRegionPlanner.MethodEvent receiveAgain = methodContext(4,
                    receiver, 4, "DATANODE", "DataXceiver", 23L);
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(), Arrays.asList(send,
                            receive, sendAgain, receiveAgain),
                    Collections.emptyList(), Collections.emptyList());

            assertEquals("ENDPOINTS_OBSERVED",
                    result.edgeValidations.get(0).get("status"));
            assertEquals("",
                    result.edgeValidations.get(0).get("validatedRelation"));
            assertEquals("STATIC_FORMAT_AND_PORT_MAPPING",
                    result.edgeValidations.get(0).get("mappingAuthority"));
            assertEquals("STATIC_HDFS_SASL_CONTRACT",
                    result.edgeValidations.get(0).get(
                            "sourceMappingAuthority"));
            assertEquals(false,
                    result.edgeValidations.get(0).get("composable"));
            assertEquals(false, result.edgeValidations.get(0)
                    .get("eligibleForAutomaticDerivation"));
            assertEquals(false, result.edgeValidations.get(0)
                    .get("valueEqualityObserved"));
            assertEquals(4,
                    result.edgeValidations.get(0).get("endpointPairCount"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void saslUsernameUsesCrossProcessEndpointFingerprintAndRootLifetime()
            throws Exception {
        String fingerprint = "sha256:same-sasl-user";
        RuntimeRegionPlanner.MethodEvent firstClient = methodContext(1,
                SASL_CLIENT, 1, "BALANCER", "Dispatcher-1", 31L);
        RuntimeRegionPlanner.MethodEvent selectedClient = methodContext(15,
                SASL_CLIENT, 2, "BALANCER", "Dispatcher-2", 32L);
        RuntimeRegionPlanner.MethodEvent server = methodContext(20,
                SASL_SERVER, 4, "DATANODE", "DataXceiver-1", 41L);
        // This endpoint is globally closer to the callback return, but its
        // root entered after the server activation and belongs to another
        // handshake lifetime.
        RuntimeRegionPlanner.MethodEvent laterClient = methodContext(30,
                SASL_CLIENT, 3, "BALANCER", "Dispatcher-3", 33L);
        RuntimeRegionPlanner.RuntimeEvent firstArgument = saslArgument(
                10, 1, fingerprint);
        RuntimeRegionPlanner.RuntimeEvent selectedArgument = saslArgument(
                18, 2, fingerprint);
        RuntimeRegionPlanner.RuntimeEvent laterArgument = saslArgument(
                40, 3, fingerprint);
        RuntimeRegionPlanner.RuntimeEvent callbackReturn =
                saslCallbackReturn(50, 4, fingerprint);

        RuntimeRegionPlanner.Result result = planSaslUsernameEdge(
                Arrays.asList(firstClient, selectedClient, server,
                        laterClient),
                Arrays.asList(firstArgument, selectedArgument,
                        laterArgument, callbackReturn));

        Map<String, Object> validation = result.edgeValidations.get(0);
        assertEquals("CONFIRMED_RUNTIME_VALUE_EQUALITY",
                validation.get("status"));
        assertEquals("EQUALITY", validation.get("validatedRelation"));
        assertEquals(true, validation.get("composable"));
        assertEquals(1, validation.get("confirmedValueEqualityPairCount"));
        assertEquals(1, validation.get("validatedBindingCount"));
        assertEquals("GLOBAL_TRACE_ENDPOINT_SEQUENCE",
                validation.get("endpointOrderAuthority"));
        assertEquals("NEAREST_PRECEDING_SOURCE_ROOT_THEN_ENDPOINT",
                validation.get("endpointCorrelationAuthority"));
        Map<?, ?> binding = (Map<?, ?>) ((List<?>) validation.get(
                "validatedBindings")).get(0);
        assertEquals("REGION.C@testHandle#call2",
                binding.get("fromRegionInstance"));
        assertEquals("REGION.S@testHandle#call4",
                binding.get("toRegionInstance"));
        assertEquals(18L, binding.get("fromEndpointSeq"));
        assertEquals(50L, binding.get("toEndpointSeq"));
        assertEquals("METHOD_ARGUMENT",
                binding.get("fromFingerprintSource"));
        assertEquals("HDFS_SASL_NAME_CALLBACK_DEFAULT_RETURN",
                binding.get("toFingerprintSource"));
        assertEquals(false, binding.get("sameProcess"));
    }

    @Test
    public void saslUsernameRejectsReverseEndpointOrder()
            throws Exception {
        String fingerprint = "sha256:same-sasl-user";
        RuntimeRegionPlanner.Result result = planSaslUsernameEdge(
                Arrays.asList(
                        methodContext(1, SASL_CLIENT, 1, "BALANCER",
                                "Dispatcher", 31L),
                        methodContext(20, SASL_SERVER, 2, "DATANODE",
                                "DataXceiver", 41L)),
                Arrays.asList(
                        saslCallbackReturn(50, 2, fingerprint),
                        saslArgument(60, 1, fingerprint)));

        Map<String, Object> validation = result.edgeValidations.get(0);
        assertEquals("ENDPOINTS_OBSERVED", validation.get("status"));
        assertEquals(false, validation.get("composable"));
        assertEquals(0, validation.get("confirmedValueEqualityPairCount"));
        assertEquals(0, validation.get("validatedBindingCount"));
    }

    @Test
    public void saslUsernameRejectsDifferentCompleteFingerprint()
            throws Exception {
        RuntimeRegionPlanner.Result result = planSaslUsernameEdge(
                Arrays.asList(
                        methodContext(1, SASL_CLIENT, 1, "BALANCER",
                                "Dispatcher", 31L),
                        methodContext(20, SASL_SERVER, 2, "DATANODE",
                                "DataXceiver", 41L)),
                Arrays.asList(
                        saslArgument(10, 1, "sha256:client-user"),
                        saslCallbackReturn(50, 2,
                                "sha256:different-server-user")));

        Map<String, Object> validation = result.edgeValidations.get(0);
        assertEquals("ENDPOINTS_OBSERVED", validation.get("status"));
        assertEquals(false, validation.get("composable"));
        assertEquals(0, validation.get("confirmedValueEqualityPairCount"));
        assertEquals(0, validation.get("validatedBindingCount"));
    }

    @Test
    public void rpcPortMappingNeedsRuntimeValueEquality()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String server = "<example.NameNode: example.Keys getBlockKeys()>";
            String updater = "<example.KeyUpdater: void run()>";
            Files.write(regions, (region("REGION.NN", server)
                    + region("REGION.B", updater)).getBytes(StandardCharsets.UTF_8));
            String site = updater + "#u4";
            String edge = "{\"edgeId\":\"E.RPC\","
                    + "\"fromRegion\":\"REGION.NN\","
                    + "\"toRegion\":\"REGION.B\","
                    + "\"fromPort\":\"" + server
                    + ".return#field:currentKey#field:keyId\","
                    + "\"toPort\":\"" + updater
                    + "::keys#field:currentKey#field:keyId\","
                    + "\"kind\":\"RPC_RETURN\",\"relation\":\"EQUALITY\","
                    + "\"requiresOrder\":true,"
                    + "\"siteId\":\"synthetic:projected_rpc_return\"}\n";
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent send = methodContext(1, server, 1,
                    "NAMENODE", "IPC Server", 31L);
            RuntimeRegionPlanner.MethodEvent receive = methodContext(2, updater, 2,
                    "BALANCER", "KeyUpdater", 32L);
            RuntimeRegionPlanner.RuntimeEvent callSite =
                    new RuntimeRegionPlanner.RuntimeEvent(3, "CALL_SITE_ENTER",
                            updater, 2, 3, 0, site, server, -1,
                            "example.NameNode", 0, "", false, false);
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(), Arrays.asList(send, receive),
                    Collections.singletonList(callSite), Collections.emptyList());

            assertEquals("PORT_MAPPING_OBSERVED_VALUE_EQUALITY_UNPROVEN",
                    result.edgeValidations.get(0).get("status"));
            assertEquals("",
                    result.edgeValidations.get(0).get("validatedRelation"));
            assertEquals(false,
                    result.edgeValidations.get(0).get("composable"));
            assertEquals(false, result.edgeValidations.get(0)
                    .get("eligibleForAutomaticDerivation"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void completeRuntimeFingerprintsPromotePortMapToEquality()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String server = "<example.NameNode: example.Keys getKeys()>";
            String updater = "<example.Updater: void run()>";
            String site = updater + "#u4";
            Files.write(regions, (region("REGION.NN", server)
                    + region("REGION.UP", updater)).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.RUNTIME\","
                    + "\"fromRegion\":\"REGION.NN\","
                    + "\"toRegion\":\"REGION.UP\","
                    + "\"fromPort\":\"" + server + ".return\","
                    + "\"toPort\":\"" + updater + "::$r2\","
                    + "\"kind\":\"RPC_RETURN\","
                    + "\"candidateRelation\":\"EQUALITY\","
                    + "\"requiresOrder\":true,\"siteId\":\""
                    + site + "\"}\n").getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent send = methodContext(1, server,
                    1, "NAMENODE", "IPC Server", 31L);
            RuntimeRegionPlanner.MethodEvent receive = methodContext(4,
                    updater, 4, "BALANCER", "Updater", 32L);
            String fingerprint = "sha256:0123456789abcdef";
            RuntimeRegionPlanner.RuntimeEvent returned =
                    new RuntimeRegionPlanner.RuntimeEvent(2,
                            "METHOD_EXIT_NORMAL", server, 1, 0, 0,
                            server + "#exit", "", -1, "example.Keys",
                            41, "", false, false, fingerprint, true, 4,
                            "COMPLETE");
            RuntimeRegionPlanner.RuntimeEvent received =
                    new RuntimeRegionPlanner.RuntimeEvent(5,
                            "CALL_SITE_RETURN", updater, 4, 9, 0, site,
                            server, -1, "example.Keys", 42, "", false,
                            false, fingerprint, true, 4, "COMPLETE");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(send, receive),
                    Arrays.asList(returned, received),
                    Collections.emptyList());

            Map<String, Object> validation = result.edgeValidations.get(0);
            assertEquals("CONFIRMED_RUNTIME_VALUE_EQUALITY",
                    validation.get("status"));
            assertEquals("EQUALITY", validation.get("validatedRelation"));
            assertEquals(true, validation.get("composable"));
            assertEquals(true,
                    validation.get("eligibleForAutomaticDerivation"));
            assertEquals("RUNTIME_COMPLETE_VALUE_FINGERPRINT",
                    validation.get("valueEqualityAuthority"));
            assertEquals(1, validation.get(
                    "confirmedValueEqualityPairCount"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void canonicalProducerOutputCapturesProjectedLocalFingerprint()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String producer =
                    "<example.BlockManager: void addKeyUpdateCommand()>";
            String consumer =
                    "<example.OfferService: void processCommand()>";
            String rawSource = producer + "::$r5#field:allKeys";
            String rawTarget = consumer + "::$r59#field:allKeys";
            String canonical =
                    "<example.ExportedKeys: example.Key[] allKeys>";
            String outputPort = "REGION.NN.out.keys";
            String site = consumer
                    + "#synthetic:projected_heartbeat_key_update";
            String producerRegion = "{\"regionId\":\"REGION.NN\","
                    + "\"rootMethod\":\"" + producer + "\","
                    + "\"anchorMethod\":\"" + producer + "\","
                    + "\"methods\":[\"" + producer + "\"],"
                    + "\"symbolicInputs\":[],\"outputs\":[{"
                    + "\"portId\":\"" + outputPort + "\","
                    + "\"cell\":\"" + canonical + "\","
                    + "\"kind\":\"HEAP_STATE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, (producerRegion
                    + region("REGION.DN", consumer)).getBytes(
                    StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.HEARTBEAT.KEYS\","
                    + "\"fromRegion\":\"REGION.NN\","
                    + "\"toRegion\":\"REGION.DN\","
                    + "\"fromPort\":\"" + rawSource + "\","
                    + "\"fromOutputPort\":\"" + outputPort + "\","
                    + "\"fromOutputCell\":\"" + canonical + "\","
                    + "\"aliasProofEdgeIds\":[\"DF.1\",\"DF.2\"],"
                    + "\"aliasProofAuthority\":"
                    + "\"STATIC_EXACT_PROJECTED_RETURN_VALUE_FLOW_"
                    + "AND_DECLARED_RETURN_FIELD\","
                    + "\"aliasProofComplete\":true,"
                    + "\"toPort\":\"" + rawTarget + "\","
                    + "\"kind\":\"HEARTBEAT_TRANSFER\","
                    + "\"candidateRelation\":\"EQUALITY\","
                    + "\"requiresOrder\":true,"
                    + "\"siteId\":\"" + site + "\"}\n";
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent send = methodContext(1,
                    producer, 11, "NAMENODE", "IPC Server", 31L);
            RuntimeRegionPlanner.MethodEvent receive = methodContext(4,
                    consumer, 22, "DATANODE", "BPServiceActor", 32L);
            String fingerprint = "sha256:heartbeat-all-keys";
            RuntimeRegionPlanner.FieldAccessEvent capturedOutput =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_WRITE", producer, 11, canonical,
                            71, 81, "", fingerprint, true, 3,
                            "COMPLETE");
            RuntimeRegionPlanner.RuntimeEvent received =
                    new RuntimeRegionPlanner.RuntimeEvent(5,
                            "CALL_SITE_RETURN", consumer, 22, 9, 0, site,
                            "<example.Command: example.Key[] getAllKeys()>",
                            -1, "example.Key[]", 82, "", false, false,
                            fingerprint, true, 3, "COMPLETE");

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(send, receive),
                    Collections.singletonList(received),
                    Collections.singletonList(capturedOutput));

            Map<String, Object> validation = result.edgeValidations.get(0);
            assertEquals("CONFIRMED_RUNTIME_VALUE_EQUALITY",
                    validation.get("status"));
            assertEquals(rawSource, validation.get("fromPort"));
            assertEquals(rawTarget, validation.get("toPort"));
            assertEquals(canonical, validation.get("fromOutputCell"));
            assertEquals(1,
                    validation.get("confirmedValueEqualityPairCount"));
            @SuppressWarnings("unchecked")
            Map<String, Object> binding = ((List<Map<String, Object>>)
                    validation.get("validatedBindings")).get(0);
            assertEquals("FIELD_VALUE",
                    binding.get("fromFingerprintSource"));
            assertEquals("MAPPED_CALL_RETURN_SITE",
                    binding.get("toFingerprintSource"));

            // Canonical capture is authorized only by the complete proof.
            Files.write(edges, edge.replace(
                    "\"aliasProofComplete\":true",
                    "\"aliasProofComplete\":false").getBytes(
                    StandardCharsets.UTF_8));
            RuntimeRegionPlanner.Result rejected = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(send, receive),
                    Collections.singletonList(received),
                    Collections.singletonList(capturedOutput));
            assertEquals(0, rejected.edgeValidations.get(0).get(
                    "confirmedValueEqualityPairCount"));
            assertFalse(Boolean.TRUE.equals(rejected.edgeValidations.get(0)
                    .get("composable")));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void lowerRegionMethodCannotImpersonateProtocolPortEndpoint()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String sender = "<example.Server: example.Keys getKeys()>";
            String expectedReceiver = "<example.BalancerUpdater: void run()>";
            String sharedLowerMethod = "<example.Manager: void addKeys(example.Keys)>";
            String rows = region("REGION.S", sender)
                    + "{\"regionId\":\"REGION.R\",\"rootMethod\":\""
                    + expectedReceiver + "\",\"anchorMethod\":\""
                    + sharedLowerMethod + "\",\"methods\":[\""
                    + expectedReceiver + "\",\"" + sharedLowerMethod
                    + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, rows.getBytes(StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.2\","
                    + "\"fromRegion\":\"REGION.S\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + sender + ".return\","
                    + "\"toPort\":\"" + expectedReceiver + "::keys\","
                    + "\"kind\":\"RPC_RETURN\",\"relation\":\"EQUALITY\","
                    + "\"requiresOrder\":true,\"siteId\":\"\"}\n";
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), edges.toFile(),
                    Arrays.asList(method(1, sender, 1, 0, 0),
                            method(2, sharedLowerMethod, 2, 0, 0)),
                    Collections.emptyList(), Collections.emptyList());

            assertEquals("UNOBSERVED",
                    result.edgeValidations.get(0).get("status"));
            assertEquals(0,
                    result.edgeValidations.get(0).get("endpointPairCount"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void promotesObservedBelowRootEntryToReplayRoot() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + RETRIEVE
                    + "\",\"methods\":[\"" + HANDLE + "\",\"" + RETRIEVE
                    + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, RETRIEVE, 8, 0, 0)),
                    Collections.emptyList(), Collections.emptyList());

            assertEquals(1, result.instances.size());
            assertTrue((Boolean) result.instances.get(0).get("rootObserved"));
            assertFalse((Boolean) result.instances.get(0)
                    .get("staticRootObserved"));
            assertEquals(RETRIEVE,
                    result.instances.get(0).get("finalRootMethod"));
            assertEquals(RETRIEVE,
                    result.activations.get(0).get("rootMethod"));
            assertEquals(HANDLE,
                    result.activations.get(0).get("staticRootMethod"));
            assertTrue((Boolean) result.activations.get(0).get("replayable"));
            assertEquals("RUNTIME_SELECTED_ROOT_REPLAY",
                    result.activations.get(0).get("replayMode"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void selectsHighestObservedRuntimeEntryBelowMissingStaticRoot()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + RETRIEVE
                    + "\",\"methods\":[\"" + HANDLE + "\",\"" + PASSWORD
                    + "\",\"" + RETRIEVE
                    + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent middle =
                    method(1, PASSWORD, 10, 0, 0);
            RuntimeRegionPlanner.MethodEvent anchor =
                    method(2, RETRIEVE, 11, 10, 7);
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Arrays.asList(middle, anchor),
                    Collections.emptyList(), Collections.emptyList());

            assertEquals(1, result.instances.size());
            assertEquals(PASSWORD,
                    result.instances.get(0).get("observedRootMethod"));
            assertEquals("VALIDATED_PATH",
                    result.instances.get(0).get("validationStatus"));
            assertEquals(PASSWORD,
                    result.activations.get(0).get("rootMethod"));
            assertTrue((Boolean) result.activations.get(0).get("replayable"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void ignoresStaticCandidateInvocationThatDidNotReachRuntimeAnchor()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve("symbolic_regions.jsonl");
            String row = "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + RETRIEVE
                    + "\",\"methods\":[\"" + HANDLE + "\",\""
                    + RETRIEVE + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent unrelatedStaticRoot =
                    method(1, HANDLE, 1, 0, 0);
            RuntimeRegionPlanner.MethodEvent directAnchor =
                    method(2, RETRIEVE, 2, 0, 0);
            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Arrays.asList(unrelatedStaticRoot, directAnchor),
                    Collections.emptyList(), Collections.emptyList());

            assertEquals(1, result.instances.size());
            assertEquals(RETRIEVE,
                    result.instances.get(0).get("finalRootMethod"));
            assertFalse((Boolean) result.instances.get(0)
                    .get("staticRootObserved"));
            assertEquals("RUNTIME_SELECTED_ENTRY",
                    result.instances.get(0).get("rootSelection"));
            assertEquals(RETRIEVE,
                    result.activations.get(0).get("rootMethod"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void lateRootDoesNotSpendContainmentBudgetOnGlobalPrefix()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String site = RETRIEVE + "#u8";
            String row = "{\"regionId\":\"REGION.LATE\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + RETRIEVE
                    + "\",\"methods\":[\"" + HANDLE + "\",\""
                    + RETRIEVE + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[{\"siteId\":\"" + site
                    + "\",\"policy\":\"EXPLORE\",\"guard\":\"late\","
                    + "\"requiredOutcome\":false,\"role\":\"REACHABILITY\"}],"
                    + "\"models\":[]}\n";
            Files.write(regions, row.getBytes(StandardCharsets.UTF_8));

            List<RuntimeRegionPlanner.MethodEvent> methods = new ArrayList<>();
            String noise = "<example.Noise: void run()>";
            for (int index = 0; index < 10001; index++) {
                long id = index + 1L;
                methods.add(method(id, noise, id, 0, 0));
            }
            RuntimeRegionPlanner.MethodEvent root =
                    method(20000, HANDLE, 20000, 0, 0);
            RuntimeRegionPlanner.MethodEvent anchor =
                    method(20001, RETRIEVE, 20001, 20000, 19999);
            methods.add(root);
            methods.add(anchor);
            RuntimeRegionPlanner.RuntimeEvent branch =
                    new RuntimeRegionPlanner.RuntimeEvent(20002, "BRANCH",
                            RETRIEVE, 20001, 0, 0, site, -1, "", 0,
                            "", true, false);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), methods,
                    Collections.singletonList(branch),
                    Collections.emptyList());

            assertEquals(1, result.instances.size());
            assertEquals(true, result.instances.get(0).get("anchorObserved"));
            assertEquals(true, result.instances.get(0).get("symbolicReady"));
            assertTrue(String.valueOf(result.instances.get(0).get(
                    "observedMethods")).contains(RETRIEVE));
            assertTrue(result.activationsJsonl().contains(
                    "\"siteId\":\"" + site + "\""));
            assertTrue(result.activationsJsonl().contains(
                    "\"observed\":true"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void sharedAnchorBelongsOnlyToRootInConcreteAncestry()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String heartbeat = "{\"regionId\":\"REGION.HEARTBEAT\","
                    + "\"rootMethod\":\"" + HANDLE + "\","
                    + "\"anchorMethod\":\"" + RETRIEVE + "\","
                    + "\"methods\":[\"" + HANDLE + "\",\"" + RETRIEVE
                    + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String registration = "{\"regionId\":\"REGION.REGISTRATION\","
                    + "\"rootMethod\":\"" + PASSWORD + "\","
                    + "\"anchorMethod\":\"" + RETRIEVE + "\","
                    + "\"methods\":[\"" + PASSWORD + "\",\"" + RETRIEVE
                    + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, (heartbeat + registration)
                    .getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent unrelatedHeartbeat =
                    method(1, HANDLE, 1, 0, 0);
            RuntimeRegionPlanner.MethodEvent registrationRoot =
                    method(10, PASSWORD, 10, 0, 0);
            RuntimeRegionPlanner.MethodEvent anchor =
                    method(11, RETRIEVE, 11, 10, 9);

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Arrays.asList(unrelatedHeartbeat,
                            registrationRoot, anchor),
                    Collections.emptyList(), Collections.emptyList());

            assertEquals(1, result.instances.size());
            assertEquals("REGION.REGISTRATION",
                    result.instances.get(0).get("regionId"));
            assertEquals(PASSWORD,
                    result.instances.get(0).get("finalRootMethod"));
            assertEquals(1, result.activations.size());
            assertTrue(result.unobservedRegionIds.contains("REGION.HEARTBEAT"));
            assertFalse(result.activationsJsonl().contains(
                    "REGION.HEARTBEAT"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void ambiguousSharedAnchorDoesNotCreateSuffixActivations()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            String first = "{\"regionId\":\"REGION.A\",\"rootMethod\":\""
                    + HANDLE + "\",\"anchorMethod\":\"" + RETRIEVE
                    + "\",\"methods\":[\"" + HANDLE + "\",\""
                    + RETRIEVE + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String second = "{\"regionId\":\"REGION.B\",\"rootMethod\":\""
                    + PASSWORD + "\",\"anchorMethod\":\"" + RETRIEVE
                    + "\",\"methods\":[\"" + PASSWORD + "\",\""
                    + RETRIEVE + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, (first + second)
                    .getBytes(StandardCharsets.UTF_8));

            RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                    regions.toFile(), Collections.singletonList(
                            method(1, RETRIEVE, 1, 0, 0)),
                    Collections.emptyList(), Collections.emptyList());

            assertEquals(0, result.instances.size());
            assertEquals(0, result.activations.size());
            assertTrue(result.unobservedRegionIds.contains("REGION.A"));
            assertTrue(result.unobservedRegionIds.contains("REGION.B"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void propagatesExactContainerFieldBindingToOutputActivation()
            throws Exception {
        RuntimeRegionPlanner.Result result = containerBindingRuntimeResult(
                false);
        assertEquals(3, result.activations.size());
        @SuppressWarnings("unchecked")
        Map<String, Object> upstream = result.activations.get(2);
        assertEquals(Boolean.TRUE,
                upstream.get("requestedOutputSliceComplete"));
        assertEquals(Boolean.TRUE, upstream.get("symbolicReady"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> declarations =
                (List<Map<String, Object>>) upstream.get(
                        "containerElementFieldBindings");
        assertEquals(1, declarations.size());
        assertEquals("BIND.ARRAY.0",
                declarations.get(0).get("bindingId"));
        assertEquals("EXACT_ARRAY_INDEX",
                declarations.get(0).get("selectorAuthority"));
        assertEquals(0, declarations.get(0).get("elementIndex"));
        assertEquals(1, declarations.get(0).get("elementOccurrence"));
        assertEquals(Arrays.asList("A", "C", "G", "P"),
                declarations.get(0).get("proofCausalEdgeIds"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> actions =
                (List<Map<String, Object>>) upstream.get("symbolize");
        Map<String, Object> base = actions.stream().filter(action ->
                "REGION.W.in.key".equals(action.get("symbol")))
                .findFirst().orElseThrow(AssertionError::new);
        Map<String, Object> container = actions.stream().filter(action ->
                "REGION.W.in.keys".equals(action.get("symbol")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Collections.singletonList("keyId"),
                base.get("fieldPath"));
        assertEquals("example.Key[]", container.get("javaType"));
        assertEquals("example.KeyBase", base.get("accessOwnerClass"));
        assertEquals("FIELD_ACCESS", base.get("bindingMode"));
        assertEquals(Collections.singletonList("allKeys"),
                container.get("fieldPath"));
        @SuppressWarnings("unchecked")
        Map<String, Object> slice = (Map<String, Object>) upstream.get(
                "requestedOutputSlice");
        assertEquals(1, ((List<?>) slice.get(
                "containerElementFieldBindings")).size());
    }

    @Test
    public void malformedContainerMaterializationSiteFailsOutputClosed()
            throws Exception {
        RuntimeRegionPlanner.Result result = containerBindingRuntimeResult(
                true);
        @SuppressWarnings("unchecked")
        Map<String, Object> upstream = result.activations.get(2);
        assertEquals(Boolean.FALSE,
                upstream.get("requestedOutputSliceComplete"));
        assertEquals(Boolean.FALSE, upstream.get("symbolicReady"));
        assertFalse(upstream.containsKey("containerElementFieldBindings"));
        @SuppressWarnings("unchecked")
        Map<String, Object> slice = (Map<String, Object>) upstream.get(
                "requestedOutputSlice");
        assertEquals(Boolean.FALSE, slice.get("runtimeRefinementComplete"));
        assertTrue(((List<?>) slice.get("containerElementFieldBindings"))
                .isEmpty());
    }

    @Test
    public void canonicalizesPromotedNestedArrayPortToExactConsumedLeaf()
            throws Exception {
        RuntimeRegionPlanner.Result result = arrayInputAliasRuntimeResult(
                false);
        assertEquals(3, result.activations.size());
        @SuppressWarnings("unchecked")
        Map<String, Object> upstream = result.activations.get(2);
        assertEquals(Boolean.TRUE,
                upstream.get("requestedOutputSliceComplete"));
        assertEquals(Boolean.TRUE, upstream.get("symbolicReady"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> actions =
                (List<Map<String, Object>>) upstream.get("symbolize");
        assertEquals(2, actions.size());
        Map<String, Object> exactAction = actions.stream().filter(action ->
                "REGION.W.in.exact".equals(action.get("symbol")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("example.Key[]", exactAction.get("javaType"));
        assertEquals(Boolean.TRUE,
                exactAction.get("consumedFieldBindingComplete"));
        assertFalse(String.valueOf(actions).contains(
                "REGION.W.in.promoted"));

        @SuppressWarnings("unchecked")
        Map<String, Object> slice = (Map<String, Object>) upstream.get(
                "requestedOutputSlice");
        assertEquals(Arrays.asList("REGION.W.in.exact", "REGION.W.in.key"),
                slice.get("inputPorts"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> aliases =
                (List<Map<String, Object>>) slice.get(
                        "inputAliasCanonicalizations");
        assertEquals(1, aliases.size());
        assertEquals("REGION.W.in.promoted",
                aliases.get(0).get("aliasInputPort"));
        assertEquals("REGION.W.in.exact",
                aliases.get(0).get("canonicalInputPort"));
        assertEquals(800,
                aliases.get(0).get("intermediateOwnerObjectId"));
        assertEquals(800,
                aliases.get(0).get("canonicalLeafReceiverObjectId"));
        assertEquals(2, aliases.get(0).get("aliasBindingCount"));
        assertEquals(Arrays.asList("OUTPUT_SLICE_FRONTIER_PROMOTION",
                        "UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN"),
                aliases.get(0).get("aliasBindingAuthorities"));
        assertEquals(Boolean.TRUE, aliases.get(0).get("complete"));
        assertEquals(Boolean.TRUE,
                slice.get("inputAliasCanonicalizationComplete"));
        assertTrue(((List<?>) slice.get(
                "inputAliasCanonicalizationIssues")).isEmpty());

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        List<Map<String, Object>> exactBindings = new ArrayList<>();
        for (Map<String, Object> binding : bindings) {
            if ("REGION.W.in.exact".equals(binding.get("inputPort"))) {
                exactBindings.add(binding);
            }
        }
        assertEquals(1, exactBindings.size());
        assertEquals("EXACT_CELL_IDENTITY",
                exactBindings.get(0).get("bindingAuthority"));
        assertFalse(exactBindings.get(0).containsKey(
                "aliasSourceInputPort"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> containers =
                (List<Map<String, Object>>) upstream.get(
                        "containerElementFieldBindings");
        assertEquals(1, containers.size());
        assertEquals("REGION.W.in.exact",
                containers.get(0).get("containerInputPort"));
        assertEquals("REGION.W.in.promoted",
                containers.get(0).get("containerInputAliasSourcePort"));
        assertEquals("EXACT_RUNTIME_FIELD_CHAIN_TO_CANONICAL_LEAF_INPUT_V1",
                containers.get(0).get("containerInputAliasAuthority"));
    }

    @Test
    public void ambiguousExactArrayAliasCanonicalPortFailsOutputClosed()
            throws Exception {
        RuntimeRegionPlanner.Result result = arrayInputAliasRuntimeResult(
                true);
        assertEquals(3, result.activations.size());
        @SuppressWarnings("unchecked")
        Map<String, Object> upstream = result.activations.get(2);
        assertEquals(Boolean.FALSE,
                upstream.get("requestedOutputSliceComplete"));
        assertEquals(Boolean.FALSE, upstream.get("symbolicReady"));
        @SuppressWarnings("unchecked")
        Map<String, Object> slice = (Map<String, Object>) upstream.get(
                "requestedOutputSlice");
        assertEquals(Boolean.FALSE,
                slice.get("inputAliasCanonicalizationComplete"));
        assertTrue(String.valueOf(slice.get(
                "inputAliasCanonicalizationIssues")).contains(
                "EXACT_ARRAY_ALIAS_CANONICAL_PORT_NOT_UNIQUE:2"));
        assertEquals(Boolean.FALSE, slice.get("runtimeRefinementComplete"));
    }

    @Test
    public void liftsSelectedArrayElementDemandToMapOutputProjectionCatalog() {
        RuntimeRegionPlanner.Result result =
                mapValueProjectionActivationResult(true);
        assertEquals(1, RuntimeRegionPlanner
                .refineMapValueElementProjectionActivationsForTests(result));

        Map<String, Object> producer = result.activations.get(0);
        assertEquals(Boolean.TRUE, producer.get("symbolicReady"));
        assertEquals(Boolean.TRUE, producer.get("boundaryReady"));
        assertEquals(Boolean.TRUE,
                producer.get("mapValueElementProjectionCaptureReady"));
        assertEquals(Boolean.TRUE,
                producer.get("recursiveElementProjectionComposable"));
        assertFalse(producer.containsKey(
                "recursiveElementProjectionCompositionGap"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> declarations =
                (List<Map<String, Object>>) producer.get(
                        "mapValueElementFieldProjections");
        assertEquals(1, declarations.size());
        Map<String, Object> declaration = declarations.get(0);
        assertEquals("MAP_VALUE_TO_OUTPUT_ARRAY_ELEMENT_FIELD",
                declaration.get("kind"));
        assertEquals("REGION.P.in.map",
                declaration.get("mapInputPort"));
        assertEquals("REGION.P.out.keys",
                declaration.get("outputPort"));
        assertEquals("REGION.D.in.keys",
                declaration.get("downstreamInputPort"));
        assertEquals(Collections.singletonList("expiryDate"),
                declaration.get("fieldPath"));
        assertEquals("ROOT_RETURN_PROJECTED_FIELD",
                declaration.get("outputValidationMode"));
        assertEquals(Boolean.TRUE,
                declaration.get("recursiveElementProjectionComposable"));
        @SuppressWarnings("unchecked")
        List<String> proof = (List<String>) declaration.get(
                "projectionProofCausalEdgeIds");
        assertEquals(Arrays.asList("GOOD.FIELD", "VIEW", "SNAP", "OUT"),
                proof);
        assertFalse("control-flow interference must not become proof",
                proof.contains("BAD.GUARD"));
    }

    @Test
    public void controlOrOpaqueEdgesCannotProveMapOutputProjection() {
        RuntimeRegionPlanner.Result result =
                mapValueProjectionActivationResult(false);
        assertEquals(0, RuntimeRegionPlanner
                .refineMapValueElementProjectionActivationsForTests(result));
        Map<String, Object> producer = result.activations.get(0);
        assertEquals(Boolean.FALSE,
                producer.get("mapValueElementProjectionCaptureReady"));
        assertEquals(Boolean.FALSE, producer.get("symbolicReady"));
        assertTrue(String.valueOf(producer.get(
                "mapValueElementProjectionIssues")).contains(
                "MAP_VIEW_RECEIVER_HAS_NO_EXACT_INPUT_PORT"));
        assertTrue(((List<?>) producer.get(
                "mapValueElementFieldProjections")).isEmpty());
    }

    private static RuntimeRegionPlanner.Result
    mapValueProjectionActivationResult(boolean includeExactFieldRead) {
        String mapField = "<example.Producer: java.util.Map elements>";
        String outputField = "<example.Payload: example.Element[] elements>";
        String elementField = "<example.Element: long expiryDate>";
        String mapLocal = "<example.Producer: example.Payload export()>::$r1";
        String viewLocal = "<example.Producer: example.Payload export()>::$r2";
        String arrayLocal = "<example.Producer: example.Payload export()>::$r3";

        List<Map<String, Object>> causal = new ArrayList<>();
        if (includeExactFieldRead) {
            causal.add(row("edgeId", "GOOD.FIELD", "fromCell", mapField,
                    "toCell", mapLocal, "transferKind", "HEAP_READ",
                    "kind", "field_read"));
        }
        causal.add(row("edgeId", "BAD.GUARD", "fromCell", mapField,
                "toCell", mapLocal, "transferKind", "GUARD",
                "kind", "path_guard_dependency"));
        causal.add(projectionEdge("VIEW", mapLocal, viewLocal,
                "MAP_VALUES_VIEW", false));
        causal.add(projectionEdge("SNAP", viewLocal, arrayLocal,
                "COLLECTION_TO_ARRAY", true));
        causal.add(row("edgeId", "OUT", "fromCell", arrayLocal,
                "toCell", outputField, "transferKind", "HEAP_WRITE",
                "kind", "field_write"));

        Map<String, Object> producerSlice = row(
                "outputPort", "REGION.P.out.keys",
                "outputCell", outputField,
                "inputBindings", Collections.singletonList(row(
                        "dependencyCell", mapField,
                        "inputPort", "REGION.P.in.map")),
                "causalEdges", causal);
        Map<String, Object> producer = row(
                "activationId", "ACT.P.OUT",
                "regionId", "REGION.P",
                "regionInstanceId", "REGION.P@test#call1",
                "captureGoal", row("kind", "OUTPUT_CLOSURE"),
                "requestedOutputSliceComplete", true,
                "requestedOutputCaptureRequired", false,
                "requestedOutput", row("portId", "REGION.P.out.keys",
                        "cell", outputField),
                "requestedOutputSlice", producerSlice,
                "edgeBindings", Collections.singletonList(row(
                        "edgeId", "EDGE.PD",
                        "toRegionInstance", "REGION.D@test#call2",
                        "toInputPort", "REGION.D.in.keys")),
                "symbolicReady", true,
                "boundaryReady", true);

        Map<String, Object> downstreamBinding = row(
                "schemaVersion", 1,
                "kind", "ARRAY_ELEMENT_FIELD",
                "bindingId", "BIND.DOWNSTREAM.EXPIRY",
                "baseInputSymbol", "REGION.D.in.expiry",
                "containerInputPort", "REGION.D.in.keys",
                "declaredFieldSignature", elementField,
                "declaredFieldOwnerClass", "example.Element",
                "declaredFieldType", "long",
                "declaredFieldName", "expiryDate",
                "fieldPath", Collections.singletonList("expiryDate"),
                "complete", true);
        Map<String, Object> downstream = row(
                "activationId", "ACT.D.OUT",
                "regionId", "REGION.D",
                "regionInstanceId", "REGION.D@test#call2",
                "captureGoal", row("kind", "OUTPUT_CLOSURE"),
                "requestedOutputSliceComplete", true,
                "requestedOutputSlice", row(
                        "containerElementFieldBindings",
                        Collections.singletonList(downstreamBinding)));
        RuntimeRegionPlanner.Result result =
                new RuntimeRegionPlanner.Result();
        result.activations.add(producer);
        result.activations.add(downstream);
        return result;
    }

    private static Map<String, Object> projectionEdge(
            String id, String from, String to, String operation,
            boolean snapshot) {
        return row("edgeId", id, "fromCell", from, "toCell", to,
                "siteId", "<example.Producer: example.Payload export()>#u"
                        + (snapshot ? "3" : "2"),
                "transferKind", "MODEL_TRANSFORM",
                "kind", snapshot ? "container_snapshot_projection"
                        : "container_backed_view_projection",
                "containerProjectionContractVersion", 1,
                "containerProjectionOperation", operation,
                "containerProjectionAuthority",
                "JAVA_COLLECTION_API_EXACT_SIGNATURE_WHITELIST_V1",
                "receiverValueDependencyComplete", true,
                "elementIdentityPreserving", true,
                "backedView", !snapshot,
                "snapshot", snapshot);
    }

    private static Map<String, Object> row(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index + 1 < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
        return result;
    }

    private static RuntimeRegionPlanner.Result containerBindingRuntimeResult(
            boolean mismatchedSite) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String writer = "<example.Secret: void addKeys(example.Keys)>";
            String reader = "<example.Reader: void consume()>";
            String state = "<example.Secret: java.util.Map allKeys>";
            String key = "<example.KeyBase: int keyId>";
            String keys = "<example.Keys: example.Key[] allKeys>";
            String fieldSite = writer + (mismatchedSite ? "#u99" : "#u14");
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + writer + "\","
                    + "\"anchorMethod\":\"" + writer + "\","
                    + "\"methods\":[\"" + writer + "\"],"
                    + "\"symbolicInputs\":["
                    + "{\"portId\":\"REGION.W.in.key\",\"cell\":\""
                    + key + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"},"
                    + "{\"portId\":\"REGION.W.in.keys\",\"cell\":\""
                    + keys + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"inputPorts\":[\"REGION.W.in.key\","
                    + "\"REGION.W.in.keys\"],"
                    + "\"inputBindings\":["
                    + sliceBinding(key, "REGION.W.in.key", writer) + ","
                    + sliceBinding(keys, "REGION.W.in.keys", writer) + "],"
                    + "\"methods\":[\"" + writer + "\"],"
                    + "\"sites\":[\"" + writer + "#u11\",\""
                    + writer + "#u13\",\"" + writer + "#u14\"],"
                    + "\"causalEdgeIds\":[\"A\",\"C\",\"G\",\"P\"],"
                    + "\"causalEdges\":["
                    + causalReference("A", writer, writer + "#u13") + ","
                    + causalReference("C", writer, writer + "#u11") + ","
                    + causalReference("G", writer, writer + "#u14") + ","
                    + causalReference("P", writer, writer + "#u14") + "],"
                    + "\"containerElementFieldBindings\":[{"
                    + "\"schemaVersion\":1,"
                    + "\"kind\":\"ARRAY_ELEMENT_FIELD\","
                    + "\"bindingId\":\"BIND.ARRAY.0\","
                    + "\"baseInputSymbol\":\"REGION.W.in.key\","
                    + "\"containerInputPort\":\"REGION.W.in.keys\","
                    + "\"containerInputCell\":\"" + keys + "\","
                    + "\"selectorAuthority\":\"EXACT_ARRAY_INDEX\","
                    + "\"elementIndex\":0,\"elementOccurrence\":1,"
                    + "\"fieldPath\":[\"keyId\"],"
                    + "\"declaredFieldSignature\":\"" + key + "\","
                    + "\"declaredFieldOwnerClass\":\"example.KeyBase\","
                    + "\"declaredFieldType\":\"int\","
                    + "\"declaredFieldName\":\"keyId\","
                    + "\"method\":\"" + writer + "\","
                    + "\"fieldMaterializationSiteId\":\"" + fieldSite
                    + "\",\"arrayLoadSiteId\":\"" + writer + "#u13\","
                    + "\"proofCausalEdgeIds\":[\"A\",\"C\",\"G\",\"P\"],"
                    + "\"proofAuthority\":\"STATIC_EXACT_CONTAINER_ARRAY_"
                    + "ACCESSOR_DECLARED_FIELD_FOUR_EDGE_JOIN_V1\","
                    + "\"complete\":true}],"
                    + "\"complete\":true,\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":\"REGION.R.in.0\","
                    + "\"cell\":\"" + state + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.STATE\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    writer, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent keyRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_READ", writer, 11, key, 501, 0, "7");
            RuntimeRegionPlanner.FieldAccessEvent keysRead =
                    exactFieldRead(3, writer, 11, 11, keys, 502, 600);
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(4,
                            "FIELD_WRITE", writer, 11, state, 42, 88, "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 42, 88, "");
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(keyRead, keysRead, write, read));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result arrayInputAliasRuntimeResult(
            boolean ambiguousCanonicalPort) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String writer = "<example.Handler: void process()>";
            String reader = "<example.Reader: void consume()>";
            String carrier = "<example.Command: example.Keys keys>";
            String promoted = carrier + "#field:allKeys";
            String exact = "<example.Keys: example.Key[] allKeys>";
            String key = "<example.Key: int keyId>";
            String state = "<example.Handler: java.util.Map state>";
            String extraPort = ambiguousCanonicalPort
                    ? ",\"REGION.W.in.exact.duplicate\"" : "";
            String extraInput = ambiguousCanonicalPort
                    ? ",{\"portId\":\"REGION.W.in.exact.duplicate\","
                    + "\"cell\":\"" + exact + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}" : "";
            String extraBinding = ambiguousCanonicalPort
                    ? "," + sliceBinding(exact,
                    "REGION.W.in.exact.duplicate", writer) : "";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + writer + "\","
                    + "\"anchorMethod\":\"" + writer + "\","
                    + "\"methods\":[\"" + writer + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.W.in.key\",\"cell\":\"" + key
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"},{\"portId\":"
                    + "\"REGION.W.in.promoted\",\"cell\":\""
                    + promoted + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"},{\"portId\":"
                    + "\"REGION.W.in.exact\",\"cell\":\"" + exact
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}" + extraInput + "],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{\"outputPort\":"
                    + "\"REGION.W.out.0\",\"outputCell\":\"" + state
                    + "\",\"inputPorts\":[\"REGION.W.in.key\","
                    + "\"REGION.W.in.promoted\",\"REGION.W.in.exact\""
                    + extraPort + "],\"inputBindings\":["
                    + sliceBinding(key, "REGION.W.in.key", writer) + ",{"
                    + "\"dependencyCell\":\""
                    + promoted + "\",\"inputPort\":"
                    + "\"REGION.W.in.promoted\",\"bindingAuthority\":"
                    + "\"OUTPUT_SLICE_FRONTIER_PROMOTION\","
                    + "\"dependencyMethods\":[\"" + writer + "\"]},{"
                    + "\"dependencyCell\":\"" + promoted + "\","
                    + "\"inputPort\":\"REGION.W.in.promoted\","
                    + "\"bindingAuthority\":"
                    + "\"UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN\","
                    + "\"dependencyMethods\":[\"" + writer + "\"]},"
                    + sliceBinding(exact, "REGION.W.in.exact", writer)
                    + extraBinding + "],\"methods\":[\"" + writer
                    + "\"],\"sites\":[\"" + writer + "#u5\",\""
                    + writer + "#u6\",\"" + writer + "#u7\",\""
                    + writer + "#u8\",\"" + writer + "#u9\"],"
                    + "\"causalEdgeIds\":[\"A\",\"C\",\"G\",\"P\"],"
                    + "\"causalEdges\":["
                    + causalReference("A", writer, writer + "#u5") + ","
                    + causalReference("C", writer, writer + "#u6") + ","
                    + causalReference("G", writer, writer + "#u8") + ","
                    + causalReference("P", writer, writer + "#u9") + "],"
                    + "\"containerElementFieldBindings\":[{"
                    + "\"schemaVersion\":1,"
                    + "\"kind\":\"ARRAY_ELEMENT_FIELD\","
                    + "\"bindingId\":\"BIND.ALIAS.CONTAINER\","
                    + "\"baseInputSymbol\":\"REGION.W.in.key\","
                    + "\"containerInputPort\":\"REGION.W.in.promoted\","
                    + "\"containerInputCell\":\"" + exact + "\","
                    + "\"selectorAuthority\":\"EXACT_ARRAY_INDEX\","
                    + "\"elementIndex\":0,\"elementOccurrence\":1,"
                    + "\"fieldPath\":[\"keyId\"],"
                    + "\"declaredFieldSignature\":\"" + key + "\","
                    + "\"declaredFieldOwnerClass\":\"example.Key\","
                    + "\"declaredFieldType\":\"int\","
                    + "\"declaredFieldName\":\"keyId\","
                    + "\"method\":\"" + writer + "\","
                    + "\"fieldMaterializationSiteId\":\"" + writer
                    + "#u8\",\"arrayLoadSiteId\":\"" + writer
                    + "#u7\",\"proofCausalEdgeIds\":[\"A\",\"C\","
                    + "\"G\",\"P\"],\"proofAuthority\":"
                    + "\"STATIC_EXACT_CONTAINER_ARRAY_ACCESSOR_DECLARED_"
                    + "FIELD_FOUR_EDGE_JOIN_V1\",\"complete\":true}],"
                    + "\"complete\":true,\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + state
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.STATE\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    writer, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent carrierRead =
                    exactFieldRead(2, writer, 11, 5, carrier, 700, 800);
            RuntimeRegionPlanner.FieldAccessEvent exactArrayRead =
                    exactFieldRead(3, writer, 11, 6, exact, 800, 900);
            RuntimeRegionPlanner.FieldAccessEvent keyRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(3,
                            "FIELD_READ", writer, 11, key, 901, 0, "7");
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(4,
                            "FIELD_WRITE", writer, 11, state, 42, 88, "");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 42, 88, "");
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                    Arrays.asList(carrierRead, exactArrayRead, keyRead,
                            write, read));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result mutationDischargeGateResult(
            String unresolvedOwner, String retainedKind,
            boolean contractComplete) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String alternative = "<example.State: void initialize()>";
            String updater = "<example.State: void addKeys()>";
            String reader = "<example.Reader: void consume()>";
            String state = "<example.State: java.util.Map allKeys>";
            String missing = "<example.Seed: int alternative>";
            String alternativeSite = alternative + "#u3";
            String updaterSite = updater + "#u7";
            String unresolvedMethod = "OBSERVED".equals(unresolvedOwner)
                    ? updater : alternative;
            String diagnostic = missing
                    + " [output slice input has no region port]";
            String contractIssues = contractComplete ? "[]"
                    : "[\"STATIC_TRANSFORMER_LEDGER_GAP\"]";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + alternative + "\","
                    + "\"anchorMethod\":\"" + updater + "\","
                    + "\"methods\":[\"" + alternative + "\",\""
                    + updater + "\"],\"symbolicInputs\":[{"
                    + "\"portId\":\"REGION.W.in.0\",\"cell\":\""
                    + state + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + state
                    + "\",\"kind\":\"HEAP_STATE\"}],"
                    + "\"outputSlices\":[{"
                    + "\"outputPort\":\"REGION.W.out.0\","
                    + "\"outputCell\":\"" + state + "\","
                    + "\"inputPorts\":[\"REGION.W.in.0\"],"
                    + "\"inputBindings\":["
                    + sliceBinding(state, "REGION.W.in.0", updater) + "],"
                    + "\"methods\":[\"" + alternative + "\",\""
                    + updater + "\"],\"sites\":[\"" + alternativeSite
                    + "\",\"" + updaterSite + "\"],"
                    + "\"causalEdgeIds\":[\"DF.A\",\"DF.U\"],"
                    + "\"causalEdges\":["
                    + causalReference("DF.A", alternative,
                    alternativeSite) + ","
                    + "{\"edgeId\":\"DF.U\",\"method\":\""
                    + updater + "\",\"siteId\":\"" + updaterSite
                    + "\",\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"" + retainedKind + "\"}],"
                    + "\"structuralComplete\":true,"
                    + "\"unresolvedInputs\":[\"" + diagnostic + "\"],"
                    + "\"unresolvedInputDetails\":[{"
                    + "\"dependencyCell\":\"" + missing + "\","
                    + "\"dependencyMethods\":[\"" + unresolvedMethod
                    + "\"],\"reason\":"
                    + "\"OUTPUT_SLICE_INPUT_HAS_NO_REGION_PORT\","
                    + "\"diagnostic\":\"" + diagnostic + "\","
                    + "\"provenanceAuthority\":"
                    + "\"STATIC_EXACT_DEPENDENCY_METHOD_CONSUMER_SET_V1\"}],"
                    + "\"requestedStateTransformerContractVersion\":1,"
                    + "\"requestedStateTransformerContractApplicable\":true,"
                    + "\"requestedStateTransformerContractOutputPort\":"
                    + "\"REGION.W.out.0\","
                    + "\"requestedStateTransformerContractOutputCell\":"
                    + "\"" + state + "\","
                    + "\"requestedStateTransformerObligations\":[{"
                    + "\"siteId\":\"" + alternativeSite + "\","
                    + "\"method\":\"" + alternative + "\","
                    + "\"targetCell\":\"" + state + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"field_mutation\","
                    + "\"causalEdgeIds\":[\"DF.A\"],"
                    + "\"authority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL\"},{"
                    + "\"siteId\":\"" + updaterSite + "\","
                    + "\"method\":\"" + updater + "\","
                    + "\"targetCell\":\"" + state + "\","
                    + "\"transferKind\":\"HEAP_WRITE\","
                    + "\"kind\":\"" + retainedKind + "\","
                    + "\"causalEdgeIds\":[\"DF.U\"],"
                    + "\"authority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL\"}],"
                    + "\"requestedStateTransformerObligationCount\":2,"
                    + "\"requestedStateTransformerContractIssues\":"
                    + contractIssues + ","
                    + "\"requestedStateTransformerContractComplete\":"
                    + contractComplete + ","
                    + "\"requestedStateTransformerContractAuthority\":"
                    + "\"STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1\","
                    + "\"captureBindingsRequired\":true,"
                    + "\"captureBindingsComplete\":false,"
                    + "\"captureBindings\":[],"
                    + "\"captureBindingIssues\":["
                    + "\"REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_"
                    + "ASSIGNMENT_RHS:" + alternativeSite + "\","
                    + "\"REQUESTED_TRANSFORMER_HAS_NO_EXACT_FIELD_"
                    + "ASSIGNMENT_RHS:" + updaterSite + "\"],"
                    + "\"complete\":false,\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + state
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.STATE\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + state + "\","
                    + "\"toPort\":\"" + state + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writeRoot = methodContext(1,
                    updater, 11, "PROCESS", "writer", 101L);
            RuntimeRegionPlanner.MethodEvent readRoot = methodContext(10,
                    reader, 22, "PROCESS", "reader", 202L);
            RuntimeRegionPlanner.FieldAccessEvent stateRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(2,
                            "FIELD_READ", updater, 11, state, 42, 88, "");
            RuntimeRegionPlanner.RuntimeEvent mutation =
                    new RuntimeRegionPlanner.RuntimeEvent(3,
                            "CALL_SITE_ENTER", updater, 11, 30, 0,
                            updaterSite,
                            "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                            -1, "java.util.Map", 88, "", false, false);
            RuntimeRegionPlanner.RuntimeEvent mutationReturn =
                    new RuntimeRegionPlanner.RuntimeEvent(4,
                            "CALL_SITE_RETURN", updater, 11, 30, 0,
                            updaterSite, -1, "", 0, "", false, false);
            RuntimeRegionPlanner.FieldAccessEvent downstreamRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(11,
                            "FIELD_READ", reader, 22, state, 42, 88, "");
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    Arrays.asList(writeRoot, readRoot),
                    Arrays.asList(mutation, mutationReturn),
                    Arrays.asList(stateRead, downstreamRead));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result containerMutationReadFromResult(
            boolean includeReturn, int readerContainerObjectId)
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String writerRoot = "<example.KeyUpdater: void loop()>";
            String addKeys = "<example.SecretManager: void addKeys()>";
            String reader = "<example.SecretManager: void retrieve()>";
            String field = "<example.SecretManager: java.util.Map allKeys>";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + writerRoot + "\","
                    + "\"anchorMethod\":\"" + addKeys + "\","
                    + "\"methods\":[\"" + writerRoot + "\",\""
                    + addKeys + "\"],\"symbolicInputs\":[],"
                    + "\"outputs\":[{\"portId\":\"REGION.W.out.0\","
                    + "\"cell\":\"" + field + "\","
                    + "\"kind\":\"HEAP_STATE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.0\",\"cell\":\"" + field + "\","
                    + "\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"field:allKeys\"}],"
                    + "\"outputs\":[],\"branchPolicies\":[],"
                    + "\"models\":[]}\n";
            Files.write(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            Files.write(edges, ("{\"edgeId\":\"E.ALL_KEYS\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\","
                    + "\"fromPort\":\"" + field + "\","
                    + "\"toPort\":\"" + field + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n").getBytes(
                    StandardCharsets.UTF_8));

            RuntimeRegionPlanner.MethodEvent writer = methodContext(1,
                    writerRoot, 1, "DATANODE", "KeyUpdater", 101L);
            RuntimeRegionPlanner.MethodEvent contained =
                    new RuntimeRegionPlanner.MethodEvent(5190, "testHandle",
                            "DATANODE", "KeyUpdater", 101L, addKeys,
                            273814159, "example.SecretManager", 2, 1, 0,
                            519000L);
            RuntimeRegionPlanner.MethodEvent read = methodContext(14000,
                    reader, 3, "DATANODE", "DataXceiver", 202L);
            List<RuntimeRegionPlanner.RuntimeEvent> runtime =
                    new ArrayList<>();
            for (int index = 0; index < 513; index++) {
                runtime.add(new RuntimeRegionPlanner.RuntimeEvent(index + 2L,
                        "BRANCH", writerRoot, 1, 0, 0,
                        writerRoot + "#u" + index, -1, "", 0, "",
                        true, (index & 1) == 0));
            }
            String put = "<java.util.Map: java.lang.Object put("
                    + "java.lang.Object,java.lang.Object)>";
            runtime.add(new RuntimeRegionPlanner.RuntimeEvent(5199,
                    "CALL_SITE_ENTER", addKeys, 2, 5199, 0,
                    addKeys + "#u22", put, -1, "java.util.HashMap",
                    128017166, "", false, false));
            runtime.add(new RuntimeRegionPlanner.RuntimeEvent(5207,
                    "CALL_SITE_ENTER", addKeys, 2, 5207, 0,
                    addKeys + "#u23", put, -1, "java.util.HashMap",
                    128017166, "", false, false));
            if (includeReturn) {
                runtime.add(new RuntimeRegionPlanner.RuntimeEvent(5201,
                        "CALL_SITE_RETURN", addKeys, 2, 5199, 0,
                        addKeys + "#u22", -1, "", 0, "", false,
                        false));
                runtime.add(new RuntimeRegionPlanner.RuntimeEvent(5211,
                        "CALL_SITE_RETURN", addKeys, 2, 5207, 0,
                        addKeys + "#u23", -1, "", 0, "", false,
                        false));
            }
            RuntimeRegionPlanner.FieldAccessEvent writerFieldRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(5197,
                            "FIELD_READ", addKeys, 2, field, 273814159,
                            128017166, "");
            RuntimeRegionPlanner.FieldAccessEvent readerFieldRead =
                    new RuntimeRegionPlanner.FieldAccessEvent(14261,
                            "FIELD_READ", reader, 3, field, 273814159,
                            readerContainerObjectId, "");
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    Arrays.asList(writer, contained, read), runtime,
                    Arrays.asList(writerFieldRead, readerFieldRead));
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.Result
    methodReturnCaptureRefinementResult(int normalExitCount)
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            String worker = "<example.ProducerThread: void run()>";
            String method =
                    "<example.Producer: int compute(java.lang.Boolean)>";
            String publisher = "<example.RpcBus: void publish(int)>";
            String reader = "<example.Consumer: void consume()>";
            String rawField = "<example.RpcBus: int value>";
            String outputPort = "REGION.W.out.rpc";
            String outputCell = method + ".return";
            String returnExpression = "$i0";
            String returnCell = method + "::$i0";
            String returnSite = method + "#u8";
            String writerRegion = "{\"regionId\":\"REGION.W\","
                    + "\"rootMethod\":\"" + worker + "\","
                    + "\"anchorMethod\":\"" + method + "\","
                    + "\"methods\":[\"" + worker + "\",\""
                    + method + "\",\"" + publisher
                    + "\"],\"symbolicInputs\":[],"
                    + "\"outputs\":[{\"portId\":\"" + outputPort
                    + "\",\"cell\":\"" + outputCell + "\","
                    + "\"kind\":\"RETURN_VALUE\"}],"
                    + "\"outputSlices\":[{\"outputPort\":\""
                    + outputPort + "\",\"outputCell\":\""
                    + outputCell + "\",\"inputPorts\":[],"
                    + "\"inputBindings\":[],\"methods\":[\""
                    + worker + "\",\"" + method
                    + "\"],\"sites\":[\"" + returnSite
                    + "\"],\"causalEdgeIds\":[\"DF.RETURN\"],"
                    + "\"causalEdges\":[{\"edgeId\":\"DF.RETURN\","
                    + "\"method\":\"" + method + "\",\"siteId\":\""
                    + returnSite + "\",\"fromCell\":\""
                    + returnCell + "\",\"toCell\":\""
                    + outputCell + "\",\"transferKind\":"
                    + "\"VALUE_PASS\",\"kind\":\"local_def_use\"}],"
                    + "\"structuralComplete\":true,"
                    + "\"captureBindingsRequired\":true,"
                    + "\"captureBindingsComplete\":true,"
                    + "\"captureBindings\":[{\"captureKind\":"
                    + "\"METHOD_RETURN_VALUE\",\"captureBindingId\":"
                    + "\"REGION.W.out.rpc.capture.0\",\"outputPort\":\""
                    + outputPort + "\",\"outputCell\":\"" + outputCell
                    + "\",\"method\":\"" + method + "\","
                    + "\"siteId\":\"" + returnSite + "\","
                    + "\"unitIndex\":8,\"unit\":\"return $i0\","
                    + "\"returnExpression\":\"" + returnExpression
                    + "\",\"returnCell\":\"" + returnCell + "\","
                    + "\"causalEdgeId\":\"DF.RETURN\","
                    + "\"transferKind\":\"VALUE_PASS\","
                    + "\"bindingKind\":\"method_return\","
                    + "\"bindingAuthority\":"
                    + "\"STATIC_EXACT_METHOD_RETURN_VALUE\","
                    + "\"occurrence\":0,\"occurrenceAuthority\":"
                    + "\"RUNTIME_INSTANCE_REFINEMENT_REQUIRED\"}],"
                    + "\"captureBindingIssues\":[],\"complete\":true,"
                    + "\"selection\":"
                    + "\"REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE\"}],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            String readerRegion = "{\"regionId\":\"REGION.R\","
                    + "\"rootMethod\":\"" + reader + "\","
                    + "\"anchorMethod\":\"" + reader + "\","
                    + "\"methods\":[\"" + reader + "\"],"
                    + "\"symbolicInputs\":[{\"portId\":"
                    + "\"REGION.R.in.rpc\",\"cell\":\"" + rawField
                    + "\",\"sourceKind\":\"SHARED_HEAP\","
                    + "\"projection\":\"value\"}],\"outputs\":[],"
                    + "\"branchPolicies\":[],\"models\":[]}\n";
            Files.write(regions, (writerRegion + readerRegion).getBytes(
                    StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.RPC.RETURN\","
                    + "\"fromRegion\":\"REGION.W\","
                    + "\"toRegion\":\"REGION.R\",\"fromPort\":\""
                    + rawField + "\",\"fromOutputPort\":\"" + outputPort
                    + "\",\"fromOutputCell\":\"" + outputCell + "\","
                    + "\"aliasProofEdgeIds\":[\"DF.RETURN\","
                    + "\"DF.PUBLISH\"],\"aliasProofAuthority\":"
                    + "\"CONFIGURED_RPC_PRODUCER_RETURN_AND_STATIC_EXACT_"
                    + "PUBLISH_VALUE_FLOW_V1\",\"aliasProofComplete\":true,"
                    + "\"toPort\":\"" + rawField + "\","
                    + "\"kind\":\"SHARED_STATE\","
                    + "\"relation\":\"READ_FROM_CANDIDATE\","
                    + "\"requiresOrder\":true,"
                    + "\"requiresObjectIdentity\":true}\n";
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));

            List<RuntimeRegionPlanner.MethodEvent> methods =
                    new ArrayList<>();
            methods.add(methodContext(1, worker, 11, "PROCESS", "writer",
                    101L));
            List<RuntimeRegionPlanner.RuntimeEvent> runtime =
                    new ArrayList<>();
            for (int index = 0; index < normalExitCount; index++) {
                long callId = 12L + index;
                long enterSeq = 2L + 3L * index;
                methods.add(new RuntimeRegionPlanner.MethodEvent(enterSeq,
                        "testHandle", "PROCESS", "writer", 101L, method,
                        43 + index, "example.Producer", callId, 11L, 0L,
                        enterSeq * 100L));
                long exitSeq = 4L + 3L * index;
                runtime.add(new RuntimeRegionPlanner.RuntimeEvent(exitSeq,
                        "METHOD_EXIT_NORMAL", method, callId, 0L, 0L,
                        method + "#exit", "", -1, "int", 0,
                        String.valueOf(index + 1), false, false));
            }
            long publisherSeq = 3L * normalExitCount + 3L;
            long publisherCallId = 30L;
            methods.add(new RuntimeRegionPlanner.MethodEvent(publisherSeq,
                    "testHandle", "PROCESS", "writer", 101L, publisher,
                    55, "example.RpcBus", publisherCallId, 11L, 0L,
                    publisherSeq * 100L));
            long readerSeq = publisherSeq + 3L;
            methods.add(methodContext(readerSeq, reader, 22, "PROCESS",
                    "reader", 202L));
            RuntimeRegionPlanner.FieldAccessEvent write =
                    new RuntimeRegionPlanner.FieldAccessEvent(
                            publisherSeq + 1L,
                            "FIELD_WRITE", publisher, 11, rawField,
                            77, 88, "1");
            RuntimeRegionPlanner.FieldAccessEvent read =
                    new RuntimeRegionPlanner.FieldAccessEvent(readerSeq + 1L,
                            "FIELD_READ", reader, 22, rawField,
                            77, 88, "1");
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    methods, runtime, Arrays.asList(write, read));
        } finally {
            folder.delete();
        }
    }

    private static Map<String, Object> requestedOutputActivation(
            RuntimeRegionPlanner.Result result) {
        for (Map<String, Object> activation : result.activations) {
            if (activation.containsKey("requestedOutputSlice")) {
                return activation;
            }
        }
        throw new AssertionError("missing requested-output activation");
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> requestedOutputSlice(
            RuntimeRegionPlanner.Result result) {
        return (Map<String, Object>) requestedOutputActivation(result).get(
                "requestedOutputSlice");
    }

    private static String carrierBinding(String dependencyCell) {
        return "{\"dependencyCell\":\"" + dependencyCell + "\","
                + "\"inputPort\":\"REGION.W.in.0\","
                + "\"bindingAuthority\":"
                + "\"UNIQUE_ROOT_ARGUMENT_CARRIER\"}";
    }

    private static String sliceBinding(String dependencyCell,
                                       String inputPort, String method) {
        return "{\"dependencyCell\":\"" + dependencyCell + "\","
                + "\"inputPort\":\"" + inputPort + "\","
                + "\"bindingAuthority\":\"EXACT_CELL_IDENTITY\","
                + "\"dependencyMethods\":[\"" + method + "\"]}";
    }

    private static String causalReference(String edgeId, String method,
                                          String siteId) {
        return "{\"edgeId\":\"" + edgeId + "\",\"method\":\""
                + method + "\",\"siteId\":\"" + siteId + "\","
                + "\"transferKind\":\"HEAP_WRITE\","
                + "\"kind\":\"field_mutation\"}";
    }

    private static String accessorFieldRegion(String field, String getter,
                                              String site) {
        return "{\"regionId\":\"REGION.0\",\"rootMethod\":\""
                + HANDLE + "\",\"anchorMethod\":\"" + HANDLE
                + "\",\"methods\":[\"" + HANDLE + "\",\"" + getter
                + "\"],\"symbolicInputs\":[{\"portId\":"
                + "\"REGION.0.in.0\",\"cell\":\"" + field
                + "\",\"sourceKind\":\"SHARED_HEAP\","
                + "\"projection\":\"value\","
                + "\"bindingMode\":\"FIELD_ACCESS\","
                + "\"accessFieldSignature\":\"" + field + "\","
                + "\"accessOwnerClass\":\"example.Command\","
                + "\"accessFieldType\":\"int\","
                + "\"accessField\":\"action\","
                + "\"accessorCallerMethod\":\"" + HANDLE + "\","
                + "\"accessorCallSiteId\":\"" + site + "\","
                + "\"accessorCallUnitIndex\":11,"
                + "\"accessorDeclaredCallee\":\"" + getter + "\","
                + "\"accessorImplementationMethod\":\"" + getter
                + "\",\"accessorImplementationAuthority\":"
                + "\"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY\","
                + "\"accessorCallSiteAuthority\":"
                + "\"STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                + "ACCESSOR_CALLSITE_V1\"}],\"outputs\":[],"
                + "\"branchPolicies\":[],\"models\":[]}\n";
    }

    private static RuntimeRegionPlanner.Result planSaslUsernameEdge(
            List<RuntimeRegionPlanner.MethodEvent> methods,
            List<RuntimeRegionPlanner.RuntimeEvent> events) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path regions = folder.getRoot().toPath().resolve(
                    "symbolic_regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve(
                    "symbolic_region_edges.jsonl");
            Files.write(regions, (region("REGION.C", SASL_CLIENT)
                    + region("REGION.S", SASL_SERVER)).getBytes(
                    StandardCharsets.UTF_8));
            String edge = "{\"edgeId\":\"E.SASL.RUNTIME\","
                    + "\"fromRegion\":\"REGION.C\","
                    + "\"toRegion\":\"REGION.S\","
                    + "\"fromPort\":\"" + SASL_CLIENT
                    + ".param3:java.lang.String\","
                    + "\"toPort\":\"" + SASL_SERVER + "::$r4\","
                    + "\"kind\":\"SASL_TRANSFER\","
                    + "\"candidateRelation\":\"EQUALITY\","
                    + "\"mappingKind\":\"hdfs_sasl_username\","
                    + "\"mappingAuthority\":"
                    + "\"STATIC_HDFS_SASL_CONTRACT\","
                    + "\"payloadEqualityCheckRequired\":true,"
                    + "\"requiresOrder\":true,"
                    + "\"siteId\":\"synthetic:hdfs_sasl_username\"}\n";
            Files.write(edges, edge.getBytes(StandardCharsets.UTF_8));
            return RuntimeRegionPlanner.plan(regions.toFile(), edges.toFile(),
                    methods, events, Collections.emptyList());
        } finally {
            folder.delete();
        }
    }

    private static RuntimeRegionPlanner.RuntimeEvent saslArgument(
            long seq, long callId, String fingerprint) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, "METHOD_ARGUMENT",
                SASL_CLIENT, callId, 0, 0, SASL_CLIENT + "#entry", "",
                3, "java.lang.String", 101, "", false, false,
                fingerprint, true, 1, "COMPLETE");
    }

    private static RuntimeRegionPlanner.RuntimeEvent methodArgument(
            long seq, String method, long callId, int argumentIndex,
            String runtimeType) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, "METHOD_ARGUMENT",
                method, callId, 0, 0, method + "#entry", "",
                argumentIndex, runtimeType, (int) (seq + 100), "", false,
                false, "", false, 0, "TEST_NO_FINGERPRINT");
    }

    private static RuntimeRegionPlanner.RuntimeEvent saslCallbackReturn(
            long seq, long callId, String fingerprint) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, "CALL_SITE_RETURN",
                SASL_SERVER, callId, 9, 0, SASL_SERVER + "#u4",
                NAME_CALLBACK_DEFAULT, -1, "java.lang.String", 102, "",
                false, false, fingerprint, true, 1, "COMPLETE");
    }

    private static RuntimeRegionPlanner.MethodEvent method(long seq, String method,
                                                            long callId,
                                                            long parentCallId,
                                                            long parentSiteId) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "testHandle", "DATANODE",
                "DataXceiver-1", 27L, method, 42, "example.Handler", callId,
                parentCallId, parentSiteId, seq * 100L);
    }

    private static RuntimeRegionPlanner.MethodEvent methodWithReceiver(
            long seq, String method, long callId, int receiverObjectId) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "testHandle",
                "DATANODE", "DataXceiver-1", 27L, method,
                receiverObjectId, "example.Actor", callId, 0, 0,
                seq * 100L);
    }

    private static RuntimeRegionPlanner.MethodEvent rootContextMethod(
            long seq, String method, long callId, String threadName,
            String receiverRuntimeClass, long tid) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "testHandle",
                "WORKER", threadName, tid, method, (int) (100 + callId),
                receiverRuntimeClass, callId, 0, 0, seq * 100L);
    }

    private static RuntimeRegionPlanner.MethodEvent methodContext(
            long seq, String method, long callId, String process,
            String threadName, long tid) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "testHandle", process,
                threadName, tid, method, 42, "example.State", callId,
                0, 0, seq * 100L);
    }

    private static String region(String id, String method) {
        return "{\"regionId\":\"" + id + "\",\"rootMethod\":\""
                + method + "\",\"anchorMethod\":\"" + method
                + "\",\"methods\":[\"" + method
                + "\"],\"symbolicInputs\":[],\"outputs\":[],"
                + "\"branchPolicies\":[],\"models\":[]}\n";
    }
}
