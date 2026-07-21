package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class SymbolicRegionPlannerTest {
    private static final String HANDLE =
            "<example.Handler: void handle(javax.security.auth.callback.Callback[])>";
    private static final String IDENTIFIER =
            "<example.Handler: example.Token getIdentifier(java.lang.String)>";
    private static final String PASSWORD =
            "<example.Handler: char[] getPassword(example.Token)>";
    private static final String RETRIEVE =
            "<example.SecretManager: byte[] retrievePassword(example.Token)>";

    @Test
    public void transportNamedDeclaredFieldIsStillSharedHeap()
            throws Exception {
        java.lang.reflect.Method sourceKind = SymbolicRegionPlanner.class
                .getDeclaredMethod("sourceKind", String.class, String.class);
        sourceKind.setAccessible(true);
        String field = "<example.RpcBus: int a>";
        assertEquals("SHARED_HEAP", sourceKind.invoke(null, field, HANDLE));
        assertEquals("OPAQUE_CALL", sourceKind.invoke(null,
                "<example.RpcBus: int getA()>.return", HANDLE));
    }

    @Test
    public void legacyStaticModelClassificationStillRequiresARegion() {
        String transform =
                "<example.FormatBridge: example.Value decode(byte[])>";
        Map<String, Object> transformPlan = plan(transform,
                Collections.singletonList(transform + ".param0:bytes"),
                Collections.singletonList(transform + ".return"));
        transformPlan.put("classification", "MODEL_SUMMARY");
        transformPlan.put("requiredModels",
                Collections.singletonList("legacy_codec_summary"));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                Collections.singletonList(edge(transform, "SEED", "seed",
                        transform + ".return", transform + "#observed", 1)),
                Collections.singletonList(transformPlan));

        assertEquals(1, result.regions.size());
        assertEquals(0, result.modelSummaries.size());
        assertEquals(transform, result.regions.get(0).get("rootMethod"));
    }

    @Test
    public void groupsSameThreadCallChainAtCallbackEntry() {
        List<Map<String, Object>> plans = Arrays.asList(
                plan(HANDLE,
                        Collections.singletonList(HANDLE + ".param0:callbacks"),
                        Arrays.asList(IDENTIFIER + ".return", PASSWORD + ".return")),
                plan(IDENTIFIER,
                        Collections.singletonList(IDENTIFIER + ".param0:name"),
                        Collections.singletonList(IDENTIFIER + ".return")),
                plan(PASSWORD,
                        Collections.singletonList(PASSWORD + ".param0:tokenid"),
                        Collections.singletonList(PASSWORD + ".return")),
                plan(RETRIEVE,
                        Arrays.asList(RETRIEVE + ".param0:tokenid",
                                "<example.SecretManager: java.util.Map allKeys>"),
                        Collections.singletonList(RETRIEVE + "#failure:key == null")));

        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(call(HANDLE, IDENTIFIER, 11));
        edges.add(call(HANDLE, PASSWORD, 12));
        edges.add(call(PASSWORD, RETRIEVE, 4));
        edges.add(edge(RETRIEVE, "SEED", "seed",
                RETRIEVE + "#failure:key == null", RETRIEVE + ".return", 8));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(1, result.regions.size());
        Map<String, Object> region = result.regions.get(0);
        assertEquals(HANDLE, region.get("rootMethod"));
        assertEquals(HANDLE, region.get("staticRootCandidate"));
        assertEquals("STATIC_CANDIDATE_ONLY", region.get("rootAuthority"));
        assertEquals("RUNTIME_REQUIRED", region.get("rootValidation"));
        assertEquals(RETRIEVE, region.get("anchorMethod"));
        @SuppressWarnings("unchecked")
        List<String> methods = (List<String>) region.get("methods");
        assertTrue(methods.containsAll(Arrays.asList(
                HANDLE, IDENTIFIER, PASSWORD, RETRIEVE)));
        assertTrue(((List<?>) region.get("symbolicInputs")).size() > 0);
        assertTrue(((List<?>) region.get("outputs")).size() > 0);
        assertEquals(Boolean.TRUE, result.coverage.get("complete"));
    }

    @Test
    public void keepsSaslTransferBetweenConcolicRegions() {
        String sender = "<example.Client: java.lang.String buildUserName()>";
        String receiver = "<example.Server: void handle(java.lang.String)>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(sender, Collections.singletonList("<example.Client: int keyId>"),
                        Collections.singletonList(sender + ".return")),
                plan(receiver, Collections.singletonList(receiver + ".param0:userName"),
                        Collections.singletonList(receiver + "#failure:missingKey")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(receiver, "SEED", "seed", receiver + "#failure:missingKey",
                        receiver + ".return", 2),
                edge(receiver, "PROTOCOL_TRANSFER", "hdfs_sasl_username_bridge",
                        sender + ".return", receiver + ".param0:userName", 3));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(2, result.regions.size());
        assertEquals(1, result.regionEdges.size());
        assertEquals("SASL_TRANSFER", result.regionEdges.get(0).get("kind"));
        assertEquals("", result.regionEdges.get(0).get("relation"));
        assertEquals("EQUALITY", result.regionEdges.get(0).get(
                "candidateRelation"));
        assertEquals(Boolean.TRUE, result.regionEdges.get(0).get(
                "mappingOnly"));
        assertEquals(Boolean.FALSE, result.regionEdges.get(0).get(
                "eligibleForAutomaticDerivation"));
        assertEquals(Boolean.TRUE, result.coverage.get("complete"));
    }

    @Test
    public void emitsProtocolCandidateForEveryEnclosingProducerRegion() {
        String firstRoot = "<example.First: void run()>";
        String secondRoot = "<example.Second: void run()>";
        String sender = "<example.Protocol: java.lang.String send()>";
        String receiver = "<example.Server: void receive(java.lang.String)>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(firstRoot, Collections.singletonList(
                                firstRoot + ".param0:value"),
                        Collections.singletonList(firstRoot + "#failure")),
                plan(secondRoot, Collections.singletonList(
                                secondRoot + ".param0:value"),
                        Collections.singletonList(secondRoot + "#failure")),
                plan(sender, Collections.singletonList(
                                "<example.Protocol: int keyId>"),
                        Collections.singletonList(sender + ".return")),
                plan(receiver, Collections.singletonList(
                                receiver + ".param0:userName"),
                        Collections.singletonList(receiver + "#failure")));
        List<Map<String, Object>> edges = Arrays.asList(
                invocation(firstRoot, sender, firstRoot + "::r0",
                        sender + "::r0", 1),
                invocation(secondRoot, sender, secondRoot + "::r0",
                        sender + "::r0", 2),
                edge(firstRoot, "SEED", "seed", firstRoot + "#failure",
                        firstRoot + ".return", 3),
                edge(secondRoot, "SEED", "seed", secondRoot + "#failure",
                        secondRoot + ".return", 4),
                edge(receiver, "SEED", "seed", receiver + "#failure",
                        receiver + ".return", 5),
                edge(receiver, "PROTOCOL_TRANSFER",
                        "hdfs_sasl_username_bridge", sender + ".return",
                        receiver + ".param0:userName", 6));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);

        List<String> producerRoots = new ArrayList<>();
        for (Map<String, Object> regionEdge : result.regionEdges) {
            String producerId = String.valueOf(regionEdge.get("fromRegion"));
            for (Map<String, Object> region : result.regions) {
                if (producerId.equals(String.valueOf(region.get("regionId")))) {
                    producerRoots.add(String.valueOf(region.get("rootMethod")));
                }
            }
        }
        assertEquals(2, result.regionEdges.size());
        assertTrue(producerRoots.contains(firstRoot));
        assertTrue(producerRoots.contains(secondRoot));
    }

    @Test
    public void keepsSynchronousCallbackInsideHighestSameThreadRegion() {
        String receive = "<example.Server: void receive(java.io.InputStream)>";
        String register = "<example.Server: void register()>";
        String handshake = "<example.Server: void doSaslHandshake()>";
        String handle = "<example.Handler: void handle(java.lang.Object[])>";
        String apply = "<example.Server$1: char[] apply(java.lang.String)>";
        String retrieve = "<example.Secret: byte[] retrieve(int)>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(receive, Collections.singletonList(receive + ".param0:in"),
                        Collections.singletonList(receive + "::registered")),
                plan(register, Collections.singletonList(register + "::handler"),
                        Collections.singletonList(register + "::registered")),
                plan(handshake, Collections.singletonList(handshake + "::handler"),
                        Collections.singletonList(handshake + "::response")),
                plan(handle, Collections.singletonList(handle + "::passwordFunction"),
                        Collections.singletonList(handle + "::password")),
                plan(apply, Collections.singletonList(apply + ".param0:userName"),
                        Collections.singletonList(apply + ".return")),
                plan(retrieve, Collections.singletonList(retrieve + ".param0:keyId"),
                        Collections.singletonList(retrieve + "#failure:missing")));

        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(invocation(receive, register, receive + "::server",
                register + "::r0", 1));
        edges.add(invocation(register, handshake, register + "::handler",
                handshake + "::handler", 2));
        edges.add(edge(register, "IDENTITY_BINDING",
                "synchronous_callback_receiver", register + "::handler",
                handle + "::r0", 3));
        edges.add(invocation(handle, apply, handle + "::passwordFunction",
                apply + "::r0", 4));
        edges.add(invocation(apply, retrieve, apply + "::keyId",
                retrieve + ".param0:keyId", 5));
        edges.add(edge(retrieve, "SEED", "seed",
                retrieve + "#failure:missing", retrieve + ".return", 6));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(1, result.regions.size());
        Map<String, Object> region = result.regions.get(0);
        assertEquals(receive, region.get("rootMethod"));
        @SuppressWarnings("unchecked")
        List<String> methods = (List<String>) region.get("methods");
        assertTrue(methods.containsAll(Arrays.asList(receive, register,
                handshake, handle, apply, retrieve)));
        assertEquals(0, result.regionEdges.size());
    }

    @Test
    public void recursivelyCreatesSharedStateProducerRegion() {
        String updater = "<example.Updater: void run()>";
        String reader = "<example.Handler: void handle()>";
        String field = "<example.State: int keyId>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(updater, Collections.singletonList(updater + ".param0:value"),
                        Collections.singletonList(field)),
                plan(reader, Collections.singletonList(field),
                        Collections.singletonList(reader + "#failure:stale")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(reader, "SEED", "seed", reader + "#failure:stale",
                        reader + ".return", 1),
                edge(reader, "HEAP_READ", "field_read", field,
                        reader + "::value", 2),
                edge(updater, "HEAP_WRITE", "field_write",
                        updater + ".param0:value", field, 3));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(2, result.regions.size());
        assertTrue(result.regionEdges.stream()
                .anyMatch(edge -> "SHARED_STATE".equals(edge.get("kind"))));
        assertEquals(Boolean.TRUE, result.coverage.get("complete"));
    }

    @Test
    public void constantHeapWriteSiteIsInternalToOutputSlice() {
        String root = "<example.Updater: void markReady()>";
        String field = "<example.State: boolean ready>";
        String site = root + "#u6";
        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Collections.singletonList(site),
                        Collections.singletonList(field)));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(root, "HEAP_WRITE", "field_write", site, field, 6),
                edge(root, "SEED", "seed", field,
                        root + "#observed", 7));

        Map<String, Object> region = onlyRegion(
                SymbolicRegionPlanner.plan(edges, plans));

        assertFalse(inputCells(region).contains(site));
        assertTrue(String.valueOf(region.get("derivedInputs"))
                .contains("expression or allocation is evaluated"));
    }

    @Test
    public void emitsRequestedOutputSliceForNeutralHeapProducer() {
        String updater = "<example.Updater: void run(int)>";
        String reader = "<example.Reader: void handle()>";
        String input = updater + ".param0:value";
        String field = "<example.State: java.util.Map entries>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(updater, Collections.singletonList(input),
                        Collections.singletonList(field)),
                plan(reader, Collections.singletonList(field),
                        Collections.singletonList(reader + "#failure:missing")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(reader, "SEED", "seed", reader + "#failure:missing",
                        reader + ".return", 1),
                edge(reader, "HEAP_READ", "field_read", field,
                        reader + "::entries", 2),
                edge(updater, "HEAP_WRITE", "field_write", input, field, 3));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producer = null;
        for (Map<String, Object> region : result.regions) {
            if (updater.equals(region.get("rootMethod"))) {
                producer = region;
                break;
            }
        }
        assertTrue(producer != null);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        assertEquals(1, slices.size());
        Map<String, Object> slice = slices.get(0);
        assertEquals(Boolean.TRUE, slice.get("complete"));
        assertEquals("REQUESTED_OUTPUT_BACKWARD_DEPENDENCY_CLOSURE",
                slice.get("selection"));
        assertEquals(1, ((List<?>) slice.get("inputPorts")).size());
        assertEquals(Collections.singletonList(updater), slice.get("methods"));
        assertEquals(1, slice.get("causalEdgeCount"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> outputs =
                (List<Map<String, Object>>) producer.get("outputs");
        assertEquals(outputs.get(0).get("portId"), slice.get("outputPort"));
    }

    @Test
    public void indexedHotPathsIgnoreUnrelatedEdgesWithoutWeakeningAllowedMethods() {
        String root = "<example.Updater: void run(boolean,int)>";
        String writer = "<example.Updater: void write(int)>";
        String reader = "<example.Reader: void handle()>";
        String noise = "<example.Unrelated: void write(int)>";
        String enabled = root + ".param0:boolean";
        String value = root + ".param1:int";
        String writerValue = writer + ".param0:int";
        String output = "<example.State: int value>";
        String observed = reader + "::observed";
        String failure = reader + "#failure:stale";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, Arrays.asList(enabled, value),
                        Collections.singletonList(root + ".return")),
                plan(writer, Collections.singletonList(writerValue),
                        Collections.singletonList(output)),
                plan(reader, Collections.singletonList(output),
                        Collections.singletonList(failure)));

        List<Map<String, Object>> baselineEdges = new ArrayList<>();
        Map<String, Object> call = invocation(root, writer, value,
                writerValue, 7);
        call.put("id", "RELEVANT.CALL");
        baselineEdges.add(call);
        Map<String, Object> guard = edge(root, "GUARD",
                "path_guard_dependency", enabled, root + "::writePath", 6);
        guard.put("id", "RELEVANT.GUARD");
        guard.put("evidence", "dominating branch controls call at u7");
        baselineEdges.add(guard);
        Map<String, Object> write = edge(writer, "HEAP_WRITE",
                "field_write", writerValue, output, 2);
        write.put("id", "RELEVANT.WRITE");
        baselineEdges.add(write);
        baselineEdges.add(edge(reader, "HEAP_READ", "field_read",
                output, observed, 1));
        baselineEdges.add(edge(reader, "SEED", "seed_exception_throw",
                observed, failure, 2));

        Map<String, Object> baselineSlice = requestedOutputSlice(
                SymbolicRegionPlanner.plan(baselineEdges, plans), root,
                output);

        List<Map<String, Object>> noisyEdges = new ArrayList<>();
        Map<String, Object> noiseCall = invocation(noise, writer,
                noise + ".param0:int", writerValue, 7);
        noiseCall.put("id", "NOISE.CALL");
        noisyEdges.add(noiseCall);
        Map<String, Object> noiseGuard = edge(noise, "GUARD",
                "path_guard_dependency", noise + "::enabled",
                noise + "::writePath", 6);
        noiseGuard.put("id", "NOISE.GUARD");
        noiseGuard.put("evidence", "dominating branch controls call at u7");
        noisyEdges.add(noiseGuard);
        noisyEdges.addAll(baselineEdges);
        Map<String, Object> noiseWrite = edge(noise, "HEAP_WRITE",
                "field_write", noise + ".param0:int", output, 2);
        noiseWrite.put("id", "NOISE.SAME.TARGET");
        noisyEdges.add(noiseWrite);
        Map<String, Object> noisySlice = requestedOutputSlice(
                SymbolicRegionPlanner.plan(noisyEdges, plans), root,
                output);

        // The caller index must not admit another method's call/guard rows,
        // and the incoming-cell index must still apply allowedMethods before
        // following a same-target definition from outside this thread region.
        assertEquals(baselineSlice, noisySlice);
        assertTrue(((List<?>) noisySlice.get("causalEdgeIds"))
                .contains("RELEVANT.GUARD"));
        assertFalse(String.valueOf(noisySlice).contains("NOISE."));
    }

    @Test
    public void collectionSnapshotOutputSliceClosesToBackingMapInput() {
        String exporter = "<example.SecretManager: example.Exported exportKeys()>";
        String reader = "<example.Reader: void read()>";
        String map = "<example.SecretManager: java.util.Map allKeys>";
        String mapLocal = exporter + "::$r3";
        String valuesView = exporter + "::$r5";
        String array = exporter + "::$r7";
        String output = "<example.Exported: example.Key[] allKeys>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(exporter, Collections.singletonList(map),
                        Arrays.asList(mapLocal, valuesView, array, output)),
                plan(reader, Collections.singletonList(output),
                        Collections.singletonList(reader
                                + "#failure:missing")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(exporter, "HEAP_READ", "field_read", map,
                mapLocal, 13));
        Map<String, Object> values = edge(exporter, "MODEL_TRANSFORM",
                "container_backed_view_projection", mapLocal, valuesView,
                14);
        authoritativeValueFlow(values);
        values.put("containerProjectionContractVersion", 1);
        values.put("containerProjectionOperation", "MAP_VALUES_VIEW");
        values.put("receiverValueDependencyComplete", true);
        edges.add(values);
        Map<String, Object> snapshot = edge(exporter, "MODEL_TRANSFORM",
                "container_snapshot_projection", valuesView, array, 16);
        authoritativeValueFlow(snapshot);
        snapshot.put("containerProjectionContractVersion", 1);
        snapshot.put("containerProjectionOperation", "COLLECTION_TO_ARRAY");
        snapshot.put("receiverValueDependencyComplete", true);
        edges.add(snapshot);
        Map<String, Object> write = edge(exporter, "HEAP_WRITE",
                "field_write", array, output, 20);
        write.put("siteId", exporter + "#u20");
        write.put("unit", "r0." + output + " = $r7");
        authoritativeValueFlow(write);
        edges.add(write);
        edges.add(edge(reader, "HEAP_READ", "field_read", output,
                reader + "::keys", 1));
        edges.add(edge(reader, "SEED", "seed_exception_throw",
                reader + "::keys", reader + "#failure:missing", 2));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), exporter);
        @SuppressWarnings("unchecked")
        Map<String, Object> slice = ((List<Map<String, Object>>) producer.get(
                "outputSlices")).stream().filter(candidate -> output.equals(
                candidate.get("outputCell"))).findFirst()
                .orElseThrow(AssertionError::new);

        assertEquals(Boolean.TRUE, slice.get("complete"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        assertTrue(bindings.stream().anyMatch(binding ->
                map.equals(binding.get("dependencyCell"))));
        assertTrue(((List<?>) slice.get("causalEdgeIds")).contains(
                values.get("id")));
        assertTrue(((List<?>) slice.get("causalEdgeIds")).contains(
                snapshot.get("id")));
        assertFalse(String.valueOf(slice.get("derivedInputs")).contains(
                "<java.util.Collection: java.lang.Object[] toArray"));
    }

    @Test
    public void outboundProtocolStringSliceClosesToCurrentKeyAndKeyId() {
        String dispatch = "<example.Client: void dispatch()>";
        String build = "<example.Client: void buildUserName()>";
        String construct = "<example.DataKey: void <init>(int)>";
        String handshake = "<example.Client: void doSaslHandshake(java.lang.String)>";
        String receive = "<example.Server: void receive(java.lang.String)>";
        String currentKey = "<example.KeyManager: example.BlockKey currentKey>";
        String keyId = "<example.BlockKey: int keyId>";
        String dataKeyId = "<example.DataKey: int keyId>";
        String keyLocal = build + "::$r0";
        String idLocal = build + "::$i0";
        String constructorInput = construct + ".param0:int";
        String constructorLocal = construct + "::i0";
        String userName = build + "::$r1";
        String outbound = handshake + ".param0:java.lang.String";
        String inbound = receive + ".param0:java.lang.String";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(dispatch, Collections.emptyList(),
                        Collections.singletonList(dispatch + "::started")),
                plan(build, Arrays.asList(currentKey, keyId),
                        Arrays.asList(keyLocal, idLocal, userName)),
                plan(construct, Collections.singletonList(constructorInput),
                        Arrays.asList(constructorLocal, dataKeyId)),
                plan(handshake, Collections.singletonList(outbound),
                        Collections.singletonList(outbound)),
                plan(receive, Collections.singletonList(inbound),
                        Collections.singletonList(receive
                                + "#failure:unknownUser")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(invocation(dispatch, build, dispatch + "::client",
                build + "::r0", 1));
        edges.add(edge(build, "HEAP_READ", "field_read",
                currentKey, keyLocal, 2));
        edges.add(edge(build, "HEAP_READ", "field_read",
                keyId, idLocal, 3));
        Map<String, Object> constructorArgument = edge(build, "CONSTRUCT",
                "constructor_caller_argument", idLocal, constructorInput, 3);
        constructorArgument.put("invoke", construct);
        edges.add(constructorArgument);
        edges.add(edge(construct, "VALUE_PASS", "local_def_use",
                constructorInput, constructorLocal, 1));
        edges.add(edge(construct, "HEAP_WRITE", "field_write",
                constructorLocal, dataKeyId, 2));
        edges.add(edge(build, "COMPUTE", "local_def_use",
                keyLocal, userName, 4));
        edges.add(edge(build, "HEAP_READ", "field_read",
                dataKeyId, userName, 4));
        edges.add(invocation(build, handshake, userName, outbound, 5));
        edges.add(edge(receive, "PROTOCOL_TRANSFER",
                "hdfs_sasl_username", outbound, inbound, 6));
        edges.add(edge(receive, "SEED", "seed_exception_throw",
                inbound, receive + "#failure:unknownUser", 7));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producer = regionForRoot(result, dispatch);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> outbound.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing outbound protocol scalar slice"));

        assertEquals(Boolean.TRUE, slice.get("complete"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).isEmpty());
        assertTrue(((List<?>) slice.get("heapInitializers")).isEmpty());
        assertTrue(((List<?>) slice.get("methods")).contains(construct));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        assertTrue(bindings.stream().anyMatch(binding ->
                currentKey.equals(binding.get("dependencyCell"))));
        assertTrue(bindings.stream().anyMatch(binding ->
                keyId.equals(binding.get("dependencyCell"))));
        assertTrue(result.regionEdges.stream().anyMatch(regionEdge ->
                outbound.equals(regionEdge.get("fromPort"))
                        && inbound.equals(regionEdge.get("toPort"))));
    }

    @Test
    public void outputSlicePromotesOpaqueNullnessAndBindsDeclaredProjection() {
        String send = "<example.Client: void send(java.lang.String)>";
        String external = "<example.Protocol: example.Config getConfig()>";
        String receive = "<example.Server: void receive(java.lang.String)>";
        String configField = "<example.Config: boolean enabled>";
        String opaqueReturn = external + ".return";
        String projectedReturn = opaqueReturn + "#field:enabled";
        String local = send + "::$r0";
        String localField = local + "#field:enabled";
        String userName = send + "::userName";
        String outbound = send + ".param0:java.lang.String";
        String inbound = receive + ".param0:java.lang.String";

        List<Map<String, Object>> plans = Arrays.asList(
                // Deliberately omit the opaque return from the broad method
                // plan: the output demand walk is what discovers its nullness.
                plan(send, Collections.singletonList(configField),
                        Arrays.asList(userName, outbound)),
                plan(receive, Collections.singletonList(inbound),
                        Collections.singletonList(receive
                                + "#failure:unknownUser")));
        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> baseReturn = edge(send, "FUNCTION_RETURN",
                "call_return", opaqueReturn, local, 1);
        baseReturn.put("invoke", external);
        edges.add(baseReturn);
        Map<String, Object> fieldReturn = edge(send, "FUNCTION_RETURN",
                "projected_call_return", projectedReturn, localField, 1);
        fieldReturn.put("invoke", external);
        edges.add(fieldReturn);
        edges.add(edge(send, "HEAP_READ", "field_read",
                configField, localField, 1));
        edges.add(edge(send, "GUARD", "path_guard_dependency",
                local, userName, 2));
        edges.add(edge(send, "COMPUTE", "local_def_use",
                localField, userName, 2));
        edges.add(edge(send, "VALUE_PASS", "local_def_use",
                userName, outbound, 3));
        edges.add(edge(receive, "PROTOCOL_TRANSFER",
                "username_handoff", outbound, inbound, 4));
        edges.add(edge(receive, "SEED", "seed_exception_throw", inbound,
                receive + "#failure:unknownUser", 5));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producer = regionForRoot(result, send);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> outbound.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);

        assertEquals(Boolean.FALSE, slice.get("complete"));
        assertEquals(Boolean.FALSE, slice.get("captureBindingsComplete"));
        assertTrue(String.valueOf(slice.get("captureBindingIssues"))
                .contains("NO_EXACT_CALL_ARGUMENT_CAPTURE_BINDING"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).isEmpty());
        assertTrue(inputCells(producer).contains(opaqueReturn));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        assertTrue(bindings.stream().anyMatch(binding ->
                opaqueReturn.equals(binding.get("dependencyCell"))
                        && "OUTPUT_SLICE_FRONTIER_PROMOTION".equals(
                        binding.get("bindingAuthority"))));
        assertTrue(bindings.stream().anyMatch(binding ->
                configField.equals(binding.get("dependencyCell"))
                        && "EXACT_CELL_IDENTITY".equals(
                        binding.get("bindingAuthority"))));
    }

    @Test
    public void outputSlicePromotesExactDeclaredFieldPathFrontier() {
        String dispatch = "<example.Client: void dispatch()>";
        String handshake =
                "<example.Client: void handshake(java.lang.String)>";
        String receive =
                "<example.Server: void receive(java.lang.String)>";
        String config = "<example.Client: example.Config config>";
        String enabled = config + "#field:enabled";
        String projected = dispatch + "::$r1#field:enabled";
        String userName = dispatch + "::userName";
        String outbound = handshake + ".param0:java.lang.String";
        String inbound = receive + ".param0:java.lang.String";

        List<Map<String, Object>> plans = Arrays.asList(
                // The broad region knows the declared carrier.  Only the
                // requested-output walk discovers its exact nested field.
                plan(dispatch, Collections.singletonList(config),
                        Collections.singletonList(userName)),
                plan(handshake, Collections.singletonList(outbound),
                        Collections.singletonList(outbound)),
                plan(receive, Collections.singletonList(inbound),
                        Collections.singletonList(receive
                                + "#failure:unknownUser")));
        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> fieldPath = edge(dispatch, "HEAP_READ",
                "projected_accessor_field_return", enabled, projected, 1);
        authoritativeValueFlow(fieldPath);
        fieldPath.put("fieldSensitive", true);
        fieldPath.put("objectFromCell", config);
        fieldPath.put("objectToCell", dispatch + "::$r1");
        fieldPath.put("fieldPath", "#field:enabled");
        edges.add(fieldPath);
        edges.add(edge(dispatch, "COMPUTE", "local_def_use", projected,
                userName, 2));
        edges.add(invocation(dispatch, handshake, userName, outbound, 3));
        edges.add(edge(receive, "PROTOCOL_TRANSFER", "username_handoff",
                outbound, inbound, 4));
        edges.add(edge(receive, "SEED", "seed_exception_throw", inbound,
                receive + "#failure:unknownUser", 5));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), dispatch);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> outbound.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);

        assertEquals(Boolean.TRUE, slice.get("complete"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).isEmpty());
        assertTrue(inputCells(producer).contains(enabled));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> ports =
                (List<Map<String, Object>>) producer.get("symbolicInputs");
        assertTrue(ports.stream().anyMatch(port ->
                enabled.equals(port.get("cell"))
                        && "OUTPUT_SLICE_MATERIALIZABLE_FIELD_PATH_FRONTIER"
                        .equals(port.get("selectionReason"))));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        assertTrue(bindings.stream().anyMatch(binding ->
                enabled.equals(binding.get("dependencyCell"))
                        && "OUTPUT_SLICE_FRONTIER_PROMOTION".equals(
                        binding.get("bindingAuthority"))));
    }

    @Test
    public void outputSlicePromotesUniqueBareDeclaredScalarFieldRead() {
        String dispatch = "<example.Client: void dispatch()>";
        String handshake =
                "<example.Client: void handshake(java.lang.String)>";
        String receive =
                "<example.Server: void receive(java.lang.String)>";
        String config = "<example.Client: example.Config config>";
        String expiry = "<example.DelegationKey: long expiryDate>";
        String getter =
                "<example.DelegationKey: long getExpiryDate()>";
        String local = dispatch + "::$l1";
        String userName = dispatch + "::userName";
        String outbound = handshake + ".param0:java.lang.String";
        String inbound = receive + ".param0:java.lang.String";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(dispatch, Collections.singletonList(config),
                        Collections.singletonList(userName)),
                plan(handshake, Collections.singletonList(outbound),
                        Collections.singletonList(outbound)),
                plan(receive, Collections.singletonList(inbound),
                        Collections.singletonList(receive
                                + "#failure:expired")));
        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> read = edge(dispatch, "HEAP_READ",
                "accessor_field_return", expiry, local, 11);
        read.put("siteId", dispatch + "#u11");
        read.put("invoke", getter);
        read.put("accessorImplementationMethod", getter);
        read.put("accessorImplementationAuthority",
                "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
        authoritativeValueFlow(read);
        declaredMetadata(read, expiry, "example.DelegationKey", "long",
                "expiryDate");
        edges.add(read);
        edges.add(edge(dispatch, "COMPUTE", "local_def_use", local,
                userName, 12));
        edges.add(invocation(dispatch, handshake, userName, outbound, 13));
        edges.add(edge(receive, "PROTOCOL_TRANSFER", "username_handoff",
                outbound, inbound, 14));
        edges.add(edge(receive, "SEED", "seed_exception_throw", inbound,
                receive + "#failure:expired", 15));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), dispatch);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> outbound.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);

        assertEquals(Boolean.TRUE, slice.get("complete"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).isEmpty());
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> ports =
                (List<Map<String, Object>>) producer.get("symbolicInputs");
        Map<String, Object> expiryPort = ports.stream()
                .filter(port -> expiry.equals(port.get("cell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("OUTPUT_SLICE_MATERIALIZABLE_DECLARED_FIELD_FRONTIER",
                expiryPort.get("selectionReason"));
        assertEquals("FIELD_ACCESS", expiryPort.get("bindingMode"));
        assertEquals(expiry, expiryPort.get("accessFieldSignature"));
        assertEquals("example.DelegationKey",
                expiryPort.get("accessOwnerClass"));
        assertEquals(dispatch, expiryPort.get("accessorCallerMethod"));
        assertEquals(dispatch + "#u11",
                expiryPort.get("accessorCallSiteId"));
        assertEquals(11, expiryPort.get("accessorCallUnitIndex"));
        assertEquals(getter, expiryPort.get("accessorDeclaredCallee"));
        assertEquals(getter,
                expiryPort.get("accessorImplementationMethod"));
        assertEquals("STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                        + "ACCESSOR_CALLSITE_V1",
                expiryPort.get("accessorCallSiteAuthority"));
        assertTrue(((List<?>) slice.get("methods")).contains(getter));
    }

    @Test
    public void outputSliceAdmitsEveryExactInheritedAccessorImplementationSite() {
        Map<String, Object> slice = inheritedAccessorOutputSlice(true,
                false);
        String implementation =
                "<example.KeyBase: int getKeyId()>";

        assertTrue(((List<?>) slice.get("methods")).contains(
                implementation));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> admissions =
                (List<Map<String, Object>>) slice.get(
                        "accessorImplementationAdmissions");
        assertEquals(4, admissions.size());
        assertEquals(Arrays.asList(
                        "<example.Secret: void addKeys(example.Keys)>#u14",
                        "<example.Secret: void addKeys(example.Keys)>#u20",
                        "<example.Secret: void addKeys(example.Keys)>#u26",
                        "<example.Secret: void addKeys(example.Keys)>#u32"),
                Arrays.asList(String.valueOf(admissions.get(0).get(
                                "siteId")),
                        String.valueOf(admissions.get(1).get("siteId")),
                        String.valueOf(admissions.get(2).get("siteId")),
                        String.valueOf(admissions.get(3).get("siteId"))));
        for (Map<String, Object> admission : admissions) {
            assertEquals("<example.KeyBase: int keyId>",
                    admission.get("declaredFieldSignature"));
            assertEquals("example.KeyBase",
                    admission.get("declaredFieldOwner"));
            assertEquals("<example.Key: int getKeyId()>",
                    admission.get("declaredCallee"));
            assertEquals(implementation,
                    admission.get("implementationMethod"));
            assertEquals("SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY",
                    admission.get("implementationAuthority"));
        }
    }

    @Test
    public void outputSliceRejectsRuntimeOnlyAccessorImplementation() {
        Map<String, Object> slice = inheritedAccessorOutputSlice(false,
                false);

        assertFalse(((List<?>) slice.get("methods")).contains(
                "<example.KeyBase: int getKeyId()>"));
        assertTrue(((List<?>) slice.get(
                "accessorImplementationAdmissions")).isEmpty());
    }

    @Test
    public void outputSliceRejectsAccessorWithMismatchedDeclaredFieldTuple() {
        Map<String, Object> slice = inheritedAccessorOutputSlice(true,
                true);

        assertFalse(((List<?>) slice.get("methods")).contains(
                "<example.KeyBase: int getKeyId()>"));
        assertTrue(((List<?>) slice.get(
                "accessorImplementationAdmissions")).isEmpty());
    }

    @Test
    public void reusedAccessorFieldPortAdmitsImplementationInEverySlice() {
        String update = "<example.Manager: void update()>";
        String reader = "<example.Reader: void read()>";
        String expiry = "<example.DelegationKey: long expiryDate>";
        String getter = "<example.DelegationKey: long getExpiryDate()>";
        String expiryLocal = update + "::$expiry";
        String firstValue = update + "::firstValue";
        String secondValue = update + "::secondValue";
        String firstState = "<example.Manager: long firstState>";
        String secondState = "<example.Manager: long secondState>";
        String merged = update + "::$merged";
        String failure = update + "#u20#exception:example.StaleState";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(update, Collections.singletonList(
                        "<example.Manager: example.Config config>"),
                        Arrays.asList(firstState, secondState, merged,
                                failure)),
                // These exact downstream live-ins make firstState and
                // secondState semantic region outputs; the producer's other
                // locals remain internal implementation state.
                plan(reader, Arrays.asList(firstState, secondState),
                        Collections.singletonList(reader
                                + "#failure:stale")));
        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> read = edge(update, "HEAP_READ",
                "accessor_field_return", expiry, expiryLocal, 11);
        read.put("siteId", update + "#u11");
        read.put("invoke", getter);
        read.put("accessorImplementationMethod", getter);
        read.put("accessorImplementationAuthority",
                "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
        authoritativeValueFlow(read);
        declaredMetadata(read, expiry, "example.DelegationKey", "long",
                "expiryDate");
        edges.add(read);
        // Fill the broad frontier with causally relevant but output-irrelevant
        // state.  The exact expiry dependency is therefore promoted by the
        // first requested-output slice and reused by the second one, which is
        // the ordering that exposed the missing per-slice getter admission.
        for (int index = 0; index < 128; index++) {
            String suffix = String.format("%03d", index);
            String noise = "<example.ANoise" + suffix + ": long value>";
            String noiseLocal = update + "::$noise" + suffix;
            edges.add(edge(update, "HEAP_READ", "noise_read", noise,
                    noiseLocal, 1000 + index));
            edges.add(edge(update, "COMPUTE", "noise_merge", noiseLocal,
                    merged, 2000 + index));
        }
        edges.add(edge(update, "COMPUTE", "local_def_use", expiryLocal,
                firstValue, 12));
        edges.add(edge(update, "COMPUTE", "local_def_use", expiryLocal,
                secondValue, 13));
        Map<String, Object> firstWrite = edge(update, "HEAP_WRITE",
                "field_write", firstValue, firstState, 14);
        firstWrite.put("siteId", update + "#u14");
        firstWrite.put("unit", "r0." + firstState + " = firstValue");
        authoritativeValueFlow(firstWrite);
        edges.add(firstWrite);
        Map<String, Object> secondWrite = edge(update, "HEAP_WRITE",
                "field_write", secondValue, secondState, 15);
        secondWrite.put("siteId", update + "#u15");
        secondWrite.put("unit", "r0." + secondState + " = secondValue");
        authoritativeValueFlow(secondWrite);
        edges.add(secondWrite);
        edges.add(edge(update, "HEAP_READ", "first_state_read", firstState,
                merged, 16));
        edges.add(edge(update, "HEAP_READ", "second_state_read",
                secondState, merged, 17));
        edges.add(edge(update, "SEED", "seed_exception_throw", merged,
                failure, 20));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), update);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> ports =
                (List<Map<String, Object>>) producer.get("symbolicInputs");
        Map<String, Object> expiryPort = ports.stream()
                .filter(port -> expiry.equals(port.get("cell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("REQUESTED_OUTPUT_FRONTIER_PROMOTION",
                expiryPort.get("portOrigin"));
        assertEquals(getter,
                expiryPort.get("accessorImplementationMethod"));
        String expiryPortId = String.valueOf(expiryPort.get("portId"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        for (String output : Arrays.asList(firstState, secondState)) {
            Map<String, Object> slice = slices.stream()
                    .filter(candidate -> output.equals(candidate.get(
                            "outputCell")))
                    .findFirst().orElseThrow(() -> new AssertionError(
                            output + " not found in " + slices));
            assertTrue(((List<?>) slice.get("inputPorts")).contains(
                    expiryPortId));
            assertTrue(output + " port=" + expiryPort + " methods="
                            + slice.get("methods"),
                    ((List<?>) slice.get("methods")).contains(getter));
        }
    }

    @Test
    public void exactOutputDependencyPromotesPastTruncatedBroadFrontier() {
        String dispatch = "<example.Client: void dispatch()>";
        String handshake =
                "<example.Client: void handshake(java.lang.String)>";
        String receive =
                "<example.Server: void receive(java.lang.String)>";
        String expiry = "<example.DelegationKey: long expiryDate>";
        String expiryLocal = dispatch + "::$l1";
        String userName = dispatch + "::userName";
        String outbound = handshake + ".param0:java.lang.String";
        String inbound = receive + ".param0:java.lang.String";

        List<String> broadInputs = new ArrayList<>();
        List<Map<String, Object>> edges = new ArrayList<>();
        // Fill and overflow the broad 128-port budget with dependencies that
        // are unrelated to the requested outbound value.  The expiry field is
        // discovered only by the precise requested-output backward slice.
        for (int index = 0; index < 129; index++) {
            String suffix = String.format("%03d", index);
            String field = "<example.Noise" + suffix
                    + ": int value" + suffix + ">";
            broadInputs.add(field);
            edges.add(edge(dispatch, "HEAP_READ", "field_read", field,
                    dispatch + "::$noise" + suffix, 1000 + index));
        }

        List<Map<String, Object>> plans = Arrays.asList(
                plan(dispatch, broadInputs,
                        Collections.singletonList(userName)),
                plan(handshake, Collections.singletonList(outbound),
                        Collections.singletonList(outbound)),
                plan(receive, Collections.singletonList(inbound),
                        Collections.singletonList(receive
                                + "#failure:expired")));
        Map<String, Object> read = edge(dispatch, "HEAP_READ",
                "accessor_field_return", expiry, expiryLocal, 11);
        read.put("siteId", dispatch + "#u11");
        read.put("invoke",
                "<example.DelegationKey: long getExpiryDate()>");
        read.put("accessorImplementationMethod",
                "<example.DelegationKey: long getExpiryDate()>");
        read.put("accessorImplementationAuthority",
                "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
        authoritativeValueFlow(read);
        declaredMetadata(read, expiry, "example.DelegationKey", "long",
                "expiryDate");
        edges.add(read);
        edges.add(edge(dispatch, "COMPUTE", "local_def_use", expiryLocal,
                userName, 12));
        edges.add(invocation(dispatch, handshake, userName, outbound, 13));
        edges.add(edge(receive, "PROTOCOL_TRANSFER", "username_handoff",
                outbound, inbound, 14));
        edges.add(edge(receive, "SEED", "seed_exception_throw", inbound,
                receive + "#failure:expired", 15));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), dispatch);
        assertEquals(129, producer.get("selectedExternalInputCount"));
        assertEquals(128, producer.get("broadInputPortLimit"));
        assertEquals(128, producer.get("broadInputPortCount"));
        assertEquals(Boolean.TRUE, producer.get("broadInputPortTruncated"));
        assertEquals(Boolean.FALSE, producer.get("inputSelectionComplete"));
        assertEquals(1, producer.get("outputSlicePromotedInputCount"));
        assertEquals(129, producer.get("symbolicInputPortCount"));
        assertEquals(512, producer.get("outputSliceInputPortLimit"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> ports =
                (List<Map<String, Object>>) producer.get("symbolicInputs");
        Map<String, Object> expiryPort = ports.stream()
                .filter(port -> expiry.equals(port.get("cell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(String.valueOf(producer.get("regionId")) + ".in.128",
                expiryPort.get("portId"));
        assertEquals("REQUESTED_OUTPUT_FRONTIER_PROMOTION",
                expiryPort.get("portOrigin"));
        assertEquals("EXACT_MATERIALIZABLE_REQUESTED_OUTPUT_DEPENDENCY_V1",
                expiryPort.get("promotionAuthority"));
        assertEquals("FIELD_ACCESS", expiryPort.get("bindingMode"));
        assertEquals(dispatch + "#u11",
                expiryPort.get("accessorCallSiteId"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> outbound.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Boolean.TRUE, slice.get("complete"));
        assertEquals(128, slice.get("inputPortCountBeforeSlice"));
        assertEquals(1, slice.get("promotedInputPortCount"));
        assertEquals(Boolean.FALSE, slice.get("promotionCapacityTruncated"));
        assertEquals(0, slice.get("promotionCapacityOmittedInputCount"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).isEmpty());
        assertEquals(slice.get("outputPort"),
                expiryPort.get("promotedForOutputPort"));
    }

    @Test
    public void seedGuardFrontierAndSeedOutputPreemptBroadPortNoise() {
        String handle = "<example.Handler: void handle(int)>";
        String retrieve =
                "<example.ZSecretManager: byte[] retrieve(int)>";
        String suppliedKeyId = handle + ".param0:int";
        String callerKeyId = handle + "::$keyId";
        String keyId = retrieve + ".param0:int";
        String allKeys =
                "<example.ZSecretManager: java.util.Map allKeys>";
        String map = retrieve + "::$map";
        String boxedKey = retrieve + "::$boxedKey";
        String lookup = retrieve + "::$lookup";
        String guard = retrieve + "::$missing";
        String exceptionObject = retrieve + "::$exceptionObject";
        String failure = retrieve
                + "#z999#exception:example.InvalidEncryptionKey";

        List<String> inputs = new ArrayList<>();
        List<String> outputs = new ArrayList<>();
        List<Map<String, Object>> edges = new ArrayList<>();
        // Every noise cell is genuinely in the exception closure through the
        // diagnostic payload.  They are not dependencies of the controlling
        // guard and all sort before ZSecretManager, reproducing broad-port
        // starvation without relying on irrelevant plan entries.
        for (int index = 0; index < 129; index++) {
            String suffix = String.format("%03d", index);
            String noise = "<example.ANoise" + suffix
                    + ": int value>";
            String noiseException = retrieve + "#a" + suffix
                    + "#exception:example.Noise";
            inputs.add(noise);
            outputs.add(noiseException);
            edges.add(edge(retrieve, "HEAP_READ", "field_read",
                    noise, retrieve + "::$noise" + suffix, 1000 + index));
            edges.add(edge(retrieve, "COMPUTE", "diagnostic_payload",
                    retrieve + "::$noise" + suffix, exceptionObject,
                    2000 + index));
            edges.add(edge(retrieve, "COMPUTE", "diagnostic_alias",
                    noiseException, exceptionObject, 3000 + index));
        }
        inputs.add(allKeys);
        inputs.add(keyId);
        outputs.add(failure);

        Map<String, Object> fieldRead = edge(retrieve, "HEAP_READ",
                "field_read", allKeys, map, 1);
        authoritativeValueFlow(fieldRead);
        edges.add(fieldRead);
        Map<String, Object> keyCopy = edge(retrieve, "VALUE_PASS",
                "local_def_use", keyId, boxedKey, 2);
        authoritativeValueFlow(keyCopy);
        edges.add(keyCopy);
        Map<String, Object> lookupState = edge(retrieve, "HEAP_LOOKUP",
                "map_lookup_state", map, lookup, 3);
        authoritativeValueFlow(lookupState);
        edges.add(lookupState);
        Map<String, Object> lookupKey = edge(retrieve, "HEAP_LOOKUP",
                "map_lookup_key", boxedKey, lookup, 3);
        authoritativeValueFlow(lookupKey);
        edges.add(lookupKey);
        Map<String, Object> guardValue = edge(retrieve, "VALUE_PASS",
                "local_def_use", lookup, guard, 4);
        authoritativeValueFlow(guardValue);
        edges.add(guardValue);
        edges.add(edge(retrieve, "GUARD", "exception_guard", guard,
                failure, 5));
        edges.add(edge(retrieve, "SEED", "seed_exception_throw",
                exceptionObject, failure, 6));
        Map<String, Object> callerCopy = edge(handle, "VALUE_PASS",
                "local_def_use", suppliedKeyId, callerKeyId, 0);
        authoritativeValueFlow(callerCopy);
        edges.add(callerCopy);
        Map<String, Object> callArgument = invocation(handle, retrieve,
                callerKeyId, keyId, 1);
        authoritativeValueFlow(callArgument);
        edges.add(callArgument);

        Map<String, Object> region = onlyRegion(SymbolicRegionPlanner.plan(
                edges, Arrays.asList(
                        plan(handle, Collections.singletonList(suppliedKeyId),
                                Collections.<String>emptyList()),
                        plan(retrieve, inputs, outputs))));

        assertEquals(handle, region.get("rootMethod"));
        assertEquals(131, region.get("selectedExternalInputCount"));
        assertEquals(128, region.get("broadInputPortCount"));
        assertEquals(Boolean.TRUE, region.get("broadInputPortTruncated"));
        assertEquals(2, region.get("mandatorySeedGuardInputCount"));
        assertEquals(Arrays.asList(suppliedKeyId, allKeys),
                region.get("mandatorySeedGuardInputs"));
        assertEquals(Boolean.TRUE,
                region.get("seedGuardInputDerivationComplete"));
        assertEquals(0, region.get("seedGuardInputDerivationGapCount"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputPorts =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        for (String dependency : Arrays.asList(allKeys, suppliedKeyId)) {
            Map<String, Object> port = inputPorts.stream()
                    .filter(candidate -> dependency.equals(candidate.get(
                            "cell")))
                    .findFirst().orElseThrow(AssertionError::new);
            assertEquals(Boolean.TRUE, port.get("mandatory"));
            assertEquals("SEED_GUARD_DEPENDENCY",
                    port.get("selectionPriority"));
            assertEquals("SEED_GUARD_DEPENDENCY_FRONTIER",
                    port.get("selectionReason"));
        }
        assertFalse(inputPorts.stream().anyMatch(port ->
                keyId.equals(port.get("cell"))));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> outputPorts =
                (List<Map<String, Object>>) region.get("outputs");
        assertEquals(128, outputPorts.size());
        Map<String, Object> seedOutput = outputPorts.stream()
                .filter(candidate -> failure.equals(candidate.get("cell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Boolean.TRUE, seedOutput.get("mandatory"));
        assertEquals("SEED_OUTPUT", seedOutput.get("selectionPriority"));
    }

    @Test
    public void seedGuardDerivationGapStaysConcreteInsteadOfBecomingFreeInput() {
        String handle = "<example.Handler: void handle(int)>";
        String retrieve = "<example.SecretManager: byte[] retrieve(int)>";
        String suppliedKeyId = handle + ".param0:int";
        String keyId = retrieve + ".param0:int";
        String allKeys = "<example.SecretManager: java.util.Map allKeys>";
        String map = retrieve + "::$map";
        String boxedKey = retrieve + "::$boxedKey";
        String lookup = retrieve + "::$lookup";
        String guard = retrieve + "::$missing";
        String exceptionObject = retrieve + "::$exceptionObject";
        String failure = retrieve
                + "#u9#exception:example.InvalidEncryptionKey";

        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> fieldRead = edge(retrieve, "HEAP_READ",
                "field_read", allKeys, map, 1);
        authoritativeValueFlow(fieldRead);
        edges.add(fieldRead);
        Map<String, Object> keyCopy = edge(retrieve, "VALUE_PASS",
                "local_def_use", keyId, boxedKey, 2);
        authoritativeValueFlow(keyCopy);
        edges.add(keyCopy);
        Map<String, Object> lookupState = edge(retrieve, "HEAP_LOOKUP",
                "map_lookup_state", map, lookup, 3);
        authoritativeValueFlow(lookupState);
        edges.add(lookupState);
        Map<String, Object> lookupKey = edge(retrieve, "HEAP_LOOKUP",
                "map_lookup_key", boxedKey, lookup, 3);
        authoritativeValueFlow(lookupKey);
        edges.add(lookupKey);
        Map<String, Object> guardValue = edge(retrieve, "VALUE_PASS",
                "local_def_use", lookup, guard, 4);
        authoritativeValueFlow(guardValue);
        edges.add(guardValue);
        Map<String, Object> exceptionValue = edge(retrieve, "CONSTRUCT",
                "constructor_value", guard, exceptionObject, 7);
        authoritativeValueFlow(exceptionValue);
        edges.add(exceptionValue);
        edges.add(edge(retrieve, "GUARD", "exception_guard", guard,
                failure, 5));
        edges.add(edge(retrieve, "SEED", "seed_exception_throw",
                exceptionObject, failure, 9));

        // This edge is structurally a call binding, but deliberately lacks
        // exact static/runtime provenance.  It may group the methods into one
        // region; it must not authorize suppliedKeyId -> keyId as a symbolic
        // equality or turn the deep formal into an independent free input.
        edges.add(invocation(handle, retrieve, suppliedKeyId, keyId, 1));

        Map<String, Object> region = onlyRegion(SymbolicRegionPlanner.plan(
                edges, Arrays.asList(
                        plan(handle, Collections.singletonList(suppliedKeyId),
                                Collections.<String>emptyList()),
                        plan(retrieve, Arrays.asList(allKeys, keyId),
                                Collections.singletonList(failure)))));

        assertEquals(handle, region.get("rootMethod"));
        assertEquals(Collections.singletonList(allKeys),
                region.get("mandatorySeedGuardInputs"));
        assertEquals(Boolean.FALSE,
                region.get("seedGuardInputDerivationComplete"));
        assertEquals(1, region.get("seedGuardInputDerivationGapCount"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> gaps =
                (List<Map<String, Object>>) region.get(
                        "seedGuardInputDerivationGaps");
        assertEquals(keyId, gaps.get(0).get("dependencyCell"));
        assertEquals("NON_AUTHORITATIVE_IN_REGION_DEFINITION",
                gaps.get(0).get("reason"));
        assertEquals(Boolean.FALSE, gaps.get(0).get("symbolicEligibility"));
        assertEquals("CONCRETE_BOUND_OBSERVED_VALUE",
                gaps.get(0).get("fallbackPolicy"));
        assertEquals("CONCRETE_PATH_ALLOWED",
                gaps.get(0).get("analysisContinuation"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> ports =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        assertFalse(ports.stream().anyMatch(port ->
                keyId.equals(port.get("cell"))));
        assertTrue(ports.stream().anyMatch(port ->
                suppliedKeyId.equals(port.get("cell"))));
        @SuppressWarnings("unchecked")
        List<String> derived = (List<String>) region.get("derivedInputs");
        assertTrue(derived.stream().anyMatch(value ->
                value.startsWith(keyId + " [seed guard provenance gap; "
                        + "CONCRETE_BOUND_OBSERVED_VALUE")));
        assertEquals(Boolean.TRUE, region.get("inputSelectionComplete"));
    }

    @Test
    public void seedGuardIgnoresExactAliasesOfModeledDefinitions() {
        String root = "<example.Handler: void handle(int)>";
        String suppliedKey = root + ".param0:int";
        String retrieve = "<example.Secret: void retrieve(int)>";
        String key = retrieve + ".param0:int";
        String declaredMap = "<example.Secret: java.util.Map allKeys>";
        String receiverMap = retrieve + "::r0#field:allKeys";
        String map = retrieve + "::$map";
        String boxed = retrieve + "::$boxed";
        String lookup = retrieve + "::$lookup";
        String guard = retrieve + "::$guard";
        String failure = retrieve + "#u8#exception:example.MissingKey";

        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> declaredRead = edge(retrieve, "HEAP_READ",
                "field_read", declaredMap, map, 1);
        authoritativeValueFlow(declaredRead);
        edges.add(declaredRead);
        Map<String, Object> projectedRead = edge(retrieve, "HEAP_READ",
                "instance_field_read", receiverMap, map, 1);
        authoritativeValueFlow(projectedRead);
        projectedRead.put("siteId", declaredRead.get("siteId"));
        edges.add(projectedRead);
        Map<String, Object> boxOperand = edge(retrieve, "FUNCTION_RETURN",
                "local_def_use", key, boxed, 2);
        authoritativeValueFlow(boxOperand);
        edges.add(boxOperand);
        Map<String, Object> boxReturn = edge(retrieve, "FUNCTION_RETURN",
                "call_return", "<java.lang.Integer: java.lang.Integer valueOf(int)>.return",
                boxed, 2);
        authoritativeValueFlow(boxReturn);
        boxReturn.put("siteId", boxOperand.get("siteId"));
        edges.add(boxReturn);
        Map<String, Object> lookupState = edge(retrieve, "HEAP_LOOKUP",
                "map_lookup_state", map, lookup, 3);
        authoritativeValueFlow(lookupState);
        edges.add(lookupState);
        Map<String, Object> lookupKey = edge(retrieve, "HEAP_LOOKUP",
                "map_lookup_key", boxed, lookup, 3);
        authoritativeValueFlow(lookupKey);
        edges.add(lookupKey);
        Map<String, Object> mapReturn = edge(retrieve, "HEAP_LOOKUP",
                "call_return", "<java.util.Map: java.lang.Object get(java.lang.Object)>.return",
                lookup, 3);
        authoritativeValueFlow(mapReturn);
        mapReturn.put("siteId", lookupState.get("siteId"));
        edges.add(mapReturn);
        Map<String, Object> cast = edge(retrieve, "VALUE_PASS",
                "local_def_use", "(example.Key) $lookup", guard, 4);
        authoritativeValueFlow(cast);
        edges.add(cast);
        Map<String, Object> castLeaf = edge(retrieve, "VALUE_PASS",
                "local_def_use", lookup, guard, 4);
        authoritativeValueFlow(castLeaf);
        cast.put("siteId", castLeaf.get("siteId"));
        edges.add(castLeaf);
        edges.add(edge(retrieve, "GUARD", "exception_guard", guard,
                failure, 8));
        edges.add(edge(retrieve, "SEED", "seed_exception_throw",
                retrieve + "::$exception", failure, 9));
        Map<String, Object> call = invocation(root, retrieve, suppliedKey,
                key, 1);
        authoritativeValueFlow(call);
        edges.add(call);

        Map<String, Object> region = onlyRegion(SymbolicRegionPlanner.plan(
                edges, Arrays.asList(
                        plan(root, Collections.singletonList(suppliedKey),
                                Collections.<String>emptyList()),
                        plan(retrieve, Arrays.asList(key, declaredMap,
                                receiverMap), Collections.singletonList(
                                failure)))));

        assertEquals(String.valueOf(region), Boolean.TRUE,
                region.get("seedGuardInputDerivationComplete"));
        assertEquals(0, region.get("seedGuardInputDerivationGapCount"));
        assertEquals(Arrays.asList(suppliedKey, declaredMap),
                region.get("mandatorySeedGuardInputs"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        assertFalse(inputs.stream().anyMatch(input ->
                key.equals(input.get("cell"))
                        || receiverMap.equals(input.get("cell"))));
    }

    @Test
    public void sharedHeapWriterInputsBelongToProducerRegionNotConsumer() {
        String writer = "<example.NameNode: void install(example.Keys)>";
        String exported = writer + ".param0:example.Keys";
        String mutationValue = writer + "::$key";
        String retrieve = "<example.DataNode: void retrieve(example.Keys)>";
        String context = retrieve + ".param0:example.Keys";
        String key = "<example.DataNode: int requestedKey>";
        String allKeys = "<example.DataNode: java.util.Map allKeys>";
        String map = retrieve + "::$map";
        String lookup = retrieve + "::$lookup";
        String guard = retrieve + "::$guard";
        String failure = retrieve + "#u8#exception:example.MissingKey";

        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> exportedValue = edge(writer, "VALUE_PASS",
                "local_def_use", exported, mutationValue, 1);
        authoritativeValueFlow(exportedValue);
        edges.add(exportedValue);
        Map<String, Object> mutation = edge(writer, "HEAP_WRITE",
                "field_mutation", mutationValue, allKeys, 2);
        authoritativeValueFlow(mutation);
        edges.add(mutation);
        Map<String, Object> call = invocation(writer, retrieve, exported,
                context, 3);
        authoritativeValueFlow(call);
        edges.add(call);
        Map<String, Object> read = edge(retrieve, "HEAP_READ",
                "field_read", allKeys, map, 1);
        authoritativeValueFlow(read);
        edges.add(read);
        Map<String, Object> lookupState = edge(retrieve, "HEAP_LOOKUP",
                "map_lookup_state", map, lookup, 2);
        authoritativeValueFlow(lookupState);
        edges.add(lookupState);
        Map<String, Object> lookupKey = edge(retrieve, "HEAP_LOOKUP",
                "map_lookup_key", key, lookup, 2);
        authoritativeValueFlow(lookupKey);
        edges.add(lookupKey);
        Map<String, Object> guardValue = edge(retrieve, "VALUE_PASS",
                "local_def_use", lookup, guard, 3);
        authoritativeValueFlow(guardValue);
        edges.add(guardValue);
        edges.add(edge(retrieve, "GUARD", "exception_guard", guard,
                failure, 8));
        edges.add(edge(retrieve, "SEED", "seed_exception_throw",
                retrieve + "::$exception", failure, 9));

        Map<String, Object> region = onlyRegion(SymbolicRegionPlanner.plan(
                edges, Arrays.asList(
                        plan(writer, Collections.singletonList(exported),
                                Collections.singletonList(allKeys)),
                        plan(retrieve, Arrays.asList(context, key, allKeys),
                                Collections.singletonList(failure)))));

        assertEquals(Arrays.asList(key, allKeys),
                region.get("mandatorySeedGuardInputs"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        assertFalse(inputs.stream().anyMatch(input ->
                exported.equals(input.get("cell"))));
        @SuppressWarnings("unchecked")
        List<String> derived = (List<String>) region.get("derivedInputs");
        assertTrue(derived.stream().anyMatch(value ->
                value.startsWith(exported
                        + " [upstream shared-heap producer")));
    }

    @Test
    public void requestedOutputSliceUsesIndependentMethodBudget() {
        Map<String, Object> slice = helperFanoutOutputSlice(66);

        assertEquals(67, slice.get("methodCount"));
        assertEquals(256, slice.get("methodLimit"));
        assertEquals(Boolean.FALSE, slice.get("methodBudgetTruncated"));
        assertEquals(Boolean.FALSE, slice.get("truncated"));
        assertEquals(Boolean.TRUE, slice.get("structuralComplete"));
        assertEquals(Boolean.TRUE, slice.get("complete"));
    }

    @Test
    public void requestedOutputSliceMethodBudgetFailsClosed() {
        Map<String, Object> slice = helperFanoutOutputSlice(257);

        assertEquals(258, slice.get("methodCount"));
        assertEquals(256, slice.get("methodLimit"));
        assertEquals(Boolean.TRUE, slice.get("methodBudgetTruncated"));
        assertEquals(Boolean.TRUE, slice.get("truncated"));
        assertTrue(((List<?>) slice.get("truncationReasons")).contains(
                "REQUESTED_OUTPUT_METHOD_LIMIT_EXCEEDED"));
        assertEquals(Boolean.FALSE, slice.get("structuralComplete"));
        assertEquals(Boolean.FALSE, slice.get("complete"));
    }

    @Test
    public void requestedOutputBackwardCellBudgetFailsClosed() {
        String dispatch = "<example.CellBudget: void dispatch()>";
        String handshake =
                "<example.CellBudget: void handshake(java.lang.String)>";
        String receive =
                "<example.CellBudgetReceiver: void receive(java.lang.String)>";
        String seed = "<example.CellBudget: long seed>";
        String outboundValue = dispatch + "::outboundValue";
        String outbound = handshake + ".param0:java.lang.String";
        String inbound = receive + ".param0:java.lang.String";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(dispatch, Collections.singletonList(seed),
                        Collections.singletonList(outboundValue)),
                plan(handshake, Collections.singletonList(outbound),
                        Collections.singletonList(outbound)),
                plan(receive, Collections.singletonList(inbound),
                        Collections.singletonList(receive
                                + "#failure:cell-budget")));
        List<Map<String, Object>> edges = new ArrayList<>();
        String previous = seed;
        for (int index = 0; index < 20010; index++) {
            String next = index == 20009 ? outboundValue
                    : dispatch + "::$cell" + index;
            edges.add(edge(dispatch, "COMPUTE", "cell_budget_chain",
                    previous, next, 100 + index));
            previous = next;
        }
        edges.add(invocation(dispatch, handshake, outboundValue, outbound,
                30000));
        edges.add(edge(receive, "PROTOCOL_TRANSFER", "cell_budget_handoff",
                outbound, inbound, 30001));
        edges.add(edge(receive, "SEED", "seed_exception_throw", inbound,
                receive + "#failure:cell-budget", 30002));

        Map<String, Object> slice = requestedOutputSlice(
                SymbolicRegionPlanner.plan(edges, plans), dispatch, outbound);
        assertEquals(20000, slice.get("causalCellCount"));
        assertEquals(20000, slice.get("causalCellLimit"));
        assertEquals(Boolean.TRUE, slice.get(
                "causalCellBudgetTruncated"));
        assertTrue(((List<?>) slice.get("truncationReasons")).contains(
                "BACKWARD_DEPENDENCY_CELL_LIMIT_EXCEEDED"));
        assertEquals(Boolean.FALSE, slice.get("structuralComplete"));
        assertEquals(Boolean.FALSE, slice.get("complete"));
    }

    @Test
    public void outputSliceRejectsAmbiguousBareDeclaredScalarReadSites() {
        String dispatch = "<example.Client: void dispatch()>";
        String handshake =
                "<example.Client: void handshake(java.lang.String)>";
        String receive =
                "<example.Server: void receive(java.lang.String)>";
        String config = "<example.Client: example.Config config>";
        String expiry = "<example.DelegationKey: long expiryDate>";
        String first = dispatch + "::$l1";
        String second = dispatch + "::$l2";
        String userName = dispatch + "::userName";
        String outbound = handshake + ".param0:java.lang.String";
        String inbound = receive + ".param0:java.lang.String";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(dispatch, Collections.singletonList(config),
                        Collections.singletonList(userName)),
                plan(handshake, Collections.singletonList(outbound),
                        Collections.singletonList(outbound)),
                plan(receive, Collections.singletonList(inbound),
                        Collections.singletonList(receive
                                + "#failure:expired")));
        List<Map<String, Object>> edges = new ArrayList<>();
        for (int unit : Arrays.asList(11, 12)) {
            String local = unit == 11 ? first : second;
            Map<String, Object> read = edge(dispatch, "HEAP_READ",
                    "accessor_field_return", expiry, local, unit);
            read.put("siteId", dispatch + "#u" + unit);
            read.put("invoke",
                    "<example.DelegationKey: long getExpiryDate()>");
            read.put("accessorImplementationMethod",
                    "<example.DelegationKey: long getExpiryDate()>");
            read.put("accessorImplementationAuthority",
                    "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
            authoritativeValueFlow(read);
            declaredMetadata(read, expiry, "example.DelegationKey", "long",
                    "expiryDate");
            edges.add(read);
            edges.add(edge(dispatch, "COMPUTE", "local_def_use", local,
                    userName, unit + 2));
        }
        edges.add(invocation(dispatch, handshake, userName, outbound, 15));
        edges.add(edge(receive, "PROTOCOL_TRANSFER", "username_handoff",
                outbound, inbound, 16));
        edges.add(edge(receive, "SEED", "seed_exception_throw", inbound,
                receive + "#failure:expired", 17));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), dispatch);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> outbound.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);

        assertEquals(Boolean.FALSE, slice.get("complete"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).stream()
                .anyMatch(value -> String.valueOf(value).contains(expiry)
                        && String.valueOf(value).contains(
                        "output slice input has no region port")));
        assertFalse(inputCells(producer).contains(expiry));
    }

    @Test
    public void exactOutboundRpcReturnAndProjectionGainCompleteSlices() {
        String producer =
                "<example.NameNode: example.Keys getKeys(example.Keys)>";
        String consumer =
                "<example.Balancer: void update(example.Keys)>";
        String input = producer + ".param0:example.Keys";
        String keyId = "<example.Keys: int keyId>";
        String returned = producer + ".return";
        String returnedKeyId = returned + "#field:keyId";
        String received = consumer + ".param0:example.Keys";
        String receivedKeyId = received + "#field:keyId";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(producer, Collections.singletonList(input),
                        Arrays.asList(returned, returnedKeyId)),
                plan(consumer, Collections.singletonList(receivedKeyId),
                        Collections.singletonList(consumer
                                + "#failure:missingKey")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(producer, "VALUE_PASS", "local_def_use", input,
                returned, 3));
        edges.add(edge(producer, "HEAP_READ", "projected_field_read", keyId,
                returnedKeyId, 3));

        Map<String, Object> rpcReturn = edge(consumer,
                "PROTOCOL_TRANSFER", "rpc_return", returned, received, 4);
        authoritativeValueFlow(rpcReturn);
        edges.add(rpcReturn);
        Map<String, Object> projectedRpcReturn = edge(consumer,
                "PROTOCOL_TRANSFER", "projected_rpc_return",
                returnedKeyId, receivedKeyId, 4);
        authoritativeValueFlow(projectedRpcReturn);
        projectedRpcReturn.put("fieldSensitive", true);
        projectedRpcReturn.put("objectFromCell", returned);
        projectedRpcReturn.put("objectToCell", received);
        projectedRpcReturn.put("fieldPath", "#field:keyId");
        edges.add(projectedRpcReturn);
        edges.add(edge(consumer, "SEED", "seed_exception_throw",
                receivedKeyId, consumer + "#failure:missingKey", 5));

        Map<String, Object> region = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), producer);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) region.get("outputSlices");
        Map<String, Object> rawSlice = slices.stream()
                .filter(slice -> returned.equals(slice.get("outputCell")))
                .findFirst().orElseThrow(AssertionError::new);
        Map<String, Object> projectedSlice = slices.stream()
                .filter(slice -> returnedKeyId.equals(slice.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);

        assertEquals(Boolean.TRUE, rawSlice.get("complete"));
        assertEquals(Boolean.TRUE, projectedSlice.get("complete"));
        assertEquals(Boolean.FALSE,
                rawSlice.get("captureBindingsRequired"));
        assertEquals(Boolean.TRUE, rawSlice.get("captureBindingsComplete"));
        assertEquals(Boolean.FALSE,
                projectedSlice.get("captureBindingsRequired"));
        assertTrue(((List<?>) rawSlice.get("unresolvedInputs")).isEmpty());
        assertTrue(((List<?>) projectedSlice.get("unresolvedInputs")).isEmpty());
    }

    @Test
    public void aggregateRpcReturnWithoutExactProjectionFailsClosed() {
        String producer =
                "<example.NameNode: example.Keys getKeys(example.Keys)>";
        String consumer =
                "<example.Balancer: void update(example.Keys)>";
        String input = producer + ".param0:example.Keys";
        String returned = producer + ".return";
        String received = consumer + ".param0:example.Keys";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(producer, Collections.singletonList(input),
                        Collections.singletonList(returned)),
                plan(consumer, Collections.singletonList(received),
                        Collections.singletonList(consumer
                                + "#failure:missingKey")));
        Map<String, Object> rpcReturn = edge(consumer,
                "PROTOCOL_TRANSFER", "rpc_return", returned, received, 4);
        authoritativeValueFlow(rpcReturn);
        List<Map<String, Object>> edges = Arrays.asList(
                edge(producer, "VALUE_PASS", "local_def_use", input,
                        returned, 3),
                rpcReturn,
                edge(consumer, "SEED", "seed_exception_throw", received,
                        consumer + "#failure:missingKey", 5));

        Map<String, Object> region = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), producer);
        assertTrue(((List<?>) region.get("outputSlices")).isEmpty());
    }

    @Test
    public void conflictingProjectedRpcMetadataFailsClosed() {
        String producer =
                "<example.NameNode: example.Keys getKeys(example.Keys)>";
        String consumer =
                "<example.Balancer: void update(example.Keys)>";
        String input = producer + ".param0:example.Keys";
        String returned = producer + ".return";
        String returnedKeyId = returned + "#field:keyId";
        String received = consumer + ".param0:example.Keys";
        String receivedKeyId = received + "#field:keyId";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(producer, Collections.singletonList(input),
                        Arrays.asList(returned, returnedKeyId)),
                plan(consumer, Collections.singletonList(receivedKeyId),
                        Collections.singletonList(consumer
                                + "#failure:missingKey")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(producer, "VALUE_PASS", "local_def_use", input,
                returned, 1));
        Map<String, Object> raw = edge(consumer, "PROTOCOL_TRANSFER",
                "rpc_return", returned, received, 2);
        authoritativeValueFlow(raw);
        edges.add(raw);
        Map<String, Object> exact = edge(consumer, "PROTOCOL_TRANSFER",
                "projected_rpc_return", returnedKeyId, receivedKeyId, 2);
        authoritativeValueFlow(exact);
        exact.put("fieldSensitive", true);
        exact.put("objectFromCell", returned);
        exact.put("objectToCell", received);
        exact.put("fieldPath", "#field:keyId");
        edges.add(exact);
        Map<String, Object> conflict = edge(consumer,
                "PROTOCOL_TRANSFER", "projected_rpc_return",
                returnedKeyId, consumer + "::other#field:keyId", 3);
        authoritativeValueFlow(conflict);
        conflict.put("fieldSensitive", true);
        conflict.put("objectFromCell", producer + "::notTheReturn");
        conflict.put("objectToCell", consumer + "::other");
        conflict.put("fieldPath", "#field:keyId");
        edges.add(conflict);
        edges.add(edge(consumer, "SEED", "seed_exception_throw",
                receivedKeyId, consumer + "#failure:missingKey", 4));

        Map<String, Object> region = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), producer);
        assertTrue(((List<?>) region.get("outputSlices")).isEmpty());
    }

    @Test
    public void projectedIncomingRpcValueUsesItsExactRawCarrier() {
        String upstream = "<example.Server: example.WireKeys rpc()>";
        String root = "<example.Client: example.Keys convert()>";
        String downstream =
                "<example.Balancer: void update(example.Keys)>";
        String upstreamReturn = upstream + ".return";
        String upstreamKeyId = upstreamReturn + "#field:keyId";
        String wireLocal = root + "::$r2";
        String wireKeyId = wireLocal + "#field:keyId";
        String returned = root + ".return";
        String returnedKeyId = returned + "#field:keyId";
        String received = downstream + ".param0:example.Keys";
        String receivedKeyId = received + "#field:keyId";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, Arrays.asList(wireLocal, wireKeyId),
                        Arrays.asList(returned, returnedKeyId)),
                plan(downstream, Collections.singletonList(receivedKeyId),
                        Collections.singletonList(downstream
                                + "#failure:missingKey")));
        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> incoming = edge(root, "PROTOCOL_TRANSFER",
                "rpc_return", upstreamReturn, wireLocal, 1);
        authoritativeValueFlow(incoming);
        edges.add(incoming);
        Map<String, Object> incomingProjection = edge(root,
                "PROTOCOL_TRANSFER", "projected_rpc_return",
                upstreamKeyId, wireKeyId, 1);
        authoritativeValueFlow(incomingProjection);
        incomingProjection.put("fieldSensitive", true);
        incomingProjection.put("objectFromCell", upstreamReturn);
        incomingProjection.put("objectToCell", wireLocal);
        incomingProjection.put("fieldPath", "#field:keyId");
        edges.add(incomingProjection);
        edges.add(edge(root, "VALUE_PASS", "local_def_use", wireLocal,
                returned, 2));
        edges.add(edge(root, "VALUE_PASS", "projected_local_def_use",
                wireKeyId, returnedKeyId, 2));

        Map<String, Object> outgoing = edge(downstream,
                "PROTOCOL_TRANSFER", "rpc_return", returned, received, 3);
        authoritativeValueFlow(outgoing);
        edges.add(outgoing);
        Map<String, Object> outgoingProjection = edge(downstream,
                "PROTOCOL_TRANSFER", "projected_rpc_return",
                returnedKeyId, receivedKeyId, 3);
        authoritativeValueFlow(outgoingProjection);
        outgoingProjection.put("fieldSensitive", true);
        outgoingProjection.put("objectFromCell", returned);
        outgoingProjection.put("objectToCell", received);
        outgoingProjection.put("fieldPath", "#field:keyId");
        edges.add(outgoingProjection);
        edges.add(edge(downstream, "SEED", "seed_exception_throw",
                receivedKeyId, downstream + "#failure:missingKey", 4));

        Map<String, Object> region = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), root);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) region.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> returnedKeyId.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Boolean.TRUE, slice.get("complete"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        Map<String, Object> projectedBinding = bindings.stream()
                .filter(binding -> wireKeyId.equals(binding.get(
                        "dependencyCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("UNIQUE_EXACT_PROJECTED_VALUE_CARRIER",
                projectedBinding.get("bindingAuthority"));
        String carrierPort = String.valueOf(projectedBinding.get(
                "inputPort"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> ports =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        assertTrue(ports.stream().anyMatch(port ->
                carrierPort.equals(port.get("portId"))
                        && wireLocal.equals(port.get("cell"))));
        assertFalse(((List<?>) slice.get("inputPorts")).stream()
                .anyMatch(port -> ports.stream().anyMatch(candidate ->
                        port.equals(candidate.get("portId"))
                                && wireKeyId.equals(candidate.get("cell")))));
    }

    @Test
    public void projectedGetterLocalUsesCanonicalDeclaredFieldAliasChain() {
        String upstream = "<example.NameNode: example.Keys publish()>";
        String root = "<example.DataNode: void receive()>";
        String getter = "<example.Command: example.Keys getKeys()>";
        String reader = "<example.Reader: void check()>";
        String carrier = "<example.Command: example.Keys keys>";
        String path = "#field:allKeys";
        String getterLocal = getter + "::r1";
        String returned = getter + ".return";
        String received = root + "::$r59";
        String output = "<example.Secret: java.util.Map allKeys>";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, Arrays.asList(received + path,
                                carrier, carrier + path),
                        Collections.singletonList(output)),
                plan(getter, Arrays.asList(carrier, carrier + path),
                        Arrays.asList(returned, returned + path)),
                plan(reader, Collections.singletonList(output),
                        Collections.singletonList(reader
                                + "#failure:missing")));
        List<Map<String, Object>> edges = new ArrayList<>();

        Map<String, Object> rawField = edge(getter, "HEAP_READ",
                "field_read", carrier, getterLocal, 1);
        authoritativeValueFlow(rawField);
        edges.add(rawField);
        edges.add(projectedAliasProof(getter, "HEAP_READ",
                "projected_field_read", carrier, getterLocal, path, 1));

        Map<String, Object> rawReturn = edge(getter, "VALUE_PASS",
                "local_def_use", getterLocal, returned, 2);
        authoritativeDirectCopyBase(rawReturn, "RETURN_LOCAL");
        edges.add(rawReturn);
        Map<String, Object> projectedLocalReturn =
                projectedDirectCopyProof(rawReturn, path);
        edges.add(projectedLocalReturn);

        Map<String, Object> callReturn = edge(root, "FUNCTION_RETURN",
                "call_return", returned, received, 3);
        authoritativeValueFlow(callReturn);
        callReturn.put("invoke", getter);
        edges.add(callReturn);
        Map<String, Object> projectedReturn = projectedAliasProof(root,
                "FUNCTION_RETURN", "projected_call_return", returned,
                received, path, 3);
        projectedReturn.put("invoke", getter);
        edges.add(projectedReturn);

        Map<String, Object> inboundProjection = projectedAliasProof(root,
                "PROTOCOL_TRANSFER", "projected_heartbeat_payload",
                upstream + ".return", received, path, 4);
        edges.add(inboundProjection);

        edges.add(edge(root, "HEAP_WRITE", "field_mutation",
                received + path, output, 5));
        edges.add(edge(reader, "HEAP_READ", "field_read", output,
                reader + "::allKeys", 1));
        edges.add(edge(reader, "SEED", "seed_exception_throw",
                reader + "::allKeys", reader + "#failure:missing", 2));

        Map<String, Object> region = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), root);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) region.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> output.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(String.valueOf(slice), Boolean.TRUE,
                slice.get("complete"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).isEmpty());

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        Map<String, Object> binding = bindings.stream()
                .filter(candidate -> (received + path).equals(candidate.get(
                        "dependencyCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN",
                binding.get("bindingAuthority"));
        String port = String.valueOf(binding.get("inputPort"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        assertTrue(inputs.stream().anyMatch(input ->
                port.equals(input.get("portId"))
                        && (carrier + path).equals(input.get("cell"))));

        // A synthetic projected local copy has no authority on its own.  Its
        // producer references must resolve to exactly one intact raw proof.
        List<Map<String, Object>> missingBaseEdges = copiedEdges(edges);
        missingBaseEdges.removeIf(candidate -> String.valueOf(
                rawReturn.get("id")).equals(candidate.get("id")));
        assertProjectedDependencyUnresolved(missingBaseEdges, plans, root,
                output, received + path);

        List<Map<String, Object>> missingReferenceEdges = copiedEdges(edges);
        edgeById(missingReferenceEdges, String.valueOf(
                projectedLocalReturn.get("id"))).remove(
                "baseValueFlowEdgeId");
        assertProjectedDependencyUnresolved(missingReferenceEdges, plans,
                root, output, received + path);

        List<Map<String, Object>> tamperedReferenceEdges = copiedEdges(edges);
        edgeById(tamperedReferenceEdges, String.valueOf(
                projectedLocalReturn.get("id"))).put(
                "projectionBaseEdgeId", "DF.TEST.tampered");
        assertProjectedDependencyUnresolved(tamperedReferenceEdges, plans,
                root, output, received + path);

        List<Map<String, Object>> forgedProjectedLabelEdges =
                copiedEdges(edges);
        edgeById(forgedProjectedLabelEdges, String.valueOf(
                projectedLocalReturn.get("id"))).put("valueFlowAuthority",
                "SOOT_EXACT_LOCAL_DIRECT_COPY_V1");
        assertProjectedDependencyUnresolved(forgedProjectedLabelEdges, plans,
                root, output, received + path);

        List<Map<String, Object>> forgedBaseLabelEdges = copiedEdges(edges);
        edgeById(forgedBaseLabelEdges, String.valueOf(rawReturn.get("id")))
                .put("valueFlowAuthority", "FORGED_DIRECT_COPY");
        assertProjectedDependencyUnresolved(forgedBaseLabelEdges, plans,
                root, output, received + path);

        // Even correctly-spelled labels do not prove a base with different
        // aggregate endpoints, and duplicate IDs do not prove uniqueness.
        List<Map<String, Object>> forgedBaseShapeEdges = copiedEdges(edges);
        edgeById(forgedBaseShapeEdges, String.valueOf(rawReturn.get("id")))
                .put("fromCell", getter + "::forged");
        assertProjectedDependencyUnresolved(forgedBaseShapeEdges, plans,
                root, output, received + path);

        List<Map<String, Object>> duplicateBaseEdges = copiedEdges(edges);
        duplicateBaseEdges.add(new LinkedHashMap<>(edgeById(
                duplicateBaseEdges, String.valueOf(rawReturn.get("id")))));
        assertProjectedDependencyUnresolved(duplicateBaseEdges, plans, root,
                output, received + path);

        String alternative =
                "<example.OtherCommand: example.OtherKeys backupKeys>";
        List<Map<String, Object>> ambiguousPlans = Arrays.asList(
                plan(root, Arrays.asList(received + path, carrier,
                                carrier + path, alternative + path),
                        Collections.singletonList(output)),
                plan(getter, Arrays.asList(carrier, carrier + path,
                                alternative + path),
                        Arrays.asList(returned, returned + path)),
                plan(reader, Collections.singletonList(output),
                        Collections.singletonList(reader
                                + "#failure:missing")));
        List<Map<String, Object>> ambiguousEdges = new ArrayList<>(edges);
        ambiguousEdges.add(projectedAliasProof(getter, "HEAP_READ",
                "projected_field_read", alternative, getterLocal, path, 1));
        Map<String, Object> ambiguousRegion = regionForRoot(
                SymbolicRegionPlanner.plan(ambiguousEdges, ambiguousPlans),
                root);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> ambiguousSlices =
                (List<Map<String, Object>>) ambiguousRegion.get(
                        "outputSlices");
        Map<String, Object> ambiguousSlice = ambiguousSlices.stream()
                .filter(candidate -> output.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Boolean.FALSE, ambiguousSlice.get("complete"));
        assertTrue(((List<?>) ambiguousSlice.get("unresolvedInputs"))
                .stream().anyMatch(value -> String.valueOf(value).contains(
                        received + path)));

        // A projected row with boundary semantics is never an in-region
        // alias proof, even when its endpoints happen to match the local
        // carrier chain exactly.
        List<Map<String, Object>> boundaryEdges = copiedEdges(edges);
        Map<String, Object> boundaryAlias = edgeById(boundaryEdges,
                String.valueOf(projectedReturn.get("id")));
        boundaryAlias.put("kind", "projected_rpc_return");
        assertProjectedDependencyUnresolved(boundaryEdges, plans, root,
                output, received + path);

        // Field-sensitive shape alone is insufficient: every traversed row
        // must retain automatic value-flow authority.
        List<Map<String, Object>> nonExactEdges = copiedEdges(edges);
        Map<String, Object> nonExactAlias = edgeById(nonExactEdges,
                String.valueOf(projectedReturn.get("id")));
        nonExactAlias.put("eligibleForAutomaticDerivation", false);
        assertProjectedDependencyUnresolved(nonExactEdges, plans, root,
                output, received + path);

        // The path fixed at the requested dependency is invariant across the
        // complete chain.  A row that changes it cannot be used as an alias.
        List<Map<String, Object>> mismatchedPathEdges = copiedEdges(edges);
        Map<String, Object> mismatchedPathAlias = edgeById(
                mismatchedPathEdges,
                String.valueOf(projectedReturn.get("id")));
        mismatchedPathAlias.put("fieldPath", "#field:keyIds");
        assertProjectedDependencyUnresolved(mismatchedPathEdges, plans,
                root, output, received + path);

        // Uniqueness may not be claimed from a bounded prefix of a longer
        // alias graph.  Replace the direct call-return projection with a
        // chain longer than the planner worklist proof bound.
        List<Map<String, Object>> overBoundEdges = copiedEdges(edges);
        overBoundEdges.removeIf(candidate -> String.valueOf(
                projectedReturn.get("id")).equals(candidate.get("id")));
        String previous = root + "::aliasStart";
        overBoundEdges.add(projectedAliasProof(root, "FUNCTION_RETURN",
                "projected_call_return", returned, previous, path, 99));
        for (int i = 0; i < 140; i++) {
            String next = i == 139 ? received : root + "::alias" + i;
            Map<String, Object> rawCopy = edge(root, "VALUE_PASS",
                    "local_def_use", previous, next, 100 + i);
            authoritativeDirectCopyBase(rawCopy, "LOCAL_ASSIGN_LOCAL");
            overBoundEdges.add(rawCopy);
            overBoundEdges.add(projectedDirectCopyProof(rawCopy, path));
            previous = next;
        }
        assertProjectedDependencyUnresolved(overBoundEdges, plans, root,
                output, received + path);
    }

    @Test
    public void projectedGetterAliasResolvesCanonicalPortPromotedLaterInSlice() {
        String root = "<example.DataNode: void receive()>";
        String carrier =
                "<example.KeyUpdateCommand: example.Keys keys>";
        String dependency = root + "::$r59#field:allKeys";
        String output = "<example.A0Secret: java.util.Map allKeys>";

        Map<String, Object> region = latePromotedGetterAliasRegion(false);
        assertEquals(128, region.get("broadInputPortCount"));
        assertEquals(Boolean.TRUE, region.get("broadInputPortTruncated"));

        Map<String, Object> slice = requestedOutputSlice(region, output);
        assertEquals(String.valueOf(slice), Boolean.TRUE,
                slice.get("complete"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).isEmpty());

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        Map<String, Object> binding = bindings.stream()
                .filter(candidate -> dependency.equals(candidate.get(
                        "dependencyCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN",
                binding.get("bindingAuthority"));

        String port = String.valueOf(binding.get("inputPort"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        Map<String, Object> canonical = inputs.stream()
                .filter(input -> port.equals(input.get("portId")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(carrier + "#field:allKeys", canonical.get("cell"));
        assertEquals("REQUESTED_OUTPUT_FRONTIER_PROMOTION",
                canonical.get("portOrigin"));
    }

    @Test
    public void lateCompetingCanonicalPortInvalidatesEarlierAliasUniqueness() {
        String root = "<example.DataNode: void receive()>";
        String dependency = root + "::$r59#field:allKeys";
        String output = "<example.A0Secret: java.util.Map allKeys>";
        String first = "<example.Command: example.Keys keys>"
                + "#field:allKeys";
        String second = "<example.KeyUpdateCommand: example.Keys keys>"
                + "#field:allKeys";

        Map<String, Object> region = latePromotedGetterAliasRegion(true);
        Map<String, Object> slice = requestedOutputSlice(region, output);
        assertEquals(Boolean.FALSE, slice.get("complete"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).stream()
                .anyMatch(value -> String.valueOf(value).contains(
                        dependency)));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        assertFalse(bindings.stream().anyMatch(candidate -> dependency.equals(
                candidate.get("dependencyCell"))));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        assertTrue(inputs.stream().anyMatch(input -> first.equals(
                input.get("cell")) && "REQUESTED_OUTPUT_FRONTIER_PROMOTION"
                .equals(input.get("portOrigin"))));
        assertTrue(inputs.stream().anyMatch(input -> second.equals(
                input.get("cell")) && "REQUESTED_OUTPUT_FRONTIER_PROMOTION"
                .equals(input.get("portOrigin"))));
    }

    @Test
    public void outboundProtocolStreamSinkDoesNotGainDemandSlice() {
        String send = "<example.Client: void send(java.io.OutputStream)>";
        String receive = "<example.Server: void receive(java.io.InputStream)>";
        String outbound = send + ".param0:java.io.OutputStream";
        String inbound = receive + ".param0:java.io.InputStream";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(send, Collections.singletonList(outbound),
                        Collections.singletonList(outbound)),
                plan(receive, Collections.singletonList(inbound),
                        Collections.singletonList(receive
                                + "#failure:closed")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(receive, "PROTOCOL_TRANSFER", "stream_handoff",
                        outbound, inbound, 1),
                edge(receive, "SEED", "seed_exception_throw", inbound,
                        receive + "#failure:closed", 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producer = regionForRoot(result, send);
        assertTrue(((List<?>) producer.get("outputSlices")).isEmpty());
        assertTrue(result.regionEdges.stream().anyMatch(regionEdge ->
                outbound.equals(regionEdge.get("fromPort"))
                        && inbound.equals(regionEdge.get("toPort"))));
    }

    @Test
    public void unresolvedOutboundProtocolScalarSliceRemainsIncomplete() {
        String send = "<example.Client: void send(java.lang.String)>";
        String receive = "<example.Server: void receive(java.lang.String)>";
        String unknown = "opaque.external.value";
        String outbound = send + ".param0:java.lang.String";
        String inbound = receive + ".param0:java.lang.String";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(send, Collections.singletonList(unknown),
                        Collections.singletonList(outbound)),
                plan(receive, Collections.singletonList(inbound),
                        Collections.singletonList(receive
                                + "#failure:unknownUser")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(send, "VALUE_PASS", "local_def_use", unknown,
                        outbound, 1),
                edge(receive, "PROTOCOL_TRANSFER", "username_handoff",
                        outbound, inbound, 2),
                edge(receive, "SEED", "seed_exception_throw", inbound,
                        receive + "#failure:unknownUser", 3));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producer = regionForRoot(result, send);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        assertEquals(1, slices.size());
        assertEquals(Boolean.FALSE, slices.get(0).get("complete"));
        assertTrue(String.valueOf(slices.get(0).get("unresolvedInputs"))
                .contains(unknown));
    }

    @Test
    public void scalarAndIteratorOutputGuardsAreConservativelyExplored() {
        String compute = "<example.Producer: int compute(java.lang.Boolean)>";
        String booleanValue =
                "<java.lang.Boolean: boolean booleanValue()>.return";
        String hasNext =
                "<java.util.Iterator: boolean hasNext()>.return";
        String valuePredicate = compute + "::$z0";
        String iteratorPredicate = compute + "::$z1";
        String valueResult = compute + "::valueResult";
        String iteratorResult = compute + "::iteratorResult";

        List<Map<String, Object>> plans = Collections.singletonList(
                plan(compute, Arrays.asList(booleanValue, hasNext),
                        Arrays.asList(valuePredicate, iteratorPredicate,
                                valueResult, iteratorResult,
                                compute + ".return")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(compute, "FUNCTION_RETURN", "call_return",
                booleanValue, valuePredicate, 1));
        Map<String, Object> valueGuard = edge(compute, "GUARD",
                "path_guard_dependency", valuePredicate, valueResult, 2);
        valueGuard.put("requiredOutcome", false);
        edges.add(valueGuard);

        edges.add(edge(compute, "FUNCTION_RETURN", "call_return",
                hasNext, iteratorPredicate, 3));
        Map<String, Object> iteratorGuard = edge(compute, "GUARD",
                "path_guard_dependency", iteratorPredicate, iteratorResult,
                4);
        iteratorGuard.put("requiredOutcome", true);
        edges.add(iteratorGuard);

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), compute);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> policies =
                (List<Map<String, Object>>) producer.get("branchPolicies");
        Map<String, Object> valuePolicy = policies.stream()
                .filter(policy -> Integer.valueOf(2).equals(
                        policy.get("unitIndex")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("EXPLORE", valuePolicy.get("policy"));
        assertEquals(Boolean.FALSE, valuePolicy.get("requiredOutcome"));
        Map<String, Object> iteratorPolicy = policies.stream()
                .filter(policy -> Integer.valueOf(4).equals(
                        policy.get("unitIndex")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("EXPLORE", iteratorPolicy.get("policy"));
        assertEquals(Boolean.TRUE, iteratorPolicy.get("requiredOutcome"));
    }

    @Test
    public void sameCellPathGuardExploresScalarInputRedefinition() {
        String compute = "<example.Producer: int clampAndAdd(int)>";
        String input = compute + ".param0:int";
        String value = compute + "::value";
        String output = compute + ".return";

        List<Map<String, Object>> plans = Collections.singletonList(
                plan(compute, Collections.singletonList(input),
                        Collections.singletonList(output)));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(compute, "IDENTITY_BINDING", "local_def_use",
                input, value, 0));
        Map<String, Object> genericGuard = edge(compute, "GUARD",
                "guard_dependency", value, compute + "#u1", 1);
        genericGuard.put("siteId", compute + "#u1");
        edges.add(genericGuard);
        Map<String, Object> guard = edge(compute, "GUARD",
                "path_guard_dependency", value, value, 1);
        guard.put("siteId", compute + "#u1");
        guard.put("requiredOutcome", false);
        guard.put("sameCellRedefinition", true);
        guard.put("controlledDefinitionSiteId", compute + "#u2");
        edges.add(guard);
        edges.add(edge(compute, "VALUE_PASS", "local_def_use",
                value, output, 3));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), compute);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> policies =
                (List<Map<String, Object>>) producer.get("branchPolicies");
        Map<String, Object> policy = policies.stream()
                .filter(candidate -> Integer.valueOf(1).equals(
                        candidate.get("unitIndex")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "same-cell scalar guard missing from region"));
        assertEquals("EXPLORE", policy.get("policy"));
        assertEquals(Boolean.FALSE, policy.get("requiredOutcome"));
    }

    @Test
    public void oneBranchSiteAggregatesOppositeControlledDefinitions() {
        String compute = "<example.Producer: int choose(boolean)>";
        String input = compute + ".param0:boolean";
        String predicate = compute + "::$z0";
        String trueDefinition = compute + "::trueDefinition";
        String falseDefinition = compute + "::falseDefinition";

        List<Map<String, Object>> plans = Collections.singletonList(
                plan(compute, Collections.singletonList(input),
                        Arrays.asList(trueDefinition, falseDefinition)));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(compute, "VALUE_PASS", "local_def_use",
                input, predicate, 0));
        Map<String, Object> trueGuard = edge(compute, "GUARD",
                "path_guard_dependency", predicate, trueDefinition, 1);
        trueGuard.put("requiredOutcome", true);
        trueGuard.put("reachingSuccessorIndices",
                Collections.singletonList(1));
        edges.add(trueGuard);
        Map<String, Object> falseGuard = edge(compute, "GUARD",
                "path_guard_dependency", predicate, falseDefinition, 1);
        falseGuard.put("requiredOutcome", false);
        falseGuard.put("reachingSuccessorIndices",
                Collections.singletonList(0));
        edges.add(falseGuard);

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), compute);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> policies =
                (List<Map<String, Object>>) producer.get("branchPolicies");
        assertEquals(1, policies.size());
        Map<String, Object> policy = policies.get(0);
        assertEquals("EXPLORE", policy.get("policy"));
        assertEquals(null, policy.get("requiredOutcome"));
        assertEquals(Arrays.asList(0, 1),
                policy.get("requiredSuccessorIndices"));
        assertEquals(2, ((List<?>) policy.get("sourceEdgeIds")).size());
        assertEquals("STATIC_OUTPUT_CONTROL_DEPENDENCE_REQUIRES_"
                        + "EXPLORATION_V1",
                policy.get("policyAuthority"));
    }

    @Test
    public void expiryControlledHeapMutationIsExploredAndClosedToInputs() {
        String prune = "<example.KeyManager: void prune()>";
        String reader = "<example.Reader: void read()>";
        String allKeys = "<example.KeyManager: java.util.Map allKeys>";
        String expiry = "<example.DelegationKey: long expiryDate>";
        String now = "<org.apache.hadoop.util.Time: long now()>.return";
        String hasNext = "<java.util.Iterator: boolean hasNext()>.return";
        String l1 = prune + "::$l1";
        String l0 = prune + "::$l0";
        String compare = prune + "::$b2";
        String predicate = prune + "::$i3";
        String loopPredicate = prune + "::$z0";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(prune, Arrays.asList(allKeys, expiry, now, hasNext),
                        Arrays.asList(allKeys, l1, l0, compare, predicate,
                                loopPredicate)),
                plan(reader, Collections.singletonList(allKeys),
                        Collections.singletonList(reader
                                + "#failure:missing")));
        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> read = edge(reader, "HEAP_READ", "field_read",
                allKeys, reader + "::keys", 1);
        read.put("id", "DF.READ");
        edges.add(read);
        Map<String, Object> seed = edge(reader, "SEED", "seed",
                reader + "::keys", reader + "#failure:missing", 2);
        seed.put("id", "DF.SEED");
        edges.add(seed);

        Map<String, Object> mutation = edge(prune, "HEAP_WRITE",
                "field_mutation", prune + "#u15", allKeys, 15);
        mutation.put("id", "DF.REMOVE");
        mutation.put("siteId", prune + "#u15");
        edges.add(mutation);
        Map<String, Object> loopGuard = edge(prune, "GUARD",
                "heap_mutation_path_guard", loopPredicate, allKeys, 6);
        loopGuard.put("id", "DF.LOOP.GUARD");
        loopGuard.put("siteId", prune + "#u6");
        loopGuard.put("unit", "if $z0 == 0 goto return");
        loopGuard.put("requiredOutcome", false);
        addGuardedMutationContract(loopGuard, prune + "#u15", prune,
                15, false);
        edges.add(loopGuard);
        Map<String, Object> expiryGuard = edge(prune, "GUARD",
                "heap_mutation_path_guard", predicate, allKeys, 14);
        expiryGuard.put("id", "DF.EXPIRY.GUARD");
        expiryGuard.put("siteId", prune + "#u14");
        expiryGuard.put("unit", "if $i3 >= 0 goto loop");
        expiryGuard.put("requiredOutcome", false);
        addGuardedMutationContract(expiryGuard, prune + "#u15", prune,
                15, false);
        edges.add(expiryGuard);

        Map<String, Object> expiryRead = edge(prune, "HEAP_READ",
                "accessor_field_return", expiry, l1, 11);
        expiryRead.put("id", "DF.EXPIRY.READ");
        edges.add(expiryRead);
        Map<String, Object> nowRead = edge(prune, "FUNCTION_RETURN",
                "caller_return", now, l0, 1);
        nowRead.put("id", "DF.NOW");
        edges.add(nowRead);
        Map<String, Object> compareExpiry = edge(prune, "COMPUTE",
                "local_def_use", l1, compare, 12);
        compareExpiry.put("id", "DF.CMP.EXPIRY");
        edges.add(compareExpiry);
        Map<String, Object> compareNow = edge(prune, "COMPUTE",
                "local_def_use", l0, compare, 12);
        compareNow.put("id", "DF.CMP.NOW");
        edges.add(compareNow);
        Map<String, Object> cast = edge(prune, "VALUE_PASS",
                "local_def_use", compare, predicate, 13);
        cast.put("id", "DF.CMP.CAST");
        edges.add(cast);
        Map<String, Object> iterator = edge(prune, "FUNCTION_RETURN",
                "call_return", hasNext, loopPredicate, 5);
        iterator.put("id", "DF.HAS_NEXT");
        edges.add(iterator);

        SymbolicRegionPlanner.Result planned = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producer = regionForRoot(planned, prune);
        List<String> inputs = inputCells(producer);
        assertTrue(inputs.contains(allKeys));
        assertTrue(inputs.contains(expiry));
        assertTrue(inputs.contains(now));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> policies =
                (List<Map<String, Object>>) producer.get("branchPolicies");
        Map<String, Object> expiryPolicy = policies.stream()
                .filter(policy -> Integer.valueOf(14).equals(
                        policy.get("unitIndex")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing expiry policy"));
        assertEquals("EXPLORE", expiryPolicy.get("policy"));
        assertEquals(Boolean.FALSE, expiryPolicy.get("requiredOutcome"));
        Map<String, Object> loopPolicy = policies.stream()
                .filter(policy -> Integer.valueOf(6).equals(
                        policy.get("unitIndex")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing loop policy"));
        assertEquals("EXPLORE", loopPolicy.get("policy"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> allKeys.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Boolean.TRUE, slice.get("complete"));
        assertEquals(1,
                slice.get("requestedStateTransformerContractVersion"));
        assertEquals(Boolean.TRUE, slice.get(
                "requestedStateTransformerContractComplete"));
        assertEquals(1,
                slice.get("requestedStateTransformerObligationCount"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> transformers =
                (List<Map<String, Object>>) slice.get(
                        "requestedStateTransformerObligations");
        assertEquals(prune + "#u15", transformers.get(0).get("siteId"));
        assertEquals(allKeys, transformers.get(0).get("targetCell"));
        assertEquals("STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL",
                transformers.get(0).get("authority"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        Map<String, Object> expiryBinding = bindings.stream()
                .filter(binding -> expiry.equals(binding.get(
                        "dependencyCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Collections.singletonList(prune + "#u15"),
                expiryBinding.get("requestedStateTransformerSinkSites"));
        assertEquals(Collections.singletonList(prune + "#u14"),
                expiryBinding.get("requestedStateTransformerGuardSites"));
        assertEquals(Boolean.TRUE, expiryBinding.get(
                "requestedStateTransformerSinkClosureComplete"));
        assertEquals(Boolean.TRUE, expiryBinding.get(
                "requestedStateTransformerSinkExclusive"));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> causalReferences =
                (List<Map<String, Object>>) slice.get("causalEdges");
        Map<String, Object> outerGuardReference = causalReferences.stream()
                .filter(reference -> "DF.LOOP.GUARD".equals(reference.get(
                        "edgeId")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(prune + "#u6",
                outerGuardReference.get("guardSiteId"));
        assertEquals(1,
                outerGuardReference.get("guardedMutationCount"));
        assertEquals(1, ((List<?>) outerGuardReference.get(
                "guardedMutations")).size());
        @SuppressWarnings("unchecked")
        List<String> causalIds = (List<String>) slice.get("causalEdgeIds");
        assertTrue(causalIds.containsAll(Arrays.asList(
                "DF.REMOVE", "DF.EXPIRY.GUARD", "DF.EXPIRY.READ",
                "DF.NOW", "DF.CMP.EXPIRY", "DF.CMP.NOW",
                "DF.CMP.CAST")));
    }

    private static void addGuardedMutationContract(
            Map<String, Object> guard, String mutationSite, String method,
            int mutationUnitIndex, boolean requiredOutcome) {
        String guardSite = String.valueOf(guard.get("siteId"));
        guard.put("guardSiteId", guardSite);
        guard.put("guardedMutationSiteId", mutationSite);
        guard.put("guardedMutationCount", 1);
        guard.put("guardedMutationsAuthority",
                "STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE");
        Map<String, Object> mutation = new LinkedHashMap<>();
        mutation.put("guardSiteId", guardSite);
        mutation.put("guardedMutationSiteId", mutationSite);
        mutation.put("method", method);
        mutation.put("unitIndex", mutationUnitIndex);
        mutation.put("requiredOutcome", requiredOutcome);
        guard.put("guardedMutations",
                Collections.singletonList(mutation));
    }

    @Test
    public void exactTransformerContractIgnoresCausalOtherFieldWriteAndVoidHelper() {
        String update = "<example.KeyManager: void update(int,boolean)>";
        String refresh = "<example.KeyManager: void refresh(boolean)>";
        String reader = "<example.Reader: void read()>";
        String key = update + ".param0:int";
        String config = update + ".param1:boolean";
        String refreshFlag = refresh + ".param0:boolean";
        String configured = "<example.KeyManager: boolean configured>";
        String gate = update + "::$z0";
        String allKeys = "<example.KeyManager: java.util.Map allKeys>";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(update, Arrays.asList(key, config, configured),
                        Arrays.asList(gate, allKeys)),
                plan(refresh, Collections.singletonList(refreshFlag),
                        Collections.singletonList(configured)),
                plan(reader, Collections.singletonList(allKeys),
                        Collections.singletonList(reader
                                + "#failure:missing")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(reader, "HEAP_READ", "field_read", allKeys,
                reader + "::keys", 1));
        edges.add(edge(reader, "SEED", "seed", reader + "::keys",
                reader + "#failure:missing", 2));
        edges.add(invocation(update, refresh, config, refreshFlag, 1));
        Map<String, Object> otherWrite = edge(refresh, "HEAP_WRITE",
                "field_write", refreshFlag, configured, 2);
        otherWrite.put("siteId", refresh + "#u2");
        edges.add(otherWrite);
        edges.add(edge(update, "HEAP_READ", "field_read", configured,
                gate, 3));
        Map<String, Object> exactWrite = edge(update, "HEAP_WRITE",
                "field_mutation", key, allKeys, 5);
        exactWrite.put("siteId", update + "#u5");
        edges.add(exactWrite);
        Map<String, Object> guard = edge(update, "GUARD",
                "heap_mutation_path_guard", gate, allKeys, 4);
        guard.put("siteId", update + "#u4");
        guard.put("requiredOutcome", true);
        addGuardedMutationContract(guard, update + "#u5", update, 5,
                true);
        edges.add(guard);

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), update);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> allKeys.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);

        assertEquals(Boolean.TRUE, slice.get(
                "requestedStateTransformerContractComplete"));
        assertEquals(1,
                slice.get("requestedStateTransformerObligationCount"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> obligations =
                (List<Map<String, Object>>) slice.get(
                        "requestedStateTransformerObligations");
        assertEquals(update + "#u5", obligations.get(0).get("siteId"));
        assertFalse(String.valueOf(obligations).contains(refresh + "#u2"));
        assertTrue(((List<?>) slice.get("methods")).contains(refresh));
        assertTrue(String.valueOf(slice.get("causalEdges")).contains(
                refresh + "#u2"));
    }

    @Test
    public void exactInstanceFieldTransformerPlansAssignmentRhsCapture() {
        String writer = "<example.Heartbeat: void install(example.State,java.lang.String)>";
        String reader = "<example.Reader: void read()>";
        String parameter = writer + ".param1:java.lang.String";
        String rhs = writer + "::r1";
        String field = "<example.State: java.lang.String value>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(writer, Collections.singletonList(parameter),
                        Collections.singletonList(field)),
                plan(reader, Collections.singletonList(field),
                        Collections.singletonList(reader
                                + "#failure:missing")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(writer, "IDENTITY_BINDING", "identity_binding",
                parameter, rhs, 1));
        Map<String, Object> write = edge(writer, "HEAP_WRITE",
                "field_write", rhs, field, 3);
        write.put("siteId", writer + "#u3");
        write.put("unit", "r0." + field + " = r1");
        write.put("relation", "value_flow");
        write.put("semanticAssertionsAllowed", true);
        write.put("eligibleForAutomaticSmt", true);
        edges.add(write);
        edges.add(edge(reader, "HEAP_READ", "field_read", field,
                reader + "::value", 1));
        edges.add(edge(reader, "SEED", "seed", reader + "::value",
                reader + "#failure:missing", 2));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), writer);
        @SuppressWarnings("unchecked")
        Map<String, Object> slice = ((List<Map<String, Object>>) producer.get(
                "outputSlices")).stream().filter(candidate -> field.equals(
                candidate.get("outputCell"))).findFirst()
                .orElseThrow(AssertionError::new);

        assertEquals(Boolean.TRUE, slice.get("captureBindingsRequired"));
        assertEquals(Boolean.TRUE, slice.get("captureBindingsComplete"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> captures =
                (List<Map<String, Object>>) slice.get("captureBindings");
        assertEquals(1, captures.size());
        Map<String, Object> capture = captures.get(0);
        assertEquals("FIELD_ASSIGNMENT_RHS", capture.get("captureKind"));
        assertEquals(writer, capture.get("method"));
        assertEquals(writer + "#u3", capture.get("siteId"));
        assertEquals(3, capture.get("unitIndex"));
        assertEquals(field, capture.get("fieldSignature"));
        assertEquals("r0", capture.get("fieldOwnerExpression"));
        assertEquals(writer + "::r0", capture.get("fieldOwnerCell"));
        assertEquals("example.State",
                capture.get("fieldOwnerDeclaredType"));
        assertEquals(rhs, capture.get("rhsCell"));
        assertEquals("r1", capture.get("rhsExpression"));
        assertEquals(Boolean.TRUE, capture.get("rhsRelationComplete"));
        assertEquals("STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS",
                capture.get("bindingAuthority"));
        assertEquals(0, capture.get("occurrence"));
        assertFalse(capture.containsKey("callerMethod"));
        assertFalse(capture.containsKey("calleeMethod"));
    }

    @Test
    public void readBeforeWriteProjectedFieldRemainsConservativePrestate() {
        String root = "<example.Manager: void handle(example.Node)>";
        String argument = root + ".param0:example.Node";
        String needUpdate = argument + "#field:needUpdate";
        String observed = root + "::$z0";
        String failure = root + "#u3#exception:example.StaleState";
        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Arrays.asList(argument, needUpdate),
                        Arrays.asList(needUpdate, observed, failure)));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(root, "HEAP_READ", "field_read", needUpdate,
                observed, 2));
        edges.add(edge(root, "SEED", "seed_exception_throw", observed,
                failure, 3));
        edges.add(edge(root, "HEAP_WRITE", "field_write", root + "#u5",
                needUpdate, 5));

        Map<String, Object> region = onlyRegion(
                SymbolicRegionPlanner.plan(edges, plans));
        assertTrue(inputCells(region).contains(needUpdate));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        assertTrue(inputs.stream().anyMatch(input ->
                needUpdate.equals(input.get("cell"))
                        && "MUTABLE_HEAP_PRESTATE_FRONTIER".equals(
                        input.get("selectionReason"))));
        assertFalse(String.valueOf(region.get("derivedInputs")).contains(
                needUpdate
                        + " [field is initialized by an object construction"));
    }

    @Test
    public void provenDominatingWriteBeforeAllReadsCanElidePrestate() {
        String root = "<example.Builder: void build(example.Node)>";
        String argument = root + ".param0:example.Node";
        String initialized = argument + "#field:initialized";
        String observed = root + "::$z0";
        String failure = root + "#u3#exception:example.BadBuild";
        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Arrays.asList(argument, initialized),
                        Arrays.asList(initialized, observed, failure)));
        Map<String, Object> write = edge(root, "HEAP_WRITE",
                "field_write", root + "#u1", initialized, 1);
        Map<String, Object> read = edge(root, "HEAP_READ", "field_read",
                initialized, observed, 2);
        write.put("fieldWriteDominatesAllReads", true);
        write.put("dominatedFieldReadSiteIds",
                Collections.singletonList(read.get("siteId")));
        write.put("fieldMustDefAuthority",
                "STATIC_CFG_DOMINANCE_AND_PROGRAM_ORDER");
        List<Map<String, Object>> edges = Arrays.asList(
                write, read,
                edge(root, "SEED", "seed_exception_throw", observed,
                        failure, 3));

        Map<String, Object> region = onlyRegion(
                SymbolicRegionPlanner.plan(edges, plans));
        assertFalse(inputCells(region).contains(initialized));
        assertTrue(String.valueOf(region.get("derivedInputs")).contains(
                initialized
                        + " [field is initialized by an object construction"));
    }

    @Test
    public void containerMutationRetainsCanonicalHeapPrestate() {
        String updater = "<example.Updater: void merge(int)>";
        String reader = "<example.Reader: void handle()>";
        String value = updater + ".param0:value";
        String field = "<example.State: java.util.Map entries>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(updater, Collections.singletonList(value),
                        Collections.singletonList(field)),
                plan(reader, Collections.singletonList(field),
                        Collections.singletonList(reader
                                + "#failure:missing")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(reader, "SEED", "seed", reader + "#failure:missing",
                        reader + ".return", 1),
                edge(reader, "HEAP_READ", "field_read", field,
                        reader + "::entries", 2),
                edge(updater, "HEAP_WRITE", "field_mutation", value,
                        field, 3));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), updater);
        assertTrue(inputCells(producer).contains(value));
        assertTrue(inputCells(producer).contains(field));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) producer.get("symbolicInputs");
        assertTrue(inputs.stream().anyMatch(input ->
                field.equals(input.get("cell"))
                        && "MUTABLE_HEAP_PRESTATE_FRONTIER".equals(
                        input.get("selectionReason"))));

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slices.get(0).get(
                        "inputBindings");
        assertTrue(bindings.stream().anyMatch(binding ->
                field.equals(binding.get("dependencyCell"))
                        && Collections.singletonList(updater).equals(
                        binding.get("dependencyMethods"))));
        assertFalse(((List<?>) slices.get(0).get("causalEdges")).isEmpty());
        assertEquals(Boolean.TRUE, slices.get(0).get("complete"));
    }

    @Test
    public void provesFreshDefaultConstructedHeapOutputInitializer() {
        String updater = "<example.Updater: void initialize()>";
        String reader = "<example.Reader: void handle()>";
        String local = updater + "::$r0";
        String field = "<example.State: java.util.Map entries>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(updater, Collections.singletonList("new java.util.HashMap"),
                        Collections.singletonList(field)),
                plan(reader, Collections.singletonList(field),
                        Collections.singletonList(reader + "#failure:missing")));

        Map<String, Object> allocation = edge(updater, "COMPUTE",
                "local_def_use", "new java.util.HashMap", local, 3);
        allocation.put("id", "DF.ALLOC");
        allocation.put("allocationType", "java.util.HashMap");
        allocation.put("allocationConstructor",
                "<java.util.HashMap: void <init>()>");
        allocation.put("allocationConstructorArgumentCount", 0);
        allocation.put("allocationConstructorUnitIndex", 4);
        allocation.put("allocationConstructorSiteId",
                updater + "#u4:allocation_constructor");
        allocation.put("allocationConstructorEvidence",
                "JIMPLE_SPECIALINVOKE_ON_FRESH_LOCAL");
        Map<String, Object> write = edge(updater, "HEAP_WRITE",
                "field_write", local, field, 5);
        write.put("id", "DF.WRITE");
        List<Map<String, Object>> edges = Arrays.asList(
                edge(reader, "SEED", "seed", reader + "#failure:missing",
                        reader + ".return", 1),
                edge(reader, "HEAP_READ", "field_read", field,
                        reader + "::entries", 2),
                allocation, write);

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), updater);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> initializers =
                (List<Map<String, Object>>) slices.get(0)
                        .get("heapInitializers");

        assertEquals(1, initializers.size());
        Map<String, Object> initializer = initializers.get(0);
        assertEquals("FRESH_DEFAULT_CONSTRUCTED_OBJECT",
                initializer.get("kind"));
        assertEquals("java.util.HashMap", initializer.get("allocatedType"));
        assertEquals(0, initializer.get("constructorArgumentCount"));
        assertEquals(Boolean.TRUE, initializer.get("proofComplete"));
        assertEquals(Arrays.asList("DF.ALLOC", "DF.WRITE"),
                initializer.get("proofEdgeIds"));
        assertEquals(slices.get(0).get("outputPort"),
                initializer.get("outputPort"));
    }

    @Test
    public void bindsSliceFieldToUniqueRootArgumentCarrier() {
        String updater = "<example.Updater: void run(example.Request)>";
        String reader = "<example.Reader: void handle()>";
        String argument = updater + ".param0:example.Request";
        String argumentField = "<example.Request: int keyId>";
        String local = updater + "::keyId";
        String output = "<example.State: java.util.Map entries>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(updater, Collections.singletonList(argument),
                        Collections.singletonList(output)),
                plan(reader, Collections.singletonList(output),
                        Collections.singletonList(reader + "#failure:missing")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(reader, "SEED", "seed", reader + "#failure:missing",
                        reader + ".return", 1),
                edge(reader, "HEAP_READ", "field_read", output,
                        reader + "::entries", 2),
                edge(updater, "HEAP_READ", "field_read", argumentField,
                        local, 3),
                edge(updater, "HEAP_WRITE", "field_write", local,
                        output, 4));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), updater);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.get(0);
        assertEquals(Boolean.TRUE, slice.get("complete"));
        assertEquals(1, ((List<?>) slice.get("inputPorts")).size());
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get("inputBindings");
        assertTrue(bindings.stream().anyMatch(binding ->
                argumentField.equals(binding.get("dependencyCell"))
                        && "UNIQUE_ROOT_ARGUMENT_CARRIER".equals(
                        binding.get("bindingAuthority"))));
    }

    @Test
    public void rejectsAmbiguousRootArgumentCarrierForSliceField() {
        String updater = "<example.Updater: void run(example.Request,example.Request)>";
        String reader = "<example.Reader: void handle()>";
        String first = updater + ".param0:example.Request";
        String second = updater + ".param1:example.Request";
        String argumentField = "<example.Request: int keyId>";
        String local = updater + "::keyId";
        String output = "<example.State: java.util.Map entries>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(updater, Arrays.asList(first, second),
                        Collections.singletonList(output)),
                plan(reader, Collections.singletonList(output),
                        Collections.singletonList(reader + "#failure:missing")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(reader, "SEED", "seed", reader + "#failure:missing",
                        reader + ".return", 1),
                edge(reader, "HEAP_READ", "field_read", output,
                        reader + "::entries", 2),
                edge(updater, "HEAP_READ", "field_read", argumentField,
                        local, 3),
                edge(updater, "HEAP_WRITE", "field_write", local,
                        output, 4));

        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), updater);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> slice = slices.get(0);
        assertEquals(Boolean.FALSE, slice.get("complete"));
        assertTrue(((List<?>) slice.get("unresolvedInputs")).stream()
                .anyMatch(value -> String.valueOf(value).contains(
                        "output slice input has no region port")));
    }

    @Test
    public void recursivelyClosesTransitiveSharedStateProducers() {
        String upstream = "<example.Upstream: void publish()>";
        String middle = "<example.Middle: void refresh()>";
        String receiver = "<example.Receiver: void handle()>";
        String firstField = "<example.State: int first>";
        String secondField = "<example.State: int second>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(upstream,
                        Collections.singletonList(upstream + "::external"),
                        Collections.singletonList(firstField)),
                plan(middle, Collections.singletonList(firstField),
                        Collections.singletonList(secondField)),
                plan(receiver, Collections.singletonList(secondField),
                        Collections.singletonList(receiver + "#failure:stale")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(receiver, "SEED", "seed_exception_throw",
                        receiver + "::value", receiver + "#failure:stale", 3),
                edge(receiver, "HEAP_READ", "field_read", secondField,
                        receiver + "::value", 2),
                edge(middle, "HEAP_READ", "field_read", firstField,
                        middle + "::value", 1),
                edge(middle, "HEAP_WRITE", "field_write",
                        middle + "::value", secondField, 2),
                edge(upstream, "HEAP_WRITE", "field_write",
                        upstream + "::external", firstField, 1));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);

        assertEquals(3, result.regions.size());
        assertTrue(result.regionEdges.stream().anyMatch(edge ->
                "SHARED_STATE".equals(edge.get("kind"))
                        && firstField.equals(edge.get("fromPort"))
                        && firstField.equals(edge.get("toPort"))));
        assertTrue(result.regionEdges.stream().anyMatch(edge ->
                "SHARED_STATE".equals(edge.get("kind"))
                        && secondField.equals(edge.get("fromPort"))
                        && secondField.equals(edge.get("toPort"))));
        assertEquals(Boolean.TRUE, result.coverage.get("complete"));
    }

    @Test
    public void emitsCoveredTransitiveWritersAtSiblingDynamicDispatch() {
        String root = "<example.Worker: void run()>";
        String consumer = "<example.Consumer: void executeWorker()>";
        String relay = "<example.Relay: void executeWorker()>";
        String source = "<example.Source: void executeWorker()>";
        String firstField = "<example.Bus: int first>";
        String secondField = "<example.Bus: int second>";
        String produced = source + "::$value";
        String relayed = relay + "::$value";
        String consumed = consumer + "::$value";
        String failure = consumer + "#u4#exception:example.Bug";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, Collections.singletonList(root + "::r0"),
                        Collections.<String>emptyList()),
                plan(consumer, Collections.singletonList(secondField),
                        Collections.singletonList(failure)),
                plan(relay, Collections.singletonList(firstField),
                        Collections.singletonList(secondField)),
                plan(source, Collections.singletonList(
                                source + "::external"),
                        Collections.singletonList(firstField)));

        Map<String, Object> dispatchConsumer = edge(root,
                "DYNAMIC_DISPATCH", "dispatch_receiver",
                root + "::r0", consumer + "::r0", 7);
        dispatchConsumer.put("invoke", consumer);
        Map<String, Object> dispatchRelay = edge(root,
                "DYNAMIC_DISPATCH", "dispatch_receiver",
                root + "::r0", relay + "::r0", 7);
        dispatchRelay.put("invoke", relay);
        Map<String, Object> dispatchSource = edge(root,
                "DYNAMIC_DISPATCH", "dispatch_receiver",
                root + "::r0", source + "::r0", 7);
        dispatchSource.put("invoke", source);
        Map<String, Object> producerValue = edge(source, "VALUE_PASS",
                "local_def_use", source + "::external", produced, 1);
        authoritativeValueFlow(producerValue);
        Map<String, Object> sourceWrite = edge(source, "HEAP_WRITE",
                "field_write", produced, firstField, 2);
        authoritativeValueFlow(sourceWrite);
        Map<String, Object> relayRead = edge(relay, "HEAP_READ",
                "field_read", firstField, relayed, 1);
        authoritativeValueFlow(relayRead);
        Map<String, Object> relayWrite = edge(relay, "HEAP_WRITE",
                "field_write", relayed, secondField, 2);
        authoritativeValueFlow(relayWrite);
        Map<String, Object> read = edge(consumer, "HEAP_READ",
                "field_read", secondField, consumed, 1);
        authoritativeValueFlow(read);
        List<Map<String, Object>> edges = Arrays.asList(
                dispatchConsumer,
                dispatchRelay,
                dispatchSource,
                producerValue,
                sourceWrite,
                relayRead,
                relayWrite,
                read,
                edge(consumer, "GUARD", "exception_guard", consumed,
                        failure, 3),
                edge(consumer, "SEED", "seed_exception_throw",
                        consumer + "::$exception", failure, 4));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);

        assertEquals("one target, relay, and transitive source candidate",
                3, result.regions.size());
        Map<String, Object> consumerRegion = result.regions.stream()
                .filter(region -> consumer.equals(region.get(
                        "anchorMethod"))).findFirst().orElse(null);
        Map<String, Object> relayRegion = result.regions.stream()
                .filter(region -> relay.equals(region.get(
                        "anchorMethod"))).findFirst().orElse(null);
        Map<String, Object> sourceRegion = result.regions.stream()
                .filter(region -> source.equals(region.get(
                        "anchorMethod"))).findFirst().orElse(null);
        assertNotNull(consumerRegion);
        assertNotNull(relayRegion);
        assertNotNull(sourceRegion);
        assertEquals(Collections.singletonList(secondField),
                consumerRegion.get("mandatorySeedGuardInputs"));
        assertTrue("covered relay needs an anchor-specific candidate: "
                        + result.regions,
                secondField.equals(((List<?>) relayRegion.get(
                        "outputs")).stream()
                        .map(value -> ((Map<?, ?>) value).get("cell"))
                        .filter(secondField::equals)
                        .findFirst().orElse(null)));
        assertTrue(((List<?>) relayRegion.get("outputSlices")).stream()
                .map(value -> (Map<?, ?>) value)
                .filter(slice -> secondField.equals(slice.get(
                        "outputCell")))
                .anyMatch(slice -> ((List<?>) slice.get("inputBindings"))
                        .stream().map(value -> (Map<?, ?>) value)
                        .anyMatch(binding -> firstField.equals(binding.get(
                                "dependencyCell")))));
        assertTrue("covered transitive source needs its own candidate: "
                        + result.regions,
                firstField.equals(((List<?>) sourceRegion.get(
                        "outputs")).stream()
                        .map(value -> ((Map<?, ?>) value).get("cell"))
                        .filter(firstField::equals)
                        .findFirst().orElse(null)));
        assertTrue(result.regionEdges.stream().anyMatch(edge ->
                firstField.equals(edge.get("fromPort"))
                        && firstField.equals(edge.get("toPort"))
                        && sourceRegion.get("regionId").equals(
                        edge.get("fromRegion"))
                        && relayRegion.get("regionId").equals(
                        edge.get("toRegion"))));
        assertTrue(result.regionEdges.stream().anyMatch(edge ->
                secondField.equals(edge.get("fromPort"))
                        && secondField.equals(edge.get("toPort"))
                        && relayRegion.get("regionId").equals(
                        edge.get("fromRegion"))
                        && consumerRegion.get("regionId").equals(
                        edge.get("toRegion"))));
    }

    @Test
    public void linksContainerMutationToFieldSensitiveConsumerRegion() {
        String updater = "<example.SecretManager: void updateKeys()>";
        String exporter = "<example.SecretManager: example.Keys exportKeys()>";
        String field = "<example.SecretManager: java.util.Map allKeys>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(updater, Collections.singletonList(updater + ".param0:value"),
                        Collections.singletonList(field)),
                plan(exporter,
                        Collections.singletonList(
                                "@this: example.SecretManager#field:allKeys"),
                        Collections.singletonList(exporter + ".return")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(exporter, "SEED", "seed", exporter + "#failure:stale",
                        exporter + ".return", 1),
                edge(updater, "HEAP_WRITE", "field_mutation",
                        updater + ".param0:value", field, 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(2, result.regions.size());
        assertTrue(result.regionEdges.stream().anyMatch(edge ->
                "SHARED_STATE".equals(edge.get("kind"))
                        && field.equals(edge.get("fromPort"))
                        && field.equals(edge.get("toPort"))));
    }

    @Test
    public void keepsHeartbeatPayloadBetweenNameNodeAndDataNodeRegions() {
        String sender = "<example.NameNode: void addKeyUpdateCommand()>";
        String receiver = "<example.DataNode: void processAccessKeyUpdateCommand()>";
        String payload = sender + "::exportedKeys#field:allKeys";
        String received = receiver + "::exportedKeys#field:allKeys";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(sender, Collections.singletonList("<example.Keys: int allKeys>"),
                        Collections.singletonList(payload)),
                plan(receiver, Collections.singletonList(received),
                        Collections.singletonList("<example.Secret: int allKeys>")));
        List<Map<String, Object>> edges = Collections.singletonList(
                edge(receiver, "PROTOCOL_TRANSFER",
                        "projected_hdfs_heartbeat_key_update",
                        payload, received, 4));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(2, result.regions.size());
        assertEquals(1, result.regionEdges.size());
        assertEquals("HEARTBEAT_TRANSFER", result.regionEdges.get(0).get("kind"));
        assertEquals(Boolean.TRUE, result.coverage.get("complete"));
    }

    @Test
    public void configuredHelperReturnIsCanonicalCapturedProducerOutput() {
        String producer = "<example.ProducerThread: void run(int)>";
        String compute = "<example.Producer: int compute(int)>";
        String publish = "<example.Bus: void publish(int)>";
        String consumer = "<example.ConsumerThread: void run()>";
        String getter = "<example.Bus: int get()>";
        String producerInput = producer + ".param0:int";
        String computeInput = compute + ".param0:int";
        String computeLocal = compute + "::i0";
        String computed = compute + ".return";
        String callerLocal = producer + "::i0";
        String publishInput = publish + ".param0:int";
        String publishLocal = publish + "::i0";
        String field = "<example.Bus: int value>";
        String observed = consumer + "::observed";
        String failure = consumer + "#failure:bug";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(producer, Collections.singletonList(producerInput),
                        Collections.singletonList(callerLocal)),
                plan(compute, Collections.singletonList(computeInput),
                        Arrays.asList(computeLocal, computed,
                                compute + "#u2")),
                plan(publish, Collections.singletonList(publishInput),
                        Arrays.asList(publishLocal, field,
                                publish + "::r0#field:value")),
                plan(consumer, Collections.singletonList(field),
                        Arrays.asList(observed, failure)),
                plan(getter, Collections.singletonList(field),
                        Collections.singletonList(getter + ".return")));
        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> computeArgument = edge(producer,
                "IDENTITY_BINDING", "call_argument", producerInput,
                computeInput, 1);
        computeArgument.put("invoke", compute);
        authoritativeValueFlow(computeArgument);
        edges.add(computeArgument);
        Map<String, Object> identity = edge(compute, "VALUE_PASS",
                "local_def_use", computeInput, computeLocal, 1);
        identity.put("siteId", compute + "#u1");
        identity.put("unit", "i0 := @parameter0: int");
        authoritativeValueFlow(identity);
        edges.add(identity);
        Map<String, Object> returned = edge(compute, "VALUE_PASS",
                "local_def_use", computeLocal, computed, 2);
        returned.put("siteId", compute + "#u2");
        returned.put("unit", "return i0");
        authoritativeValueFlow(returned);
        edges.add(returned);
        Map<String, Object> callerReturn = edge(producer,
                "FUNCTION_RETURN", "call_return", computed, callerLocal, 2);
        callerReturn.put("invoke", compute);
        authoritativeValueFlow(callerReturn);
        edges.add(callerReturn);
        Map<String, Object> publishArgument = edge(producer,
                "IDENTITY_BINDING", "call_argument", callerLocal,
                publishInput, 3);
        publishArgument.put("invoke", publish);
        authoritativeValueFlow(publishArgument);
        edges.add(publishArgument);
        Map<String, Object> publishIdentity = edge(publish, "VALUE_PASS",
                "local_def_use", publishInput, publishLocal, 1);
        publishIdentity.put("siteId", publish + "#u1");
        publishIdentity.put("unit", "i0 := @parameter0: int");
        authoritativeValueFlow(publishIdentity);
        edges.add(publishIdentity);
        Map<String, Object> write = edge(publish, "HEAP_WRITE",
                "field_write", publishLocal, field, 2);
        write.put("siteId", publish + "#u2");
        write.put("unit", "r0." + field + " = i0");
        authoritativeValueFlow(write);
        edges.add(write);
        edges.add(configuredRpcReturnMapping("DF.RPC.MAPPING", computed,
                getter + ".return", getter));
        edges.add(edge(consumer, "HEAP_READ", "field_read", field,
                observed, 1));
        edges.add(edge(consumer, "SEED", "seed_exception_throw", observed,
                failure, 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producerRegion = regionForRoot(result, producer);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> outputs =
                (List<Map<String, Object>>) producerRegion.get("outputs");
        assertEquals(1, outputs.size());
        assertEquals(computed, outputs.get(0).get("cell"));
        assertEquals("RETURN", outputs.get(0).get("kind"));

        Map<String, Object> slice = requestedOutputSlice(producerRegion,
                computed);
        assertEquals(Boolean.TRUE, slice.get("complete"));
        assertEquals(Boolean.TRUE, slice.get("captureBindingsRequired"));
        assertEquals(Boolean.TRUE, slice.get("captureBindingsComplete"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> captures =
                (List<Map<String, Object>>) slice.get("captureBindings");
        assertEquals(1, captures.size());
        Map<String, Object> capture = captures.get(0);
        assertEquals("METHOD_RETURN_VALUE", capture.get("captureKind"));
        assertEquals(compute, capture.get("method"));
        assertEquals(compute + "#u2", capture.get("siteId"));
        assertEquals(2, capture.get("unitIndex"));
        assertEquals("i0", capture.get("returnExpression"));
        assertEquals(computeLocal, capture.get("returnCell"));
        assertEquals("STATIC_EXACT_METHOD_RETURN_VALUE",
                capture.get("bindingAuthority"));
        assertEquals(0, capture.get("occurrence"));

        Map<String, Object> shared = result.regionEdges.stream()
                .filter(candidate -> "SHARED_STATE".equals(
                        candidate.get("kind"))
                        && field.equals(candidate.get("fromPort")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(outputs.get(0).get("portId"),
                shared.get("fromOutputPort"));
        assertEquals(computed, shared.get("fromOutputCell"));
        assertEquals(Boolean.TRUE, shared.get("aliasProofComplete"));
        assertEquals("CONFIGURED_RPC_PRODUCER_RETURN_AND_STATIC_EXACT_"
                        + "PUBLISH_VALUE_FLOW_V1",
                shared.get("aliasProofAuthority"));
        assertTrue(String.valueOf(shared.get("aliasProofEdgeIds"))
                .contains("DF.RPC.MAPPING"));

        String alternate = producer + "::alternate";
        Map<String, Object> alternateCopy = edge(producer, "VALUE_PASS",
                "local_def_use", computed, alternate, 7);
        alternateCopy.put("siteId", producer + "#u7");
        alternateCopy.put("unit", "alternate = i0");
        authoritativeValueFlow(alternateCopy);
        edges.add(alternateCopy);
        Map<String, Object> ambiguousWrite = edge(producer, "HEAP_WRITE",
                "field_write", alternate, field, 8);
        ambiguousWrite.put("siteId", producer + "#u8");
        ambiguousWrite.put("unit", "r0." + field + " = alternate");
        authoritativeValueFlow(ambiguousWrite);
        edges.add(ambiguousWrite);
        SymbolicRegionPlanner.Result ambiguous = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> ambiguousShared = ambiguous.regionEdges.stream()
                .filter(candidate -> "SHARED_STATE".equals(
                        candidate.get("kind"))
                        && field.equals(candidate.get("fromPort")))
                .findFirst().orElseThrow(AssertionError::new);
        assertFalse(ambiguousShared.containsKey("fromOutputPort"));
        assertFalse(ambiguousShared.containsKey("aliasProofComplete"));
    }

    @Test
    public void canonicalizesProjectedBoundaryEndpointWithAllExactProofs() {
        String sender = "<example.NameNode: void publish()>";
        String exporter = "<example.Manager: example.Keys export()>";
        String receiver = "<example.DataNode: void receive(example.Keys)>";
        String input = exporter + ".param0:int[]";
        String canonicalField = "<example.Keys: int[] allKeys>";
        String returnedBase = exporter + ".return";
        String rawBase = sender + "::$r5";
        String raw = rawBase + "#field:allKeys";
        String inbound = receiver + "::$r8#field:allKeys";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(sender, Collections.emptyList(),
                        Collections.singletonList(raw)),
                plan(exporter, Collections.singletonList(input),
                        Collections.singletonList(canonicalField)),
                plan(receiver, Collections.singletonList(inbound),
                        Collections.singletonList(receiver
                                + "#failure:missing")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(exporter, "HEAP_WRITE", "field_write", input,
                canonicalField, 1));
        edges.add(projectedReturnProof("DF.PROOF.3",
                "projected_method_caller_return", sender, returnedBase,
                rawBase, "allKeys"));
        edges.add(projectedReturnProof("DF.PROOF.1",
                "projected_call_return", sender, returnedBase, rawBase,
                "allKeys"));
        edges.add(projectedReturnProof("DF.PROOF.2",
                "projected_caller_return", sender, returnedBase, rawBase,
                "allKeys"));
        edges.add(edge(receiver, "PROTOCOL_TRANSFER",
                "projected_hdfs_heartbeat_key_update", raw, inbound, 2));
        edges.add(edge(receiver, "SEED", "seed_exception_throw", inbound,
                receiver + "#failure:missing", 3));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producer = regionForRoot(result, sender);
        @SuppressWarnings("unchecked")
        Map<String, Object> canonicalOutput =
                ((List<Map<String, Object>>) producer.get("outputs"))
                        .stream().filter(output -> canonicalField.equals(
                        output.get("cell"))).findFirst()
                        .orElseThrow(AssertionError::new);
        Map<String, Object> boundary = result.regionEdges.stream()
                .filter(candidate -> raw.equals(candidate.get("fromPort"))
                        && inbound.equals(candidate.get("toPort")))
                .findFirst().orElseThrow(AssertionError::new);

        assertEquals(raw, boundary.get("fromPort"));
        assertEquals(canonicalOutput.get("portId"),
                boundary.get("fromOutputPort"));
        assertEquals(canonicalField, boundary.get("fromOutputCell"));
        assertEquals(Arrays.asList("DF.PROOF.1", "DF.PROOF.2",
                "DF.PROOF.3"), boundary.get("aliasProofEdgeIds"));
        assertEquals("STATIC_EXACT_PROJECTED_RETURN_VALUE_FLOW_"
                        + "AND_DECLARED_RETURN_FIELD",
                boundary.get("aliasProofAuthority"));
        assertEquals(Boolean.TRUE, boundary.get("aliasProofComplete"));
    }

    @Test
    public void rejectsAmbiguousCanonicalProjectedBoundaryOutput() {
        String sender = "<example.NameNode: void publish()>";
        String firstExporter = "<example.Manager: example.Keys export()>";
        String secondExporter =
                "<example.OtherManager: example.OtherKeys export()>";
        String receiver = "<example.DataNode: void receive(java.lang.Object)>";
        String rawBase = sender + "::$r5";
        String raw = rawBase + "#field:allKeys";
        String inbound = receiver + "::$r8#field:allKeys";
        String firstField = "<example.Keys: int[] allKeys>";
        String secondField = "<example.OtherKeys: int[] allKeys>";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(sender, Collections.emptyList(),
                        Collections.singletonList(raw)),
                plan(firstExporter,
                        Collections.singletonList(firstExporter
                                + ".param0:int[]"),
                        Collections.singletonList(firstField)),
                plan(secondExporter,
                        Collections.singletonList(secondExporter
                                + ".param0:int[]"),
                        Collections.singletonList(secondField)),
                plan(receiver, Collections.singletonList(inbound),
                        Collections.singletonList(receiver
                                + "#failure:missing")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(firstExporter, "HEAP_WRITE", "field_write",
                firstExporter + ".param0:int[]", firstField, 1));
        edges.add(edge(secondExporter, "HEAP_WRITE", "field_write",
                secondExporter + ".param0:int[]", secondField, 1));
        edges.add(projectedReturnProof("DF.FIRST",
                "projected_call_return", sender,
                firstExporter + ".return", rawBase, "allKeys"));
        edges.add(projectedReturnProof("DF.SECOND",
                "projected_call_return", sender,
                secondExporter + ".return", rawBase, "allKeys"));
        edges.add(edge(receiver, "PROTOCOL_TRANSFER",
                "projected_hdfs_heartbeat_key_update", raw, inbound, 2));
        edges.add(edge(receiver, "SEED", "seed_exception_throw", inbound,
                receiver + "#failure:missing", 3));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> boundary = result.regionEdges.stream()
                .filter(candidate -> raw.equals(candidate.get("fromPort"))
                        && inbound.equals(candidate.get("toPort")))
                .findFirst().orElseThrow(AssertionError::new);

        assertFalse(boundary.containsKey("fromOutputPort"));
        assertFalse(boundary.containsKey("fromOutputCell"));
        assertFalse(boundary.containsKey("aliasProofEdgeIds"));
        assertFalse(boundary.containsKey("aliasProofComplete"));
    }

    @Test
    public void staticTransformLabelDoesNotHideOpaqueCallResult() {
        String root = "<example.Receiver: void handle(java.lang.String)>";
        String split = "<java.lang.String: java.lang.String[] split(java.lang.String)>";
        String rootArgument = root + ".param0:userName";
        String splitResult = split + ".return";
        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Arrays.asList(rootArgument, splitResult),
                        Collections.singletonList(root + "#failure:missing")));
        Map<String, Object> modeledCall = edge(root, "MODEL_TRANSFORM",
                "call_return", splitResult, root + "::parts", 1);
        modeledCall.put("invoke", split);
        List<Map<String, Object>> edges = Arrays.asList(
                modeledCall,
                edge(root, "SEED", "seed", root + "::parts",
                        root + "#failure:missing", 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        List<String> inputs = inputCells(result.regions.get(0));
        assertEquals(Arrays.asList(rootArgument, splitResult), inputs);
        assertFalse(String.valueOf(result.regions.get(0).get("derivedInputs"))
                .contains(splitResult));
    }

    @Test
    public void ordinaryFieldContainingTimeIsNotAnEnvironmentSource()
            throws Exception {
        String updater = "<example.Updater: void initialize(example.Keys)>";
        String lifetime = updater + "::$r2#field:tokenLifetime";
        java.lang.reflect.Method sourceKind = SymbolicRegionPlanner.class
                .getDeclaredMethod("sourceKind", String.class, String.class);
        sourceKind.setAccessible(true);

        assertEquals("SHARED_HEAP",
                sourceKind.invoke(null, lifetime, updater));
        assertEquals("ENVIRONMENT", sourceKind.invoke(null,
                "<java.lang.System: long currentTimeMillis()>.return",
                updater));
        assertEquals("ENVIRONMENT", sourceKind.invoke(null,
                "<org.apache.hadoop.util.Time: long now()>.return",
                updater));
        assertEquals("OPAQUE_CALL", sourceKind.invoke(null,
                "<example.RpcProtocol: example.Response fetch()>.return",
                updater));
    }

    @Test
    public void excludesParametersAndReturnsOfInternalCallees() {
        String root = "<example.Receiver: void handle(java.lang.Integer)>";
        String lookup = "<example.Receiver: java.lang.Object lookup(int)>";
        String rootArgument = root + ".param0:keyId";
        String lookupArgument = lookup + ".param0:keyId";
        String lookupReturn = lookup + ".return";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, Arrays.asList(rootArgument, lookupReturn),
                        Collections.singletonList(root + "#failure:missing")),
                plan(lookup, Collections.singletonList(lookupArgument),
                        Collections.singletonList(lookupReturn)));
        Map<String, Object> call = edge(root, "CALL_ARGUMENT", "call_argument",
                rootArgument, lookupArgument, 1);
        call.put("invoke", lookup);
        Map<String, Object> returned = edge(root, "FUNCTION_RETURN", "call_return",
                lookupReturn, root + "::value", 1);
        returned.put("invoke", lookup);
        List<Map<String, Object>> edges = Arrays.asList(
                call, returned,
                edge(root, "SEED", "seed", root + "::value",
                        root + "#failure:missing", 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(Collections.singletonList(rootArgument),
                inputCells(result.regions.get(0)));
    }

    @Test
    public void collapsesAliasesOfTheSameRootReceiverField() {
        String root = "<example.SecretManager: void lookup(int)>";
        String globalField = "<example.SecretManager: java.util.Map allKeys>";
        String localField = root + "::r0#field:allKeys";
        String receiverField = "@this: example.SecretManager#field:allKeys";
        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Arrays.asList(globalField, localField, receiverField),
                        Collections.singletonList(root + "#failure:missing")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(root, "HEAP_READ", "field_read", globalField,
                        root + "::map", 1),
                edge(root, "SEED", "seed", root + "::map",
                        root + "#failure:missing", 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(Collections.singletonList(receiverField),
                inputCells(result.regions.get(0)));
        assertEquals(2, result.regions.get(0).get("derivedInputCount"));
    }

    @Test
    public void keepsReceiverFieldsButNotReceiverIdentity() {
        String root = "<example.SecretManager: void lookup(int)>";
        String receiver = "@this: example.SecretManager";
        String receiverField = receiver + "#field:allKeys";
        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Arrays.asList(receiver, receiverField),
                        Collections.singletonList(root + "#failure:missing")));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(root, "HEAP_READ", "field_read", receiverField,
                        root + "::map", 1),
                edge(root, "SEED", "seed", root + "::map",
                        root + "#failure:missing", 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(Collections.singletonList(receiverField),
                inputCells(result.regions.get(0)));
        assertTrue(String.valueOf(result.regions.get(0).get("derivedInputs"))
                .contains("concrete carrier"));
    }

    @Test
    public void excludesAllocationsCastsConditionsAndStaticConstants() {
        String root = "<example.Server: void receive(java.lang.String)>";
        String argument = root + ".param0:userName";
        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Arrays.asList(argument,
                                "new example.CallbackHandler",
                                "(example.NameCallback) r6",
                                "r6 instanceof example.NameCallback",
                                "$z0 == 0",
                                "<example.Protocol: int MAGIC_NUMBER>"),
                        Collections.singletonList(root + "#failure:missing")));
        List<Map<String, Object>> edges = Collections.singletonList(
                edge(root, "SEED", "seed", argument,
                        root + "#failure:missing", 1));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        assertEquals(Collections.singletonList(argument),
                inputCells(result.regions.get(0)));
        assertTrue(String.valueOf(result.regions.get(0).get("derivedInputs"))
                .contains("new example.CallbackHandler"));
        assertTrue(String.valueOf(result.regions.get(0).get("derivedInputs"))
                .contains("MAGIC_NUMBER"));
    }

    @Test
    public void exceptionCausalRegionExcludesSiblingBranchAndRecordsOutcome() {
        String root = "<example.Server: void receive(boolean)>";
        String encrypted = "<example.Server: void encrypted()>";
        String general = "<example.Server: void general()>";
        String retrieve = "<example.Secret: void retrieve()>";
        String exception = retrieve + "#u9#exception:example.MissingKey";
        String encryptedResult = root + "::encryptedResult";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, Arrays.asList(root + ".param0:encrypt",
                                root + "::generalResult"),
                        Arrays.asList(encryptedResult, root + "::generalResult")),
                plan(encrypted, Collections.singletonList(encrypted + "::state"),
                        Collections.singletonList(encrypted + ".return")),
                plan(general, Collections.singletonList(general + "::state"),
                        Collections.singletonList(general + ".return")),
                plan(retrieve, Collections.singletonList(retrieve + "::allKeys"),
                        Collections.singletonList(exception)));

        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(invocation(root, encrypted, root + "::server",
                encrypted + "::r0", 4));
        edges.add(invocation(root, general, root + "::server",
                general + "::r0", 8));
        edges.add(invocation(encrypted, retrieve, encrypted + "::state",
                retrieve + "::allKeys", 2));
        Map<String, Object> guard = edge(root, "GUARD",
                "path_guard_dependency", root + ".param0:encrypt",
                encryptedResult, 3);
        guard.put("evidence",
                "dominating branch requires Jimple outcome false "
                        + "to reach relevant definition at u4");
        edges.add(guard);
        edges.add(edge(retrieve, "SEED", "seed_exception_throw",
                retrieve + "::exceptionObject", exception, 9));
        edges.add(edge(retrieve, "HEAP_LOOKUP", "map_lookup_state",
                retrieve + "::allKeys", retrieve + "::exceptionObject", 7));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);

        Map<String, Object> targetRegion = result.regions.stream()
                .filter(region -> retrieve.equals(region.get("anchorMethod")))
                .findFirst().orElseThrow(AssertionError::new);
        @SuppressWarnings("unchecked")
        List<String> methods = (List<String>) targetRegion.get("methods");
        assertTrue(methods.containsAll(Arrays.asList(root, encrypted, retrieve)));
        assertTrue(!methods.contains(general));
        assertEquals("EXCEPTION_BACKWARD_CAUSAL_CLOSURE",
                targetRegion.get("selection"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> policies =
                (List<Map<String, Object>>) targetRegion.get("branchPolicies");
        assertTrue(policies.stream().anyMatch(policy ->
                Boolean.FALSE.equals(policy.get("requiredOutcome"))));
    }

    @Test
    public void contradictionPruningIsInvocationSiteSensitive() {
        String root = "<example.Server: void receive()>";
        String branch = "<example.Server: void handshake()>";
        String getter = "<example.Config: boolean enabled()>";
        String wrongOnly = "<example.BadMagic: void <init>(int,boolean)>";
        String retrieve = "<example.Secret: void retrieve(boolean)>";
        String exception = retrieve + "#u9#exception:example.MissingKey";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, Collections.singletonList(root + "::config"),
                        Collections.singletonList(root + "::enabled")),
                plan(branch, Collections.singletonList(branch + "::magic"),
                        Collections.singletonList(branch + "::state")),
                plan(getter, Collections.singletonList(getter + "::flag"),
                        Collections.singletonList(getter + ".return")),
                plan(wrongOnly, Arrays.asList(wrongOnly + ".param0:int",
                                wrongOnly + ".param1:boolean"),
                        Collections.singletonList(wrongOnly + ".return")),
                plan(retrieve, Collections.singletonList(
                                retrieve + ".param0:state"),
                        Collections.singletonList(exception)));

        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> validGetter = edge(root, "FUNCTION_RETURN",
                "call_return", getter + ".return", root + "::enabled", 1);
        validGetter.put("invoke", getter);
        edges.add(validGetter);

        Map<String, Object> rootGuard = edge(root, "GUARD",
                "path_guard_dependency", root + "::enabled",
                root + "::enabledPath", 2);
        rootGuard.put("evidence",
                "dominating branch requires Jimple outcome true "
                        + "to reach relevant definition at u3");
        edges.add(rootGuard);
        edges.add(invocation(root, branch, root + "::enabledPath",
                branch + "::r0", 3));

        Map<String, Object> required = edge(branch, "GUARD",
                "path_guard_dependency", branch + "::magic",
                branch + "::state", 2);
        required.put("siteId", branch + "#u2");
        required.put("evidence",
                "dominating branch requires Jimple outcome true "
                        + "to reach relevant definition at u7");
        edges.add(required);
        Map<String, Object> opposite = edge(branch, "GUARD",
                "path_guard_dependency", branch + "::magic",
                branch + "::opposite", 2);
        opposite.put("siteId", branch + "#u2");
        opposite.put("evidence",
                "dominating branch requires Jimple outcome false "
                        + "to reach relevant definition at u5");
        edges.add(opposite);

        Map<String, Object> rejectedGetter = invocation(branch, getter,
                branch + "::opposite", getter + "::r0", 4);
        edges.add(rejectedGetter);

        // Model a multi-argument call whose first argument is present in the
        // data-flow slice but whose invocation is gated by the opposite branch.
        Map<String, Object> wrongCausalArgument = edge(branch,
                "IDENTITY_BINDING", "call_argument", branch + "::magic",
                branch + "::state", 5);
        wrongCausalArgument.put("invoke", wrongOnly);
        edges.add(wrongCausalArgument);
        Map<String, Object> wrongBranchArgument = edge(branch,
                "IDENTITY_BINDING", "call_argument", branch + "::opposite",
                wrongOnly + ".param1:boolean", 5);
        wrongBranchArgument.put("invoke", wrongOnly);
        edges.add(wrongBranchArgument);

        edges.add(invocation(branch, retrieve, branch + "::state",
                retrieve + ".param0:state", 7));
        edges.add(edge(retrieve, "SEED", "seed_exception_throw",
                retrieve + ".param0:state", exception, 9));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> targetRegion = result.regions.stream()
                .filter(region -> retrieve.equals(region.get("anchorMethod")))
                .findFirst().orElseThrow(AssertionError::new);
        @SuppressWarnings("unchecked")
        List<String> methods = (List<String>) targetRegion.get("methods");

        assertTrue(methods.contains(getter));
        assertTrue(!methods.contains(wrongOnly));
    }

    @Test
    public void incomingProtocolPortReplacesDuplicateRemoteAlias() {
        String client = "<example.Client: java.lang.String send()>";
        String server = "<example.Server: void receive(java.lang.String)>";
        String remote = client + ".return";
        String local = server + ".param0:userName";
        String exception = server + "#u2#exception:example.BadName";
        List<Map<String, Object>> plans = Arrays.asList(
                plan(client, Collections.singletonList(client + ".param0:name"),
                        Collections.singletonList(remote)),
                plan(server, Arrays.asList(remote, local),
                        Collections.singletonList(exception)));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(server, "PROTOCOL_TRANSFER", "hdfs_sasl_username",
                        remote, local, 1),
                edge(server, "SEED", "seed_exception_throw",
                        local, exception, 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(edges, plans);
        Map<String, Object> serverRegion = result.regions.stream()
                .filter(region -> server.equals(region.get("anchorMethod")))
                .findFirst().orElseThrow(AssertionError::new);

        assertEquals(Collections.singletonList(local), inputCells(serverRegion));
        assertTrue(String.valueOf(serverRegion.get("derivedInputs"))
                .contains("remote protocol producer"));
        assertTrue(result.regionEdges.stream().anyMatch(edge ->
                "EQUALITY".equals(edge.get("candidateRelation"))
                        && Boolean.FALSE.equals(edge.get(
                        "eligibleForAutomaticDerivation"))
                        && remote.equals(edge.get("fromPort"))
                        && local.equals(edge.get("toPort"))));
    }

    @Test
    public void internallyDefinedProtocolLocalIsDerivedAlias() {
        String sender = "<example.NameNode: example.Keys sendKeys()>";
        String root = "<example.DataNode: void process(example.Command)>";
        String active = "<example.DataNode: void processActive(example.Command)>";
        String getter = "<example.Command: example.Keys getKeys()>";
        String sink = "<example.Secret: void addKeys(example.Keys)>";
        String reader = "<example.Reader: void handle()>";
        String remote = sender + ".return";
        String rootArgument = root + ".param0:example.Command";
        String activeArgument = active + ".param0:example.Command";
        String commandKeys = "<example.Command: example.Keys keys>";
        String returned = getter + ".return";
        String local = active + "::$r8";
        String sinkArgument = sink + ".param0:example.Keys";
        String allKeys = "<example.Secret: java.util.Map allKeys>";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(sender, Collections.singletonList(sender + "::source"),
                        Collections.singletonList(remote)),
                plan(root, Collections.singletonList(rootArgument),
                        Collections.singletonList(root + "::dispatched")),
                plan(active, Arrays.asList(activeArgument, local),
                        Collections.singletonList(local)),
                plan(getter, Collections.singletonList(commandKeys),
                        Collections.singletonList(returned)),
                plan(sink, Collections.singletonList(sinkArgument),
                        Collections.singletonList(allKeys)),
                plan(reader, Collections.singletonList(allKeys),
                        Collections.singletonList(reader + "#failure:missing")));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(invocation(root, active, rootArgument, activeArgument, 1));
        edges.add(edge(getter, "HEAP_READ", "field_read",
                commandKeys, returned, 1));
        Map<String, Object> callReturn = edge(active, "FUNCTION_RETURN",
                "call_return", returned, local, 2);
        callReturn.put("invoke", getter);
        callReturn.put("relation", "value_flow");
        edges.add(callReturn);
        edges.add(edge(active, "PROTOCOL_TRANSFER",
                "hdfs_heartbeat_key_update", remote, local, 2));
        edges.add(invocation(active, sink, local, sinkArgument, 3));
        edges.add(edge(sink, "HEAP_WRITE", "field_mutation",
                sinkArgument, allKeys, 1));
        edges.add(edge(reader, "HEAP_READ", "field_read", allKeys,
                reader + "::keys", 1));
        edges.add(edge(reader, "SEED", "seed_exception_throw",
                reader + "::keys", reader + "#failure:missing", 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producer = regionForRoot(result, root);

        assertEquals(Boolean.TRUE, producer.get("inputSelectionComplete"));
        assertTrue(inputCells(producer).contains(rootArgument));
        assertTrue(inputCells(producer).contains(commandKeys));
        assertFalse(inputCells(producer).contains(local));
        assertTrue(String.valueOf(producer.get("derivedInputs"))
                .contains("protocol boundary target aliases a value defined inside the region"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> allKeysSlice = slices.stream()
                .filter(slice -> allKeys.equals(slice.get("outputCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Boolean.TRUE, allKeysSlice.get("complete"));
        assertTrue(((List<?>) allKeysSlice.get("unresolvedInputs")).isEmpty());
        assertTrue(result.regionEdges.stream().anyMatch(edge ->
                remote.equals(edge.get("fromPort"))
                        && local.equals(edge.get("toPort"))));
    }

    @Test
    public void protocolLocalWithoutInternalDefinitionRemainsUnresolved() {
        String sender = "<example.NameNode: example.Keys sendKeys()>";
        String root = "<example.DataNode: void process(example.Command)>";
        String active = "<example.DataNode: void processActive(example.Command)>";
        String sink = "<example.Secret: void addKeys(example.Keys)>";
        String reader = "<example.Reader: void handle()>";
        String remote = sender + ".return";
        String rootArgument = root + ".param0:example.Command";
        String activeArgument = active + ".param0:example.Command";
        String local = active + "::$r8";
        String sinkArgument = sink + ".param0:example.Keys";
        String allKeys = "<example.Secret: java.util.Map allKeys>";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(sender, Collections.singletonList(sender + "::source"),
                        Collections.singletonList(remote)),
                plan(root, Collections.singletonList(rootArgument),
                        Collections.singletonList(root + "::dispatched")),
                plan(active, Arrays.asList(activeArgument, local),
                        Collections.singletonList(local)),
                plan(sink, Collections.singletonList(sinkArgument),
                        Collections.singletonList(allKeys)),
                plan(reader, Collections.singletonList(allKeys),
                        Collections.singletonList(reader + "#failure:missing")));
        List<Map<String, Object>> edges = Arrays.asList(
                invocation(root, active, rootArgument, activeArgument, 1),
                edge(active, "PROTOCOL_TRANSFER",
                        "hdfs_heartbeat_key_update", remote, local, 2),
                invocation(active, sink, local, sinkArgument, 3),
                edge(sink, "HEAP_WRITE", "field_mutation",
                        sinkArgument, allKeys, 1),
                edge(reader, "HEAP_READ", "field_read", allKeys,
                        reader + "::keys", 1),
                edge(reader, "SEED", "seed_exception_throw",
                        reader + "::keys", reader + "#failure:missing", 2));

        SymbolicRegionPlanner.Result result = SymbolicRegionPlanner.plan(
                edges, plans);
        Map<String, Object> producer = regionForRoot(result, root);

        assertEquals(Boolean.FALSE, producer.get("inputSelectionComplete"));
        assertTrue(String.valueOf(producer.get("unresolvedInputs"))
                .contains(local));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> outputSlices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        Map<String, Object> allKeysSlice = outputSlices.stream()
                .filter(slice -> allKeys.equals(slice.get("outputCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Boolean.TRUE, allKeysSlice.get("structuralComplete"));
        assertEquals(Boolean.FALSE, allKeysSlice.get("complete"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> details =
                (List<Map<String, Object>>) allKeysSlice.get(
                        "unresolvedInputDetails");
        Map<String, Object> detail = details.stream()
                .filter(row -> local.equals(row.get("dependencyCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertTrue(String.valueOf(detail.get("dependencyMethods"))
                .contains(active));
        assertEquals("NO_MATERIALIZABLE_REGION_BOUNDARY_REPRESENTATION",
                detail.get("reason"));
        assertEquals("STATIC_EXACT_DEPENDENCY_METHOD_CONSUMER_SET_V1",
                detail.get("provenanceAuthority"));
        assertTrue(result.regionEdges.stream().anyMatch(edge ->
                remote.equals(edge.get("fromPort"))
                        && local.equals(edge.get("toPort"))));
    }

    @Test
    public void exactCausalProjectedBoundaryRemainsInOutputSlice() {
        String updater =
                "<example.ProjectedDataNode: void processKeys()>";
        String localAllKeys = updater + "::$r59#field:allKeys";
        String output = "<example.ProjectedSecret: java.util.Map allKeys>";
        Map<String, Object> slice = projectedBoundaryCausalFilterSlice();

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> causalEdges =
                (List<Map<String, Object>>) slice.get("causalEdges");
        assertTrue(causalEdges.stream().anyMatch(edge ->
                localAllKeys.equals(edge.get("fromCell"))
                        && output.equals(edge.get("toCell"))));
        assertTrue(String.valueOf(slice.get("unresolvedInputs"))
                .contains(localAllKeys));
    }

    @Test
    public void nonCausalProjectedBoundaryDoesNotEnterByFieldFamily() {
        String updater =
                "<example.ProjectedDataNode: void processKeys()>";
        String localTokenLifetime =
                updater + "::$r59#field:tokenLifetime";
        Map<String, Object> slice = projectedBoundaryCausalFilterSlice();

        assertFalse(String.valueOf(slice.get("inputBindings"))
                .contains(localTokenLifetime));
        assertFalse(String.valueOf(slice.get("unresolvedInputs"))
                .contains(localTokenLifetime));
        assertTrue(String.valueOf(slice.get("derivedInputs"))
                .contains(localTokenLifetime));
        assertTrue(String.valueOf(slice.get("derivedInputs"))
                .contains("not in the exception-directed backward slice"));
    }

    @Test
    public void callGuardResultDerivedFromRootInputIsNotResymbolized() {
        String root = "<example.Reader: void process(boolean)>";
        String readSuccess = "<example.Reader: boolean readSuccess(boolean)>";
        String flag = root + ".param0:flag";
        String calleeFlag = readSuccess + ".param0:flag";
        String returned = readSuccess + ".return";
        String predicate = root + "::readSucceeded";
        String exception = root + "#u3#exception:example.FatalRead";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, Arrays.asList(flag, returned),
                        Arrays.asList(predicate, exception)),
                plan(readSuccess, Collections.singletonList(calleeFlag),
                        Collections.singletonList(returned)));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(invocation(root, readSuccess, flag, calleeFlag, 1));
        Map<String, Object> compute = edge(readSuccess, "COMPUTE",
                "local_def_use", calleeFlag, returned, 1);
        edges.add(compute);
        Map<String, Object> callReturn = edge(root, "FUNCTION_RETURN",
                "call_return", returned, predicate, 1);
        callReturn.put("invoke", readSuccess);
        edges.add(callReturn);
        edges.add(edge(root, "SEED", "seed_exception_throw",
                predicate, exception, 3));

        Map<String, Object> region = onlyRegion(
                SymbolicRegionPlanner.plan(edges, plans));
        assertEquals(Collections.singletonList(flag), inputCells(region));
        assertTrue(String.valueOf(region.get("derivedInputs"))
                .contains(returned));
        assertEquals("BACKWARD_DEPENDENCY_FRONTIER",
                region.get("symbolicInputPolicy"));
        assertEquals(Boolean.TRUE, region.get("inputSelectionComplete"));
    }

    @Test
    public void callGuardResultDerivedFromSharedFieldSelectsFieldOnly() {
        String root = "<example.Reader: void process()>";
        String readSuccess = "<example.Reader: boolean readSuccess()>";
        String field = "<example.Reader: boolean lastReadSuccessful>";
        String returned = readSuccess + ".return";
        String predicate = root + "::readSucceeded";
        String exception = root + "#u3#exception:example.FatalRead";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, Collections.singletonList(returned),
                        Arrays.asList(predicate, exception)),
                plan(readSuccess, Collections.singletonList(field),
                        Collections.singletonList(returned)));
        List<Map<String, Object>> edges = new ArrayList<>();
        Map<String, Object> invoke = edge(root, "FUNCTION_RETURN",
                "call_return", returned, predicate, 1);
        invoke.put("invoke", readSuccess);
        edges.add(invoke);
        edges.add(edge(readSuccess, "HEAP_READ", "field_read",
                field, returned, 1));
        edges.add(edge(root, "SEED", "seed_exception_throw",
                predicate, exception, 3));

        Map<String, Object> region = onlyRegion(
                SymbolicRegionPlanner.plan(edges, plans));
        assertEquals(Collections.singletonList(field), inputCells(region));
        assertTrue(String.valueOf(region.get("derivedInputs"))
                .contains(returned));
    }

    @Test
    public void opaqueCallUsedByGuardBecomesSymbolicFrontier() {
        String root = "<example.Reader: void process()>";
        String opaqueRead = "<example.Channel: boolean readSuccess()>";
        String returned = opaqueRead + ".return";
        String predicate = root + "::readSucceeded";
        String exception = root + "#u3#exception:example.FatalRead";

        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Collections.singletonList(returned),
                        Arrays.asList(predicate, exception)));
        Map<String, Object> invoke = edge(root, "FUNCTION_RETURN",
                "call_return", returned, predicate, 1);
        invoke.put("invoke", opaqueRead);
        List<Map<String, Object>> edges = Arrays.asList(
                invoke,
                edge(root, "SEED", "seed_exception_throw",
                        predicate, exception, 3));

        Map<String, Object> region = onlyRegion(
                SymbolicRegionPlanner.plan(edges, plans));
        assertEquals(Collections.singletonList(returned), inputCells(region));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        assertEquals("OPAQUE_CALL", inputs.get(0).get("sourceKind"));
        assertEquals("OPAQUE_CALL_RETURN_FRONTIER",
                inputs.get(0).get("selectionReason"));
        assertEquals(Boolean.TRUE, region.get("inputSelectionComplete"));
    }

    @Test
    public void canonicalGuardInputCarriesItsUniqueExactAccessorSite() {
        String field = "<javax.security.auth.callback.NameCallback: "
                + "java.lang.String defaultName>";
        String getter = "<javax.security.auth.callback.NameCallback: "
                + "java.lang.String getDefaultName()>";
        String local = HANDLE + "::$r4";
        String failure = HANDLE + "#failure:missing";
        Map<String, Object> accessor = edge(HANDLE, "HEAP_READ",
                "accessor_field_return", field, local, 36);
        accessor.put("siteId", HANDLE + "#u36");
        accessor.put("unit", "$r4 = virtualinvoke r12." + getter + "()");
        accessor.put("invoke", getter);
        accessor.put("accessorImplementationMethod", getter);
        accessor.put("accessorImplementationAuthority",
                "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
        authoritativeValueFlow(accessor);
        declaredMetadata(accessor, field,
                "javax.security.auth.callback.NameCallback",
                "java.lang.String", "defaultName");

        Map<String, Object> region = onlyRegion(SymbolicRegionPlanner.plan(
                Arrays.asList(accessor, edge(HANDLE, "SEED",
                        "seed_exception_throw", local, failure, 40)),
                Collections.singletonList(plan(HANDLE,
                        Collections.singletonList(field),
                        Collections.singletonList(failure)))));
        @SuppressWarnings("unchecked")
        Map<String, Object> input = ((List<Map<String, Object>>) region.get(
                "symbolicInputs")).stream()
                .filter(candidate -> field.equals(candidate.get("cell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("FIELD_ACCESS", input.get("bindingMode"));
        assertEquals(field, input.get("accessFieldSignature"));
        assertEquals(HANDLE + "#u36", input.get("accessorCallSiteId"));
        assertEquals(36, input.get("accessorCallUnitIndex"));
        assertEquals(getter, input.get("accessorDeclaredCallee"));
        assertEquals("STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                        + "ACCESSOR_CALLSITE_V1",
                input.get("accessorCallSiteAuthority"));
    }

    @Test
    public void parallelProjectionPreventsDuplicateCallReturnInput() {
        String root = "<example.Reader: void process(example.State)>";
        String accessor = "<example.State: boolean isReady()>";
        String argument = root + ".param0:example.State";
        String field = root + "::r1#field:ready";
        String returned = accessor + ".return";
        String predicate = root + "::ready";
        String exception = root + "#u3#exception:example.NotReady";

        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Arrays.asList(argument, returned, field),
                        Arrays.asList(predicate, exception)));
        Map<String, Object> projected = edge(root, "PROJECTION",
                "accessor_field_return", field, predicate, 1);
        projected.put("invoke", accessor);
        Map<String, Object> genericReturn = edge(root, "FUNCTION_RETURN",
                "call_return", returned, predicate, 1);
        genericReturn.put("invoke", accessor);
        List<Map<String, Object>> edges = Arrays.asList(
                projected, genericReturn,
                edge(root, "SEED", "seed_exception_throw",
                        predicate, exception, 3));

        Map<String, Object> region = onlyRegion(
                SymbolicRegionPlanner.plan(edges, plans));
        assertFalse(inputCells(region).contains(returned));
        assertTrue(String.valueOf(region.get("derivedInputs"))
                .contains("tracked in-region operand or field projection"));
    }

    @Test
    public void parallelProjectionMatchesAnyExactReturnedSite() {
        String root = "<example.Reader: void process(boolean)>";
        String accessor = "<example.State: boolean isReady()>";
        String argument = root + ".param0:boolean";
        String returned = accessor + ".return";
        String firstPredicate = root + "::firstReady";
        String secondPredicate = root + "::secondReady";
        String combined = root + "::combined";
        String exception = root + "#u5#exception:example.NotReady";

        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Arrays.asList(argument, returned),
                        Arrays.asList(combined, exception)));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(root, "FUNCTION_RETURN", "call_return",
                        returned, firstPredicate, 1),
                edge(root, "FUNCTION_RETURN", "call_return",
                        returned, secondPredicate, 2),
                edge(root, "COMPUTE", "local_def_use",
                        argument, secondPredicate, 2),
                edge(root, "COMPUTE", "local_def_use",
                        firstPredicate, combined, 3),
                edge(root, "COMPUTE", "local_def_use",
                        secondPredicate, combined, 3),
                edge(root, "SEED", "seed_exception_throw",
                        combined, exception, 5));

        Map<String, Object> region = onlyRegion(
                SymbolicRegionPlanner.plan(edges, plans));
        assertFalse(inputCells(region).contains(returned));
        assertTrue(String.valueOf(region.get("derivedInputs"))
                .contains("tracked in-region operand or field projection"));
    }

    @Test
    public void parallelProjectionRequiresSameNonBoundaryMethodAndUnit() {
        String root = "<example.Reader: void process(boolean,boolean)>";
        String other = "<example.Other: void compute()>";
        String accessor = "<example.State: boolean isReady()>";
        String first = root + ".param0:boolean";
        String second = root + ".param1:boolean";
        String returned = accessor + ".return";
        String predicate = root + "::ready";
        String negativeUnitPredicate = root + "::negativeUnitReady";
        String emptyMethodPredicate = root + "::emptyMethodReady";
        String combined = root + "::combined";
        String exception = root + "#u12#exception:example.NotReady";

        List<Map<String, Object>> plans = Collections.singletonList(
                plan(root, Arrays.asList(first, second, returned),
                        Arrays.asList(combined, exception)));
        List<Map<String, Object>> edges = new ArrayList<>();
        edges.add(edge(root, "FUNCTION_RETURN", "call_return",
                returned, predicate, 7));
        edges.add(edge(other, "COMPUTE", "local_def_use",
                first, predicate, 7));
        edges.add(edge(root, "COMPUTE", "local_def_use",
                second, predicate, 8));
        edges.add(edge(root, "PROTOCOL_TRANSFER", "rpc_argument",
                first, predicate, 7));
        edges.add(edge(root, "COMPUTE", "local_def_use",
                "", predicate, 7));

        edges.add(edge(root, "FUNCTION_RETURN", "call_return",
                returned, negativeUnitPredicate, -1));
        edges.add(edge(root, "COMPUTE", "local_def_use",
                first, negativeUnitPredicate, -1));

        Map<String, Object> emptyMethodReturn = edge(root,
                "FUNCTION_RETURN", "call_return", returned,
                emptyMethodPredicate, 10);
        emptyMethodReturn.put("method", "");
        edges.add(emptyMethodReturn);
        Map<String, Object> emptyMethodAlternative = edge(root,
                "COMPUTE", "local_def_use", first,
                emptyMethodPredicate, 10);
        emptyMethodAlternative.put("method", "");
        edges.add(emptyMethodAlternative);

        edges.add(edge(root, "COMPUTE", "local_def_use",
                predicate, combined, 11));
        edges.add(edge(root, "COMPUTE", "local_def_use",
                negativeUnitPredicate, combined, 11));
        edges.add(edge(root, "COMPUTE", "local_def_use",
                emptyMethodPredicate, combined, 11));
        edges.add(edge(root, "SEED", "seed_exception_throw",
                combined, exception, 12));

        Map<String, Object> region = onlyRegion(
                SymbolicRegionPlanner.plan(edges, plans));
        assertTrue(inputCells(region).contains(returned));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        assertTrue(inputs.stream().anyMatch(input ->
                returned.equals(input.get("cell"))
                        && "OPAQUE_CALL_RETURN_FRONTIER".equals(
                        input.get("selectionReason"))));
    }

    @Test
    public void emitsContainerElementBindingOnlyForExactFourEdgeJoin() {
        List<Map<String, Object>> edges = containerFieldEdges("0");
        Map<String, Object> slice = containerFieldSlice(edges);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get(
                        "containerElementFieldBindings");

        assertEquals(2, bindings.size());
        Map<String, Object> binding = bindings.stream()
                .filter(row -> Collections.singletonList("keyId").equals(
                        row.get("fieldPath")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(1, binding.get("schemaVersion"));
        assertEquals("ARRAY_ELEMENT_FIELD", binding.get("kind"));
        assertEquals("EXACT_ARRAY_INDEX",
                binding.get("selectorAuthority"));
        assertEquals(0, binding.get("elementIndex"));
        assertEquals(1, binding.get("elementOccurrence"));
        assertEquals(Collections.singletonList("keyId"),
                binding.get("fieldPath"));
        assertEquals(CONTAINER_ADD + "#u14",
                binding.get("fieldMaterializationSiteId"));
        assertEquals(CONTAINER_ADD + "#u13",
                binding.get("arrayLoadSiteId"));
        assertEquals(Arrays.asList("A", "C", "G", "P"),
                binding.get("proofCausalEdgeIds"));
        assertEquals(Boolean.TRUE, binding.get("complete"));
        assertTrue(((List<?>) slice.get("causalEdgeIds")).contains("A"));

        Map<String, Object> expiry = bindings.stream()
                .filter(row -> Collections.singletonList("expiryDate").equals(
                        row.get("fieldPath")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(2, expiry.get("schemaVersion"));
        assertEquals("CONTAINER_SNAPSHOT",
                expiry.get("materializationMode"));
        assertEquals("EXACT_ARRAY_INDEX",
                expiry.get("selectorAuthority"));
        assertEquals(Arrays.asList("A", "C", "EXPIRY.G", "EXPIRY.P",
                        "PUT.VALUE"),
                expiry.get("proofCausalEdgeIds"));
        assertEquals("STATIC_EXACT_ARRAY_ELEMENT_MAP_PUT_VALUE_AND_"
                        + "DECLARED_FIELD_FIVE_EDGE_JOIN_V1",
                expiry.get("proofAuthority"));
    }

    @Test
    public void arrayPutValueSnapshotPreservesNestedLeafPath() {
        List<Map<String, Object>> edges = containerFieldEdges("$i7");
        Map<String, Object> projection = edges.stream()
                .filter(edge -> "EXPIRY.P".equals(edge.get("id")))
                .findFirst().orElseThrow(AssertionError::new);
        String owner = CONTAINER_ADD + "::$r7";
        projection.put("fromCell", owner
                + "#field:metadata#field:expiryDate");
        projection.put("fieldPath", "#field:metadata#field:expiryDate");

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings = (List<Map<String, Object>>)
                containerFieldSlice(edges).get(
                        "containerElementFieldBindings");
        Map<String, Object> expiry = bindings.stream()
                .filter(row -> "CONTAINER_SNAPSHOT".equals(
                        row.get("materializationMode")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Arrays.asList("metadata", "expiryDate"),
                expiry.get("fieldPath"));
        assertEquals("<example.KeyBase: long expiryDate>",
                expiry.get("declaredFieldSignature"));
    }

    @Test
    public void dynamicArrayIndexUsesIdentityDiscoverySeed() {
        List<Map<String, Object>> edges = containerFieldEdges("$i7");
        Map<String, Object> slice = containerFieldSlice(edges);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> bindings =
                (List<Map<String, Object>>) slice.get(
                        "containerElementFieldBindings");
        assertEquals(2, bindings.size());
        Map<String, Object> keyId = bindings.stream()
                .filter(row -> Collections.singletonList("keyId").equals(
                        row.get("fieldPath")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals("DISCOVER_UNIQUE_IDENTITY_INDEX",
                keyId.get("selectorAuthority"));
        assertEquals(-1, keyId.get("elementIndex"));
        assertEquals(-1, keyId.get("elementOccurrence"));
    }

    @Test
    public void missingOrAmbiguousFourEdgeSegmentFailsClosed() {
        for (String id : Arrays.asList("C", "A", "P", "G")) {
            List<Map<String, Object>> missing = containerFieldEdges("0");
            missing.removeIf(edge -> id.equals(edge.get("id")));
            assertEquals("missing " + id, 0,
                    containerBindingCount(containerFieldSlice(missing),
                            "keyId"));

            List<Map<String, Object>> ambiguous = containerFieldEdges("0");
            Map<String, Object> original = ambiguous.stream()
                    .filter(edge -> id.equals(edge.get("id")))
                    .findFirst().orElseThrow(AssertionError::new);
            Map<String, Object> duplicate = new LinkedHashMap<>(original);
            duplicate.put("id", id + ".DUPLICATE");
            ambiguous.add(duplicate);
            assertEquals("ambiguous " + id, 0,
                    containerBindingCount(containerFieldSlice(ambiguous),
                            "keyId"));
        }
    }

    private static final String CONTAINER_ADD =
            "<example.Secret: void addKeys(example.Keys)>";
    private static final String CONTAINER_READER =
            "<example.Reader: void consume()>";
    private static final String CONTAINER_FIELD =
            "<example.Keys: example.Key[] allKeys>";
    private static final String ELEMENT_FIELD =
            "<example.KeyBase: int keyId>";
    private static final String OUTPUT_FIELD =
            "<example.Secret: java.util.Map allKeys>";

    private static Map<String, Object> inheritedAccessorOutputSlice(
            boolean includeImplementationPlan,
            boolean mismatchedDeclaredFieldTuple) {
        String caller = "<example.Secret: void addKeys(example.Keys)>";
        String reader = "<example.Reader: void consume()>";
        String declaredField = "<example.KeyBase: int keyId>";
        String declaredCallee = "<example.Key: int getKeyId()>";
        String implementation = "<example.KeyBase: int getKeyId()>";
        String output = "<example.Secret: java.util.Map allKeys>";

        List<Map<String, Object>> plans = new ArrayList<>();
        plans.add(plan(caller, Collections.singletonList(declaredField),
                Collections.singletonList(output)));
        if (includeImplementationPlan) {
            plans.add(plan(implementation,
                    Collections.singletonList(declaredField),
                    Collections.singletonList(
                            implementation + ".return")));
        }
        plans.add(plan(reader, Collections.singletonList(output),
                Collections.singletonList(reader + "#failure:missing")));

        List<Map<String, Object>> edges = new ArrayList<>();
        for (int unit : Arrays.asList(14, 20, 26, 32)) {
            String result = caller + "::$key" + unit;
            Map<String, Object> accessor = edge(caller, "HEAP_READ",
                    "accessor_field_return", declaredField, result, unit);
            accessor.put("siteId", caller + "#u" + unit);
            accessor.put("unit", result.substring(
                    (caller + "::").length()) + " = virtualinvoke r0."
                    + declaredCallee + "()");
            accessor.put("invoke", declaredCallee);
            accessor.put("accessorImplementationMethod", implementation);
            accessor.put("accessorImplementationAuthority",
                    "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
            authoritativeValueFlow(accessor);
            declaredMetadata(accessor, declaredField,
                    mismatchedDeclaredFieldTuple
                            ? "example.UnrelatedKeyBase"
                            : "example.KeyBase",
                    "int", "keyId");
            edges.add(accessor);

            Map<String, Object> mutation = edge(caller, "HEAP_WRITE",
                    "field_mutation", result, output, unit + 1);
            mutation.put("id", "EFFECT.KEY." + unit);
            edges.add(mutation);
        }
        edges.add(edge(reader, "HEAP_READ", "field_read", output,
                reader + "::allKeys", 1));
        edges.add(edge(reader, "SEED", "seed_exception_throw",
                reader + "::allKeys", reader + "#failure:missing", 2));
        return requestedOutputSlice(SymbolicRegionPlanner.plan(edges, plans),
                caller, output);
    }

    private static Map<String, Object> containerFieldSlice(
            List<Map<String, Object>> edges) {
        List<Map<String, Object>> plans = Arrays.asList(
                plan(CONTAINER_ADD,
                        Arrays.asList(CONTAINER_FIELD, ELEMENT_FIELD),
                        Collections.singletonList(OUTPUT_FIELD)),
                plan(CONTAINER_READER,
                        Collections.singletonList(OUTPUT_FIELD),
                        Collections.singletonList(CONTAINER_READER
                                + "#failure:missing")));
        Map<String, Object> producer = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), CONTAINER_ADD);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) producer.get("outputSlices");
        return slices.stream().filter(slice -> OUTPUT_FIELD.equals(
                slice.get("outputCell"))).findFirst()
                .orElseThrow(AssertionError::new);
    }

    private static int containerBindingCount(Map<String, Object> slice) {
        return ((List<?>) slice.get("containerElementFieldBindings")).size();
    }

    @SuppressWarnings("unchecked")
    private static int containerBindingCount(Map<String, Object> slice,
                                             String leaf) {
        int count = 0;
        for (Map<String, Object> binding : (List<Map<String, Object>>) slice
                .get("containerElementFieldBindings")) {
            List<String> path = (List<String>) binding.get("fieldPath");
            if (path != null && !path.isEmpty()
                    && leaf.equals(path.get(path.size() - 1))) {
                count++;
            }
        }
        return count;
    }

    private static List<Map<String, Object>> containerFieldEdges(
            String selector) {
        String array = CONTAINER_ADD + "::$r4";
        String owner = CONTAINER_ADD + "::$r5";
        String result = CONTAINER_ADD + "::$i0";
        List<Map<String, Object>> edges = new ArrayList<>();

        Map<String, Object> c = exactStaticEdge("C", "HEAP_READ",
                "accessor_field_return", CONTAINER_FIELD, array, 11,
                "$r4 = virtualinvoke r1.<example.Keys: example.Key[] "
                        + "getAllKeys()>()");
        declaredMetadata(c, CONTAINER_FIELD, "example.Keys",
                "example.Key[]", "allKeys");
        edges.add(c);

        Map<String, Object> a = exactStaticEdge("A", "VALUE_PASS",
                "local_def_use", array, owner, 13,
                "$r5 = $r4[" + selector + "]");
        a.put("relation", "taint_depends_on");
        edges.add(a);

        String accessorUnit = "$i0 = virtualinvoke $r5."
                + "<example.Key: int getKeyId()>()";
        Map<String, Object> p = exactStaticEdge("P", "PROJECTION",
                "accessor_field_return", owner + "#field:keyId", result,
                14, accessorUnit);
        p.put("fieldSensitive", true);
        p.put("objectFromCell", owner);
        p.put("objectToCell", result);
        p.put("fieldPath", "#field:keyId");
        p.put("invoke", "<example.Key: int getKeyId()>");
        declaredMetadata(p, ELEMENT_FIELD, "example.KeyBase", "int",
                "keyId");
        edges.add(p);

        Map<String, Object> g = exactStaticEdge("G", "HEAP_READ",
                "accessor_field_return", ELEMENT_FIELD, result, 14,
                accessorUnit);
        g.put("invoke", "<example.Key: int getKeyId()>");
        declaredMetadata(g, ELEMENT_FIELD, "example.KeyBase", "int",
                "keyId");
        edges.add(g);

        // Make C part of the requested-output slice independently of A, as
        // in the HDFS addKeys graph where the array also feeds the map writes.
        Map<String, Object> containerEffect = edge(CONTAINER_ADD,
                "HEAP_WRITE", "field_mutation", array, OUTPUT_FIELD, 16);
        containerEffect.put("id", "EFFECT.CONTAINER");
        edges.add(containerEffect);
        Map<String, Object> elementEffect = edge(CONTAINER_ADD,
                "HEAP_WRITE", "field_mutation", result, OUTPUT_FIELD, 17);
        elementEffect.put("id", "EFFECT.ELEMENT");
        edges.add(elementEffect);

        Map<String, Object> putValue = exactStaticEdge("PUT.VALUE",
                "HEAP_WRITE", "field_mutation", owner, OUTPUT_FIELD, 18,
                "interfaceinvoke $r8.<java.util.Map: java.lang.Object "
                        + "put(java.lang.Object,java.lang.Object)>($r9, $r5)");
        putValue.put("invoke", "<java.util.Map: java.lang.Object "
                + "put(java.lang.Object,java.lang.Object)>");
        edges.add(putValue);

        // Same accessor pair as expiry handling, deliberately rooted in a
        // map iterator value rather than the exact array-load owner.
        String iteratorOwner = CONTAINER_ADD + "::$r7";
        String expiryResult = CONTAINER_ADD + "::$l1";
        String expiryField = "<example.KeyBase: long expiryDate>";
        String expiryUnit = "$l1 = virtualinvoke $r7."
                + "<example.Key: long getExpiryDate()>()";
        Map<String, Object> expiryP = exactStaticEdge("EXPIRY.P",
                "PROJECTION", "accessor_field_return",
                iteratorOwner + "#field:expiryDate", expiryResult, 21,
                expiryUnit);
        expiryP.put("fieldSensitive", true);
        expiryP.put("objectFromCell", iteratorOwner);
        expiryP.put("objectToCell", expiryResult);
        expiryP.put("fieldPath", "#field:expiryDate");
        expiryP.put("invoke", "<example.Key: long getExpiryDate()>");
        declaredMetadata(expiryP, expiryField, "example.KeyBase", "long",
                "expiryDate");
        edges.add(expiryP);
        Map<String, Object> expiryG = exactStaticEdge("EXPIRY.G",
                "HEAP_READ", "accessor_field_return", expiryField,
                expiryResult, 21, expiryUnit);
        expiryG.put("invoke", "<example.Key: long getExpiryDate()>");
        declaredMetadata(expiryG, expiryField, "example.KeyBase", "long",
                "expiryDate");
        edges.add(expiryG);
        Map<String, Object> expiryEffect = edge(CONTAINER_ADD,
                "HEAP_WRITE", "field_mutation", expiryResult,
                OUTPUT_FIELD, 22);
        expiryEffect.put("id", "EFFECT.EXPIRY");
        edges.add(expiryEffect);

        edges.add(edge(CONTAINER_READER, "HEAP_READ", "field_read",
                OUTPUT_FIELD, CONTAINER_READER + "::allKeys", 1));
        edges.add(edge(CONTAINER_READER, "SEED", "seed_exception_throw",
                CONTAINER_READER + "::allKeys",
                CONTAINER_READER + "#failure:missing", 2));
        return edges;
    }

    private static Map<String, Object> exactStaticEdge(
            String id, String transfer, String kind, String from, String to,
            int unit, String jimple) {
        Map<String, Object> edge = edge(CONTAINER_ADD, transfer, kind,
                from, to, unit);
        edge.put("id", id);
        edge.put("siteId", CONTAINER_ADD + "#u" + unit);
        edge.put("unit", jimple);
        edge.put("relation", "value_flow");
        edge.put("mappingOnly", false);
        edge.put("semanticAssertionsAllowed", true);
        edge.put("eligibleForAutomaticDerivation", true);
        edge.put("eligibleForAutomaticSmt", true);
        edge.put("direction", "backward_provenance");
        return edge;
    }

    private static void declaredMetadata(Map<String, Object> edge,
                                         String signature, String owner,
                                         String type, String name) {
        edge.put("declaredFieldSignature", signature);
        edge.put("declaredFieldOwner", owner);
        edge.put("declaredFieldType", type);
        edge.put("declaredFieldName", name);
        edge.put("declaredFieldAuthority",
                "SOOT_RESOLVED_DECLARATION_HIERARCHY");
    }

    private static Map<String, Object> onlyRegion(
            SymbolicRegionPlanner.Result result) {
        assertEquals(1, result.regions.size());
        return result.regions.get(0);
    }

    private static Map<String, Object> regionForRoot(
            SymbolicRegionPlanner.Result result, String root) {
        for (Map<String, Object> region : result.regions) {
            if (root.equals(region.get("rootMethod"))) {
                return region;
            }
        }
        throw new AssertionError("missing region rooted at " + root);
    }

    private static Map<String, Object> requestedOutputSlice(
            SymbolicRegionPlanner.Result result, String root,
            String outputCell) {
        Map<String, Object> region = regionForRoot(result, root);
        return requestedOutputSlice(region, outputCell);
    }

    private static Map<String, Object> requestedOutputSlice(
            Map<String, Object> region, String outputCell) {
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) region.get("outputSlices");
        return slices.stream().filter(slice -> outputCell.equals(
                slice.get("outputCell"))).findFirst()
                .orElseThrow(AssertionError::new);
    }

    /**
     * Reproduces the production ordering that exposed the REGION.15 bug.
     * The broad 128-port frontier is intentionally occupied by unrelated
     * reads, while the requested-output slice contains an exact
     * Command.keys -> getter return -> caller local projection chain.  The
     * canonical field path must therefore be promoted by the slice itself.
     */
    private static Map<String, Object> latePromotedGetterAliasRegion(
            boolean competingCanonicalField) {
        String upstream = "<example.NameNode: example.Keys publish()>";
        String root = "<example.DataNode: void receive()>";
        String getter =
                "<example.KeyUpdateCommand: example.Keys getKeys()>";
        String reader = "<example.Reader: void check()>";
        String lateCarrier =
                "<example.KeyUpdateCommand: example.Keys keys>";
        String earlyCarrier = "<example.Command: example.Keys keys>";
        String path = "#field:allKeys";
        String getterLocal = getter + "::r1";
        String returned = getter + ".return";
        String received = root + "::$r59";
        String output = "<example.A0Secret: java.util.Map allKeys>";

        List<String> rootInputs = new ArrayList<>();
        List<Map<String, Object>> edges = new ArrayList<>();
        // These fields sort before Command/DataNode/KeyUpdateCommand.  They
        // are broad-region reads but are disconnected from the requested
        // output, so the exact output slice correctly drops them.
        rootInputs.add(output);
        for (int index = 0; index < 127; index++) {
            String filler = String.format(
                    "<example.AFill%03d: int value>", index);
            rootInputs.add(filler);
            edges.add(edge(root, "HEAP_READ", "field_read", filler,
                    root + "::filler" + index, 1000 + index));
        }
        rootInputs.add(received + path);

        List<String> carriers = new ArrayList<>();
        if (competingCanonicalField) {
            carriers.add(earlyCarrier);
        }
        carriers.add(lateCarrier);
        List<String> getterInputs = new ArrayList<>();
        int fieldUnit = 1;
        for (String carrier : carriers) {
            getterInputs.add(carrier);
            getterInputs.add(carrier + path);
            Map<String, Object> rawField = edge(getter, "HEAP_READ",
                    "field_read", carrier, getterLocal, fieldUnit);
            authoritativeValueFlow(rawField);
            edges.add(rawField);
            edges.add(projectedAliasProof(getter, "HEAP_READ",
                    "projected_field_read", carrier, getterLocal, path,
                    fieldUnit));
            fieldUnit++;
        }

        Map<String, Object> rawReturn = edge(getter, "VALUE_PASS",
                "local_def_use", getterLocal, returned, 10);
        authoritativeDirectCopyBase(rawReturn, "RETURN_LOCAL");
        edges.add(rawReturn);
        edges.add(projectedDirectCopyProof(rawReturn, path));

        Map<String, Object> callReturn = edge(root, "FUNCTION_RETURN",
                "call_return", returned, received, 20);
        authoritativeValueFlow(callReturn);
        callReturn.put("invoke", getter);
        edges.add(callReturn);
        Map<String, Object> projectedReturn = projectedAliasProof(root,
                "FUNCTION_RETURN", "projected_call_return", returned,
                received, path, 20);
        projectedReturn.put("invoke", getter);
        edges.add(projectedReturn);

        edges.add(projectedAliasProof(root, "PROTOCOL_TRANSFER",
                "projected_heartbeat_payload", upstream + ".return",
                received, path, 21));
        edges.add(edge(root, "HEAP_WRITE", "field_mutation",
                received + path, output, 22));
        edges.add(edge(reader, "HEAP_READ", "field_read", output,
                reader + "::allKeys", 1));
        edges.add(edge(reader, "SEED", "seed_exception_throw",
                reader + "::allKeys", reader + "#failure:missing", 2));

        List<Map<String, Object>> plans = Arrays.asList(
                plan(root, rootInputs, Collections.singletonList(output)),
                plan(getter, getterInputs,
                        Arrays.asList(returned, returned + path)),
                plan(reader, Collections.singletonList(output),
                        Collections.singletonList(reader
                                + "#failure:missing")));
        return regionForRoot(SymbolicRegionPlanner.plan(edges, plans), root);
    }

    private static Map<String, Object> helperFanoutOutputSlice(
            int helperCount) {
        String dispatch = "<example.MethodBudget: void dispatch()>";
        String handshake =
                "<example.MethodBudget: void handshake(java.lang.String)>";
        String receive =
                "<example.MethodBudgetReceiver: void receive(java.lang.String)>";
        String outboundValue = dispatch + "::outboundValue";
        String outbound = handshake + ".param0:java.lang.String";
        String inbound = receive + ".param0:java.lang.String";

        List<Map<String, Object>> plans = new ArrayList<>();
        plans.add(plan(dispatch, Collections.<String>emptyList(),
                Collections.singletonList(outboundValue)));
        plans.add(plan(handshake, Collections.singletonList(outbound),
                Collections.singletonList(outbound)));
        plans.add(plan(receive, Collections.singletonList(inbound),
                Collections.singletonList(receive
                        + "#failure:method-budget")));
        List<Map<String, Object>> edges = new ArrayList<>();
        for (int index = 0; index < helperCount; index++) {
            String helper = "<example.MethodBudgetHelper" + index
                    + ": void supply()>";
            String field = "<example.MethodBudgetState" + index
                    + ": long value>";
            plans.add(plan(helper, Collections.singletonList(field),
                    Collections.singletonList(outboundValue)));
            edges.add(call(dispatch, helper, 1000 + index));
            Map<String, Object> read = edge(helper, "HEAP_READ",
                    "field_read", field, outboundValue, 1);
            read.put("siteId", helper + "#u1");
            authoritativeValueFlow(read);
            declaredMetadata(read, field,
                    "example.MethodBudgetState" + index, "long", "value");
            edges.add(read);
        }
        edges.add(invocation(dispatch, handshake, outboundValue, outbound,
                4000));
        edges.add(edge(receive, "PROTOCOL_TRANSFER", "method_budget_handoff",
                outbound, inbound, 4001));
        edges.add(edge(receive, "SEED", "seed_exception_throw", inbound,
                receive + "#failure:method-budget", 4002));
        return requestedOutputSlice(SymbolicRegionPlanner.plan(edges, plans),
                dispatch, outbound);
    }

    private static Map<String, Object> projectedBoundaryCausalFilterSlice() {
        String sender =
                "<example.ProjectedNameNode: void publishKeys()>";
        String updater =
                "<example.ProjectedDataNode: void processKeys()>";
        String reader =
                "<example.ProjectedReader: void readKeys()>";
        String remoteAllKeys = sender + "::$r5#field:allKeys";
        String remoteTokenLifetime =
                sender + "::$r5#field:tokenLifetime";
        String localAllKeys = updater + "::$r59#field:allKeys";
        String localTokenLifetime =
                updater + "::$r59#field:tokenLifetime";
        // This exact causal cell deliberately has the same semantic
        // owner/field family as localTokenLifetime.  The projected local is
        // nevertheless a different runtime value and is not on the output
        // slice's exact cell graph.
        String canonicalTokenLifetime =
                "<example.ProjectedDataNode: long tokenLifetime>";
        String output = "<example.ProjectedSecret: java.util.Map allKeys>";
        String observed = reader + "::allKeys";
        String failure = reader + "#failure:missing";

        List<Map<String, Object>> plans = Arrays.asList(
                plan(sender, Collections.singletonList(sender + "::source"),
                        Arrays.asList(remoteAllKeys, remoteTokenLifetime)),
                plan(updater, Arrays.asList(localAllKeys,
                                localTokenLifetime,
                                canonicalTokenLifetime),
                        Collections.singletonList(output)),
                plan(reader, Collections.singletonList(output),
                        Collections.singletonList(failure)));
        List<Map<String, Object>> edges = Arrays.asList(
                edge(updater, "PROTOCOL_TRANSFER",
                        "projected_hdfs_heartbeat_key_update",
                        remoteAllKeys, localAllKeys, 1),
                edge(updater, "PROTOCOL_TRANSFER",
                        "projected_hdfs_heartbeat_key_update",
                        remoteTokenLifetime, localTokenLifetime, 2),
                edge(updater, "HEAP_WRITE", "field_mutation",
                        localAllKeys, output, 3),
                edge(updater, "HEAP_WRITE", "field_mutation",
                        canonicalTokenLifetime, output, 4),
                edge(reader, "HEAP_READ", "field_read", output,
                        observed, 1),
                edge(reader, "SEED", "seed_exception_throw", observed,
                        failure, 2));
        return requestedOutputSlice(SymbolicRegionPlanner.plan(edges, plans),
                updater, output);
    }

    private static List<String> inputCells(Map<String, Object> region) {
        List<String> result = new ArrayList<>();
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> inputs =
                (List<Map<String, Object>>) region.get("symbolicInputs");
        for (Map<String, Object> input : inputs) {
            result.add(String.valueOf(input.get("cell")));
        }
        return result;
    }

    private static List<Map<String, Object>> copiedEdges(
            List<Map<String, Object>> edges) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> edge : edges) {
            result.add(new LinkedHashMap<>(edge));
        }
        return result;
    }

    private static Map<String, Object> edgeById(
            List<Map<String, Object>> edges, String id) {
        return edges.stream().filter(edge -> id.equals(edge.get("id")))
                .findFirst().orElseThrow(AssertionError::new);
    }

    private static void assertProjectedDependencyUnresolved(
            List<Map<String, Object>> edges,
            List<Map<String, Object>> plans,
            String root, String output, String dependency) {
        Map<String, Object> region = regionForRoot(
                SymbolicRegionPlanner.plan(edges, plans), root);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slices =
                (List<Map<String, Object>>) region.get("outputSlices");
        Map<String, Object> slice = slices.stream()
                .filter(candidate -> output.equals(candidate.get(
                        "outputCell")))
                .findFirst().orElseThrow(AssertionError::new);
        assertEquals(Boolean.FALSE, slice.get("complete"));
        assertTrue(String.valueOf(slice),
                ((List<?>) slice.get("unresolvedInputs")).stream()
                        .anyMatch(value -> String.valueOf(value).contains(
                                dependency)));
    }

    private static Map<String, Object> plan(String method, List<String> inputs,
                                            List<String> outputs) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("method", method);
        row.put("classification", "SYMBOLIC_EXECUTION");
        row.put("symbolicInputs", inputs);
        row.put("outputs", outputs);
        row.put("requiredModels", Collections.emptyList());
        row.put("siteIds", Collections.singletonList(method + "#u0:test"));
        row.put("guards", Collections.emptyList());
        return row;
    }

    private static Map<String, Object> call(String caller, String callee, int unit) {
        Map<String, Object> row = edge(caller, "CALL_ARGUMENT", "call_argument",
                caller + ".param0:value", callee + ".param0:value", unit);
        row.put("invoke", callee);
        return row;
    }

    private static Map<String, Object> invocation(String caller, String callee,
                                                   String from, String to,
                                                   int unit) {
        Map<String, Object> row = edge(caller, "IDENTITY_BINDING",
                "call_argument", from, to, unit);
        row.put("invoke", callee);
        return row;
    }

    private static Map<String, Object> projectedReturnProof(
            String id, String kind, String caller, String returnedBase,
            String localBase, String field) {
        String path = "#field:" + field;
        Map<String, Object> row = edge(caller, "FUNCTION_RETURN", kind,
                returnedBase + path, localBase + path, 1);
        row.put("id", id);
        row.put("relation", "value_flow");
        row.put("candidateRelation", "value_flow");
        row.put("mappingOnly", false);
        row.put("semanticAssertionsAllowed", true);
        row.put("eligibleForAutomaticDerivation", true);
        row.put("eligibleForAutomaticSmt", true);
        row.put("direction", "backward_provenance");
        row.put("fieldSensitive", true);
        row.put("objectFromCell", returnedBase);
        row.put("objectToCell", localBase);
        row.put("fieldPath", path);
        return row;
    }

    private static Map<String, Object> configuredRpcReturnMapping(
            String id, String from, String to, String consumerMethod) {
        Map<String, Object> row = edge(consumerMethod,
                "PROTOCOL_TRANSFER", "configured_rpc_return_mapping",
                from, to, 0);
        row.put("id", id);
        row.put("siteId", consumerMethod
                + "#synthetic:configured_rpc_return_mapping");
        row.put("relation", "");
        row.put("candidateRelation", "value_flow");
        row.put("mappingOnly", true);
        row.put("mappingAuthority", "STATIC_FORMAT_AND_PORT_MAPPING");
        row.put("semanticAssertionsAllowed", false);
        row.put("eligibleForAutomaticDerivation", false);
        row.put("eligibleForAutomaticSmt", false);
        row.put("direction", "backward_provenance");
        return row;
    }

    private static Map<String, Object> projectedAliasProof(
            String method, String transfer, String kind, String fromBase,
            String toBase, String path, int unit) {
        Map<String, Object> row = edge(method, transfer, kind,
                fromBase + path, toBase + path, unit);
        authoritativeValueFlow(row);
        row.put("fieldSensitive", true);
        row.put("objectFromCell", fromBase);
        row.put("objectToCell", toBase);
        row.put("fieldPath", path);
        return row;
    }

    private static Map<String, Object> projectedDirectCopyProof(
            Map<String, Object> base, String path) {
        String method = String.valueOf(base.get("method"));
        int unit = ((Number) base.get("unitIndex")).intValue();
        Map<String, Object> row = projectedAliasProof(method, "VALUE_PASS",
                "projected_local_def_use",
                String.valueOf(base.get("fromCell")),
                String.valueOf(base.get("toCell")), path, unit);
        row.put("valueFlowAuthority",
                "PROJECTED_FROM_SOOT_EXACT_LOCAL_DIRECT_COPY_V1");
        row.put("baseValueFlowEdgeId", base.get("id"));
        row.put("baseValueFlowAuthority", base.get("valueFlowAuthority"));
        row.put("projectionBaseEdgeId", base.get("id"));
        row.put("authorityInheritance",
                "PROJECTED_EDGE_CANNOT_EXCEED_BASE_EDGE_V1");
        return row;
    }

    private static void authoritativeDirectCopyBase(
            Map<String, Object> edge, String directCopyKind) {
        authoritativeValueFlow(edge);
        edge.put("valueFlowAuthority", "SOOT_EXACT_LOCAL_DIRECT_COPY_V1");
        edge.put("directCopyKind", directCopyKind);
    }

    private static void authoritativeValueFlow(Map<String, Object> edge) {
        edge.put("relation", "value_flow");
        edge.put("candidateRelation", "value_flow");
        edge.put("mappingOnly", false);
        edge.put("semanticAssertionsAllowed", true);
        edge.put("eligibleForAutomaticDerivation", true);
        edge.put("eligibleForAutomaticSmt", true);
        edge.put("direction", "backward_provenance");
    }

    private static Map<String, Object> edge(String method, String transfer,
                                            String kind, String from, String to,
                                            int unit) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("method", method);
        row.put("transferKind", transfer);
        row.put("kind", kind);
        row.put("fromCell", from);
        row.put("toCell", to);
        row.put("unitIndex", unit);
        row.put("siteId", method + "#u" + unit + ":" + kind);
        row.put("id", "DF.TEST." + Integer.toHexString(
                (method + "\n" + transfer + "\n" + kind + "\n" + from
                        + "\n" + to + "\n" + unit).hashCode()));
        return row;
    }
}
