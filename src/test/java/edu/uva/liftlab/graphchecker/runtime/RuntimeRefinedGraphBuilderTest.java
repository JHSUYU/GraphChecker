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

    @Test
    public void objectIdentityBuildsUnboundedStructuredFieldChain()
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
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
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
        JsonObject binding = edge.getAsJsonArray("runtimeFieldBindings")
                .get(0).getAsJsonObject();
        assertEquals(Arrays.asList("b", "c", "d", "e", "f"),
                Arrays.asList(
                        binding.getAsJsonArray("fieldPath").get(0).getAsString(),
                        binding.getAsJsonArray("fieldPath").get(1).getAsString(),
                        binding.getAsJsonArray("fieldPath").get(2).getAsString(),
                        binding.getAsJsonArray("fieldPath").get(3).getAsString(),
                        binding.getAsJsonArray("fieldPath").get(4).getAsString()));
        assertEquals(10, binding.get("rootObjectId").getAsInt());
        assertEquals(50,
                binding.get("fieldReceiverObjectId").getAsInt());
        assertTrue(edge.get("runtimeObserved").getAsBoolean());
        assertFalse(edge.has("fieldPathDepth"));
    }

    @Test
    public void callOnObservedFieldContainerBindsContainerMutation()
            throws Exception {
        String mapField = "<example.A: java.util.Map values>";
        File candidate = write("mutation-candidate.jsonl", object(
                "schemaVersion", 3, "id", "DF.mutation",
                "kind", "field_mutation", "transferKind", "HEAP_WRITE",
                "method", METHOD, "unitIndex", 9,
                "fromCell", "value", "toCell", mapField));
        File skeleton = write("mutation-skeleton.jsonl", object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", METHOD,
                "anchorMethod", METHOD,
                "methods", Collections.singletonList(METHOD)));
        RuntimeRegionPlanner.MethodEvent root =
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        1, METHOD, 0, "", 11, 0, 0);
        RuntimeRegionPlanner.RuntimeEvent argument =
                new RuntimeRegionPlanner.RuntimeEvent(2, "METHOD_ARGUMENT",
                        METHOD, 11, 0, 0, "", 0, "example.A", 10, "",
                        false, false);
        RuntimeRegionPlanner.FieldAccessEvent mapRead =
                new RuntimeRegionPlanner.FieldAccessEvent(3, "FIELD_READ",
                        METHOD, 11, 1, METHOD + "#u1", mapField,
                        10, 50, "");
        RuntimeRegionPlanner.RuntimeEvent mutationCall =
                new RuntimeRegionPlanner.RuntimeEvent(4, "CALL_SITE_ENTER",
                        METHOD, 11, 1, 0, METHOD + "#u9",
                        "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                        -1, "java.util.Map", 50, "", false, false);
        RuntimeRegionPlanner.RuntimeEvent mutationReturn =
                new RuntimeRegionPlanner.RuntimeEvent(5, "CALL_SITE_RETURN",
                        METHOD, 11, 1, 0, METHOD + "#u9",
                        "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                        -1, "", 0, "", false, false);
        File output = new File(folder.getRoot(), "mutation-refined.jsonl");

        RuntimeRefinedGraphBuilder.Result result =
                RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                        Collections.singletonList(activation("REGION.1", 11,
                                "STATE_CONTEXT", METHOD)),
                        Collections.singletonList(root),
                        Arrays.asList(argument, mutationCall, mutationReturn),
                        Collections.singletonList(mapRead),
                        Collections.emptyList(), output.toPath());

        assertEquals(1, result.runtimeBoundEdgeCount);
        JsonObject edge = GSON.fromJson(Files.readAllLines(output.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        JsonObject binding = edge.getAsJsonArray("runtimeFieldBindings")
                .get(0).getAsJsonObject();
        assertEquals("CONTAINER_MUTATION",
                binding.get("bindingKind").getAsString());
        assertEquals(10, binding.get("fieldReceiverObjectId").getAsInt());
        assertEquals(50, binding.get("valueObjectId").getAsInt());
        assertEquals(5, binding.get("eventSeq").getAsLong());
        assertEquals(3, binding.get("writerFieldReadSeq").getAsLong());
        assertEquals(4, binding.get("mutatorEnterSeq").getAsLong());
        assertEquals(5, binding.get("mutationCompletionSeq").getAsLong());
        assertEquals("values", binding.getAsJsonArray("fieldPath")
                .get(0).getAsString());
    }

    @Test
    public void unrootedHelperFieldAccessRemainsActivationEvidence()
            throws Exception {
        String field = "<example.Hidden: java.util.Map values>";
        File candidate = write("unrooted-candidate.jsonl", object(
                "schemaVersion", 3, "id", "DF.unrooted",
                "kind", "field_read", "transferKind", "HEAP_READ",
                "method", METHOD, "unitIndex", 5,
                "fromCell", field, "toCell", "value"));
        File skeleton = write("unrooted-skeleton.jsonl", object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", METHOD,
                "anchorMethod", "<example.Missing: void primary()>",
                "anchorMethods", Arrays.asList(
                        "<example.Missing: void primary()>", METHOD),
                "methods", Collections.singletonList(METHOD)));
        RuntimeRegionPlanner.MethodEvent root =
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        1, METHOD, 0, "", 11, 0, 0);
        RuntimeRegionPlanner.FieldAccessEvent access =
                new RuntimeRegionPlanner.FieldAccessEvent(2, "FIELD_READ",
                        METHOD, 11, 5, METHOD + "#u5", field,
                        90, 91, "");
        File output = new File(folder.getRoot(), "unrooted-refined.jsonl");

        RuntimeRefinedGraphBuilder.Result result =
                RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                        Collections.singletonList(activation("REGION.1", 11,
                                "STATE_CONTEXT", METHOD)),
                        Collections.singletonList(root),
                        Collections.emptyList(),
                        Collections.singletonList(access),
                        Collections.emptyList(), output.toPath());

        assertEquals(1, result.runtimeBoundEdgeCount);
        JsonObject edge = GSON.fromJson(Files.readAllLines(output.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        JsonObject binding = edge.getAsJsonArray("runtimeFieldBindings")
                .get(0).getAsJsonObject();
        assertEquals("ACTIVATION_FIELD_ACCESS",
                binding.get("bindingKind").getAsString());
        assertEquals("OBSERVED_FIELD_RECEIVER",
                binding.get("rootKind").getAsString());
        assertEquals("ACTIVATION_LOCAL",
                binding.get("boundaryState").getAsString());
        assertEquals(RuntimeRefinedGraphBuilder.FIELD_ACCESS_AUTHORITY,
                binding.get("authority").getAsString());
    }

    @Test
    public void primitiveAccessorBindsReceiverReturnAndOccurrence()
            throws Exception {
        String callee = "<example.Key: long expiry()>";
        String field = "<example.KeyBase: long expiryDate>";
        String site = METHOD + "#u7";
        File candidate = write("accessor-candidate.jsonl", object(
                "schemaVersion", 3, "id", "DF.accessor",
                "kind", "accessor_field_return", "transferKind", "HEAP_READ",
                "method", METHOD, "unitIndex", 7, "siteId", site,
                "fromCell", field, "toCell", METHOD + "::expiry",
                "invoke", callee, "declaredFieldSignature", field,
                "accessorImplementationMethod",
                "<example.KeyBase: long expiry()>"));
        File skeleton = write("accessor-skeleton.jsonl", object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", METHOD,
                "anchorMethod", METHOD,
                "methods", Collections.singletonList(METHOD)));
        RuntimeRegionPlanner.MethodEvent root =
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        1, METHOD, 10, "example.Root", 11, 0, 0);
        RuntimeRegionPlanner.RuntimeEvent firstEnter =
                new RuntimeRegionPlanner.RuntimeEvent(2, "CALL_SITE_ENTER",
                        METHOD, 11, 21, 0, site, callee, -1,
                        "example.Key", 31, "", false, false);
        RuntimeRegionPlanner.RuntimeEvent firstReturn =
                new RuntimeRegionPlanner.RuntimeEvent(3, "CALL_SITE_RETURN",
                        METHOD, 11, 21, 0, site, callee, -1,
                        "", 0, "100", false, false);
        RuntimeRegionPlanner.RuntimeEvent secondEnter =
                new RuntimeRegionPlanner.RuntimeEvent(4, "CALL_SITE_ENTER",
                        METHOD, 11, 22, 0, site, callee, -1,
                        "example.Key", 32, "", false, false);
        RuntimeRegionPlanner.RuntimeEvent secondReturn =
                new RuntimeRegionPlanner.RuntimeEvent(5, "CALL_SITE_RETURN",
                        METHOD, 11, 22, 0, site, callee, -1,
                        "", 0, "200", false, false);
        File output = new File(folder.getRoot(), "accessor-refined.jsonl");

        RuntimeRefinedGraphBuilder.Result result =
                RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                        Collections.singletonList(activation("REGION.1", 11,
                                "STATE_CONTEXT", METHOD)),
                        Collections.singletonList(root),
                        Arrays.asList(firstEnter, firstReturn, secondEnter,
                                secondReturn), Collections.emptyList(),
                        Collections.emptyList(), output.toPath());

        assertEquals(1, result.runtimeBoundEdgeCount);
        JsonObject edge = GSON.fromJson(Files.readAllLines(output.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        assertTrue(edge.get("runtimeObserved").getAsBoolean());
        assertEquals(2, edge.getAsJsonArray("runtimeAccessorBindings").size());
        JsonObject second = edge.getAsJsonArray("runtimeAccessorBindings")
                .get(1).getAsJsonObject();
        assertEquals(32, second.get("receiverObjectId").getAsInt());
        assertEquals("200", second.get("primitiveValue").getAsString());
        assertEquals(2, second.get("accessorOccurrence").getAsInt());
        assertEquals("EXACT_RUNTIME_ACCESSOR_RECEIVER_RETURN_V1",
                second.get("authority").getAsString());
    }

    @Test
    public void referenceAccessorRetainsExactObjectLink() throws Exception {
        String callee = "<example.Box: example.Payload payload()>";
        String field = "<example.Box: example.Payload payload>";
        String site = METHOD + "#u7";
        File candidate = write("reference-accessor-candidate.jsonl", object(
                "schemaVersion", 3, "id", "DF.reference.accessor",
                "kind", "accessor_field_return", "transferKind", "HEAP_READ",
                "method", METHOD, "unitIndex", 7, "siteId", site,
                "fromCell", field, "toCell", METHOD + "::payload",
                "invoke", callee, "declaredFieldSignature", field,
                "accessorImplementationMethod", callee));
        File skeleton = write("reference-accessor-skeleton.jsonl", object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", METHOD,
                "anchorMethod", METHOD,
                "methods", Collections.singletonList(METHOD)));
        RuntimeRegionPlanner.MethodEvent root =
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        1, METHOD, 10, "example.Root", 11, 0, 0);
        RuntimeRegionPlanner.RuntimeEvent enter =
                new RuntimeRegionPlanner.RuntimeEvent(2, "CALL_SITE_ENTER",
                        METHOD, 11, 21, 0, site, callee, -1,
                        "example.Box", 31, "", false, false);
        RuntimeRegionPlanner.RuntimeEvent returned =
                new RuntimeRegionPlanner.RuntimeEvent(3, "CALL_SITE_RETURN",
                        METHOD, 11, 21, 0, site, callee, -1,
                        "example.Payload", 41, "", false, false);
        File output = new File(folder.getRoot(),
                "reference-accessor-refined.jsonl");

        RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                Collections.singletonList(activation("REGION.1", 11,
                        "STATE_CONTEXT", METHOD)),
                Collections.singletonList(root), Arrays.asList(enter,
                        returned), Collections.emptyList(),
                Collections.emptyList(), output.toPath());

        JsonObject edge = GSON.fromJson(Files.readAllLines(output.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        JsonObject binding = edge.getAsJsonArray("runtimeAccessorBindings")
                .get(0).getAsJsonObject();
        assertEquals(31, binding.get("receiverObjectId").getAsInt());
        assertEquals(41, binding.get("valueObjectId").getAsInt());
        assertEquals("example.Payload",
                binding.get("valueRuntimeType").getAsString());
    }

    @Test
    public void trustedConfiguredMappingBindsRpcAcrossActivations()
            throws Exception {
        String client = "<example.Client: void send(java.lang.String)>";
        String server = "<example.Server: void receive(java.lang.String)>";
        String adapter = "<example.Adapter: void invoke()>";
        File candidate = write("rpc-candidate.jsonl", object(
                "schemaVersion", 3, "id", "DF.rpc",
                "kind", "rpc_argument",
                "transferKind", "PROTOCOL_TRANSFER",
                "method", adapter, "unitIndex", 7,
                "fromCell", client + ".param0:java.lang.String",
                "toCell", server + ".param0:java.lang.String",
                "protocolStubMappingId", "example.rpc",
                "protocolTransport", "TEST_RPC",
                "protocolPort", "payload",
                "protocolDirection", "REQUEST",
                "protocolClientStub", client,
                "protocolServerStub", server,
                "invoke", client,
                "protocolClientArgument", 0,
                "protocolServerParameter", 0));
        File skeleton = writeRows("rpc-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.client",
                        "rootMethod", client, "anchorMethod", client,
                        "methods", Collections.singletonList(client),
                        "selection", "PROTOCOL_CONTEXT"),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.server",
                        "rootMethod", server, "anchorMethod", server,
                        "methods", Collections.singletonList(server),
                        "selection", "EXCEPTION_CONTEXT"));
        RuntimeRegionPlanner.MethodEvent clientCall =
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "c",
                        1, client, 0, "", 11, 0, 10,
                        101, 201, 301, 0, 0);
        RuntimeRegionPlanner.MethodEvent serverCall =
                new RuntimeRegionPlanner.MethodEvent(5, "test", "p", "s",
                        2, server, 0, "", 22, 0, 0,
                        102, 202, 302, 0, 301);
        RuntimeRegionPlanner.ProtocolEvent directSend =
                new RuntimeRegionPlanner.ProtocolEvent(3, "SEND", "TEST_RPC",
                        "native-10", "p", "c", 1,
                        client, 11, 91, client,
                        101, 201, 301, 0, 0);
        RuntimeRegionPlanner.ProtocolEvent directReceive =
                new RuntimeRegionPlanner.ProtocolEvent(4, "RECEIVE",
                        "TEST_RPC", "native-10", "p", "s",
                        2, server, 22, 0, "",
                        102, 202, 302, 0, 301);
        RuntimeRegionPlanner.RuntimeEvent callerSite =
                new RuntimeRegionPlanner.RuntimeEvent(2,
                        "CALL_SITE_ENTER", adapter, 9, 91, 0,
                        adapter + "#u7", client, -1, "example.Client", 0,
                        "", false, false);
        File refined = new File(folder.getRoot(), "rpc-refined.jsonl");

        RuntimeRefinedGraphBuilder.Result refinement =
                RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                        Arrays.asList(
                                activation("REGION.client", 11,
                                        "PROTOCOL_CONTEXT", client),
                                activation("REGION.server", 22,
                                        "EXCEPTION_CONTEXT", server)),
                        Arrays.asList(clientCall, serverCall),
                        Collections.singletonList(callerSite),
                        Collections.emptyList(),
                        Arrays.asList(directSend, directReceive),
                        refined.toPath());

        assertEquals(1, refinement.runtimeBoundEdgeCount);
        JsonObject refinedEdge = GSON.fromJson(Files.readAllLines(
                refined.toPath(), StandardCharsets.UTF_8).get(0),
                JsonObject.class);
        JsonObject binding = refinedEdge
                .getAsJsonArray("runtimeProtocolBindings")
                .get(0).getAsJsonObject();
        assertEquals(1, refinedEdge
                .getAsJsonArray("runtimeProtocolBindings").size());
        assertEquals("REGION.client",
                binding.get("fromRegionId").getAsString());
        assertEquals("REGION.server",
                binding.get("toRegionId").getAsString());
        assertEquals("TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                binding.get("authority").getAsString());
        assertEquals("EXACT_RUNTIME_PROTOCOL_CALLSITE_RESULT_V1",
                binding.get("callsiteAuthority").getAsString());
        assertEquals(adapter, binding.get("callerMethod").getAsString());
        assertEquals(7, binding.get("callerUnitIndex").getAsInt());
        assertEquals(0, binding.get("clientArgumentIndex").getAsInt());
        assertEquals(0, binding.get("serverParameterIndex").getAsInt());
        assertEquals(11, binding.get("fromRootCallId").getAsLong());
        assertEquals(22, binding.get("toRootCallId").getAsLong());
        assertEquals(2, binding.get("callerSiteEventSeq").getAsLong());
        assertEquals(3, binding.get("sendEventSeq").getAsLong());
        assertEquals(4, binding.get("receiveEventSeq").getAsLong());
        assertEquals(101, binding.get("fromOwnerId").getAsLong());
        assertEquals(201, binding.get("fromLaneId").getAsLong());
        assertEquals(301, binding.get("fromSpanId").getAsLong());
        assertEquals(102, binding.get("toOwnerId").getAsLong());
        assertEquals(202, binding.get("toLaneId").getAsLong());
        assertEquals(302, binding.get("toSpanId").getAsLong());
        assertEquals(301, binding.get("receiveRemoteParentSpanId")
                .getAsLong());
    }

    @Test
    public void configuredProtocolRejectsWrongRuntimeCallerSite()
            throws Exception {
        String client = "<example.Client: void send(java.lang.String)>";
        String server = "<example.Server: void receive(java.lang.String)>";
        String adapter = "<example.Adapter: void invoke()>";
        File candidate = write("rpc-wrong-site-candidate.jsonl", object(
                "schemaVersion", 3, "id", "DF.rpc.wrong",
                "kind", "rpc_argument",
                "transferKind", "PROTOCOL_TRANSFER",
                "method", adapter, "unitIndex", 8,
                "invoke", client,
                "fromCell", client + ".param0:java.lang.String",
                "toCell", server + ".param0:java.lang.String",
                "protocolStubMappingId", "example.rpc",
                "protocolTransport", "TEST_RPC",
                "protocolPort", "payload",
                "protocolDirection", "REQUEST",
                "protocolClientStub", client,
                "protocolServerStub", server));
        File skeleton = writeRows("rpc-wrong-site-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.client",
                        "rootMethod", client, "anchorMethod", client,
                        "methods", Collections.singletonList(client)),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.server",
                        "rootMethod", server, "anchorMethod", server,
                        "methods", Collections.singletonList(server)));
        RuntimeRegionPlanner.MethodEvent clientCall =
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "c",
                        1, client, 0, "", 11, 0, 10);
        RuntimeRegionPlanner.MethodEvent serverCall =
                new RuntimeRegionPlanner.MethodEvent(5, "test", "p", "s",
                        2, server, 0, "", 22, 0, 0);
        RuntimeRegionPlanner.RuntimeEvent callerSite =
                new RuntimeRegionPlanner.RuntimeEvent(10,
                        "CALL_SITE_ENTER", adapter, 9, 91, 0,
                        adapter + "#u7", client, -1, "example.Client", 0,
                        "", false, false);
        RuntimeRegionPlanner.ProtocolEvent send =
                new RuntimeRegionPlanner.ProtocolEvent(2, "SEND", "TEST_RPC",
                        "native-9", "p", "c", 1,
                        client, 11, 0, "");
        RuntimeRegionPlanner.ProtocolEvent receive =
                new RuntimeRegionPlanner.ProtocolEvent(4, "RECEIVE",
                        "TEST_RPC", "native-9", "p", "s",
                        2, server, 22, 0, "");
        File refined = new File(folder.getRoot(),
                "rpc-wrong-site-refined.jsonl");

        RuntimeRefinedGraphBuilder.Result result =
                RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                        Arrays.asList(
                                activation("REGION.client", 11,
                                        "PROTOCOL_CONTEXT", client),
                                activation("REGION.server", 22,
                                        "EXCEPTION_CONTEXT", server)),
                        Arrays.asList(clientCall, serverCall),
                        Collections.singletonList(callerSite),
                        Collections.emptyList(), Arrays.asList(send, receive),
                        refined.toPath());

        assertEquals(0, result.runtimeBoundEdgeCount);
        JsonObject edge = GSON.fromJson(Files.readAllLines(refined.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        assertFalse(edge.get("runtimeObserved").getAsBoolean());
        assertFalse(edge.has("runtimeProtocolBindings"));
    }

    @Test
    public void trustedResponseMappingUsesTraceLineage()
            throws Exception {
        String client = "<example.Client: example.Payload fetch()>";
        String server = "<example.Server: example.Payload fetch()>";
        String adapter = "<example.Adapter: void invoke()>";
        File candidate = write("rpc-response-candidate.jsonl", object(
                "schemaVersion", 3, "id", "DF.rpc.response",
                "kind", "rpc_return", "transferKind", "PROTOCOL_TRANSFER",
                "method", adapter, "unitIndex", 7, "invoke", client,
                "fromCell", server + ".return",
                "toCell", client + ".return",
                "protocolStubMappingId", "example.response",
                "protocolTransport", "TEST_RPC",
                "protocolPort", "response",
                "protocolDirection", "RESPONSE",
                "protocolClientStub", client,
                "protocolServerStub", server));
        File skeleton = writeRows("rpc-response-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.client", "rootMethod", client,
                        "anchorMethod", client,
                        "methods", Collections.singletonList(client)),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.server", "rootMethod", server,
                        "anchorMethod", server,
                        "methods", Collections.singletonList(server)));
        RuntimeRegionPlanner.MethodEvent clientCall =
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "c",
                        1, client, 0, "", 11, 0, 10,
                        101, 201, 301, 0, 0);
        RuntimeRegionPlanner.MethodEvent serverCall =
                new RuntimeRegionPlanner.MethodEvent(5, "test", "p", "s",
                        2, server, 0, "", 22, 0, 0,
                        102, 202, 302, 0, 301);
        RuntimeRegionPlanner.RuntimeEvent callerSite = runtimeEvent(2,
                "CALL_SITE_ENTER", adapter, 9, 91, adapter + "#u7",
                client);
        RuntimeRegionPlanner.RuntimeEvent producerReturn =
                new RuntimeRegionPlanner.RuntimeEvent(6,
                        "METHOD_EXIT_NORMAL", server, 22, 0, 0, "", "",
                        -1, "example.Payload", 2, "", false, false);
        RuntimeRegionPlanner.RuntimeEvent callerReturn = runtimeEvent(7,
                "CALL_SITE_RETURN", adapter, 9, 91, adapter + "#u7",
                client);
        RuntimeRegionPlanner.ProtocolEvent send =
                new RuntimeRegionPlanner.ProtocolEvent(3, "SEND", "TEST_RPC",
                        "native-a", "p", "c", 1,
                        client, 11, 91, client,
                        101, 201, 301, 0, 0);
        RuntimeRegionPlanner.ProtocolEvent receive =
                new RuntimeRegionPlanner.ProtocolEvent(4, "RECEIVE",
                        "TEST_RPC", "native-b", "p", "s", 2,
                        server, 22, 0, "",
                        102, 202, 302, 0, 301);
        File refined = new File(folder.getRoot(),
                "rpc-response-refined.jsonl");

        RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                Arrays.asList(activation("REGION.client", 11,
                                "PROTOCOL_CONTEXT", client),
                        activation("REGION.server", 22,
                                "EXCEPTION_CONTEXT", server)),
                Arrays.asList(clientCall, serverCall),
                Arrays.asList(callerSite, producerReturn, callerReturn),
                Collections.emptyList(), Arrays.asList(send, receive),
                refined.toPath());

        JsonObject edge = GSON.fromJson(Files.readAllLines(refined.toPath(),
                StandardCharsets.UTF_8).get(0), JsonObject.class);
        JsonObject binding = edge.getAsJsonArray("runtimeProtocolBindings")
                .get(0).getAsJsonObject();
        assertEquals("TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                binding.get("authority").getAsString());
        assertEquals(2, binding.get("callerSiteEventSeq").getAsLong());
        assertEquals(3, binding.get("sendEventSeq").getAsLong());
        assertEquals(4, binding.get("receiveEventSeq").getAsLong());
        assertEquals(22, binding.get("fromRootCallId").getAsLong());
        assertEquals(11, binding.get("toRootCallId").getAsLong());
        assertEquals(1, binding.get("callerResultObjectId").getAsInt());
        assertEquals("example.Payload",
                binding.get("callerResultRuntimeType").getAsString());
        assertEquals(7, binding.get("callerResultEventSeq").getAsLong());
        assertEquals(2, binding.get("producerResultObjectId").getAsInt());
        assertEquals("example.Payload",
                binding.get("producerResultRuntimeType").getAsString());
        assertEquals(6, binding.get("producerResultEventSeq").getAsLong());
        assertFalse(binding.has("writerEventSeq"));
        assertFalse(binding.has("readerEventSeq"));

        RuntimeRegionPlanner.RuntimeEvent duplicateProducerReturn =
                new RuntimeRegionPlanner.RuntimeEvent(6,
                        "METHOD_EXIT_NORMAL", server, 22, 0, 0, "", "",
                        -1, "example.Payload", 3, "", false, false);
        File ambiguous = new File(folder.getRoot(),
                "rpc-response-ambiguous-server-exit.jsonl");
        RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                Arrays.asList(activation("REGION.client", 11,
                                "PROTOCOL_CONTEXT", client),
                        activation("REGION.server", 22,
                                "EXCEPTION_CONTEXT", server)),
                Arrays.asList(clientCall, serverCall),
                Arrays.asList(callerSite, producerReturn,
                        duplicateProducerReturn, callerReturn),
                Collections.emptyList(), Arrays.asList(send, receive),
                ambiguous.toPath());
        JsonObject ambiguousBinding = GSON.fromJson(Files.readAllLines(
                ambiguous.toPath(), StandardCharsets.UTF_8).get(0),
                JsonObject.class).getAsJsonArray("runtimeProtocolBindings")
                .get(0).getAsJsonObject();
        assertFalse(ambiguousBinding.has("producerResultObjectId"));
        assertFalse(ambiguousBinding.has("producerResultEventSeq"));
    }

    @Test
    public void trustedRequestMappingUsesTraceLineage()
            throws Exception {
        String client = "<example.Client: void send(java.lang.String)>";
        String server = "<example.Server: void receive(java.lang.String)>";
        File candidate = write("rpc-request-candidate.jsonl", object(
                "schemaVersion", 3, "id", "DF.rpc.request",
                "kind", "rpc_argument", "transferKind", "PROTOCOL_TRANSFER",
                "method", client, "unitIndex", 7, "invoke", client,
                "fromCell", client + "::payload",
                "toCell", server + ".param0:java.lang.String",
                "protocolStubMappingId", "example.request",
                "protocolTransport", "TEST_RPC",
                "protocolPort", "payload",
                "protocolDirection", "REQUEST",
                "protocolClientStub", client,
                "protocolServerStub", server,
                "protocolClientArgument", 0,
                "protocolServerParameter", 0));
        File skeleton = writeRows("rpc-request-skeleton.jsonl",
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.client", "rootMethod", client,
                        "anchorMethod", client,
                        "methods", Collections.singletonList(client)),
                object("schemaVersion", 3, "kind", "REGION_SKELETON",
                        "regionId", "REGION.server", "rootMethod", server,
                        "anchorMethod", server,
                        "methods", Collections.singletonList(server)));
        RuntimeRegionPlanner.MethodEvent clientCall =
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "c",
                        1, client, 0, "", 11, 0, 0,
                        101, 201, 301, 0, 0);
        RuntimeRegionPlanner.MethodEvent serverCall =
                new RuntimeRegionPlanner.MethodEvent(6, "test", "p", "s",
                        2, server, 0, "", 22, 0, 0,
                        102, 202, 302, 0, 301);
        RuntimeRegionPlanner.RuntimeEvent callerSite = runtimeEvent(2,
                "CALL_SITE_ENTER", client, 11, 2, client + "#u7",
                client);
        RuntimeRegionPlanner.ProtocolEvent send =
                new RuntimeRegionPlanner.ProtocolEvent(4, "SEND", "TEST_RPC",
                        "native-a", "p", "c", 1,
                        client, 11, 2, client,
                        101, 201, 301, 0, 0);
        RuntimeRegionPlanner.ProtocolEvent receive =
                new RuntimeRegionPlanner.ProtocolEvent(8, "RECEIVE",
                        "TEST_RPC", "native-b", "p", "s", 2,
                        server, 22, 0, "",
                        102, 202, 302, 0, 301);
        File refined = new File(folder.getRoot(),
                "rpc-request-refined.jsonl");

        RuntimeRefinedGraphBuilder.refine(candidate, skeleton,
                Arrays.asList(activation("REGION.client", 11,
                                "PROTOCOL_CONTEXT", client),
                        activation("REGION.server", 22,
                                "EXCEPTION_CONTEXT", server)),
                Arrays.asList(clientCall, serverCall),
                Collections.singletonList(callerSite),
                Collections.emptyList(), Arrays.asList(send, receive),
                refined.toPath());

        JsonObject binding = GSON.fromJson(Files.readAllLines(
                refined.toPath(), StandardCharsets.UTF_8).get(0),
                JsonObject.class).getAsJsonArray("runtimeProtocolBindings")
                .get(0).getAsJsonObject();
        assertEquals("TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                binding.get("authority").getAsString());
        assertEquals(0, binding.get("clientArgumentIndex").getAsInt());
        assertEquals(0, binding.get("serverParameterIndex").getAsInt());
        assertEquals(4, binding.get("sendEventSeq").getAsLong());
        assertEquals(8, binding.get("receiveEventSeq").getAsLong());
    }

    private static RuntimeRegionPlanner.RuntimeEvent runtimeEvent(
            long seq, String kind, String method, long callId,
            long invocationId, String siteId, String declaredCallee) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, kind, method,
                callId, invocationId, 0, siteId, declaredCallee, -1,
                "example.Payload", 1, "", false, false);
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
