package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import com.google.gson.JsonArray;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Method;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class CausynthTraceRecorderTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void stateTraceRecordsReceiverAndValueIdentity() throws Exception {
        String previous = System.getProperty("causynth.trace.output.dir");
        Path output = folder.newFolder("trace").toPath();
        try {
            clear();
            System.setProperty("causynth.trace.output.dir",
                    output.toString());
            Object methodReceiver = new Object();
            Object fieldReceiver = new Object();
            Object value = new Object();
            String method = "<example.Root: void run()>";
            long call = CausynthTraceRecorder.enterMethod(method,
                    methodReceiver);
            CausynthTraceRecorder.recordField("FIELD_READ", method, 7,
                    "<example.Root: java.lang.Object child>",
                    methodReceiver, fieldReceiver, value, "");
            Object[] carrierArray = new Object[]{value};
            CausynthTraceRecorder.recordField("FIELD_WRITE", method, 8,
                    "<example.Root: java.lang.Object[] carrier>",
                    methodReceiver, fieldReceiver, carrierArray, "");
            CausynthTraceRecorder.recordArrayElement("ARRAY_READ", method,
                    9, carrierArray, 0, value);
            CausynthTraceRecorder.recordRpc("SEND", "TEST_RPC",
                    "native-1", null);
            CausynthTraceRecorder.exitActiveMethod(null, "");
            shutdown();

            List<String> lines = Files.readAllLines(
                    output.resolve("runtime_trace.jsonl"),
                    StandardCharsets.UTF_8);
            JsonObject field = null;
            JsonObject arrayRow = null;
            JsonObject rpc = null;
            for (String line : lines) {
                JsonObject row = JsonParser.parseString(line)
                        .getAsJsonObject();
                if ("FIELD_READ".equals(row.get("event").getAsString())) {
                    field = row;
                } else if ("ARRAY_READ".equals(
                        row.get("event").getAsString())) {
                    arrayRow = row;
                } else if ("RPC_SEND".equals(
                        row.get("event").getAsString())) {
                    rpc = row;
                }
            }
            assertEquals(3, field.get("schemaVersion").getAsInt());
            assertEquals(call, field.get("callId").getAsLong());
            assertEquals(7, field.get("unitIndex").getAsInt());
            assertNotEquals(0,
                    field.get("fieldReceiverObjectId").getAsInt());
            assertNotEquals(0, field.get("valueObjectId").getAsInt());
            assertNotEquals(field.get("fieldReceiverObjectId").getAsInt(),
                    field.get("valueObjectId").getAsInt());
            assertEquals(call, arrayRow.get("callId").getAsLong());
            assertEquals(9, arrayRow.get("unitIndex").getAsInt());
            assertEquals(0, arrayRow.get("arrayIndex").getAsInt());
            assertNotEquals(0, arrayRow.get("arrayObjectId").getAsInt());
            assertEquals(field.get("valueObjectId").getAsInt(),
                    arrayRow.get("elementObjectId").getAsInt());
            assertEquals("native-1",
                    rpc.get("correlationId").getAsString());
            assertEquals(call, rpc.get("callId").getAsLong());
        } finally {
            shutdown();
            clear();
            if (previous == null) {
                System.clearProperty("causynth.trace.output.dir");
            } else {
                System.setProperty("causynth.trace.output.dir", previous);
            }
        }
    }

    @Test
    public void configuredNestedArrayScalarsAreRecordedAtBothCallBoundaries()
            throws Exception {
        String outputProperty = System.getProperty(
                "causynth.trace.output.dir");
        String mappingProperty = System.getProperty(
                "causynth.protocol.stubs");
        Path output = folder.newFolder("boundary-scalars").toPath();
        Path mapping = folder.newFile("boundary-scalars.jsonl").toPath();
        String client = "<example.Client: " + BoundaryResponse.class.getName()
                + " fetch()>";
        String server = "<example.Server: " + BoundaryResponse.class.getName()
                + " fetch()>";
        writeBoundaryMapping(mapping, client, server, 4);
        try {
            clear();
            System.setProperty("causynth.trace.output.dir",
                    output.toString());
            System.setProperty("causynth.protocol.stubs",
                    mapping.toString());
            BoundaryResponse response = new BoundaryResponse(
                    new BoundaryKey(7), new BoundaryKey(9));

            long caller = CausynthTraceRecorder.enterMethod(
                    "<example.Caller: void run()>", new Object());
            long invocation = CausynthTraceRecorder.beginCall(caller,
                    "<example.Caller: void run()>", 3, client,
                    new Object());
            CausynthTraceRecorder.endCall(invocation, response, "");
            CausynthTraceRecorder.exitMethod(caller, null, "");
            long serverCall = CausynthTraceRecorder.enterMethod(server,
                    new Object());
            CausynthTraceRecorder.exitMethod(serverCall, response, "");
            shutdown();

            List<JsonObject> rows = traceRows(output,
                    "RPC_BOUNDARY_SCALAR");
            assertEquals(4, rows.size());
            int clientRows = 0;
            int serverRows = 0;
            for (JsonObject row : rows) {
                assertEquals(4, row.get("schemaVersion").getAsInt());
                assertEquals("example.fetch",
                        row.get("mappingId").getAsString());
                assertEquals("keys.id", row.get("leafId").getAsString());
                assertEquals("int", row.get("javaType").getAsString());
                assertEquals(4, row.get("containerBound").getAsInt());
                assertEquals(3, row.getAsJsonArray("declaredPath").size());
                assertEquals(1, row.getAsJsonArray("arrayIndices").size());
                assertNotEquals(0,
                        row.get("leafReceiverObjectId").getAsInt());
                assertEquals(
                        "EXACT_CONFIGURED_RPC_BOUNDARY_SCALAR_V1",
                        row.get("valueAuthority").getAsString());
                assertTrue(row.get("leafObservationComplete")
                        .getAsBoolean());
                assertEquals(2, row.get("leafValueCount").getAsInt());
                assertEquals("ROOT=2", row.getAsJsonArray(
                        "containerObservations").get(0).getAsString());
                assertTrue("7".equals(row.get("primitiveValue").getAsString())
                        || "9".equals(
                        row.get("primitiveValue").getAsString()));
                if ("CLIENT".equals(row.get("side").getAsString())) {
                    clientRows++;
                    assertEquals(invocation,
                            row.get("invocationId").getAsLong());
                    assertEquals("CALL_RETURN",
                            row.get("boundaryKind").getAsString());
                } else {
                    serverRows++;
                    assertEquals(serverCall, row.get("callId").getAsLong());
                    assertEquals("METHOD_RETURN",
                            row.get("boundaryKind").getAsString());
                }
            }
            assertEquals(2, clientRows);
            assertEquals(2, serverRows);
        } finally {
            shutdown();
            clear();
            restore("causynth.trace.output.dir", outputProperty);
            restore("causynth.protocol.stubs", mappingProperty);
        }
    }

    @Test
    public void insufficientConfiguredArrayBoundEmitsOneNamedGap()
            throws Exception {
        String outputProperty = System.getProperty(
                "causynth.trace.output.dir");
        String mappingProperty = System.getProperty(
                "causynth.protocol.stubs");
        Path output = folder.newFolder("boundary-gap").toPath();
        Path mapping = folder.newFile("boundary-gap.jsonl").toPath();
        String client = "<example.Client: " + BoundaryResponse.class.getName()
                + " fetch()>";
        String server = "<example.Server: " + BoundaryResponse.class.getName()
                + " fetch()>";
        writeBoundaryMapping(mapping, client, server, 1);
        try {
            clear();
            System.setProperty("causynth.trace.output.dir",
                    output.toString());
            System.setProperty("causynth.protocol.stubs",
                    mapping.toString());
            BoundaryResponse response = new BoundaryResponse(
                    new BoundaryKey(1), new BoundaryKey(2));

            long caller = CausynthTraceRecorder.enterMethod(
                    "<example.Caller: void run()>", new Object());
            long invocation = CausynthTraceRecorder.beginCall(caller,
                    "<example.Caller: void run()>", 4, client,
                    new Object());
            CausynthTraceRecorder.endCall(invocation, response, "");
            CausynthTraceRecorder.exitMethod(caller, null, "");
            shutdown();

            assertTrue(traceRows(output, "RPC_BOUNDARY_SCALAR").isEmpty());
            List<JsonObject> gaps = traceRows(output,
                    "RPC_BOUNDARY_SCALAR_GAP");
            assertEquals(1, gaps.size());
            JsonObject gap = gaps.get(0);
            assertEquals("CONTAINER_BOUND_INSUFFICIENT",
                    gap.get("gap").getAsString());
            assertEquals(2, gap.get("observedContainerWidth").getAsInt());
            assertEquals("CONFIGURED_RPC_BOUNDARY_SCALAR_GAP_V1",
                    gap.get("valueAuthority").getAsString());
            assertTrue(gap.get("leafObservationComplete").getAsBoolean());
            assertEquals(0, gap.get("leafValueCount").getAsInt());
            assertEquals("ROOT=2", gap.getAsJsonArray(
                    "containerObservations").get(0).getAsString());
            assertEquals(invocation, gap.get("invocationId").getAsLong());
        } finally {
            shutdown();
            clear();
            restore("causynth.trace.output.dir", outputProperty);
            restore("causynth.protocol.stubs", mappingProperty);
        }
    }

    @Test
    public void boundaryScalarTraceSchemaIsBidirectionallyStrict()
            throws Exception {
        assertIOException(() -> CausynthTraceRecorder.parseTraceLineForTests(
                "{\"schemaVersion\":3,\"event\":"
                        + "\"RPC_BOUNDARY_SCALAR\"}"));
        assertIOException(() -> CausynthTraceRecorder.parseTraceLineForTests(
                "{\"schemaVersion\":4,\"event\":\"FIELD_READ\"}"));
    }

    @Test
    public void configuredBoundaryCompletenessRejectsMissingExtraAndChangedRows()
            throws Exception {
        String previous = System.getProperty("causynth.protocol.stubs");
        Path mapping = folder.newFile("complete-boundary.jsonl").toPath();
        String client = "<example.Client: example.Reply fetch()>";
        String server = "<example.Server: example.Reply fetch()>";
        String leaf = "<example.Reply: int code>";
        writeScalarBoundaryMapping(mapping, client, server, "code", leaf);
        try {
            System.setProperty("causynth.protocol.stubs",
                    mapping.toString());
            RuntimeRegionPlanner.RuntimeEvent serverExit =
                    new RuntimeRegionPlanner.RuntimeEvent(
                            10, "METHOD_EXIT_NORMAL", server, 2, 0, 0,
                            "", "", -1, "example.Reply", 500, "",
                            false, false);
            RuntimeRegionPlanner.RuntimeEvent clientReturn =
                    new RuntimeRegionPlanner.RuntimeEvent(
                            20, "CALL_SITE_RETURN",
                            "<example.Caller: void run()>", 1, 91, 0,
                            "", client, -1, "example.Reply", 300, "",
                            false, false);
            RuntimeRegionPlanner.ProtocolEvent producer = boundaryValue(
                    30, "SERVER", "METHOD_RETURN", server, 2, 0, 10,
                    500, 501, "code", leaf);
            RuntimeRegionPlanner.ProtocolEvent consumer = boundaryValue(
                    31, "CLIENT", "CALL_RETURN", client, 1, 91, 20,
                    300, 301, "code", leaf);
            List<RuntimeRegionPlanner.RuntimeEvent> execution = Arrays.asList(
                    serverExit, clientReturn);
            CausynthTraceRecorder.requireConfiguredBoundaryScalarEvidenceForTests(
                    execution, Arrays.asList(producer, consumer));

            assertIOException(() -> CausynthTraceRecorder
                    .requireConfiguredBoundaryScalarEvidenceForTests(
                            execution, Collections.singletonList(producer)));
            RuntimeRegionPlanner.ProtocolEvent extra = boundaryValue(
                    32, "CLIENT", "CALL_RETURN", client, 1, 91, 20,
                    300, 301, "notConfigured", leaf);
            assertIOException(() -> CausynthTraceRecorder
                    .requireConfiguredBoundaryScalarEvidenceForTests(
                            execution, Arrays.asList(producer, consumer,
                                    extra)));

            writeScalarBoundaryMapping(mapping, client, server,
                    "renamed", leaf);
            assertIOException(() -> CausynthTraceRecorder
                    .requireConfiguredBoundaryScalarEvidenceForTests(
                            execution, Arrays.asList(producer, consumer)));
        } finally {
            restore("causynth.protocol.stubs", previous);
        }
    }

    @Test
    public void configuredClientBoundaryAcceptsImplementationOnly()
            throws Exception {
        String previous = System.getProperty("causynth.protocol.stubs");
        Path mapping = folder.newFile("client-implementation.jsonl").toPath();
        String subSignature = BoundaryResponse.class.getName() + " fetch()";
        String configuredClient = "<" + BoundaryClient.class.getName()
                + ": " + subSignature + ">";
        String concreteClient = "<" + ConcreteBoundaryClient.class.getName()
                + ": " + subSignature + ">";
        String unrelatedClient = "<" + UnrelatedBoundaryClient.class.getName()
                + ": " + subSignature + ">";
        String server = "<example.Server: " + subSignature + ">";
        String leaf = "<example.Reply: int code>";
        writeScalarBoundaryMapping(mapping, configuredClient, server,
                "code", leaf);
        try {
            System.setProperty("causynth.protocol.stubs", mapping.toString());
            RuntimeRegionPlanner.RuntimeEvent concreteReturn =
                    new RuntimeRegionPlanner.RuntimeEvent(
                            20, "CALL_SITE_RETURN",
                            "<example.Caller: void run()>", 1, 91, 0,
                            "", concreteClient, -1, "example.Reply", 300,
                            "", false, false);
            RuntimeRegionPlanner.ProtocolEvent concreteValue = boundaryValue(
                    21, "CLIENT", "CALL_RETURN", concreteClient, 1, 91,
                    20, 300, 301, "code", leaf);
            CausynthTraceRecorder.requireConfiguredBoundaryScalarEvidenceForTests(
                    Collections.singletonList(concreteReturn),
                    Collections.singletonList(concreteValue));

            RuntimeRegionPlanner.RuntimeEvent unrelatedReturn =
                    new RuntimeRegionPlanner.RuntimeEvent(
                            30, "CALL_SITE_RETURN",
                            "<example.Caller: void run()>", 2, 92, 0,
                            "", unrelatedClient, -1, "example.Reply", 400,
                            "", false, false);
            RuntimeRegionPlanner.ProtocolEvent unrelatedValue = boundaryValue(
                    31, "CLIENT", "CALL_RETURN", unrelatedClient, 2, 92,
                    30, 400, 401, "code", leaf);
            assertIOException(() -> CausynthTraceRecorder
                    .requireConfiguredBoundaryScalarEvidenceForTests(
                            Collections.singletonList(unrelatedReturn),
                            Collections.singletonList(unrelatedValue)));
        } finally {
            restore("causynth.protocol.stubs", previous);
        }
    }

    @Test
    public void selectedSkeletonKeepsStaticPotentialMethods() throws Exception {
        String root = "<example.Root: void run()>";
        String observed = "<example.Root: void observed()>";
        String latent = "<example.Root: void latent()>";
        Path candidates = folder.newFile("candidate-skeletons.jsonl")
                .toPath();
        Path selected = folder.newFile("selected-skeletons.jsonl").toPath();
        Files.write(candidates, Collections.singletonList(
                "{\"schemaVersion\":3,\"kind\":\"REGION_SKELETON\","
                        + "\"regionId\":\"REGION.1\","
                        + "\"rootMethod\":\"" + root + "\","
                        + "\"anchorMethod\":\"" + observed + "\","
                        + "\"methods\":[\"" + root + "\",\""
                        + observed + "\",\"" + latent + "\"]}"),
                StandardCharsets.UTF_8);

        Map<String, Object> activation = new LinkedHashMap<>();
        activation.put("regionId", "REGION.1");
        activation.put("rootMethod", root);
        activation.put("selection", "STATE_CONTEXT");
        activation.put("anchorMethod", observed);
        activation.put("anchorMethods", Collections.singletonList(observed));
        activation.put("observedMethods", Arrays.asList(root, observed));
        invokeWriteSelectedSkeletons(candidates, selected,
                Collections.singletonList(activation));

        JsonObject result = JsonParser.parseString(Files.readAllLines(
                selected, StandardCharsets.UTF_8).get(0)).getAsJsonObject();
        assertEquals(3, result.getAsJsonArray("methods").size());
        assertEquals(latent, result.getAsJsonArray("methods").get(2)
                .getAsString());
        assertEquals(2, result.getAsJsonArray("baselineObservedMethods")
                .size());
        assertEquals(observed,
                result.getAsJsonArray("baselineObservedMethods").get(1)
                        .getAsString());
    }

    @Test
    public void selectedSkeletonMergesCoalescedStaticTemplates()
            throws Exception {
        String root = "<example.Root: void run()>";
        String stateAnchor = "<example.State: void read()>";
        String helperRoot = "<example.Helper: void call()>";
        String failureAnchor = "<example.Helper: void fail()>";
        Path candidates = folder.newFile("coalesced-candidates.jsonl")
                .toPath();
        Path selected = folder.newFile("coalesced-selected.jsonl").toPath();
        Files.write(candidates, Arrays.asList(
                "{\"schemaVersion\":3,\"kind\":\"REGION_SKELETON\","
                        + "\"regionId\":\"REGION.root\","
                        + "\"rootMethod\":\"" + root + "\","
                        + "\"anchorMethod\":\"" + stateAnchor + "\","
                        + "\"methods\":[\"" + root + "\",\""
                        + stateAnchor + "\"]}",
                "{\"schemaVersion\":3,\"kind\":\"REGION_SKELETON\","
                        + "\"regionId\":\"REGION.failure\","
                        + "\"rootMethod\":\"" + helperRoot + "\","
                        + "\"anchorMethod\":\"" + failureAnchor + "\","
                        + "\"methods\":[\"" + helperRoot + "\",\""
                        + failureAnchor + "\"]}"), StandardCharsets.UTF_8);

        Map<String, Object> activation = new LinkedHashMap<>();
        activation.put("regionId", "REGION.root");
        activation.put("regionIds", Arrays.asList(
                "REGION.root", "REGION.failure"));
        activation.put("rootMethod", root);
        activation.put("selection", "EXCEPTION_CONTEXT");
        activation.put("anchorMethod", failureAnchor);
        activation.put("anchorMethods",
                Collections.singletonList(failureAnchor));
        activation.put("observedMethods", Arrays.asList(root, failureAnchor));
        invokeWriteSelectedSkeletons(candidates, selected,
                Collections.singletonList(activation));

        List<String> lines = Files.readAllLines(selected,
                StandardCharsets.UTF_8);
        assertEquals(1, lines.size());
        JsonObject result = JsonParser.parseString(lines.get(0))
                .getAsJsonObject();
        assertEquals(4, result.getAsJsonArray("methods").size());
        assertEquals(failureAnchor, result.get("anchorMethod").getAsString());
    }

    private static void invokeWriteSelectedSkeletons(
            Path candidates, Path selected,
            List<Map<String, Object>> activations) throws Exception {
        Method method = CausynthTraceRecorder.class.getDeclaredMethod(
                "writeSelectedSkeletons", java.io.File.class,
                java.io.File.class, java.util.Collection.class);
        method.setAccessible(true);
        method.invoke(null, candidates.toFile(), selected.toFile(),
                activations);
    }

    private static void writeBoundaryMapping(Path path, String client,
                                             String server, int bound)
            throws Exception {
        String responseType = BoundaryResponse.class.getName();
        String keyType = BoundaryKey.class.getName();
        JsonObject mapping = new JsonObject();
        mapping.addProperty("schemaVersion", 2);
        mapping.addProperty("kind", "PROTOCOL_STUB_MAPPING");
        mapping.addProperty("id", "example.fetch");
        mapping.addProperty("clientStub", client);
        mapping.addProperty("serverStub", server);
        mapping.add("request", new JsonArray());
        mapping.addProperty("response", true);
        JsonObject leaf = new JsonObject();
        leaf.addProperty("leafId", "keys.id");
        leaf.addProperty("direction", "RESPONSE");
        JsonArray declaredPath = new JsonArray();
        declaredPath.add("<" + responseType + ": " + keyType
                + "[] keys>");
        declaredPath.add("[]");
        declaredPath.add("<" + keyType + ": int id>");
        leaf.add("declaredPath", declaredPath);
        leaf.addProperty("containerBound", bound);
        JsonArray leaves = new JsonArray();
        leaves.add(leaf);
        mapping.add("boundaryScalarLeaves", leaves);
        Files.write(path, Collections.singletonList(mapping.toString()),
                StandardCharsets.UTF_8);
    }

    private static void writeScalarBoundaryMapping(
            Path path, String client, String server, String leafId,
            String declaration) throws Exception {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("schemaVersion", 2);
        mapping.addProperty("kind", "PROTOCOL_STUB_MAPPING");
        mapping.addProperty("id", "example.fetch");
        mapping.addProperty("clientStub", client);
        mapping.addProperty("serverStub", server);
        mapping.add("request", new JsonArray());
        mapping.addProperty("response", true);
        JsonObject leaf = new JsonObject();
        leaf.addProperty("leafId", leafId);
        leaf.addProperty("direction", "RESPONSE");
        JsonArray declaredPath = new JsonArray();
        declaredPath.add(declaration);
        leaf.add("declaredPath", declaredPath);
        JsonArray leaves = new JsonArray();
        leaves.add(leaf);
        mapping.add("boundaryScalarLeaves", leaves);
        Files.write(path, Collections.singletonList(mapping.toString()),
                StandardCharsets.UTF_8);
    }

    private static RuntimeRegionPlanner.ProtocolEvent boundaryValue(
            long seq, String side, String kind, String method, long callId,
            long invocationId, long boundarySeq, int rootObjectId,
            int receiverObjectId, String leafId, String declaration) {
        return new RuntimeRegionPlanner.ProtocolEvent(
                seq, "RPC_BOUNDARY_SCALAR", "example.fetch",
                "RESPONSE", side, "response", leafId, kind, method,
                callId, invocationId, boundarySeq, rootObjectId,
                receiverObjectId, 0,
                Collections.singletonList(declaration),
                Collections.emptyList(), "int", "7", false, 0, -1,
                "EXACT_CONFIGURED_RPC_BOUNDARY_SCALAR_V1", "", true, 1,
                Collections.emptyList());
    }

    private static void assertIOException(IoAction action) throws Exception {
        try {
            action.run();
            fail("expected IOException");
        } catch (IOException expected) {
            assertFalse(expected.getMessage().isEmpty());
        }
    }

    private interface IoAction {
        void run() throws Exception;
    }

    private static List<JsonObject> traceRows(Path output, String event)
            throws Exception {
        List<JsonObject> result = new java.util.ArrayList<>();
        for (String line : Files.readAllLines(
                output.resolve("runtime_trace.jsonl"),
                StandardCharsets.UTF_8)) {
            JsonObject row = JsonParser.parseString(line).getAsJsonObject();
            if (event.equals(row.get("event").getAsString())) {
                result.add(row);
            }
        }
        return result;
    }

    private static final class BoundaryResponse {
        private final BoundaryKey[] keys;

        private BoundaryResponse(BoundaryKey... keys) {
            this.keys = keys;
        }
    }

    private static final class BoundaryKey {
        private final int id;

        private BoundaryKey(int id) {
            this.id = id;
        }
    }

    private interface BoundaryClient {
        BoundaryResponse fetch();
    }

    private static final class ConcreteBoundaryClient
            implements BoundaryClient {
        @Override
        public BoundaryResponse fetch() {
            return null;
        }
    }

    private static final class UnrelatedBoundaryClient {
        public BoundaryResponse fetch() {
            return null;
        }
    }

    private static void shutdown() throws Exception {
        Method method = CausynthTraceRecorder.class.getDeclaredMethod(
                "shutdown");
        method.setAccessible(true);
        method.invoke(null);
    }

    private static void clear() throws Exception {
        Method method = CausynthTraceRecorder.class.getDeclaredMethod(
                "clearInMemoryTrace");
        method.setAccessible(true);
        method.invoke(null);
    }

    private static void restore(String property, String value) {
        if (value == null) {
            System.clearProperty(property);
        } else {
            System.setProperty(property, value);
        }
    }

}
