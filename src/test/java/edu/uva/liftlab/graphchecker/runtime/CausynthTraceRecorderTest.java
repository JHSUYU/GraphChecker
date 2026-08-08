package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Method;
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
            JsonObject snapshot = null;
            JsonObject rpc = null;
            for (String line : lines) {
                JsonObject row = JsonParser.parseString(line)
                        .getAsJsonObject();
                if ("FIELD_READ".equals(row.get("event").getAsString())) {
                    field = row;
                } else if ("ARRAY_READ".equals(
                        row.get("event").getAsString())) {
                    arrayRow = row;
                } else if ("ARRAY_SNAPSHOT".equals(
                        row.get("event").getAsString())) {
                    snapshot = row;
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
            assertEquals(8, snapshot.get("unitIndex").getAsInt());
            assertEquals(1, snapshot.get("arrayLength").getAsInt());
            assertEquals(0, snapshot.get("arrayIndex").getAsInt());
            assertTrue(snapshot.get("snapshotBoundarySeq").getAsLong()
                    < snapshot.get("seq").getAsLong());
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
