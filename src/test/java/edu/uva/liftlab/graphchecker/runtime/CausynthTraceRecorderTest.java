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
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;

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
            CausynthTraceRecorder.recordRpcEndpoint("SEND", "TEST_RPC",
                    "wire-1", "example.send");
            CausynthTraceRecorder.exitActiveMethod(null, "");
            shutdown();

            List<String> lines = Files.readAllLines(
                    output.resolve("runtime_trace.jsonl"),
                    StandardCharsets.UTF_8);
            JsonObject field = null;
            JsonObject rpc = null;
            for (String line : lines) {
                JsonObject row = JsonParser.parseString(line)
                        .getAsJsonObject();
                if ("FIELD_READ".equals(row.get("event").getAsString())) {
                    field = row;
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
            assertFalse(field.has("valueFingerprint"));
            assertEquals("wire-1", rpc.get("wireId").getAsString());
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
}
