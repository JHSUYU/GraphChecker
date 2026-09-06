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
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class CausynthTraceRecorderTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

        @Test
    public void exchangeRecorderHasOneFullyStatedAbi() throws Exception {
        int exchanges = 0;
        for (Method method : CausynthTraceRecorder.class
                .getDeclaredMethods()) {
            if ("recordExchange".equals(method.getName())) {
                assertEquals(String.valueOf(method), 6,
                        method.getParameterCount());
                exchanges++;
            }
        }
        assertEquals(1, exchanges);
        String outputProperty = System.getProperty(
                "causynth.trace.output.dir");
        Path output = folder.newFolder("exchange-identity").toPath();
        try {
            clear();
            System.setProperty("causynth.trace.output.dir",
                    output.toString());
            Object client = new Object();
            CausynthTraceRecorder.registerSource(client, "EXTERNAL_APP",
                    "CLIENT", "app/client0", 0L);
            long request = CausynthTraceRecorder.beginSourceRequest(client,
                    "fetchindex");
            String header = CausynthTraceRecorder.outboundExchange(
                    "HTTP", "exchange-1", "attempt-2", "REQUEST", client);
            assertTrue(header.startsWith("1|"));
            CausynthTraceRecorder.endSourceRequest(request, "fetchindex");
            shutdown();
            JsonObject row = traceRows(output, "EXCHANGE_SEND").get(0);
            assertEquals("attempt-2", row.get("attemptId").getAsString());
            assertEquals("REQUEST", row.get("half").getAsString());
            assertEquals("fetchindex", row.get("requestApi").getAsString());
        } finally {
            shutdown();
            clear();
            restore("causynth.trace.output.dir", outputProperty);
        }
    }

    @Test
    public void activeCallSiteContextDoesNotSurviveThrowOrStaleReplacement()
            throws Exception {
        String results = System.getProperty("causynth.concolic.results");
        try {
            clear();
            System.setProperty("causynth.concolic.results",
                    folder.newFile("throw-results.jsonl").getPath());
            long root = CausynthTraceRecorder.enterMethod(
                    "<example.Root: void run()>", new Object());
            long stale = CausynthTraceRecorder.beginCall(root,
                    "<example.Root: void run()>", 1,
                    "<example.Stale: void call()>", null);
            assertCallSite("<example.Root: void run()>#u1",
                    "<example.Stale: void call()>", root, stale);
            long replacement = CausynthTraceRecorder.beginCall(root,
                    "<example.Root: void run()>", 2,
                    "<example.Throwing: void call()>", null);
            assertCallSite("<example.Root: void run()>#u2",
                    "<example.Throwing: void call()>", root, replacement);

            long child = CausynthTraceRecorder.enterMethod(
                    "<example.Throwing: void call()>", new Object());
            CausynthTraceRecorder.throwMethod(child,
                    new IllegalStateException("expected"));
            assertNull(CausynthTraceRecorder.currentCallSiteContext());
            CausynthTraceRecorder.exitMethod(root, null, "");
        } finally {
            clear();
            restore("causynth.concolic.results", results);
        }
    }

    private static void assertCallSite(String siteId, String callee,
                                       long ownerCallId,
                                       long invocationId) {
        CausynthTraceRecorder.ActiveCallSiteContext context =
                CausynthTraceRecorder.currentCallSiteContext();
        assertNotNull(context);
        assertEquals(siteId, context.siteId());
        assertEquals(callee, context.declaredCallee());
        assertEquals(ownerCallId, context.ownerCallId());
        assertEquals(invocationId, context.invocationId());
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
