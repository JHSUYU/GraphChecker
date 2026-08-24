package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Method;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class CausynthTraceRecorderTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /**
     * The recorded trace schema is strict in both directions -- a row the
     * reader does not know and a version it does not know are equally
     * unreadable.
     */
    @Test
    public void theTraceSchemaIsStrict()
            throws Exception {
        assertIOException(() -> CausynthTraceRecorder.parseTraceLineForTests(
                "{\"schemaVersion\":4,\"event\":\"FIELD_READ\"}"));
    }

    @Test
    public void rpcRecorderHasOneFullyStatedAbi() throws Exception {
        for (Method method : CausynthTraceRecorder.class
                .getDeclaredMethods()) {
            if ("recordRpc".equals(method.getName())) {
                assertEquals(String.valueOf(method), 6,
                        method.getParameterCount());
            }
        }
        String outputProperty = System.getProperty(
                "causynth.trace.output.dir");
        Path output = folder.newFolder("rpc-identity").toPath();
        try {
            clear();
            System.setProperty("causynth.trace.output.dir",
                    output.toString());
            CausynthTraceRecorder.recordRpc("SEND", "EXAMPLE",
                    "exchange-1", "attempt-2", "REQUEST", null);
            shutdown();
            JsonObject row = traceRows(output, "RPC_SEND").get(0);
            assertEquals("attempt-2", row.get("attemptId").getAsString());
            assertEquals("REQUEST", row.get("half").getAsString());
        } finally {
            shutdown();
            clear();
            restore("causynth.trace.output.dir", outputProperty);
        }
    }

    @Test
    public void activeCallSiteContextTracksNestedNormalReturn()
            throws Exception {
        String results = System.getProperty("causynth.concolic.results");
        try {
            clear();
            System.setProperty("causynth.concolic.results",
                    folder.newFile("context-results.jsonl").getPath());
            long root = CausynthTraceRecorder.enterMethod(
                    "<example.Root: void run()>", new Object());
            long outer = CausynthTraceRecorder.beginCall(root,
                    "<example.Root: void run()>", 4,
                    "<example.Helper: void call()>", new Object());
            assertCallSite("<example.Root: void run()>#u4",
                    "<example.Helper: void call()>", root, outer);

            long child = CausynthTraceRecorder.enterMethod(
                    "<example.Helper: void call()>", new Object());
            long nested = CausynthTraceRecorder.beginCall(child,
                    "<example.Helper: void call()>", 7,
                    "<example.Source: void publish()>", null);
            assertCallSite("<example.Helper: void call()>#u7",
                    "<example.Source: void publish()>", child, nested);
            CausynthTraceRecorder.endCall(nested, null, "");
            assertCallSite("<example.Root: void run()>#u4",
                    "<example.Helper: void call()>", root, outer);
            CausynthTraceRecorder.exitMethod(child, null, "");
            CausynthTraceRecorder.endCall(outer, null, "");
            assertNull(CausynthTraceRecorder.currentCallSiteContext());
            CausynthTraceRecorder.exitMethod(root, null, "");
        } finally {
            clear();
            restore("causynth.concolic.results", results);
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

    /**
     * A frame stamped before its receiver was registered is attributed to
     * that receiver after the trace is re-read.
     *
     * <p>This is the production sequence and it is deliberately awkward: the
     * registration is written, the process state is cleared, and only the
     * durable trace is left to answer.  A DataNode starts its
     * {@code BPServiceActor} thread long before it declares which source owns
     * it, so the frame freezes on whoever started the thread; the
     * registration that corrects it arrives later in the same run.  The row
     * therefore has to carry the recorded object identity, because a class
     * name cannot tell two nodes' service objects apart.</p>
     */
    @Test
    public void aFrameIsAttributedToItsReceiverAfterTheTraceIsReread()
            throws Exception {
        String outputProperty = System.getProperty(
                "causynth.trace.output.dir");
        Path output = folder.newFolder("late-registration").toPath();
        String actorRun = "<example.ServiceActor: void run()>";
        String helperRun = "<example.Helper: void run()>";
        String otherRun = "<example.OtherService: void run()>";
        try {
            clear();
            System.setProperty("causynth.trace.output.dir",
                    output.toString());
            Object node = new Object();
            Object actor = new Object();
            Object helper = new Object();
            Object otherNode = new Object();
            Object otherService = new Object();

            // The service thread runs first; nothing about its owner is known
            // and the frame is stamped with what is ambient, which is nothing.
            long frame = CausynthTraceRecorder.enterMethod(actorRun, actor);
            long helperFrame = CausynthTraceRecorder.enterMethod(
                    helperRun, helper);
            CausynthTraceRecorder.exitMethod(helperFrame, null, "");
            long otherFrame = CausynthTraceRecorder.enterMethod(
                    otherRun, otherService);
            CausynthTraceRecorder.exitMethod(otherFrame, null, "");
            // The node declares itself and claims the actor afterwards.
            CausynthTraceRecorder.registerSource(node, "CLUSTER_NODE",
                    "DATANODE", "cluster0/dn0", 1L);
            CausynthTraceRecorder.registerSourceAlias(actor, node);
            CausynthTraceRecorder.registerSource(otherNode, "CLUSTER_NODE",
                    "DATANODE", "cluster0/dn1", 1L);
            CausynthTraceRecorder.registerSourceAlias(otherService,
                    otherNode);
            CausynthTraceRecorder.exitMethod(frame, null, "");
            shutdown();

            // The durable row carries the identity, not just the class: two
            // nodes' actors are the same class and must not collapse.
            List<JsonObject> aliases = traceRows(output, "SOURCE_ALIAS");
            assertEquals(2, aliases.size());
            JsonObject actorAlias = aliases.get(0);
            assertTrue(actorAlias.has("objectId"));
            int recorded = actorAlias.get("objectId").getAsInt();
            assertEquals(recorded, traceRows(output, "METHOD_ENTER").get(0)
                    .get("objectId").getAsInt());

            // Clear and re-read: the in-memory binding is gone, exactly as it
            // is when the aggregation path plans.
            Map<String, String> sources = new LinkedHashMap<>();
            for (RuntimeRegionPlanner.MethodEvent event
                    : CausynthTraceRecorder.reattributedFramesForTests(
                            output.resolve("runtime_trace.jsonl").toFile(),
                            null)) {
                sources.put(event.method, event.sourceKey);
            }
            assertEquals("cluster0/dn0#epoch1", sources.get(actorRun));
            assertEquals("an unregistered synchronous descendant inherits "
                            + "the nearest registered receiver owner",
                    "cluster0/dn0#epoch1", sources.get(helperRun));
            assertEquals("a descendant's own registered receiver wins",
                    "cluster0/dn1#epoch1", sources.get(otherRun));
        } finally {
            shutdown();
            clear();
            restore("causynth.trace.output.dir", outputProperty);
        }
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
