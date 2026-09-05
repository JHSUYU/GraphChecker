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

    /** A late alias affects later frames without rewriting earlier history. */
    @Test
    public void aSourceAliasIsAppliedFromItsRecordedSequenceForward()
            throws Exception {
        String outputProperty = System.getProperty(
                "causynth.trace.output.dir");
        Path output = folder.newFolder("late-registration").toPath();
        String actorBefore = "<example.ServiceActor: void beforeAlias()>";
        String helperBefore = "<example.Helper: void beforeAlias()>";
        String otherBefore = "<example.OtherService: void beforeAlias()>";
        String actorAfter = "<example.ServiceActor: void afterAlias()>";
        String helperAfter = "<example.Helper: void afterAlias()>";
        String otherAfter = "<example.OtherService: void afterAlias()>";
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
            long frame = CausynthTraceRecorder.enterMethod(
                    actorBefore, actor);
            long helperFrame = CausynthTraceRecorder.enterMethod(
                    helperBefore, helper);
            CausynthTraceRecorder.exitMethod(helperFrame, null, "");
            long otherFrame = CausynthTraceRecorder.enterMethod(
                    otherBefore, otherService);
            CausynthTraceRecorder.exitMethod(otherFrame, null, "");
            CausynthTraceRecorder.exitMethod(frame, null, "");

            // The node declares itself and claims the actor afterwards.
            CausynthTraceRecorder.registerSource(node, "CLUSTER_NODE",
                    "DATANODE", "cluster0/dn0", 1L);
            CausynthTraceRecorder.registerSourceAlias(actor, node);
            CausynthTraceRecorder.registerSource(otherNode, "CLUSTER_NODE",
                    "DATANODE", "cluster0/dn1", 1L);
            CausynthTraceRecorder.registerSourceAlias(otherService,
                    otherNode);

            // The same receivers enter again after their aliases exist.
            frame = CausynthTraceRecorder.enterMethod(actorAfter, actor);
            helperFrame = CausynthTraceRecorder.enterMethod(
                    helperAfter, helper);
            CausynthTraceRecorder.exitMethod(helperFrame, null, "");
            otherFrame = CausynthTraceRecorder.enterMethod(
                    otherAfter, otherService);
            CausynthTraceRecorder.exitMethod(otherFrame, null, "");
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
            Map<String, Boolean> receiverOwned = new LinkedHashMap<>();
            for (RuntimeRegionPlanner.MethodEvent event
                    : CausynthTraceRecorder.reattributedFramesForTests(
                            output.resolve("runtime_trace.jsonl").toFile(),
                            null)) {
                sources.put(event.method, event.sourceKey);
                receiverOwned.put(event.method, event.receiverAttributed);
            }
            assertEquals(RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                    sources.get(actorBefore));
            assertEquals(RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                    sources.get(helperBefore));
            assertEquals(RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                    sources.get(otherBefore));
            assertEquals("cluster0/dn0#epoch1", sources.get(actorAfter));
            assertEquals("an unregistered synchronous descendant inherits "
                            + "the nearest registered receiver owner",
                    "cluster0/dn0#epoch1", sources.get(helperAfter));
            assertEquals("a descendant's own registered receiver wins",
                    "cluster0/dn1#epoch1", sources.get(otherAfter));

            // Which authority answered is recorded, because replay can
            // re-check a receiver's own registration by object identity and
            // can only re-check an inherited one by context.
            assertEquals("the actor's own alias named it",
                    Boolean.TRUE, receiverOwned.get(actorAfter));
            assertEquals("the helper was named by its caller's registration",
                    Boolean.FALSE, receiverOwned.get(helperAfter));
            assertEquals("the other service's own alias named it",
                    Boolean.TRUE, receiverOwned.get(otherAfter));
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
