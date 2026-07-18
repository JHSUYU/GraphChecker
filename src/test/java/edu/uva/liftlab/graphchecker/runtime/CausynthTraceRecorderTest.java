package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class CausynthTraceRecorderTest {
    @Test
    public void richTraceCorrelatesCallsArgumentsReturnsAndBranches() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path output = folder.getRoot().toPath();
        String previousOutput = System.getProperty("causynth.trace.output.dir");
        String previousTest = System.getProperty("causynth.trace.test");
        try {
            resetRecorder();
            System.setProperty("causynth.trace.output.dir", output.toString());
            System.setProperty("causynth.trace.test", "rich-recorder-test");

            Object receiver = new Object();
            Object argument = new Object();
            long parent = CausynthTraceRecorder.enterMethod("<test.Parent: void run()>",
                    receiver);
            long invocation = CausynthTraceRecorder.beginCall(parent,
                    "<test.Parent: void run()>", 7,
                    "<test.Child: java.lang.Object pass(java.lang.Object)>", receiver);
            CausynthTraceRecorder.recordCallArgument(invocation, 0,
                    "java.lang.Object", argument, "");
            long child = CausynthTraceRecorder.enterMethod(
                    "<test.Child: java.lang.Object pass(java.lang.Object)>", receiver);
            CausynthTraceRecorder.recordMethodArgument(child, 0,
                    "java.lang.Object", argument, "");
            CausynthTraceRecorder.exitMethod(child, argument, "");
            CausynthTraceRecorder.endCall(invocation, argument, "");

            long throwingInvocation = CausynthTraceRecorder.beginCall(parent,
                    "<test.Parent: void run()>", 8,
                    "<test.Child: void fail()>", receiver);
            long throwingChild = CausynthTraceRecorder.enterMethod(
                    "<test.Child: void fail()>", receiver);
            CausynthTraceRecorder.throwActiveMethod(
                    new IllegalStateException("expected"));
            CausynthTraceRecorder.recordBranch(parent,
                    "<test.Parent: void run()>", 9, "arg != null", true);
            CausynthTraceRecorder.exitMethod(parent, null, "");

            Method shutdown = CausynthTraceRecorder.class
                    .getDeclaredMethod("shutdown");
            shutdown.setAccessible(true);
            shutdown.invoke(null);

            List<String> lines = Files.readAllLines(
                    output.resolve("runtime_trace.jsonl"), StandardCharsets.UTF_8);
            String trace = String.join("\n", lines);
            assertTrue(trace.contains("\"event\":\"METHOD_ENTER\""));
            assertTrue(trace.contains("\"event\":\"CALL_SITE_ENTER\""));
            assertTrue(trace.contains("\"event\":\"CALL_ARGUMENT\""));
            assertTrue(trace.contains("\"event\":\"METHOD_ARGUMENT\""));
            assertTrue(trace.contains("\"event\":\"CALL_SITE_RETURN\""));
            assertTrue(trace.contains("\"event\":\"CALL_SITE_THROW\""));
            assertTrue(trace.contains("\"event\":\"METHOD_EXIT_THROW\""));
            assertTrue(trace.contains("\"event\":\"METHOD_EXIT_NORMAL\""));
            assertTrue(trace.contains("\"event\":\"BRANCH\""));
            assertTrue(trace.contains("\"parentSiteId\":" + invocation));
            assertTrue(trace.contains("\"parentSiteId\":" + throwingInvocation));
            assertTrue(trace.contains("\"event\":\"METHOD_EXIT_THROW\",\"seq\":"));
            assertTrue(trace.contains("\"callId\":" + throwingChild));
            assertTrue(trace.contains("\"outcome\":true"));
            assertFalse(trace.contains("\"event\":\"CALL_SITE_INCOMPLETE\""));
        } finally {
            resetRecorder();
            if (previousOutput == null) {
                System.clearProperty("causynth.trace.output.dir");
            } else {
                System.setProperty("causynth.trace.output.dir", previousOutput);
            }
            if (previousTest == null) {
                System.clearProperty("causynth.trace.test");
            } else {
                System.setProperty("causynth.trace.test", previousTest);
            }
            folder.delete();
        }
    }

    @Test
    public void concurrentFirstEventsWaitForFullyPublishedWriter() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path output = folder.getRoot().toPath();
        for (int index = 0; index < 24; index++) {
            output = output.resolve("initialization-level-" + index);
        }
        String previousOutput = System.getProperty("causynth.trace.output.dir");
        String previousTest = System.getProperty("causynth.trace.test");
        String previousMaxEvents = System.getProperty("causynth.trace.max.events");
        try {
            resetRecorder();
            System.setProperty("causynth.trace.output.dir", output.toString());
            System.setProperty("causynth.trace.test", "concurrent-init-test");
            System.setProperty("causynth.trace.max.events", "10000");

            int threadCount = 128;
            CountDownLatch ready = new CountDownLatch(threadCount);
            CountDownLatch start = new CountDownLatch(1);
            List<Throwable> failures = Collections.synchronizedList(
                    new ArrayList<Throwable>());
            List<Thread> threads = new ArrayList<>();
            for (int index = 0; index < threadCount; index++) {
                final int threadIndex = index;
                Thread thread = new Thread(new Runnable() {
                    @Override
                    public void run() {
                        ready.countDown();
                        try {
                            start.await();
                            CausynthTraceRecorder.record(
                                    "<test.Concurrent" + threadIndex
                                            + ": void run()>", new Object());
                        } catch (Throwable failure) {
                            failures.add(failure);
                        }
                    }
                }, "recorder-init-" + index);
                threads.add(thread);
                thread.start();
            }
            assertTrue("recording threads did not become ready",
                    ready.await(15, TimeUnit.SECONDS));
            start.countDown();
            for (Thread thread : threads) {
                thread.join(TimeUnit.SECONDS.toMillis(15));
                assertFalse("recording thread remained blocked: "
                        + thread.getName(), thread.isAlive());
            }
            assertTrue("recording thread failed: " + failures,
                    failures.isEmpty());

            shutdownRecorder();
            List<String> lines = Files.readAllLines(
                    output.resolve("runtime_trace.jsonl"),
                    StandardCharsets.UTF_8);
            int methodEntries = 0;
            for (String line : lines) {
                if (line.contains("\"event\":\"METHOD_ENTER\"")) {
                    methodEntries++;
                }
            }
            assertEquals("no first-wave event may observe an unpublished writer",
                    threadCount, methodEntries);
        } finally {
            resetRecorder();
            restoreProperty("causynth.trace.output.dir", previousOutput);
            restoreProperty("causynth.trace.test", previousTest);
            restoreProperty("causynth.trace.max.events", previousMaxEvents);
            folder.delete();
        }
    }

    @Test
    public void failedInitializationIsExplicitAndRetryable() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path root = folder.getRoot().toPath();
        Path notDirectory = root.resolve("not-a-directory");
        Files.write(notDirectory, Collections.singletonList("file"),
                StandardCharsets.UTF_8);
        Path validOutput = root.resolve("valid-output");
        String previousOutput = System.getProperty("causynth.trace.output.dir");
        String previousTest = System.getProperty("causynth.trace.test");
        try {
            resetRecorder();
            System.setProperty("causynth.trace.output.dir",
                    notDirectory.toString());
            System.setProperty("causynth.trace.test", "retry-init-test");

            boolean failedExplicitly = false;
            try {
                CausynthTraceRecorder.record(
                        "<test.Retry: void firstAttempt()>", null);
            } catch (IllegalStateException failure) {
                failedExplicitly = true;
                assertTrue(failure.getMessage().contains(
                        "Failed to initialize Causynth trace recorder"));
            }
            assertTrue("an unusable output path must fail explicitly",
                    failedExplicitly);

            Field initializedField = CausynthTraceRecorder.class
                    .getDeclaredField("INITIALIZED");
            initializedField.setAccessible(true);
            AtomicBoolean initialized = (AtomicBoolean) initializedField.get(null);
            assertFalse("failed initialization must remain retryable",
                    initialized.get());

            System.setProperty("causynth.trace.output.dir",
                    validOutput.toString());
            CausynthTraceRecorder.record(
                    "<test.Retry: void secondAttempt()>", null);
            shutdownRecorder();
            String trace = String.join("\n", Files.readAllLines(
                    validOutput.resolve("runtime_trace.jsonl"),
                    StandardCharsets.UTF_8));
            assertTrue(trace.contains("<test.Retry: void secondAttempt()>"));
            assertFalse(trace.contains("firstAttempt"));
        } finally {
            resetRecorder();
            restoreProperty("causynth.trace.output.dir", previousOutput);
            restoreProperty("causynth.trace.test", previousTest);
            folder.delete();
        }
    }

    @Test
    public void streamingOnlyWritesCompleteRowsWithoutRetainingGraphEvents()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path output = folder.getRoot().toPath();
        String previousOutput = System.getProperty(
                "causynth.trace.output.dir");
        String previousStreaming = System.getProperty(
                "causynth.trace.streaming.only");
        try {
            resetRecorder();
            System.setProperty("causynth.trace.output.dir",
                    output.toString());
            System.setProperty("causynth.trace.streaming.only", "true");

            long call = CausynthTraceRecorder.enterMethod(
                    "<test.Streaming: void run()>", new Object());
            CausynthTraceRecorder.recordBranch(call,
                    "<test.Streaming: void run()>", 1, "x != 0", true);
            CausynthTraceRecorder.exitMethod(call, null, "");
            shutdownRecorder();

            String trace = String.join("\n", Files.readAllLines(
                    output.resolve("runtime_trace.jsonl"),
                    StandardCharsets.UTF_8));
            assertTrue(trace.contains("\"event\":\"METHOD_ENTER\""));
            assertTrue(trace.contains("\"event\":\"BRANCH\""));
            assertTrue(trace.contains("\"event\":\"METHOD_EXIT_NORMAL\""));
            String manifest = new String(Files.readAllBytes(output.resolve(
                    "streaming_trace_manifest.json")),
                    StandardCharsets.UTF_8);
            assertTrue(manifest.contains("\"status\":\"CLOSED\""));
            assertTrue(manifest.contains("\"complete\":true"));
            assertTrue(manifest.contains("\"writeFailure\":false"));
            assertEquals(0, retainedEventCount("EVENTS"));
            assertEquals(0, retainedEventCount("FIELD_EVENTS"));
            assertEquals(0, retainedEventCount("EXECUTION_EVENTS"));
        } finally {
            resetRecorder();
            restoreProperty("causynth.trace.output.dir", previousOutput);
            restoreProperty("causynth.trace.streaming.only",
                    previousStreaming);
            folder.delete();
        }
    }

    @Test
    public void offlineAggregationUsesSequenceOrderForContextsAndLatestWrite()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path output = folder.getRoot().toPath().resolve("offline-order");
        Files.createDirectories(output);
        Path trace = output.resolve("runtime_trace.jsonl");
        Path graph = output.resolve("static_dataflow_edges.jsonl");
        String writer = "<test.Writer: void write()>";
        String reader = "<test.Reader: void read()>";
        String field = "<test.State: int value>";
        List<String> rows = new ArrayList<>();
        // File order deliberately differs from recorder sequence order.
        rows.add(methodRow(10, writer, "writer", 1, 11, 10));
        rows.add(methodRow(2, reader, "reader", 2, 22, 2));
        rows.add(methodRow(1, writer, "writer", 1, 11, 1));
        rows.add(fieldRow(5, "FIELD_WRITE", writer, "writer", 1,
                11, 5, field, 77, "5"));
        rows.add(fieldRow(3, "FIELD_WRITE", writer, "writer", 1,
                11, 3, field, 77, "3"));
        rows.add(fieldRow(6, "FIELD_READ", reader, "reader", 2,
                22, 6, field, 77, "5"));
        Files.write(trace, rows, StandardCharsets.UTF_8);
        Files.write(graph, Collections.singletonList("{"
                        + "\"id\":\"DF.FIELD\","
                        + "\"kind\":\"value_flow\","
                        + "\"fromCell\":\"" + field + "\","
                        + "\"toCell\":\"local:observed\","
                        + "\"method\":\"" + writer + "\","
                        + "\"unitIndex\":1}"),
                StandardCharsets.UTF_8);

        try {
            aggregateExistingTrace(output, graph, 100, 100);
            String instantiated = new String(Files.readAllBytes(output.resolve(
                    "unit_test_instantiated_graph.json")),
                    StandardCharsets.UTF_8);
            assertTrue(instantiated.contains("\"kind\":\"runtime_field_state\""));
            assertTrue(instantiated.contains("@value:5"));
            assertFalse("lower-sequence write that appeared later in the file "
                            + "must not become the latest write",
                    instantiated.contains("@value:3"));
            assertTrue(instantiated.contains("\"firstSeq\":1"));
            assertTrue(instantiated.contains("\"lastSeq\":10"));
        } finally {
            resetRecorder();
            folder.delete();
        }
    }

    @Test
    public void streamedGraphEdgesPreserveInsertionOrderIdsAndCounts()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path output = folder.getRoot().toPath().resolve("streamed-edges");
        Files.createDirectories(output);
        Path trace = output.resolve("runtime_trace.jsonl");
        Path graph = output.resolve("static_dataflow_edges.jsonl");
        String method = "<test.StreamedEdges: void run()>";
        Files.write(trace, Collections.singletonList(
                methodRow(1, method, "worker", 1, 11, 1)),
                StandardCharsets.UTF_8);
        Files.write(graph, java.util.Arrays.asList(
                "{\"id\":\"DF.FIRST\","
                        + "\"kind\":\"first_flow\","
                        + "\"fromCell\":\"local:firstFrom\","
                        + "\"toCell\":\"local:firstTo\","
                        + "\"method\":\"" + method + "\","
                        + "\"unitIndex\":1}",
                "{\"id\":\"DF.SECOND\","
                        + "\"kind\":\"second_flow\","
                        + "\"fromCell\":\"local:secondFrom\","
                        + "\"toCell\":\"local:secondTo\","
                        + "\"method\":\"" + method + "\","
                        + "\"unitIndex\":2}"),
                StandardCharsets.UTF_8);

        try {
            aggregateExistingTrace(output, graph, 100, 100);
            String instantiated = new String(Files.readAllBytes(output.resolve(
                    "unit_test_instantiated_graph.json")),
                    StandardCharsets.UTF_8);
            int first = instantiated.indexOf("\"id\":\"DYN.0\"");
            int second = instantiated.indexOf("\"id\":\"DYN.1\"");
            assertTrue(first >= 0);
            assertTrue(second > first);
            assertTrue(instantiated.indexOf("\"staticEdgeId\":\"DF.FIRST\"",
                    first) < second);
            assertTrue(instantiated.indexOf("\"staticEdgeId\":\"DF.SECOND\"",
                    second) > second);
            assertFalse(instantiated.contains("\"id\":\"DYN.2\""));
            assertTrue(instantiated.contains("\"instantiatedEdgeCount\":2"));

            String roleMerged = new String(Files.readAllBytes(output.resolve(
                    "unit_test_role_merged_graph.json")),
                    StandardCharsets.UTF_8);
            int roleFirst = roleMerged.indexOf("\"id\":\"ROLE.0\"");
            int roleSecond = roleMerged.indexOf("\"id\":\"ROLE.1\"");
            assertTrue(roleFirst >= 0);
            assertTrue(roleSecond > roleFirst);
            assertFalse(roleMerged.contains("\"id\":\"ROLE.2\""));
            assertTrue(roleMerged.contains("\"roleMergedEdgeCount\":2"));
        } finally {
            resetRecorder();
            folder.delete();
        }
    }

    @Test
    public void contextPairLimitIsReportedAsGraphTruncation()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path output = folder.getRoot().toPath().resolve("context-cap");
        Files.createDirectories(output);
        Path trace = output.resolve("runtime_trace.jsonl");
        Path graph = output.resolve("static_dataflow_edges.jsonl");
        String method = "<test.Contexts: void run()>";
        Files.write(trace, java.util.Arrays.asList(
                methodRow(1, method, "thread-1", 1, 11, 1),
                methodRow(2, method, "thread-2", 2, 22, 2)),
                StandardCharsets.UTF_8);
        Files.write(graph, Collections.singletonList("{"
                        + "\"id\":\"DF.CAP\","
                        + "\"kind\":\"value_flow\","
                        + "\"fromCell\":\"local:a\","
                        + "\"toCell\":\"local:b\","
                        + "\"method\":\"" + method + "\","
                        + "\"unitIndex\":1}"),
                StandardCharsets.UTF_8);

        try {
            aggregateExistingTrace(output, graph, 100, 1);
            String summary = new String(Files.readAllBytes(output.resolve(
                    "summary.json")), StandardCharsets.UTF_8);
            assertTrue(summary.contains("\"contextPairTruncated\":true"));
            assertTrue(summary.contains("\"skippedContextPairInstances\":1"));
            assertTrue(summary.contains("\"truncated\":true"));
            assertTrue(summary.contains("\"roleTruncated\":true"));
        } finally {
            resetRecorder();
            folder.delete();
        }
    }

    @Test
    public void fingerprintFailureIsIncompleteEvidenceNotProgramFailure()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path output = folder.getRoot().toPath();
        String previousOutput = System.getProperty(
                "causynth.trace.output.dir");
        try {
            resetRecorder();
            System.setProperty("causynth.trace.output.dir", output.toString());
            long call = CausynthTraceRecorder.enterMethod(
                    "<test.Fingerprint: void run()>", new Object());
            CausynthTraceRecorder.recordMethodArgument(call, 0,
                    "java.util.Map", new ExplodingMap(), "");
            CausynthTraceRecorder.exitMethod(call, null, "");
            shutdownRecorder();

            String trace = new String(Files.readAllBytes(output.resolve(
                    "runtime_trace.jsonl")), StandardCharsets.UTF_8);
            assertTrue(trace.contains("\"valueFingerprintComplete\":false"));
            assertTrue(trace.contains("CAPTURE_FAILURE:java.util.ConcurrentModificationException"));
        } finally {
            resetRecorder();
            restoreProperty("causynth.trace.output.dir", previousOutput);
            folder.delete();
        }
    }

    @Test
    public void boundedFingerprintPreservesMapArrayElementAndNestedFields()
            throws Exception {
        Map<Integer, KeySnapshot[]> left = new LinkedHashMap<>();
        left.put(17, new KeySnapshot[]{
                new KeySnapshot(17, 1000L, 1001L, new byte[]{1, 2, 3})});
        left.put(9, new KeySnapshot[]{
                new KeySnapshot(9, 800L, 801L, new byte[]{4, 5})});

        // Reverse insertion order and use fresh instances: canonical map
        // ordering must retain structural equality, not iteration order or
        // host object identity.
        Map<Integer, KeySnapshot[]> right = new LinkedHashMap<>();
        right.put(9, new KeySnapshot[]{
                new KeySnapshot(9, 800L, 801L, new byte[]{4, 5})});
        right.put(17, new KeySnapshot[]{
                new KeySnapshot(17, 1000L, 1001L, new byte[]{1, 2, 3})});

        FingerprintView leftView = captureFingerprint(left);
        FingerprintView rightView = captureFingerprint(right);
        assertTrue(leftView.complete);
        assertTrue(rightView.complete);
        assertEquals(leftView.digest, rightView.digest);
        assertTrue(leftView.nodes <= 256);

        Map<Integer, KeySnapshot[]> changedExpiry = new LinkedHashMap<>();
        changedExpiry.put(17, new KeySnapshot[]{
                new KeySnapshot(17, 1000L, 1002L, new byte[]{1, 2, 3})});
        changedExpiry.put(9, new KeySnapshot[]{
                new KeySnapshot(9, 800L, 801L, new byte[]{4, 5})});
        assertFalse(leftView.digest.equals(
                captureFingerprint(changedExpiry).digest));
    }

    @Test
    public void mapEntryFingerprintIsCycleSafe() throws Exception {
        Map<Object, Object> self = new LinkedHashMap<>();
        self.put("self", self);
        FingerprintView view = captureFingerprint(self);
        assertTrue(view.complete);
        assertEquals("COMPLETE", view.reason);
        assertTrue(view.nodes <= 3);
    }

    @Test(timeout = 2000L)
    public void managerLikeContainerGraphStopsAtStrictBudget()
            throws Exception {
        ManagerLike manager = new ManagerLike();
        for (int index = 0; index < 5000; index++) {
            manager.keys.put(index, new KeySnapshot(index,
                    100000L + index, 200000L + index,
                    new byte[]{1, 2, 3, 4}));
        }
        Map<String, ManagerLike> pools = new LinkedHashMap<>();
        pools.put("bp-1", manager);

        FingerprintView view = captureFingerprint(pools);
        assertFalse(view.complete);
        assertTrue(view.reason.startsWith("MAX_"));
        assertTrue(view.nodes <= 256);
    }

    @Test
    public void canonicalFingerprintHasStrictUtf8ByteBudget()
            throws Exception {
        StringBuilder huge = new StringBuilder();
        for (int index = 0; index < 100000; index++) {
            huge.append('\u4e2d');
        }
        FingerprintView view = captureFingerprint(huge.toString());
        assertFalse(view.complete);
        assertEquals("MAX_CANONICAL_BYTES", view.reason);
        assertEquals(1, view.nodes);
    }

    @Test
    public void plainConcolicReplayKeepsExactCallContextWithoutTraceHashing()
            throws Exception {
        String previousResults = System.getProperty(
                "causynth.concolic.results");
        String previousOutput = System.getProperty(
                "causynth.trace.output.dir");
        String previousFingerprints = System.getProperty(
                "causynth.trace.value.fingerprints");
        String previousMaxEvents = System.getProperty(
                "causynth.trace.max.events");
        String caller = "<test.Parent: void run()>";
        String callee = "<test.Child: void read()>";
        try {
            resetRecorder();
            System.setProperty("causynth.concolic.results",
                    "target/context-only-concolic.jsonl");
            System.clearProperty("causynth.trace.output.dir");
            System.clearProperty("causynth.trace.value.fingerprints");
            // Context-only mode must not inherit the diagnostic event cap:
            // the selected activation may occur after an arbitrary number of
            // unrelated rich-trace hooks.
            System.setProperty("causynth.trace.max.events", "1");

            Object receiver = new Object();
            long parent = CausynthTraceRecorder.enterMethod(caller, receiver);
            long invocation = CausynthTraceRecorder.beginCall(parent, caller,
                    7, callee, receiver);
            long child = CausynthTraceRecorder.enterMethod(callee, receiver);
            CausynthTraceRecorder.recordMethodArgument(child, 0,
                    "java.util.Map", new ExplodingMap(), "");

            assertTrue(CausynthTraceRecorder.currentCallParentSiteMatches(
                    caller, 7, caller + "#u7", callee));
            assertTrue(staticBoolean("contextOnlyConcolicReplay"));
            assertFalse(staticBoolean("valueFingerprintsEnabled"));
            assertEquals(Integer.MAX_VALUE, staticInt("maxEvents"));
            assertEquals(null, staticObject("traceWriter"));
            assertEquals(null, staticObject("outputDir"));

            CausynthTraceRecorder.exitMethod(child, null, "");
            CausynthTraceRecorder.endCall(invocation, null, "");
            CausynthTraceRecorder.exitMethod(parent, null, "");
            assertFalse(CausynthTraceRecorder.currentCallParentSiteMatches(
                    caller, 7, caller + "#u7", callee));
        } finally {
            resetRecorder();
            restoreProperty("causynth.concolic.results", previousResults);
            restoreProperty("causynth.trace.output.dir", previousOutput);
            restoreProperty("causynth.trace.value.fingerprints",
                    previousFingerprints);
            restoreProperty("causynth.trace.max.events", previousMaxEvents);
        }
    }

    private static void aggregateExistingTrace(Path output, Path graph,
                                               int maxEdges,
                                               int maxContextPairs)
            throws Exception {
        String previousGraph = System.getProperty("causynth.static.graph");
        String previousRegions = System.getProperty(
                "causynth.symbolic.regions");
        String previousRegionEdges = System.getProperty(
                "causynth.symbolic.region.edges");
        try {
            System.setProperty("causynth.symbolic.regions",
                    output.resolve("symbolic_regions.jsonl").toString());
            System.setProperty("causynth.symbolic.region.edges",
                    output.resolve("symbolic_region_edges.jsonl").toString());
            Method aggregate = CausynthTraceRecorder.class.getDeclaredMethod(
                    "aggregateExistingTrace", java.io.File.class,
                    java.io.File.class, String.class, int.class, int.class);
            aggregate.setAccessible(true);
            aggregate.invoke(null, output.toFile(), graph.toFile(), "test",
                    maxEdges, maxContextPairs);
        } finally {
            restoreProperty("causynth.static.graph", previousGraph);
            restoreProperty("causynth.symbolic.regions", previousRegions);
            restoreProperty("causynth.symbolic.region.edges",
                    previousRegionEdges);
        }
    }

    private static String methodRow(long seq, String method, String thread,
                                    long tid, int objectId, long callId) {
        return "{\"event\":\"METHOD_ENTER\",\"seq\":" + seq
                + ",\"test\":\"test\",\"process\":\"process\","
                + "\"threadName\":\"" + thread + "\",\"tid\":" + tid
                + ",\"method\":\"" + method + "\",\"objectId\":"
                + objectId + ",\"callId\":" + callId
                + ",\"parentCallId\":0,\"parentSiteId\":0,"
                + "\"siteId\":\"" + method + "#entry\","
                + "\"receiverType\":\"test.State\",\"timeNanos\":"
                + (seq * 10) + "}";
    }

    private static String fieldRow(long seq, String kind, String method,
                                   String thread, long tid, int objectId,
                                   long callId, String field, int receiverId,
                                   String primitive) {
        return "{\"event\":\"" + kind + "\",\"seq\":" + seq
                + ",\"test\":\"test\",\"process\":\"process\","
                + "\"threadName\":\"" + thread + "\",\"tid\":" + tid
                + ",\"method\":\"" + method + "\",\"objectId\":"
                + objectId + ",\"callId\":" + callId
                + ",\"siteId\":\"" + method + "#u1\","
                + "\"unitIndex\":1,\"field\":\"" + field + "\","
                + "\"fieldReceiverObjectId\":" + receiverId + ","
                + "\"valueObjectId\":0,\"primitiveValue\":\""
                + primitive + "\",\"timeNanos\":" + (seq * 10) + "}";
    }

    private static final class ExplodingMap
            extends AbstractMap<Object, Object> {
        @Override
        public Set<Map.Entry<Object, Object>> entrySet() {
            throw new ConcurrentModificationException("simulated race");
        }
    }

    private static final class KeySnapshot {
        private final int keyId;
        private final long expiry;
        private final Epoch epoch;
        private final byte[] encoded;

        private KeySnapshot(int keyId, long expiry, long observedExpiry,
                            byte[] encoded) {
            this.keyId = keyId;
            this.expiry = expiry;
            this.epoch = new Epoch(observedExpiry);
            this.encoded = encoded;
        }
    }

    private static final class Epoch {
        private final long observedExpiry;

        private Epoch(long observedExpiry) {
            this.observedExpiry = observedExpiry;
        }
    }

    private static final class ManagerLike {
        private final Map<Integer, KeySnapshot> keys =
                new LinkedHashMap<>();
    }

    private static final class FingerprintView {
        private final String digest;
        private final boolean complete;
        private final int nodes;
        private final String reason;

        private FingerprintView(String digest, boolean complete, int nodes,
                                String reason) {
            this.digest = digest;
            this.complete = complete;
            this.nodes = nodes;
            this.reason = reason;
        }
    }

    private static FingerprintView captureFingerprint(Object value)
            throws Exception {
        Class<?> type = Class.forName(CausynthTraceRecorder.class.getName()
                + "$ValueFingerprint");
        Method capture = type.getDeclaredMethod("capture", Object.class,
                String.class);
        capture.setAccessible(true);
        Object result = capture.invoke(null, value, "");
        Field digest = type.getDeclaredField("digest");
        Field complete = type.getDeclaredField("complete");
        Field nodes = type.getDeclaredField("nodes");
        Field reason = type.getDeclaredField("reason");
        digest.setAccessible(true);
        complete.setAccessible(true);
        nodes.setAccessible(true);
        reason.setAccessible(true);
        return new FingerprintView((String) digest.get(result),
                complete.getBoolean(result), nodes.getInt(result),
                (String) reason.get(result));
    }

    private static int retainedEventCount(String fieldName) throws Exception {
        Field field = CausynthTraceRecorder.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        return ((List<?>) field.get(null)).size();
    }

    private static Object staticObject(String fieldName) throws Exception {
        Field field = CausynthTraceRecorder.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        return field.get(null);
    }

    private static boolean staticBoolean(String fieldName) throws Exception {
        return (Boolean) staticObject(fieldName);
    }

    private static int staticInt(String fieldName) throws Exception {
        return (Integer) staticObject(fieldName);
    }

    private static void resetRecorder() throws Exception {
        shutdownRecorder();
        Method clear = CausynthTraceRecorder.class
                .getDeclaredMethod("clearInMemoryTrace");
        clear.setAccessible(true);
        clear.invoke(null);
    }

    private static void shutdownRecorder() throws Exception {
        Method shutdown = CausynthTraceRecorder.class
                .getDeclaredMethod("shutdown");
        shutdown.setAccessible(true);
        shutdown.invoke(null);
    }

    private static void restoreProperty(String name, String value) {
        if (value == null) {
            System.clearProperty(name);
        } else {
            System.setProperty(name, value);
        }
    }
}
