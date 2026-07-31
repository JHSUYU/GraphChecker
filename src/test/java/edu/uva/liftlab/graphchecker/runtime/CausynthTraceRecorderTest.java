package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.zip.GZIPOutputStream;

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
            Path manifestPath = output.resolve(
                    "streaming_trace_manifest.json");
            Files.write(manifestPath, "{\"status\":\"CLOSED\"}".getBytes(
                    StandardCharsets.UTF_8));

            Object receiver = new Object();
            Object argument = new Object();
            long parent = CausynthTraceRecorder.enterMethod("<test.Parent: void run()>",
                    receiver);
            assertFalse(Files.exists(manifestPath));
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
            String manifest = new String(Files.readAllBytes(manifestPath),
                    StandardCharsets.UTF_8);
            assertTrue(manifest.contains("\"status\":\"CLOSED\""));
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
            assertTrue(lines.stream().allMatch(line ->
                    line.contains("\"schemaVersion\":2")));
            assertFalse(trace.contains("\"timeNanos\""));
            assertFalse(trace.contains("\"hasOutcome\""));
            assertFalse(trace.contains("\"hasSuccessorIndex\""));
            assertFalse(trace.contains("\"declaredType\""));
            assertFalse(trace.contains("\"expression\""));
            assertFalse(trace.contains("\"exceptionType\""));
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
    public void liteTraceKeepsActivationTreeAndExactFieldOnly() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path output = folder.getRoot().toPath();
        String previousOutput = System.getProperty("causynth.trace.output.dir");
        String previousTest = System.getProperty("causynth.trace.test");
        try {
            resetRecorder();
            System.setProperty("causynth.trace.output.dir", output.toString());
            System.setProperty("causynth.trace.test", "lite-recorder-test");

            String parentMethod = "<test.Parent: void run()>";
            String childMethod = "<test.Child: void read()>";
            String throwingMethod = "<test.Child: void fail()>";
            String field = "<test.State: java.util.Map keys>";
            Object fieldOwner = new Object();
            Object fieldValue = new Object();
            long parent = CausynthTraceRecorder.enterMethodLite(
                    parentMethod, new Object());
            long child = CausynthTraceRecorder.enterMethodLite(
                    childMethod, new Object());
            CausynthTraceRecorder.recordFieldReadLite(
                    field, fieldOwner, fieldValue);
            CausynthTraceRecorder.recordFieldWriteLite(
                    field, fieldOwner, fieldValue);
            CausynthTraceRecorder.exitActiveMethodLite();
            CausynthTraceRecorder.recordFieldReadLite(field);
            long returned = CausynthTraceRecorder.beginCall(
                    parent, parentMethod, 6,
                    "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>",
                    fieldOwner);
            CausynthTraceRecorder.endCallLite(returned);
            long throwing = CausynthTraceRecorder.enterMethodLite(
                    throwingMethod, new Object());
            long invocation = CausynthTraceRecorder.beginCall(
                    throwing, throwingMethod, 7,
                    "<java.util.Map: java.lang.Object get(java.lang.Object)>",
                    fieldOwner);
            CausynthTraceRecorder.throwActiveMethodLite(
                    new IllegalStateException("expected"));
            CausynthTraceRecorder.recordFieldReadLite(field);
            shutdownRecorder();

            List<String> lines = Files.readAllLines(
                    output.resolve("runtime_trace.jsonl"),
                    StandardCharsets.UTF_8);
            List<String> entries = new ArrayList<>();
            List<String> reads = new ArrayList<>();
            List<String> writes = new ArrayList<>();
            for (String line : lines) {
                if (line.contains("\"event\":\"METHOD_ENTER\"")) {
                    entries.add(line);
                } else if (line.contains("\"event\":\"FIELD_READ\"")) {
                    reads.add(line);
                } else if (line.contains("\"event\":\"FIELD_WRITE\"")) {
                    writes.add(line);
                }
            }
            assertEquals(3, entries.size());
            assertEquals(3, reads.size());
            assertEquals(1, writes.size());
            assertTrue(entries.stream().anyMatch(line ->
                    line.contains("\"method\":\"" + childMethod + "\"")
                            && line.contains("\"parentCallId\":" + parent)));
            assertTrue(reads.get(0).contains("\"callId\":" + child));
            assertTrue(reads.get(0).contains(
                    "\"fieldReceiverObjectId\":"
                            + System.identityHashCode(fieldOwner)));
            assertTrue(reads.get(0).contains(
                    "\"valueObjectId\":"
                            + System.identityHashCode(fieldValue)));
            assertTrue(reads.get(1).contains("\"callId\":" + parent));
            assertTrue(reads.get(2).contains("\"callId\":" + parent));
            assertTrue(writes.get(0).contains("\"callId\":" + child));
            assertTrue(writes.get(0).contains(
                    "\"fieldReceiverObjectId\":"
                            + System.identityHashCode(fieldOwner)));
            assertTrue(writes.get(0).contains(
                    "\"valueObjectId\":"
                            + System.identityHashCode(fieldValue)));
            List<String> fields = new ArrayList<>(reads);
            fields.addAll(writes);
            for (String fieldEvent : fields) {
                assertTrue(fieldEvent.contains(
                        "\"field\":\"" + field + "\""));
                assertFalse(fieldEvent.contains("valueFingerprint"));
                assertFalse(fieldEvent.contains("primitiveValue"));
                assertFalse(fieldEvent.contains("siteId"));
                assertFalse(fieldEvent.contains("unitIndex"));
                assertFalse(fieldEvent.contains("\"method\""));
            }
            String trace = String.join("\n", lines);
            assertFalse(trace.contains("\"event\":\"METHOD_EXIT_"));
            assertTrue(trace.contains(
                    "\"event\":\"CALL_SITE_ENTER\""));
            assertTrue(trace.contains(
                    "\"event\":\"CALL_SITE_THROW\""));
            assertTrue(trace.contains(
                    "\"invocationId\":" + invocation));
            assertTrue(trace.contains(
                    "\"objectId\":"
                            + System.identityHashCode(fieldOwner)));
            String liteReturn = lines.stream().filter(line ->
                    line.contains("\"event\":\"CALL_SITE_RETURN\"")
                            && line.contains(
                            "\"invocationId\":" + returned))
                    .findFirst().orElse("");
            assertFalse(liteReturn.isEmpty());
            assertFalse(liteReturn.contains("valueFingerprint"));
            assertFalse(liteReturn.contains("runtimeType"));
            assertFalse(liteReturn.contains("objectId"));
        } finally {
            resetRecorder();
            restoreProperty("causynth.trace.output.dir", previousOutput);
            restoreProperty("causynth.trace.test", previousTest);
            folder.delete();
        }
    }

    @Test
    public void skeletonCliWritesOnlySkeletonAndRuntimeGraph() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path trace = root.resolve("trace");
            Path output = root.resolve("output");
            Files.createDirectories(trace);
            Files.write(trace.resolve("streaming_trace_manifest.json"),
                    ("{\"schemaVersion\":1,"
                            + "\"kind\":\"STREAMING_RUNTIME_TRACE\","
                            + "\"status\":\"CLOSED\"}").getBytes(
                            StandardCharsets.UTF_8));
            String method = "<test.Root: void run()>";
            Files.write(trace.resolve("runtime_trace.jsonl"), (
                    "{\"schemaVersion\":2,\"event\":\"METHOD_ENTER\","
                            + "\"seq\":1,\"process\":\"test\","
                            + "\"threadName\":\"main\",\"tid\":1,"
                            + "\"method\":\"" + method + "\","
                            + "\"receiverType\":\"test.Root\","
                            + "\"callId\":1,\"parentCallId\":0}\n"
                            + "{\"schemaVersion\":2,"
                            + "\"event\":\"FIELD_READ\",\"seq\":2,"
                            + "\"callId\":1,"
                            + "\"field\":\"<test.Root: int ignored>\"}\n")
                    .getBytes(StandardCharsets.UTF_8));
            Path candidates = root.resolve("candidate_skeletons.jsonl.gz");
            writeGzip(candidates, ("{\"schemaVersion\":2,"
                            + "\"kind\":\"REGION_SKELETON\","
                            + "\"regionId\":\"REGION.0\","
                            + "\"rootMethod\":\"" + method + "\","
                            + "\"anchorMethod\":\"" + method + "\","
                            + "\"methods\":[\"" + method + "\"],"
                            + "\"planningMode\":"
                            + "\"REGION_SKELETON_ONLY\"}\n"));

            CausynthTraceRecorder.main(new String[]{
                    "--trace-dir", trace.toString(),
                    "--region-skeletons", candidates.toString(),
                    "--test", "skeleton-cli-test",
                    "--output-dir", output.toString(),
                    "--region-skeleton-only"});

            Path skeletons = output.resolve("region_skeletons.jsonl");
            Path runtimeGraph = output.resolve("runtime_region_graph.jsonl");
            assertTrue(Files.isRegularFile(skeletons));
            assertTrue(Files.isRegularFile(runtimeGraph));
            String staticOutput = new String(Files.readAllBytes(skeletons),
                    StandardCharsets.UTF_8);
            String runtimeOutput = new String(Files.readAllBytes(runtimeGraph),
                    StandardCharsets.UTF_8);
            assertTrue(staticOutput.contains("\"kind\":\"REGION_SKELETON\""));
            assertFalse(staticOutput.contains("symbolicInputs"));
            assertTrue(runtimeOutput.contains(
                    "\"kind\":\"RUNTIME_REGION_GRAPH_METADATA\""));
            assertTrue(runtimeOutput.contains(
                    "\"kind\":\"RUNTIME_PHYSICAL_REGION_ACTIVATION\""));
            assertFalse(runtimeOutput.contains("regionInputs"));
            assertFalse(Files.exists(output.resolve(
                    "concolic_region_plan.jsonl")));
            assertFalse(Files.exists(output.resolve(
                    "runtime_region_instances.jsonl")));
            assertFalse(Files.exists(output.resolve(
                    "runtime_region_inventory_manifest.json")));
            assertFalse(Files.exists(output.resolve(
                    "runtime_region_edge_validation.jsonl")));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void skeletonAggregateRejectsEmptyCandidatesAndActivations()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path trace = root.resolve("trace");
            Files.createDirectories(trace);
            Files.write(trace.resolve("streaming_trace_manifest.json"),
                    ("{\"schemaVersion\":1,"
                            + "\"kind\":\"STREAMING_RUNTIME_TRACE\","
                            + "\"status\":\"CLOSED\"}").getBytes(
                            StandardCharsets.UTF_8));
            String anchor = "<test.Anchor: void step()>";
            Files.write(trace.resolve("runtime_trace.jsonl"),
                    ("{\"schemaVersion\":2,"
                            + "\"event\":\"METHOD_ENTER\",\"seq\":1,"
                            + "\"process\":\"test\","
                            + "\"threadName\":\"main\",\"tid\":1,"
                            + "\"method\":\"" + anchor + "\","
                            + "\"callId\":1,\"parentCallId\":0}\n")
                            .getBytes(StandardCharsets.UTF_8));

            Path empty = root.resolve("empty.jsonl.gz");
            writeGzip(empty, "");
            IOException noCandidates = skeletonAggregationFailure(
                    trace, empty, root.resolve("no-candidates"));
            assertTrue(noCandidates.getMessage().contains(
                    "no static regions"));

            String firstRoot = "<test.First: void run()>";
            String secondRoot = "<test.Second: void run()>";
            Path ambiguous = root.resolve("ambiguous.jsonl.gz");
            writeGzip(ambiguous,
                    skeletonCandidate("REGION.FIRST", firstRoot, anchor)
                            + skeletonCandidate("REGION.SECOND", secondRoot,
                            anchor));
            IOException noActivations = skeletonAggregationFailure(
                    trace, ambiguous, root.resolve("no-activations"));
            assertTrue(noActivations.getMessage().contains(
                    "no runtime activations"));
            assertFalse(Files.exists(root.resolve("no-candidates")
                    .resolve("runtime_region_graph.jsonl")));
            assertFalse(Files.exists(root.resolve("no-activations")
                    .resolve("runtime_region_graph.jsonl")));
        } finally {
            folder.delete();
        }
    }

    private static IOException skeletonAggregationFailure(
            Path trace, Path candidates, Path output) throws Exception {
        Method aggregate = CausynthTraceRecorder.class.getDeclaredMethod(
                "aggregateSkeletonTrace", java.io.File.class,
                java.io.File.class, java.io.File.class, String.class,
                java.io.File.class);
        aggregate.setAccessible(true);
        try {
            aggregate.invoke(null, trace.toFile(), null,
                    candidates.toFile(), "skeleton-fail-closed-test",
                    output.toFile());
        } catch (InvocationTargetException failure) {
            assertTrue(failure.getCause() instanceof IOException);
            return (IOException) failure.getCause();
        }
        throw new AssertionError("skeleton aggregation unexpectedly passed");
    }

    private static String skeletonCandidate(
            String id, String root, String anchor) {
        return "{\"schemaVersion\":2,"
                + "\"kind\":\"REGION_SKELETON\","
                + "\"regionId\":\"" + id + "\","
                + "\"rootMethod\":\"" + root + "\","
                + "\"anchorMethod\":\"" + anchor + "\","
                + "\"methods\":[\"" + root + "\",\"" + anchor
                + "\"],\"planningMode\":\"REGION_SKELETON_ONLY\"}\n";
    }

    private static void writeGzip(Path output, String value)
            throws Exception {
        try (GZIPOutputStream stream = new GZIPOutputStream(
                Files.newOutputStream(output))) {
            stream.write(value.getBytes(StandardCharsets.UTF_8));
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
        try {
            resetRecorder();
            System.setProperty("causynth.trace.output.dir", output.toString());
            System.setProperty("causynth.trace.test", "concurrent-init-test");

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
                            CausynthTraceRecorder.enterMethod(
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
            folder.delete();
        }
    }

    private static void aggregateExistingTrace(Path output, Path graph)
            throws Exception {
        Method aggregate = CausynthTraceRecorder.class.getDeclaredMethod(
                "aggregateExistingTrace", java.io.File.class,
                java.io.File.class, java.io.File.class,
                java.io.File.class, String.class);
        aggregate.setAccessible(true);
        aggregate.invoke(null, output.toFile(), graph.toFile(),
                output.resolve("symbolic_regions.jsonl").toFile(),
                output.resolve("symbolic_region_edges.jsonl").toFile(),
                "test");
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

    private static List<Long> retainedEventSequences(String fieldName)
            throws Exception {
        Field field = CausynthTraceRecorder.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        List<Long> result = new ArrayList<>();
        for (Object event : (List<?>) field.get(null)) {
            Field id = event.getClass().getDeclaredField("id");
            id.setAccessible(true);
            result.add(id.getLong(event));
        }
        return result;
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
