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
            String manifest = new String(Files.readAllBytes(output.resolve(
                    "streaming_trace_manifest.json")),
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
