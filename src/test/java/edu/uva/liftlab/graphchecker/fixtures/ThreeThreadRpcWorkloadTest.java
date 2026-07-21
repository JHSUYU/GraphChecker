package edu.uva.liftlab.graphchecker.fixtures;

import org.junit.Test;

import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class ThreeThreadRpcWorkloadTest {
    private static final Path FIXTURE = Paths.get("experiments", "generic",
            "three-thread-rpc");

    @Test
    public void executesEveryBooleanInputWithThreeRealWorkerThreads()
            throws Exception {
        int reachingExecutions = 0;
        for (Boolean b1 : new Boolean[]{Boolean.FALSE, Boolean.TRUE}) {
            for (Boolean b2 : new Boolean[]{Boolean.FALSE, Boolean.TRUE}) {
                ThreeThreadRpcWorkload.RunResult result =
                        ThreeThreadRpcWorkload.execute(b1, b2);

                assertEquals(b1, result.getB1());
                assertEquals(b2, result.getB2());
                int expectedA = (b1.booleanValue() ? 1 : -1)
                        + ThreeThreadRpcWorkload.t - 9;
                assertEquals(expectedA, result.getA());
                assertEquals(b2.booleanValue() ? 0 : 10, result.getB());
                assertEquals(result.getA() > result.getB(),
                        result.isBugReached());
                assertTrue("producer worker frames did not overlap",
                        result.isProducerConcurrencyObserved());
                assertTrue("consumer started before both producer threads "
                                + "terminated",
                        result.isConsumerStartedAfterProducerThreadsTerminated());
                Set<Long> workers = new HashSet<>();
                for (long threadId : result.getWorkerThreadIds()) {
                    assertTrue(threadId > 0L);
                    workers.add(threadId);
                }
                assertEquals(3, workers.size());
                assertRpcObservations(result.getRpcObservations(),
                        result.getWorkerThreadIds(), workers);

                if (result.isBugReached()) {
                    reachingExecutions++;
                    assertEquals(ThreeThreadRpcWorkload.CONSUMER_THREAD,
                            result.getFailureThread());
                    assertTrue(result.getFailure()
                            instanceof ThreeThreadRpcWorkload.BugReachedException);
                } else {
                    assertNull(result.getFailure());
                }
            }
        }
        // This is a workload sanity gate, not a handwritten reachability
        // formula. The composer/verifier must derive the actual condition.
        assertTrue(reachingExecutions > 0);
        assertTrue(reachingExecutions < 4);
    }

    @Test
    public void localChannelsRequireNoDeclaredRpcTopology() throws Exception {
        Path workflow = FIXTURE.resolve("workflow.properties");
        assertTrue(Files.isRegularFile(workflow));
        String configuration = new String(Files.readAllBytes(workflow),
                StandardCharsets.UTF_8);
        assertFalse(configuration.contains("rpc_mapping_file"));
        assertFalse(Files.exists(FIXTURE.resolve("rpc-topology.jsonl")));
        assertNotNull(ThreeThreadRpcWorkload.RpcBus.class
                .getDeclaredField("a"));
        assertNotNull(ThreeThreadRpcWorkload.RpcBus.class
                .getDeclaredField("b"));
    }

    @Test
    public void producerSupportMethodsAndConsumerTargetAreDisjoint()
            throws Exception {
        Method producerA = ThreeThreadRpcWorkload.ProducerA.class
                .getDeclaredMethod("compute", Boolean.class);
        Method producerB = ThreeThreadRpcWorkload.ProducerB.class
                .getDeclaredMethod("compute", Boolean.class);
        Class<?> targetOwner = Class.forName(ThreeThreadRpcWorkload.class
                .getName() + "$ConsumerThread");
        Method target = targetOwner.getDeclaredMethod("executeWorker");

        assertFalse(producerA.equals(producerB));
        assertFalse(producerA.getDeclaringClass().equals(
                target.getDeclaringClass()));
        assertFalse(producerB.getDeclaringClass().equals(
                target.getDeclaringClass()));
        int directedTargetMethods = 0;
        for (Method method : targetOwner.getDeclaredMethods()) {
            if ("executeWorker".equals(method.getName())) {
                directedTargetMethods++;
            }
        }
        assertEquals("fixture must expose one engine target method", 1,
                directedTargetMethods);
    }

    private static void assertRpcObservations(
            List<ThreeThreadRpcWorkload.RpcObservation> observations,
            long[] workerIds,
            Set<Long> workers) {
        assertEquals(2, observations.size());
        Set<String> channels = new HashSet<>();
        for (ThreeThreadRpcWorkload.RpcObservation observation
                : observations) {
            channels.add(observation.getChannel());
            assertEquals(observation.getPublishedValue(),
                    observation.getReceivedValue());
            assertTrue(observation.isRuntimeValueEqualityObserved());
            assertTrue(workers.contains(observation.getPublisherThreadId()));
            assertTrue(workers.contains(observation.getConsumerThreadId()));
            assertEquals("RPC must be received by the real consumer thread",
                    workerIds[2], observation.getConsumerThreadId());
            if ("A".equals(observation.getChannel())) {
                assertEquals(workerIds[0],
                        observation.getPublisherThreadId());
            } else if ("B".equals(observation.getChannel())) {
                assertEquals(workerIds[1],
                        observation.getPublisherThreadId());
            }
            assertFalse(observation.getPublisherThreadId()
                    == observation.getConsumerThreadId());
            assertTrue(observation.getValueFingerprint()
                    .matches("sha256:[0-9a-f]{64}"));
        }
        assertTrue(channels.contains("A"));
        assertTrue(channels.contains("B"));
    }

}
