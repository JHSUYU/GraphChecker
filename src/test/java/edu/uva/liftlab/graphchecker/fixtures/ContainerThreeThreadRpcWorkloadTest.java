package edu.uva.liftlab.graphchecker.fixtures;

import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class ContainerThreeThreadRpcWorkloadTest {
    private static final Path SOURCE = Paths.get("src", "test", "java",
            "edu", "uva", "liftlab", "graphchecker", "fixtures",
            "ContainerThreeThreadRpcWorkload.java");

    @Test
    public void nestedArrayAndMapLeavesDriveEveryConcreteExecution()
            throws Exception {
        String source = new String(Files.readAllBytes(SOURCE),
                StandardCharsets.UTF_8);
        assertTrue(source.contains("payloads[1]"));
        assertTrue(source.contains("new StateNode(Boolean.valueOf(!enabled"));
        assertTrue(source.contains("payload.state.guard.enabled"));
        assertTrue(source.contains("value.state.guard.enabled"));
        assertTrue(source.contains("values.entrySet().iterator()"));
        assertFalse(source.matches("(?s).*\\bwhile\\s*\\(.*"));

        int reachingExecutions = 0;
        for (Boolean arrayInput : new Boolean[]{Boolean.FALSE,
                Boolean.TRUE}) {
            for (Boolean mapInput : new Boolean[]{Boolean.FALSE,
                    Boolean.TRUE}) {
                ContainerThreeThreadRpcWorkload.RunResult result =
                        ContainerThreeThreadRpcWorkload.execute(arrayInput,
                                mapInput);
                assertEquals(arrayInput, result.getArrayInput());
                assertEquals(mapInput, result.getMapInput());
                assertEquals(arrayInput.booleanValue() ? 1 : -1,
                        result.getArrayValue());
                assertEquals(mapInput.booleanValue() ? 20 : 10,
                        result.getMapValue());
                assertEquals(result.getArrayValue() > result.getMapValue(),
                        result.isBugReached());
                assertTrue(result.isProducerConcurrencyObserved());
                assertTrue(result
                        .isConsumerStartedAfterProducersTerminated());
                assertWorkerAndChannelIdentity(result);
                if (result.isBugReached()) {
                    reachingExecutions++;
                    assertEquals(ContainerThreeThreadRpcWorkload
                                    .CONSUMER_THREAD,
                            result.getFailureThread());
                    assertTrue(result.getFailure() instanceof
                            ContainerThreeThreadRpcWorkload
                                    .ContainerBugReachedException);
                } else {
                    assertNull(result.getFailure());
                }
            }
        }
        assertEquals(0, reachingExecutions);
    }

    @Test
    public void mapProducerClampsInputsAndPreservesJavaIntOverflow() {
        assertMapValue(false, 10, 9, 10);
        assertMapValue(false, 11, 9, 21);
        assertMapValue(true, Integer.MAX_VALUE, Integer.MAX_VALUE, -2);
    }

    private static void assertMapValue(boolean enabled, int input1,
                                       int input2, int expected) {
        ContainerThreeThreadRpcWorkload.MapProducer producer =
                new ContainerThreeThreadRpcWorkload.MapProducer(
                        Boolean.valueOf(enabled));
        producer.input1 = input1;
        producer.input2 = input2;
        assertEquals(expected, producer.compute());
    }

    private static void assertWorkerAndChannelIdentity(
            ContainerThreeThreadRpcWorkload.RunResult result) {
        long[] workers = result.getWorkerThreadIds();
        Set<Long> identities = new HashSet<>();
        for (long worker : workers) {
            assertTrue(worker > 0L);
            identities.add(worker);
        }
        assertEquals(3, identities.size());

        List<ContainerThreeThreadRpcWorkload.ChannelObservation> channels =
                result.getObservations();
        assertEquals(2, channels.size());
        for (ContainerThreeThreadRpcWorkload.ChannelObservation channel
                : channels) {
            assertTrue(channel.isCrossThread());
            assertEquals(workers[2], channel.getConsumerThreadId());
            if ("ARRAY".equals(channel.getChannel())) {
                assertEquals(workers[0], channel.getPublisherThreadId());
                assertEquals(result.getArrayValue(), channel.getValue());
            } else {
                assertEquals("MAP", channel.getChannel());
                assertEquals(workers[1], channel.getPublisherThreadId());
                assertEquals(result.getMapValue(), channel.getValue());
            }
        }
    }
}
