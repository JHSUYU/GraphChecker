package edu.uva.liftlab.graphchecker.fixtures;

import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class FourThreadSharedFieldWorkloadTest {
    @Test
    public void propagatesBothForkedChainsAcrossFourRealThreads()
            throws Exception {
        Path source = Paths.get("src", "test", "java", "edu", "uva",
                "liftlab", "graphchecker", "fixtures",
                "FourThreadSharedFieldWorkload.java");
        String sourceText = new String(Files.readAllBytes(source),
                StandardCharsets.UTF_8);
        assertFalse(sourceText.contains("while("));
        assertFalse(sourceText.contains("while ("));

        int reachingExecutions = 0;
        for (Boolean left : new Boolean[]{Boolean.FALSE, Boolean.TRUE}) {
            for (Boolean right : new Boolean[]{Boolean.FALSE, Boolean.TRUE}) {
                FourThreadSharedFieldWorkload.RunResult result =
                        FourThreadSharedFieldWorkload.execute(left, right);

                int sourceForTwo = left.booleanValue() ? 1 : -3;
                int sourceForFour = right.booleanValue() ? 2 : -2;
                int fromTwo = sourceForTwo + 2;
                int fromFour = sourceForFour + 2;
                boolean bugReached = left.booleanValue()
                        && !right.booleanValue();

                assertEquals(left, result.getLeftInput());
                assertEquals(right, result.getRightInput());
                assertEquals(sourceForTwo, result.getSourceForTwo());
                assertEquals(sourceForFour, result.getSourceForFour());
                assertEquals(fromTwo, result.getFromTwo());
                assertEquals(fromFour, result.getFromFour());
                assertEquals(bugReached, result.isBugReached());

                long[] workerIds = result.getWorkerThreadIds();
                Set<Long> uniqueIds = new HashSet<>();
                for (long workerId : workerIds) {
                    assertTrue(workerId > 0L);
                    uniqueIds.add(workerId);
                }
                assertEquals(4, uniqueIds.size());
                assertPropagation(result.getObservations(), workerIds,
                        sourceForTwo, sourceForFour, fromTwo, fromFour);

                if (bugReached) {
                    reachingExecutions++;
                    assertEquals(FourThreadSharedFieldWorkload.SINK_THREAD,
                            result.getFailureThread());
                    assertTrue(result.getFailure()
                            instanceof FourThreadSharedFieldWorkload
                            .MergeBugReachedException);
                } else {
                    assertNull(result.getFailure());
                }
                assertTrue(result.toJson().contains(
                        "\"kind\":\"FOUR_THREAD_SHARED_FIELD_RESULT\""));
            }
        }
        assertEquals(1, reachingExecutions);
    }

    private static void assertPropagation(
            List<FourThreadSharedFieldWorkload.EdgeObservation> observations,
            long[] workerIds, int sourceForTwo, int sourceForFour,
            int fromTwo, int fromFour) {
        assertEquals(4, observations.size());
        Map<String, FourThreadSharedFieldWorkload.EdgeObservation> byChannel =
                new HashMap<>();
        for (FourThreadSharedFieldWorkload.EdgeObservation observation
                : observations) {
            byChannel.put(observation.getChannel(), observation);
            assertTrue(observation.isHappensBeforeObserved());
            assertTrue(observation.getValueFingerprint()
                    .matches("sha256:[0-9a-f]{64}"));
        }
        assertEquals(4, byChannel.size());

        assertEdge(byChannel.get("1_TO_2"), sourceForTwo,
                workerIds[0], workerIds[1]);
        assertEdge(byChannel.get("1_TO_4"), sourceForFour,
                workerIds[0], workerIds[3]);
        assertEdge(byChannel.get("2_TO_3"), fromTwo,
                workerIds[1], workerIds[2]);
        assertEdge(byChannel.get("4_TO_3"), fromFour,
                workerIds[3], workerIds[2]);

        assertTrue(byChannel.get("1_TO_2").getReceiveSequence()
                < byChannel.get("2_TO_3").getPublishSequence());
        assertTrue(byChannel.get("1_TO_4").getReceiveSequence()
                < byChannel.get("4_TO_3").getPublishSequence());
        assertTrue("thread 3 must read the two relay fields in fixed order",
                byChannel.get("2_TO_3").getReceiveSequence()
                        < byChannel.get("4_TO_3").getReceiveSequence());
    }

    private static void assertEdge(
            FourThreadSharedFieldWorkload.EdgeObservation observation,
            int value, long publisher, long consumer) {
        assertEquals(value, observation.getPublishedValue());
        assertEquals(value, observation.getReceivedValue());
        assertEquals(publisher, observation.getPublisherThreadId());
        assertEquals(consumer, observation.getConsumerThreadId());
        assertTrue(observation.getPublishSequence()
                < observation.getReceiveSequence());
    }
}
