package edu.uva.liftlab.graphchecker.fixtures;

import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class ThreeThreadRpcScenarioWorkloadTest {
    private static final Path CASES = Paths.get("experiments", "generic",
            "three-thread-rpc", "cases");

    @Test
    public void additiveOrReachesWhenEitherProducerIsTrue() throws Exception {
        assertScenario(
                ThreeThreadRpcScenarioWorkload.Variant.ADDITIVE_OR,
                new int[]{-1, 2}, new int[]{-1, 3},
                values("01", "10", "11"),
                ThreeThreadRpcScenarioWorkload.AdditiveOrProducerA.class,
                ThreeThreadRpcScenarioWorkload.AdditiveOrProducerB.class,
                ThreeThreadRpcScenarioWorkload
                        .AdditiveOrBugReachedException.class);
    }

    @Test
    public void xorReachesThroughTheConsumerElseEdge() throws Exception {
        assertScenario(
                ThreeThreadRpcScenarioWorkload.Variant.XOR_ELSE_EDGE,
                new int[]{0, 1}, new int[]{0, 1},
                values("01", "10"),
                ThreeThreadRpcScenarioWorkload.XorElseEdgeProducerA.class,
                ThreeThreadRpcScenarioWorkload.XorElseEdgeProducerB.class,
                ThreeThreadRpcScenarioWorkload
                        .XorElseEdgeBugReachedException.class);
    }

    @Test
    public void greaterComparisonReachesOnlyProducerAOneHot()
            throws Exception {
        assertScenario(
                ThreeThreadRpcScenarioWorkload.Variant.GREATER_ONE_HOT,
                new int[]{-1, 1}, new int[]{-1, 1}, values("10"),
                ThreeThreadRpcScenarioWorkload.GreaterOneHotProducerA.class,
                ThreeThreadRpcScenarioWorkload.GreaterOneHotProducerB.class,
                ThreeThreadRpcScenarioWorkload
                        .GreaterOneHotBugReachedException.class);
    }

    @Test
    public void lessComparisonReachesOnlyProducerBOneHot() throws Exception {
        assertScenario(
                ThreeThreadRpcScenarioWorkload.Variant.LESS_ONE_HOT,
                new int[]{-1, 1}, new int[]{-1, 1}, values("01"),
                ThreeThreadRpcScenarioWorkload.LessOneHotProducerA.class,
                ThreeThreadRpcScenarioWorkload.LessOneHotProducerB.class,
                ThreeThreadRpcScenarioWorkload
                        .LessOneHotBugReachedException.class);
    }

    @Test
    public void dependentProducerRelationsReachOnlyWhenBothAreTrue()
            throws Exception {
        assertScenario(
                ThreeThreadRpcScenarioWorkload.Variant.DEPENDENT_MERGE,
                new int[]{-3, 7}, new int[]{-3, 4}, values("11"),
                ThreeThreadRpcScenarioWorkload.DependentMergeProducerA.class,
                ThreeThreadRpcScenarioWorkload.DependentMergeProducerB.class,
                ThreeThreadRpcScenarioWorkload
                        .DependentMergeBugReachedException.class);
    }

    private static void assertScenario(
            ThreeThreadRpcScenarioWorkload.Variant variant,
            int[] expectedA, int[] expectedB, Set<String> reachingInputs,
            Class<?> producerA, Class<?> producerB,
            Class<? extends Throwable> bugType) throws Exception {
        assertFalse("false,false must remain the discovery seed",
                reachingInputs.contains("00"));
        int reachingExecutions = 0;
        for (Boolean b1 : new Boolean[]{Boolean.FALSE, Boolean.TRUE}) {
            for (Boolean b2 : new Boolean[]{Boolean.FALSE, Boolean.TRUE}) {
                ThreeThreadRpcScenarioWorkload.RunResult result =
                        ThreeThreadRpcScenarioWorkload.execute(variant, b1, b2);
                String valuation = (b1.booleanValue() ? "1" : "0")
                        + (b2.booleanValue() ? "1" : "0");
                boolean expectedBug = reachingInputs.contains(valuation);

                assertEquals(variant, result.getVariant());
                assertEquals(b1, result.getB1());
                assertEquals(b2, result.getB2());
                assertEquals(expectedA[b1.booleanValue() ? 1 : 0],
                        result.getA());
                assertEquals(expectedB[b2.booleanValue() ? 1 : 0],
                        result.getB());
                assertEquals(expectedBug, result.isBugReached());
                assertTrue("producer worker frames did not overlap",
                        result.isProducerConcurrencyObserved());
                assertTrue("consumer started before both producers terminated",
                        result.isConsumerStartedAfterProducerThreadsTerminated());

                long[] workerIds = result.getWorkerThreadIds();
                Set<Long> workers = new HashSet<>();
                for (long threadId : workerIds) {
                    assertTrue(threadId > 0L);
                    workers.add(threadId);
                }
                assertEquals(3, workers.size());
                assertRpcObservations(result.getRpcObservations(), workerIds,
                        workers);

                if (expectedBug) {
                    reachingExecutions++;
                    assertEquals(ThreeThreadRpcScenarioWorkload.CONSUMER_THREAD,
                            result.getFailureThread());
                    assertTrue(bugType.isInstance(result.getFailure()));
                } else {
                    assertNull(result.getFailure());
                }
            }
        }
        assertEquals(reachingInputs.size(), reachingExecutions);
        assertCaseMetadata(variant, producerA, producerB, bugType);
    }

    private static void assertRpcObservations(
            List<ThreeThreadRpcScenarioWorkload.RpcObservation> observations,
            long[] workerIds, Set<Long> workers) {
        assertEquals(2, observations.size());
        Set<String> channels = new HashSet<>();
        for (ThreeThreadRpcScenarioWorkload.RpcObservation observation
                : observations) {
            channels.add(observation.getChannel());
            assertEquals(observation.getPublishedValue(),
                    observation.getReceivedValue());
            assertTrue(observation.isRuntimeValueEqualityObserved());
            assertTrue(workers.contains(observation.getPublisherThreadId()));
            assertEquals(workerIds[2], observation.getConsumerThreadId());
            if ("A".equals(observation.getChannel())) {
                assertEquals(workerIds[0],
                        observation.getPublisherThreadId());
            } else if ("B".equals(observation.getChannel())) {
                assertEquals(workerIds[1],
                        observation.getPublisherThreadId());
            }
            assertTrue(observation.getValueFingerprint()
                    .matches("sha256:[0-9a-f]{64}"));
        }
        assertEquals(values("A", "B"), channels);
    }

    private static void assertCaseMetadata(
            ThreeThreadRpcScenarioWorkload.Variant variant,
            Class<?> producerA, Class<?> producerB,
            Class<? extends Throwable> bugType) throws Exception {
        Path caseDirectory = CASES.resolve(variant.getDirectoryName());
        Path target = caseDirectory.resolve("target.yaml");
        Path workflow = caseDirectory.resolve("workflow.properties");
        assertFalse("case must not declare an RPC topology",
                Files.exists(caseDirectory.resolve("rpc-topology.jsonl")));
        assertTrue("case target is missing: " + target,
                Files.isRegularFile(target));
        assertTrue("case workflow is missing: " + workflow,
                Files.isRegularFile(workflow));

        assertNotNull(producerA.getDeclaredMethod("compute", Boolean.class));
        assertNotNull(producerB.getDeclaredMethod("compute", Boolean.class));

        String targetText = new String(Files.readAllBytes(target),
                StandardCharsets.UTF_8).trim();
        assertEquals("seed_exception: " + bugType.getName(), targetText);
        String workflowText = new String(Files.readAllBytes(workflow),
                StandardCharsets.UTF_8);
        assertTrue(workflowText.contains("fixture_variant=" + variant.name()));
        assertTrue(workflowText.contains("fixture_class="
                + ThreeThreadRpcScenarioWorkload.class.getName()));
        assertTrue(workflowText.contains("fixture_test_class="
                + ThreeThreadRpcScenarioWorkloadTest.class.getName()));
        assertFalse(workflowText.contains("rpc_mapping_file"));
        assertTrue(workflowText.contains("-D"
                + ThreeThreadRpcScenarioWorkload.VARIANT_PROPERTY + "="
                + variant.name()));
    }

    private static Set<String> values(String... values) {
        return new HashSet<>(Arrays.asList(values));
    }
}
