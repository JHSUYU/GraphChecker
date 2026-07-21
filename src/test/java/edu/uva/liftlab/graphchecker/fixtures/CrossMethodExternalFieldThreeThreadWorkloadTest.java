package edu.uva.liftlab.graphchecker.fixtures;

import org.junit.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
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

public class CrossMethodExternalFieldThreeThreadWorkloadTest {
    private static final Path SOURCE = Paths.get("src", "test", "java",
            "edu", "uva", "liftlab", "graphchecker", "fixtures",
            "CrossMethodExternalFieldThreeThreadWorkload.java");
    private static final Path FIXTURE = Paths.get("experiments", "generic",
            "three-thread-rpc", "cross-method-fields");

    @Test
    public void exactBooleanTruthTableUsesThreeRealThreads()
            throws Exception {
        int savedProcessWeight = CrossMethodExternalFieldThreeThreadWorkload
                .ExternalTuning.processWeight;
        try {
            CrossMethodExternalFieldThreeThreadWorkload.ExternalTuning
                    .processWeight = 2;
            boolean[][] inputs = new boolean[][]{
                    {false, false},
                    {false, true},
                    {true, false},
                    {true, true}
            };
            int[] expectedProducerValues = new int[]{7, 7, 19, 19};
            int[] expectedThresholdValues = new int[]{10, 20, 10, 20};
            boolean[] expectedFatal = new boolean[]{
                    false, false, true, false
            };
            int reachingExecutions = 0;

            for (int index = 0; index < inputs.length; index++) {
                Boolean enabled = Boolean.valueOf(inputs[index][0]);
                Boolean strict = Boolean.valueOf(inputs[index][1]);
                CrossMethodExternalFieldThreeThreadWorkload.RunResult result =
                        CrossMethodExternalFieldThreeThreadWorkload.execute(
                                enabled, strict);

                assertEquals(enabled, result.getProducerAEnabled());
                assertEquals(strict, result.getStrictThreshold());
                assertEquals(expectedProducerValues[index],
                        result.getProducerValue());
                assertEquals(expectedThresholdValues[index],
                        result.getThresholdValue());
                assertEquals(expectedFatal[index], result.isBugReached());
                assertEquals(enabled.booleanValue()
                                && !strict.booleanValue(),
                        result.isBugReached());
                assertTrue(result.isProducerConcurrencyObserved());
                assertTrue(result
                        .isConsumerStartedAfterProducersTerminated());
                assertThreadAndChannelIdentity(result);

                if (result.isBugReached()) {
                    reachingExecutions++;
                    assertEquals(CrossMethodExternalFieldThreeThreadWorkload
                                    .CONSUMER_THREAD,
                            result.getFailureThread());
                    assertTrue(result.getFailure() instanceof
                            CrossMethodExternalFieldThreeThreadWorkload
                                    .CrossMethodBugReachedException);
                } else {
                    assertNull(result.getFailure());
                    assertNull(result.getFailureThread());
                }
            }
            assertEquals(1, reachingExecutions);
        } finally {
            CrossMethodExternalFieldThreeThreadWorkload.ExternalTuning
                    .processWeight = savedProcessWeight;
        }
    }

    @Test
    public void auxiliaryFieldsStaySymbolicWithoutFlatteningTruthTable() {
        int savedProcessWeight = CrossMethodExternalFieldThreeThreadWorkload
                .ExternalTuning.processWeight;
        int[] values = new int[]{Integer.MIN_VALUE, -1, 0, 1, 2, 3,
                Integer.MAX_VALUE};
        String[] routes = new String[]{"plain", "ready", "already-set"};
        try {
            for (int profileValue : values) {
                CrossMethodExternalFieldThreeThreadWorkload.ExternalProfile
                        profile = new CrossMethodExternalFieldThreeThreadWorkload
                        .ExternalProfile(profileValue);
                CrossMethodExternalFieldThreeThreadWorkload.ProducerA producer =
                        new CrossMethodExternalFieldThreeThreadWorkload
                                .ProducerA(profile);
                for (int processValue : values) {
                    CrossMethodExternalFieldThreeThreadWorkload.ExternalTuning
                            .processWeight = processValue;
                    for (int baseValue : values) {
                        for (String route : routes) {
                            int disabled = producer.compute(Boolean.FALSE,
                                    baseValue, route);
                            int enabled = producer.compute(Boolean.TRUE,
                                    baseValue, route);
                            int expectedBase = bounded(baseValue)
                                    + bounded(profileValue)
                                    + bounded(processValue)
                                    + (route.contains("ready") ? 1 : 0);
                            assertEquals(expectedBase, disabled);
                            assertEquals(expectedBase + 12, enabled);

                            assertTrue(disabled
                                    < CrossMethodExternalFieldThreeThreadWorkload
                                    .RELAXED_THRESHOLD);
                            assertTrue(enabled
                                    > CrossMethodExternalFieldThreeThreadWorkload
                                    .RELAXED_THRESHOLD);
                            assertTrue(enabled
                                    < CrossMethodExternalFieldThreeThreadWorkload
                                    .STRICT_THRESHOLD);
                        }
                    }
                }
            }
        } finally {
            CrossMethodExternalFieldThreeThreadWorkload.ExternalTuning
                    .processWeight = savedProcessWeight;
        }
    }

    @Test
    public void helperChainAndExternalLiveInsHaveRequiredShape()
            throws Exception {
        Method compute = CrossMethodExternalFieldThreeThreadWorkload
                .ProducerA.class.getDeclaredMethod("compute", Boolean.class,
                        int.class, String.class);
        Method firstHop = CrossMethodExternalFieldThreeThreadWorkload
                .ProducerA.class.getDeclaredMethod("firstHop", Boolean.class,
                        int.class, String.class);
        Method secondHop = CrossMethodExternalFieldThreeThreadWorkload
                .SecondHop.class.getDeclaredMethod("secondHop",
                        CrossMethodExternalFieldThreeThreadWorkload
                                .ExternalProfile.class,
                        Boolean.class, int.class, String.class);
        Method thirdHop = CrossMethodExternalFieldThreeThreadWorkload
                .ThirdHop.class.getDeclaredMethod("thirdHop", Boolean.class,
                        int.class, String.class);
        assertNotNull(compute);
        assertNotNull(firstHop);
        assertNotNull(secondHop);
        assertNotNull(thirdHop);

        Field instanceWeight = CrossMethodExternalFieldThreeThreadWorkload
                .ExternalProfile.class.getDeclaredField("instanceWeight");
        Field processWeight = CrossMethodExternalFieldThreeThreadWorkload
                .ExternalTuning.class.getDeclaredField("processWeight");
        assertEquals(int.class, instanceWeight.getType());
        assertFalse(Modifier.isStatic(instanceWeight.getModifiers()));
        assertFalse(Modifier.isFinal(instanceWeight.getModifiers()));
        assertEquals(int.class, processWeight.getType());
        assertTrue(Modifier.isStatic(processWeight.getModifiers()));
        assertFalse(Modifier.isFinal(processWeight.getModifiers()));

        Class<?> worker = Class.forName(
                CrossMethodExternalFieldThreeThreadWorkload.class.getName()
                        + "$ProducerAThread");
        Field baseInput = worker.getDeclaredField("baseInput");
        Field routeInput = worker.getDeclaredField("routeInput");
        assertEquals(int.class, baseInput.getType());
        assertEquals(String.class, routeInput.getType());
        assertFalse(Modifier.isStatic(baseInput.getModifiers()));
        assertFalse(Modifier.isFinal(baseInput.getModifiers()));
        assertFalse(Modifier.isStatic(routeInput.getModifiers()));
        assertFalse(Modifier.isFinal(routeInput.getModifiers()));

        String source = new String(Files.readAllBytes(SOURCE),
                StandardCharsets.UTF_8);
        String compact = source.replaceAll("\\s+", " ");
        assertTrue(compact.contains(
                "return firstHop(enabled, baseInput, routeInput);"));
        assertTrue(compact.contains(
                "return secondHop.secondHop(profile, enabled, boundedBase, routeInput);"));
        assertTrue(compact.contains(
                "return thirdHop.thirdHop(enabled, accumulated, routeInput);"));
        assertTrue(compact.contains(
                "int instanceWeight = profile.instanceWeight;"));
        assertTrue(compact.contains(
                "int processWeight = ExternalTuning.processWeight;"));
        assertTrue(compact.contains("if (args.length != 2)"));
        int profileConstruction = source.indexOf("new ExternalProfile(2)");
        int producerStart = source.indexOf("producerAThread.start()");
        assertTrue(profileConstruction >= 0);
        assertTrue(producerStart > profileConstruction);
        assertFalse(source.matches("(?s).*\\bwhile\\s*\\(.*"));
    }

    @Test
    public void workflowReusesGenericRunnerWithOnlyTwoBooleanCliInputs()
            throws Exception {
        Path workflow = FIXTURE.resolve("workflow.properties");
        Path target = FIXTURE.resolve("target.yaml");
        assertTrue(Files.isRegularFile(workflow));
        assertTrue(Files.isRegularFile(target));
        String configuration = new String(Files.readAllBytes(workflow),
                StandardCharsets.UTF_8);
        String targetSpec = new String(Files.readAllBytes(target),
                StandardCharsets.UTF_8);
        assertTrue(configuration.contains("fixture_class="
                + CrossMethodExternalFieldThreeThreadWorkload.class
                .getName()));
        assertTrue(configuration.contains(" false false"));
        assertFalse(configuration.contains("rpc_mapping_file"));
        assertTrue(targetSpec.contains(CrossMethodExternalFieldThreeThreadWorkload
                .CrossMethodBugReachedException.class.getName()));
    }

    private static int bounded(int value) {
        if (value < 0) {
            return 0;
        }
        if (value > 2) {
            return 2;
        }
        return value;
    }

    private static void assertThreadAndChannelIdentity(
            CrossMethodExternalFieldThreeThreadWorkload.RunResult result) {
        long[] workers = result.getWorkerThreadIds();
        Set<Long> identities = new HashSet<>();
        for (long worker : workers) {
            assertTrue(worker > 0L);
            identities.add(worker);
        }
        assertEquals(3, identities.size());

        List<CrossMethodExternalFieldThreeThreadWorkload.ChannelObservation>
                observations = result.getObservations();
        assertEquals(2, observations.size());
        Set<String> channels = new HashSet<>();
        for (CrossMethodExternalFieldThreeThreadWorkload.ChannelObservation
                observation : observations) {
            channels.add(observation.getChannel());
            assertTrue(observation.isCrossThread());
            assertEquals(workers[2], observation.getConsumerThreadId());
            if ("A".equals(observation.getChannel())) {
                assertEquals(workers[0], observation.getPublisherThreadId());
                assertEquals(result.getProducerValue(),
                        observation.getValue());
            } else {
                assertEquals("B", observation.getChannel());
                assertEquals(workers[1], observation.getPublisherThreadId());
                assertEquals(result.getThresholdValue(),
                        observation.getValue());
            }
        }
        assertTrue(channels.contains("A"));
        assertTrue(channels.contains("B"));
    }
}
