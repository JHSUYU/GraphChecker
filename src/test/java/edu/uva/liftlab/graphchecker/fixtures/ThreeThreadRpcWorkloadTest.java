package edu.uva.liftlab.graphchecker.fixtures;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
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
    private static final Path TOPOLOGY = Paths.get("experiments", "generic",
            "three-thread-rpc", "rpc-topology.jsonl");

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
                assertEquals(result.getA() > result.getB(),
                        result.isBugReached());
                Set<Long> workers = new HashSet<>();
                for (long threadId : result.getWorkerThreadIds()) {
                    assertTrue(threadId > 0L);
                    workers.add(threadId);
                }
                assertEquals(3, workers.size());
                assertRpcObservations(result.getRpcObservations(), workers);

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
    public void declaredRpcTopologyNamesRealMethodsOnly() throws Exception {
        assertTrue("RPC topology is missing: " + TOPOLOGY,
                Files.isRegularFile(TOPOLOGY));
        List<String> rows = Files.readAllLines(TOPOLOGY,
                StandardCharsets.UTF_8);
        assertEquals(2, rows.size());
        Set<String> channels = new HashSet<>();
        for (String row : rows) {
            JsonObject mapping = JsonParser.parseString(row)
                    .getAsJsonObject();
            assertEquals("TEST_DECLARED_RPC_TOPOLOGY",
                    mapping.get("authority").getAsString());
            assertFalse(mapping.has("formula"));
            assertFalse(mapping.has("smt"));
            channels.add(mapping.get("channel").getAsString());
            assertMethod(mapping.getAsJsonObject("producer"));
            assertMethod(mapping.getAsJsonObject("publisher"));
            assertMethod(mapping.getAsJsonObject("consumer"));
        }
        assertTrue(channels.contains("A"));
        assertTrue(channels.contains("B"));
    }

    private static void assertRpcObservations(
            List<ThreeThreadRpcWorkload.RpcObservation> observations,
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
            assertTrue(observation.getValueFingerprint()
                    .matches("sha256:[0-9a-f]{64}"));
        }
        assertTrue(channels.contains("A"));
        assertTrue(channels.contains("B"));
    }

    private static void assertMethod(JsonObject selector) throws Exception {
        String owner = selector.get("owner").getAsString();
        String name = selector.get("name").getAsString();
        Class<?> type = Class.forName(owner);
        Class<?>[] parameters;
        if (selector.has("parameter")
                && "java.lang.Boolean".equals(
                selector.get("parameter").getAsString())) {
            parameters = new Class<?>[]{Boolean.class};
        } else if (selector.has("parameter")
                && "int".equals(selector.get("parameter").getAsString())) {
            parameters = new Class<?>[]{Integer.TYPE};
        } else {
            parameters = new Class<?>[0];
        }
        Method method = type.getDeclaredMethod(name, parameters);
        assertNotNull(method);
    }
}
