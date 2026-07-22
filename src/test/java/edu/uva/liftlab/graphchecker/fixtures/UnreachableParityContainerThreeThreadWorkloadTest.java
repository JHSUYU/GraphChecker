package edu.uva.liftlab.graphchecker.fixtures;

import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class UnreachableParityContainerThreeThreadWorkloadTest {
    private static final Path SOURCE = Paths.get("src", "test", "java",
            "edu", "uva", "liftlab", "graphchecker", "fixtures",
            "UnreachableParityContainerThreeThreadWorkload.java");

    @Test
    public void everyNestedInputValuationKeepsParityTargetUnreachable()
            throws Exception {
        String source = new String(Files.readAllBytes(SOURCE),
                StandardCharsets.UTF_8);
        assertTrue(source.contains("payloads[1]"));
        assertTrue(source.contains("selected.state.guard.enabled"));
        assertTrue(source.contains("values.entrySet().iterator()"));
        assertTrue(source.contains("sign * 2 + 1"));
        assertTrue(source.contains("magnitude * 2"));
        assertTrue(source.contains("if (odd == even)"));
        assertTrue(source.contains("@CausynthExceptionTarget("
                + "\"unreachable-parity\")"));
        assertFalse(source.matches("(?s).*\\bwhile\\s*\\(.*"));

        for (Boolean oddInput : new Boolean[]{Boolean.FALSE,
                Boolean.TRUE}) {
            for (Boolean evenInput : new Boolean[]{Boolean.FALSE,
                    Boolean.TRUE}) {
                UnreachableParityContainerThreeThreadWorkload.RunResult result =
                        UnreachableParityContainerThreeThreadWorkload.execute(
                                oddInput, evenInput);
                assertEquals(oddInput, result.getOddInput());
                assertEquals(evenInput, result.getEvenInput());
                assertEquals(oddInput.booleanValue() ? 3 : -1,
                        result.getOddValue());
                assertEquals(evenInput.booleanValue() ? 4 : 0,
                        result.getEvenValue());
                assertEquals(1, Math.floorMod(result.getOddValue(), 2));
                assertEquals(0, Math.floorMod(result.getEvenValue(), 2));
                assertFalse(result.isBugReached());
                assertNull(result.getFailure());
                assertNull(result.getFailureThread());
                assertTrue(result.isProducerConcurrencyObserved());
                assertTrue(result
                        .isConsumerStartedAfterProducersTerminated());
                assertTrue(result.isChannelIdentityValid());
                assertDistinctWorkers(result.getWorkerThreadIds());
            }
        }
    }

    private static void assertDistinctWorkers(long[] workers) {
        assertEquals(3, workers.length);
        Set<Long> identities = new HashSet<>();
        for (long worker : workers) {
            assertTrue(worker > 0L);
            identities.add(worker);
        }
        assertEquals(3, identities.size());
    }
}
