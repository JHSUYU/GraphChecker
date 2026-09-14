package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * One occurrence's loop bodies are one enclosing invocation's.
 *
 * <p>An enclosing activation of a region on a node is the k-th activation in
 * the window, and its loop bodies are {@code #k#aN}. Bodies of a different
 * enclosing invocation -- another thread, another entry event, another
 * request -- belong to a different k by definition.</p>
 *
 * <p>Two things let one occurrence absorb another activation, and lane
 * 11741f shows both in one row: {@code REGION.2392e4b7…#5} published
 * {@code #a1..#a6} from an enclosing call on {@code IPC Server handler 8} and
 * {@code #a7,#a8} from another on {@code handler 2} -- eight bodies of a
 * four-element key array -- while the tasks addressed #1 and #4, the two
 * other balancer-driven invocations of the same region, were never answered.
 * First, admission at the loop root did not compare the address at all when
 * the task had a unique OUT anchor and the request matched: any invocation
 * under {@code balancer/balance-block#1} was every one of those addresses.
 * Second, nothing bound a task to the invocation it was admitted for.</p>
 */
public class LoopBodiesBelongToOneInvocationTest {
    private static final String NODE = "hdfs-17899/nn0";
    private static final String PLANNED_REQUEST_API = "heartbeat";
    private static final String PLANNED_REQUEST_SOURCE =
            "hdfs-17899/target-dn";

    @After
    public void clear() {
        RuntimeTraceContext.resetForTests();
        CausynthTraceRecorder.setRecordingStartedForTests(false);
    }

    /** Two enclosing invocations are occurrences #1 and #2, never one. */
    @Test
    public void twoEnclosingInvocationsAreTwoOccurrences() {
        ConcolicTaskPlan.RuntimeTask first = task(1);
        ConcolicTaskPlan.RuntimeTask second = task(2);
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Arrays.asList(first, second));
        Object node = openWindowOn(NODE);

        Map<String, Integer> firstEntry = plan.addressLoopRootInvocation(
                first.rootMethod, first.rootMethod, node, new Object[0], 11L);
        Map<String, Integer> secondEntry = plan.addressLoopRootInvocation(
                first.rootMethod, first.rootMethod, node, new Object[0], 12L);

        assertEquals("the first enclosing invocation is occurrence 1",
                Collections.singletonMap(first.taskId, 1), firstEntry);
        assertEquals("the second is occurrence 2, and only that",
                Collections.singletonMap(second.taskId, 2), secondEntry);
    }

    /**
     * A task keeps the one enclosing invocation it was admitted for.
     *
     * <p>Every hook of one physical entry asks again, so the same entry
     * event answers yes for as long as that invocation runs; a different
     * entry event never does, whatever else about it matches.</p>
     */
    @Test
    public void aTaskKeepsTheInvocationItWasAdmittedFor() {
        ConcolicTaskPlan.RuntimeTask task = task(1);

        assertTrue("the invocation it was admitted for",
                task.claimsEnclosingInvocation(11L));
        assertTrue("and every sibling hook of that same entry",
                task.claimsEnclosingInvocation(11L));
        assertEquals(11L, task.enclosingInvocationEvent());
        assertTrue("a second enclosing invocation is not this occurrence",
                !task.claimsEnclosingInvocation(12L));
        assertEquals("and it did not take it either", 11L,
                task.enclosingInvocationEvent());
    }

    /**
     * The OUT anchor may defer a missing registration; it may not be the
     * address.
     *
     * <p>The deferral exists because a producer's receiver is commonly
     * unregistered at entry and its unique planner-authored OUT port
     * confirms the node before the activation publishes. At an enclosing
     * loop root it stood in for the whole address instead, so every
     * invocation under the planned request answered every k of that region.
     * It is gone from this path: the address decides, and the refusal names
     * the difference.</p>
     */
    @Test
    public void anInvocationUnderThePlannedRequestIsNotEveryOccurrence() {
        ConcolicTaskPlan.RuntimeTask first = task(1);
        ConcolicTaskPlan.RuntimeTask second = task(2);
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Arrays.asList(first, second));
        CausynthTraceRecorder.setRecordingStartedForTests(true);
        Object caller = new Object();
        RuntimeTraceContext.registerSource(caller, new SourceRef(
                "DATANODE", "dn", PLANNED_REQUEST_SOURCE, 0L));
        long request = RuntimeTraceContext.beginRequest(caller,
                PLANNED_REQUEST_API);
        try {
            // The condition the deferral turns on, stated rather than
            // assumed: unique OUT anchor, no registered receiver, and the
            // exact planned request.
            assertTrue("this is the shape the deferral admitted",
                    ConcolicTaskPlan
                            .mayDeferMissingContextToOutgoingAnchor(first,
                                    null, RuntimeTraceContext.current()));

            Map<String, Integer> admitted =
                    plan.addressLoopRootInvocation(first.rootMethod,
                            first.rootMethod, null, new Object[0], 11L);

            assertTrue("an activation of another node is no occurrence of "
                            + "this one: " + admitted,
                    admitted.isEmpty());
            assertTrue(first.unansweredAddress(),
                    first.unansweredAddress().startsWith(
                            "1 compatible activation(s)"));
        } finally {
            RuntimeTraceContext.endRequest(request);
        }
    }

    /** Opens the recording window with {@code node} registered. */
    private static Object openWindowOn(String sourceKey) {
        RuntimeTraceContext.resetForTests();
        CausynthTraceRecorder.setRecordingStartedForTests(true);
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("NAMENODE", "nn", sourceKey, 0L));
        return node;
    }

    /** The lane's own producer plan row, addressed at {@code ordinal}. */
    private static ConcolicTaskPlan.RuntimeTask task(int ordinal) {
        JsonObject encoded =
                row("plans/hdfs-17899-bug3-loop-body-producer.json");
        String regionId = encoded.get("regionId").getAsString();
        encoded.addProperty("taskId", "TASK.SEED.occurrence" + ordinal);
        encoded.addProperty("occurrenceId", NODE + "#epoch0/region/"
                + regionId + "#" + ordinal);
        encoded.getAsJsonObject("rootSelector")
                .addProperty("invocationOrdinal", ordinal);
        return new ConcolicTaskPlan.RuntimeTask(
                ExecutionTask.decode(encoded));
    }

    private static JsonObject row(String resource) {
        try (InputStream bytes = LoopBodiesBelongToOneInvocationTest.class
                .getClassLoader().getResourceAsStream(resource)) {
            if (bytes == null) {
                throw new IllegalStateException("missing " + resource);
            }
            return new JsonParser().parse(new InputStreamReader(bytes,
                    StandardCharsets.UTF_8)).getAsJsonObject();
        } catch (Exception failure) {
            throw new IllegalStateException(failure);
        }
    }
}
