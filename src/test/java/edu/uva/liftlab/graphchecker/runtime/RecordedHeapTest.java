package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.RecordedHeap;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * THE RECORDED HEAP as the trace aggregation builds it ({@link
 * RuntimeRegionPlanner#recordedHeap}): a field access's receiver holds its
 * value, a static field's value is a root, a storing call's receiver holds
 * each argument, an accessor call's receiver what it returned; each object
 * is mentioned under its call's causal context (the entry's requestKey in
 * its recording window; none under a turn every window counts #0), and
 * each activation states its root call's.
 */
public class RecordedHeapTest {
    private static final String METHOD = "<ex.Server: void handle()>";
    private static final String STORE = METHOD + "#u3";
    private static final String ACCESSOR = METHOD + "#u4";

    @Test
    public void theAggregationStatesHoldersMentionsAndContexts() {
        // Calls 10-21 serve request A#1 (call 20 on another thread); 30 is
        // tick B#1; 40 runs under no context; 50 serves request C#1.  In a
        // second window, 60 serves another request A#1; 70 a turn begun in
        // an older window, which every window counts #0.
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                method(1L, 1L, 10L, 0L, 0, "A#1", 1),
                method(2L, 1L, 11L, 10L, 100, "A#1", 1),
                method(3L, 2L, 20L, 0L, 0, "A#1", 1),
                method(4L, 2L, 21L, 20L, 0, "A#1", 1),
                method(5L, 3L, 30L, 0L, 0, "B#1", 1),
                method(6L, 4L, 40L, 0L, 400, "", 1),
                method(7L, 1L, 50L, 0L, 0, "C#1", 1),
                method(8L, 1L, 60L, 0L, 600, "A#1", 2),
                method(9L, 1L, 70L, 0L, 700, "T#0", 2));
        List<RuntimeRegionPlanner.FieldAccessEvent> fields = Arrays.asList(
                // A's 200 held 201; B read a static field holding 300; C
                // read 201 too.
                field(8L, 21L, 200, 201), field(9L, 30L, 0, 300),
                field(10L, 50L, 500, 201));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                // A handed 202 to a store on its 100; B's accessor on 300
                // returned 301.
                call(11L, "CALL_SITE_ENTER", 11L, 5L, STORE, 100),
                call(12L, "CALL_ARGUMENT", 11L, 5L, STORE, 202),
                call(13L, "CALL_SITE_RETURN", 11L, 5L, STORE, 0),
                call(14L, "CALL_SITE_ENTER", 30L, 6L, ACCESSOR, 300),
                call(15L, "CALL_SITE_RETURN", 30L, 6L, ACCESSOR, 301));
        List<Map<String, Object>> activations = Arrays.asList(
                activation(10L), activation(20L), activation(30L),
                activation(40L), activation(60L), activation(70L));
        RecordedHeap heap = RuntimeRegionPlanner.recordedHeap(methods,
                fields, runtime, activations,
                Collections.singletonMap(STORE, "<ex.Server: java.util.List"
                        + " items>"),
                Collections.singletonMap(ACCESSOR, "<ex.Conf: ex.Value"
                        + " value>"));

        Set<Integer> fromNothing = heap.reachable(new int[0]);
        assertTrue("a static field's object and what it held",
                fromNothing.containsAll(Arrays.asList(300, 301)));
        assertFalse(fromNothing.contains(202));
        assertTrue(heap.reachable(new int[] {200}).contains(201));
        assertTrue(heap.reachable(new int[] {100}).contains(202));

        long a = heap.contextOfRoot(10L);
        long b = heap.contextOfRoot(30L);
        assertEquals("one request on two threads is one context", a,
                heap.contextOfRoot(20L));
        assertFalse(a == b);
        assertEquals("an occurrence under no context has none",
                RecordedHeap.NOWHERE, heap.contextOfRoot(40L));
        assertFalse("a request's key in another window is another context",
                a == heap.contextOfRoot(60L));
        assertEquals("a turn begun in an older window names none",
                RecordedHeap.NOWHERE, heap.contextOfRoot(70L));
        // 202 and its holder 100: A's alone, on two of its threads' calls.
        assertEquals(a, heap.confinement(202));
        // 301 and its holder 300: B's alone.
        assertEquals(b, heap.confinement(301));
        // 201, mentioned under A and C, is confined nowhere; its holder
        // 200, mentioned under A alone, is A's.
        assertEquals(RecordedHeap.NOWHERE, heap.confinement(201));
        assertEquals(a, heap.confinement(200));
        // A call under no context or under #0, and an object no event
        // mentions.
        assertEquals(RecordedHeap.NOWHERE, heap.confinement(400));
        assertEquals(RecordedHeap.NOWHERE, heap.confinement(700));
        assertEquals(heap.contextOfRoot(60L), heap.confinement(600));
        assertEquals(RecordedHeap.NOWHERE, heap.confinement(999));
    }

    private static RuntimeRegionPlanner.MethodEvent method(
            long seq, long tid, long callId, long parentCallId,
            int objectId, String context, int window) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "test", "t" + tid,
                tid, METHOD, objectId, "ex.Server", callId, parentCallId,
                0L, 0L, 0L, 0L, null, false, context, "", "", false, window);
    }

    private static RuntimeRegionPlanner.FieldAccessEvent field(
            long seq, long callId, int receiver, int value) {
        return new RuntimeRegionPlanner.FieldAccessEvent(seq, "FIELD_WRITE",
                METHOD, callId, 2, "", "<ex.Server: java.lang.Object held>",
                receiver, value, "");
    }

    private static RuntimeRegionPlanner.RuntimeEvent call(
            long seq, String kind, long callId, long invocationId,
            String siteId, int objectId) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, kind, METHOD,
                callId, invocationId, siteId, "", 0, "", objectId, "", null,
                null, "", "");
    }

    private static Map<String, Object> activation(long rootCallId) {
        Map<String, Object> activation = new HashMap<>();
        activation.put("rootCallId", rootCallId);
        return activation;
    }
}
