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
 * is mentioned under the activation enclosing its call nearest, inside the
 * outermost one, on its call's thread; and each activation states its
 * thread and the activation enclosing it.
 */
public class RecordedHeapTest {
    private static final String METHOD = "<ex.Server: void handle()>";
    private static final String STORE = METHOD + "#u3";
    private static final String ACCESSOR = METHOD + "#u4";

    @Test
    public void theAggregationStatesHoldersMentionsAndNesting() {
        // A (call 10, thread 1) encloses B (call 20, under A's call 11);
        // C (call 30) runs on thread 2; call 40 on thread 3 under none.
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                method(1L, 1L, 10L, 0L, 0), method(2L, 1L, 11L, 10L, 100),
                method(3L, 1L, 20L, 11L, 0), method(4L, 1L, 21L, 20L, 0),
                method(5L, 2L, 30L, 0L, 0), method(6L, 3L, 40L, 0L, 400));
        List<RuntimeRegionPlanner.FieldAccessEvent> fields = Arrays.asList(
                // B's 200 held 201; C read a static field holding 300.
                field(7L, 21L, 200, 201), field(8L, 30L, 0, 300));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                // A handed 202 to a store on its 100; C's accessor on 300
                // returned 301.
                call(9L, "CALL_SITE_ENTER", 11L, 5L, STORE, 100),
                call(10L, "CALL_ARGUMENT", 11L, 5L, STORE, 202),
                call(11L, "CALL_SITE_RETURN", 11L, 5L, STORE, 0),
                call(12L, "CALL_SITE_ENTER", 30L, 6L, ACCESSOR, 300),
                call(13L, "CALL_SITE_RETURN", 30L, 6L, ACCESSOR, 301));
        List<Map<String, Object>> activations = Arrays.asList(
                activation(10L), activation(20L), activation(30L));
        RecordedHeap heap = RuntimeRegionPlanner.recordedHeap(methods,
                fields, runtime, activations,
                Collections.singletonMap(STORE, "<ex.Server: java.util.List"
                        + " items>"),
                Collections.singletonMap(ACCESSOR, "<ex.Conf: ex.Value"
                        + " value>"));

        Set<Integer> fromNothing = heap.reachable(new int[0]);
        assertTrue("a static field's object and what it held",
                fromNothing.containsAll(Arrays.asList(300, 301)));
        assertFalse(fromNothing.contains(201));
        assertTrue(heap.reachable(new int[] {200}).contains(201));
        assertTrue(heap.reachable(new int[] {100}).contains(202));

        // 201 and its holder 200: B's alone, inside A's tree, thread 1.
        assertConfinement(heap, 201, 20L, 10L, 1L);
        // 202 and its holder 100: A's alone.
        assertConfinement(heap, 202, 10L, 10L, 1L);
        // 301 and its holder 300: C's alone, its own tree, thread 2.
        assertConfinement(heap, 301, 30L, 30L, 2L);
        // An ambient call's object: under no occurrence, thread 3.
        assertConfinement(heap, 400, RecordedHeap.NOWHERE,
                RecordedHeap.NOWHERE, 3L);
        // An object no event mentions is confined nowhere.
        assertConfinement(heap, 999, RecordedHeap.NOWHERE,
                RecordedHeap.NOWHERE, RecordedHeap.NOWHERE);

        assertTrue(heap.within(20L, 10L));
        assertTrue(heap.within(10L, 10L));
        assertFalse(heap.within(10L, 20L));
        assertFalse(heap.within(30L, 10L));
        assertEquals(2L, heap.threadOfRoot(30L));
        assertEquals(RecordedHeap.NOWHERE, heap.threadOfRoot(40L));
    }

    private static void assertConfinement(RecordedHeap heap, int object,
                                          long occurrence, long tree,
                                          long thread) {
        RecordedHeap.Confinement found = heap.confinement(object);
        assertEquals(object + " occurrence", occurrence, found.occurrence);
        assertEquals(object + " tree", tree, found.tree);
        assertEquals(object + " thread", thread, found.thread);
    }

    private static RuntimeRegionPlanner.MethodEvent method(
            long seq, long tid, long callId, long parentCallId,
            int objectId) {
        return new RuntimeRegionPlanner.MethodEvent(seq, "test", "t" + tid,
                tid, METHOD, objectId, "ex.Server", callId, parentCallId,
                0L, 0L, 0L, 0L, null, false, "", "", "", false);
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
