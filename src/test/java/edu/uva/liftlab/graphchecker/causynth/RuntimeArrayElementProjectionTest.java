package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

public class RuntimeArrayElementProjectionTest {
    @Test
    public void exactObjectAndIndexPairReferenceArrayElements() {
        List<Map<String, Object>> producer = Arrays.asList(
                access("ARRAY_READ", 11, 100, 0, 201),
                access("ARRAY_READ", 13, 100, 1, 202));
        List<Map<String, Object>> consumer = Arrays.asList(
                access("ARRAY_WRITE", 21, 110, 0, 301),
                access("ARRAY_WRITE", 22, 110, 1, 302));

        RuntimeSelectedRegionFinalizer.ArrayElementProjection result =
                RuntimeSelectedRegionFinalizer
                        .exactDeclaredArrayElementPairs(
                                producer, 100, consumer, 110,
                                10, 20, 20, 30);

        assertTrue(result.proved());
        assertEquals(2, result.width);
        assertEquals(201, result.pairs.get(0)[0]);
        assertEquals(301, result.pairs.get(0)[1]);
        assertEquals(202, result.pairs.get(1)[0]);
        assertEquals(302, result.pairs.get(1)[1]);
    }

    @Test
    public void conflictingIndexOrCapacityFailsClosed() {
        List<Map<String, Object>> conflict = Arrays.asList(
                access("ARRAY_READ", 11, 100, 0, 201),
                access("ARRAY_READ", 12, 100, 0, 202));
        RuntimeSelectedRegionFinalizer.ArrayElementProjection ambiguous =
                RuntimeSelectedRegionFinalizer
                        .exactDeclaredArrayElementPairs(
                                conflict, 100,
                                Arrays.asList(access("ARRAY_WRITE", 21,
                                        110, 0, 301)),
                                110, 10, 20, 20, 30);
        assertFalse(ambiguous.proved());
        assertEquals("AMBIGUOUS_ARRAY_ELEMENT_IDENTITY",
                ambiguous.blocker);

        int beyond = LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY;
        List<Map<String, Object>> producer = new ArrayList<>();
        List<Map<String, Object>> consumer = new ArrayList<>();
        for (int index = 0; index <= beyond; index++) {
            producer.add(access("ARRAY_READ", 11 + index, 100,
                    index, 200 + index));
            consumer.add(access("ARRAY_WRITE", 111 + index, 110,
                    index, 400 + index));
        }
        RuntimeSelectedRegionFinalizer.ArrayElementProjection overflow =
                RuntimeSelectedRegionFinalizer
                        .exactDeclaredArrayElementPairs(
                                producer, 100, consumer, 110,
                                10, 100, 100, 1000);
        assertFalse(overflow.proved());
        assertEquals("BOUND_INSUFFICIENT", overflow.blocker);
    }

    @Test
    public void repeatedExactObservationIsIdempotent() {
        List<Map<String, Object>> producer = Arrays.asList(
                access("ARRAY_READ", 11, 100, 0, 201),
                access("ARRAY_READ", 12, 100, 0, 201));
        List<Map<String, Object>> consumer = Arrays.asList(
                access("ARRAY_WRITE", 21, 110, 0, 301),
                access("ARRAY_WRITE", 22, 110, 0, 301));

        RuntimeSelectedRegionFinalizer.ArrayElementProjection result =
                RuntimeSelectedRegionFinalizer
                        .exactDeclaredArrayElementPairs(
                                producer, 100, consumer, 110,
                                10, 20, 20, 30);

        assertTrue(result.proved());
        assertEquals(1, result.width);
        assertEquals(1, result.pairs.size());
        assertArrayEquals(new int[]{201, 301}, result.pairs.get(0));
    }

    @Test
    public void latestLogicalResultSnapshotsNeedNoSerializerRead() {
        List<Map<String, Object>> producer = Arrays.asList(
                snapshot(11, 11, 100, 2, 0, 901),
                snapshot(12, 11, 100, 2, 1, 902),
                snapshot(16, 15, 100, 2, 0, 201),
                snapshot(17, 15, 100, 2, 1, 202),
                access("ARRAY_WRITE", 18, 100, 1, 203));
        List<Map<String, Object>> consumer = Arrays.asList(
                snapshot(21, 20, 110, 2, 0, 301),
                snapshot(22, 20, 110, 2, 1, 302));

        RuntimeSelectedRegionFinalizer.ArrayElementProjection result =
                RuntimeSelectedRegionFinalizer
                        .exactDeclaredArrayElementPairs(
                                producer, 100, consumer, 110,
                                10, 20, 19, 30);

        assertTrue(result.proved());
        assertEquals(2, result.width);
        assertArrayEquals(new int[]{201, 301}, result.pairs.get(0));
        assertArrayEquals(new int[]{203, 302}, result.pairs.get(1));
    }

    @Test
    public void declaredCarrierStartsOnlyFromExactResponseRoots() {
        Map<String, Object> exact = new LinkedHashMap<>();
        exact.put("callsiteAuthority",
                "EXACT_RUNTIME_PROTOCOL_CALLSITE_RESULT_V1");
        exact.put("producerResultObjectId", 500);
        exact.put("callerResultObjectId", 600);
        assertArrayEquals(new int[]{500, 600},
                RuntimeSelectedRegionFinalizer
                        .exactDeclaredCarrierRootPair(exact));

        exact.remove("callsiteAuthority");
        assertNull(RuntimeSelectedRegionFinalizer
                .exactDeclaredCarrierRootPair(exact));
        exact.put("callsiteAuthority",
                "EXACT_RUNTIME_PROTOCOL_CALLSITE_RESULT_V1");
        exact.remove("callerResultObjectId");
        assertNull(RuntimeSelectedRegionFinalizer
                .exactDeclaredCarrierRootPair(exact));
    }

    private static Map<String, Object> access(
            String kind, long event, int array, int index, int element) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("kind", kind);
        result.put("eventSeq", event);
        result.put("arrayObjectId", array);
        result.put("arrayIndex", index);
        result.put("elementObjectId", element);
        result.put("authority",
                "EXACT_RUNTIME_REFERENCE_ARRAY_ELEMENT_V1");
        return result;
    }

    private static Map<String, Object> snapshot(
            long event, long boundary, int array, int length,
            int index, int element) {
        Map<String, Object> result = access("ARRAY_SNAPSHOT", event,
                array, index, element);
        result.put("snapshotBoundarySeq", boundary);
        result.put("arrayLength", length);
        result.put("authority",
                "EXACT_RUNTIME_REFERENCE_ARRAY_SNAPSHOT_V1");
        return result;
    }
}
