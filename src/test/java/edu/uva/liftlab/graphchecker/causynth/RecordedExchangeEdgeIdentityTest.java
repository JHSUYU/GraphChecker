package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.lang.reflect.Method;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * What names a recorded exchange edge across two recordings of one workload.
 *
 * <p>An {@code RPC.} producer edge and the {@code CTRL.} request-control edge
 * that depends on it used to be named from the wire transaction the exchange
 * ran on: Hadoop's IPC client id and call number
 * ({@code hadoop-ipc-f76d5ada...-21}) or a SASL negotiation uuid
 * ({@code hdfs-sasl-e21aa975-...}).  The workload mints those fresh in every
 * run, so two recordings of hdfs-17899/bug3 published a different
 * {@code RPC.}/{@code CTRL.} id for the same exchange, and the 25 plan rows
 * that bind those edges differed by name alone.</p>
 *
 * <p>The transaction stays on the edge as recorded transport evidence.  It is
 * no longer part of the edge's name: the producing and consuming occurrence,
 * the port, the direction and an ordinal counted over that tuple say which
 * exchange this is in terms the next recording reproduces.</p>
 */
public class RecordedExchangeEdgeIdentityTest {
    private static final String SITE =
            "hdfs-17899/nn0#epoch0/region/REGION.a#1\n"
                    + "hdfs-17899/source-dn#epoch0/region/REGION.b#1\n"
                    + "REGION.b.in.port\nREQUEST";
    private static final String OTHER_SITE =
            "hdfs-17899/nn0#epoch0/region/REGION.a#2\n"
                    + "hdfs-17899/source-dn#epoch0/region/REGION.b#1\n"
                    + "REGION.b.in.port\nREQUEST";

    /** The one transaction of one exchange site is exchange number one. */
    @Test
    public void twoRecordingsNumberOneExchangeAlike() {
        assertNotEquals("the wire transactions of two recordings are "
                        + "expected to differ",
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0",
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0");

        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                new LinkedHashMap<>(), SITE,
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0"));
        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                new LinkedHashMap<>(), SITE,
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0"));
    }

    /**
     * A retry is a second exchange of the same site, in both recordings.
     *
     * <p>The ordinal is what keeps two attempts on one port apart now that
     * their transaction ids no longer do it, so it has to count per site and
     * answer stably when one transaction is offered again.</p>
     */
    @Test
    public void retriesAreNumberedInOrderInBothRecordings() {
        Map<String, Map<String, Integer>> first = new LinkedHashMap<>();
        Map<String, Map<String, Integer>> second = new LinkedHashMap<>();

        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                first, SITE, "hadoop-ipc-aaaa-1\n0"));
        assertEquals(2, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                first, SITE, "hadoop-ipc-aaaa-2\n0"));
        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                first, SITE, "hadoop-ipc-aaaa-1\n0"));

        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                second, SITE, "hdfs-sasl-zzzz\n0"));
        assertEquals(2, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                second, SITE, "hdfs-sasl-yyyy\n0"));
        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                second, SITE, "hdfs-sasl-zzzz\n0"));
    }

    /** Each exchange site counts its own exchanges. */
    @Test
    public void ordinalsAreCountedPerExchangeSite() {
        Map<String, Map<String, Integer>> ordinals = new LinkedHashMap<>();

        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                ordinals, SITE, "t1"));
        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                ordinals, OTHER_SITE, "t2"));
        assertEquals(2, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                ordinals, SITE, "t3"));
    }

    /**
     * A request-control edge is named by the response edge, not the wire.
     *
     * <p>The response edge already names the exchange from content, and it
     * names it more exactly than the transaction does, because each retry of
     * one logical request has its own response edge.</p>
     */
    @Test
    public void requestControlEdgeIdIgnoresTheWireTransaction() throws Exception {
        String first = controlEdgeId(
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0");
        String second = controlEdgeId(
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0");

        assertEquals("two recordings of one request fault must publish one "
                + "control edge name", first, second);
    }

    /** Two response edges are still two control edges. */
    @Test
    public void requestControlEdgeIdStillFollowsTheResponseEdge()
            throws Exception {
        assertNotEquals(controlEdgeId("t", "RPC.first"),
                controlEdgeId("t", "RPC.second"));
    }

    private static String controlEdgeId(String transaction) throws Exception {
        return controlEdgeId(transaction, "RPC.response");
    }

    @SuppressWarnings("unchecked")
    private static String controlEdgeId(String transaction,
                                        String responseEdgeId)
            throws Exception {
        Method edge = RuntimeSelectedRegionFinalizer.class
                .getDeclaredMethod("requestFaultControlEdge", Map.class,
                        Map.class, Map.class, Map.class, Map.class,
                        String.class, String.class, long.class, long.class,
                        long.class, long.class, long.class);
        edge.setAccessible(true);
        Map<String, Object> result = (Map<String, Object>) edge.invoke(null,
                row("occurrenceId", "hdfs-17899/nn0#epoch0/region/REGION.f#1",
                        "regionId", "REGION.f", "rootCallId", 11L),
                row("occurrenceId", "hdfs-17899/nn0#epoch0/region/REGION.c#1",
                        "regionId", "REGION.c", "rootCallId", 12L),
                row("portId", "REGION.c.in.port", "symbolicName", "S1"),
                row("edgeId", "RPC.request", "requestKey", "rk",
                        "attemptId", "a1"),
                row("edgeId", responseEdgeId),
                transaction, "hdfs-17899/nn0#epoch0",
                1L, 2L, 3L, 4L, 5L);
        return String.valueOf(result.get("edgeId"));
    }

    private static Map<String, Object> row(Object... fields) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < fields.length; index += 2) {
            result.put((String) fields[index], fields[index + 1]);
        }
        return result;
    }
}
