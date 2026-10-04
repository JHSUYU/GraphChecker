package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.CopyOnWriteArrayList;

import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * What a draw is keyed by (SYMBOL-SCOPE §4.5): its endpoint in an occurrence
 * with a context; anywhere else its node, handoffs, site and count under
 * that key in this window, so draws a Lost context makes stay apart.
 */
public class RandomsTest {
    private static final String SITE =
            "<o.a.h.hdfs.server.datanode.DataNode: java.lang.String"
                    + " generateUuid()>#u3";

    @Before
    @After
    public void freshRun() {
        Identity.resetForTests();
        RuntimeTraceContext.resetForTests();
        RecordingWindow.reset();
        Randoms.resetForTests();
    }

    @Test
    public void aDrawWithNoContextOfItsOwnIsKeyedByItsCountInItsWindow() {
        String unregistered = "#" + RuntimeTraceContext.nodeHere() + "|#"
                + SITE + "#";
        assertEquals("before the window", Arrays.asList("0" + unregistered
                + "0", "0" + unregistered + "1"), Arrays.asList(
                Randoms.key(SITE), Randoms.key(SITE)));
        RecordingWindow.open();
        assertEquals("a Lost context inside the window, counted afresh",
                "1" + unregistered + "0", Randoms.key(SITE));
        RecordingWindow.open();
        assertEquals("every window counts from 0", "2" + unregistered + "0",
                Randoms.key(SITE));
    }

    /** Each node's thread counts its own draws, in its own program order,
     *  however the two threads' draws interleave. */
    @Test
    public void lostDrawsOfTwoNodesCountApart() throws InterruptedException {
        RecordingWindow.open();
        List<String> second = new CopyOnWriteArrayList<>();
        Thread other = new Thread(() -> second.addAll(drawsOn("t/dn1", 1)));
        List<String> first = drawsOn("t/dn0", 1);
        other.start();
        other.join();
        first.addAll(drawsOn("t/dn0", 1));
        assertEquals(Arrays.asList("1#t/dn0#epoch0|#" + SITE + "#0",
                "1#t/dn0#epoch0|#" + SITE + "#1"), first);
        assertEquals(Arrays.asList("1#t/dn1#epoch0|#" + SITE + "#0"), second);
    }

    /** {@code draws} keys of the running thread inside a startup of node
     *  {@code id}. */
    private static List<String> drawsOn(String id, int draws) {
        long startup = RuntimeTraceContext.beginNodeStartup(new SourceRef(
                "CLUSTER_NODE", "DATANODE", id, 0L));
        try {
            List<String> keys = new java.util.ArrayList<>();
            for (int i = 0; i < draws; i++) {
                keys.add(Randoms.key(SITE));
            }
            return keys;
        } finally {
            RuntimeTraceContext.endNodeStartup(startup);
        }
    }

    /** hdfs-adhoc-01, round HS1: DataNodes started inside the window under
     *  no hop drew one UUID and refused each other's registrations. */
    @Test
    public void unnamedThreadsInsideTheWindowDrawDistinctUuids()
            throws InterruptedException {
        RecordingWindow.open();
        List<UUID> drawn = new CopyOnWriteArrayList<>();
        Thread[] dataNodes = new Thread[3];
        for (int i = 0; i < dataNodes.length; i++) {
            dataNodes[i] = new Thread(
                    () -> drawn.add(Randoms.randomUUID(SITE)));
            dataNodes[i].start();
        }
        for (Thread dataNode : dataNodes) {
            dataNode.join();
        }
        assertEquals(3, new HashSet<>(drawn).size());
    }

    @Test
    public void aDrawInAnOccurrenceWithAContextIsKeyedByItsEndpoint() {
        RecordingWindow.open();
        long turn = Lineage.pushRoot("hdfs/dn0", Role.of("BP_SERVICE_ACTOR"),
                "");
        String first = Randoms.key(SITE);
        String second = Randoms.key(SITE);
        Lineage.pop(turn);
        assertNotEquals("two draws of one site in one occurrence", first,
                second);
        assertFalse("an endpoint, not a count", first.contains(SITE));

        Identity.resetForTests();
        RuntimeTraceContext.resetForTests();
        RecordingWindow.reset();
        RecordingWindow.open();
        turn = Lineage.pushRoot("hdfs/dn0", Role.of("BP_SERVICE_ACTOR"), "");
        assertEquals("the same inputs, the same key, in another run", first,
                Randoms.key(SITE));
        Lineage.pop(turn);
    }

    /** Neighbouring counts of one site start unlike generators: unmixed,
     *  every one of these draws picks the same of four. */
    @Test
    public void neighbouringKeysSeedUnlikeGenerators() {
        Set<Integer> picked = new HashSet<>();
        for (int count = 0; count < 8; count++) {
            picked.add(new Random(Randoms.seed("1#" + SITE + "#" + count))
                    .nextInt(4));
        }
        assertNotEquals(1, picked.size());
    }

    /**
     * {@code ThreadLocalRandom.current()}'s stand-in draws, in a fresh run,
     * what the first drew; its bounded draws keep ThreadLocalRandom's
     * contract: in [origin, bound), and a bad bound refused.
     */
    @Test
    public void aThreadLocalDrawRepeatsInEveryPassWithinItsBounds() {
        List<Long> passes = new java.util.ArrayList<>();
        for (int pass = 0; pass < 2; pass++) {
            freshRun();
            Random drawn = Randoms.current(SITE);
            passes.add(Randoms.nextLong(drawn, 1L << 40));
        }
        assertEquals(passes.get(0), passes.get(1));
        Random drawn = Randoms.current(SITE);
        for (int i = 0; i < 100; i++) {
            int one = Randoms.nextInt(drawn, -3, 4);
            long other = Randoms.nextLong(drawn, Long.MIN_VALUE, -5L);
            double third = Randoms.nextDouble(drawn, 0.5);
            assertTrue(one >= -3 && one < 4 && other < -5L && third >= 0.0
                    && third < 0.5);
        }
        Runnable[] refused = {() -> Randoms.nextInt(drawn, 4, 4),
                () -> Randoms.nextLong(drawn, 0L),
                () -> Randoms.nextDouble(drawn, 1.0, -1.0)};
        for (Runnable bad : refused) {
            try {
                bad.run();
                fail("a bad bound is refused");
            } catch (IllegalArgumentException expected) {
            }
        }
    }
}
