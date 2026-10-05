package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
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
 * What a draw is keyed by (SYMBOL-SCOPE §4.5): inside the window its schedule
 * context, site and count; before it its node, handoffs, site and count; the
 * counts restart at each window, and a region woven around a draw moves
 * nothing.
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
    public void aDrawIsKeyedByItsContextSiteAndCountInItsWindow() {
        String unregistered = "#" + RuntimeTraceContext.nodeHere() + "|#"
                + SITE + "#";
        assertEquals("before the window", Arrays.asList("0" + unregistered
                + "0", "0" + unregistered + "1"), Arrays.asList(
                Randoms.key(SITE), Randoms.key(SITE)));
        RecordingWindow.open();
        String context = ScheduleLog.contextOf(Identity.contextHere());
        assertEquals("inside the window, by its schedule context",
                "1#" + context + "#" + SITE + "#0", Randoms.key(SITE));
        RecordingWindow.open();
        assertEquals("every window counts from 0",
                "2#" + context + "#" + SITE + "#0", Randoms.key(SITE));
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
        String lost = "|" + Identity.contextHere().render() + "#" + SITE;
        assertEquals(Arrays.asList("1#t/dn0#epoch0" + lost + "#0",
                "1#t/dn0#epoch0" + lost + "#1"), first);
        assertEquals(Arrays.asList("1#t/dn1#epoch0" + lost + "#0"), second);
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

    /**
     * A draw's key is no occurrence's: a region a GROW weaves around the
     * draw site (IDENTITY §9: its occurrences and endpoints are new ids)
     * leaves the keys and the values drawn as they were, run after run.
     */
    @Test
    public void aRegionWovenAroundADrawMovesNoKeyAndNoValue() {
        List<List<Object>> runs = new java.util.ArrayList<>();
        for (boolean woven : new boolean[] {false, true}) {
            freshRun();
            RecordingWindow.open();
            long turn = Lineage.pushRoot("hdfs/dn0",
                    Role.of("BP_SERVICE_ACTOR"), "");
            if (woven) {
                Identity.occurrence(RuntimeTraceContext.nodeHere(),
                        "REGION.grown", true);
            }
            String first = Randoms.key(SITE);
            String second = Randoms.key(SITE);
            long drawn = Randoms.at(SITE).nextLong();
            if (woven) Identity.regionExit();
            Lineage.pop(turn);
            assertNotEquals("two draws of one site in one context", first,
                    second);
            runs.add(Arrays.asList(first, second, drawn));
        }
        assertTrue(runs.get(0).get(0).toString(),
                runs.get(0).get(0).toString().contains("Root:"));
        assertEquals("woven or not, the same keys and the same value",
                runs.get(0), runs.get(1));
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
     * A draw keyed by its site draws, in a fresh run, what the first drew;
     * the bounded draws keep ThreadLocalRandom's contract: in [origin,
     * bound), and a bad bound refused.
     */
    @Test
    public void aSiteKeyedDrawRepeatsInEveryPassWithinItsBounds() {
        List<Long> passes = new java.util.ArrayList<>();
        for (int pass = 0; pass < 2; pass++) {
            freshRun();
            Random drawn = Randoms.at(SITE);
            passes.add(Randoms.nextLong(drawn, 1L << 40));
        }
        assertEquals(passes.get(0), passes.get(1));
        Random drawn = Randoms.at(SITE);
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
