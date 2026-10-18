package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Arrays;
import java.util.List;
import java.util.Random;

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
