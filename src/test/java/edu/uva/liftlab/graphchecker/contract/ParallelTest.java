package edu.uva.liftlab.graphchecker.contract;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * Independent items on every core, their results in the items' order: what
 * is made of them is what one thread made of them in turn, byte for byte
 * (the planner's keys and rows, PIPELINE §7.9).
 */
public class ParallelTest {
    /** As a planner's JVM computes, on more cores than one. */
    @Before
    public void manyCores() {
        Parallel.width(8);
    }

    @After
    public void oneCore() {
        Parallel.width(1);
    }

    /** Results in the items' order however long each took; the first
     *  failure in the items' order is the one thrown. */
    @Test
    public void mapKeepsTheItemsOrder() throws IOException {
        List<Integer> items = new ArrayList<Integer>();
        for (int at = 0; at < 2000; at++) items.add(at);
        List<String> done = Parallel.map(items, item -> {
            if (item % 7 == 0) Thread.yield();
            return "#" + item;
        });
        for (int at = 0; at < items.size(); at++) {
            assertEquals("#" + at, done.get(at));
        }
        try {
            Parallel.map(items, item -> {
                if (item >= 5) throw new IOException("item " + item);
                return item;
            });
            fail("a failing item fails the map");
        } catch (IOException failed) {
            assertEquals("item 5", failed.getMessage());
        }
    }
}
