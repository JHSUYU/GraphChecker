package edu.uva.liftlab.graphchecker.contract;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

public class ParallelTest {
    @Before
    public void manyCores() {
        Parallel.width(8);
    }

    @After
    public void oneCore() {
        Parallel.width(1);
    }

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
