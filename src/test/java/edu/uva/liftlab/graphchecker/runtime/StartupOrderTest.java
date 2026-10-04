package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.RowCodec;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * A replay holds a node at a startup step to the order its recording's nodes
 * completed it (hdfs-adhoc-01/43: DataNodes registered in another order
 * placed every pipeline elsewhere); a node the order does not mark, or one
 * whose predecessor never comes, goes on.
 */
public class StartupOrderTest {
    @Before
    @After
    public void freshRun() {
        System.clearProperty(ScheduleLog.PREFIX_PROPERTY);
        System.clearProperty(ScheduleLog.TIMEOUT_PROPERTY);
        ScheduleLog.resetForTests();
        StartupOrder.resetForTests();
    }

    @Test
    public void aReplayTakesTheStepInItsRecordingsOrder() throws Exception {
        Path order = Files.createTempFile("startup", ".jsonl");
        RowCodec.writeJsonl(order, Arrays.asList(
                RowCodec.writeScheduleStartup("register", "dn1"),
                RowCodec.writeScheduleStartup("register", "dn0")));
        System.setProperty(ScheduleLog.PREFIX_PROPERTY, order.toString());
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "30000");
        final List<String> took =
                Collections.synchronizedList(new ArrayList<String>());
        Thread dn0 = new Thread(() -> take("dn0", took));
        dn0.start();
        Thread.sleep(200L);
        assertTrue("dn0 waits for dn1, marked before it", dn0.isAlive());
        take("dn1", took);
        dn0.join(5000L);
        assertEquals(Arrays.asList("dn1", "dn0"), took);

        StartupOrder.resetForTests();
        System.setProperty(ScheduleLog.TIMEOUT_PROPERTY, "300");
        long before = System.nanoTime();
        take("dn0", took);
        assertTrue("a predecessor that never comes holds one timeout",
                System.nanoTime() - before >= 250_000_000L);
        before = System.nanoTime();
        take("dn9", took);
        assertTrue("a node the order does not mark goes on",
                System.nanoTime() - before < 250_000_000L);
        Files.delete(order);
    }

    private static void take(String node, List<String> took) {
        String[] pass = StartupOrder.begin("register", node);
        took.add(node);
        StartupOrder.done(pass);
    }
}
