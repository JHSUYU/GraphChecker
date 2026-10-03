package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

/**
 * A consumer thread that claims one queue item after another runs them in
 * the order their starters queued them: each item's work is keyed by its
 * claimed start, not by the thread (the program order {@code
 * ActivationRow#threadKey} states), and work under no claim keeps none.
 */
public class AClaimedItemIsKeyedByItsStartTest {
    private static final SourceRef NODE =
            new SourceRef("CLUSTER_NODE", "ZK_SERVER", "t/server0", 0L);
    private static final String ADD =
            "<a.Sync: void processRequest(a.Request)>#u4";

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        Identity.resetForTests();
    }

    @Test
    public void twoItemsOnOneConsumerAreTwoProgramOrders() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        final Object[] items = {new Object(), new Object()};
        for (Object item : items) {
            // Two clients' requests, each queued under its own scope.
            long request = RuntimeTraceContext.beginRequest(node, "getData");
            Identity.startWork(ADD, item);
            RuntimeTraceContext.endRequest(request);
        }
        final String[] keys = new String[3];
        Thread consumer = new Thread(() -> {
            keys[2] = Identity.claimedStart();
            for (int item = 0; item < 2; item++) {
                Identity.claimStart(items[item]);
                keys[item] = Identity.claimedStart();
            }
        });
        consumer.start();
        consumer.join(5000L);
        assertNull("no claim, no start: the thread orders it", keys[2]);
        assertNotNull(keys[0]);
        assertNotEquals("each item is its own program order", keys[0],
                keys[1]);
    }
}
