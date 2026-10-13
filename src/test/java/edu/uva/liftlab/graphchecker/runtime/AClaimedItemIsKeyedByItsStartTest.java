package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ActivationRow.ClaimKind;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.SynchronousQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
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
            Identity.startWork(ADD, item, null);
            RuntimeTraceContext.endRequest(request);
        }
        final String[] keys = new String[3];
        Thread consumer = new Thread(() -> {
            keys[2] = Identity.claimedStart();
            for (int item = 0; item < 2; item++) {
                Identity.claimItem(items[item]);
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
    /**
     * A claim states what its work is: a task an executor hands to a worker
     * of its own (a ThreadPoolExecutor whose queue has no room: an
     * Overseer's SynchronousQueue), a task a worker takes off its
     * executor's queue (a single-thread executor's), a queue item, or no
     * claim.  Only the first is held where it runs (Confirmation#submitter).
     */
    @Test
    public void aClaimStatesItsExecutorsHandOff() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        ThreadPoolExecutor handOff = new ThreadPoolExecutor(0, 4, 1L,
                TimeUnit.SECONDS, new SynchronousQueue<Runnable>());
        ThreadPoolExecutor single = new ThreadPoolExecutor(1, 1, 1L,
                TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());
        Object[][] table = {
                // submitted to, claimed as an item?, its claim's kind
                {handOff, false, ClaimKind.HANDOFF_TASK},
                {single, false, ClaimKind.QUEUED_TASK},
                {null, false, ClaimKind.QUEUED_TASK},
                {new Object(), true, ClaimKind.ITEM},
        };
        try {
            for (Object[] row : table) {
                Object work = new Object();
                long request = RuntimeTraceContext.beginRequest(node,
                        "submit");
                Identity.startWork(ADD, work, row[0]);
                RuntimeTraceContext.endRequest(request);
                final ClaimKind[] kinds = new ClaimKind[2];
                final boolean item = (Boolean) row[1];
                Thread worker = new Thread(() -> {
                    kinds[0] = Identity.claimKind();
                    if (item) {
                        Identity.claimItem(work);
                        kinds[1] = Identity.claimKind();
                    } else {
                        long claim = Identity.claimStart(work);
                        kinds[1] = Identity.claimKind();
                        Identity.endClaim(claim);
                    }
                });
                worker.start();
                worker.join(5000L);
                assertEquals("no claim yet", ClaimKind.NONE, kinds[0]);
                assertEquals(String.valueOf(row[0]), row[2], kinds[1]);
            }
        } finally {
            handOff.shutdownNow();
            single.shutdownNow();
        }
    }
}
