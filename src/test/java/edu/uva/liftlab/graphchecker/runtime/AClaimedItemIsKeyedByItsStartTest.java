package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.ActivationRow.ClaimKind;
import java.util.Collections;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ScheduledThreadPoolExecutor;
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
     * of its own (a ThreadPoolExecutor on a SynchronousQueue: an Overseer's
     * pool), a task a worker takes off its executor's queue (a
     * single-thread executor's, a full bounded queue's, any executor that
     * is no ThreadPoolExecutor), a task its starter runs itself (a
     * caller-runs rejection: queued, it runs inside the starter's work), a
     * queue item, or no claim.  Only the first is held where it runs
     * (Confirmation#submitter).
     */
    @Test
    public void aClaimStatesItsExecutorsHandOff() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        ThreadPoolExecutor handOff = new ThreadPoolExecutor(0, 4, 1L,
                TimeUnit.SECONDS, new SynchronousQueue<Runnable>());
        ThreadPoolExecutor single = new ThreadPoolExecutor(1, 1, 1L,
                TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());
        // No worker started: the queue stays full.
        ThreadPoolExecutor full = new ThreadPoolExecutor(1, 1, 1L,
                TimeUnit.SECONDS, new ArrayBlockingQueue<Runnable>(1));
        full.getQueue().add(() -> { });
        ExecutorService wrapped = Executors.newSingleThreadExecutor();
        ScheduledThreadPoolExecutor scheduled =
                new ScheduledThreadPoolExecutor(1);
        Object[][] table = {
                // submitted to, claimed as, its claim's kind
                {handOff, "task", ClaimKind.HANDOFF_TASK},
                {handOff, "task run here", ClaimKind.QUEUED_TASK},
                {single, "task", ClaimKind.QUEUED_TASK},
                {full, "task", ClaimKind.QUEUED_TASK},
                {wrapped, "task", ClaimKind.QUEUED_TASK},
                {ForkJoinPool.commonPool(), "task", ClaimKind.QUEUED_TASK},
                {scheduled, "task", ClaimKind.QUEUED_TASK},
                {null, "task", ClaimKind.QUEUED_TASK},
                {new Object(), "item", ClaimKind.ITEM},
        };
        try {
            for (Object[] row : table) {
                Object work = new Object();
                final ClaimKind[] kinds = new ClaimKind[2];
                final String as = (String) row[1];
                Runnable claim = () -> {
                    kinds[0] = Identity.claimKind();
                    if ("item".equals(as)) {
                        Identity.claimItem(work);
                        kinds[1] = Identity.claimKind();
                    } else {
                        long claimed = Identity.claimStart(work);
                        kinds[1] = Identity.claimKind();
                        Identity.endClaim(claimed);
                    }
                };
                long request = RuntimeTraceContext.beginRequest(node,
                        "submit");
                Identity.startWork(ADD, work, row[0]);
                if ("task run here".equals(as)) claim.run();
                RuntimeTraceContext.endRequest(request);
                if (!"task run here".equals(as)) {
                    Thread worker = new Thread(claim);
                    worker.start();
                    worker.join(5000L);
                }
                assertEquals("no claim yet", ClaimKind.NONE, kinds[0]);
                assertEquals(row[0] + " " + as, row[2], kinds[1]);
            }
            assertEquals("no task took other work", Collections.emptySet(),
                    Identity.servingTasks());
        } finally {
            handOff.shutdownNow();
            single.shutdownNow();
            full.shutdownNow();
            wrapped.shutdownNow();
            scheduled.shutdownNow();
        }
    }

    /**
     * A hand-off task that takes queue items on its thread -- a
     * ConcurrentUpdate client's Runner polling its update queue, the take
     * inside a callee that returns -- serves a queue: its rows still state
     * HANDOFF_TASK, written at entry, and the run states it at its close
     * (Identity#servingTasks), for its whole life.  A task its starter runs
     * itself takes nothing another thread started.
     */
    @Test
    public void aHandOffTaskThatTakesItemsServesAQueue() throws Exception {
        Object node = new Object();
        RuntimeTraceContext.registerSource(node, NODE);
        ThreadPoolExecutor handOff = new ThreadPoolExecutor(0, 4, 1L,
                TimeUnit.SECONDS, new SynchronousQueue<Runnable>());
        try {
            Object runner = new Object();
            Object quiet = new Object();
            Object[] updates = {new Object(), new Object()};
            long request = RuntimeTraceContext.beginRequest(node, "update");
            Identity.startWork(ADD, runner, handOff);
            Identity.startWork(ADD, quiet, handOff);
            for (Object update : updates) {
                Identity.startWork(ADD, update, new LinkedBlockingQueue<>());
            }
            RuntimeTraceContext.endRequest(request);
            final String[] keys = new String[2];
            final ClaimKind[] kinds = new ClaimKind[2];
            Thread worker = new Thread(() -> {
                long claimed = Identity.claimStart(runner);
                keys[0] = Identity.claimedStart();
                for (Object update : updates) {
                    // CustomBlockingQueue.poll: the take, in a callee
                    long poll = Identity.enterFrame(
                            "<a.Queue: java.lang.Object poll()>#u1", null);
                    Identity.claimItem(update);
                    Identity.exitFrame(poll);
                }
                kinds[0] = Identity.claimKind();
                Identity.endClaim(claimed);
                // A hand-off task of its own that takes nothing.
                claimed = Identity.claimStart(quiet);
                keys[1] = Identity.claimedStart();
                kinds[1] = Identity.claimKind();
                Identity.endClaim(claimed);
            });
            worker.start();
            worker.join(5000L);
            assertEquals("the row's kind is the entry's",
                    ClaimKind.HANDOFF_TASK, kinds[0]);
            assertEquals(ClaimKind.HANDOFF_TASK, kinds[1]);
            assertNotNull(keys[0]);
            assertEquals("the runner, not the quiet task",
                    Collections.singleton(keys[0]), Identity.servingTasks());
        } finally {
            handOff.shutdownNow();
        }
    }
}
