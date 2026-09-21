package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.util.Arrays;
import java.util.Collections;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.Test;

/**
 * The two class monitors of the WIRE stores are taken in ONE order.
 *
 * <p>{@link Interactions} then {@link InteractionRefusals}, never the
 * reverse.  On 11741 campaign #4 the reverse edge existed --
 * {@code InteractionRefusals.filedProducers} was {@code synchronized} and
 * delegated to {@code Interactions.filedProducers} -- and the focused replay
 * of one obligation hung forever: the main thread was rendering a refusal
 * (holding the refusals monitor, waiting for the interactions one) while a
 * DataNode heartbeat was inside {@code Interactions.sharedProducer} (holding
 * the interactions monitor, waiting for the refusals one).  The JVM named it
 * itself, "Found one Java-level deadlock", and the wave that replay belonged
 * to stayed open until the campaign's own wall clock ran out.</p>
 *
 * <p>This drives both paths concurrently and asks the VM the same question
 * that dump answered.  It is a race, so it is not a proof that no order
 * violation exists; with the {@code synchronized} put back on
 * {@code InteractionRefusals.filedProducers} it hangs within the first
 * thousands of iterations, which is what it is here to catch.</p>
 */
public class InteractionsLockOrderTest {
    /** How many producers the stores hold while the two paths run. */
    private static final int FILED = 2000;

    /**
     * How long the two paths run against each other.
     *
     * <p>Both loop until this elapses rather than for a fixed count: the
     * window one holds a monitor in is microseconds wide, so what catches an
     * order violation is overlap, and two counts tuned to different per-
     * iteration costs stop overlapping.</p>
     */
    private static final long OVERLAP_MS = 2000L;

    /** What a finished thread is given after the overlap ends, at most. */
    private static final long JOIN_MS = 4000L;

    @Test
    public void theTwoStoresAreLockedInOneOrder() throws Exception {
        Interactions.resetForTests();
        // A filled store: both paths then walk a real list while they hold a
        // monitor, which is the window the two orders collide in.
        String scanned = "";
        for (int k = 0; k < FILED; k++) {
            Endpoint producer = producer(k);
            Interactions.sent("RPC", "correlation-" + k, "req", producer);
            scanned = producer.id();
        }

        final String lookup = scanned;
        final CountDownLatch ready = new CountDownLatch(2);
        final CountDownLatch go = new CountDownLatch(1);
        final AtomicInteger sending = new AtomicInteger();
        final AtomicInteger rendering = new AtomicInteger();
        final AtomicReference<Throwable> failure =
                new AtomicReference<Throwable>();

        // The delivery path: files a message and asks whether this producer
        // id already named another one.  Holds Interactions, takes
        // InteractionRefusals.
        Thread sender = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    ready.countDown();
                    go.await();
                    long end = System.nanoTime() + OVERLAP_MS * 1000000L;
                    for (int k = 0; System.nanoTime() < end; k++) {
                        Endpoint producer = producer(FILED + k);
                        Interactions.sent("RPC", "live-" + k, "req", producer);
                        Interactions.sharedProducer("RPC", "live-" + k, "req",
                                producer);
                        sending.incrementAndGet();
                    }
                } catch (Throwable thrown) {
                    failure.compareAndSet(null, thrown);
                }
            }
        }, "interactions-sender");

        // The refusal path: resolves an anchor's components by walking the
        // filed producers.  Takes Interactions from inside
        // InteractionRefusals -- and must own nothing of its own when it
        // does.
        Thread refuser = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    ready.countDown();
                    go.await();
                    long end = System.nanoTime() + OVERLAP_MS * 1000000L;
                    while (System.nanoTime() < end) {
                        InteractionRefusals.endpoint(lookup);
                        InteractionRefusals.components(lookup);
                        rendering.incrementAndGet();
                    }
                } catch (Throwable thrown) {
                    failure.compareAndSet(null, thrown);
                }
            }
        }, "interactions-refuser");

        // Daemons: a test that does deadlock fails on its own clock instead
        // of holding the surefire JVM open behind it.
        sender.setDaemon(true);
        refuser.setDaemon(true);
        sender.start();
        refuser.start();
        ready.await();
        long deadline = System.currentTimeMillis() + OVERLAP_MS + JOIN_MS;
        go.countDown();
        sender.join(Math.max(1L, deadline - System.currentTimeMillis()));
        refuser.join(Math.max(1L, deadline - System.currentTimeMillis()));

        // The VM's own answer, which is the one the thread dump gave.
        ThreadMXBean threads = ManagementFactory.getThreadMXBean();
        long[] deadlocked = threads.findDeadlockedThreads();
        assertNull("the WIRE stores deadlocked: "
                + render(threads, deadlocked), deadlocked);
        if (failure.get() != null) {
            throw new AssertionError("a lock-order path threw",
                    failure.get());
        }
        assertTrue("the delivery path never left its loop: "
                        + sending.get() + " iteration(s) in " + OVERLAP_MS
                        + "ms of overlap and " + JOIN_MS + "ms of join",
                !sender.isAlive());
        assertTrue("the refusal path never left its loop: "
                        + rendering.get() + " iteration(s) in " + OVERLAP_MS
                        + "ms of overlap and " + JOIN_MS + "ms of join",
                !refuser.isAlive());
        // Both paths actually ran: a test that raced nothing proves nothing.
        assertTrue("the delivery path ran no iteration", sending.get() > 0);
        assertTrue("the refusal path ran no iteration", rendering.get() > 0);

        Interactions.resetForTests();
    }

    /** The threads the VM says are deadlocked, and where each one stands. */
    private static String render(ThreadMXBean threads, long[] deadlocked) {
        if (deadlocked == null) return "";
        StringBuilder rendered = new StringBuilder();
        for (ThreadInfo info : threads.getThreadInfo(deadlocked, 4)) {
            if (info == null) continue;
            rendered.append('\n').append(info.getThreadName())
                    .append(" blocked on ").append(info.getLockName())
                    .append(" held by ").append(info.getLockOwnerName())
                    .append(' ').append(Arrays.toString(info.getStackTrace()));
        }
        return rendered.toString();
    }

    /** One producer endpoint, built the way the runtime builds one. */
    private static Endpoint producer(int k) {
        OccurrenceAddress occurrence = OccurrenceAddress.of(
                NodeId.of("dn" + (k % 4), 0), "REGION.wire",
                CausalContext.of(Role.CLIENT, "", k + 1),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of("BPServiceActor#offerService", k))));
        return Endpoint.of(occurrence, "XCH.wire.req.block-key-id",
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of("Client#sendRpcRequest", k))), 0);
    }
}
