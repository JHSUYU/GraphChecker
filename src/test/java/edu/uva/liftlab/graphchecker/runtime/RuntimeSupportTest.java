package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertFalse;
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
import java.security.Security;
import java.util.Arrays;
import java.util.Collections;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

@RunWith(FreshStatics.class)
public class RuntimeSupportTest {
    @Before
    @After
    public void reset() {
        Security.removeProvider("CausynthReplayKeys");
    }

    @Test
    public void theTwoStoresAreLockedInOneOrder() throws Exception {
        int filed = 2000;
        long overlapMs = 2000L;
        long joinMs = 4000L;
        String scanned = "";
        for (int k = 0; k < filed; k++) {
            Endpoint producer = producer(k);
            Interactions.sent("RPC", "correlation-" + k, "req", producer);
            scanned = producer.id();
        }
        String lookup = scanned;
        CountDownLatch ready = new CountDownLatch(2);
        CountDownLatch go = new CountDownLatch(1);
        AtomicInteger sending = new AtomicInteger();
        AtomicInteger rendering = new AtomicInteger();
        AtomicReference<Throwable> failure = new AtomicReference<>();
        Runnable[] paths = {() -> {
            long end = System.nanoTime() + overlapMs * 1000000L;
            for (int k = 0; System.nanoTime() < end; k++) {
                Endpoint producer = producer(filed + k);
                Interactions.sent("RPC", "live-" + k, "req", producer);
                Interactions.sharedProducer("RPC", "live-" + k, "req",
                        producer);
                sending.incrementAndGet();
            }
        }, () -> {
            long end = System.nanoTime() + overlapMs * 1000000L;
            while (System.nanoTime() < end) {
                InteractionRefusals.endpoint(lookup);
                InteractionRefusals.components(lookup);
                rendering.incrementAndGet();
            }
        }};
        Thread[] threads = new Thread[paths.length];
        for (int at = 0; at < paths.length; at++) {
            Runnable path = paths[at];
            threads[at] = new Thread(() -> {
                try {
                    ready.countDown();
                    go.await();
                    path.run();
                } catch (Throwable thrown) {
                    failure.compareAndSet(null, thrown);
                }
            }, "interactions-" + at);
            threads[at].setDaemon(true);
            threads[at].start();
        }
        ready.await();
        long deadline = System.currentTimeMillis() + overlapMs + joinMs;
        go.countDown();
        for (Thread thread : threads) {
            thread.join(Math.max(1L, deadline - System.currentTimeMillis()));
        }
        ThreadMXBean beans = ManagementFactory.getThreadMXBean();
        long[] deadlocked = beans.findDeadlockedThreads();
        StringBuilder where = new StringBuilder();
        if (deadlocked != null) {
            for (ThreadInfo info : beans.getThreadInfo(deadlocked, 4)) {
                if (info == null) continue;
                where.append('\n').append(info.getThreadName())
                        .append(" blocked on ").append(info.getLockName())
                        .append(" held by ").append(info.getLockOwnerName())
                        .append(' ').append(Arrays.toString(
                        info.getStackTrace()));
            }
        }
        assertNull("the WIRE stores deadlocked: " + where, deadlocked);
        if (failure.get() != null) {
            throw new AssertionError("a lock-order path threw", failure.get());
        }
        for (Thread thread : threads) {
            assertFalse(thread.getName() + " never left its loop: "
                    + sending.get() + "/" + rendering.get() + " iterations",
                    thread.isAlive());
        }
        assertTrue("both paths ran: a race of nothing proves nothing",
                sending.get() > 0 && rendering.get() > 0);
    }

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
