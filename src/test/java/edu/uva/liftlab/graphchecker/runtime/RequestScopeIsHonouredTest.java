package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * A thread inside the workload's own request scope carries it.
 *
 * <p>The workload opens the scope itself --
 * {@code CausynthMessagePropagation.beginRequest(nnc, "refresh-block-keys")}
 * in bug2, {@code beginRequestIfRegistered(dn.getDatanodeId(), "heartbeat")}
 * in the DataNode -- and the same call runs in the recording and in the
 * replay. Everything the send then needs hangs off it: the outbound envelope
 * is active only when the thread carries a source, a request key and a
 * request api ({@code outboundHeader}), and the activation's attribution is
 * that same source ({@code activationSource}'s ambient arm). One scope, two
 * consumers, and this pins both against the one implementation.</p>
 */
public class RequestScopeIsHonouredTest {
    private static final String SPS = "hdfs-17899/sps";

    @After
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
    }

    /** The envelope is active and the activation is that source's. */
    @Test
    public void aThreadInsideARequestScopeCarriesItsSource() {
        RuntimeTraceContext.resetForTests();
        Object nnc = new Object();
        RuntimeTraceContext.registerSource(nnc,
                new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));

        long request = RuntimeTraceContext.beginRequest(nnc,
                "refresh-block-keys");
        try {
            assertNotNull("the thread carries the source",
                    RuntimeTraceContext.currentSource());
            assertEquals(SPS + "#epoch0",
                    RuntimeTraceContext.currentSource().key());
            // What Client$Connection.sendRpcRequest asks for: an active
            // outbound envelope.  It refuses without source + request flow,
            // and that refusal is what leaves causynth.active() false and
            // the fault marker behind its short circuit unminted.
            String header = RuntimeTraceContext.outboundHeader(nnc);
            assertTrue(header, header.startsWith("1|"));
            assertEquals("source, request key and api, all present",
                    8, header.split("\\|", -1).length);
            // And the activation that runs here is that source's, by the
            // ambient arm of the one attribution function.
            assertEquals(SPS + "#epoch0",
                    RuntimeTraceContext.activationSource(null).key());
        } finally {
            RuntimeTraceContext.endRequest(request);
        }

        // Outside it again: no envelope, and nothing attributed.
        assertEquals("the unregistered source, as the planner counts it",
                RuntimeTraceContext.UNREGISTERED_SOURCE.key(),
                RuntimeTraceContext.activationSource(null).key());
    }

    /**
     * A thread started inside the scope inherits it; one started before it
     * does not.
     *
     * <p>{@code RuntimeTraceContext}'s state is an
     * {@link InheritableThreadLocal}, which is how work handed to a thread
     * the workload creates inside its own request keeps that request's
     * node.  It also means the moment a thread is created decides what it
     * carries, which is worth pinning: an executor thread created once, at
     * cluster start, carries nothing however many requests later run on
     * it.</p>
     */
    @Test
    public void aRequestScopeIsInheritedByThreadsStartedInsideIt()
            throws Exception {
        RuntimeTraceContext.resetForTests();
        Object nnc = new Object();
        RuntimeTraceContext.registerSource(nnc,
                new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));
        long request = RuntimeTraceContext.beginRequest(nnc,
                "refresh-block-keys");
        try {
            final String[] inside = new String[1];
            Thread started = new Thread(() -> inside[0] =
                    RuntimeTraceContext.activationSource(null).key(),
                    "inside");
            started.start();
            started.join();
            assertEquals("a thread started inside the scope inherits it",
                    SPS + "#epoch0", inside[0]);
        } finally {
            RuntimeTraceContext.endRequest(request);
        }
    }

    /** A thread that existed before the scope carries nothing. */
    @Test
    public void aThreadOlderThanTheScopeCarriesNothing() throws Exception {
        RuntimeTraceContext.resetForTests();
        Object nnc = new Object();
        RuntimeTraceContext.registerSource(nnc,
                new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));

        final java.util.concurrent.CountDownLatch open =
                new java.util.concurrent.CountDownLatch(1);
        final java.util.concurrent.CountDownLatch read =
                new java.util.concurrent.CountDownLatch(1);
        final String[] seen = new String[1];
        Thread older = new Thread(() -> {
            try {
                open.await();
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
                return;
            }
            seen[0] = RuntimeTraceContext.activationSource(null).key();
            read.countDown();
        }, "older");
        older.start();

        long request = RuntimeTraceContext.beginRequest(nnc,
                "refresh-block-keys");
        open.countDown();
        read.await();
        RuntimeTraceContext.endRequest(request);

        assertEquals("the send runs on a thread the scope never reached",
                RuntimeTraceContext.UNREGISTERED_SOURCE.key(), seen[0]);
    }
}
