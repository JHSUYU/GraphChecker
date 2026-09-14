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

    /**
     * Work carries its own scope to the thread that performs it.
     *
     * <p>The point of the capture: Hadoop's {@code Client} builds a
     * {@code Call} on the caller's thread, inside the workload's request,
     * and writes it from a sender thread its connection pool created once,
     * before that request existed. The scope travels with the call, so the
     * send names the node and request the work belongs to however old the
     * thread is.</p>
     */
    @Test
    public void workCarriesItsScopeToThePoolThreadThatWritesIt()
            throws Exception {
        RuntimeTraceContext.resetForTests();
        Object nnc = new Object();
        RuntimeTraceContext.registerSource(nnc,
                new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));

        // A pool thread that existed before any request, as a connection's
        // sender threads do.
        final java.util.concurrent.CountDownLatch made =
                new java.util.concurrent.CountDownLatch(1);
        final java.util.concurrent.CountDownLatch wrote =
                new java.util.concurrent.CountDownLatch(1);
        final Object[] carried = new Object[1];
        final String[] header = new String[1];
        final String[] withoutScope = new String[1];
        final String[] filedUnder = new String[1];
        final String[] filedWithoutScope = new String[1];
        Thread sender = new Thread(() -> {
            try {
                made.await();
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
                return;
            }
            try {
                RuntimeTraceContext.outboundHeader(nnc);
                withoutScope[0] = "ACTIVE";
            } catch (IllegalStateException noFlow) {
                withoutScope[0] = "REFUSED";
            }
            header[0] = RuntimeTraceContext.outboundHeader(nnc, carried[0]);
            // The row the recorder writes for this send is attributed from
            // the same token, so the trace and the wire agree on the node.
            RuntimeTraceContext.View scoped =
                    RuntimeTraceContext.exchange(nnc, carried[0]);
            filedUnder[0] = (scoped.source == null ? ""
                    : scoped.source.key()) + " " + scoped.requestKey;
            RuntimeTraceContext.View unscoped =
                    RuntimeTraceContext.exchange(nnc, null);
            filedWithoutScope[0] = (unscoped.source == null ? ""
                    : unscoped.source.key()) + " " + unscoped.requestKey;
            wrote.countDown();
        }, "IPC Parameter Sending Thread #0");
        sender.start();

        long request = RuntimeTraceContext.beginRequest(nnc,
                "refresh-block-keys");
        carried[0] = RuntimeTraceContext.captureScope();
        made.countDown();
        wrote.await();
        RuntimeTraceContext.endRequest(request);

        assertEquals("the pool thread's own state names no request",
                "REFUSED", withoutScope[0]);
        assertTrue(header[0], header[0].startsWith("1|"));
        assertEquals("and the carried scope names all eight fields",
                8, header[0].split("[|]", -1).length);
        assertTrue("the source is the work's, not the thread's",
                header[0].contains(java.util.Base64.getUrlEncoder()
                        .withoutPadding().encodeToString(
                        SPS.getBytes("UTF-8"))));
        assertEquals("and the recorded row names the same node and request",
                SPS + "#epoch0 " + SPS
                        + "#epoch0/request/refresh-block-keys#1",
                filedUnder[0]);
        assertEquals("which the thread alone cannot name: no request at all",
                SPS + "#epoch0 ", filedWithoutScope[0]);
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
