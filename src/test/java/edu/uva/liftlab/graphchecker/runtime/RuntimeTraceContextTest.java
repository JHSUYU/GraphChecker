package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

public class RuntimeTraceContextTest {
    @Before
    public void setUp() {
        RuntimeTraceContext.resetForTests();
    }

    @After
    public void tearDown() {
        RuntimeTraceContext.resetForTests();
    }

                /**
     * A source is a stable logical identity plus an epoch, and every span the
     * workload opens is attributed to one: a restart advances the epoch
     * without rewriting what the old runtime object already reported, a
     * spawned thread inherits its parent's source on a lane of its own, and
     * a message receive switches to the registered server source while carrying
     * the caller as its remote parent.
     */
    @Test
    public void everySpanIsAttributedToOneSourceEpoch() throws Exception {
        SourceRef source = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 3L);
        assertEquals("CLUSTER_NODE", source.kind());
        assertEquals("NAMENODE", source.role());
        assertEquals("cluster0/nn0", source.id());
        assertEquals(3L, source.epoch());
        assertEquals("cluster0/nn0#epoch3", source.key());

        // A restart moves the stable anchor to the next epoch.  The runtime
        // object the old epoch used keeps answering for that old epoch, so
        // nothing already recorded is silently re-attributed.
        RuntimeTraceContext.resetForTests();
        Object stableSlot = new Object();
        Object oldNameNode = new Object();
        Object newNameNode = new Object();
        SourceRef before = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 0L);
        SourceRef after = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 1L);
        RuntimeTraceContext.registerSource(stableSlot, before);
        RuntimeTraceContext.registerSourceAlias(oldNameNode, stableSlot);
        RuntimeTraceContext.restartSource(stableSlot, after);
        RuntimeTraceContext.registerSourceAlias(newNameNode, stableSlot);
        assertEquals(before, RuntimeTraceContext.sourceFor(oldNameNode));
        assertEquals(after, RuntimeTraceContext.sourceFor(stableSlot));
        assertEquals(after, RuntimeTraceContext.sourceFor(newNameNode));
        // A thread the workload spawns inherits the parent span and the
        // parent's source, on a lane of its own.
        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        SourceRef dataNode = new SourceRef(
                "CLUSTER_NODE", "DATANODE", "cluster0/dn0", 0L);
        RuntimeTraceContext.registerSource(node, dataNode);
        RuntimeTraceContext.View parent = RuntimeTraceContext.enterRoot(node);
        final AtomicReference<RuntimeTraceContext.View> spawned =
                new AtomicReference<>();
        Thread child = new Thread(() -> spawned.set(
                RuntimeTraceContext.enterRoot(Thread.currentThread())));
        RuntimeTraceContext.captureAsync(child);
        child.start();
        child.join();
        assertEquals(dataNode, spawned.get().source);
        assertEquals(parent.spanId, spawned.get().parentSpanId);
        assertNotEquals(parent.laneId, spawned.get().laneId);

        // Request and response use the same carried context. Correlation is
        // intentionally absent: it names graph topology, never context.
        RuntimeTraceContext.resetForTests();
        Object client = new Object();
        Object nameNode = new Object();
        SourceRef clientSource = new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "app/client0", 0L);
        SourceRef serverSource = new SourceRef(
                "CLUSTER_NODE", "NAMENODE", "cluster0/nn0", 1L);
        RuntimeTraceContext.registerSource(client, clientSource);
        RuntimeTraceContext.registerSource(nameNode, serverSource);
        long request = RuntimeTraceContext.beginRequest(client,
                "fetchindex");
        RuntimeTraceContext.View caller = RuntimeTraceContext.enterRoot(client);
        String requestHeader = RuntimeTraceContext.outboundHeader(client);
        final AtomicReference<RuntimeTraceContext.View> receive =
                new AtomicReference<>();
        final AtomicReference<RuntimeTraceContext.View> serverSpan =
                new AtomicReference<>();
        final AtomicReference<String> responseHeader = new AtomicReference<>();
        Thread server = new Thread(() -> {
            long scope = RuntimeTraceContext.enterInbound(requestHeader,
                    nameNode);
            try {
                receive.set(RuntimeTraceContext.current());
                RuntimeTraceContext.View handler =
                        RuntimeTraceContext.enterRoot(nameNode);
                serverSpan.set(handler);
                responseHeader.set(RuntimeTraceContext.outboundHeader(
                        nameNode));
                RuntimeTraceContext.exitRoot(handler.spanId);
            } finally {
                RuntimeTraceContext.exitInbound(scope);
            }
        });
        server.start();
        server.join();
        assertEquals(serverSource, receive.get().source);
        assertEquals(caller.spanId, receive.get().remoteParentSpanId);
        assertEquals(caller.requestKey, receive.get().requestKey);

        long response = RuntimeTraceContext.enterInbound(
                responseHeader.get(), client);
        RuntimeTraceContext.View completed = RuntimeTraceContext.current();
        assertEquals(clientSource, completed.source);
        assertEquals(serverSpan.get().spanId, completed.remoteParentSpanId);
        assertEquals(caller.requestKey, completed.requestKey);
        RuntimeTraceContext.exitInbound(response);
        assertEquals(clientSource, RuntimeTraceContext.currentSource());
        assertEquals(0L, RuntimeTraceContext.current().remoteParentSpanId);
        RuntimeTraceContext.exitRoot(caller.spanId);
        RuntimeTraceContext.endRequest(request);
    }

    @Test
    public void messageContextRejectsMissingNonCanonicalAndUnknownHeaders() {
        for (String malformed : new String[]{null, "", "0|1|2|a|b|c|d|e",
                "1|-1|0|QQ|Qg|Qw|RA|RQ", "1|0|0|QQ==|Qg|Qw|RA|RQ"}) {
            try {
                RuntimeTraceContext.enterInbound(malformed, null);
                throw new AssertionError("accepted malformed header: "
                        + malformed);
            } catch (IllegalArgumentException expected) {
                assertEquals("malformed trace context header",
                        expected.getMessage());
            }
        }
    }
}
