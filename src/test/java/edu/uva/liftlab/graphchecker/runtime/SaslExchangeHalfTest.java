package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.apache.hadoop.ipc.CausynthMessagePropagation;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * A SASL message's half is its sender's role in the exchange.
 *
 * <p>hdfs-17967: a DataNode serving the source's transfer opens its own
 * handshake with the mirror.  Its messages there are REQUESTS of the exchange
 * it opened; labelled as the RESPONSE to the request it was serving, they left
 * under the source's correlation, the recording stated no export of the key id
 * on the forwarding node, and no plan ever instrumented the occurrence that
 * sent it.</p>
 */
public class SaslExchangeHalfTest {
    private static final SourceRef HEAD =
            new SourceRef("CLUSTER_NODE", "DATANODE", "hdfs-17967/head-dn", 0);

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        RecordingWindow.open();
    }

    @After
    public void clear() {
        CausynthMessagePropagation.endInbound();
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        RecordingWindow.reset();
    }

    @Test
    public void aClientHandshakeOpenedWhileServingSendsItsOwnRequests() {
        Object head = new Object();
        RuntimeTraceContext.registerSource(head, HEAD);
        long upstream = RuntimeTraceContext.beginRequest(head, "transfer");
        String header = RuntimeTraceContext.outboundHeader(head);
        RuntimeTraceContext.endRequest(upstream);
        assertTrue("the upstream message carries a context", !header.isEmpty());
        // The serving thread's own flow, so every message it sends carries a
        // header and the half is the only thing asked.
        long serving = RuntimeTraceContext.beginRequest(head, "serve");

        // Serving the source's handshake: its message is a REQUEST, and the
        // server's answer is the RESPONSE of that same exchange.
        CausynthMessagePropagation.inboundSasl(header, "", "source-sasl", "1");
        CausynthMessagePropagation.Outbound answer =
                CausynthMessagePropagation.outboundSasl();
        assertEquals("source-sasl", answer.correlationId);

        // The same thread, still serving it, opens its own handshake with the
        // next node: that exchange's messages are ITS requests.
        CausynthMessagePropagation.inboundSasl(header, "", "source-sasl", "1");
        CausynthMessagePropagation.beginSasl();
        CausynthMessagePropagation.Outbound own =
                CausynthMessagePropagation.outboundSasl();
        assertTrue("the forwarding node's own exchange, not the served one: "
                        + own.correlationId,
                own.correlationId.startsWith("hdfs-sasl-"));
        // The next node answers under that exchange, and the next request
        // stays in it.
        CausynthMessagePropagation.inboundSasl(header, "", own.correlationId,
                "1");
        CausynthMessagePropagation.Outbound next =
                CausynthMessagePropagation.outboundSasl();
        assertEquals(own.correlationId, next.correlationId);
        CausynthMessagePropagation.endSasl();

        // Closed: the served exchange is the thread's again.
        CausynthMessagePropagation.Outbound after =
                CausynthMessagePropagation.outboundSasl();
        assertEquals("source-sasl", after.correlationId);
        RuntimeTraceContext.endRequest(serving);
    }
}
