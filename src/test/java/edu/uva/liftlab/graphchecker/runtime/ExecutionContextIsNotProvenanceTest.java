package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

/**
 * A value arriving over the wire does not say where the receiver ran.
 *
 * <p>An occurrence is addressed by (node, epoch, region, k-th activation),
 * and the node is where the activation ran. Execution context is set by
 * execution-scope events only: a node registering its instances, or an async
 * seed taken from a registered source. What a message carries is provenance,
 * and the propagated expression already states it.</p>
 *
 * <p>{@code enterInbound} used to fall back to the SENDER's source, parsed
 * out of the message header, when the local owner was unregistered and the
 * thread had no source yet. At record time a DataNode thread already carries
 * the DN, so the arm never fired; at replay the thread may be fresh, so it
 * did. On hdfs-17899 bug3 that is "matching root inherited
 * hdfs-17899/nn0#epoch0 instead of hdfs-17899/target-dn#epoch0", and the
 * ordinal inflation behind it: every node's activations of one region landing
 * in one counter because they all claimed one node.</p>
 */
public class ExecutionContextIsNotProvenanceTest {
    private static final String NN = "hdfs-17899/nn0";
    private static final String DN = "hdfs-17899/target-dn";

    @After
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
    }

    /** A thread carrying the DataNode keeps it when the NameNode's value
     *  arrives on it. */
    @Test
    public void anArrivingValueDoesNotRestampTheReceivingThread() {
        RuntimeTraceContext.resetForTests();
        Object nameNode = new Object();
        RuntimeTraceContext.registerSource(nameNode,
                new SourceRef("NAMENODE", "nn", NN, 0L));
        Object dataNode = new Object();
        RuntimeTraceContext.registerSource(dataNode,
                new SourceRef("DATANODE", "dn", DN, 0L));

        // The NameNode sends; the header states its source, as provenance.
        long request = RuntimeTraceContext.beginRequest(nameNode, "heartbeat");
        String header = RuntimeTraceContext.outboundHeader(nameNode);
        RuntimeTraceContext.endRequest(request);
        assertNotNull(header);

        // The DataNode thread is executing as the DataNode.
        long dnRequest = RuntimeTraceContext.beginRequest(dataNode,
                "block-report");
        assertEquals(DN + "#epoch0",
                RuntimeTraceContext.currentSource().key());

        // The value arrives on that thread, through an owner the workload
        // never registered -- an IPC connection, not a node.
        long inbound = RuntimeTraceContext.enterInbound(header, "IPC",
                "corr-1", "attempt-1", "REQUEST", new Object());

        assertEquals("the thread still runs as the DataNode",
                DN + "#epoch0",
                RuntimeTraceContext.currentSource().key());

        RuntimeTraceContext.exitInbound(inbound);
        RuntimeTraceContext.endRequest(dnRequest);
    }

    /** With nothing registered and no ambient source, the arrival names none. */
    @Test
    public void anArrivalOnAnUnattributedThreadNamesNoNode() {
        RuntimeTraceContext.resetForTests();
        Object nameNode = new Object();
        RuntimeTraceContext.registerSource(nameNode,
                new SourceRef("NAMENODE", "nn", NN, 0L));
        long request = RuntimeTraceContext.beginRequest(nameNode, "heartbeat");
        String header = RuntimeTraceContext.outboundHeader(nameNode);
        RuntimeTraceContext.endRequest(request);

        long inbound = RuntimeTraceContext.enterInbound(header, "IPC",
                "corr-1", "attempt-1", "REQUEST", new Object());

        assertNull("provenance is not an execution scope",
                RuntimeTraceContext.currentSource());

        RuntimeTraceContext.exitInbound(inbound);
    }

    /** A registered local owner still names the receiving side, as before. */
    @Test
    public void aRegisteredLocalOwnerStillNamesTheReceiver() {
        RuntimeTraceContext.resetForTests();
        Object nameNode = new Object();
        RuntimeTraceContext.registerSource(nameNode,
                new SourceRef("NAMENODE", "nn", NN, 0L));
        Object dataNode = new Object();
        RuntimeTraceContext.registerSource(dataNode,
                new SourceRef("DATANODE", "dn", DN, 0L));
        long request = RuntimeTraceContext.beginRequest(nameNode, "heartbeat");
        String header = RuntimeTraceContext.outboundHeader(nameNode);
        RuntimeTraceContext.endRequest(request);

        long inbound = RuntimeTraceContext.enterInbound(header, "IPC",
                "corr-1", "attempt-1", "REQUEST", dataNode);

        assertEquals(DN + "#epoch0",
                RuntimeTraceContext.currentSource().key());

        RuntimeTraceContext.exitInbound(inbound);
    }
}
