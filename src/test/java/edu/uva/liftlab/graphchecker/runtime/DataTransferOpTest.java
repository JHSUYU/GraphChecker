package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.util.ArrayList;
import java.util.List;
import org.apache.hadoop.ipc.CausynthMessagePropagation;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * A DataTransfer op is a message the DataNode's turn takes into its own
 * context: the turn keeps its address (a replay that sent the op from
 * another IPC chain still answers it), and its RECV names the op's SEND, the
 * message that made the turn.
 *
 * <p>b20h FsDatasetImpl-1749 and three more checks: the op crossed with no
 * envelope, so the block id the DataNode decoded from its header paired with
 * no export and every path through it was refused UNATTESTED_ARM; standing
 * on the sender instead, the turn's tasks inherited the sender thread's IPC
 * chain, which the seed replays of FsDatasetImpl-1531 and -1843 did not
 * reproduce.</p>
 */
public class DataTransferOpTest {
    private static final SourceRef CLIENT =
            new SourceRef("CLUSTER_NODE", "CLIENT", "adhoc/client0", 0);
    private static final SourceRef DN =
            new SourceRef("CLUSTER_NODE", "DATANODE", "adhoc/dn1", 0);

    private final List<JsonObject> written = new ArrayList<JsonObject>();

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        Interactions.resetForTests();
        ScheduleLog.resetForTests();
        RecordingWindow.open();
        ScheduleLog.install(written::add);
    }

    @After
    public void clear() {
        CausynthMessagePropagation.endInbound();
        ScheduleLog.resetForTests();
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        Interactions.resetForTests();
        RecordingWindow.reset();
    }

    @Test
    public void aTurnTakesItsOpInAndKeepsItsAddress() {
        Object client = new Object();
        RuntimeTraceContext.registerSource(client, CLIENT);
        long writing = RuntimeTraceContext.beginRequest(client, "write");
        CausynthMessagePropagation.Outbound op =
                CausynthMessagePropagation.outboundOp();
        RuntimeTraceContext.endRequest(writing);
        assertTrue("an op is a request on a correlation of its own: "
                + op.correlationId, op.correlationId.startsWith("hdfs-dt-"));
        String sent = Interactions.sender(
                CausynthMessagePropagation.DATA_TRANSFER, op.correlationId,
                MessageDoors.REQUEST);
        assertFalse("its send filed a producer endpoint", sent.isEmpty());

        Object dataNode = new Object();
        RuntimeTraceContext.registerSource(dataNode, DN);
        long turn = MessageDoors.beginTick(dataNode, "DATA_XCEIVER");
        CausalContext before = Identity.contextHere();
        CausynthMessagePropagation.inboundOp(op.symbolic, op.correlationId);
        assertEquals("the turn keeps its address", before,
                Identity.contextHere());
        assertTrue(before instanceof CausalContext.Root);
        assertEquals("and serves the op it took in", op.correlationId,
                MessageDoors.current().correlationId);

        ScheduleEvent recv = null;
        for (JsonObject row : written) {
            if (!row.has("kind")) continue;
            ScheduleEvent event = RowCodec.readScheduleEvent(row);
            if (event.kind() == ScheduleEvent.Kind.RECV) recv = event;
        }
        assertTrue("the turn's RECV names the message that made it",
                recv != null && sent.equals(recv.received()));

        MessageDoors.endTick(turn);
        CausynthMessagePropagation.endInbound();
        assertTrue("and the turn's end ends it",
                MessageDoors.current() == null);
    }
}
