package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

import org.apache.hadoop.ipc.CausynthMessagePropagation;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * The shim entry points the r6 trees call before codec capture gives them a
 * behaviour: a response or an op leaving with its message is the plain door,
 * and a parsed message changes nothing.
 */
public class ShimCodecEntriesTest {
    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    @After
    public void clear() {
        CausynthMessagePropagation.endInbound();
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    @Test
    public void bothEntriesAreNoOps() {
        Object server = new Object();
        CausynthMessagePropagation.received(null);
        CausynthMessagePropagation.received(new Object());
        assertNull("a parse installs nothing", MessageDoors.current());

        CausynthMessagePropagation.Outbound plain =
                CausynthMessagePropagation.outbound(
                        CausynthMessagePropagation.IPC, "c-1", "0",
                        MessageDoors.RESPONSE, server);
        CausynthMessagePropagation.Outbound carrying =
                CausynthMessagePropagation.outboundResponse(
                        CausynthMessagePropagation.IPC, "c-1", "0", server,
                        new Object());
        assertEquals(plain.correlationId, carrying.correlationId);
        assertEquals(plain.attemptId, carrying.attemptId);
        assertEquals(plain.trace, carrying.trace);
        assertEquals(plain.symbolic, carrying.symbolic);
    }

    @Test
    public void anOpLeavingWithItsMessageIsThePlainOpDoor() {
        CausynthMessagePropagation.Outbound plain =
                CausynthMessagePropagation.outboundOp();
        CausynthMessagePropagation.Outbound carrying =
                CausynthMessagePropagation.outboundOp(new Object());
        assertEquals(plain.active(), carrying.active());
        assertEquals(plain.trace, carrying.trace);
        assertEquals(plain.symbolic, carrying.symbolic);
    }
}
