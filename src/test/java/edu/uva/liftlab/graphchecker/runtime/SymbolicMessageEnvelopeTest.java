package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * An expression belongs to a value inside the message, not to a queue.
 *
 * <p>One declared port carries many unrelated values of one shape in one
 * message, so each is addressed by its element ordinal and a decode looks its
 * own element up.  What these tests pin down is that addressing: the element
 * a decode asks for is the element it gets, an element the sender never
 * staged answers absent instead of handing over the next one along, and an
 * element nothing looked up is still countable when the message closes.</p>
 */
public class SymbolicMessageEnvelopeTest {
    private static final String PORT = "XCH.port.resp.key-id";
    private static final String OTHER = "XCH.port.resp.expiry";
    private static final List<String> CONSUMERS =
            Collections.singletonList("node/region/R#1#a1");

    @After
    public void clearThread() {
        SymbolicMessageEnvelope.clear();
    }

    /** Element n of a message is taken by the decode of element n. */
    @Test
    public void eachElementIsTakenByItsOwnDecode() {
        stage(PORT, 11L);
        stage(PORT, 22L);
        stage(PORT, 33L);
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
        assertEquals(22L, SymbolicMessageEnvelope.take(PORT).handle());
        assertEquals(33L, SymbolicMessageEnvelope.take(PORT).handle());
        assertEquals(0, SymbolicMessageEnvelope.inboundUnattached());
    }

    /**
     * A concrete leaf arrives present, carrying no expression.
     *
     * <p>{@code exportCommunicationLeaf} stages handle 0 for a leaf the VM
     * answered {@code NOT_SYMBOLIC} -- a concrete leaf is still a leaf the
     * message carried -- so the consumer takes an element that is
     * {@code present()} with no live handle.  For the consumer that is the
     * same fact as no element at all: there is an arrived value and no
     * producer expression, so it mints v_H from the arrival and the row
     * states {@code elementAbsent}.  It used to be refused with
     * RPC_HANDOFF_UNKNOWN_HANDLE, which left the obligation's assignment
     * unapplied exactly as the no-element refusal did.</p>
     */
    @Test
    public void aConcreteLeafArrivesPresentWithNoHandle() {
        assertTrue("a concrete leaf is still staged",
                SymbolicMessageEnvelope.stage(PORT, 0L, "TASK.SEED.1",
                        "node/region/R#1", CONSUMERS));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        SymbolicMessageEnvelope.Entry arrived =
                SymbolicMessageEnvelope.take(PORT);
        assertTrue("the element is there", arrived.present());
        assertEquals("and it carries no expression", 0L, arrived.handle());
        assertEquals("nothing is left unlooked-up", 0,
                SymbolicMessageEnvelope.inboundUnattached());
    }

    /** Ordinals are per port, so two ports do not shift each other. */
    @Test
    public void ordinalsAreCountedWithinOnePort() {
        stage(PORT, 11L);
        stage(OTHER, 91L);
        stage(PORT, 22L);
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertEquals(91L, SymbolicMessageEnvelope.take(OTHER).handle());
        assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
        assertEquals(22L, SymbolicMessageEnvelope.take(PORT).handle());
    }

    /**
     * A decode past the end of a message is told so.
     *
     * <p>The head of a queue would have handed it the next port's value or
     * the next message's; an ordinal has nothing to hand over.</p>
     */
    @Test
    public void aDecodeOfAnElementTheSenderNeverStagedIsAbsent() {
        stage(PORT, 11L);
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
        assertFalse(SymbolicMessageEnvelope.take(PORT).present());
        assertFalse(SymbolicMessageEnvelope.take(PORT).present());
    }

    /** An element is handed out once; a repeat decode is absent. */
    @Test
    public void anElementIsNotHandedOutTwice() {
        stage(PORT, 11L);
        String wire = SymbolicMessageEnvelope.takeOutbound();
        SymbolicMessageEnvelope.installInbound(wire);
        assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());

        SymbolicMessageEnvelope.installInbound(wire);
        assertEquals("a fresh message starts at its own first element",
                11L, SymbolicMessageEnvelope.take(PORT).handle());
    }

    /** What no decode looked up is still countable while the message lives. */
    @Test
    public void elementsNothingLookedUpAreCounted() {
        stage(PORT, 11L);
        stage(PORT, 22L);
        stage(PORT, 33L);
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertEquals(3, SymbolicMessageEnvelope.inboundUnattached());
        SymbolicMessageEnvelope.take(PORT);
        assertEquals(2, SymbolicMessageEnvelope.inboundUnattached());
        SymbolicMessageEnvelope.clearInbound();
        assertEquals(0, SymbolicMessageEnvelope.inboundUnattached());
    }

    /** The ordinal the sender stamped travels with the element. */
    @Test
    public void theOrdinalTravelsOnTheWire() {
        stage(PORT, 11L);
        stage(PORT, 22L);
        String wire = SymbolicMessageEnvelope.takeOutbound();
        assertTrue(wire.startsWith("CSE4;"));
        SymbolicMessageEnvelope.installInbound(wire);

        assertEquals(0, SymbolicMessageEnvelope.peek(PORT).ordinal());
        assertEquals(0, SymbolicMessageEnvelope.take(PORT).ordinal());
        assertEquals(1, SymbolicMessageEnvelope.take(PORT).ordinal());
    }

    /** A wire this vocabulary did not write is refused, not guessed at. */
    @Test(expected = IllegalArgumentException.class)
    public void anOlderWireIsRefused() {
        SymbolicMessageEnvelope.installInbound("CSE3;cG9ydA,1,dA,bw,Yw,0");
    }

    /**
     * Two groups of the same shape in one message do not run together.
     *
     * <p>The frame is the thing whose one construction builds one instance of
     * the value the port belongs to.  Without it a receiver decoding the
     * second group would take the first group's leaves; with it each group's
     * elements are counted inside their own frame.</p>
     */
    @Test
    public void aFrameKeepsTwoGroupsOfOneShapeApart() {
        SymbolicMessageEnvelope.pushOutboundFrame();
        stage(PORT, 11L);
        stage(PORT, 12L);
        SymbolicMessageEnvelope.popOutboundFrame();
        SymbolicMessageEnvelope.pushOutboundFrame();
        stage(PORT, 21L);
        stage(PORT, 22L);
        SymbolicMessageEnvelope.popOutboundFrame();
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        SymbolicMessageEnvelope.pushInboundFrame();
        assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
        assertEquals(12L, SymbolicMessageEnvelope.take(PORT).handle());
        assertFalse("a frame holds only its own elements",
                SymbolicMessageEnvelope.take(PORT).present());
        SymbolicMessageEnvelope.popInboundFrame();

        SymbolicMessageEnvelope.pushInboundFrame();
        assertEquals(21L, SymbolicMessageEnvelope.take(PORT).handle());
        assertEquals(22L, SymbolicMessageEnvelope.take(PORT).handle());
        SymbolicMessageEnvelope.popInboundFrame();
        assertEquals(0, SymbolicMessageEnvelope.inboundUnattached());
    }

    /** A decode that opens fewer frames leaves the rest unclaimed, by name. */
    @Test
    public void aFrameNobodyDecodesLeavesItsElementsUnclaimed() {
        SymbolicMessageEnvelope.pushOutboundFrame();
        stage(PORT, 11L);
        SymbolicMessageEnvelope.popOutboundFrame();
        SymbolicMessageEnvelope.pushOutboundFrame();
        stage(PORT, 21L);
        SymbolicMessageEnvelope.popOutboundFrame();
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        SymbolicMessageEnvelope.pushInboundFrame();
        assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
        SymbolicMessageEnvelope.popInboundFrame();

        assertEquals(1, SymbolicMessageEnvelope.inboundUnattached());
    }

    /** A port that declares no frame is addressed within the message. */
    @Test
    public void anUnframedPortIsAddressedWithinTheMessage() {
        stage(PORT, 11L);
        stage(PORT, 22L);
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertEquals(0, SymbolicMessageEnvelope.peek(PORT).frame());
        assertEquals(11L, SymbolicMessageEnvelope.take(PORT).handle());
        assertEquals(22L, SymbolicMessageEnvelope.take(PORT).handle());
    }

    private static void stage(String portId, long handle) {
        assertTrue(SymbolicMessageEnvelope.stage(portId, handle,
                "TASK.SEED.0", "node/region/R#1#a1",
                Arrays.asList(CONSUMERS.get(0))));
    }
}
