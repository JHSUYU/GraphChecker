package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

public class SymbolicMessageEnvelopeTest {

    @After
    public void clearThreadState() {
        SymbolicMessageEnvelope.clear();
    }

    @Test
    public void messageCarriesExactPortHandleAndProducerAcrossThreads()
            throws Exception {
        assertTrue(SymbolicMessageEnvelope.stage("request/generation", 41L,
                "producer-task", "producer-occurrence"));
        String wire = SymbolicMessageEnvelope.takeOutbound();
        assertFalse(wire.isEmpty());
        assertEquals("", SymbolicMessageEnvelope.takeOutbound());

        AtomicReference<SymbolicMessageEnvelope.Entry> received =
                new AtomicReference<>();
        Thread receiver = new Thread(() -> {
            SymbolicMessageEnvelope.installInbound(wire);
            received.set(SymbolicMessageEnvelope.take(
                    "request/generation"));
        });
        receiver.start();
        receiver.join();

        SymbolicMessageEnvelope.Entry entry = received.get();
        assertTrue(entry.present());
        assertEquals("request/generation", entry.portId());
        assertEquals(41L, entry.handle());
        assertEquals("producer-task", entry.producerTaskId());
        assertEquals("producer-occurrence",
                entry.producerOccurrenceId());
    }

    @Test
    public void requestAndResponseUseTheSameDrainingMechanism() {
        roundTrip("request/generation", 7L);
        roundTrip("response/status", 0L);
    }

    @Test
    public void takeConsumesOnlyTheInstalledMessage() {
        assertTrue(SymbolicMessageEnvelope.stage("p", 9L, "task", "occ"));
        String first = SymbolicMessageEnvelope.takeOutbound();
        SymbolicMessageEnvelope.installInbound(first);
        assertTrue(SymbolicMessageEnvelope.take("p").present());
        assertFalse(SymbolicMessageEnvelope.take("p").present());

        assertTrue(SymbolicMessageEnvelope.stage("p", 10L, "task2",
                "occ2"));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertEquals(10L, SymbolicMessageEnvelope.take("p").handle());
    }

    @Test
    public void duplicatePortFailsClosedInsteadOfSendingAnOlderValue() {
        assertTrue(SymbolicMessageEnvelope.stage("p", 1L, "task", "occ"));
        assertFalse(SymbolicMessageEnvelope.stage("p", 2L, "task", "occ"));
        assertEquals("", SymbolicMessageEnvelope.takeOutbound());
    }

    @Test
    public void malformedWireIsRejectedAndCannotExposeStaleInbound() {
        assertTrue(SymbolicMessageEnvelope.stage("p", 3L, "task", "occ"));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertThrows(IllegalArgumentException.class,
                () -> SymbolicMessageEnvelope.installInbound(
                        "CSE1;cA,01,dA,bw"));
        assertFalse(SymbolicMessageEnvelope.take("p").present());
        assertThrows(IllegalArgumentException.class,
                () -> SymbolicMessageEnvelope.installInbound(
                        "CSE1;cA,1,dA,bw;cA,2,dA,bw"));
        assertThrows(IllegalArgumentException.class,
                () -> SymbolicMessageEnvelope.installInbound(
                        "CSE2;cA,1,dA,bw"));
        assertThrows(IllegalArgumentException.class,
                () -> SymbolicMessageEnvelope.installInbound(
                        "CSE1;***,1,dA,bw"));
    }

    private static void roundTrip(String portId, long handle) {
        assertTrue(SymbolicMessageEnvelope.stage(portId, handle,
                "task", "occurrence"));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        SymbolicMessageEnvelope.Entry entry =
                SymbolicMessageEnvelope.take(portId);
        assertTrue(entry.present());
        assertEquals(handle, entry.handle());
        assertFalse(SymbolicMessageEnvelope.take(portId).present());
    }
}
