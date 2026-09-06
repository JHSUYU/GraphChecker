package edu.uva.liftlab.graphchecker.runtime;

import org.junit.After;
import org.junit.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
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

}
