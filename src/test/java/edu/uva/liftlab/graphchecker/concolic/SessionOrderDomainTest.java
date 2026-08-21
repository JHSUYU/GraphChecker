package edu.uva.liftlab.graphchecker.concolic;

import org.junit.Test;

import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.twoWriterLedger;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The one order domain over the recorded event ledger.
 *
 * <p>Field, synchronization, handoff and region events live in one relation
 * here, which is the property the composer's per-channel position variables
 * never had: two events on different channels were previously in disjoint
 * integer domains and therefore unrelatable.</p>
 */
public class SessionOrderDomainTest {

    @Test
    public void twoWritesWithRecordedSynchronizationStayOrdered() {
        SessionOrderDomain domain = SessionOrderDomain.of(
                SharedStateEvidence.ledgerRecord(twoWriterLedger(),
                        RecordedSharedStateFixtures.identity(
                                "REGION.reader", 1L)));

        // The fixture records one explicit cross-thread synchronization edge.
        assertTrue(domain.orderedBefore(11L, 12L));
        assertFalse(domain.orderedBefore(12L, 11L));
        assertFalse(domain.orderedBefore(11L, 21L));
        assertFalse(domain.orderedBefore(21L, 11L));
        assertEquals(3, domain.eventCount());
        assertEquals("FIELD_WRITE", domain.eventKind(11L));
        assertEquals("REGION.writerB", domain.regionOf(12L));
        assertEquals(102L, domain.contextOf(12L));
    }
}
