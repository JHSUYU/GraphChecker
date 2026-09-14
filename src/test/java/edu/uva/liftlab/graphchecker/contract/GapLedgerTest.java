package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The one register that decides which published gap withholds a claim.
 *
 * <p>Design point 6 is fail-closed, which holds only if the default answer
 * for a code nobody classed is "blocking": a gap added to some stage and
 * never classed here cannot pass as telemetry.  {@code run_engine.sh} reads
 * the same table, so the two readers cannot disagree.</p>
 */
public class GapLedgerTest {

    /**
     * A gap is classed fail-closed: a code nobody registered blocks, and a
     * code decided against the replay slice blocks for a reader that cannot
     * see the slice.
     */
    @Test
    public void aGapIsClassedFailClosed() {
        assertEquals(GapLedger.GapClass.BLOCKING,
                GapLedger.classOf("A_CODE_NOBODY_REGISTERED"));
        assertTrue(GapLedger.blocking("A_CODE_NOBODY_REGISTERED"));
        assertFalse("an unregistered code is not an exception to the rule",
                GapLedger.diagnosticCodes()
                        .contains("A_CODE_NOBODY_REGISTERED"));

        // A reader that also knows the slice answers the same way, because
        // not knowing a code is not knowing whether it breaks a chain.
        assertEquals(GapLedger.GapClass.BLOCKING,
                GapLedger.classOf("A_CODE_NOBODY_REGISTERED", false));

        // A region code is decided against the replay slice, not by a blanket
        // rule: blocking on a task the slice kept, diagnostic on one it pruned.
        String code = null;
        for (GapLedger.Entry entry : GapLedger.entries()) {
            if (entry.scope == GapLedger.Scope.KEPT_SLICE) {
                code = entry.code;
                break;
            }
        }
        assertTrue("the ledger must carry at least one slice-conditional"
                + " code", code != null);
        assertTrue(GapLedger.sliceConditional(code));
        assertEquals(GapLedger.GapClass.BLOCKING,
                GapLedger.classOf(code, true));
        assertEquals(GapLedger.GapClass.DIAGNOSTIC,
                GapLedger.classOf(code, false));
        // A reader that cannot see the slice keeps withholding.
        assertEquals(GapLedger.GapClass.BLOCKING, GapLedger.classOf(code));

        // The same shape for the composed-port scope: the handoff gap is
        // decided by joining its port against the composed formula's phases
        // and the campaign's attaches, a question only the campaign fold can
        // ask, so every reader here answers BLOCKING and the fold is told
        // which codes to ask it about.
        assertTrue(GapLedger.composedPortConditional("RPC_HANDOFF_GAP"));
        assertEquals(GapLedger.GapClass.BLOCKING,
                GapLedger.classOf("RPC_HANDOFF_GAP"));
        assertEquals(GapLedger.GapClass.BLOCKING,
                GapLedger.classOf("RPC_HANDOFF_GAP", false));
        assertFalse("a composed-port code is not an unconditional exception",
                GapLedger.diagnosticCodes().contains("RPC_HANDOFF_GAP"));
        assertFalse("the two conditional scopes are different questions",
                GapLedger.sliceConditional("RPC_HANDOFF_GAP"));
        assertFalse(GapLedger.composedPortConditional(code));
        assertFalse(GapLedger.composedPortConditional(
                "A_CODE_NOBODY_REGISTERED"));
        // And the shell reads the list from the same table it reads the
        // slice-conditional one from.
        assertTrue("the published ledger must name the composed-port codes",
                GapLedger.toJson().getAsJsonArray("composedPortConditional")
                        .toString().contains("RPC_HANDOFF_GAP"));
    }

    /** Every exception to the default states why it cannot break a chain. */
    @Test
    public void everyNonBlockingCodeStatesItsReason() {
        for (GapLedger.Entry entry : GapLedger.entries()) {
            if (entry.gapClass == GapLedger.GapClass.BLOCKING
                    && entry.scope == GapLedger.Scope.ALWAYS) {
                continue;
            }
            assertTrue("a code that is anything but blocking-always must say"
                            + " why: " + entry.code,
                    entry.reason != null && !entry.reason.trim().isEmpty());
        }
    }
}
