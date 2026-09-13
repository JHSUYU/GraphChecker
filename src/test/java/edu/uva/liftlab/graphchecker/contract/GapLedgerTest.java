package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The one register that decides which published gap withholds a claim.
 *
 * <p>Design point 6 is fail-closed: a missing chain link is a reported gap
 * and the claim stays withheld while it is open.  That only holds if the
 * default answer for a code nobody thought about is "blocking", so a gap
 * added to some stage and never classed here cannot quietly pass as
 * telemetry.  {@code run_engine.sh} reads the same table over the stages the
 * Java claim cannot see, so the two readers cannot disagree.</p>
 */
public class GapLedgerTest {
    /** A code nobody registered withholds the claim. */
    @Test
    public void anUnregisteredCodeBlocks() {
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

    /**
     * A region code is decided against the replay slice, not by a blanket
     * rule: blocking on a task the slice kept, diagnostic on one it pruned.
     */
    @Test
    public void aSliceConditionalCodeIsDecidedAgainstTheKeptSlice() {
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
    }
}
