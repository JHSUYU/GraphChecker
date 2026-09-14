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
     * code the campaign fold decides blocks for every reader that cannot
     * see what the fold sees.
     */
    @Test
    public void aGapIsClassedFailClosed() {
        assertEquals(GapLedger.GapClass.BLOCKING,
                GapLedger.classOf("A_CODE_NOBODY_REGISTERED"));
        assertTrue(GapLedger.blocking("A_CODE_NOBODY_REGISTERED"));
        assertFalse("an unregistered code is not an exception to the rule",
                GapLedger.diagnosticCodes()
                        .contains("A_CODE_NOBODY_REGISTERED"));

        // A planned region that never ran blocks outright.  It used to be
        // decided against the replay slice -- blocking on a task the slice
        // kept, diagnostic on one it pruned -- and there is no slice: a
        // replay focuses one occurrence and everything else runs concretely,
        // so a planned region with no activation is a broken chain, full
        // stop.
        assertEquals(GapLedger.GapClass.BLOCKING,
                GapLedger.classOf("REGION_ROOT_NEVER_EXECUTED"));
        assertEquals(GapLedger.GapClass.BLOCKING,
                GapLedger.classOf("COVERAGE_GAP"));

        // The composed-port scope is the one conditional left: the handoff
        // gap is
        // decided by joining its port against the composed formula's phases
        // and the campaign's attaches, a question only the campaign fold can
        // ask, so every reader here answers BLOCKING and the fold is told
        // which codes to ask it about.
        assertTrue(GapLedger.composedPortConditional("RPC_HANDOFF_GAP"));
        assertEquals(GapLedger.GapClass.BLOCKING,
                GapLedger.classOf("RPC_HANDOFF_GAP"));
        assertFalse("a composed-port code is not an unconditional exception",
                GapLedger.diagnosticCodes().contains("RPC_HANDOFF_GAP"));
        assertFalse(GapLedger.composedPortConditional(
                "REGION_ROOT_NEVER_EXECUTED"));
        assertFalse(GapLedger.composedPortConditional(
                "A_CODE_NOBODY_REGISTERED"));
        // And the shell reads the list from the published table.
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
