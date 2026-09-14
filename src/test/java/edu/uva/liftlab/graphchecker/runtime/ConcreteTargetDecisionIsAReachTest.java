package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapLedger;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * An activation that decides the target site has reached the target.
 *
 * <p>Whether the predicate there was symbolic is evidence about the anchor,
 * not a condition on publishing it: the reach carries the expression when
 * the branch has one and the concrete outcome when it has not, and the
 * composer reads which of the two it is from the branch row beside it.</p>
 *
 * <p>hdfs-17960's target branch is {@code i != sm.getNumSnapshots()} over
 * two concrete ints; the root reaches it by control dependence, because the
 * flip skips a decrement. Gated on a solver witness, that activation
 * recorded the decision AND was named by {@code nameUnreachedTargetBranch}
 * as never having decided it -- two statements about one activation that
 * cannot both be true, and the reason MARKER_FLIPPED had no reach to read on
 * lanes BJ, BK and BL.</p>
 */
public class ConcreteTargetDecisionIsAReachTest {
    private static final String TARGET =
            "<org.apache.hadoop.hdfs.server.namenode.snapshot."
                    + "SnapshotManager: void deleteSnapshot()>#u61";
    private static final String ELSEWHERE =
            "<org.apache.hadoop.hdfs.server.namenode.snapshot."
                    + "SnapshotManager: void deleteSnapshot()>#u44";

    /** A concrete decision at the addressed occurrence states the reach. */
    @Test
    public void aConcreteDecisionAtTheTargetStatesTheReach() {
        assertTrue("the site executed and the outcome is this run's own",
                ConcolicRegionRuntime.statesTargetReach(true, false,
                        TARGET, 1, TARGET, 1));
    }

    /** A symbolic one states it in exactly the same way. */
    @Test
    public void aSymbolicDecisionAtTheTargetStatesTheSameReach() {
        assertTrue(ConcolicRegionRuntime.statesTargetReach(true, false,
                TARGET, 1, TARGET, 1));
    }

    /** Another activation of the site is another occurrence. */
    @Test
    public void anotherOccurrenceOfTheTargetSiteIsNotTheAddressedOne() {
        assertFalse(ConcolicRegionRuntime.statesTargetReach(true, false,
                TARGET, 1, TARGET, 2));
    }

    /** A bounded loop may run the planned occurrence at another k. */
    @Test
    public void aPermutedLoopOccurrenceStillStatesTheReach() {
        assertTrue(ConcolicRegionRuntime.statesTargetReach(true, true,
                TARGET, 1, TARGET, 3));
    }

    /** Another site is not the target, however it decided. */
    @Test
    public void anotherSiteIsNotTheTarget() {
        assertFalse(ConcolicRegionRuntime.statesTargetReach(true, false,
                TARGET, 1, ELSEWHERE, 1));
        assertFalse("and a task naming no target reaches none",
                ConcolicRegionRuntime.statesTargetReach(true, false,
                        "", 1, ELSEWHERE, 1));
    }

    /**
     * A decision the VM emitted no event for states nothing.
     *
     * <p>There is no branch row beside which the reach could be read, so
     * this is the one case that is still silent -- and it is the case
     * {@code TARGET_BRANCH_NOT_REACHED} is for.</p>
     */
    @Test
    public void aDecisionWithNoRecordedRowStatesNoReach() {
        assertFalse(ConcolicRegionRuntime.statesTargetReach(false, false,
                TARGET, 1, TARGET, 1));
    }

    /**
     * Every skip kind the runtime publishes is classed under the code the
     * importer actually spells.
     *
     * <p>A region skip reaches the ledger as {@code "REGION_" + skipKind}
     * ({@code ConcolicSummaryImporter.skippedEventCode}). Two entries were
     * written under the bare skip kind and matched no row at all, so
     * {@code REGION_ROOT_NEVER_EXECUTED} took the blocking default on lanes
     * VM9 and VM10 with the slice-conditional scope written for it deciding
     * nothing.</p>
     */
    @Test
    public void everySkipKindIsClassedUnderItsPublishedCode()
            throws Exception {
        for (java.lang.reflect.Field field
                : ConcolicRegionRuntime.class.getDeclaredFields()) {
            if (!field.getName().startsWith("SKIP_")) continue;
            field.setAccessible(true);
            String code = "REGION_" + field.get(null);
            assertTrue(code + " is not registered in the gap ledger",
                    GapLedger.blockingCodes().contains(code)
                            || GapLedger.diagnosticCodes().contains(code));
        }
    }

    /**
     * The flip wave is classed apart, and only where the campaign can name
     * the row as one.
     */
    @Test
    public void theFlipWaveCodesAreRegisteredAndFailClosed() {
        for (String code : new String[]{"REGION_ROOT_NEVER_EXECUTED",
                "REGION_REPLAY_PREFIX_UNMATCHED",
                "PUBLICATION_TASK_ANSWERED_BY_NO_RUN"}) {
            assertTrue(code, GapLedger.flipWaveDiagnostic(code));
            assertFalse(code + " states no reason",
                    GapLedger.flipWaveReason(code).isEmpty());
            assertTrue(code + " must still block a reader that cannot see"
                            + " the wave", GapLedger.blocking(code));
        }
        assertFalse("a seed-wave code carries no flip-wave qualifier",
                GapLedger.flipWaveDiagnostic("PUBLICATION_TASK_SILENT"));
    }
}
