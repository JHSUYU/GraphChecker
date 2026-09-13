package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * Replay-side selection of a workload-declared fault marker.
 *
 * <p>Two defects met here.  The gate read {@code symbolicDemand}, which no
 * producer ever stamps with the fault classification, so every marker
 * resolved to nothing and {@code Debug.makeSymbolicBoolean} returned a
 * concrete {@code false} on every replay.  And the match ignored the
 * recorded {@code replayOccurrence}, so two in-scope requests inside one
 * activation collapsed into one ambiguous name.</p>
 */
public class ExplicitFaultReplaySelectionTest {

    private static final String NAME = "hadoopIpcRequestFails";

    /**
     * The field the finalizer actually writes.  A row shaped exactly like
     * the one in a recorded plan resolves; the same row with the
     * classification moved to {@code symbolicDemand} does not.
     */
    @Test
    public void theGateReadsTheFieldTheFinalizerWrites() {
        ConcolicRegionRuntime.SymbolizeAction recorded = action(
                RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT,
                NAME, 1);
        assertEquals(RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT,
                recorded.sourceKind);
        assertEquals(Collections.singletonList(recorded),
                ConcolicRegionRuntime.explicitFaultCandidates(
                        Collections.singletonList(recorded), NAME, 1));

        JsonObject misplaced = json(NAME, 1);
        misplaced.addProperty("symbolicDemand",
                RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT);
        assertTrue("the demand field must not gate the marker",
                ConcolicRegionRuntime.explicitFaultCandidates(
                        Collections.singletonList(
                                new ConcolicRegionRuntime.SymbolizeAction(
                                        misplaced)), NAME, 1).isEmpty());
    }

    /**
     * The scheduler's own verdict travels on {@code symbolicDemand} for the
     * very same action, so carrying it must not disturb the gate.
     */
    @Test
    public void theSchedulerSelectionVerdictDoesNotDisturbTheGate() {
        JsonObject selected = json(NAME, 1);
        selected.addProperty("sourceKind",
                RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT);
        selected.addProperty("symbolicDemand",
                "WORKLOAD_DECLARED_SYMBOLIC_FAULT");
        assertEquals(1, ConcolicRegionRuntime.explicitFaultCandidates(
                Collections.singletonList(
                        new ConcolicRegionRuntime.SymbolizeAction(selected)),
                NAME, 1).size());
    }

    /** Two firings of one marker inside one activation stay two roots. */
    @Test
    public void twoFiringsInOneActivationSelectByRecordedOccurrence() {
        ConcolicRegionRuntime.SymbolizeAction first = action(
                RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT,
                NAME, 1);
        ConcolicRegionRuntime.SymbolizeAction second = action(
                RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT,
                NAME, 2);
        List<ConcolicRegionRuntime.SymbolizeAction> both =
                Arrays.asList(first, second);

        assertSame(first, only(ConcolicRegionRuntime
                .explicitFaultCandidates(both, NAME, 1)));
        assertSame(second, only(ConcolicRegionRuntime
                .explicitFaultCandidates(both, NAME, 2)));
        assertTrue("a firing the recording never saw models nothing",
                ConcolicRegionRuntime.explicitFaultCandidates(both, NAME, 3)
                        .isEmpty());
        assertTrue(ConcolicRegionRuntime.explicitFaultCandidates(
                both, "otherMarker", 1).isEmpty());

        // Without the ordinal both rows answer to the name, which is the
        // ambiguity the caller refuses on.
        List<ConcolicRegionRuntime.SymbolizeAction> unordinaled =
                Arrays.asList(
                        action(RuntimeSelectedRegionFinalizer
                                .EXPLICIT_SYMBOLIC_FAULT, NAME, -1),
                        action(RuntimeSelectedRegionFinalizer
                                .EXPLICIT_SYMBOLIC_FAULT, NAME, -1));
        assertEquals(2, ConcolicRegionRuntime.explicitFaultCandidates(
                unordinaled, NAME, 1).size());
    }

    /** The replay ordinal counts per activation and per declared symbol. */
    @Test
    public void theReplayOrdinalCountsPerActivationAndName() {
        ConcolicRegionRuntime.OccurrenceCounter counter =
                new ConcolicRegionRuntime.OccurrenceCounter();
        assertEquals(1, counter.explicitFault(NAME));
        assertEquals(2, counter.explicitFault(NAME));
        assertEquals(1, counter.explicitFault("otherMarker"));
        assertEquals(3, counter.explicitFault(NAME));
        // A new activation owns a new counter.
        assertEquals(1, new ConcolicRegionRuntime.OccurrenceCounter()
                .explicitFault(NAME));
    }

    private static ConcolicRegionRuntime.SymbolizeAction only(
            List<ConcolicRegionRuntime.SymbolizeAction> candidates) {
        assertEquals(1, candidates.size());
        return candidates.get(0);
    }

    private static ConcolicRegionRuntime.SymbolizeAction action(
            String sourceKind, String name, int replayOccurrence) {
        JsonObject json = json(name, replayOccurrence);
        json.addProperty("sourceKind", sourceKind);
        return new ConcolicRegionRuntime.SymbolizeAction(json);
    }

    private static JsonObject json(String name, int replayOccurrence) {
        JsonObject json = new JsonObject();
        json.addProperty("symbol", "REGION.ipc.in." + name + "."
                + replayOccurrence);
        json.addProperty("javaType", "boolean");
        json.addProperty("location", "CALL_RETURN");
        json.addProperty("rootKind", "ACTIVATION_LOCAL");
        json.addProperty("symbolicName", name);
        if (replayOccurrence >= 1) {
            json.addProperty("replayOccurrence", replayOccurrence);
        }
        return json;
    }
}
