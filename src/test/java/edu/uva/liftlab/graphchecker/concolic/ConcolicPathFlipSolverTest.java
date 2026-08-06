package edu.uva.liftlab.graphchecker.concolic;

import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicPathFlipSolverTest {
    @Test
    public void anUnmaterializableFlipIsRecordedRatherThanFailed() {
        // A flip the replay cannot materialize is an explored-and-abandoned
        // proposal, exactly like one whose IR the encoder cannot express.
        // Failing the process there kills a whole campaign over a single
        // exploration proposal that decides nothing.
        assertTrue(ConcolicPathFlipSolver.terminalExplorationOutcome(
                "MATERIALIZATION_GAP"));
        assertTrue(ConcolicPathFlipSolver.terminalExplorationOutcome(
                "UNSUPPORTED"));
        assertTrue(ConcolicPathFlipSolver.terminalExplorationOutcome(
                "SAT_MODEL_READY"));
        assertTrue(ConcolicPathFlipSolver.terminalExplorationOutcome(
                "UNSAT"));

        // A solver that reached no verdict still fails the process.
        assertFalse(ConcolicPathFlipSolver.terminalExplorationOutcome(
                "SOLVER_ERROR"));
        assertFalse(ConcolicPathFlipSolver.terminalExplorationOutcome(""));
    }
}
