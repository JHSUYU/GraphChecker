package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Assume;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * An unsat the case frontier decided is not an unsat about the program.
 *
 * <p>The reach driver fixes one case selector per advertised partition and
 * enumerates the alternatives.  Over a partition the formula asserts
 * unconditionally that is free: every model already picks one member, so
 * enumerating them decides nothing.  Over a partition the formula leaves to a
 * fault marker it is not free at all -- pinning a member answers for the
 * marker, and every attempt then refutes the fault-true half of the root
 * space for a reason that is about this driver.  hdfs-17899-bug1 is exactly
 * that shape: all 400 attempts pinned all nine fault-controlled selectors,
 * and each unsat core was {the polarity, the fault-control assertion, the
 * pin}.</p>
 */
public class FrontierPinnedUnsatTest {
    /** The formula is satisfiable; pinning the controlled case is not. */
    private static final String CONTROLLED_SMT =
            "(set-logic ALL)\n"
            + "(declare-const case_selector__c Bool)\n"
            + "(declare-const marker Bool)\n"
            + "(assert (! (and (=> marker (not case_selector__c))"
            + " (=> (not marker) (= (+ (ite case_selector__c 1 0)) 1)))"
            + " :named request_fault_control__CTRL_ONE))\n"
            + "(assert marker)\n"
            + "(check-sat)\n";

    @Test
    public void pinnedCoreSelectorsReadsBothLiteralShapes() {
        List<String> literals = Arrays.asList("case_selector__a",
                "(not case_selector__b)", "case_selector__c");

        assertEquals(Arrays.asList("case_selector__a", "case_selector__b"),
                BooleanReachConditionExtractor.Z3Solver.pinnedCoreSelectors(
                        "unsat\n(case_selector__a some_named_assertion"
                                + " case_selector__b)\n", literals));
        assertTrue(BooleanReachConditionExtractor.Z3Solver
                .pinnedCoreSelectors("unsat\n(only_a_named_assertion)\n",
                        literals).isEmpty());
        // A selector that was never pinned is not this driver's doing.
        assertTrue(BooleanReachConditionExtractor.Z3Solver
                .pinnedCoreSelectors("unsat\n(case_selector__z)\n",
                        literals).isEmpty());
        assertTrue(BooleanReachConditionExtractor.Z3Solver
                .pinnedCoreSelectors("sat\n", literals).isEmpty());
    }

    /** A conditional partition in the pinned set downgrades the verdict. */
    @Test
    public void anUnsatThatRestsOnAConditionalPinIsUndecided()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonArray partitions = partitions("case_selector__c");
        BooleanReachConditionExtractor.Z3Solver solver =
                new BooleanReachConditionExtractor.Z3Solver("z3", 20_000L,
                        partitions, partitions, 1);

        solver.check(CONTROLLED_SMT);

        assertEquals(BooleanReachConditionExtractor.FRONTIER_PINNED_UNSAT,
                solver.lastStatus());
        assertEquals(Collections.singletonList("case_selector__c"),
                solver.lastFrontierPins());
        // The probe is published, not only its conclusion.
        JsonObject probe = lastAttemptWithStrategyPrefix(solver,
                "FRONTIER_CORE_");
        assertEquals("unsat", probe.get("status").getAsString());
        assertEquals("[\"case_selector__c\"]",
                probe.get("unsatCorePinnedSelectors").toString());
    }

    /**
     * The same formula and the same pin, with the partition advertised as
     * one the formula asserts unconditionally, stays {@code unsat}: pinning
     * a member of an exhaustively enumerated partition decides nothing, so
     * downgrading there would withhold verdicts that are the program's.
     */
    @Test
    public void anUnconditionalPinDoesNotDowngradeTheVerdict()
            throws Exception {
        Assume.assumeTrue(z3Available());
        BooleanReachConditionExtractor.Z3Solver solver =
                new BooleanReachConditionExtractor.Z3Solver("z3", 20_000L,
                        partitions("case_selector__c"), new JsonArray(), 1);

        solver.check(CONTROLLED_SMT);

        assertEquals("unsat", solver.lastStatus());
        assertTrue(solver.lastFrontierPins().isEmpty());
    }

    /** A refutation the pin took no part in is still published as unsat. */
    @Test
    public void anUnsatIndependentOfThePinIsExonerated() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonArray partitions = partitions("case_selector__c");
        BooleanReachConditionExtractor.Z3Solver solver =
                new BooleanReachConditionExtractor.Z3Solver("z3", 20_000L,
                        partitions, partitions, 1);

        solver.check("(set-logic ALL)\n"
                + "(declare-const case_selector__c Bool)\n"
                + "(declare-const contradiction Bool)\n"
                + "(assert (! contradiction :named holds))\n"
                + "(assert (! (not contradiction) :named fails))\n"
                + "(check-sat)\n");

        assertEquals("unsat", solver.lastStatus());
        assertTrue(solver.lastFrontierPins().isEmpty());
    }

    /** A satisfiable valuation is unaffected by the review. */
    @Test
    public void aSatisfiableFrontierIsUntouched() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonArray partitions = partitions("case_selector__c");
        BooleanReachConditionExtractor.Z3Solver solver =
                new BooleanReachConditionExtractor.Z3Solver("z3", 20_000L,
                        partitions, partitions, 1);

        solver.check("(set-logic ALL)\n"
                + "(declare-const case_selector__c Bool)\n"
                + "(check-sat)\n");

        assertEquals("sat", solver.lastStatus());
        assertTrue(solver.lastFrontierPins().isEmpty());
    }

    /** ClaimPolicy counts the new status as an unanswered valuation. */
    @Test
    public void claimPolicyTreatsThePinnedVerdictAsUndecided() {
        JsonArray valuations = new JsonArray();
        valuations.add(valuation(true, "sat"));
        valuations.add(valuation(false,
                BooleanReachConditionExtractor.FRONTIER_PINNED_UNSAT));

        // A sat/not-sat pair one root apart is fault sensitivity only when
        // both rows were answered.
        assertTrue(!ClaimPolicy.faultSensitive(valuations, false));
        JsonArray decided = new JsonArray();
        decided.add(valuation(true, "sat"));
        decided.add(valuation(false, "unsat"));
        assertTrue(ClaimPolicy.faultSensitive(decided, false));
    }

    private static JsonObject valuation(boolean value, String status) {
        JsonObject row = new JsonObject();
        JsonArray values = new JsonArray();
        values.add(value);
        row.add("values", values);
        row.addProperty("status", status);
        return row;
    }

    private static JsonArray partitions(String selector) {
        return new JsonParser().parse("[[\"" + selector + "\"]]")
                .getAsJsonArray();
    }

    private static JsonObject lastAttemptWithStrategyPrefix(
            BooleanReachConditionExtractor.Z3Solver solver, String prefix) {
        JsonObject found = null;
        for (JsonElement element : solver.attempts()) {
            JsonObject row = element.getAsJsonObject();
            if (row.get("strategy").getAsString().startsWith(prefix)) {
                found = row;
            }
        }
        if (found == null) {
            throw new AssertionError("no attempt with strategy " + prefix);
        }
        return found;
    }

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "-version").start().waitFor()
                    == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}
