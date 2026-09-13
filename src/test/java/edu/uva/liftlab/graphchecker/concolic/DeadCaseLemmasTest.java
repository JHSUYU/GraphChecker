package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * A case arm the composed formula refutes becomes a named lemma; every other
 * arm, and every formula the pass must not touch, is left exactly as it was.
 */
public class DeadCaseLemmasTest {

    private static final String NL = System.lineSeparator();
    /** {@code b} is dead: it forces {@code x > 5} while the formula says {@code x < 0}. */
    private static final String FORMULA = String.join(NL,
            "(set-option :smt.arith.solver 2)",
            "(declare-const case_selector__a Bool)",
            "(declare-const case_selector__b Bool)",
            "(declare-const case_selector__c Bool)",
            "(declare-const x Int)",
            "(assert (! (= (+ (ite case_selector__a 1 0)"
                    + " (ite case_selector__b 1 0)) 1)"
                    + " :named region_case_selector_partition_r_1))",
            "(assert (! (= (+ (ite case_selector__c 1 0)) 1)"
                    + " :named region_case_selector_partition_r_2))",
            "(assert (! (=> case_selector__b (> x 5))"
                    + " :named case_selector_definition_b))",
            "(assert (! (=> case_selector__a (< x 3))"
                    + " :named case_selector_definition_a))",
            "(assert (< x 0))",
            "(check-sat)") + NL;
    private static final List<List<String>> PARTITIONS = Arrays.asList(
            Arrays.asList("case_selector__a", "case_selector__b"),
            Collections.singletonList("case_selector__c"));

    @Test
    public void aRefutedArmBecomesANamedLemmaAndNothingElseChanges()
            throws Exception {
        Assume.assumeTrue(z3Available());
        DeadCaseLemmas.Result result = DeadCaseLemmas.prove(FORMULA,
                PARTITIONS, Paths.get("z3"),
                DeadCaseLemmas.DEFAULT_ARM_RLIMIT);

        String lemma = DeadCaseLemmas.lemmaAssertion("case_selector__b");
        assertEquals("(assert (! (not case_selector__b) :named "
                + DeadCaseLemmas.lemmaName("case_selector__b") + "))", lemma);
        assertTrue(lemma, result.smtLib.contains(lemma + NL + "(check-sat)"));
        assertFalse(result.smtLib.contains("(not case_selector__a)"));
        assertFalse(result.smtLib.contains("(not case_selector__c)"));
        // The lemma is the only addition: the original text is a prefix.
        String original = FORMULA.substring(0,
                FORMULA.lastIndexOf("(check-sat)"));
        assertTrue(result.smtLib.startsWith(original));
        assertTrue(result.smtLib.endsWith("(check-sat)" + NL));

        JsonObject ledger = result.ledger;
        assertEquals(DeadCaseLemmas.KIND, ledger.get("kind").getAsString());
        assertEquals("", ledger.get("skipped").getAsString());
        assertEquals(2, ledger.get("probedArms").getAsInt());
        JsonArray lemmas = ledger.getAsJsonArray("lemmas");
        assertEquals(1, lemmas.size());
        JsonObject row = lemmas.get(0).getAsJsonObject();
        assertEquals("case_selector__b", row.get("selector").getAsString());
        assertEquals(DeadCaseLemmas.lemmaName("case_selector__b"),
                row.get("lemma").getAsString());
        assertEquals(2, row.getAsJsonArray("partition").size());
        JsonArray probes = ledger.getAsJsonArray("probes");
        assertEquals(2, probes.size());
        assertEquals("sat", status(probes, "case_selector__a"));
        assertEquals("unsat", status(probes, "case_selector__b"));

        // The lemma preserves the model set: the formula is still sat, and
        // the arm it names is still refuted.
        assertEquals("sat", check(result.smtLib));
        assertEquals("unsat", check(result.smtLib.replace("(check-sat)",
                "(assert case_selector__b)" + NL + "(check-sat)")));
    }

    @Test
    public void withoutASolverTheFormulaIsUntouched() throws Exception {
        DeadCaseLemmas.Result result = DeadCaseLemmas.prove(FORMULA,
                PARTITIONS, null, DeadCaseLemmas.DEFAULT_ARM_RLIMIT);
        assertSame(FORMULA, result.smtLib);
        assertEquals("NO_SOLVER", result.ledger.get("skipped").getAsString());
        assertEquals(0, result.ledger.get("probedArms").getAsInt());
        assertEquals(0, result.ledger.getAsJsonArray("lemmas").size());
    }

    @Test
    public void aZeroBudgetDisablesThePass() throws Exception {
        DeadCaseLemmas.Result result = DeadCaseLemmas.prove(FORMULA,
                PARTITIONS, Paths.get("/nonexistent/z3"), 0L);
        assertSame(FORMULA, result.smtLib);
        assertEquals("DISABLED", result.ledger.get("skipped").getAsString());
    }

    /** A fail-closed formula refutes every arm; none of that is a lemma. */
    @Test
    public void aFailClosedFormulaIsNotProbed() throws Exception {
        String failClosed = FORMULA.replace("(check-sat)",
                DeadCaseLemmas.FAIL_CLOSED_MARKER + ": unsupported" + NL
                        + "(check-sat)");
        // The solver path does not exist: probing would fail loudly.
        DeadCaseLemmas.Result result = DeadCaseLemmas.prove(failClosed,
                PARTITIONS, Paths.get("/nonexistent/z3"),
                DeadCaseLemmas.DEFAULT_ARM_RLIMIT);
        assertSame(failClosed, result.smtLib);
        assertEquals("FAIL_CLOSED",
                result.ledger.get("skipped").getAsString());
    }

    /** A partition with one arm has no choice to refute. */
    @Test
    public void singletonPartitionsAreNotProbed() throws Exception {
        DeadCaseLemmas.Result result = DeadCaseLemmas.prove(FORMULA,
                Collections.singletonList(
                        Collections.singletonList("case_selector__c")),
                Paths.get("/nonexistent/z3"),
                DeadCaseLemmas.DEFAULT_ARM_RLIMIT);
        assertSame(FORMULA, result.smtLib);
        assertEquals("NO_MULTI_ARM_PARTITION",
                result.ledger.get("skipped").getAsString());
    }

    private static String status(JsonArray probes, String selector) {
        for (int index = 0; index < probes.size(); index++) {
            JsonObject probe = probes.get(index).getAsJsonObject();
            if (selector.equals(probe.get("selector").getAsString())) {
                return probe.get("status").getAsString();
            }
        }
        throw new AssertionError("no probe for " + selector);
    }

    private static String check(String smt) throws Exception {
        return ConcolicConstraintSolver.run(Paths.get("z3"), smt, 20_000L)
                .status();
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
