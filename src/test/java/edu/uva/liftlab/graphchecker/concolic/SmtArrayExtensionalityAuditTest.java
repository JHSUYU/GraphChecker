package edu.uva.liftlab.graphchecker.concolic;

import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SmtArrayExtensionalityAuditTest {
    private static final String PRELUDE =
            "(set-logic ALL)\n"
                    + "(declare-datatypes () ((Box (box (items (Array Int Int))))))\n"
                    + "(declare-const a Box)\n"
                    + "(declare-const b Box)\n";

    @Test
    public void admitsPositiveStateEqualitiesAndScalarDisequalities() {
        String smt = PRELUDE
                + "(define-fun scalarDifferent ((x Int) (y Int)) Bool"
                + " (not (= x y)))\n"
                + "(assert (=> (scalarDifferent 1 2) (= a b)))\n";

        assertTrue(SmtArrayExtensionalityAudit
                .provesExtensionalityRedundant(smt));
    }

    @Test
    public void rejectsDirectAndImpliedStateDisequalities() {
        assertFalse(SmtArrayExtensionalityAudit
                .provesExtensionalityRedundant(PRELUDE
                        + "(assert (not (= a b)))\n"));
        assertFalse(SmtArrayExtensionalityAudit
                .provesExtensionalityRedundant(PRELUDE
                        + "(assert (=> (= a b) false))\n"));
        assertFalse(SmtArrayExtensionalityAudit
                .provesExtensionalityRedundant(PRELUDE
                        + "(assert (distinct a b))\n"));
    }

    @Test
    public void rejectsArrayEqualityHiddenBehindBooleanEquivalence() {
        String smt = PRELUDE
                + "(declare-const choose Bool)\n"
                + "(assert (= choose (= a b)))\n";

        assertFalse(SmtArrayExtensionalityAudit
                .provesExtensionalityRedundant(smt));
    }

    @Test
    public void rejectsArrayDisequalityInBareZeroArityDefinition() {
        String smt = PRELUDE
                + "(define-fun bad () Bool (not (= a b)))\n"
                + "(assert bad)\n";

        assertFalse(SmtArrayExtensionalityAudit
                .provesExtensionalityRedundant(smt));
    }

    @Test
    public void rejectsUninterpretedArrayObserversAndUnknownSorts() {
        String smt = PRELUDE
                + "(declare-fun observes (Box) Bool)\n"
                + "(assert (observes a))\n";
        assertFalse(SmtArrayExtensionalityAudit
                .provesExtensionalityRedundant(smt));
        assertFalse(SmtArrayExtensionalityAudit
                .provesExtensionalityRedundant(PRELUDE
                        + "(assert (not (= mystery 1)))\n"));
    }

    @Test
    public void failsClosedOnMalformedInput() {
        assertFalse(SmtArrayExtensionalityAudit
                .provesExtensionalityRedundant("(declare-const a (Array Int Int)"));
    }
}
