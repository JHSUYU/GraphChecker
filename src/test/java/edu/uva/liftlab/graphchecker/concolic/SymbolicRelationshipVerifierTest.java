package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SymbolicRelationshipVerifierTest {
    @Test
    public void labelsOnlyUnsatNegationsAsDerived() throws Exception {
        JsonObject candidates = new JsonObject();
        candidates.addProperty("eligibleForAutomaticVerification", true);
        JsonArray relationships = new JsonArray();
        relationships.add(candidate("positive_x", "(> x 0)", true));
        relationships.add(candidate("x_is_four", "(= x 4)", false));
        candidates.add("relationships", relationships);

        SymbolicRelationshipVerifier.Solver solver =
                new SymbolicRelationshipVerifier.Solver() {
                    @Override
                    public SymbolicRelationshipVerifier.SolverResult check(
                            String smt) throws IOException {
                        if (smt.contains("(not (> x 0))")) {
                            return new SymbolicRelationshipVerifier.SolverResult(
                                    "unsat", "unsat");
                        }
                        return new SymbolicRelationshipVerifier.SolverResult(
                                "sat", "sat");
                    }
                };

        SymbolicRelationshipVerifier.Verification verification =
                SymbolicRelationshipVerifier.verify(
                        "(declare-const x Int)\n(assert (= x 3))\n"
                                + "(check-sat)\n",
                        candidates, solver);
        JsonObject report = verification.report;

        assertTrue(report.get("baseSatisfiable").getAsBoolean());
        assertTrue(report.get("complete").getAsBoolean());
        assertEquals(1, report.get("provedRelationshipCount").getAsInt());
        assertEquals(1, report.get("notEntailedRelationshipCount").getAsInt());
        JsonArray rows = report.getAsJsonArray("relationships");
        assertEquals("DERIVED", rows.get(0).getAsJsonObject()
                .get("classification").getAsString());
        assertFalse(rows.get(0).getAsJsonObject()
                .get("concreteModelUsed").getAsBoolean());
        assertEquals("CANDIDATE_NOT_DERIVED", rows.get(1).getAsJsonObject()
                .get("classification").getAsString());
    }

    @Test
    public void rejectsVacuousProofWhenBaseIsUnsatisfiable()
            throws Exception {
        JsonObject candidates = new JsonObject();
        candidates.addProperty("eligibleForAutomaticVerification", true);
        JsonArray relationships = new JsonArray();
        relationships.add(candidate("anything", "true", true));
        candidates.add("relationships", relationships);

        SymbolicRelationshipVerifier.Verification verification =
                SymbolicRelationshipVerifier.verify("(assert false)\n",
                        candidates,
                        new SymbolicRelationshipVerifier.Solver() {
                            @Override
                            public SymbolicRelationshipVerifier.SolverResult
                            check(String smt) {
                                return new SymbolicRelationshipVerifier
                                        .SolverResult("unsat", "unsat");
                            }
                        });

        assertFalse(verification.report.get("complete").getAsBoolean());
        assertEquals("NOT_CHECKED_BASE_NOT_SAT",
                verification.report.getAsJsonArray("relationships").get(0)
                        .getAsJsonObject().get("status").getAsString());
    }

    @Test
    public void refusesToProveCandidatesFromIncompleteComposition()
            throws Exception {
        JsonObject candidates = new JsonObject();
        candidates.addProperty("eligibleForAutomaticVerification", false);
        JsonArray relationships = new JsonArray();
        relationships.add(candidate("trivially_true", "true", true));
        candidates.add("relationships", relationships);

        SymbolicRelationshipVerifier.Verification verification =
                SymbolicRelationshipVerifier.verify("(assert true)\n",
                        candidates,
                        new SymbolicRelationshipVerifier.Solver() {
                            @Override
                            public SymbolicRelationshipVerifier.SolverResult
                            check(String smt) {
                                throw new AssertionError(
                                        "solver must not run for an ineligible candidate set");
                            }
                        });

        JsonObject report = verification.report;
        assertFalse(report.get("automaticVerificationAttempted")
                .getAsBoolean());
        assertFalse(report.get("complete").getAsBoolean());
        assertEquals("RELATIONSHIP_PROOF_BLOCKED_BY_COMPOSITION_GAPS",
                report.get("status").getAsString());
        assertEquals("NOT_ELIGIBLE_INCOMPLETE_COMPOSITION",
                report.getAsJsonArray("relationships").get(0)
                        .getAsJsonObject().get("status").getAsString());
    }

    private static JsonObject candidate(String id, String formula,
                                        boolean required) {
        JsonObject value = new JsonObject();
        value.addProperty("relationshipId", id);
        value.addProperty("formula", formula);
        value.addProperty("required", required);
        return value;
    }
}
