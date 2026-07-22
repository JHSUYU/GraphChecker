package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class BranchReplayContractTest {
    @Test
    public void complementIsCanonicalAndInvolutiveForBinaryPredicates() {
        JsonObject predicate = predicate("<", "REGION.IN.x", "7");
        JsonElement complement = BranchPredicateAlgebra.complement(predicate);
        assertEquals(">=", complement.getAsJsonObject().get("_op")
                .getAsString());
        assertTrue(BranchPredicateAlgebra.equivalent(predicate,
                BranchPredicateAlgebra.complement(complement)));
    }

    @Test
    public void witnessOwnsOneExclusiveEvidenceVariantAndStableHash() {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", 41L);
        event.addProperty("contextId", 9L);
        BranchWitness witness = BranchWitness.vmPc("ROOT#u7", "ROOT", 7,
                2, true, predicate("==", "REGION.IN.flag", "1"), 3,
                event);

        BranchWitness roundTrip = BranchWitness.fromJson(witness.toJson());
        assertEquals(witness.witnessId(), roundTrip.witnessId());
        assertEquals(3, roundTrip.vmPcIndex());
        assertEquals(BranchWitness.VM_PC, roundTrip.evidenceKind());
        assertFalse(roundTrip.evidence().has("certificate"));

        JsonObject tampered = witness.toJson();
        tampered.getAsJsonObject("site").addProperty("unitIndex", 8);
        expectRejected(tampered, "content hash");
    }

    @Test
    public void certifiedWitnessCannotAlsoClaimVmPcEvidence() {
        JsonObject certificate = new JsonObject();
        certificate.addProperty("certificateId", "CERT.1");
        BranchWitness witness = BranchWitness.certifiedNoPc("ROOT#u3",
                "ROOT", 3, 1, false,
                predicate("==", "REGION.IN.ref", "N"), certificate);
        assertEquals(BranchWitness.CERTIFIED_NO_PC,
                witness.evidenceKind());
        assertEquals(-1, witness.vmPcIndex());

        JsonObject malformed = witness.toJson();
        malformed.getAsJsonObject("evidence").addProperty("vmPcIndex", 0);
        expectRejected(malformed, "keys must be");
    }

    @Test
    public void flipOwnsPolarityAndPreservesOnlyOrderedPrefix() {
        BranchWitness first = witness("ROOT#u1", 1, 1, true, "<");
        BranchWitness second = witness("ROOT#u2", 2, 1, false, "==");
        BranchWitness source = witness("ROOT#u7", 7, 1, true, ">=");

        BranchReplayContract contract = BranchReplayContract.flip(
                Arrays.asList(first, second), source);
        assertFalse(contract.requiredTakenOutcome());
        assertEquals("<", contract.requiredSatisfiedPredicate()
                .getAsJsonObject().get("_op").getAsString());
        assertEquals(3, contract.requiredPathPredicates().size());
        assertEquals(first.witnessId(), contract.orderedPrefix().get(0)
                .witnessId());
        assertEquals(second.witnessId(), contract.orderedPrefix().get(1)
                .witnessId());

        JsonObject encoded = contract.toJson();
        assertFalse(encoded.has("prefix"));
        assertFalse(encoded.has("suffix"));
        assertFalse(encoded.has("observedOutcome"));
        assertFalse(encoded.has("desiredOutcome"));
        assertFalse(encoded.has("negatedCondition"));
        assertEquals(contract.contractId(),
                BranchReplayContract.fromJson(encoded).contractId());
    }

    @Test
    public void replayContractRejectsASecondPolarityAuthority() {
        BranchReplayContract contract = BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(),
                witness("ROOT#u7", 7, 1, true, "=="));
        JsonObject malformed = contract.toJson();
        malformed.getAsJsonObject("required").addProperty("takenOutcome",
                true);
        expectContractRejected(malformed, "exact source-witness flip");
    }

    private static BranchWitness witness(String site, int unit,
                                         int occurrence, boolean outcome,
                                         String operator) {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", unit * 100L + occurrence);
        event.addProperty("contextId", 17L);
        return BranchWitness.vmPc(site, "ROOT", unit, occurrence, outcome,
                predicate(operator, "REGION.IN.x", "7"), unit, event);
    }

    private static JsonObject predicate(String operator, String left,
                                        String right) {
        JsonObject result = new JsonObject();
        JsonObject rightExpression = new JsonObject();
        rightExpression.addProperty("_exp", right);
        rightExpression.addProperty("_type", "SymbolExpression");
        JsonObject leftExpression = new JsonObject();
        leftExpression.addProperty("_type", "SymbolExpression");
        leftExpression.addProperty("_exp", left);
        result.add("_right", rightExpression);
        result.addProperty("_op", operator);
        result.add("_left", leftExpression);
        result.addProperty("_type", "BinaryExpression");
        return result;
    }

    private static void expectRejected(JsonObject value, String fragment) {
        try {
            BranchWitness.fromJson(value);
            fail("expected malformed witness to be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(),
                    expected.getMessage().contains(fragment));
        }
    }

    private static void expectContractRejected(JsonObject value,
                                               String fragment) {
        try {
            BranchReplayContract.fromJson(value);
            fail("expected malformed contract to be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(),
                    expected.getMessage().contains(fragment));
        }
    }
}
