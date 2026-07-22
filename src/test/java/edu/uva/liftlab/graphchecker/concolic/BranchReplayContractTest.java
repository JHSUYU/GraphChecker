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
    public void witnessRoundTripPreservesPredicateAndPcBinding() {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", 41L);
        event.addProperty("contextId", 9L);
        BranchWitness witness = BranchWitness.vmPc("ROOT#u7", "ROOT", 7,
                2, true, predicate("==", "REGION.IN.flag", "1"), 3,
                event);

        BranchWitness roundTrip = BranchWitness.fromJson(witness.toJson());
        assertEquals(3, roundTrip.vmPcIndex());
        assertEquals(BranchWitness.IDENTITY_NORMALIZATION,
                roundTrip.predicateNormalization());
        assertTrue(witness.sameContent(roundTrip));
        assertFalse(roundTrip.toJson().has("witnessId"));
        assertFalse(roundTrip.toJson().has("evidence"));

        JsonObject tampered = witness.toJson();
        tampered.remove("vmPcIndex");
        expectRejected(tampered, "keys must be");
    }

    @Test
    public void nestedUnaryMinusRoundTripsWithoutWireHashes() {
        JsonObject input = new JsonObject();
        input.addProperty("_type", "SymbolExpression");
        input.addProperty("_java_type", "I");
        input.addProperty("_exp", "M_I_field_REGION.4.in.8_Producer");

        JsonObject negated = new JsonObject();
        negated.addProperty("_type", "BinaryExpression");
        negated.addProperty("_op", "-");
        negated.add("_right", input);

        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "M_I_field_REGION.4.in.6_Producer");

        JsonObject subtraction = new JsonObject();
        subtraction.addProperty("_type", "BinaryExpression");
        subtraction.add("_left", left);
        subtraction.addProperty("_op", "-");
        subtraction.add("_right", negated);

        JsonObject ten = new JsonObject();
        ten.addProperty("_type", "ConstExpr");
        ten.addProperty("_java_type", "I");
        ten.addProperty("_exp", "Y_I_10");

        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.add("_left", subtraction);
        predicate.addProperty("_op", ">");
        predicate.add("_right", ten);

        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization", "IDENTITY");
        BranchWitness witness = BranchWitness.vmPc("ROOT#u26", "ROOT",
                26, 1, false, predicate, 4, metadata);
        JsonObject encoded = witness.toJson();
        BranchWitness decoded = BranchWitness.fromJson(encoded);

        assertTrue(witness.sameContent(decoded));
        JsonObject decodedUnary = decoded.sourceSatisfiedPredicate()
                .getAsJsonObject().getAsJsonObject("_left")
                .getAsJsonObject("_right");
        assertEquals("-", decodedUnary.get("_op").getAsString());
        assertFalse(decodedUnary.has("_left"));
        assertFalse(encoded.has("witnessId"));
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
        assertEquals(first.siteId(), contract.orderedPrefix().get(0)
                .siteId());
        assertEquals(second.siteId(), contract.orderedPrefix().get(1)
                .siteId());

        JsonObject encoded = contract.toJson();
        assertFalse(encoded.has("prefix"));
        assertFalse(encoded.has("suffix"));
        assertFalse(encoded.has("observedOutcome"));
        assertFalse(encoded.has("desiredOutcome"));
        assertFalse(encoded.has("negatedCondition"));
        assertFalse(encoded.has("required"));
        assertFalse(encoded.has("contractId"));
        assertTrue(contract.sameContent(
                BranchReplayContract.fromJson(encoded)));
    }

    @Test
    public void replayContractDerivesPolarityWithoutASecondJsonAuthority() {
        BranchReplayContract contract = BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(),
                witness("ROOT#u7", 7, 1, true, "=="));
        JsonObject encoded = contract.toJson();
        assertFalse(encoded.has("required"));
        BranchReplayContract decoded = BranchReplayContract.fromJson(encoded);
        assertFalse(decoded.requiredTakenOutcome());
        assertEquals("!=", decoded.requiredSatisfiedPredicate()
                .getAsJsonObject().get("_op").getAsString());
    }

    @Test
    public void replayContractRejectsDuplicateBranchEventIdentities() {
        BranchWitness prefix = witness("ROOT#u7", 7, 1, true, ">");
        BranchWitness sameEventDifferentEvidence = witness("ROOT#u7", 7,
                1, false, "<=");
        try {
            BranchReplayContract.flip(
                    Collections.singletonList(prefix),
                    sameEventDifferentEvidence);
            fail("expected duplicate event identity to be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains("source branch event"));
        }
    }

    @Test
    public void oneValidatorChecksOrderedPrefixAndRequiredPredicate() {
        BranchWitness prefix = witness("ROOT#u1", 1, 1, true, "<");
        BranchWitness source = witness("ROOT#u7", 7, 1, true, ">=");
        BranchReplayContract contract = BranchReplayContract.flip(
                Collections.singletonList(prefix), source);
        BranchWitness replayedPrefix = witness("ROOT#u1", 1, 1, true,
                "<");
        BranchWitness replayedTarget = witness("ROOT#u7", 7, 1, false,
                "<");

        BranchReplayObservationValidator.Result valid =
                BranchReplayObservationValidator.validate(contract,
                        Arrays.asList(replayedPrefix, replayedTarget));
        assertTrue(valid.toJson().toString(), valid.valid());

        BranchReplayObservationValidator.Result wrong =
                BranchReplayObservationValidator.validate(contract,
                        Arrays.asList(replayedTarget, replayedPrefix));
        assertFalse(wrong.valid());
        assertTrue(wrong.failures().toString(), wrong.failures().toString()
                .contains("TARGET_BEFORE_PREFIX"));
    }

    @Test
    public void replayIdentitySurvivesNullSensitiveVmSymbolNames() {
        JsonObject source = predicate("!=",
                "M_L'String'_REGION.4.in.6_ProducerThread", "N");
        source.getAsJsonObject("_left").addProperty("_java_type",
                "java/lang/String");
        JsonObject replay = predicate("!=",
                "M_L_field_REGION.4.in.6_ProducerThread", "N");
        replay.getAsJsonObject("_left").addProperty("_java_type", "L");

        assertFalse(BranchPredicateAlgebra.equivalent(source, replay));
        assertTrue(BranchPredicateAlgebra.replayEquivalent(source, replay));

        JsonObject otherInput = predicate("!=",
                "M_L_field_REGION.4.in.7_ProducerThread", "N");
        otherInput.getAsJsonObject("_left").addProperty("_java_type", "L");
        assertFalse(BranchPredicateAlgebra.replayEquivalent(source,
                otherInput));
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

}
