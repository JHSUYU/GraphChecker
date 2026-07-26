package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class BranchReplayContractTest {
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
        assertEquals(encoded, BranchReplayContract.fromJson(encoded)
                .toJson());
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

        List<String> valid =
                BranchReplayObservationValidator.validate(contract,
                        Arrays.asList(replayedPrefix, replayedTarget));
        assertTrue(valid.toString(), valid.isEmpty());

        List<String> wrong =
                BranchReplayObservationValidator.validate(contract,
                        Arrays.asList(replayedTarget, replayedPrefix));
        assertFalse(wrong.isEmpty());
        assertTrue(wrong.toString(), wrong.toString().contains(
                "TARGET_BEFORE_PREFIX"));
    }

    @Test
    public void explicitFieldBindingIsSolverContextNotBranchEvidence() {
        JsonObject field = new JsonObject();
        field.addProperty("_type", "FieldAccessExpression");
        field.addProperty("_java_type", "I");
        field.addProperty("ownerClass", "example.Input");
        field.addProperty("fieldOffset", 24);
        field.add("owner", symbol("M_L'example.Input'_1"));
        JsonObject binding = predicate("==", field,
                symbol("M_I_field_input"));
        binding.addProperty("_code_position",
                "static void java.lang.System.symbolizeField"
                        + "(jobject, jobject, jobject):-1");
        JsonArray path = new JsonArray();
        path.add(binding);
        path.add(predicate(">", "M_I_field_input", "7"));

        SolverPathContext context = SolverPathContext.fromPath(path,
                Collections.<Integer>emptySet(), 1);

        assertEquals(1, context.size());
        assertEquals(binding, context.expressions().get(0));
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
        return predicate(operator, symbol(left), symbol(right));
    }

    private static JsonObject predicate(String operator,
                                        JsonObject leftExpression,
                                        JsonObject rightExpression) {
        JsonObject result = new JsonObject();
        result.add("_right", rightExpression);
        result.addProperty("_op", operator);
        result.add("_left", leftExpression);
        result.addProperty("_type", "BinaryExpression");
        return result;
    }

    private static JsonObject symbol(String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_exp", value);
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
