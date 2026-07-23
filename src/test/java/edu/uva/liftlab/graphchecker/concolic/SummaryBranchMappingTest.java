package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class SummaryBranchMappingTest {
    @Test
    public void witnessedRowHasOnlyOneAuthorityIndexAndPolicy() {
        JsonObject predicate = predicate("<");
        SummaryBranchMapping mapping = SummaryBranchMapping.witnessed(
                witness("ROOT#u7", 7, 1, true, predicate, 4), 2,
                SummaryBranchMapping.Policy.EXPLORE);

        JsonObject encoded = mapping.toJson();
        assertEquals(set("witness", "summaryPcIndex", "policy"),
                encoded.keySet());
        assertFalse(encoded.has("siteId"));
        assertFalse(encoded.has("conditionIndex"));
        assertFalse(encoded.has("condition"));
        assertFalse(encoded.has("conditionAuthority"));

        SummaryBranchMapping decoded =
                SummaryBranchMapping.fromJson(encoded);
        assertTrue(decoded.isWitnessed());
        assertEquals("ROOT#u7", decoded.siteId());
        assertEquals(2, decoded.summaryPcIndex());
        assertEquals(SummaryBranchMapping.Policy.EXPLORE,
                decoded.policy());
        assertTrue(mapping.witness().sameContent(decoded.witness()));
    }

    @Test
    public void concreteRowIsObservationOnlyAndDefensivelySerialized() {
        ExactConcreteBranchObservation observation =
                ExactConcreteBranchObservation.attested(
                        "ROOT#u9", "ROOT", 9, 3, false);
        SummaryBranchMapping mapping = SummaryBranchMapping.concrete(
                observation, SummaryBranchMapping.Policy.PATH_ASSUMPTION);

        JsonObject encoded = mapping.toJson();
        assertEquals(set("concreteObservation", "policy"),
                encoded.keySet());
        SummaryBranchMapping decoded =
                SummaryBranchMapping.fromJson(encoded);
        assertTrue(decoded.isConcreteObservation());
        assertEquals(-1, decoded.summaryPcIndex());
        assertEquals(3, decoded.occurrence());
        assertFalse(decoded.sourceTakenOutcome());

        encoded.getAsJsonObject("concreteObservation")
                .getAsJsonObject("site").addProperty("siteId", "TAMPERED");
        assertEquals("ROOT#u9", mapping.toJson()
                .getAsJsonObject("concreteObservation")
                .getAsJsonObject("site").get("siteId").getAsString());
    }

    @Test
    public void summaryParserOwnsPcAndRejectsAliasesOrDuplicateEvents() {
        JsonObject predicate = predicate("==");
        BranchWitness witness = witness("ROOT#u4", 4, 1, true,
                predicate, 8);
        JsonObject summary = summary(predicate,
                SummaryBranchMapping.witnessed(witness, 0,
                        SummaryBranchMapping.Policy.EXPLORE).toJson());

        List<SummaryBranchMapping> decoded =
                SummaryBranchMapping.fromSummary(summary);
        assertEquals(1, decoded.size());
        assertEquals(0, decoded.get(0).summaryPcIndex());

        JsonObject aliased = summary.deepCopy();
        aliased.getAsJsonArray("branchMappings").get(0).getAsJsonObject()
                .addProperty("siteId", "ROOT#u4");
        expectSummaryRejected(aliased, "keys must be");

        JsonObject duplicate = summary.deepCopy();
        duplicate.getAsJsonArray("branchMappings").add(
                SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                "ROOT#u4", "ROOT", 4, 1, true),
                        SummaryBranchMapping.Policy.EXPLORE).toJson());
        expectSummaryRejected(duplicate, "duplicate branch event");

        JsonObject mismatch = summary.deepCopy();
        mismatch.getAsJsonArray("pathCondition").set(0, predicate(">"));
        expectSummaryRejected(mismatch, "does not own summary PC");
    }

    @Test
    public void malformedPolicyAndIndexFailClosed() {
        JsonObject encoded = SummaryBranchMapping.witnessed(
                witness("ROOT#u2", 2, 1, true, predicate("<"), 0), 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson();
        encoded.addProperty("policy", "LEGACY_DEFAULT");
        expectRowRejected(encoded, "unsupported branch policy");

        encoded = SummaryBranchMapping.witnessed(
                witness("ROOT#u2", 2, 1, true, predicate("<"), 0), 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson();
        encoded.addProperty("summaryPcIndex", -1);
        expectRowRejected(encoded, "nonnegative");
    }

    private static JsonObject summary(JsonObject predicate,
                                      JsonObject mapping) {
        JsonObject summary = new JsonObject();
        JsonArray path = new JsonArray();
        path.add(predicate.deepCopy());
        summary.add("pathCondition", path);
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        summary.add("branchMappings", mappings);
        return summary;
    }

    private static BranchWitness witness(
            String site, int unit, int occurrence, boolean outcome,
            JsonObject predicate, int vmPcIndex) {
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization",
                BranchWitness.IDENTITY_NORMALIZATION);
        return BranchWitness.vmPc(site, "ROOT", unit, occurrence, outcome,
                predicate, vmPcIndex, metadata);
    }

    private static JsonObject predicate(String operator) {
        JsonObject result = new JsonObject();
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "M_I_ROOT");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_7");
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static Set<String> set(String... values) {
        return new LinkedHashSet<>(Arrays.asList(values));
    }

    private static void expectSummaryRejected(
            JsonObject value, String fragment) {
        try {
            SummaryBranchMapping.fromSummary(value);
            fail("expected malformed summary to be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(),
                    expected.getMessage().contains(fragment));
        }
    }

    private static void expectRowRejected(
            JsonObject value, String fragment) {
        try {
            SummaryBranchMapping.fromJson(value);
            fail("expected malformed row to be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(),
                    expected.getMessage().contains(fragment));
        }
    }
}
