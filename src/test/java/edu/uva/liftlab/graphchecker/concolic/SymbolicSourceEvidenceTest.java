package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class SymbolicSourceEvidenceTest {
    private static final String SOURCE = "HDFS11741.NAMENODE.CURRENT_KEY_ID";
    private static final String OCCURRENCE =
            "cluster0/nn0#epoch1/region/REGION.2aed#1";
    private static final String FIELD =
            "<org.apache.hadoop.security.token.delegation.DelegationKey: int keyId>";
    private static final String PHASE_A = "SOURCE_PHASE.publish-a";
    private static final String PHASE_B = "SOURCE_PHASE.publish-b";

    @Test
    public void duplicateCaseEvidenceNamesOneCanonicalSource() {
        String raw = raw(PHASE_A, SOURCE, "shared");
        JsonObject first = owner(event(raw, PHASE_A, SOURCE, OCCURRENCE));
        JsonObject replay = owner(event(raw, PHASE_A, SOURCE, OCCURRENCE));

        Map<String, String> identities =
                SymbolicSourceEvidence.rawSymbolIdentities(
                        Arrays.asList(first, replay));

        assertEquals(1, identities.size());
        assertEquals(PHASE_A + "\n" + SOURCE, identities.get(raw));
    }

    @Test
    public void rawSymbolAndSourceIdentityAreBothOneToOne() {
        String shared = raw(PHASE_A, SOURCE, "shared");
        JsonObject conflicting = event(raw(PHASE_A, "OTHER", "shared"),
                PHASE_A, "OTHER", OCCURRENCE);
        conflicting.addProperty("rawSymbol", shared);
        conflicting.getAsJsonObject("expression")
                .addProperty("_exp", shared);
        assertMalformed(Arrays.asList(
                owner(event(shared, PHASE_A, SOURCE, OCCURRENCE)),
                owner(conflicting)));
        assertMalformed(Arrays.asList(
                owner(event(raw(PHASE_A, SOURCE, "first"), PHASE_A,
                        SOURCE, OCCURRENCE)),
                owner(event(raw(PHASE_A, SOURCE, "second"), PHASE_A,
                        SOURCE, OCCURRENCE))));
    }

    @Test
    public void twoPublishPhasesInOneOccurrenceStayDistinct() {
        String first = raw(PHASE_A, SOURCE, "first");
        String second = raw(PHASE_B, SOURCE, "second");

        Map<String, String> identities =
                SymbolicSourceEvidence.rawSymbolIdentities(Arrays.asList(
                        owner(event(first, PHASE_A, SOURCE, OCCURRENCE)),
                        owner(event(second, PHASE_B, SOURCE, OCCURRENCE))));

        assertEquals(2, identities.size());
        assertEquals(PHASE_A + "\n" + SOURCE, identities.get(first));
        assertEquals(PHASE_B + "\n" + SOURCE, identities.get(second));
    }

    @Test
    public void oneOwnerCannotRepeatOnePhaseEvent() {
        String raw = raw(PHASE_A, SOURCE, "shared");
        JsonObject duplicate = new JsonObject();
        JsonArray rows = new JsonArray();
        rows.add(event(raw, PHASE_A, SOURCE, OCCURRENCE));
        rows.add(event(raw, PHASE_A, SOURCE, OCCURRENCE));
        duplicate.add(SymbolicSourceEvidence.FIELD, rows);

        assertMalformed(Collections.singletonList(duplicate));
    }

    @Test
    public void constantsAndTruncatedExpressionsCannotClaimSourceAuthority() {
        JsonObject constant = symbol("Y_I_1307341805");
        constant.addProperty("_type", "ConstExpr");
        assertEventRejected(constant);

        JsonObject truncated = new JsonObject();
        truncated.addProperty("_type", "TruncatedExpression");
        truncated.addProperty("_java_type", "int");
        truncated.addProperty("_exp", "M_I_field_SRC.truncated");
        assertEventRejected(truncated);
    }

    @Test
    public void expressionTypeMustExactlyMatchTheDeclaredField() {
        JsonObject intExpression = symbol(raw(PHASE_A, SOURCE, "typed"));
        try {
            SymbolicSourceEvidence.event(PHASE_A, SOURCE, OCCURRENCE,
                    "<example.Owner: long value>", intExpression);
            fail("expected field/expression width mismatch rejection");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains(
                    "field type differs from VM expression"));
        }
    }

    @Test
    public void composerScopeKeyIsGlobalOnlyForAttestedSource() {
        String raw = raw(PHASE_A, SOURCE, "shared");
        JsonObject attested = owner(event(raw, PHASE_A, SOURCE,
                OCCURRENCE));

        assertEquals(
                ConcolicSmtComposer.symbolScopeKeyForTests(
                        Collections.singletonList(attested),
                        raw, "case-a"),
                ConcolicSmtComposer.symbolScopeKeyForTests(
                        Collections.singletonList(attested),
                        raw, "case-b"));
        assertTrue(!ConcolicSmtComposer.symbolScopeKeyForTests(
                        Collections.singletonList(attested),
                        "M_I_field_ordinary", "case-a").equals(
                ConcolicSmtComposer.symbolScopeKeyForTests(
                        Collections.singletonList(attested),
                        "M_I_field_ordinary", "case-b")));
    }

    private static JsonObject owner(JsonObject event) {
        JsonObject owner = new JsonObject();
        JsonArray rows = new JsonArray();
        rows.add(event);
        owner.add(SymbolicSourceEvidence.FIELD, rows);
        return owner;
    }

    private static JsonObject event(String raw, String phase, String source,
                                    String occurrence) {
        return SymbolicSourceEvidence.event(phase, source, occurrence, FIELD,
                symbol(raw));
    }

    private static String raw(String phase, String source, String suffix) {
        return "M_I_field_" + SymbolicSourceEvidence.engineLabelForPhase(
                phase, source) + "_" + suffix;
    }

    private static JsonObject symbol(String raw) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "int");
        expression.addProperty("_exp", raw);
        return expression;
    }

    private static void assertMalformed(Iterable<JsonObject> owners) {
        try {
            SymbolicSourceEvidence.rawSymbolIdentities(owners);
            fail("expected malformed source evidence");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), !expected.getMessage().isEmpty());
        }
    }

    private static void assertEventRejected(JsonObject expression) {
        try {
            SymbolicSourceEvidence.event(PHASE_A, SOURCE, OCCURRENCE,
                    FIELD, expression);
            fail("expected source expression rejection");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), !expected.getMessage().isEmpty());
        }
    }
}
