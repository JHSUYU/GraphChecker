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

    @Test
    public void duplicateCaseEvidenceNamesOneCanonicalSource() {
        JsonObject first = owner(event("M_I_field_SRC.shared", SOURCE,
                OCCURRENCE));
        JsonObject replay = owner(event("M_I_field_SRC.shared", SOURCE,
                OCCURRENCE));

        Map<String, String> identities =
                SymbolicSourceEvidence.rawSymbolIdentities(
                        Arrays.asList(first, replay));

        assertEquals(1, identities.size());
        assertEquals(OCCURRENCE + "\n" + SOURCE,
                identities.get("M_I_field_SRC.shared"));
    }

    @Test
    public void rawSymbolAndSourceIdentityAreBothOneToOne() {
        assertMalformed(Arrays.asList(
                owner(event("M_I_field_SRC.shared", SOURCE, OCCURRENCE)),
                owner(event("M_I_field_SRC.shared", "OTHER", OCCURRENCE))));
        assertMalformed(Arrays.asList(
                owner(event("M_I_field_SRC.first", SOURCE, OCCURRENCE)),
                owner(event("M_I_field_SRC.second", SOURCE, OCCURRENCE))));
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
    public void composerScopeKeyIsGlobalOnlyForAttestedSource() {
        JsonObject attested = owner(event("M_I_field_SRC.shared", SOURCE,
                OCCURRENCE));

        assertEquals(
                ConcolicSmtComposer.symbolScopeKeyForTests(
                        Collections.singletonList(attested),
                        "M_I_field_SRC.shared", "case-a"),
                ConcolicSmtComposer.symbolScopeKeyForTests(
                        Collections.singletonList(attested),
                        "M_I_field_SRC.shared", "case-b"));
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

    private static JsonObject event(String raw, String source,
                                    String occurrence) {
        return SymbolicSourceEvidence.event(source, occurrence, FIELD,
                symbol(raw));
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
            SymbolicSourceEvidence.event(SOURCE, OCCURRENCE, FIELD,
                    expression);
            fail("expected source expression rejection");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), !expected.getMessage().isEmpty());
        }
    }
}
