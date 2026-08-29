package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
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
        // Wave 3 C1: the mint entry, not the source phase, is the identity.
        assertEquals(SOURCE + "\n" + OCCURRENCE + "\n#1",
                identities.get(raw));
    }

    @Test
    public void oneVmRootSurvivingAcrossActivationsKeepsOneSource() {
        String raw = raw(PHASE_A, SOURCE, "shared-object-field");
        String later = OCCURRENCE + "#a2";

        Map<String, String> identities =
                SymbolicSourceEvidence.rawSymbolIdentities(Arrays.asList(
                        owner(event(raw, PHASE_A, SOURCE, OCCURRENCE)),
                        owner(event(raw, PHASE_A, SOURCE, later))));

        assertEquals(1, identities.size());
        assertEquals(SOURCE + "\n" + OCCURRENCE + "\n#1",
                identities.get(raw));
    }

    @Test
    public void twoEntriesOfOneSiteAreTwoRoots() {
        String first = raw(PHASE_A, SOURCE, "entry1");
        String second = raw(PHASE_A, SOURCE, "entry2");

        Map<String, String> identities =
                SymbolicSourceEvidence.rawSymbolIdentities(Arrays.asList(
                        owner(entry(first, PHASE_A, SOURCE, OCCURRENCE, 1)),
                        owner(entry(second, PHASE_A, SOURCE, OCCURRENCE,
                                2))));

        assertEquals(2, identities.size());
        assertEquals(SOURCE + "\n" + OCCURRENCE + "\n#1",
                identities.get(first));
        assertEquals(SOURCE + "\n" + OCCURRENCE + "\n#2",
                identities.get(second));
    }

    @Test
    public void aReusedReadDeclaresNoRoot() {
        String propagated = raw(PHASE_A, SOURCE, "propagated");
        JsonObject reused = SymbolicSourceEvidence.event(PHASE_A, SOURCE,
                OCCURRENCE, FIELD, symbol(propagated), 2, true, "");

        assertTrue(SymbolicSourceEvidence.isReused(reused));
        assertEquals(2, SymbolicSourceEvidence.ordinalOf(reused));
        assertTrue(SymbolicSourceEvidence.rawSymbolIdentities(
                Collections.singletonList(owner(reused))).isEmpty());
    }

    @Test
    public void aPublishedRootNameTravelsOnTheRow() {
        String raw = raw(PHASE_A, SOURCE, "named");
        JsonObject named = SymbolicSourceEvidence.event(PHASE_A, SOURCE,
                OCCURRENCE, FIELD, symbol(raw), 1, false,
                "sym__" + SOURCE + "__occ__1");

        assertEquals("sym__" + SOURCE + "__occ__1",
                named.get(SymbolicSourceEvidence.SYMBOL).getAsString());
        assertEquals(1, SymbolicSourceEvidence.rawSymbolIdentities(
                Collections.singletonList(owner(named))).size());
    }

    @Test
    public void theFreeSymbolCensusIsStatedOrRefused() {
        try {
            SymbolicSourceEvidence.freeSymbolsOf(new JsonObject());
            fail("expected an unstated free-symbol census to be refused");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(),
                    expected.getMessage().contains("is not stated"));
        }
        JsonObject owner = new JsonObject();
        JsonArray rows = new JsonArray();
        JsonObject free = new JsonObject();
        free.addProperty("symbol", "free__SITE__OCC__1");
        free.addProperty("siteId", "SITE");
        free.addProperty("occurrenceId", "OCC");
        free.addProperty("ordinal", 1);
        free.addProperty("javaType", "int");
        free.addProperty("reason", "no recorded lineage");
        rows.add(free);
        JsonObject nameless = new JsonObject();
        nameless.addProperty("siteId", "SITE");
        rows.add(nameless);
        owner.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, rows);

        assertEquals(1,
                SymbolicSourceEvidence.freeSymbolsOf(owner).size());
    }

    @Test
    public void oneRawSymbolStillCannotNameTwoConfiguredSources() {
        String shared = raw(PHASE_A, SOURCE, "shared");
        JsonObject conflicting = event(raw(PHASE_A, "OTHER", "shared"),
                PHASE_A, "OTHER", OCCURRENCE);
        conflicting.addProperty("rawSymbol", shared);
        conflicting.getAsJsonObject("expression")
                .addProperty("_exp", shared);
        assertMalformed(Arrays.asList(
                owner(event(shared, PHASE_A, SOURCE, OCCURRENCE)),
                owner(conflicting)));
        // Two VM symbols for one declared field is what wave 3 C1 makes the
        // normal case - one per entry - so it is admitted, not refused.
        Map<String, String> identities =
                SymbolicSourceEvidence.rawSymbolIdentities(Arrays.asList(
                        owner(event(raw(PHASE_A, SOURCE, "first"), PHASE_A,
                                SOURCE, OCCURRENCE)),
                        owner(event(raw(PHASE_A, SOURCE, "second"), PHASE_A,
                                SOURCE, OCCURRENCE))));
        assertEquals(2, identities.size());
    }

    @Test
    public void twoPublishPhasesInOneOccurrenceStayDistinct() {
        String first = raw(PHASE_A, SOURCE, "first");
        String second = raw(PHASE_B, SOURCE, "second");

        Map<String, String> identities =
                SymbolicSourceEvidence.rawSymbolIdentities(Arrays.asList(
                        owner(entry(first, PHASE_A, SOURCE, OCCURRENCE, 1)),
                        owner(entry(second, PHASE_B, SOURCE, OCCURRENCE,
                                2))));

        // Distinct VM symbols stay distinct registry entries: the registry
        // is keyed by the symbol the VM minted, which is what the Composer
        // keys its roots by.
        assertEquals(2, identities.size());
        assertTrue(identities.containsKey(first));
        assertTrue(identities.containsKey(second));
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
                    "<example.Owner: long value>", intExpression, 1, false, null);
            fail("expected field/expression width mismatch rejection");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains(
                    "field type differs from VM expression"));
        }
    }


    /**
     * The real HDFS-11741 shape: {@code currentKey.keyId} already carries
     * {@code M_I_22_field32}, a root the MAP symbolization minted, so no
     * phase label of this source's own can be in it.  A named row publishes
     * it anyway; a minted row still may not.
     */
    @Test
    public void aNamedRootNeedNotCarryThisPhasesLabel() {
        String propagated = "M_I_22_field32";
        JsonObject named = SymbolicSourceEvidence.event(PHASE_A, SOURCE,
                OCCURRENCE, FIELD, symbol(propagated), 1, true, "");
        JsonObject owner = owner(named);

        assertEquals(1, SymbolicSourceEvidence.eventsOf(owner).size());
        assertTrue(SymbolicSourceEvidence.isReused(
                SymbolicSourceEvidence.eventsOf(owner).get(0)));
        // Still not a root: the registry the Composer names roots by skips
        // it, so the symbol keeps the name its own mint gave it.
        assertTrue(SymbolicSourceEvidence.rawSymbolIdentities(
                Collections.singletonList(owner)).isEmpty());

        JsonObject minted = SymbolicSourceEvidence.event(PHASE_A, SOURCE,
                OCCURRENCE, FIELD, symbol(propagated), 1, false, "");
        assertMalformed(Collections.singletonList(owner(minted)));
    }

    /** Exactly what a reused read must be before it can be named. */
    @Test
    public void onlyABareVmRootCanBeNamedAsAConfiguredSource() {
        assertTrue(SymbolicSourceEvidence.namesOneBareVmRoot(FIELD,
                symbol("M_I_22_field32")));

        // A compound over that same root names roots that live elsewhere.
        JsonObject compound = new JsonObject();
        compound.addProperty("_type", "BinaryExpression");
        compound.addProperty("_java_type", "int");
        compound.add("_left", symbol("M_I_22_field32"));
        assertFalse(SymbolicSourceEvidence.namesOneBareVmRoot(FIELD,
                compound));

        // A fold is not a root.
        JsonObject constant = symbol("Y_I_7");
        constant.addProperty("_type", "ConstExpr");
        assertFalse(SymbolicSourceEvidence.namesOneBareVmRoot(FIELD,
                constant));

        // A leaf the VM did not mint is not a root either.
        assertFalse(SymbolicSourceEvidence.namesOneBareVmRoot(FIELD,
                symbol("X_I_22_field32")));

        // The declared field type still has to be the expression's own.
        assertFalse(SymbolicSourceEvidence.namesOneBareVmRoot(
                "<example.Owner: long value>", symbol("M_I_22_field32")));

        assertFalse(SymbolicSourceEvidence.namesOneBareVmRoot(FIELD, null));
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
                symbol(raw), 1, false, null);
    }

    private static JsonObject entry(String raw, String phase, String source,
                                    String occurrence, int ordinal) {
        return SymbolicSourceEvidence.event(phase, source, occurrence, FIELD,
                symbol(raw), ordinal, false, "");
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
                    FIELD, expression, 1, false, null);
            fail("expected source expression rejection");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), !expected.getMessage().isEmpty());
        }
    }
}
