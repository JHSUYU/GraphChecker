package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class SymbolicRootProposalTest {
    private static final String DIGEST =
            "0123456789abcdef0123456789abcdef"
                    + "0123456789abcdef0123456789abcdef";

    @Test
    public void currentShapeRoundTripsAsProposalOnlyDecisions() {
        SymbolicRootProposal.Decision root =
                SymbolicRootProposal.Decision.create(
                        "CANDIDATE.root", SymbolicRootProposal.SiteRole.ROOT,
                        SymbolicRootProposal.DecisionKind.SELECT_ROOT,
                        Arrays.asList("EDGE.1", "TRACE.7"), "ROOT_GROUP.1");
        SymbolicRootProposal.Decision carrier =
                SymbolicRootProposal.Decision.create(
                        "CANDIDATE.carrier",
                        SymbolicRootProposal.SiteRole.CARRIER,
                        SymbolicRootProposal.DecisionKind.RETAIN_CONTEXT,
                        Collections.singletonList("EDGE.2"), null);

        SymbolicRootProposal proposal = SymbolicRootProposal.create(
                DIGEST, Arrays.asList(root, carrier));
        SymbolicRootProposal decoded = SymbolicRootProposal.decode(
                proposal.json());

        assertEquals(DIGEST, decoded.inputDigest());
        assertEquals(2, decoded.decisions().size());
        assertEquals("ROOT_GROUP.1",
                decoded.decisions().get(0).rootGroupId());
        assertTrue(decoded.decisions().get(0).hasRootGroupId());
        assertNull(decoded.decisions().get(1).rootGroupId());
        assertTrue(decoded.json().getAsJsonArray("decisions").get(1)
                .getAsJsonObject().get("rootGroupId").isJsonNull());
    }

    @Test
    public void strictSchemaRejectsMalformedOrInconsistentRows() {
        JsonObject valid = proposal(decision("CANDIDATE.1", "ROOT",
                "SELECT_ROOT", "EDGE.1"));

        JsonObject unknown = valid.deepCopy();
        unknown.addProperty("legacyFallback", true);
        assertRejected(unknown, "exact current fields");

        JsonObject wrongDigest = valid.deepCopy();
        wrongDigest.addProperty("inputDigest", "abc");
        assertRejected(wrongDigest, "SHA-256");

        JsonObject inconsistent = proposal(decision("CANDIDATE.1", "GUARD",
                "SELECT_ROOT", "EDGE.1"));
        assertRejected(inconsistent, "requires decision RETAIN_CONTEXT");

        JsonObject duplicate = valid.deepCopy();
        duplicate.getAsJsonArray("decisions").add(
                duplicate.getAsJsonArray("decisions").get(0).deepCopy());
        assertRejected(duplicate, "duplicate candidateId");

        JsonObject emptyEvidence = proposal(decision("CANDIDATE.1", "ROOT",
                "SELECT_ROOT", ""));
        assertRejected(emptyEvidence, "evidenceIds");

        JsonObject noEvidence = valid.deepCopy();
        noEvidence.getAsJsonArray("decisions").get(0).getAsJsonObject()
                .add("evidenceIds", new JsonArray());
        assertRejected(noEvidence, "evidenceIds must not be empty");

        JsonObject missingNullableField = valid.deepCopy();
        missingNullableField.getAsJsonArray("decisions").get(0)
                .getAsJsonObject().remove("rootGroupId");
        assertRejected(missingNullableField, "exact current fields");
    }

    @Test
    public void reviewRemainsAnExplicitProposalDecision() {
        JsonObject row = decision("CANDIDATE.review", "REVIEW", "REVIEW",
                "TRACE.9");
        row.add("rootGroupId", JsonNull.INSTANCE);
        SymbolicRootProposal proposal = SymbolicRootProposal.decode(
                proposal(row));

        assertEquals(SymbolicRootProposal.DecisionKind.REVIEW,
                proposal.decisions().get(0).decision());
    }

    private static JsonObject proposal(JsonObject... decisions) {
        JsonObject proposal = new JsonObject();
        proposal.addProperty("schemaVersion", 1);
        proposal.addProperty("kind", SymbolicRootProposal.KIND);
        proposal.addProperty("authority", SymbolicRootProposal.AUTHORITY);
        proposal.addProperty("inputDigest", DIGEST);
        JsonArray rows = new JsonArray();
        for (JsonObject decision : decisions) rows.add(decision);
        proposal.add("decisions", rows);
        return proposal;
    }

    private static JsonObject decision(
            String candidateId, String role, String selected,
            String evidenceId) {
        JsonObject decision = new JsonObject();
        decision.addProperty("candidateId", candidateId);
        decision.addProperty("siteRole", role);
        decision.addProperty("decision", selected);
        JsonArray evidence = new JsonArray();
        evidence.add(evidenceId);
        decision.add("evidenceIds", evidence);
        decision.add("rootGroupId", JsonNull.INSTANCE);
        return decision;
    }

    private static void assertRejected(JsonObject row, String message) {
        try {
            SymbolicRootProposal.decode(row);
            fail("malformed proposal was accepted");
        } catch (IllegalArgumentException rejected) {
            assertTrue(rejected.getMessage(),
                    rejected.getMessage().contains(message));
        }
    }
}
