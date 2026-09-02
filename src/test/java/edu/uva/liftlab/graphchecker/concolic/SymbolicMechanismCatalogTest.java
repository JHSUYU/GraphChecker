package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class SymbolicMechanismCatalogTest {
    @Test
    public void compressesReaderNoiseButKeepsStaticWritersDistinct() {
        JsonObject first = symbolicField("PORT.1", "<Keys: int keyId>");
        first.addProperty("replayOccurrence", 1);
        JsonObject repeated = symbolicField("PORT.2", "<Keys: int keyId>");
        repeated.addProperty("replayOccurrence", 3);
        repeated.addProperty("cell", "<Reader: int poll()>#u9");
        JsonObject nextWriter = symbolicField(
                "PORT.3", "<Keys: int keyId>");

        JsonArray writer = oneAnchor("<Manager: void rotate()>#u7");
        JsonArray otherWriter = oneAnchor("<Manager: void rotate()>#u11");
        assertEquals(SymbolicMechanismCatalog.candidateId(first, writer),
                SymbolicMechanismCatalog.candidateId(repeated, writer));
        assertFalse(SymbolicMechanismCatalog.candidateId(first, writer)
                .equals(SymbolicMechanismCatalog.candidateId(
                        nextWriter, otherWriter)));

        List<JsonObject> observations = new ArrayList<>();
        observations.addAll(observe(context("OCC.1"), first,
                unselected(first), writer));
        observations.addAll(observe(context("OCC.2"), repeated,
                unselected(repeated), writer));
        observations.addAll(observe(context("OCC.3"), nextWriter,
                unselected(nextWriter), otherWriter));

        SymbolicMechanismCatalog catalog = SymbolicMechanismCatalog.create(
                inputs(), observations);
        assertEquals(2, catalog.candidateCount());
        boolean foundRepeatedEvidence = false;
        for (JsonElement card : catalog.json().getAsJsonArray("candidates")) {
            JsonObject row = card.getAsJsonObject();
            if (row.getAsJsonArray("evidence").size() == 2) {
                foundRepeatedEvidence = true;
                assertTrue(row.get("relationBound").getAsBoolean());
                assertFalse(row.get("symbolizable").getAsBoolean());
            }
        }
        assertTrue(foundRepeatedEvidence);
    }

    @Test
    public void runtimeCoordinatesDoNotChangeRelationProposalIdentity() {
        JsonObject firstAction = symbolicField(
                "XCH.STATUS", "<Wire: int httpStatus>");
        firstAction.addProperty("sourceKind", "COMMUNICATION_SITE_PORT");
        firstAction.addProperty("javaType", "int");
        firstAction.addProperty("exchangeSiteKey", "XCH.STATUS");
        firstAction.addProperty("direction", "RESPONSE");
        firstAction.addProperty("replayOccurrence", 7);
        firstAction.addProperty("outputOccurrence", 9);
        JsonObject secondAction = firstAction.deepCopy();
        secondAction.addProperty("replayOccurrence", 70);
        secondAction.addProperty("outputOccurrence", 90);

        JsonObject firstContext = context("OCC.RUNTIME.1");
        firstContext.addProperty("goalId", "GOAL.RUNTIME.1");
        firstContext.addProperty("eventSequence", 41);
        JsonObject secondContext = context("OCC.RUNTIME.2");
        secondContext.addProperty("goalId", "GOAL.RUNTIME.2");
        secondContext.addProperty("eventSequence", 99);

        JsonObject firstAnchor = new JsonObject();
        firstAnchor.addProperty("kind", "UNRESOLVED_WRITER");
        firstAnchor.addProperty("edgeId", "RPC.RUNTIME.1");
        firstAnchor.addProperty("fromOccurrenceId", "OCC.WRITER.1");
        JsonObject secondAnchor = new JsonObject();
        secondAnchor.addProperty("kind", "UNRESOLVED_WRITER");
        secondAnchor.addProperty("edgeId", "RPC.RUNTIME.2");
        secondAnchor.addProperty("fromOccurrenceId", "OCC.WRITER.2");

        SymbolicMechanismCatalog first = SymbolicMechanismCatalog.create(
                inputs(), observe(firstContext, firstAction,
                        unselected(firstAction), array(firstAnchor)));
        SymbolicMechanismCatalog second = SymbolicMechanismCatalog.create(
                new JsonObject(), observe(secondContext, secondAction,
                        unselected(secondAction), array(secondAnchor)));

        String candidateId = SymbolicMechanismCatalog.candidateId(
                firstAction, array(firstAnchor));
        assertEquals(candidateId, SymbolicMechanismCatalog.candidateId(
                secondAction, array(secondAnchor)));
        assertEquals(first.inputDigest(), second.inputDigest());
        assertEquals(evidenceByCandidate(first), evidenceByCandidate(second));
        assertFalse(CanonicalJson.render(first.json()
                .getAsJsonArray("candidates").get(0).getAsJsonObject()
                .get("semantic")).contains("RPC.RUNTIME.1"));

        String evidenceId = evidenceByCandidate(first).get(candidateId);
        second.validate(SymbolicRootProposal.create(first.inputDigest(),
                Collections.singletonList(retain(candidateId, evidenceId))));
        assertEquals("GOAL.RUNTIME.2", second.json()
                .getAsJsonArray("candidates").get(0).getAsJsonObject()
                .getAsJsonArray("evidence").get(0).getAsJsonObject()
                .get("goalId").getAsString());

        JsonObject changedAction = secondAction.deepCopy();
        changedAction.addProperty("javaType", "long");
        SymbolicMechanismCatalog changed = SymbolicMechanismCatalog.create(
                new JsonObject(), observe(secondContext, changedAction,
                        unselected(changedAction), array(secondAnchor)));
        assertFalse(candidateId.equals(SymbolicMechanismCatalog.candidateId(
                changedAction, array(secondAnchor))));
        assertFalse(first.inputDigest().equals(changed.inputDigest()));
    }

    @Test
    public void selectionKeepsRelationsButMintsOnlySelectedRoots() {
        JsonObject root = symbolicField("PORT.ROOT", "<Keys: int keyId>");
        JsonObject carrier = symbolicField(
                "PORT.CARRIER", "<Wire: int keyId>");
        carrier.addProperty("symbolicDemand", "EXACT_INCOMING_COMPOSITION");
        JsonObject noise = symbolicField("PORT.NOISE", "<Poller: long tick>");
        JsonObject fixed = symbolicField("PORT.FIXED", "<Keys: long expiry>");
        JsonObject concrete = symbolicField(
                "PORT.CONCRETE", "<Keys: boolean enabled>");
        concrete.addProperty("mode", "CONCRETE");

        JsonArray actions = array(root, carrier, noise, fixed, concrete);
        JsonArray baseline = array(unselected(root), unselected(carrier),
                unselected(noise), owned(fixed), concrete);
        JsonArray anchors = anchors(empty(),
                oneAnchor("<Manager: void rotate()>#u7"),
                empty(), empty(), empty());
        SymbolicMechanismCatalog catalog = SymbolicMechanismCatalog.create(
                inputs(), SymbolicMechanismCatalog.observations(
                        context("OCC.1"), actions, baseline, anchors));
        Map<String, String> evidence = evidenceByCandidate(catalog);

        String rootId = SymbolicMechanismCatalog.candidateId(root, empty());
        String carrierId = SymbolicMechanismCatalog.candidateId(
                carrier, anchors.get(1).getAsJsonArray());
        String noiseId = SymbolicMechanismCatalog.candidateId(noise, empty());
        String concreteId = SymbolicMechanismCatalog.candidateId(
                concrete, empty());
        List<SymbolicRootProposal.Decision> decisions = new ArrayList<>();
        decisions.add(decision(rootId, SymbolicRootProposal.SiteRole.ROOT,
                evidence.get(rootId), "MECHANISM.KEY"));
        decisions.add(decision(carrierId,
                SymbolicRootProposal.SiteRole.CARRIER,
                evidence.get(carrierId), null));
        decisions.add(decision(noiseId,
                SymbolicRootProposal.SiteRole.STUTTER_NOISE,
                evidence.get(noiseId), null));
        decisions.add(decision(concreteId,
                SymbolicRootProposal.SiteRole.CARRIER,
                evidence.get(concreteId), null));

        List<SymbolicRootProposal.Decision> cutRelation =
                new ArrayList<>(decisions);
        cutRelation.set(1, decision(carrierId,
                SymbolicRootProposal.SiteRole.STUTTER_NOISE,
                evidence.get(carrierId), null));
        assertRejected(catalog, SymbolicRootProposal.create(
                catalog.inputDigest(), cutRelation),
                "must retain producer context");

        SymbolicMechanismCatalog.Selection selection = catalog.validate(
                SymbolicRootProposal.create(catalog.inputDigest(), decisions));
        JsonArray selected = selection.select(actions, baseline, anchors);

        assertEquals("SYMBOLIC", mode(selected, 0));
        assertEquals("SYMBOLIC", mode(selected, 1));
        assertFalse(selected.get(1).getAsJsonObject()
                .has("symbolicRootCandidateId"));
        assertEquals("RETAIN_CONTEXT", selected.get(1).getAsJsonObject()
                .get("symbolicSelectionDecision").getAsString());
        assertEquals("CONCRETE", mode(selected, 2));
        assertEquals("CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED",
                selected.get(3).getAsJsonObject()
                        .get("symbolicDemand").getAsString());
        assertEquals("CONCRETE", mode(selected, 4));
        assertEquals(4, catalog.candidateCount());
    }

    @Test
    public void staleOrIncompleteProposalIsRejected() {
        JsonObject root = symbolicField("PORT.ROOT", "<Keys: int keyId>");
        SymbolicMechanismCatalog catalog = SymbolicMechanismCatalog.create(
                inputs(), observe(context("OCC.1"), root,
                        unselected(root), empty()));
        JsonObject rerun = symbolicField("PORT.RERUN", "<Keys: int keyId>");
        assertEquals(catalog.inputDigest(), SymbolicMechanismCatalog.create(
                new JsonObject(), observe(context("OCC.1"), rerun,
                        unselected(rerun), empty())).inputDigest());
        assertRejected(catalog, SymbolicRootProposal.create(
                repeat('0', 64),
                Collections.<SymbolicRootProposal.Decision>emptyList()),
                "stale");
        assertRejected(catalog, SymbolicRootProposal.create(
                catalog.inputDigest(),
                Collections.<SymbolicRootProposal.Decision>emptyList()),
                "omits candidates");
    }

    @Test
    public void rejectsUntrustedProposalBoundaries() {
        JsonObject a = symbolicField("PORT.A", "<Keys: int a>");
        JsonObject b = symbolicField("PORT.B", "<Keys: int b>");
        JsonObject fixedCovered = symbolicField("PORT.C", "<Keys: int c>");
        JsonArray actions = array(a, b, fixedCovered);
        JsonArray baseline = array(unselected(a), unselected(b),
                unselected(fixedCovered));
        JsonArray noWriters = anchors(empty(), empty(), empty());
        SymbolicMechanismCatalog catalog = SymbolicMechanismCatalog.create(
                inputs(), SymbolicMechanismCatalog.observations(
                        context("OCC.1"), actions, baseline, noWriters),
                array(fixedRoot("<Keys: int c>")));
        Map<String, String> evidence = evidenceByCandidate(catalog);
        String aId = SymbolicMechanismCatalog.candidateId(a, empty());
        String bId = SymbolicMechanismCatalog.candidateId(b, empty());
        String cId = SymbolicMechanismCatalog.candidateId(fixedCovered, empty());

        List<SymbolicRootProposal.Decision> unknown = retainedAll(evidence);
        unknown.add(SymbolicRootProposal.Decision.create("UNKNOWN",
                SymbolicRootProposal.SiteRole.CARRIER,
                SymbolicRootProposal.DecisionKind.RETAIN_CONTEXT,
                Collections.singletonList("UNKNOWN.EVIDENCE"), null));
        assertRejected(catalog, SymbolicRootProposal.create(
                catalog.inputDigest(), unknown), "unknown candidate");

        List<SymbolicRootProposal.Decision> foreign = new ArrayList<>();
        foreign.add(retain(aId, evidence.get(bId)));
        foreign.add(retain(bId, evidence.get(bId)));
        foreign.add(retain(cId, evidence.get(cId)));
        assertRejected(catalog, SymbolicRootProposal.create(
                catalog.inputDigest(), foreign), "foreign evidence");

        List<SymbolicRootProposal.Decision> promotion = new ArrayList<>();
        promotion.add(retain(aId, evidence.get(aId)));
        promotion.add(retain(bId, evidence.get(bId)));
        promotion.add(decision(cId, SymbolicRootProposal.SiteRole.ROOT,
                evidence.get(cId), "G"));
        assertRejected(catalog, SymbolicRootProposal.create(
                catalog.inputDigest(), promotion), "concrete-only");

        List<SymbolicRootProposal.Decision> groups = new ArrayList<>();
        groups.add(decision(aId, SymbolicRootProposal.SiteRole.ROOT,
                evidence.get(aId), "G1"));
        groups.add(decision(bId, SymbolicRootProposal.SiteRole.ROOT,
                evidence.get(bId), "G2"));
        groups.add(retain(cId, evidence.get(cId)));
        assertRejected(catalog, SymbolicRootProposal.create(
                catalog.inputDigest(), groups), "one rootGroupId");

        List<SymbolicRootProposal.Decision> review = new ArrayList<>();
        review.add(SymbolicRootProposal.Decision.create(aId,
                SymbolicRootProposal.SiteRole.REVIEW,
                SymbolicRootProposal.DecisionKind.REVIEW,
                Collections.singletonList(evidence.get(aId)), null));
        review.add(retain(bId, evidence.get(bId)));
        review.add(retain(cId, evidence.get(cId)));
        assertRejected(catalog, SymbolicRootProposal.create(
                catalog.inputDigest(), review), "requires review");
    }

    private static JsonObject inputs() {
        JsonObject result = new JsonObject();
        result.addProperty("regionPlanSha256", repeat('a', 64));
        result.addProperty("refinedGraphSha256", repeat('b', 64));
        return result;
    }

    private static JsonObject context(String occurrence) {
        JsonObject result = new JsonObject();
        result.addProperty("sourceKey", "cluster/nn#epoch1");
        result.addProperty("occurrenceId", occurrence);
        result.addProperty("relationKey", "REL.1");
        result.addProperty("regionId", "REGION.1");
        result.addProperty("goalId", "GOAL.1");
        result.addProperty("goalKind", "TARGET_REACH");
        return result;
    }

    private static JsonObject symbolicField(String port, String field) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("portId", port);
        action.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        action.addProperty("dependencyRole", "VALUE_FRONTIER");
        action.addProperty("cell", "<Reader: int read()>#u3.fieldReceiver");
        action.addProperty("leafFieldSignature", field);
        JsonArray declarations = new JsonArray();
        declarations.add(field);
        action.add("fieldPathDeclarations", declarations);
        return action;
    }

    private static JsonArray oneAnchor(String site) {
        JsonObject anchor = new JsonObject();
        anchor.addProperty("kind", "REGION_OUTPUT");
        anchor.addProperty("fromRegion", "REGION.PRODUCER");
        anchor.addProperty("cell", site);
        return array(anchor);
    }

    private static List<JsonObject> observe(
            JsonObject context, JsonObject action, JsonObject baseline,
            JsonArray writerAnchors) {
        return SymbolicMechanismCatalog.observations(context, one(action),
                one(baseline), anchors(writerAnchors));
    }

    private static Map<String, String> evidenceByCandidate(
            SymbolicMechanismCatalog catalog) {
        Map<String, String> result = new LinkedHashMap<>();
        for (JsonElement element : catalog.json().getAsJsonArray("candidates")) {
            JsonObject card = element.getAsJsonObject();
            result.put(card.get("candidateId").getAsString(),
                    card.getAsJsonArray("evidenceIds").get(0).getAsString());
        }
        return result;
    }

    private static List<SymbolicRootProposal.Decision> retainedAll(
            Map<String, String> evidence) {
        List<SymbolicRootProposal.Decision> result = new ArrayList<>();
        for (Map.Entry<String, String> entry : evidence.entrySet()) {
            result.add(retain(entry.getKey(), entry.getValue()));
        }
        return result;
    }

    private static SymbolicRootProposal.Decision retain(
            String id, String evidence) {
        return decision(id, SymbolicRootProposal.SiteRole.CARRIER,
                evidence, null);
    }

    private static SymbolicRootProposal.Decision decision(
            String id, SymbolicRootProposal.SiteRole role,
            String evidence, String group) {
        SymbolicRootProposal.DecisionKind kind;
        switch (role) {
            case ROOT:
                kind = SymbolicRootProposal.DecisionKind.SELECT_ROOT;
                break;
            case STUTTER_NOISE:
            case IRRELEVANT:
                kind = SymbolicRootProposal.DecisionKind.EXCLUDE_SYMBOLIZATION;
                break;
            default:
                kind = SymbolicRootProposal.DecisionKind.RETAIN_CONTEXT;
        }
        return SymbolicRootProposal.Decision.create(id, role, kind,
                Collections.singletonList(evidence), group);
    }

    private static void assertRejected(SymbolicMechanismCatalog catalog,
                                       SymbolicRootProposal proposal,
                                       String message) {
        try {
            catalog.validate(proposal);
            fail("proposal was accepted: " + message);
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(),
                    expected.getMessage().contains(message));
        }
    }

    private static JsonObject unselected(JsonObject action) {
        JsonObject result = action.deepCopy();
        result.addProperty("mode", "CONCRETE");
        result.addProperty("symbolicDemand",
                "CONFIGURED_SYMBOLIC_INPUT_UNSELECTED");
        return result;
    }

    private static JsonObject owned(JsonObject action) {
        JsonObject result = action.deepCopy();
        result.addProperty("mode", "CONCRETE");
        result.addProperty("symbolicDemand",
                "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED");
        return result;
    }

    private static JsonObject fixedRoot(String field) {
        JsonObject root = new JsonObject();
        root.addProperty("fixedRootId", "FIXED.1");
        JsonObject semantic = new JsonObject();
        semantic.addProperty("fieldSignature", field);
        root.add("semantic", semantic);
        return root;
    }

    private static String mode(JsonArray rows, int index) {
        return rows.get(index).getAsJsonObject().get("mode").getAsString();
    }

    private static JsonArray empty() { return new JsonArray(); }

    private static JsonArray one(JsonObject row) { return array(row); }

    private static JsonArray anchors(JsonArray... rows) {
        JsonArray result = new JsonArray();
        for (JsonArray row : rows) result.add(row.deepCopy());
        return result;
    }

    private static JsonArray array(JsonObject... rows) {
        JsonArray result = new JsonArray();
        for (JsonObject row : rows) result.add(row.deepCopy());
        return result;
    }

    private static String repeat(char value, int count) {
        StringBuilder result = new StringBuilder();
        for (int index = 0; index < count; index++) result.append(value);
        return result.toString();
    }
}
