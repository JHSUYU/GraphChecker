package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/** Regression coverage for replay-local VM event ids in guarded cases. */
public class RecordedSessionModelCaseScopedEventIdentityTest {
    private static final String REGION = "REGION.reader";
    private static final String OCCURRENCE =
            RecordedSharedStateFixtures.occurrenceOf(REGION);
    private static final String LOCATION = "INSTANCE_FIELD/7#24";
    private static final String FIELD = "example.State#value";
    private static final long LOCAL_VERSION = 11L;
    private static final long LOCAL_READ = 21L;

    @Test
    public void equalLocalIdsInTwoCasesHaveDisjointSolverIdentities() {
        JsonObject summary = new JsonObject();
        summary.addProperty("regionId", REGION);
        summary.addProperty("occurrenceId", OCCURRENCE);
        JsonArray cases = new JsonArray();
        cases.add(guardedCaseRow("CASE.target"));
        cases.add(guardedCaseRow("CASE.replay"));
        JsonObject relation = new JsonObject();
        relation.add("cases", cases);
        summary.add("regionRelation", relation);

        RecordedSessionModel model = RecordedSessionModel.of(
                Collections.singletonList(summary), null, REGION);
        String targetOwner = RecordedSessionModel.caseOwner(
                REGION, OCCURRENCE, "CASE.target", 0);
        String replayOwner = RecordedSessionModel.caseOwner(
                REGION, OCCURRENCE, "CASE.replay", 1);
        long targetRead = model.resolveEventId(targetOwner, LOCAL_READ);
        long replayRead = model.resolveEventId(replayOwner, LOCAL_READ);
        long targetVersion = model.resolveEventId(
                targetOwner, LOCAL_VERSION);
        long replayVersion = model.resolveEventId(
                replayOwner, LOCAL_VERSION);

        assertTrue("target read must have a synthetic event id",
                targetRead > 0L);
        assertTrue("replay read must have a synthetic event id",
                replayRead > 0L);
        assertTrue("equal replay-local read ids must not alias",
                targetRead != replayRead);
        assertTrue("equal replay-local version ids must not alias",
                targetVersion != replayVersion);
        assertTrue(model.ordersEvent(targetRead));
        assertTrue(model.ordersEvent(replayRead));
        assertTrue(model.ordersEvent(targetVersion));
        assertTrue(model.ordersEvent(replayVersion));

        String targetPosition = model.scopedPositionName(targetRead);
        String replayPosition = model.scopedPositionName(replayRead);
        assertFalse("case-local reads need different position variables",
                targetPosition.equals(replayPosition));
        assertTrue(targetPosition.startsWith(
                RecordedSessionModel.POSITION_PREFIX));
        assertTrue(replayPosition.startsWith(
                RecordedSessionModel.POSITION_PREFIX));

        String targetArm = model.scopedSelectorName(targetRead, "rf1");
        String replayArm = model.scopedSelectorName(replayRead, "rf1");
        assertFalse("the same local read arm needs a different selector",
                targetArm.equals(replayArm));
        assertTrue(model.selectors().toString(),
                model.selectors().contains(targetArm));
        assertTrue(model.selectors().toString(),
                model.selectors().contains(replayArm));

        String readerSite = RecordedEvidenceIdentity.siteKey(OCCURRENCE);
        List<RecordedSessionModel.ReadCase> readCases = model.readCasesOf(
                LOCATION, readerSite);
        assertEquals("both case-local reads must survive the site index",
                2, readCases.size());
        Map<Long, String> guards = new LinkedHashMap<>();
        for (RecordedSessionModel.ReadCase readCase : readCases) {
            guards.put(readCase.readEventId, readCase.caseGuard);
        }
        assertEquals(RecordedSessionModel.caseSelector(targetOwner),
                guards.get(targetRead));
        assertEquals(RecordedSessionModel.caseSelector(replayOwner),
                guards.get(replayRead));
        assertFalse("case-local reads need different existence guards",
                guards.get(targetRead).equals(guards.get(replayRead)));

        JsonArray choices = model.manifest().getAsJsonArray("readChoices");
        assertEquals(2, choices.size());
        assertTrue(hasReadChoice(choices, targetRead, targetArm,
                targetVersion));
        assertTrue(hasReadChoice(choices, replayRead, replayArm,
                replayVersion));

        JsonArray identities = model.manifest()
                .getAsJsonArray("eventIdentities");
        assertNotNull("the manifest must expose the alpha-renaming table",
                identities);
        assertEquals("three colliding local events in each of two scopes",
                6, identities.size());
        Map<String, Integer> identityCounts = new LinkedHashMap<>();
        for (JsonElement element : identities) {
            JsonObject identity = element.getAsJsonObject();
            assertTrue(identity.has("scope"));
            assertTrue(identity.has("localEventId"));
            assertTrue(identity.has("syntheticEventId"));
            assertTrue(identity.has("solverToken"));
            assertTrue(identity.has("qualified"));
            String scope = identity.get("scope").getAsString();
            identityCounts.put(scope,
                    identityCounts.getOrDefault(scope, 0) + 1);
        }
        assertEquals(2, identityCounts.size());
        assertEquals(Integer.valueOf(3), identityCounts.get(targetOwner));
        assertEquals(Integer.valueOf(3), identityCounts.get(replayOwner));
        assertEventIdentity(identities, model, targetOwner, LOCAL_READ,
                targetRead);
        assertEventIdentity(identities, model, targetOwner, LOCAL_VERSION,
                targetVersion);
        assertEventIdentity(identities, model, replayOwner, LOCAL_READ,
                replayRead);
        assertEventIdentity(identities, model, replayOwner, LOCAL_VERSION,
                replayVersion);
    }

    @Test
    public void exactAndGuardedCasesWithEqualLocalIdsRemainDistinct() {
        JsonObject summary = new JsonObject();
        summary.addProperty("regionId", REGION);
        summary.addProperty("occurrenceId", OCCURRENCE);
        JsonArray cases = new JsonArray();
        cases.add(exactCaseRow("CASE.exact"));
        cases.add(guardedCaseRow("CASE.guarded"));
        JsonObject relation = new JsonObject();
        relation.add("cases", cases);
        summary.add("regionRelation", relation);

        RecordedSessionModel model = RecordedSessionModel.of(
                Collections.singletonList(summary), null, REGION);
        String exactOwner = RecordedSessionModel.caseOwner(
                REGION, OCCURRENCE, "CASE.exact", 0);
        String guardedOwner = RecordedSessionModel.caseOwner(
                REGION, OCCURRENCE, "CASE.guarded", 1);
        long exactRead = model.resolveEventId(exactOwner, LOCAL_READ);
        long guardedRead = model.resolveEventId(guardedOwner, LOCAL_READ);
        long exactVersion = model.resolveEventId(exactOwner, LOCAL_VERSION);
        long guardedVersion = model.resolveEventId(
                guardedOwner, LOCAL_VERSION);

        assertTrue(exactRead > 0L);
        assertTrue(guardedRead > 0L);
        assertTrue(exactRead != guardedRead);
        assertTrue(exactVersion != guardedVersion);

        String readerSite = RecordedEvidenceIdentity.siteKey(OCCURRENCE);
        List<RecordedSessionModel.ReadCase> all = model.readCasesOf(
                LOCATION, readerSite);
        assertEquals("both resolutions must survive the shared site index",
                2, all.size());
        Map<Long, RecordedSessionModel.ReadCase> byRead =
                new LinkedHashMap<>();
        for (RecordedSessionModel.ReadCase readCase : all) {
            byRead.put(readCase.readEventId, readCase);
        }
        assertNotNull(byRead.get(exactRead));
        assertNotNull(byRead.get(guardedRead));
        assertEquals(SharedStateEvidence.RESOLUTION_EXACT,
                byRead.get(exactRead).resolution);
        assertEquals(exactVersion,
                byRead.get(exactRead).chosenFieldVersionId);
        assertEquals(RecordedSessionModel.caseSelector(exactOwner),
                byRead.get(exactRead).caseGuard);
        assertEquals(SharedStateEvidence.RESOLUTION_GUARDED,
                byRead.get(guardedRead).resolution);
        assertEquals(0L, byRead.get(guardedRead).chosenFieldVersionId);
        assertEquals(RecordedSessionModel.caseSelector(guardedOwner),
                byRead.get(guardedRead).caseGuard);

        List<RecordedSessionModel.ReadCase> guarded =
                model.guardedReadCasesOf(LOCATION, readerSite);
        assertEquals("the exact replay must not become a selector case",
                1, guarded.size());
        assertEquals(guardedRead, guarded.get(0).readEventId);

        assertTrue(model.exactReadSelects(exactRead, exactVersion));
        assertFalse(model.exactReadSelects(LOCAL_READ, LOCAL_VERSION));
        assertFalse(model.exactReadSelects(exactRead, LOCAL_VERSION));
        assertFalse(model.exactReadSelects(exactRead, guardedVersion));
        assertFalse(model.exactReadSelects(guardedRead, guardedVersion));
        assertFalse(model.exactReadSelects(guardedRead, exactVersion));
    }

    private static JsonObject guardedCaseRow(String caseId) {
        return caseRow(caseId, SharedStateEvidence.RESOLUTION_GUARDED,
                "AMBIGUOUS_WRITERS", 0L, true);
    }

    private static JsonObject exactCaseRow(String caseId) {
        return caseRow(caseId, SharedStateEvidence.RESOLUTION_EXACT,
                "UNIQUE_VERSION", LOCAL_VERSION, false);
    }

    private static JsonObject caseRow(String caseId, String resolution,
                                      String reason, long chosenVersion,
                                      boolean attachGuardedRead) {
        JsonObject envelope = RecordedSharedStateFixtures.twoWriterEnvelope(
                resolution, reason, chosenVersion);
        for (JsonElement element : envelope.getAsJsonArray("versions")) {
            JsonObject version = element.getAsJsonObject();
            version.addProperty("regionId", REGION);
            version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                    OCCURRENCE);
        }
        SharedStateEvidence.normalizeGuards(envelope);
        if (attachGuardedRead) {
            JsonObject guarded = RecordedSharedStateFixtures.guardedRead(
                    LOCAL_READ, 7L, 24);
            SharedStateEvidence.normalizeGuards(guarded);
            envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                    .add("expression", guarded);
        }

        JsonObject row = new JsonObject();
        row.addProperty("caseId", caseId);
        row.add(SharedStateEvidence.RECORDED_FIELD,
                RecordedSharedStateFixtures.recordedMember(envelope,
                        RecordedSharedStateFixtures.twoWriterLedger(), FIELD));
        return row;
    }

    private static void assertEventIdentity(JsonArray identities,
                                            RecordedSessionModel model,
                                            String scope, long localEventId,
                                            long syntheticEventId) {
        JsonObject identity = null;
        for (JsonElement element : identities) {
            JsonObject candidate = element.getAsJsonObject();
            if (scope.equals(candidate.get("scope").getAsString())
                    && candidate.get("localEventId").getAsLong()
                    == localEventId) {
                identity = candidate;
                break;
            }
        }
        assertNotNull("missing identity for " + scope + ":" + localEventId,
                identity);
        assertEquals(syntheticEventId,
                identity.get("syntheticEventId").getAsLong());
        assertTrue("colliding raw ids must use qualified solver tokens",
                identity.get("qualified").getAsBoolean());
        String solverToken = identity.get("solverToken").getAsString();
        assertFalse(solverToken.isEmpty());
        assertEquals(RecordedSessionModel.POSITION_PREFIX + solverToken,
                model.scopedPositionName(syntheticEventId));
    }

    private static boolean hasReadChoice(JsonArray choices, long readEventId,
                                         String selector,
                                         long fieldVersionId) {
        for (JsonElement element : choices) {
            JsonObject read = element.getAsJsonObject();
            if (read.get("readEventId").getAsLong() != readEventId) {
                continue;
            }
            for (JsonElement candidateElement
                    : read.getAsJsonArray("candidates")) {
                JsonObject candidate = candidateElement.getAsJsonObject();
                if (selector.equals(candidate.get("selector").getAsString())
                        && candidate.get("fieldVersionId").getAsLong()
                        == fieldVersionId) {
                    return true;
                }
            }
        }
        return false;
    }
}
