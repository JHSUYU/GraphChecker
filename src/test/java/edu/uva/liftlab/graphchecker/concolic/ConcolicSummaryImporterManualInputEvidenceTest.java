package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public final class ConcolicSummaryImporterManualInputEvidenceTest {
    private static final String PORT = "REGION.r.in.p";
    private static final String PLANNED = "source#region#1";
    private static final String RAW =
            "M_I_field_REGION.r.in.p_java/lang/Integer";

    @Test
    public void exactMintUsesPlannedIdentityWhileReuseAndBareLabelsDoNotMint()
            throws Exception {
        JsonObject action = action();
        ExecutionTask task = task(action);

        List<String> firstIssues = new ArrayList<>();
        ConcolicSummaryImporter.ManualInputEvidence first = imported(task,
                observation(action, PLANNED + "#a1", true, false), 1,
                firstIssues);
        assertTrue(firstIssues.toString(), firstIssues.isEmpty());
        assertEquals(1, first.observations.size());
        assertEquals(1, first.sources.size());
        JsonObject firstSource = first.sources.get(0).getAsJsonObject();
        assertEquals(PORT, firstSource.get("portId").getAsString());
        assertEquals(RAW, firstSource.get("rawSymbol").getAsString());
        assertEquals(PLANNED,
                firstSource.get("sourceOccurrenceId").getAsString());

        List<String> secondIssues = new ArrayList<>();
        ConcolicSummaryImporter.ManualInputEvidence second = imported(task,
                observation(action, PLANNED + "#a2", true, false), 2,
                secondIssues);
        assertTrue(secondIssues.toString(), secondIssues.isEmpty());
        assertEquals(firstSource.get("sourceIdentity").getAsString(),
                second.sources.get(0).getAsJsonObject()
                        .get("sourceIdentity").getAsString());

        List<String> reusedIssues = new ArrayList<>();
        ConcolicSummaryImporter.ManualInputEvidence reused = imported(task,
                observation(action, PLANNED + "#a3", false, true), 3,
                reusedIssues);
        assertTrue(reusedIssues.toString(), reusedIssues.isEmpty());
        assertEquals(1, reused.observations.size());
        assertEquals(0, reused.sources.size());

        JsonObject bare = new JsonObject();
        bare.addProperty("symbol", PORT);
        bare.addProperty("reused", false);
        List<String> bareIssues = new ArrayList<>();
        ConcolicSummaryImporter.ManualInputEvidence ignored = imported(task,
                bare, 4, bareIssues);
        assertFalse(bareIssues.toString(), bareIssues.isEmpty());
        assertEquals(0, ignored.observations.size());
        assertEquals(0, ignored.sources.size());

        JsonObject forged = observation(action, PLANNED + "#a5", true,
                false);
        forged.addProperty("actionDigest", "not-the-frozen-action");
        List<String> forgedIssues = new ArrayList<>();
        ConcolicSummaryImporter.ManualInputEvidence rejected = imported(task,
                forged, 5, forgedIssues);
        assertEquals(0, rejected.sources.size());
        assertFalse(forgedIssues.isEmpty());
    }

    @Test
    public void exactReuseHasNarrowAuthority() {
        JsonObject action = action();
        JsonObject reused = observation(action, PLANNED + "#a1", false,
                true);
        JsonObject owner = new JsonObject();
        owner.addProperty(LocalCaseIdentity.OWNER, "case-owner");
        owner.addProperty("sourceKey", "source");
        owner.addProperty("regionId", "region");
        owner.addProperty("occurrenceId", PLANNED + "#a1");
        owner.addProperty("boundarySessionScope", "replay-group:test");
        JsonArray observations = new JsonArray();
        observations.add(reused);
        owner.add(ConcolicSummaryImporter.MANUAL_INPUT_OBSERVATION_FIELD,
                observations);

        Map<String, List<JsonObject>> authorities = ConcolicSmtComposer
                .exactReusedManualRootAuthorities(
                        Collections.singletonList(owner),
                        Collections.singletonMap("case-owner",
                                "replay-group:test"));
        assertEquals(1, authorities.size());
        JsonObject admitted = authorities.values().iterator().next().get(0);
        assertEquals(RAW, admitted.get("rawSymbol").getAsString());
        assertTrue(admitted.get("sourceIdentity").getAsString()
                .startsWith("MANUAL."));
    }

    private static ConcolicSummaryImporter.ManualInputEvidence imported(
            ExecutionTask task, JsonObject observation, int activation,
            List<String> issues) {
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("schemaVersion", 1);
        raw.addProperty("taskId", "task");
        raw.addProperty("plannedOccurrenceId", PLANNED);
        raw.addProperty("occurrenceId", PLANNED + "#a" + activation);
        raw.addProperty("activationOrdinal", activation);
        raw.add("engineSummary", new JsonObject());
        JsonArray rows = new JsonArray();
        rows.add(observation);
        raw.add("symbolizedInputs", rows);
        return ConcolicSummaryImporter.manualSymbolicSourceEvidence(
                new ConcolicSummaryImporter.ResultRow(raw, 0), task, issues);
    }

    private static JsonObject observation(JsonObject action,
                                          String occurrence,
                                          boolean minted,
                                          boolean reused) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", RAW);

        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind",
                ConcolicSummaryImporter.MANUAL_INPUT_OBSERVATION_KIND);
        row.addProperty("authority",
                ConcolicSummaryImporter.MANUAL_INPUT_OBSERVATION_AUTHORITY);
        row.addProperty("portId", PORT);
        row.addProperty("actionDigest", CanonicalJson.sha256(action));
        row.addProperty("plannedOccurrenceId", PLANNED);
        row.addProperty("occurrenceId", occurrence);
        row.addProperty("symbol", PORT);
        row.add("fieldPath", new JsonArray());
        row.addProperty("fieldSignature", "");
        row.add("expression", expression);
        row.addProperty("rawSymbol", RAW);
        row.addProperty("javaType", "I");
        row.addProperty("minted", minted);
        row.addProperty("reused", reused);
        return row;
    }

    private static JsonObject action() {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("symbol", PORT);
        action.addProperty("location", "CALL_RETURN");
        action.addProperty("javaType", "int");
        return action;
    }

    private static ExecutionTask task(JsonObject action) {
        JsonObject task = new JsonObject();
        task.addProperty("sourceKey", "source");
        task.addProperty("occurrenceId", PLANNED);
        task.addProperty("relationKey", "relation");
        task.addProperty("regionId", "region");
        task.addProperty("taskId", "task");
        task.addProperty("goalId", "goal");
        JsonArray actions = new JsonArray();
        actions.add(action);
        task.add("inputActions", actions);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        return ExecutionTask.decode(task);
    }
}
