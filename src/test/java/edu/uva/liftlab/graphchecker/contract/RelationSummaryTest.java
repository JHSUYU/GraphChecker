package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.NavigableMap;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RelationSummaryTest {

    @Test
    public void versionedOutputExpandsToOneGuardedCasePerVersion() {
        JsonObject summary = versionedSummary(3);
        PathObservation path = PathObservation.decode(summary, null);
        RelationSummary merged = RelationSummary.guardedPathMerge(
                OutputClosureCodec.decode(summary),
                Collections.singletonList(path),
                Collections.<JsonObject>emptyList());

        JsonArray cases = merged.toJson()
                .getAsJsonObject("regionRelation").getAsJsonArray("cases");
        assertEquals(3, cases.size());
        Set<String> caseIds = new LinkedHashSet<>();
        for (int index = 0; index < cases.size(); index++) {
            JsonObject item = cases.get(index).getAsJsonObject();
            caseIds.add(item.get("caseId").getAsString());
            JsonArray conditions = item.getAsJsonObject("guard")
                    .getAsJsonArray("conditions");
            assertEquals(1, conditions.size());
            JsonObject selection = conditions.get(0).getAsJsonObject();
            assertTrue(BoundedOutputVersions.isVersionSelection(selection));
            assertEquals(port(),
                    selection.get("outputPort").getAsString());
            assertEquals(3, selection.get("versionBound").getAsInt());
            int ordinal = selection.get("versionOrdinal").getAsInt();
            // The case binds exactly the expression of its own version.
            JsonObject bound = item.getAsJsonObject("outputExpressions")
                    .getAsJsonObject(port());
            assertFalse(BoundedOutputVersions.isVersionSet(bound));
            assertEquals("Y_I_" + ordinal,
                    bound.get("_exp").getAsString());
        }
        assertEquals(3, caseIds.size());
    }

    @Test
    public void unversionedOutputKeepsOneCaseWithoutVersionGuards() {
        JsonObject summary = versionedSummary(1);
        PathObservation path = PathObservation.decode(summary, null);
        RelationSummary merged = RelationSummary.guardedPathMerge(
                OutputClosureCodec.decode(summary),
                Collections.singletonList(path),
                Collections.<JsonObject>emptyList());

        JsonArray cases = merged.toJson()
                .getAsJsonObject("regionRelation").getAsJsonArray("cases");
        assertEquals(1, cases.size());
        JsonObject item = cases.get(0).getAsJsonObject();
        assertEquals(0, item.getAsJsonObject("guard")
                .getAsJsonArray("conditions").size());
        assertEquals("Y_I_1", item.getAsJsonObject("outputExpressions")
                .getAsJsonObject(port()).get("_exp").getAsString());
    }

    @Test
    public void referenceIdentityPortsCountTowardTheExactOutputSet() {
        JsonObject summary = versionedSummary(2);
        JsonObject identity = new JsonObject();
        identity.addProperty("authority",
                "CONCRETE_REFERENCE_IDENTITY_RELATION_V1");
        identity.addProperty("objectId", 74965L);
        JsonObject identities = new JsonObject();
        identities.add("REGION.V.out.ref", identity);
        summary.add("outputReferenceIdentities", identities);
        PathObservation path = PathObservation.decode(summary, null);

        Set<String> joint = new LinkedHashSet<>();
        joint.add(port());
        joint.add("REGION.V.out.ref");
        assertTrue(path.hasExactOutputSet(joint));
        assertFalse(path.hasExactOutputSet(
                Collections.singleton(port())));

        // Each expanded case passes the identity relation through so the
        // composed joint output check sees the complete port set.
        RelationSummary merged = RelationSummary.guardedPathMerge(
                OutputClosureCodec.decode(summary),
                Collections.singletonList(path),
                Collections.<JsonObject>emptyList());
        JsonArray cases = merged.toJson()
                .getAsJsonObject("regionRelation").getAsJsonArray("cases");
        assertEquals(2, cases.size());
        for (JsonElement element : cases) {
            assertEquals(1, element.getAsJsonObject()
                    .getAsJsonObject("outputReferenceIdentities").size());
        }
    }

    private static String port() {
        return "REGION.V.out.0";
    }

    private static JsonObject versionedSummary(int versionCount) {
        String region = "REGION.V";
        String instance = region + "@test#call1";
        String cell = "<test.State: int value0>";
        String site = "<test.Worker: void run()>#u1";

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port());
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.add("causalEdges", new JsonArray());

        JsonObject summary = new JsonObject();
        summary.addProperty("taskId", "TASK.V");
        summary.addProperty("goalId", "GOAL.V");
        summary.addProperty("regionId", region);
        summary.addProperty("regionInstanceId", instance);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(summary);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(summary);
        OutputClosureCodec.writeTo(summary, OutputClosureCodec.singleton(
                region, instance, 1L, port(), cell, "HEAP_STATE", "int",
                slice));
        summary.add("symbolicInputs", new JsonArray());
        summary.add("edgeBindings", new JsonArray());
        summary.add("pathCondition", new JsonArray());
        summary.add("branchMappings", new JsonArray());
        JsonObject outputs = new JsonObject();
        outputs.add(port(), expressions(site, versionCount));
        summary.add("outputExpressions", outputs);
        summary.addProperty("normalExit", true);
        summary.addProperty("exceptionType", "");
        summary.addProperty("relationallyComplete", true);
        return summary;
    }

    private static JsonElement expressions(String site, int versionCount) {
        if (versionCount == 1) return constant(1);
        NavigableMap<Integer, JsonElement> versions = new TreeMap<>();
        for (int ordinal = 1; ordinal <= versionCount; ordinal++) {
            versions.put(ordinal, constant(ordinal));
        }
        return BoundedOutputVersions.encodeVersionSet(site, versions);
    }

    private static JsonObject constant(int value) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConstExpr");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", "Y_I_" + value);
        return expression;
    }
}
