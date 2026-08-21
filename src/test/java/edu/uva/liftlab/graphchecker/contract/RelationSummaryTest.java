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

    /**
     * The guarded merge expands a versioned output into exactly one guarded
     * case per version, and a merge that only partly covered its paths keeps
     * the cases it did observe as a partial relation -- neither dropped nor
     * promoted to a complete one.
     */
    @Test
    public void versionedOutputExpandsToOneGuardedCasePerVersion() {
        JsonObject summary = versionedSummary(3);
        PathObservation path = PathObservation.decode(summary, null);
        RelationSummary merged = RelationSummary.guardedPathMerge(
                OutputClosureCodec.decode(summary),
                Collections.singletonList(path),
                Collections.<JsonObject>emptyList());

        assertEquals(ClosureGoalKind.OUTPUT_RELATION_CLOSURE.name(),
                merged.toJson().get(ClosureGoalKind.TASK_FIELD)
                        .getAsString());
        assertEquals("GOAL.V",
                merged.toJson().get("goalId").getAsString());

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

        JsonObject partialSummary = versionedSummary(1);
        PathObservation partialPath = PathObservation.decode(
                partialSummary, null);

        JsonObject partialMerged = RelationSummary.observedPathMerge(
                OutputClosureCodec.decode(partialSummary),
                Collections.singletonList(partialPath),
                Collections.<JsonObject>emptyList(),
                "PARTIAL", "CLOSED").toJson();

        assertEquals("PARTIAL",
                partialMerged.get("pathCoverageState").getAsString());
        JsonObject coverage = partialMerged.getAsJsonObject("pathCoverage");
        assertEquals("PARTIAL",
                coverage.get("coverageState").getAsString());
        JsonArray partialCases = partialMerged
                .getAsJsonObject("regionRelation").getAsJsonArray("cases");
        assertEquals(1, partialCases.size());
        assertTrue(partialCases.get(0).getAsJsonObject()
                .getAsJsonObject("outputExpressions").has(port()));
        assertEquals("RELATION.V",
                RelationSummary.decode(partialMerged).relationKey());
    }

    private static String port() {
        return "REGION.V.out.0";
    }

    private static JsonObject versionedSummary(int versionCount) {
        String region = "REGION.V";
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

        JsonObject summary = new JsonObject();
        summary.addProperty("taskId", "TASK.V");
        summary.addProperty("goalId", "GOAL.V");
        summary.addProperty("regionId", region);
        summary.addProperty("sourceKey", "NAMENODE/active/epoch-0");
        summary.addProperty("occurrenceId", "REGION.V/occurrence-1");
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(summary);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(summary);
        OutputClosureCodec.writeTo(summary, OutputClosureCodec.singleton(
                "RELATION.V", region, port(), cell,
                "HEAP_STATE", "int", slice));
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
