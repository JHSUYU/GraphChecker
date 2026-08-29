package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.RecordedReadFrom;
import edu.uva.liftlab.graphchecker.concolic.RecordedSessionModel;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.NavigableMap;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class RelationSummaryTest {

    @Test
    public void pathObservationRequiresTheExactActivationTuple() {
        JsonObject missingOrdinal = versionedSummary(1);
        missingOrdinal.remove(PathObservation.ACTIVATION_ORDINAL);
        assertPathRejected(missingOrdinal);
        JsonObject missingPlanned = versionedSummary(1);
        missingPlanned.remove(PathObservation.PLANNED_OCCURRENCE_ID);
        assertPathRejected(missingPlanned);
        JsonObject wrongOccurrence = versionedSummary(1);
        wrongOccurrence.addProperty("occurrenceId", "REGION.V/occurrence-1");
        assertPathRejected(wrongOccurrence);
        JsonObject missingComplete = versionedSummary(1);
        missingComplete.remove("relationallyComplete");
        assertPathRejected(missingComplete);
    }

    @Test
    public void outputGuardExcludesDownstreamAuxiliaryConsumers() {
        JsonObject summary = versionedSummary(1);
        JsonObject output = symbol("M_I_output_key");
        summary.getAsJsonObject("outputExpressions")
                .add(port(), output.deepCopy());
        summary.getAsJsonArray("pathCondition").add(
                binary(output, "<", constant(10),
                        "virtual void example.Base64.encode():0"));

        PathObservation path = PathObservation.decode(summary, null);

        assertEquals(path.relationPathCondition().toString(), 0,
                path.relationPathCondition().size());
    }

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
                Collections.singletonList(path));

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
                "PARTIAL").toJson();

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

    /**
     * README CASE-1's acceptance condition, for the last evidence family that
     * was still unioned at row level.
     *
     * <p>Two paths of one occurrence resolved the same {@code edgeId}
     * differently -- the importer resolves every edge against that path's own
     * recorded read-from, so each stamped its own writer and location onto it
     * -- and both rows survived the merge's payload dedup precisely because
     * they differ.  Neither resolution may reach the other case: the merged
     * row states only what every case agreed on, and each divergent row is
     * offered under exactly the case selector of the case that observed it,
     * which is the selector that case's own guard is lowered against.</p>
     */
    @Test
    public void divergentEdgeResolutionsStayInTheCaseThatObservedThem() {
        JsonObject agreed = binding("EDGE.AGREED", 40L,
                RecordedReadFrom.PROVENANCE_EXACT, "INSTANCE_FIELD/7#24");
        JsonObject firstArm = binding("EDGE.SHARED", 51L,
                RecordedReadFrom.PROVENANCE_EXACT, "INSTANCE_FIELD/7#31");
        JsonObject secondArm = binding("EDGE.SHARED", 52L,
                RecordedReadFrom.PROVENANCE_GUARDED, "INSTANCE_FIELD/9#31");

        RelationSummary merged = RelationSummary.guardedPathMerge(
                OutputClosureCodec.decode(versionedSummary(1)),
                Arrays.asList(
                        PathObservation.decode(pathSummary(1,
                                Arrays.asList(agreed, firstArm)), null),
                        PathObservation.decode(pathSummary(2,
                                Arrays.asList(agreed, secondArm)), null)));
        JsonObject row = merged.toJson();

        // Only the resolution both executions made is a fact of the whole
        // relation; the two that disagree never reach row level.
        JsonArray rowLevel = row.getAsJsonArray("edgeBindings");
        assertEquals(1, rowLevel.size());
        assertEquals("EDGE.AGREED", rowLevel.get(0).getAsJsonObject()
                .get("edgeId").getAsString());

        JsonArray cases = row.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        assertEquals(2, cases.size());
        List<String> selectors = new ArrayList<>();
        for (int index = 0; index < cases.size(); index++) {
            JsonObject item = cases.get(index).getAsJsonObject();
            JsonArray caseBindings = item.getAsJsonArray("edgeBindings");
            assertEquals(1, caseBindings.size());
            assertEquals("EDGE.SHARED", caseBindings.get(0).getAsJsonObject()
                    .get("edgeId").getAsString());
            selectors.add(RecordedSessionModel.caseSelector(
                    RecordedSessionModel.caseOwner(
                            row.get("regionId").getAsString(),
                            item.get("occurrenceId").getAsString(),
                            item.get("caseId").getAsString(), index)));
        }
        assertEquals(2, new LinkedHashSet<>(selectors).size());

        // The acceptance condition itself: each resolution of EDGE.SHARED is
        // offered under its own case's selector and under no other, so no
        // case guard can enable the writer the other case resolved.
        int attributed = 0;
        for (JsonObject offered : merged.edgeBindings()) {
            String edgeId = offered.get("edgeId").getAsString();
            if ("EDGE.AGREED".equals(edgeId)) {
                assertFalse(offered.has(RelationSummary.CASE_SELECTORS));
                continue;
            }
            assertEquals("EDGE.SHARED", edgeId);
            JsonArray owners = offered.getAsJsonArray(
                    RelationSummary.CASE_SELECTORS);
            assertEquals(1, owners.size());
            String owner = owners.get(0).getAsString();
            assertTrue(selectors.contains(owner));
            String other = selectors.get(1 - selectors.indexOf(owner));
            for (JsonElement named : owners) {
                assertFalse(other.equals(named.getAsString()));
            }
            attributed++;
        }
        assertEquals(2, attributed);
        assertEquals(3, merged.edgeBindings().size());
    }

    @Test
    public void decodeRejectsSummariesOutsideTheCurrentSchema() {
        JsonObject current = RelationSummary.guardedPathMerge(
                OutputClosureCodec.decode(versionedSummary(1)),
                Collections.singletonList(PathObservation.decode(
                        versionedSummary(1), null))).toJson();

        JsonObject missingVersion = current.deepCopy();
        missingVersion.remove("schemaVersion");
        assertSummaryRejected(missingVersion);
        JsonObject missingKind = current.deepCopy();
        missingKind.remove("kind");
        assertSummaryRejected(missingKind);
        JsonObject wrongVersion = current.deepCopy();
        wrongVersion.addProperty("schemaVersion", 2);
        assertSummaryRejected(wrongVersion);
        JsonObject stringVersion = current.deepCopy();
        stringVersion.addProperty("schemaVersion", "1");
        assertSummaryRejected(stringVersion);
        JsonObject wrongKind = current.deepCopy();
        wrongKind.addProperty("kind", "CONCOLIC_REGION_RESULT");
        assertSummaryRejected(wrongKind);
    }

    /** One resolved read-from row of the shape the importer stamps. */
    private static JsonObject binding(String edgeId, long writerEventSeq,
                                      String provenance, String location) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromRegion", "REGION.U");
        binding.addProperty("toRegion", "REGION.V");
        binding.addProperty("fromOccurrenceId", "REGION.U/occurrence-1");
        binding.addProperty("toOccurrenceId", "REGION.V/occurrence-1");
        binding.addProperty("fromOutputPort", "REGION.U.out.0");
        binding.addProperty("toInputPort", "REGION.V.in.0");
        binding.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty(RecordedReadFrom.EDGE_PROVENANCE, provenance);
        binding.addProperty("locationKey", location);
        binding.addProperty("writerEventSeq", writerEventSeq);
        binding.addProperty("readerEventSeq", 60L);
        return binding;
    }

    /** One imported path of the shared occurrence, with its own bindings. */
    private static JsonObject pathSummary(int outputValue,
                                          List<JsonObject> bindings) {
        JsonObject summary = versionedSummary(1);
        summary.addProperty("taskId", "TASK.V." + outputValue);
        JsonObject outputs = new JsonObject();
        outputs.add(port(), constant(outputValue));
        summary.add("outputExpressions", outputs);
        JsonArray encoded = new JsonArray();
        for (JsonObject binding : bindings) encoded.add(binding.deepCopy());
        summary.add("edgeBindings", encoded);
        return summary;
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
        summary.addProperty("schemaVersion", RelationSummary.SCHEMA_VERSION);
        summary.addProperty("kind", RelationSummary.KIND);
        summary.addProperty("taskId", "TASK.V");
        summary.addProperty("goalId", "GOAL.V");
        summary.addProperty("regionId", region);
        summary.addProperty("sourceKey", "NAMENODE/active/epoch-0");
        String plannedOccurrence = "REGION.V/occurrence-1";
        summary.addProperty("occurrenceId", plannedOccurrence + "#a1");
        summary.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
        summary.addProperty(PathObservation.PLANNED_OCCURRENCE_ID,
                plannedOccurrence);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(summary);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(summary);
        OutputClosureCodec.writeTo(summary, OutputClosureCodec.singleton(
                "RELATION.V", region, Collections.<String>emptyList(), port(), cell,
                "HEAP_STATE", "int", slice));
        summary.add("symbolicInputs", new JsonArray());
        summary.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
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

    private static void assertSummaryRejected(JsonObject summary) {
        try {
            RelationSummary.decode(summary);
            fail("unsupported relation summary schema was accepted");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("unsupported schema"));
        }
    }

    private static void assertPathRejected(JsonObject summary) {
        try {
            PathObservation.decode(summary, null);
            fail("incomplete activation tuple was accepted");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("activation tuple"));
        }
    }

    private static JsonObject symbol(String name) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", name);
        return expression;
    }

    private static JsonObject binary(JsonObject left, String operator,
                                     JsonObject right, String position) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        expression.addProperty("_java_type", "Z");
        expression.addProperty("_op", operator);
        expression.addProperty("_code_position", position);
        expression.add("_left", left.deepCopy());
        expression.add("_right", right.deepCopy());
        return expression;
    }
}
