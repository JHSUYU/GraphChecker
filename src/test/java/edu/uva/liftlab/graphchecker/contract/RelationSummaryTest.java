package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;
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

    @Test
    public void selectedBranchKeepsOnlyItsExactFieldDefinition() {
        JsonObject summary = versionedSummary(1);
        String site = "<test.Worker: void run()>#u7";
        JsonObject member = summary.getAsJsonObject(
                        OutputClosureContract.FIELD)
                .getAsJsonArray("members").get(0).getAsJsonObject();
        member.getAsJsonObject("slice").getAsJsonArray("sites").add(site);

        String map = "M_L_field_REGION.V.in.map";
        String expiry = "M_J_field_REGION.V.in.expiry";
        String unrelated = "M_I_field_REGION.V.in.keyId";
        JsonObject expiryDefinition = exactFieldBinding(map, expiry, 24);
        JsonObject selectedBranch = binary(symbol(expiry, "J"), "<",
                constant(100));
        JsonObject unrelatedDefinition = exactFieldBinding(map, unrelated,
                32);
        JsonArray path = new JsonArray();
        path.add(expiryDefinition);
        path.add(selectedBranch);
        path.add(unrelatedDefinition);
        summary.add("pathCondition", path);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(
                BranchWitness.pcPredicate(site,
                        "<test.Worker: void run()>", 7, 1, 1,
                        selectedBranch, 1), 1,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        summary.add("branchMappings", mappings);

        PathObservation observation = PathObservation.decode(summary, null);
        JsonArray projected = observation.relationPathCondition();

        assertEquals(2, projected.size());
        String rendered = CanonicalJson.render(projected);
        assertTrue(rendered.contains(expiry));
        assertTrue(rendered.contains("symbolizeExactField"));
        assertFalse(rendered.contains(unrelated));
    }

    @Test
    public void outputValueKeepsItsExactFieldDefinition() {
        JsonObject summary = versionedSummary(1);
        String map = "M_L_field_REGION.V.in.map";
        String keyId = "M_I_field_REGION.V.in.keyId";
        JsonObject member = summary.getAsJsonObject(
                        OutputClosureContract.FIELD)
                .getAsJsonArray("members").get(0).getAsJsonObject();
        member.getAsJsonObject("slice").getAsJsonArray("inputPorts")
                .add("REGION.V.in.keyId");
        summary.getAsJsonObject("outputExpressions").add(port(),
                symbol(keyId, "I"));
        JsonArray path = new JsonArray();
        path.add(exactFieldBinding(map, keyId, 32));
        summary.add("pathCondition", path);

        PathObservation observation = PathObservation.decode(summary, null);

        JsonArray projected = observation.relationPathCondition();
        assertEquals(1, projected.size());
        String rendered = CanonicalJson.render(projected);
        assertTrue(rendered.contains("symbolizeExactField"));
        assertTrue(rendered.contains(keyId));
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

    private static JsonObject symbol(String name, String javaType) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", javaType);
        expression.addProperty("_exp", name);
        return expression;
    }

    private static JsonObject binary(JsonElement left, String operator,
                                     JsonElement right) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        expression.addProperty("_op", operator);
        expression.add("_left", left);
        expression.add("_right", right);
        return expression;
    }

    private static JsonObject exactFieldBinding(
            String map, String value, int fieldOffset) {
        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "ASSOCIATIVE");
        state.addProperty("operation", "STATE");
        state.addProperty("_java_type", "L");
        state.add("receiver", symbol(map, "L"));
        state.add("arguments", new JsonArray());

        JsonObject field = new JsonObject();
        field.addProperty("_type", "FieldAccessExpression");
        field.addProperty("_java_type", fieldOffset == 24 ? "J" : "I");
        field.addProperty("ownerClass", "test/Member");
        field.addProperty("fieldOffset", fieldOffset);
        field.add("owner", state);

        JsonObject binding = binary(field, "==", symbol(value,
                fieldOffset == 24 ? "J" : "I"));
        binding.addProperty("_code_position",
                "static void java.lang.System.symbolizeExactField("
                        + "jobject,jobject,jobject,jobject,jobject):-1");
        return binding;
    }
}
