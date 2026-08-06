package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

public class RegionInstancePlanTest {
    @Test
    public void occurrenceCatalogCollapsesEquivalentExactGoals() {
        String instance = "REGION.1@test#call1";
        JsonObject canonical = targetGoal("GOAL.LOGICAL", "canonical");
        JsonObject first = targetGoal("GOAL.EXACT.2", "exact");
        JsonObject duplicate = first.deepCopy();
        duplicate.addProperty("goalId", "GOAL.EXACT.1");
        first.getAsJsonArray("symbolize").get(0).getAsJsonObject()
                .addProperty("eventSeq", 101L);
        duplicate.getAsJsonArray("symbolize").get(0).getAsJsonObject()
                .addProperty("eventSeq", 202L);
        duplicate.getAsJsonArray("symbolize").get(0).getAsJsonObject()
                .addProperty("rootObjectId", 303L);

        JsonObject plan = plan(instance, canonical,
                occurrence(instance, 1L, first, duplicate));

        JsonArray catalog = RegionInstancePlan.decode(plan).goals().get(0)
                .occurrenceInstantiationCatalog()
                .getAsJsonArray("occurrences");

        assertEquals(1, catalog.size());
        assertEquals(6, catalog.get(0).getAsJsonObject()
                .getAsJsonArray("inputPortMap").size());
    }

    @Test(expected = IllegalArgumentException.class)
    public void occurrenceCatalogRejectsConflictingExactGoals() {
        String instance = "REGION.1@test#call1";
        JsonObject canonical = targetGoal("GOAL.LOGICAL", "canonical");
        JsonObject first = targetGoal("GOAL.EXACT.1", "exact");
        JsonObject conflict = first.deepCopy();
        conflict.addProperty("goalId", "GOAL.EXACT.2");
        conflict.getAsJsonArray("symbolize").get(0).getAsJsonObject()
                .addProperty("dependencyRole",
                        "CONCRETE_STRUCTURE_CARRIER");

        JsonObject plan = plan(instance, canonical,
                occurrence(instance, 1L, first, conflict));

        RegionInstancePlan.decode(plan).goals().get(0)
                .occurrenceInstantiationCatalog();
    }

    @Test
    public void occurrenceCatalogKeepsRepeatedAccessorSlotsDistinct() {
        JsonObject canonicalGoal = targetGoal("GOAL.LOGICAL", "canonical");
        JsonObject firstGoal = targetGoal("GOAL.EXACT.1", "canonical");
        JsonObject secondGoal = targetGoal("GOAL.EXACT.2", "exact");

        JsonObject plan = new JsonObject();
        plan.addProperty("schemaVersion", 3);
        plan.addProperty("kind", "CONCOLIC_REGION_PLAN");
        plan.addProperty("regionId", "REGION.1");
        plan.addProperty("regionInstanceId", "REGION.1@test#call1");
        plan.addProperty("logicalRegionId", "REGION.1@owner7");
        plan.addProperty("summaryReuseKey", "REGION.1@owner7");
        plan.addProperty("logicalInstanceCount", 2);
        plan.addProperty("rootCallId", 1);
        JsonArray goals = new JsonArray();
        goals.add(canonicalGoal);
        plan.add("closureGoals", goals);
        JsonArray occurrences = new JsonArray();
        occurrences.add(occurrence("REGION.1@test#call1", 1,
                firstGoal));
        occurrences.add(occurrence("REGION.1@test#call2", 2,
                secondGoal));
        plan.add("occurrences", occurrences);

        JsonObject catalog = RegionInstancePlan.decode(plan).goals().get(0)
                .occurrenceInstantiationCatalog();

        assertEquals(2, catalog.getAsJsonArray("occurrences").size());
        JsonObject second = catalog.getAsJsonArray("occurrences")
                .get(1).getAsJsonObject();
        JsonArray mappings = second.getAsJsonArray("inputPortMap");
        assertEquals(6, mappings.size());
        Map<String, String> exactByCanonical = new LinkedHashMap<>();
        for (JsonElement element : mappings) {
            JsonObject mapping = element.getAsJsonObject();
            exactByCanonical.put(
                    mapping.get("canonicalPort").getAsString(),
                    mapping.get("exactPort").getAsString());
        }
        for (int slot = 1; slot <= 6; slot++) {
            assertEquals("REGION.1.in.exact." + slot,
                    exactByCanonical.get(
                            "REGION.1.in.canonical." + slot));
        }
        assertFalse(second.has("closureGoals"));
    }

    @Test
    public void occurrenceCatalogSelectsRepeatedOutputByLocalOrdinal() {
        String first = "REGION.1@test#call1";
        String second = "REGION.1@test#call2";
        JsonObject canonicalGoal = outputGoal(
                "GOAL.LOGICAL.2", first, 1L, "canonical", 2);

        JsonObject plan = new JsonObject();
        plan.addProperty("schemaVersion", 3);
        plan.addProperty("kind", "CONCOLIC_REGION_PLAN");
        plan.addProperty("regionId", "REGION.1");
        plan.addProperty("regionInstanceId", first);
        plan.addProperty("logicalRegionId", "REGION.1@owner7");
        plan.addProperty("summaryReuseKey", "REGION.1@owner7");
        plan.addProperty("logicalInstanceCount", 2);
        plan.addProperty("rootCallId", 1L);
        JsonArray goals = new JsonArray();
        goals.add(canonicalGoal);
        plan.add("closureGoals", goals);
        JsonArray occurrences = new JsonArray();
        occurrences.add(occurrence(first, 1L,
                outputGoal("GOAL.EXACT.1.1", first, 1L, "first", 1),
                outputGoal("GOAL.EXACT.1.2", first, 1L, "first", 2)));
        occurrences.add(occurrence(second, 2L,
                outputGoal("GOAL.EXACT.2.1", second, 2L, "second", 1),
                outputGoal("GOAL.EXACT.2.2", second, 2L, "second", 2)));
        plan.add("occurrences", occurrences);

        JsonArray catalog = RegionInstancePlan.decode(plan).goals().get(0)
                .occurrenceInstantiationCatalog()
                .getAsJsonArray("occurrences");

        assertEquals(2, catalog.size());
        assertOutputMapping(catalog.get(0).getAsJsonObject(),
                "REGION.1.out.canonical.2", "REGION.1.out.first.2");
        assertOutputMapping(catalog.get(1).getAsJsonObject(),
                "REGION.1.out.canonical.2", "REGION.1.out.second.2");
    }

    private static void assertOutputMapping(
            JsonObject occurrence, String canonical, String exact) {
        JsonArray mappings = occurrence.getAsJsonArray("outputPortMap");
        assertEquals(1, mappings.size());
        assertEquals(canonical, mappings.get(0).getAsJsonObject()
                .get("canonicalPort").getAsString());
        assertEquals(exact, mappings.get(0).getAsJsonObject()
                .get("exactPort").getAsString());
    }

    private static JsonObject outputGoal(
            String goalId, String instance, long rootCallId,
            String portStem, int occurrence) {
        String method = "<Test: void send(java.lang.String)>";
        String callee = "<Wire: void write(java.lang.String)>";
        String siteId = "CALL_ARGUMENT:" + method + "#u15:"
                + callee + "#arg3";
        String port = "REGION.1.out." + portStem + "." + occurrence;
        String cell = method + "::$r5";

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE." + portStem
                + "." + occurrence);
        capture.addProperty("captureKind", "CALL_ARGUMENT");
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("definitionMethod", method);
        capture.addProperty("definitionUnitIndex", 15);
        capture.addProperty("declaredCallee", callee);
        capture.addProperty("argumentIndex", 3);
        capture.addProperty("javaType", "java.lang.String");

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        JsonArray staticSites = new JsonArray();
        staticSites.add(method + "#u15");
        slice.add("staticSites", staticSites);
        JsonArray methods = new JsonArray();
        methods.add(method);
        slice.add("methods", methods);
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("causalEdges", new JsonArray());
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());

        JsonObject closure = OutputClosureCodec.singleton(
                "REGION.1", instance, rootCallId, port, cell,
                "REGION_OUTPUT", "java.lang.String", slice).toJson();
        JsonObject output = closure.getAsJsonArray("members").get(0)
                .getAsJsonObject().getAsJsonObject("output");
        output.addProperty("outputSiteId", siteId);
        output.addProperty("outputOccurrence", occurrence);
        output.addProperty("replayOccurrence", occurrence);
        JsonObject encodedCapture = closure.getAsJsonArray("members").get(0)
                .getAsJsonObject().getAsJsonObject("slice")
                .getAsJsonArray("captureBindings").get(0)
                .getAsJsonObject();
        encodedCapture.addProperty("outputSiteId", siteId);
        encodedCapture.addProperty("outputOccurrence", occurrence);
        encodedCapture.addProperty("replayOccurrence", occurrence);

        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", goalId);
        goal.addProperty("kind", "OUTPUT_RELATION_CLOSURE");
        goal.addProperty("outputSiteId", siteId);
        goal.addProperty("outputOccurrence", occurrence);
        goal.addProperty("replayOccurrence", occurrence);
        JsonArray runtimeMethods = new JsonArray();
        runtimeMethods.add(method);
        goal.add("runtimeDefinitionMethods", runtimeMethods);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        admission.add("blockers", new JsonArray());
        goal.add("admission", admission);
        goal.add("symbolize", new JsonArray());
        goal.add("branches", new JsonArray());
        goal.add("edgeBindings", new JsonArray());
        goal.add(OutputClosureContract.FIELD, closure);
        return goal;
    }

    private static JsonObject targetGoal(String goalId, String portStem) {
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", goalId);
        goal.addProperty("kind", "TARGET_REACH_CLOSURE");
        JsonArray methods = new JsonArray();
        methods.add("<Test: void removeExpiredKeys()>");
        goal.add("runtimeDefinitionMethods", methods);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        admission.add("blockers", new JsonArray());
        goal.add("admission", admission);
        JsonArray symbolize = new JsonArray();
        for (int slot = 1; slot <= 6; slot++) {
            symbolize.add(accessorPort(portStem, slot));
        }
        goal.add("symbolize", symbolize);
        goal.add("branches", new JsonArray());
        goal.add("edgeBindings", new JsonArray());
        return goal;
    }

    private static JsonObject accessorPort(String stem, int slot) {
        String caller = "<Test: void removeExpiredKeys()>";
        String callee = "<Key: long getExpiryDate()>";
        String field = "<Key: long expiryDate>";
        JsonObject port = new JsonObject();
        port.addProperty("portId", "REGION.1.in." + stem + "." + slot);
        port.addProperty("symbol", "REGION.1.in." + stem + "." + slot);
        port.addProperty("cell", field);
        port.addProperty("location", "HEAP_OBJECT_FIELD");
        port.addProperty("sourceKind", "ACCESSOR_RETURN");
        port.addProperty("rootKind", "OBSERVED_FIELD_RECEIVER");
        port.addProperty("javaType", "long");
        port.addProperty("bindingMode", "FIELD_ACCESS");
        port.addProperty("dependencyRole", "VALUE_FRONTIER");
        port.addProperty("accessorOccurrence", slot);
        port.addProperty("replayOccurrence", slot);
        port.addProperty("siteId", caller + "#u11");
        port.addProperty("unitIndex", 11);
        port.addProperty("accessorCallerMethod", caller);
        port.addProperty("accessorCallUnitIndex", 11);
        port.addProperty("declaredCallee", callee);
        port.addProperty("accessorDeclaredCallee", callee);
        port.addProperty("accessorImplementationMethod", callee);
        port.addProperty("declaredFieldSignature", field);
        port.addProperty("accessFieldSignature", field);
        port.addProperty("leafFieldSignature", field);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiryDate");
        port.add("fieldPath", fieldPath);
        JsonArray fieldPaths = new JsonArray();
        fieldPaths.add(fieldPath.deepCopy());
        port.add("fieldPaths", fieldPaths);
        JsonArray declarations = new JsonArray();
        declarations.add(field);
        port.add("fieldPathDeclarations", declarations);
        return port;
    }

    private static JsonObject plan(String instance, JsonObject goal,
                                   JsonObject... occurrences) {
        JsonObject plan = new JsonObject();
        plan.addProperty("schemaVersion", 3);
        plan.addProperty("kind", "CONCOLIC_REGION_PLAN");
        plan.addProperty("regionId", "REGION.1");
        plan.addProperty("regionInstanceId", instance);
        plan.addProperty("logicalRegionId", "REGION.1@owner7");
        plan.addProperty("summaryReuseKey", "REGION.1@owner7");
        plan.addProperty("logicalInstanceCount", occurrences.length);
        plan.addProperty("rootCallId", 1L);
        JsonArray goals = new JsonArray();
        goals.add(goal);
        plan.add("closureGoals", goals);
        JsonArray exact = new JsonArray();
        for (JsonObject occurrence : occurrences) exact.add(occurrence);
        plan.add("occurrences", exact);
        return plan;
    }

    private static JsonObject occurrence(
            String instance, long rootCallId, JsonObject... exactGoals) {
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("regionInstanceId", instance);
        occurrence.addProperty("rootCallId", rootCallId);
        occurrence.addProperty("ownerId", 7);
        occurrence.addProperty("laneId", 11 + rootCallId);
        occurrence.addProperty("spanId", 101 + rootCallId);
        JsonArray goals = new JsonArray();
        for (JsonObject goal : exactGoals) goals.add(goal);
        occurrence.add("closureGoals", goals);
        return occurrence;
    }
}
