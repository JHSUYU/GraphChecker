package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicSummaryImporterReplayAdmissionTest {
    @Test
    public void acceptsReplayWithoutDynamicSelectors() {
        List<String> failures =
                ConcolicSummaryImporter.dynamicRebindingAdmissionFailures(
                        raw(new JsonArray(), new JsonArray()));

        assertTrue(failures.toString(), failures.isEmpty());
    }

    @Test
    public void acceptsFreshMapEntrySelectorCapturedByReplay() {
        JsonObject planned = freshMapAssignment();
        JsonObject applied = planned.deepCopy();
        applied.remove("solverSymbol");
        applied.addProperty("entryReadObservationId", "MAP.READ.1");
        applied.add("keyExpression", integerKey(7));
        applied.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        applied.addProperty("freshEntrySelectorCaptured", true);
        applied.addProperty("sameSeedEntryClaimed", false);

        JsonObject rawBinding = freshMapBinding(applied,
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        List<String> failures =
                ConcolicSummaryImporter.dynamicRebindingAdmissionFailures(
                        raw(array(applied), array(rawBinding)));

        assertTrue(failures.toString(), failures.isEmpty());
    }

    @Test
    public void rejectsFreshMapReplayWithoutCapturedKey() {
        JsonObject applied = freshMapAssignment();
        applied.addProperty("freshEntrySelectorCaptured", false);
        applied.addProperty("sameSeedEntryClaimed", false);
        JsonObject binding = freshMapBinding(applied,
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");

        List<String> failures =
                ConcolicSummaryImporter.dynamicRebindingAdmissionFailures(
                        raw(array(applied), array(binding)));

        assertTrue(failures.toString(), failures.toString().contains(
                "SELECTOR_EVIDENCE_MISMATCH"));
    }

    @Test
    public void rejectsDuplicateFreshMapRuntimeBinding() {
        JsonObject applied = freshMapAssignment();
        applied.addProperty("entryReadObservationId", "MAP.READ.1");
        applied.add("keyExpression", integerKey(7));
        applied.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        applied.addProperty("freshEntrySelectorCaptured", true);
        applied.addProperty("sameSeedEntryClaimed", false);
        JsonObject binding = freshMapBinding(applied,
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");

        List<String> failures =
                ConcolicSummaryImporter.dynamicRebindingAdmissionFailures(
                        raw(array(applied), array(binding, binding.deepCopy())));

        assertTrue(failures.toString(), failures.toString().contains(
                "RAW_BINDING_NOT_UNIQUE"));
    }

    @Test
    public void acceptsContainerReboundInReplayActivation() {
        JsonObject planned = containerAssignment();
        JsonObject applied = replayedContainer(planned, "ACT.REPLAY");
        JsonObject binding = containerBinding(applied);
        List<String> failures =
                ConcolicSummaryImporter.dynamicRebindingAdmissionFailures(
                        raw(array(applied), array(binding)));

        assertTrue(failures.toString(), failures.isEmpty());
    }

    @Test
    public void rejectsContainerTokenOutsideReplayActivation() {
        JsonObject planned = containerAssignment();
        JsonObject applied = replayedContainer(planned, "ACT.WRONG");
        JsonObject binding = containerBinding(applied);
        List<String> failures =
                ConcolicSummaryImporter.dynamicRebindingAdmissionFailures(
                        raw(array(applied), array(binding)));

        assertFalse(failures.toString(), failures.isEmpty());
        assertTrue(failures.toString(), failures.toString().contains(
                "SELECTOR_EVIDENCE_MISMATCH"));
    }

    private static JsonObject replayedContainer(
            JsonObject planned, String tokenScope) {
        JsonObject applied = planned.deepCopy();
        applied.remove("solverSymbol");
        JsonObject selector = applied.getAsJsonObject("containerSelector");
        selector.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        selector.addProperty("containerObjectToken", 301L);
        selector.addProperty("elementObjectToken", 302L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", tokenScope);
        selector.addProperty("containerObservationLocation",
                "EXACT_CONSUMED_LEAF_OBSERVATION");
        selector.addProperty("authority",
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                        + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
        selector.addProperty("complete", true);
        applied.addProperty("sameSourceContainerIdentityClaimed", false);
        applied.addProperty("currentContainerSelectorCaptured", true);
        return applied;
    }

    private static JsonObject raw(JsonArray assignments,
                                  JsonArray bindings) {
        JsonObject raw = new JsonObject();
        raw.addProperty("activationId", "ACT.REPLAY");
        raw.add("modelAssignmentsApplied", assignments);
        raw.add("dynamicFieldBindings", bindings);
        return raw;
    }

    private static JsonObject freshMapAssignment() {
        JsonObject assignment = baseAssignment(
                "REGION.3.in.0.field.fresh.occ.1");
        assignment.addProperty("materializationSiteId", "SITE.FIELD");
        assignment.addProperty("materializationOccurrence", 1);
        assignment.addProperty("dynamicReplayRebindingAuthority",
                "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                        + "FRESH_ENTRY_REBIND_V1");
        assignment.addProperty("sourceEntrySelectorRetained", false);
        assignment.add("materializationPath", strings("expiry"));
        return assignment;
    }

    private static JsonObject freshMapBinding(JsonObject applied,
                                              String authority) {
        JsonObject binding = new JsonObject();
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("authority", authority);
        for (String field : new String[]{"baseInputSymbol",
                "dynamicBindingId", "dynamicFieldSymbol",
                "materializationSiteId", "materializationOccurrence",
                "entryReadObservationId", "keyExpression",
                "keyExpressionAuthority"}) {
            if (applied.has(field)) {
                binding.add(field, applied.get(field).deepCopy());
            }
        }
        binding.add("fieldPath", applied.getAsJsonArray(
                "materializationPath").deepCopy());
        binding.addProperty("complete", true);
        return binding;
    }

    private static JsonObject containerAssignment() {
        JsonObject assignment = baseAssignment(
                "REGION.3.in.0.field.array.occ.1");
        assignment.addProperty("materializationSiteId", "SITE.FIELD");
        assignment.addProperty("materializationOccurrence", 1);
        assignment.addProperty("dynamicFieldBindingKind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        assignment.add("materializationPath", strings("id"));
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.ARRAY.3");
        selector.addProperty("containerInputPort", "REGION.3.in.array");
        selector.addProperty("containerInputCell",
                "<example.Keys: example.Key[] keys>");
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", 0);
        selector.addProperty("elementOccurrence", 1);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "int");
        assignment.add("containerSelector", selector);
        assignment.addProperty("containerReplayRebindingAuthority",
                "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                        + "IDENTITY_REBIND_V1");
        assignment.addProperty("sourceContainerObjectTokensRetained", false);
        return assignment;
    }

    private static JsonObject containerBinding(JsonObject applied) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("kind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                        + "STABLE_FIELD_SITE_OCCURRENCE");
        for (String field : new String[]{"baseInputSymbol",
                "dynamicBindingId", "dynamicFieldSymbol",
                "materializationSiteId", "materializationOccurrence"}) {
            binding.add(field, applied.get(field).deepCopy());
        }
        binding.add("fieldPath", applied.getAsJsonArray(
                "materializationPath").deepCopy());
        JsonObject selector = applied.getAsJsonObject(
                "containerSelector").deepCopy();
        binding.add("containerSelector", selector);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope",
                selector.get("objectTokenScope").getAsString());
        binding.addProperty("complete", true);
        return binding;
    }

    private static JsonObject baseAssignment(String dynamic) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        assignment.addProperty("baseInputSymbol", "REGION.3.in.0");
        assignment.addProperty("dynamicFieldSymbol", dynamic);
        assignment.addProperty("engineSymbol", dynamic);
        assignment.addProperty("solverSymbol", "solver_1");
        assignment.addProperty("inputSymbol", "REGION.3.in.0");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "41");
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        return assignment;
    }

    private static JsonObject integerKey(int value) {
        JsonObject key = new JsonObject();
        key.addProperty("_type", "ConstExpr");
        key.addProperty("_java_type", "java/lang/Integer");
        key.addProperty("_exp", "Y_I_" + value);
        return key;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    private static JsonArray array(JsonObject... values) {
        JsonArray result = new JsonArray();
        for (JsonObject value : values) result.add(value);
        return result;
    }
}
