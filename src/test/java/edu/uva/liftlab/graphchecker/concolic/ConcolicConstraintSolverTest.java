package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Paths;
import java.security.MessageDigest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicConstraintSolverTest {
    @Test
    public void z3ModelIsMappedToARealInputMaterialization() throws Exception {
        Assume.assumeTrue(z3Available());
        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task(binary(">", 3)),
                        activation(), Paths.get("z3"), 10_000L);

        assertEquals("SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("REGION.3.in.0",
                assignment.get("inputSymbol").getAsString());
        assertEquals("Z3_PATH_FLIP_MODEL",
                assignment.get("authority").getAsString());
        assertFalse(result.record.get("branchOverrideAllowed")
                .getAsBoolean());
    }

    @Test
    public void contradictoryPrefixAndFlipAreUnsat() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject task = task(binary(">", 3));
        task.getAsJsonArray("constraints").add(binary("<", 0));

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("UNSAT", result.record.get("status").getAsString());
        assertEquals(0, result.modelAssignments.size());
    }

    @Test
    public void unsupportedExpressionIsAnExplicitGap() throws Exception {
        JsonObject unsupported = new JsonObject();
        unsupported.addProperty("_type", "UNSUPPORTED_TEST_NODE");

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task(unsupported), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("UNSUPPORTED",
                result.record.get("status").getAsString());
        assertEquals("UNSUPPORTED_EXPRESSION_IR",
                result.record.get("reason").getAsString());
    }

    @Test
    public void vmClockPlaceholderIsUncontrolledAndNeverProjected()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject condition = binary("<", 0);
        condition.add("_right", currentTimePlaceholder(1));

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task(condition), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.record.get(
                "uncontrolledEnvironmentTermCount").getAsInt());
        assertEquals(0, result.record.get(
                "environmentModelAssignmentCount").getAsInt());
        assertTrue(result.record.get(
                "requiresUnforcedEnvironmentValidation").getAsBoolean());
        assertTrue(result.record.getAsJsonArray(
                "uncontrolledEnvironmentTerms").toString().contains(
                "currentTimeMills#1"));
        assertEquals(1, result.modelAssignments.size());
        assertEquals("REGION.3.in.0", result.modelAssignments.get(0)
                .getAsJsonObject().get("inputSymbol").getAsString());
        assertFalse(result.smtLib.contains(
                "get-value (environment__currentTimeMills"));
    }

    @Test
    public void replayProjectsOnlyFlipConditionInputsAndLeavesPrefixNatural()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String prefixRaw =
                "M_I_field_REGION.3.in.0_java/lang/Integer";
        String targetRaw =
                "M_I_field_REGION.3.in.1_java/lang/Integer";
        JsonObject prefix = binarySymbol(prefixRaw, ">", 0);
        JsonObject target = binarySymbol(targetRaw, "<", 0);
        JsonObject task = task(target);
        JsonArray constraints = new JsonArray();
        constraints.add(prefix);
        constraints.add(target);
        task.add("constraints", constraints);
        task.add("negatedCondition", target.deepCopy());

        JsonObject activation = new JsonObject();
        JsonArray materializations = new JsonArray();
        materializations.add(materialization("REGION.3.in.0", 0));
        materializations.add(materialization("REGION.3.in.1", 1));
        activation.add("materializations", materializations);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task, activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals("FLIP_CONDITION_DELTA_ONLY_V1", result.record.get(
                "modelProjectionPolicy").getAsString());
        assertEquals(2, result.record.get("controlledSymbolCount").getAsInt());
        assertEquals(1, result.record.get(
                "targetControlledSymbolCount").getAsInt());
        assertEquals(1, result.record.get(
                "unforcedPrefixControlledSymbolCount").getAsInt());
        assertEquals(1, result.modelAssignments.size());
        assertEquals("REGION.3.in.1", result.modelAssignments.get(0)
                .getAsJsonObject().get("inputSymbol").getAsString());
        assertTrue(result.record.getAsJsonArray(
                "unforcedPrefixControlledSymbols").toString().contains(
                prefixRaw));
    }

    @Test
    public void unverifiedPlaceholderKindIsAnExplicitIrGap()
            throws Exception {
        JsonObject condition = binary("<", 0);
        JsonObject placeholder = currentTimePlaceholder(1);
        placeholder.addProperty("_place_holder_func", "nanoTime");
        condition.add("_right", placeholder);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task(condition), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("UNSUPPORTED",
                result.record.get("status").getAsString());
        assertTrue(result.record.getAsJsonArray("unsupported").toString()
                .contains("UNVERIFIED_PLACEHOLDER_EXPRESSION:nanoTime#1"));
        assertEquals(0, result.record.get(
                "environmentModelAssignmentCount").getAsInt());
    }

    @Test
    public void unmappedFlipDependencyIsRejectedBeforeSolverExecution()
            throws Exception {
        JsonObject condition = binary(">", 3);
        condition.getAsJsonObject("_left").addProperty("_exp",
                "A[_2.length");

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task(condition), activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertEquals("FLIP_CONDITION_DEPENDS_ON_UNMATERIALIZABLE_SYMBOLS",
                result.record.get("reason").getAsString());
        assertFalse(result.record.get("solverInvoked").getAsBoolean());
        assertTrue(result.record.getAsJsonArray(
                "unmaterializableFlipSymbols").toString()
                .contains("A[_2.length"));
    }

    @Test
    public void exactOccurrenceTwoDynamicBindingDefersKeyToFreshReplay()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject first = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one");
        JsonObject second = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 2, "key-two");
        String dynamic = second.get("dynamicFieldSymbol").getAsString();
        JsonObject task = task(binarySymbol(dynamic, ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(first);
        bindings.add(second);
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals(dynamic,
                assignment.get("dynamicFieldSymbol").getAsString());
        assertEquals(2, assignment.get("materializationOccurrence")
                .getAsInt());
        assertEquals("REGION.3.in.0",
                assignment.get("baseInputSymbol").getAsString());
        assertFalse(assignment.has("expectedEntryKey"));
        assertFalse(assignment.has("keyExpression"));
        assertFalse(assignment.has("entryReadObservationId"));
        assertFalse(assignment.get("sourceEntrySelectorRetained")
                .getAsBoolean());
        assertEquals("EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                        + "FRESH_ENTRY_REBIND_V1",
                assignment.get("dynamicReplayRebindingAuthority")
                        .getAsString());
    }

    @Test
    public void exactArrayElementBindingProducesRuntimeContainerSelector()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject binding = containerBinding("REGION.3.in.0",
                "ENTRY.FIELD#id", 2, 1);
        String dynamic = binding.get("dynamicFieldSymbol").getAsString();
        JsonObject task = task(binarySymbol(dynamic, ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task, containerActivation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertFalse(assignment.has("expectedEntryKey"));
        JsonObject selector = assignment.getAsJsonObject(
                "containerSelector");
        assertEquals("BIND.ARRAY.1",
                selector.get("bindingId").getAsString());
        assertEquals("REGION.3.in.array",
                selector.get("containerInputPort").getAsString());
        assertEquals(2, selector.get("elementIndex").getAsInt());
        assertEquals(1, selector.get("elementOccurrence").getAsInt());
        assertEquals("EXACT_ARRAY_INDEX",
                selector.get("selectorAuthority").getAsString());
        assertEquals("example.Key", selector.get(
                "declaredFieldOwnerClass").getAsString());
        assertEquals("int",
                selector.get("declaredFieldType").getAsString());
        assertFalse(selector.has("containerObjectToken"));
        assertFalse(selector.has("objectTokenScope"));
        assertFalse(selector.has("complete"));
        assertEquals("EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                        + "IDENTITY_REBIND_V1",
                assignment.get("containerReplayRebindingAuthority")
                        .getAsString());
        assertFalse(assignment.get("sourceContainerObjectTokensRetained")
                .getAsBoolean());
    }

    @Test
    public void selectorOnlySnapshotLeafUsesUniqueDeclaredAction()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String site = "<example.Producer: int compute()>#u3";
        JsonObject binding = containerBinding("REGION.3.in.8", site,
                0, 1);
        binding.addProperty("fieldSignature",
                "<example.BooleanLeaf: boolean enabled>");
        JsonArray path = new JsonArray();
        path.add("state");
        path.add("guard");
        path.add("enabled");
        binding.add("fieldPath", path);
        JsonObject selector = binding.getAsJsonObject("containerSelector");
        selector.addProperty("declaredFieldOwnerClass",
                "example.BooleanLeaf");
        selector.addProperty("declaredFieldType", "boolean");
        String dynamic = binding.get("dynamicFieldSymbol").getAsString();
        String engine = "M_Z_field_" + dynamic
                + "_example/BooleanLeaf";
        JsonObject condition = binarySymbol(engine, "!=", 0);
        condition.getAsJsonObject("_left").addProperty("_java_type", "Z");
        JsonObject task = task(condition);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        task.add("dynamicFieldBindings", bindings);

        JsonObject activation = new JsonObject();
        JsonObject container = new JsonObject();
        container.addProperty("symbol", "REGION.3.in.array");
        container.addProperty("cell",
                "<example.Keys: example.Key[] keys>");
        container.addProperty("location", "HEAP_OBJECT_FIELD");
        container.addProperty("bindingMode",
                "CONTAINER_INPUT_OBSERVATION");
        JsonArray materializations = new JsonArray();
        materializations.add(container);
        activation.add("materializations", materializations);
        JsonObject leaf = new JsonObject();
        leaf.addProperty("symbol", "REGION.3.in.8");
        leaf.addProperty("cell", "<example.State: example.Guard state>"
                + "#field:guard#field:enabled");
        leaf.addProperty("field",
                "<example.BooleanLeaf: boolean enabled>");
        leaf.addProperty("leafFieldSignature",
                "<example.BooleanLeaf: boolean enabled>");
        leaf.addProperty("leafOwnerClass", "example.BooleanLeaf");
        leaf.addProperty("leafField", "enabled");
        leaf.addProperty("accessSiteId", site);
        leaf.addProperty("bindingMode", "FIELD_ACCESS");
        leaf.addProperty("location", "HEAP_OBJECT_FIELD");
        leaf.addProperty("fieldPathAuthority",
                "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
        leaf.add("fieldPath", path.deepCopy());
        JsonArray declared = new JsonArray();
        declared.add(leaf);
        activation.add("symbolize", declared);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task, activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals("REGION.3.in.8",
                assignment.get("inputSymbol").getAsString());
        assertEquals(path, assignment.get("materializationPath"));
        assertEquals("REGION.3.in.array", assignment.getAsJsonObject(
                "containerSelector").get("containerInputPort")
                .getAsString());
        assertEquals("REGION.3.in.8", assignment.getAsJsonObject(
                "target").get("symbol").getAsString());
    }

    @Test
    public void missingOrDiscoveryArraySelectorIsInvalidRegistry()
            throws Exception {
        JsonObject missing = containerBinding("REGION.3.in.0",
                "ENTRY.FIELD#id", 0, 1);
        missing.remove("containerSelector");
        JsonObject discovery = containerBinding("REGION.3.in.0",
                "ENTRY.FIELD#id", 0, 1);
        discovery.getAsJsonObject("containerSelector").addProperty(
                "selectorAuthority", "DISCOVER_UNIQUE_IDENTITY_INDEX");
        for (JsonObject binding : new JsonObject[]{missing, discovery}) {
            JsonObject task = task(binarySymbol(binding.get(
                    "dynamicFieldSymbol").getAsString(), ">", 3));
            JsonArray bindings = new JsonArray();
            bindings.add(binding);
            task.add("dynamicFieldBindings", bindings);
            ConcolicConstraintSolver.Result result =
                    ConcolicConstraintSolver.solve(task,
                            containerActivation(), Paths.get("z3"),
                            10_000L);
            assertEquals("MATERIALIZATION_GAP",
                    result.record.get("status").getAsString());
            assertEquals("INVALID_DYNAMIC_FIELD_BINDING_REGISTRY",
                    result.record.get("reason").getAsString());
            assertFalse(result.record.get("solverInvoked").getAsBoolean());
        }
    }

    @Test
    public void realVmFieldWrapperAndOwnerSuffixResolveExactDynamicBinding()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject first = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one");
        JsonObject second = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 2, "key-two");
        String dynamic = second.get("dynamicFieldSymbol").getAsString();
        String engine = "M_J_field_" + dynamic
                + "_org/apache/hadoop/hdfs/security/token/block/BlockKey";
        JsonObject task = task(binarySymbol(engine, ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(first);
        bindings.add(second);
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        JsonObject assignment = result.modelAssignments.get(0)
                .getAsJsonObject();
        assertEquals(engine, assignment.get("engineSymbol").getAsString());
        assertEquals(dynamic,
                assignment.get("dynamicFieldSymbol").getAsString());
        assertEquals(2, assignment.get("materializationOccurrence")
                .getAsInt());
    }

    @Test
    public void malformedSuffixAndDynamicPrefixCollisionAreNotAssociated()
            throws Exception {
        JsonObject binding = dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one");
        String dynamic = binding.get("dynamicFieldSymbol").getAsString();
        JsonArray bindings = new JsonArray();
        bindings.add(binding);

        String[] rejected = {
                "M_J_field_" + dynamic + "0_java/lang/Long",
                "M_J_field_" + dynamic + "_java.lang.Long",
                "M_Q_field_" + dynamic + "_java/lang/Long"
        };
        for (String engine : rejected) {
            JsonObject task = task(binarySymbol(engine, ">", 3));
            task.add("dynamicFieldBindings", bindings.deepCopy());
            ConcolicConstraintSolver.Result result =
                    ConcolicConstraintSolver.solve(task, activation(),
                            Paths.get("z3"), 10_000L);
            assertEquals(engine + ": " + result.record,
                    "MATERIALIZATION_GAP",
                    result.record.get("status").getAsString());
            assertFalse(result.record.get("solverInvoked").getAsBoolean());
            assertTrue(result.record.getAsJsonArray(
                    "dynamicBindingResolutionGaps").toString().contains(
                    "ENGINE_SYMBOL_NOT_EXACT_DYNAMIC_BINDING"));
        }
    }

    @Test
    public void oneEntryBaseOnlyDynamicModelIsStillRejected()
            throws Exception {
        JsonObject task = task(binarySymbol("REGION.3.in.0", ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one"));
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertTrue(result.record.getAsJsonArray(
                "dynamicBindingResolutionGaps").toString().contains(
                "BASE_ONLY_DYNAMIC_INPUT_PROHIBITED"));
    }

    @Test
    public void twoDynamicEntriesNeverBroadcastABaseOnlyModel()
            throws Exception {
        JsonObject task = task(binarySymbol("REGION.3.in.0", ">", 3));
        JsonArray bindings = new JsonArray();
        bindings.add(dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 1, "key-one"));
        bindings.add(dynamicBinding("REGION.3.in.0",
                "ENTRY.FIELD#expiry", 2, "key-two"));
        task.add("dynamicFieldBindings", bindings);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(task, activation(),
                        Paths.get("z3"), 10_000L);

        assertEquals("MATERIALIZATION_GAP",
                result.record.get("status").getAsString());
        assertFalse(result.record.get("solverInvoked").getAsBoolean());
        assertTrue(result.record.getAsJsonArray(
                "dynamicBindingResolutionGaps").toString().contains(
                "AMBIGUOUS_DYNAMIC_BASE_INPUT"));
    }

    private static JsonObject activation() {
        JsonObject activation = new JsonObject();
        JsonArray materializations = new JsonArray();
        materializations.add(materialization("REGION.3.in.0", 0));
        activation.add("materializations", materializations);
        return activation;
    }

    private static JsonObject materialization(String symbol, int index) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", index);
        return action;
    }

    private static JsonObject containerActivation() {
        JsonObject activation = activation();
        JsonObject container = new JsonObject();
        container.addProperty("symbol", "REGION.3.in.array");
        container.addProperty("cell", "<example.Keys: example.Key[] keys>");
        container.addProperty("location", "HEAP_OBJECT_FIELD");
        container.addProperty("bindingMode", "FIELD_ACCESS");
        activation.getAsJsonArray("materializations").add(container);
        return activation;
    }

    private static JsonObject task(JsonObject condition) {
        JsonObject task = new JsonObject();
        task.addProperty("queryKey", "QUERY.0");
        task.addProperty("regionId", "REGION.3");
        JsonArray constraints = new JsonArray();
        constraints.add(condition);
        task.add("constraints", constraints);
        return task;
    }

    private static JsonObject binary(String operator, int constant) {
        return binarySymbol(
                "M_I_field_REGION.3.in.0_java/lang/Integer",
                operator, constant);
    }

    private static JsonObject binarySymbol(String raw, String operator,
                                           int constant) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", raw);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
    }

    private static JsonObject currentTimePlaceholder(int count) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "PlaceholderExpression");
        result.addProperty("_place_holder_func", "currentTimeMills");
        result.addProperty("_count", count);
        return result;
    }

    private static JsonObject dynamicBinding(String base, String site,
                                             int occurrence, String key)
            throws Exception {
        String dynamic = base + ".field." + sha256(site).substring(0, 12)
                + ".occ." + occurrence;
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        binding.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("fieldSignature", "<Key: long expiry>");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        binding.add("fieldPath", fieldPath);
        binding.addProperty("leafOwnerObjectToken", "OBJECT.old-run");
        binding.addProperty("entryReadObservationId", "ENTRY.READ."
                + occurrence);
        JsonObject keyExpression = new JsonObject();
        keyExpression.addProperty("_type", "ConstExpr");
        keyExpression.addProperty("_java_type", "Ljava/lang/String;");
        keyExpression.addProperty("_exp", key);
        binding.add("keyExpression", keyExpression);
        binding.addProperty("keyExpressionAuthority",
                "RUNTIME_MAP_ENTRY_READ_KEY_EXPRESSION");
        binding.addProperty("complete", true);
        return binding;
    }

    private static JsonObject containerBinding(String base, String site,
                                               int index, int occurrence)
            throws Exception {
        String dynamic = base + ".field." + sha256(site).substring(0, 12)
                + ".occ." + occurrence;
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 2);
        binding.addProperty("kind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                        + "STABLE_FIELD_SITE_OCCURRENCE");
        binding.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("fieldSignature", "<example.Key: int id>");
        JsonArray path = new JsonArray();
        path.add("id");
        binding.add("fieldPath", path);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.ARRAY.1");
        selector.addProperty("containerInputPort", "REGION.3.in.array");
        selector.addProperty("containerInputCell",
                "<example.Keys: example.Key[] keys>");
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", index);
        selector.addProperty("elementOccurrence", occurrence);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "int");
        selector.addProperty("containerObjectToken", 301L);
        selector.addProperty("elementObjectToken", 302L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.SOURCE");
        selector.addProperty("authority",
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_ACTIVATION_"
                        + "LOCAL_ELEMENT_IDENTITY");
        selector.addProperty("complete", true);
        binding.add("containerSelector", selector);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope", "ACT.SOURCE");
        binding.addProperty("complete", true);
        return binding;
    }

    private static String sha256(String value) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] bytes = digest.digest(value.getBytes(StandardCharsets.UTF_8));
        StringBuilder result = new StringBuilder();
        for (byte current : bytes) {
            result.append(String.format("%02x", current & 0xff));
        }
        return result.toString();
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception ignored) {
            return false;
        }
    }
}
