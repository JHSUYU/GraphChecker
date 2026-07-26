package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

public class ConcolicRegionRuntimeTest {
    @Test
    public void materializesExactStaticPrimitiveReadFromSolverModel()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.StaticConsumer: void run()>";
        String method = "<example.StaticConsumer: int compute()>";
        String field = "<example.StaticInputs: int t>";
        String symbol = "REGION.TEST.in.t";

        JsonObject activation = symbolicTask(
                "ACT.MODEL.STATIC.PRIMITIVE", root, 1);
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", field);
        action.addProperty("field", field);
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature", field);
        action.addProperty("accessMethod", method);
        action.addProperty("accessUnitIndex", 7);
        action.addProperty("accessSiteId", method + "#u7");
        action.addProperty("accessSiteAuthority",
                "RUNTIME_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1");
        action.addProperty("javaType", "int");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("t");
        action.add("fieldPath", fieldPath);
        action.addProperty("mode", "SYMBOLIC");
        activation.add("inputActions", singleton(action));

        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "M_I_field_" + symbol);
        assignment.addProperty("solverSymbol", "sym_t");
        assignment.addProperty("inputSymbol", symbol);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "21");
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        assignment.add("target", action.deepCopy());
        JsonArray materializationPath = new JsonArray();
        materializationPath.add("t");
        assignment.add("materializationPath", materializationPath);
        activation.add("modelAssignments", singleton(assignment));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "concrete-model-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            long token = ConcolicRegionRuntime.enterRegionFrame(root,
                    new Object(), new Object[0]);
            assertTrue(token > 0L);
            Object materialized = ConcolicRegionRuntime
                    .materializeStaticPrimitiveField(method, 7, field, "t",
                            Integer.valueOf(10));
            assertEquals(Integer.valueOf(21), materialized);
            ConcolicRegionRuntime.exitRegionFrame(root, null, "");

            JsonObject result = resultRows(results).get(0);
            assertFalse(result.has("activationId"));
            assertEquals("TASK.ACT.MODEL.STATIC.PRIMITIVE",
                    result.get("taskId").getAsString());
            assertEquals(1, result.getAsJsonArray(
                    "modelAssignmentsApplied").size());
            JsonObject applied = result.getAsJsonArray(
                    "modelAssignmentsApplied").get(0).getAsJsonObject();
            assertEquals(1, applied.size());
            assertEquals("M_I_field_" + symbol,
                    applied.get("modelAssignmentKey").getAsString());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }


    private static JsonObject testIntegerPredicate(String operator) {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "REGION.TEST.in.0");
        JsonObject zero = new JsonObject();
        zero.addProperty("_type", "ConstExpr");
        zero.addProperty("_java_type", "I");
        zero.addProperty("_exp", "Y_I_0");
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.add("_left", left);
        condition.addProperty("_op", operator);
        condition.add("_right", zero);
        return condition;
    }

    private static JsonObject runExactBranchEvent(boolean foreignOwner)
            throws Exception {
        return runExactBranchEvent(foreignOwner, false);
    }

    private static JsonObject runExactBranchEvent(boolean foreignOwner,
                                                  boolean conditionless)
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String method = "<example.Target: java.lang.Object lookup(int)>";
        JsonObject activation = symbolicTask("ACT.EXACT.BRANCH",
                method, 1);
        activation.addProperty("regionId", "REGION.EXACT.BRANCH");
        activation.addProperty("test", "exact-branch-test");
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "exact-branch-test");
        try {
            ExactBranchEngine.reset();
            ExactBranchEngine.foreignOwner = foreignOwner;
            ExactBranchEngine.conditionless = conditionless;
            ConcolicRegionRuntime.installEngineApiForTests(
                    ExactBranchEngine.class);
            long token = ConcolicRegionRuntime.enterRegion(method,
                    new Object(), null);
            assertTrue(token > 0L);
            long handle = ConcolicRegionRuntime.prepareBranch(method, 7,
                    "result != null");
            assertTrue(handle > 0L);
            long eventId = ExactBranchEngine.markBranch(method + "#u7",
                    (int) handle);
            assertTrue(ConcolicRegionRuntime.resolveBranch(handle, eventId,
                    method, 7, "result != null", true));
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(1, row.getAsJsonArray("branchMappings").size());
            return row.getAsJsonArray("branchMappings").get(0)
                    .getAsJsonObject();
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }





    private static JsonObject runExactSwitchEvent(
            String branchKind, String caseKeys, int observedSuccessor,
            int opcode, boolean outcome, int[] conditionKeys,
            String[] conditionOperators, int[] conditionIndices)
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String method = "<example.Target: int choose(int)>";
        String siteId = method + "#u7";
        JsonObject activation = symbolicTask("ACT.EXACT.SWITCH",
                method, 1);
        activation.addProperty("regionId", "REGION.EXACT.SWITCH");
        activation.addProperty("test", "exact-switch-test");
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", siteId);
        branch.addProperty("policy", "EXPLORE");
        JsonArray branches = new JsonArray();
        branches.add(branch);
        activation.add("branches", branches);
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "exact-switch-test");
        try {
            ExactSwitchEngine.configure(opcode, outcome, conditionKeys,
                    conditionOperators, conditionIndices);
            ConcolicRegionRuntime.installEngineApiForTests(
                    ExactSwitchEngine.class);
            long token = ConcolicRegionRuntime.enterRegion(method,
                    new Object(), null);
            assertTrue(token > 0L);
            long handle = ConcolicRegionRuntime.prepareBranch(method, 7,
                    "selector");
            assertTrue(handle > 0L);
            long eventId = ExactSwitchEngine.markBranch(siteId,
                    (int) handle);
            assertEquals(observedSuccessor,
                    ConcolicRegionRuntime.resolveSwitchBranch(handle,
                            eventId, method, 7, "selector", branchKind,
                            caseKeys, observedSuccessor));
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(1, row.getAsJsonArray("branchMappings").size());
            return row.getAsJsonArray("branchMappings").get(0)
                    .getAsJsonObject();
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }
































    @Test
    public void malformedOutputCaptureFailsClosedBeforeRegionEntry()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Root: void run()>";
        String cell = "<example.Root: int value>";
        JsonObject activation = symbolicTask(
                "ACT.OUTPUT.MALFORMED", root, 1);
        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "CALL_ARGUMENT");
        capture.addProperty("captureBindingId",
                "REGION.TEST.out.0.capture.0");
        capture.addProperty("outputPort", "REGION.TEST.out.0");
        capture.addProperty("outputCell", cell);
        capture.addProperty("accessRootInputPort",
                "REGION.TEST.in.0");
        capture.add("fieldPath", strings("value"));
        capture.addProperty("fieldSignature", cell);
        capture.addProperty("javaType", "int");
        attachDirectOutputClosure(activation, singleton(capture), "I");
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            boolean rejected = false;
            try {
                ConcolicRegionRuntime.enterRegion(root, new Object(), null);
            } catch (IllegalStateException expected) {
                rejected = true;
            }
            assertTrue(rejected);
            assertFalse(Files.exists(results));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void capturesExactFieldValueOnceAtNormalRegionExit()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Root: void run()>";
        String field = "<" + AssignmentOwner.class.getName()
                + ": java.lang.Object assigned>";
        JsonObject activation = symbolicTask("ACT.FIELD.OUTPUT", root,
                1);
        activation.addProperty("test", "field-output-capture-test");
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId",
                "REGION.TEST.out.field.exit-field");
        capture.addProperty("outputPort", "REGION.TEST.out.field");
        capture.addProperty("outputCell", field);
        capture.addProperty("accessRootInputPort", "REGION.TEST.in.field");
        capture.add("fieldPath", strings("assigned"));
        capture.addProperty("fieldSignature", field);
        capture.addProperty("javaType", "java.lang.Object");
        JsonObject prestate = new JsonObject();
        prestate.addProperty("symbol", "REGION.TEST.in.field");
        prestate.addProperty("cell", field);
        prestate.addProperty("sourceKind", "HEAP_PRESTATE");
        prestate.addProperty("location", "RECEIVER_FIELD");
        prestate.addProperty("field", field);
        prestate.add("fieldPath", strings("assigned"));
        prestate.addProperty("leafFieldSignature", field);
        prestate.addProperty("leafField", "assigned");
        prestate.addProperty("javaType", "java.lang.Object");
        prestate.addProperty("frameConditionAuthority",
                "RUNTIME_UNIQUE_ROOT_TO_OUTPUT_OWNER_FIELD_PATH");
        addExecutableActions(activation, singleton(prestate));
        attachDirectOutputClosure(activation, singleton(capture),
                "Ljava/lang/Object;");
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "field-output-capture-test");
        try {
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            AssignmentOwner owner = new AssignmentOwner();
            owner.assigned = "prestate";
            long token = ConcolicRegionRuntime.enterRegion(root, owner, null);
            assertTrue(token > 0L);
            assertEquals(token, ConcolicRegionRuntime.activeToken());
            owner.assigned = "first";
            owner.assigned = "second";
            ConcolicRegionRuntime.recordRegionExitFieldOutput(
                    "REGION.TEST.out.field.exit-field",
                    "REGION.TEST.out.field", field, field,
                    owner, owner.assigned);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
            JsonArray captures = row.getAsJsonArray("outputCaptures");
            assertEquals(1, captures.size());
            JsonObject observed = captures.get(0).getAsJsonObject();
            assertFalse(observed.has("captureKind"));
            assertFalse(observed.has("occurrence"));
            assertFalse(observed.has("method"));
            assertFalse(observed.has("siteId"));
            long ownerToken = observed.get("fieldOwnerObjectToken")
                    .getAsLong();
            assertTrue(ownerToken > 0L);
            assertEquals("M_L_field_REGION.TEST.in.0_java/lang/String",
                    observed.getAsJsonObject("expression").get("_exp")
                            .getAsString());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void materializesSchemaV2ContainerSnapshotAtExactIndexAndIgnoresUnrelatedOwner()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.ContainerSnapshot: void run()>";
        String base = "REGION.ARRAY.in.element.id";
        String container = "REGION.ARRAY.in.elements";
        String bindingId = "BIND.ARRAY.ELEMENT.ID";
        String site = root + "#u6";
        int selectedIndex = 1;
        int occurrence = 1;
        String dynamic = ConcolicRegionRuntime.dynamicFieldSymbolForTests(
                base, site, occurrence);

        JsonObject activation = symbolicTask(
                "ACT.CONTAINER.SNAPSHOT.V2", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        JsonArray actions = genericArrayActions(base, container, root);
        JsonArray catalog = new JsonArray();
        JsonObject containerAction = actions.get(0).getAsJsonObject();
        containerAction.addProperty("mode", "SYMBOLIC");
        containerAction.addProperty("bindingMode",
                "CONTAINER_INPUT_OBSERVATION");
        catalog.add(containerAction);
        JsonObject leafAction = actions.get(1).getAsJsonObject();
        leafAction.addProperty("mode", "DECLARATION_ONLY");
        catalog.add(leafAction);
        activation.add("inputActions", catalog);
        activation.add("containerElementFieldBindings", singleton(
                genericArrayBinding(bindingId, base, container,
                        "EXACT_ARRAY_INDEX", selectedIndex, occurrence, site)));
        activation.add("modelAssignments", singleton(genericArrayAssignment(
                bindingId, base, container, dynamic, site, occurrence,
                selectedIndex, "41")));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            GenericArrayEnvelope envelope = new GenericArrayEnvelope(3);
            Current selected = envelope.elements[selectedIndex];
            Current unrelated = new Current();
            runGenericArrayActivation(root, envelope,
                    java.util.Arrays.asList(selected, unrelated));

            assertEquals(41, selected.id);
            assertEquals(7, unrelated.id);
            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
            JsonArray bindings = row.getAsJsonArray("dynamicFieldBindings");
            assertEquals(1, bindings.size());
            JsonObject dynamicBinding = bindings.get(0).getAsJsonObject();
            assertEquals(2, dynamicBinding.get("schemaVersion").getAsInt());
            assertEquals("DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING",
                    dynamicBinding.get("kind").getAsString());
            JsonObject selector = dynamicBinding
                    .getAsJsonObject("containerSelector");
            assertEquals(selectedIndex,
                    selector.get("elementIndex").getAsInt());
            assertEquals(occurrence,
                    selector.get("elementOccurrence").getAsInt());
            assertTrue(selector.get("complete").getAsBoolean());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }





















    private static JsonObject runHiddenConsumedArrayField(
            boolean consumeSubclassField) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.HiddenArrayLeaf: void run()>";
        String signature = "<" + HiddenArrayBase.class.getName() + ": "
                + Current.class.getName() + "[] values>";
        JsonObject action = engineArrayFieldAction(
                "REGION.ARRAY.in.hidden.base", signature, "values",
                "HEAP_OBJECT_FIELD");
        action.addProperty("accessOwnerClass",
                HiddenArrayBase.class.getName());
        action.addProperty("leafOwnerClass",
                HiddenArrayBase.class.getName());
        JsonObject activation = symbolicTask(
                "ACT.ENGINE.ARRAY.HIDDEN."
                        + (consumeSubclassField ? "REJECT" : "EXACT"),
                root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        addExecutableActions(activation, singleton(consumedFieldAction(action,
                root, 23,
                "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1")));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            HiddenArraySub owner = new HiddenArraySub();
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object(), null);
            ConcolicRegionRuntime.prepareFieldMaterialization(root, 23,
                    owner, signature, "values");
            Current[] consumed = consumeSubclassField ? owner.values
                    : ((HiddenArrayBase) owner).values;
            ConcolicRegionRuntime.materializeConsumedField(root, 23,
                    owner, signature, "values", consumed);
            ConcolicRegionRuntime.exitRegion(token, null, "");
            return resultRows(results).get(0).deepCopy();
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }




    private static JsonObject runEngineArrayInputFailure(
            String expressionMode, boolean repeatDifferentArray)
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.ArrayInput: void run(" + Current.class
                .getName() + "[])>";
        JsonObject activation = symbolicTask(
                "ACT.ENGINE.ARRAY.FAIL." + expressionMode, root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        addExecutableActions(activation, singleton(engineArrayArgumentAction(
                "REGION.ARRAY.in.0", root, 0)));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));
        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object(), null);
            DelayedExpressionEngine.arrayExpressionMode = expressionMode;
            ConcolicRegionRuntime.symbolizeArgument(token, 0,
                    new Current[]{new Current()}, "");
            if (repeatDifferentArray) {
                ConcolicRegionRuntime.symbolizeArgument(token, 0,
                        new Current[]{new Current()}, "");
            }
            ConcolicRegionRuntime.exitRegion(token, null, "");
            return resultRows(results).get(0).deepCopy();
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    private static JsonObject runPrimitiveEngineArrayInput(String mode)
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.PrimitiveArrayInput: void run(int[])>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.PRIMITIVE.ARRAY.in.0");
        action.addProperty("cell", root + ".param0:int[]");
        action.addProperty("javaType", "int[]");
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", 0);
        JsonObject activation = symbolicTask(
                "ACT.ENGINE.PRIMITIVE.ARRAY." + mode, root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        addExecutableActions(activation, singleton(action));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));
        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object(), null);
            DelayedExpressionEngine.arrayExpressionMode = mode;
            ConcolicRegionRuntime.symbolizeArgument(token, 0,
                    new int[]{7, -3}, "");
            ConcolicRegionRuntime.exitRegion(token, null, "");
            return resultRows(results).get(0).deepCopy();
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    private static JsonObject runEngineArrayIdCollision() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.ArrayInput: void run(" + Current.class
                .getName() + "[]," + Current.class.getName() + "[])>";
        JsonObject activation = symbolicTask(
                "ACT.ENGINE.ARRAY.ID.COLLISION", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        JsonArray actions = new JsonArray();
        actions.add(engineArrayArgumentAction("REGION.ARRAY.in.0",
                root, 0));
        actions.add(engineArrayArgumentAction("REGION.ARRAY.in.1",
                root, 1));
        addExecutableActions(activation, actions);
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));
        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object(), null);
            DelayedExpressionEngine.forcedArrayId = "AL_77";
            ConcolicRegionRuntime.symbolizeArgument(token, 0,
                    new Current[]{new Current()}, "");
            ConcolicRegionRuntime.symbolizeArgument(token, 1,
                    new Current[]{new Current()}, "");
            ConcolicRegionRuntime.exitRegion(token, null, "");
            return resultRows(results).get(0).deepCopy();
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    private static JsonObject engineArrayArgumentAction(
            String port, String root, int index) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("cell", root + ".param" + index + ":"
                + Current.class.getName() + "[]");
        action.addProperty("javaType", Current.class.getName() + "[]");
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", index);
        return action;
    }

    private static JsonObject engineArrayFieldAction(
            String port, String signature, String field, String location) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("cell", signature);
        action.addProperty("field", signature);
        action.addProperty("javaType", Current.class.getName() + "[]");
        action.addProperty("location", location);
        action.addProperty("bindingMode", "HEAP_OBJECT_FIELD".equals(
                location) ? "FIELD_ACCESS" : "ROOT_ENTRY");
        action.addProperty("accessOwnerClass",
                EngineArrayInputOwner.class.getName());
        action.addProperty("accessField", field);
        action.addProperty("leafOwnerClass",
                EngineArrayInputOwner.class.getName());
        action.addProperty("leafField", field);
        action.add("fieldPath", JsonParser.parseString("[\"" + field
                + "\"]"));
        return action;
    }

    private static JsonObject consumedFieldAction(
            JsonObject action, String method, int unitIndex,
            String rootAuthority) {
        action.addProperty("consumedFieldMethod", method);
        action.addProperty("consumedFieldUnitIndex", unitIndex);
        action.addProperty("consumedFieldRootAuthority", rootAuthority);
        return action;
    }

    private static String engineArrayReceiverFieldSignature() {
        return "<" + EngineArrayInputOwner.class.getName() + ": "
                + Current.class.getName() + "[] receiverValues>";
    }

    private static String engineArrayAccessFieldSignature() {
        return "<" + EngineArrayInputOwner.class.getName() + ": "
                + Current.class.getName() + "[] accessedValues>";
    }












    private static JsonObject runMapProjectionRuntimeCase(
            String activationId, String outputValidationMode,
            String mutation, JsonObject assignment) throws Exception {
        return runMapProjectionRuntimeCase(activationId,
                outputValidationMode, mutation, assignment, false);
    }

    private static JsonObject runMapProjectionRuntimeCase(
            String activationId, String outputValidationMode,
            String mutation, JsonObject assignment,
            boolean mapStateObservationOnly) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = mapProjectionRoot();
        JsonObject activation = symbolicTask(activationId, root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        JsonObject mapAction = mapProjectionMapAction();
        if (mapStateObservationOnly) {
            mapAction.addProperty("bindingMode",
                    "MAP_STATE_INPUT_OBSERVATION");
            mapAction.addProperty("javaType", "java.util.Map");
            mapAction.addProperty("mapStateObservationOnly", true);
            mapAction.addProperty("modelControllable", false);
            mapAction.addProperty("containerObservationAuthority",
                    "FIRST_MATCHING_CONTAINER_INSTANCE_APPROXIMATION_V1");
            mapAction.addProperty("mapStateInputCell",
                    mapProjectionMapFieldSignature());
            mapAction.addProperty("mapStateRequestedOutputCell",
                    mapProjectionMapFieldSignature());
        }
        addExecutableActions(activation, singleton(mapAction));
        JsonObject projectionDeclaration = mapProjectionDeclaration(
                outputValidationMode);
        if ("KEY_SET_VIEW".equals(mutation)) {
            projectionDeclaration.addProperty("mapProjectionOperation",
                    "MAP_KEY_SET_VIEW");
        }
        activation.add("mapValueElementFieldProjections", singleton(
                projectionDeclaration));
        if (assignment != null) {
            activation.add("modelAssignments", singleton(assignment));
        }
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            java.util.Map<Object, MapProjectionElement> backing =
                    "IDENTITY_MAP".equals(mutation)
                            ? new java.util.IdentityHashMap<>()
                            : "HASH_MAP".equals(mutation)
                            ? new java.util.HashMap<>()
                            : new java.util.LinkedHashMap<>();
            MapProjectionProducer producer = new MapProjectionProducer(
                    backing);
            MapProjectionElement first = "SHADOW_FIELD".equals(mutation)
                    ? new ShadowMapProjectionElement(11L, 111L)
                    : new MapProjectionElement(11L);
            MapProjectionElement second = new MapProjectionElement(22L);
            MapProjectionElement third = new MapProjectionElement(33L);
            if ("REORDERED_MAP".equals(mutation)) {
                producer.values.put(2, second);
                producer.values.put(1, first);
                producer.values.put(3, third);
            } else if ("FLOAT_KEY".equals(mutation)) {
                producer.values.put(Float.valueOf(-0.0f), first);
                producer.values.put(2, second);
                producer.values.put(3, third);
            } else {
                producer.values.put(1, first);
                producer.values.put(2, second);
                producer.values.put(3, third);
            }

            long token = ConcolicRegionRuntime.enterRegion(root, producer,
                    null);
            assertTrue(token > 0L);
            ConcolicRegionRuntime.materializeField(root, 4, producer,
                    mapProjectionMapFieldSignature(), "values");

            // Assert this before output construction: symbols must be born at
            // producer entry, never synthesized by the output-capture hook.
            // Three recursive element-field symbols plus the existing
            // shallow backing-map field symbol.
            boolean projectionRejectedAtEntry =
                    "FLOAT_KEY".equals(mutation)
                            || "IDENTITY_MAP".equals(mutation)
                            || "SHADOW_FIELD".equals(mutation)
                            || "KEY_SET_VIEW".equals(mutation);
            int mapReferenceSymbols = mapStateObservationOnly ? 0 : 1;
            assertEquals(projectionRejectedAtEntry
                            ? mapReferenceSymbols
                            : mapReferenceSymbols + 3,
                    DelayedExpressionEngine.SYMBOLIC_FIELD_PREFIXES.size());
            assertEquals(!mapStateObservationOnly,
                    DelayedExpressionEngine.SYMBOLIC_FIELD_PREFIXES
                            .containsKey(producer));
            if (!projectionRejectedAtEntry) {
                assertTrue(DelayedExpressionEngine.SYMBOLIC_FIELD_PREFIXES
                        .containsKey(first));
                assertTrue(DelayedExpressionEngine.SYMBOLIC_FIELD_PREFIXES
                        .containsKey(second));
                assertTrue(DelayedExpressionEngine.SYMBOLIC_FIELD_PREFIXES
                        .containsKey(third));
            }
            if (assignment != null) {
                assertEquals("wrong-scope model must not mutate input", 11L,
                        first.expiryDate);
            }

            if ("CROSS_THREAD_WRITE".equals(mutation)
                    || "CROSS_THREAD_NOISE".equals(mutation)) {
                Thread writer = new Thread(() -> {
                    if ("CROSS_THREAD_WRITE".equals(mutation)) {
                        long original = first.expiryDate;
                        first.expiryDate = original + 1L;
                        CausynthTraceRecorder.recordField("FIELD_WRITE",
                                root, 17, mapProjectionElementFieldSignature(),
                                producer, first, null,
                                Long.toString(first.expiryDate));
                        // Restoring the value must not turn a concrete write
                        // into a false schema-v3 entry/output equality proof.
                        first.expiryDate = original;
                    } else {
                        CausynthTraceRecorder.recordField("FIELD_WRITE",
                                root, 18,
                                mapProjectionElementFieldSignature(),
                                producer, new MapProjectionElement(44L),
                                null, "44");
                        CausynthTraceRecorder.recordField("FIELD_WRITE",
                                root, 19,
                                "<" + MapProjectionElement.class.getName()
                                        + ": long otherExpiry>",
                                producer, first, null, "11");
                    }
                }, "map-projection-cross-thread-writer");
                writer.start();
                writer.join(5000L);
                assertFalse("cross-thread field writer did not finish",
                        writer.isAlive());
            }

            MapProjectionElement[] output = producer.values.values()
                    .toArray(new MapProjectionElement[0]);
            if ("REVERSED".equals(mutation)) {
                output = new MapProjectionElement[]{third, second, first};
            } else if ("SHORTER".equals(mutation)) {
                output = new MapProjectionElement[]{first, second};
            } else if ("REPLACED_IDENTITY".equals(mutation)) {
                output = new MapProjectionElement[]{first,
                        new MapProjectionElement(second.expiryDate), third};
            }
            ConcolicRegionRuntime.exitRegion(token,
                    new MapProjectionPayload(output), "");
            return resultRows(results).get(0).deepCopy();
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    private static JsonObject mapProjectionMapAction() {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", mapProjectionMapPort());
        action.addProperty("cell", mapProjectionMapFieldSignature());
        action.addProperty("field", mapProjectionMapFieldSignature());
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessOwnerClass",
                MapProjectionProducer.class.getName());
        action.addProperty("accessField", "values");
        action.addProperty("leafOwnerClass",
                MapProjectionProducer.class.getName());
        action.addProperty("leafField", "values");
        action.add("fieldPath", JsonParser.parseString("[\"values\"]"));
        return action;
    }

    private static JsonObject mapProjectionDeclaration(
            String outputValidationMode) {
        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion", 1);
        declaration.addProperty("kind",
                "MAP_VALUE_TO_OUTPUT_ARRAY_ELEMENT_FIELD");
        declaration.addProperty("bindingId", mapProjectionBindingId());
        declaration.addProperty("mapInputPort", mapProjectionMapPort());
        declaration.addProperty("mapInputCell",
                mapProjectionMapFieldSignature());
        declaration.addProperty("outputPort", mapProjectionOutputPort());
        declaration.addProperty("outputCell",
                mapProjectionOutputFieldSignature());
        declaration.add("outputFieldPath",
                JsonParser.parseString("[\"values\"]"));
        declaration.addProperty("outputValidationMode",
                outputValidationMode);
        declaration.addProperty("mapProjectionOperation",
                "MAP_VALUES_VIEW");
        declaration.addProperty("mapViewSiteId",
                mapProjectionRoot() + "#u5");
        declaration.addProperty("snapshotSiteId",
                mapProjectionRoot() + "#u6");
        declaration.addProperty("downstreamRegion", "REGION.DOWNSTREAM");
        declaration.addProperty("downstreamRegionInstance",
                "ACT.DOWNSTREAM.INSTANCE");
        declaration.addProperty("downstreamInputPort",
                "REGION.DOWNSTREAM.in.array");
        declaration.addProperty("downstreamBaseInputSymbol",
                "REGION.DOWNSTREAM.in.expiry");
        declaration.addProperty("downstreamContainerBindingId",
                "BIND.DOWNSTREAM.ARRAY.EXPIRY");
        declaration.addProperty("declaredFieldSignature",
                mapProjectionElementFieldSignature());
        declaration.addProperty("declaredFieldOwnerClass",
                MapProjectionElement.class.getName());
        declaration.addProperty("declaredFieldType", "long");
        declaration.addProperty("declaredFieldName", "expiryDate");
        declaration.add("fieldPath",
                JsonParser.parseString("[\"expiryDate\"]"));
        declaration.addProperty("selectorAuthority",
                "CURRENT_EXECUTION_ENTRY_SNAPSHOT_THEN_EXACT_"
                        + "OUTPUT_INDEX_IDENTITY");
        declaration.add("projectionProofCausalEdgeIds",
                JsonParser.parseString("[\"EDGE.MAP.FIELD\","
                        + "\"EDGE.MAP.VALUES\",\"EDGE.TO.ARRAY\","
                        + "\"EDGE.OUTPUT.FIELD\"]"));
        declaration.addProperty("complete", true);
        return declaration;
    }

    private static JsonObject mapProjectionAssignment(
            String objectTokenScope, int outputIndex, String value) {
        String site = mapProjectionRoot() + "#u6#map-element:"
                + mapProjectionBindingId();
        int occurrence = outputIndex + 1;
        String dynamic = ConcolicRegionRuntime.dynamicFieldSymbolForTests(
                mapProjectionMapPort(), site, occurrence);
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", dynamic);
        assignment.addProperty("inputSymbol", mapProjectionMapPort());
        assignment.addProperty("baseInputSymbol", mapProjectionMapPort());
        assignment.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        assignment.addProperty("dynamicFieldSymbol", dynamic);
        assignment.addProperty("materializationSiteId", site);
        assignment.addProperty("materializationOccurrence", occurrence);
        assignment.addProperty("valueType", "LONG");
        assignment.addProperty("value", value);
        assignment.addProperty("authority", "TEST_MAP_PROJECTION_MODEL");
        assignment.add("materializationPath",
                JsonParser.parseString("[\"expiryDate\"]"));
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
        selector.addProperty("bindingId", mapProjectionBindingId());
        selector.addProperty("mapInputPort", mapProjectionMapPort());
        selector.addProperty("mapInputCell",
                mapProjectionMapFieldSignature());
        selector.addProperty("outputPort", mapProjectionOutputPort());
        selector.addProperty("outputCell",
                mapProjectionOutputFieldSignature());
        selector.addProperty("mapProjectionOperation", "MAP_VALUES_VIEW");
        selector.addProperty("outputIndex", outputIndex);
        selector.addProperty("elementOccurrence", occurrence);
        selector.addProperty("declaredFieldOwnerClass",
                MapProjectionElement.class.getName());
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("declaredFieldSignature",
                mapProjectionElementFieldSignature());
        selector.addProperty("mapObjectToken", 501L);
        selector.addProperty("elementObjectToken", 601L + outputIndex);
        selector.addProperty("outputArrayObjectToken", 701L);
        selector.addProperty("authority",
                "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                        + "EXACT_OUTPUT_IDENTITY");
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", objectTokenScope);
        selector.addProperty("sourceObjectTokenScope",
                "ACT.MAP.PROJECTION.SOURCE");
        selector.addProperty("replayScopeRebindingAuthority",
                "SOURCE_CASE_SELECTOR_VALIDATED_THEN_REPLAY_ACTIVATION_"
                        + "SCOPE_REBOUND_TOKENS_NOT_COMPARED_ACROSS_"
                        + "EXECUTIONS");
        selector.addProperty("crossExecutionOrdinalAuthority", "NONE");
        selector.add("expectedMapKey",
                ConcolicRegionRuntime.immutableEntryKeyExpression(
                        outputIndex + 1));
        selector.addProperty("expectedMapKeyAuthority",
                "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
        selector.addProperty("sourceOutputIndexAuthority",
                "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                        + "POSITIONAL_REFERENCE_EQUALITY");
        selector.addProperty("replaySelectionAuthority",
                "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_"
                        + "EXACT_OUTPUT_IDENTITY");
        selector.addProperty("outputIdentityVerified", true);
        selector.addProperty("outputVerificationAuthority",
                "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD");
        selector.addProperty("complete", true);
        assignment.add("mapProjectionSelector", selector);
        return assignment;
    }

    private static String mapProjectionRoot() {
        return "<example.ProjectionProducer: example.Payload export()>";
    }

    private static String mapProjectionBindingId() {
        return "MAP_OUTPUT_ELEMENT:EDGE.PRODUCER.DOWNSTREAM:"
                + "BIND.DOWNSTREAM.ARRAY.EXPIRY";
    }

    private static String mapProjectionMapPort() {
        return "REGION.PRODUCER.in.map";
    }

    private static String mapProjectionOutputPort() {
        return "REGION.PRODUCER.out.payload";
    }

    private static String mapProjectionMapFieldSignature() {
        return "<" + MapProjectionProducer.class.getName()
                + ": java.util.Map values>";
    }

    private static String mapProjectionOutputFieldSignature() {
        return "<" + MapProjectionPayload.class.getName() + ": "
                + MapProjectionElement.class.getName() + "[] values>";
    }

    private static String mapProjectionElementFieldSignature() {
        return "<" + MapProjectionElement.class.getName()
                + ": long expiryDate>";
    }

    private static void runEntryFieldActivation(
            String root,
            java.util.LinkedHashMap<Integer, ExpiringValue> map,
            ExpiringValue target, boolean skipFirstEntry) {
        long token = ConcolicRegionRuntime.enterRegion(root, map, null);
        assertTrue(token > 0L);
        Object view = map.entrySet();
        ConcolicRegionRuntime.registerMapView(root, 3, map, view,
                "ENTRY_SET");
        java.util.Iterator<?> iterator =
                ((java.util.Set<?>) view).iterator();
        ConcolicRegionRuntime.registerMapViewIterator(root, 4, view,
                iterator);
        if (skipFirstEntry) {
            Object skipped = iterator.next();
            ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                    skipped);
        }
        Object selected = iterator.next();
        ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                selected);
        ConcolicRegionRuntime.materializeField(root, 6, target,
                expiryFieldSignature(), "expiry");
        ConcolicRegionRuntime.exitRegion(token, null, "");
    }

    private static JsonObject symbolicTask(
            String id, String root, int ordinal) {
        JsonObject activation = new JsonObject();
        activation.addProperty("goalId", id + ".GOAL");
        activation.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        activation.addProperty("taskId", "TASK." + id);
        activation.addProperty("regionId", "REGION.TEST");
        activation.addProperty("regionInstanceId",
                "REGION.TEST@TEST#call" + ordinal);
        activation.addProperty("test", id.startsWith("ACT.MODEL")
                ? "concrete-model-test" : "concrete-overlap-test");
        JsonObject rootSelector = new JsonObject();
        rootSelector.addProperty("kind", "GLOBAL_INVOCATION");
        rootSelector.addProperty("method", root);
        rootSelector.addProperty("ordinal", ordinal);
        activation.add("rootSelector", rootSelector);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        admission.addProperty("mode", "TEST_SYMBOLIC_CONCOLIC");
        admission.add("blockers", new JsonArray());
        activation.add("admission", admission);
        activation.add("inputActions", new JsonArray());
        activation.add("modelAssignments", new JsonArray());
        return activation;
    }

    private static void addExecutableActions(JsonObject activation,
                                             JsonArray actions) {
        JsonArray catalog = new JsonArray();
        for (JsonElement element : actions) {
            JsonObject action = element.getAsJsonObject().deepCopy();
            action.addProperty("mode", "SYMBOLIC");
            catalog.add(action);
        }
        activation.add("inputActions", catalog);
    }

    private static void addRootArgumentSelector(
            JsonObject activation, int matchOrdinalWithinReceiver,
            String... runtimeTypes) {
        addRootArgumentSelector(activation, 1,
                matchOrdinalWithinReceiver, runtimeTypes);
    }

    private static void addRootArgumentSelector(
            JsonObject activation, int receiverOrdinal,
            int matchOrdinalWithinReceiver, String... runtimeTypes) {
        JsonObject selector = new JsonObject();
        selector.addProperty("receiverOrdinal", receiverOrdinal);
        selector.addProperty("matchOrdinalWithinReceiver",
                matchOrdinalWithinReceiver);
        JsonArray predicates = new JsonArray();
        for (int index = 0; index < runtimeTypes.length; index++) {
            JsonObject predicate = new JsonObject();
            predicate.addProperty("kind",
                    RuntimeRegionPlanner.ROOT_ARGUMENT_PREDICATE_KIND);
            predicate.addProperty("argumentIndex", index);
            predicate.addProperty("runtimeType", runtimeTypes[index]);
            predicates.add(predicate);
        }
        selector.add("predicates", predicates);
        activation.getAsJsonObject("rootSelector").add(
                "arguments", selector);
    }

    private static void addStableRootContext(
            JsonObject activation, String receiverRuntimeClass,
            String threadName, int ordinalWithinContext) {
        JsonObject selector = activation.getAsJsonObject("rootSelector");
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("receiverClass", receiverRuntimeClass);
        selector.addProperty("thread", threadName);
        selector.addProperty("ordinal", ordinalWithinContext);
    }

    private static final class KeyUpdateCommand {
    }

    private static final class HeartbeatCommand {
    }

    private static final class BPServiceActor {
    }

    private static final class ProducerWorker {
    }

    private static final class ConsumerWorker {
    }

    private static String expiryFieldSignature() {
        return "<" + ExpiringValue.class.getName() + ": long expiry>";
    }

    private static JsonObject expiryFieldAction(String baseSymbol) {
        String owner = ExpiringValue.class.getName();
        JsonObject action = new JsonObject();
        action.addProperty("symbol", baseSymbol);
        action.addProperty("cell", expiryFieldSignature());
        action.addProperty("field", expiryFieldSignature());
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessOwnerClass", owner);
        action.addProperty("accessField", "expiry");
        action.addProperty("leafOwnerClass", owner);
        action.addProperty("leafField", "expiry");
        action.add("fieldPath", new JsonParser().parse("[\"expiry\"]"));
        return action;
    }

    private static String deepStateFieldSignature() {
        return "<" + ExpiringValue.class.getName() + ": "
                + DeepState.class.getName() + " state>";
    }

    private static String deepEnabledFieldSignature() {
        return "<" + DeepGuard.class.getName()
                + ": boolean enabled>";
    }

    private static JsonObject deepEnabledFieldAction(String baseSymbol) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", baseSymbol);
        action.addProperty("cell", deepStateFieldSignature()
                + "#field:guard#field:enabled");
        action.addProperty("field", deepEnabledFieldSignature());
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("javaType", "boolean");
        action.addProperty("accessOwnerClass",
                ExpiringValue.class.getName());
        action.addProperty("accessField", "state");
        action.addProperty("accessFieldSignature",
                deepStateFieldSignature());
        action.addProperty("leafOwnerClass", DeepGuard.class.getName());
        action.addProperty("leafField", "enabled");
        action.addProperty("leafFieldSignature",
                deepEnabledFieldSignature());
        action.add("fieldPath", JsonParser.parseString(
                "[\"state\",\"guard\",\"enabled\"]"));
        return action;
    }

    private static JsonObject dynamicAssignment(
            String baseSymbol, String dynamicSymbol, String site,
            int occurrence, String value) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", dynamicSymbol);
        assignment.addProperty("inputSymbol", baseSymbol);
        assignment.addProperty("baseInputSymbol", baseSymbol);
        assignment.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicSymbol);
        assignment.addProperty("dynamicFieldSymbol", dynamicSymbol);
        assignment.addProperty("materializationSiteId", site);
        assignment.addProperty("materializationOccurrence", occurrence);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", value);
        assignment.addProperty("solverSymbol",
                z3SolverSymbolForTest(dynamicSymbol));
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        assignment.add("target", expiryFieldAction(baseSymbol));
        assignment.add("materializationPath",
                JsonParser.parseString("[\"expiry\"]"));
        return assignment;
    }

    /** Mirrors ConcolicConstraintSolver's stable raw-symbol encoding. */
    private static String z3SolverSymbolForTest(String engineSymbol) {
        String safe = engineSymbol == null ? "" : engineSymbol.replaceAll(
                "[^A-Za-z0-9_]", "_");
        if (safe.isEmpty()) safe = "empty";
        if (Character.isDigit(safe.charAt(0))) safe = "n_" + safe;
        if (safe.length() > 80) safe = safe.substring(0, 80);
        try {
            byte[] digest = MessageDigest.getInstance("SHA-256").digest(
                    (engineSymbol == null ? "" : engineSymbol).getBytes(
                            StandardCharsets.UTF_8));
            StringBuilder hex = new StringBuilder();
            for (byte value : digest) {
                hex.append(String.format("%02x", value & 0xff));
            }
            return "sym__" + safe + "__" + hex.substring(0, 10);
        } catch (Exception unavailable) {
            throw new AssertionError(unavailable);
        }
    }

    private static JsonArray genericArrayActions(String baseSymbol,
                                                 String containerSymbol,
                                                 String root) {
        JsonArray actions = new JsonArray();
        JsonObject container = new JsonObject();
        container.addProperty("symbol", containerSymbol);
        container.addProperty("cell", genericArrayFieldSignature());
        container.addProperty("field", genericArrayFieldSignature());
        container.addProperty("location", "HEAP_OBJECT_FIELD");
        container.addProperty("bindingMode", "FIELD_ACCESS");
        container.add("fieldPath",
                JsonParser.parseString("[\"elements\"]"));
        consumedFieldAction(container, root, 2,
                "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                        + "PATH_PREFIX_REFERENCE_EQUALITY");
        actions.add(container);

        JsonObject elementField = new JsonObject();
        elementField.addProperty("symbol", baseSymbol);
        elementField.addProperty("cell", currentIdFieldSignature());
        elementField.addProperty("field", currentIdFieldSignature());
        elementField.addProperty("location", "HEAP_OBJECT_FIELD");
        elementField.addProperty("bindingMode", "FIELD_ACCESS");
        elementField.add("fieldPath", JsonParser.parseString("[\"id\"]"));
        actions.add(elementField);
        return actions;
    }

    private static JsonObject genericArrayBinding(
            String bindingId, String baseSymbol, String containerSymbol,
            String selectorAuthority, int elementIndex,
            int elementOccurrence, String fieldMaterializationSiteId) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 2);
        binding.addProperty("kind", "ARRAY_ELEMENT_FIELD");
        binding.addProperty("materializationMode", "CONTAINER_SNAPSHOT");
        binding.addProperty("bindingId", bindingId);
        binding.addProperty("baseInputSymbol", baseSymbol);
        binding.addProperty("containerInputPort", containerSymbol);
        binding.addProperty("containerInputCell",
                genericArrayFieldSignature());
        binding.addProperty("selectorAuthority", selectorAuthority);
        binding.addProperty("elementIndex", elementIndex);
        binding.addProperty("elementOccurrence", elementOccurrence);
        binding.addProperty("fieldMaterializationSiteId",
                fieldMaterializationSiteId);
        binding.add("fieldPath", JsonParser.parseString("[\"id\"]"));
        binding.addProperty("declaredFieldSignature",
                currentIdFieldSignature());
        return binding;
    }

    private static JsonObject genericArrayAssignment(
            String bindingId, String baseSymbol, String containerSymbol,
            String dynamicSymbol, String site, int occurrence,
            int elementIndex, String value) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", dynamicSymbol);
        assignment.addProperty("inputSymbol", baseSymbol);
        assignment.addProperty("baseInputSymbol", baseSymbol);
        assignment.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicSymbol);
        assignment.addProperty("dynamicFieldSymbol", dynamicSymbol);
        assignment.addProperty("materializationSiteId", site);
        assignment.addProperty("materializationOccurrence", occurrence);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", value);
        assignment.addProperty("authority", "TEST_EXACT_ARRAY_SELECTOR");
        assignment.add("materializationPath",
                JsonParser.parseString("[\"id\"]"));
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", bindingId);
        selector.addProperty("containerInputPort", containerSymbol);
        selector.addProperty("containerInputCell",
                genericArrayFieldSignature());
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", elementIndex);
        selector.addProperty("elementOccurrence", occurrence);
        selector.addProperty("declaredFieldSignature",
                currentIdFieldSignature());
        assignment.add("containerSelector", selector);
        assignment.addProperty("containerReplayRebindingAuthority",
                "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                        + "IDENTITY_REBIND_V1");
        return assignment;
    }

    private static void runGenericArrayActivation(
            String root, GenericArrayEnvelope envelope,
            List<Current> fieldOwners) {
        runGenericArrayActivation(root, envelope, fieldOwners, root, 6);
    }

    private static void runGenericArrayActivation(
            String root, GenericArrayEnvelope envelope,
            List<Current> fieldOwners, String fieldHookMethod,
            int fieldHookUnit) {
        long token = ConcolicRegionRuntime.enterRegion(root, envelope, null);
        assertTrue(token > 0L);
        ConcolicRegionRuntime.prepareFieldMaterialization(root, 2, envelope,
                genericArrayFieldSignature(), "elements");
        Current[] consumed = envelope.elements;
        ConcolicRegionRuntime.materializeConsumedField(root, 2, envelope,
                genericArrayFieldSignature(), "elements", consumed);
        for (Current owner : fieldOwners) {
            ConcolicRegionRuntime.materializeField(fieldHookMethod,
                    fieldHookUnit, owner,
                    currentIdFieldSignature(), "id");
        }
        ConcolicRegionRuntime.exitRegion(token, null, "");
    }

    private static String genericArrayFieldSignature() {
        return "<" + GenericArrayEnvelope.class.getName() + ": "
                + Current[].class.getName() + " elements>";
    }

    private static String currentIdFieldSignature() {
        return "<" + Current.class.getName() + ": int id>";
    }

    private static String metadataExpiryFieldSignature() {
        return "<" + Metadata.class.getName() + ": long expiry>";
    }

    private static List<JsonObject> resultRows(Path results)
            throws Exception {
        java.util.ArrayList<JsonObject> rows = new java.util.ArrayList<>();
        for (String line : Files.readAllLines(results,
                StandardCharsets.UTF_8)) {
            if (!line.trim().isEmpty()) {
                rows.add(new JsonParser().parse(line).getAsJsonObject());
            }
        }
        return rows;
    }

    private static JsonArray singleton(JsonObject object) {
        JsonArray result = new JsonArray();
        result.add(object);
        return result;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    private static void attachDirectOutputClosure(
            JsonObject activation, JsonArray captures,
            String... descriptors) {
        if (captures.size() != descriptors.length) {
            throw new IllegalArgumentException(
                    "capture and descriptor counts differ");
        }
        String regionId = activation.get("regionId").getAsString();
        activation.addProperty("goalKind", "OUTPUT_RELATION_CLOSURE");
        long rootCallId = 0L;
        String regionInstanceId = regionId + "@TEST#call" + rootCallId;
        activation.addProperty("regionInstanceId", regionInstanceId);
        activation.addProperty("rootCallId", rootCallId);

        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", regionId);
        producer.addProperty("regionInstanceId", regionInstanceId);
        producer.addProperty("rootCallId", rootCallId);
        envelope.add("producer", producer);

        JsonArray members = new JsonArray();
        for (int index = 0; index < captures.size(); index++) {
            JsonObject capture = captures.get(index).getAsJsonObject();
            JsonObject output = new JsonObject();
            output.addProperty("portId",
                    capture.get("outputPort").getAsString());
            output.addProperty("cell",
                    capture.get("outputCell").getAsString());
            output.addProperty("kind", "REGION_OUTPUT");
            output.addProperty("javaTypeDescriptor", descriptors[index]);
            output.addProperty("selectionAuthority",
                    "TEST_EXACT_DIRECT_CAPTURE");

            JsonObject slice = new JsonObject();
            slice.addProperty("outputPort",
                    capture.get("outputPort").getAsString());
            slice.addProperty("outputCell",
                    capture.get("outputCell").getAsString());
            JsonArray inputPorts = new JsonArray();
            inputPorts.add(capture.get(
                    "accessRootInputPort").getAsString());
            slice.add("inputPorts", inputPorts);
            slice.add("sites", new JsonArray());
            slice.add("staticSites", new JsonArray());
            slice.add("methods", new JsonArray());
            slice.add("causalEdgeIds", new JsonArray());
            slice.add("captureBindings",
                    singleton(capture.deepCopy()));
            slice.add("captureBindingIssues", new JsonArray());

            JsonObject member = new JsonObject();
            member.add("output", output);
            member.add("slice", slice);
            members.add(member);
        }
        envelope.add("members", members);
        activation.add("outputClosure", envelope);
    }

    private static String[] installPlan(Path plan, Path results, String test)
            throws Exception {
        String[] old = {
                System.getProperty("causynth.concolic.task.plan"),
                System.getProperty("causynth.concolic.task.id"),
                System.getProperty("causynth.concolic.results"),
                System.getProperty("causynth.trace.test")};
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        String task = Files.readAllLines(plan, StandardCharsets.UTF_8)
                .stream().filter(row -> !row.trim().isEmpty())
                .findFirst().orElseThrow(() ->
                        new IllegalArgumentException("empty task plan"));
        System.setProperty("causynth.concolic.task.id",
                new JsonParser().parse(task).getAsJsonObject()
                        .get("taskId").getAsString());
        System.setProperty("causynth.concolic.results", results.toString());
        System.setProperty("causynth.trace.test", test);
        ConcolicRegionRuntime.resetForTests();
        return old;
    }

    private static void restorePlan(String[] old) {
        restore("causynth.concolic.task.plan", old[0]);
        restore("causynth.concolic.task.id", old[1]);
        restore("causynth.concolic.results", old[2]);
        restore("causynth.trace.test", old[3]);
    }

    private static void restore(String property, String value) {
        if (value == null) {
            System.clearProperty(property);
        } else {
            System.setProperty(property, value);
        }
    }

    private static String condition(String codePosition) {
        return "{\"_type\":\"BinaryExpression\","
                + "\"_left\":{\"_type\":\"SymbolExpression\","
                + "\"_exp\":\"map_result\"},\"_op\":\"!=\","
                + "\"_right\":{\"_type\":\"SymbolExpression\","
                + "\"_exp\":\"N\"},\"_code_position\":\""
                + codePosition + "\"}";
    }

    private static final class Envelope {
        private final Payload payload = new Payload();
        @SuppressWarnings("unused")
        private final String unrelatedInternedValue = "UNRELATED";
    }

    private static final class Payload {
        @SuppressWarnings("unused")
        private final Object entries = new Object();
        private final Current current = new Current();
        private final Current[] elements = {new Current(), new Current()};
    }

    private static final class Current {
        @SuppressWarnings("unused")
        private int id = 7;
        private final Metadata metadata = new Metadata();
    }

    private static final class Metadata {
        @SuppressWarnings("unused")
        private long expiry = 17L;
    }

    private static final class ArrayEnvelope {
        private final Current[] elements = {new Current(), new Current()};
    }

    private static final class GenericArrayEnvelope {
        private final Current[] elements;

        private GenericArrayEnvelope(int size) {
            this.elements = new Current[size];
            for (int index = 0; index < size; index++) {
                this.elements[index] = new Current();
            }
        }
    }

    private static final class EngineArrayInputOwner {
        private final Current[] receiverValues =
                {new Current(), new Current()};
        private Current[] accessedValues = {new Current()};
    }

    private static class HiddenArrayBase {
        private final Current[] values = {new Current()};
    }

    private static final class HiddenArraySub extends HiddenArrayBase {
        private final Current[] values = {new Current(), new Current()};
    }

    private static final class NestedArrayInputRoot {
        private final NestedArrayInputPayload payload =
                new NestedArrayInputPayload();
    }

    private static final class NestedArrayInputPayload {
        private final Current[] values = {new Current(), new Current()};
    }

    private static final class MapProjectionProducer {
        private final java.util.Map<Object, MapProjectionElement> values;

        private MapProjectionProducer() {
            this(new java.util.LinkedHashMap<>());
        }

        private MapProjectionProducer(
                java.util.Map<Object, MapProjectionElement> values) {
            this.values = values;
        }
    }

    private static final class MapProjectionPayload {
        private final MapProjectionElement[] values;

        private MapProjectionPayload(MapProjectionElement[] values) {
            this.values = values;
        }
    }

    private static class MapProjectionElement {
        private long expiryDate;

        private MapProjectionElement(long expiryDate) {
            this.expiryDate = expiryDate;
        }
    }

    private static final class ShadowMapProjectionElement
            extends MapProjectionElement {
        @SuppressWarnings("unused")
        private long expiryDate;

        private ShadowMapProjectionElement(long inheritedExpiryDate,
                                           long shadowExpiryDate) {
            super(inheritedExpiryDate);
            this.expiryDate = shadowExpiryDate;
        }
    }

    private static final class Manager {
        @SuppressWarnings("unused")
        private final java.util.Map<Object, Object> allKeys =
                new java.util.HashMap<>();
    }

    private static final class AssignmentOwner {
        private Object assigned;
    }

    private static final class ExpiringValue {
        @SuppressWarnings("unused")
        private long expiry;
        private final DeepState state = new DeepState();

        private ExpiringValue(long expiry) {
            this.expiry = expiry;
        }
    }

    private static final class DeepState {
        private final DeepGuard guard = new DeepGuard();
    }

    private static final class DeepGuard {
        @SuppressWarnings("unused")
        private boolean enabled;
    }

    /** Exact-event stand-in with an intentionally ambiguous PC suffix. */
    private static final class ExactBranchEngine {
        private static String regionId;
        private static String activationId;
        private static String siteId;
        private static int markerSequence;
        private static long ownerThreadId;
        private static boolean foreignOwner;
        private static boolean conditionless;
        private static String symbolicCondition;
        private static final long EVENT_ID = 41L;
        private static final long CONTEXT_ID = 77L;
        private static final long OS_THREAD_ID = 9001L;

        private static void reset() {
            regionId = "";
            activationId = "";
            siteId = "";
            markerSequence = 0;
            ownerThreadId = 0L;
            foreignOwner = false;
            conditionless = false;
            symbolicCondition = "";
        }

        @SuppressWarnings("unused")
        private static long startRegion(String region, String activation) {
            regionId = region;
            activationId = activation;
            ownerThreadId = Thread.currentThread().getId();
            return 0L;
        }

        @SuppressWarnings("unused")
        private static void symbolize(Object value, String prefix) {
        }

        @SuppressWarnings("unused")
        private static void symbolizeField(Object owner, String field,
                                           String prefix) {
        }

        @SuppressWarnings("unused")
        private static String expression(Object value) {
            return "{\"schemaVersion\":1,\"active\":true,"
                    + "\"symbolic\":false,\"expression\":null}";
        }

        @SuppressWarnings("unused")
        private static String finishRegion() {
            return "{\"schemaVersion\":1,\"engine\":\"exact-mock\","
                    + "\"active\":true,\"pathCondition\":"
                    + pathCondition() + "}";
        }

        @SuppressWarnings("unused")
        private static String pathCondition() {
            if (conditionless) return "[]";
            if (!symbolicCondition.isEmpty()) {
                return "[" + symbolicCondition + "]";
            }
            return "[" + condition(
                    "virtual jobject example.Target.lookup(jint):41")
                    + "," + condition(
                    "virtual jobject example.Target.lookup(jint):42")
                    + "]";
        }

        @SuppressWarnings("unused")
        private static void pausePathCondition() {
        }

        @SuppressWarnings("unused")
        private static void resumePathCondition() {
        }

        @SuppressWarnings("unused")
        private static long markBranch(String site, int sequence) {
            siteId = site;
            markerSequence = sequence;
            return EVENT_ID;
        }

        @SuppressWarnings("unused")
        private static String branchEvents() {
            long claimedOwner = ownerThreadId + (foreignOwner ? 1L : 0L);
            JsonObject event = new JsonObject();
            event.addProperty("eventId", EVENT_ID);
            event.addProperty("contextId", CONTEXT_ID);
            event.addProperty("ownerJavaThreadId", claimedOwner);
            event.addProperty("ownerOsThreadId", OS_THREAD_ID);
            event.addProperty("regionId", regionId);
            event.addProperty("activationId", activationId);
            event.addProperty("siteId", siteId);
            event.addProperty("occurrence", markerSequence);
            event.addProperty("outcome", true);
            event.addProperty("opcode", 199);
            event.addProperty("codePosition",
                    "virtual jobject example.Target.lookup(jint):42");
            JsonArray indices = new JsonArray();
            if (!conditionless) {
                indices.add(symbolicCondition.isEmpty() ? 1 : 0);
            }
            event.add("conditionIndices", indices);
            event.addProperty("conditionCount", indices.size());
            event.addProperty("authority",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");

            JsonObject envelope = new JsonObject();
            envelope.addProperty("schemaVersion", 1);
            envelope.addProperty("kind",
                    "CONCOLIC_THREAD_BRANCH_EVENTS");
            envelope.addProperty("active", true);
            envelope.addProperty("contextId", CONTEXT_ID);
            envelope.addProperty("ownerJavaThreadId", claimedOwner);
            envelope.addProperty("ownerOsThreadId", OS_THREAD_ID);
            envelope.addProperty("regionId", regionId);
            envelope.addProperty("activationId", activationId);
            JsonArray events = new JsonArray();
            events.add(event);
            envelope.add("events", events);
            return envelope.toString();
        }

        @SuppressWarnings("unused")
        private static void endRegion() {
        }
    }

    /** Exact-event stand-in for selected and default switch arms. */
    private static final class ExactSwitchEngine {
        private static final long EVENT_ID = 73L;
        private static final long CONTEXT_ID = 91L;
        private static final long OS_THREAD_ID = 9002L;
        private static final String CODE_POSITION =
                "example.Target.choose:(I)I:42";
        private static String regionId = "";
        private static String activationId = "";
        private static String siteId = "";
        private static int markerSequence;
        private static long ownerThreadId;
        private static int opcode;
        private static boolean outcome;
        private static int[] conditionKeys = new int[0];
        private static String[] conditionOperators = new String[0];
        private static int[] conditionIndices = new int[0];

        private static void configure(
                int configuredOpcode, boolean configuredOutcome,
                int[] keys, String[] operators, int[] indices) {
            if (keys.length != operators.length) {
                throw new IllegalArgumentException(
                        "switch mock condition arrays differ");
            }
            opcode = configuredOpcode;
            outcome = configuredOutcome;
            conditionKeys = keys.clone();
            conditionOperators = operators.clone();
            conditionIndices = indices.clone();
            regionId = "";
            activationId = "";
            siteId = "";
            markerSequence = 0;
            ownerThreadId = 0L;
        }

        @SuppressWarnings("unused")
        private static long startRegion(String region, String activation) {
            regionId = region;
            activationId = activation;
            ownerThreadId = Thread.currentThread().getId();
            return 0L;
        }

        @SuppressWarnings("unused")
        private static void symbolize(Object value, String prefix) {
        }

        @SuppressWarnings("unused")
        private static void symbolizeField(Object owner, String field,
                                           String prefix) {
        }

        @SuppressWarnings("unused")
        private static String expression(Object value) {
            return "{\"schemaVersion\":1,\"active\":true,"
                    + "\"symbolic\":false,\"expression\":null}";
        }

        @SuppressWarnings("unused")
        private static String finishRegion() {
            return "{\"schemaVersion\":1,\"engine\":\"switch-mock\","
                    + "\"active\":true,\"pathCondition\":"
                    + pathCondition() + "}";
        }

        @SuppressWarnings("unused")
        private static String pathCondition() {
            StringBuilder result = new StringBuilder("[");
            for (int index = 0; index < conditionKeys.length; index++) {
                if (index > 0) result.append(',');
                result.append(switchCondition(conditionOperators[index],
                        conditionKeys[index]));
            }
            return result.append(']').toString();
        }

        @SuppressWarnings("unused")
        private static void pausePathCondition() {
        }

        @SuppressWarnings("unused")
        private static void resumePathCondition() {
        }

        @SuppressWarnings("unused")
        private static long markBranch(String site, int sequence) {
            siteId = site;
            markerSequence = sequence;
            return EVENT_ID;
        }

        @SuppressWarnings("unused")
        private static String branchEvents() {
            JsonObject event = new JsonObject();
            event.addProperty("eventId", EVENT_ID);
            event.addProperty("contextId", CONTEXT_ID);
            event.addProperty("ownerJavaThreadId", ownerThreadId);
            event.addProperty("ownerOsThreadId", OS_THREAD_ID);
            event.addProperty("regionId", regionId);
            event.addProperty("activationId", activationId);
            event.addProperty("siteId", siteId);
            event.addProperty("occurrence", markerSequence);
            event.addProperty("outcome", outcome);
            event.addProperty("opcode", opcode);
            event.addProperty("codePosition", CODE_POSITION);
            JsonArray indices = new JsonArray();
            for (int index : conditionIndices) indices.add(index);
            event.add("conditionIndices", indices);
            event.addProperty("conditionCount", conditionIndices.length);
            event.addProperty("authority",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");

            JsonObject envelope = new JsonObject();
            envelope.addProperty("schemaVersion", 1);
            envelope.addProperty("kind",
                    "CONCOLIC_THREAD_BRANCH_EVENTS");
            envelope.addProperty("active", true);
            envelope.addProperty("contextId", CONTEXT_ID);
            envelope.addProperty("ownerJavaThreadId", ownerThreadId);
            envelope.addProperty("ownerOsThreadId", OS_THREAD_ID);
            envelope.addProperty("regionId", regionId);
            envelope.addProperty("activationId", activationId);
            JsonArray events = new JsonArray();
            events.add(event);
            envelope.add("events", events);
            return envelope.toString();
        }

        private static String switchCondition(String operator, int key) {
            return "{\"_type\":\"BinaryExpression\","
                    + "\"_left\":{\"_type\":\"SymbolExpression\","
                    + "\"_java_type\":\"I\","
                    + "\"_exp\":\"switch_selector\"},"
                    + "\"_op\":\"" + operator + "\","
                    + "\"_right\":{\"_type\":\"ConstExpr\","
                    + "\"_java_type\":\"I\","
                    + "\"_exp\":\"Y_I_" + key + "\"},"
                    + "\"_code_position\":\"" + CODE_POSITION
                    + "\"}";
        }

        @SuppressWarnings("unused")
        private static void endRegion() {
        }
    }

    /** Ordinary-JDK stand-in for the custom System APIs and their timing. */
    private static final class DelayedExpressionEngine {
        private static final java.util.IdentityHashMap<Object, Boolean>
                SYMBOLIC_FIELD_OWNERS = new java.util.IdentityHashMap<>();
        private static final java.util.IdentityHashMap<Object, String>
                SYMBOLIC_FIELD_PREFIXES = new java.util.IdentityHashMap<>();
        private static final java.util.IdentityHashMap<Object, String>
                SYMBOLIC_ARRAY_IDS = new java.util.IdentityHashMap<>();
        private static int valueExpressionCalls;
        private static int nextArrayId;
        private static int pathConditionPauseDepth;
        private static int arrayExpressionCallsOutsidePause;
        private static String arrayExpressionMode = "NORMAL";
        private static String forcedArrayId = "";
        private static Object arrayFieldMutationOwner;
        private static String arrayFieldMutationName = "";
        private static Object arrayFieldMutationReplacement;
        private static boolean integerOutputExpressions;
        private static boolean mapExpressionsAvailable;

        private static void reset() {
            SYMBOLIC_FIELD_OWNERS.clear();
            SYMBOLIC_FIELD_PREFIXES.clear();
            SYMBOLIC_ARRAY_IDS.clear();
            valueExpressionCalls = 0;
            nextArrayId = 1;
            pathConditionPauseDepth = 0;
            arrayExpressionCallsOutsidePause = 0;
            arrayExpressionMode = "NORMAL";
            forcedArrayId = "";
            arrayFieldMutationOwner = null;
            arrayFieldMutationName = "";
            arrayFieldMutationReplacement = null;
            integerOutputExpressions = false;
            mapExpressionsAvailable = true;
        }

        @SuppressWarnings("unused")
        private static long startRegion(String region, String activation) {
            reset();
            return 0L;
        }

        @SuppressWarnings("unused")
        private static void symbolize(Object value, String prefix) {
            symbolizeArray(value);
            if (arrayFieldMutationOwner != null
                    && !arrayFieldMutationName.isEmpty()) {
                try {
                    java.lang.reflect.Field field = arrayFieldMutationOwner
                            .getClass().getDeclaredField(
                                    arrayFieldMutationName);
                    if (!field.isAccessible()) field.setAccessible(true);
                    field.set(arrayFieldMutationOwner,
                            arrayFieldMutationReplacement);
                } catch (Throwable ignored) {
                    // The runtime negative test observes a failed mutation as
                    // an unexpectedly complete same-reference proof.
                } finally {
                    arrayFieldMutationOwner = null;
                    arrayFieldMutationName = "";
                    arrayFieldMutationReplacement = null;
                }
            }
        }

        @SuppressWarnings("unused")
        private static void symbolizeField(Object owner, String field,
                                           String prefix) {
            SYMBOLIC_FIELD_OWNERS.put(owner, Boolean.TRUE);
            SYMBOLIC_FIELD_PREFIXES.put(owner, prefix);
            try {
                java.lang.reflect.Field declared = owner.getClass()
                        .getDeclaredField(field);
                if (!declared.isAccessible()) declared.setAccessible(true);
                symbolizeArray(declared.get(owner));
            } catch (Throwable ignored) {
                // Non-array field tests retain their existing behavior.
            }
        }

        @SuppressWarnings("unused")
        private static String expression(Object value) {
            if (value != null && value.getClass().isArray()) {
                if (pathConditionPauseDepth <= 0) {
                    arrayExpressionCallsOutsidePause++;
                }
                return arrayEnvelope(value);
            }
            if (value instanceof String) {
                return envelope("java/lang/String",
                        "M_L_field_REGION.TEST.in.0_java/lang/String");
            }
            if (value instanceof java.util.Map) {
                return mapExpressionsAvailable
                        ? envelope("java/util/HashMap", "entryMap")
                        : emptyEnvelope();
            }
            if (value instanceof Integer && integerOutputExpressions) {
                return integerEnvelope(((Integer) value).intValue());
            }
            if (value instanceof ExpiringValue) {
                valueExpressionCalls++;
                return SYMBOLIC_FIELD_OWNERS.containsKey(value)
                        ? envelope(ExpiringValue.class.getName()
                        .replace('.', '/'), "entryValue")
                        : emptyEnvelope();
            }
            // Integer deliberately has no JDK shadow ref so the runtime must
            // build its exact immutable-key ConstExpr fallback. Map.Entry is
            // also deliberately expression-less and remains optional.
            return emptyEnvelope();
        }

        private static String envelope(String javaType, String symbol) {
            return "{\"schemaVersion\":1,\"active\":true,"
                    + "\"symbolic\":true,\"expression\":{"
                    + "\"_type\":\"SymbolExpression\","
                    + "\"_java_type\":\"" + javaType + "\","
                    + "\"_exp\":\"" + symbol + "\"}}";
        }

        private static String emptyEnvelope() {
            return "{\"schemaVersion\":1,\"active\":true,"
                    + "\"symbolic\":false,\"expression\":null}";
        }

        private static String integerEnvelope(int value) {
            return "{\"schemaVersion\":1,\"kind\":\"CONCRETE_VALUE\","
                    + "\"active\":true,\"symbolic\":false,"
                    + "\"expressionAuthority\":"
                    + "\"TEST_EXACT_BOXED_PRIMITIVE_VALUE\","
                    + "\"javaTypeDescriptor\":\"I\",\"expression\":{"
                    + "\"_type\":\"ConstExpr\",\"_java_type\":\"I\","
                    + "\"_exp\":\"Y_I_" + value + "\"}}";
        }

        private static void symbolizeArray(Object value) {
            if (value == null || !value.getClass().isArray()
                    || SYMBOLIC_ARRAY_IDS.containsKey(value)) {
                return;
            }
            String descriptor = value.getClass().getName()
                    .replace('.', '/');
            char componentType = descriptor.length() > 1
                    ? descriptor.charAt(1) : '?';
            String id;
            if (!forcedArrayId.isEmpty()) {
                id = forcedArrayId;
            } else if ("MALFORMED_ARRAY_ID".equals(arrayExpressionMode)) {
                id = "ARRAY_" + nextArrayId++;
            } else if ("WRONG_ARRAY_ID_TYPE".equals(
                    arrayExpressionMode)) {
                id = "A" + (componentType == 'I' ? 'L' : 'I') + "_"
                        + nextArrayId++;
            } else {
                id = "A" + componentType + "_" + nextArrayId++;
            }
            SYMBOLIC_ARRAY_IDS.put(value, id);
        }

        private static String arrayEnvelope(Object value) {
            String descriptor = value.getClass().getName()
                    .replace('.', '/');
            if ("WRONG_DESCRIPTOR".equals(arrayExpressionMode)) {
                descriptor = "[Ljava/lang/String;";
            }
            int reflectedLength = java.lang.reflect.Array.getLength(value);
            int vmLength = "WRONG_LENGTH".equals(arrayExpressionMode)
                    ? reflectedLength + 1 : reflectedLength;
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ArrayValueExpression");
            expression.addProperty("_schema_version", 1);
            expression.addProperty("_java_type", descriptor);
            expression.addProperty("_component_java_type",
                    descriptor.substring(1));
            expression.addProperty("_concrete_length", vmLength);
            JsonObject length = new JsonObject();
            length.addProperty("_type", "ConstExpr");
            length.addProperty("_java_type", "I");
            length.addProperty("_exp", "Y_I_" + ("WRONG_LENGTH_EXPRESSION"
                    .equals(arrayExpressionMode)
                    ? reflectedLength + 1 : reflectedLength));
            expression.add("_length_exp", length);
            expression.addProperty("_elements_complete",
                    !"OPAQUE_ELEMENTS".equals(arrayExpressionMode));
            JsonArray elements = new JsonArray();
            for (int index = 0; index < reflectedLength; index++) {
                JsonObject element = new JsonObject();
                element.addProperty("index", "WRONG_ELEMENT_INDEX".equals(
                        arrayExpressionMode) && index == 0 ? 1 : index);
                Object concrete = java.lang.reflect.Array.get(value, index);
                JsonObject valueExpression = new JsonObject();
                String component = value.getClass().getComponentType()
                        .getName();
                if (concrete == null) {
                    valueExpression.addProperty("_type",
                            "SymbolExpression");
                    valueExpression.addProperty("_java_type", component);
                    valueExpression.addProperty("_exp", "N");
                    element.addProperty("provenance", "CONCRETE_NULL");
                } else if (value.getClass().getComponentType()
                        .isPrimitive()) {
                    valueExpression.addProperty("_type", "ConstExpr");
                    String componentDescriptor = descriptor.substring(1);
                    valueExpression.addProperty("_java_type",
                            componentDescriptor);
                    String literal = String.valueOf(concrete);
                    if ("WRONG_PRIMITIVE_LITERAL".equals(
                            arrayExpressionMode) && index == 0) {
                        literal = "999";
                    }
                    valueExpression.addProperty("_exp", "Y_"
                            + componentDescriptor + "_" + literal);
                    element.addProperty("provenance",
                            "CONCRETE_PRIMITIVE");
                } else {
                    valueExpression.addProperty("_type",
                            "SymbolExpression");
                    valueExpression.addProperty("_java_type", component);
                    valueExpression.addProperty("_exp", "EL_" + index);
                    element.addProperty("provenance",
                            "WRONG_PROVENANCE".equals(arrayExpressionMode)
                                    ? "OPAQUE" : "SYMBOLIC_ELEMENT");
                }
                if (!"OPAQUE_ELEMENTS".equals(arrayExpressionMode)) {
                    element.add("expression", valueExpression);
                } else {
                    element.add("expression",
                            JsonParser.parseString("null"));
                }
                elements.add(element);
            }
            expression.add("_elements", elements);
            if (!"MISSING_ARRAY_ID".equals(arrayExpressionMode)) {
                expression.addProperty("_engine_array_id",
                        SYMBOLIC_ARRAY_IDS.get(value));
                expression.addProperty("_engine_array_id_authority",
                        "WRONG_ID_AUTHORITY".equals(arrayExpressionMode)
                                ? "UNTRUSTED" : "VM_ACTIVE_SYM_ARRAY_ID_V1");
            }
            expression.addProperty("_authority",
                    "VM_EXACT_FINITE_ARRAY_VALUE_V1");
            JsonObject envelope = new JsonObject();
            envelope.addProperty("schemaVersion", 1);
            envelope.addProperty("active",
                    !"INACTIVE".equals(arrayExpressionMode));
            envelope.addProperty("symbolic", true);
            envelope.addProperty("kind", "ARRAY_VALUE");
            envelope.add("expression", expression);
            return envelope.toString();
        }

        @SuppressWarnings("unused")
        private static String finishRegion() {
            return "{\"schemaVersion\":1,\"engine\":\"mock\","
                    + "\"active\":true,\"pathCondition\":[]}";
        }

        @SuppressWarnings("unused")
        private static String pathCondition() {
            return "[]";
        }

        @SuppressWarnings("unused")
        private static void pausePathCondition() {
            pathConditionPauseDepth++;
        }

        @SuppressWarnings("unused")
        private static void resumePathCondition() {
            if (pathConditionPauseDepth > 0) pathConditionPauseDepth--;
        }

        @SuppressWarnings("unused")
        private static void endRegion() {
        }
    }
}
