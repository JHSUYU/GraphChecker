package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.ConcolicReplayValidator;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.RegionCaptureGoal;
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
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

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

        JsonObject activation = concreteActivation(
                "ACT.MODEL.STATIC.PRIMITIVE", root, 1);
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", field);
        action.addProperty("field", field);
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessOwnerClass", "example.StaticInputs");
        action.addProperty("accessField", "t");
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
        activation.add("materializations", singleton(action));

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
            long token = ConcolicRegionRuntime.enterRegionFrame(root,
                    new Object(), new Object[0]);
            assertTrue(token > 0L);
            Object materialized = ConcolicRegionRuntime
                    .materializeStaticPrimitiveField(method, 7, field, "t",
                            Integer.valueOf(10));
            assertEquals(Integer.valueOf(21), materialized);
            ConcolicRegionRuntime.exitRegionFrame(root, null, "");

            JsonObject result = resultRows(results).get(0);
            assertTrue(result.get("allModelAssignmentsApplied")
                    .getAsBoolean());
            JsonObject applied = result.getAsJsonArray(
                    "modelAssignmentsApplied").get(0).getAsJsonObject();
            assertEquals(symbol, applied.get("inputSymbol").getAsString());
            assertEquals("STATIC_FIELD_READ",
                    applied.get("appliedAt").getAsString());
            assertEquals("21", applied.get("value").getAsString());
            assertEquals("t", applied.getAsJsonArray(
                    "materializationPath").get(0).getAsString());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void rejectsMalformedExecutableMaterializationCatalogs()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.ProtocolInput: void run(java.lang.Object)>";

        JsonObject missing = concreteActivation(
                "ACT.MATERIALIZATIONS.MISSING", root, 1);
        missing.remove("materializations");
        JsonObject wrongType = concreteActivation(
                "ACT.MATERIALIZATIONS.WRONG.TYPE", root, 1);
        wrongType.addProperty("materializations", "not-an-array");
        JsonObject nonObject = concreteActivation(
                "ACT.MATERIALIZATIONS.NON.OBJECT", root, 1);
        JsonArray malformedMembers = new JsonArray();
        malformedMembers.add("not-an-action");
        nonObject.add("materializations", malformedMembers);

        String[] old = installPlan(plan, results, "concrete-overlap-test");
        try {
            for (JsonObject activation : Arrays.asList(
                    missing, wrongType, nonObject)) {
                Files.write(plan, (activation + "\n").getBytes(
                        StandardCharsets.UTF_8));
                ConcolicRegionRuntime.resetForTests();
                try {
                    ConcolicRegionRuntime.enterRegion(root, new Object());
                    throw new AssertionError("non-canonical executable "
                            + "materializations must fail closed");
                } catch (IllegalStateException expected) {
                    assertTrue(expected.getMessage(), expected.getMessage()
                            .contains("materializations"));
                    assertTrue(expected.getMessage(), expected.getMessage()
                            .contains(activation.get("activationId")
                                    .getAsString()));
                }
            }
            assertFalse(Files.exists(results));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void declarationCatalogIsNotAnExecutableFallback()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.DeclaredInput: void run(java.lang.String)>";
        JsonObject activation = concreteActivation(
                "ACT.DECLARATION.ONLY", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        JsonObject declaration = new JsonObject();
        declaration.addProperty("symbol", "REGION.DECLARED.in.0");
        declaration.addProperty("cell", root
                + ".param0:java.lang.String");
        declaration.addProperty("location", "ARGUMENT");
        declaration.addProperty("bindingMode", "ROOT_ENTRY");
        declaration.addProperty("index", 0);
        declaration.addProperty("javaType", "java.lang.String");
        activation.add("symbolize", singleton(declaration));
        assertEquals(0, activation.getAsJsonArray(
                "materializations").size());
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            assertTrue(token > 0L);
            ConcolicRegionRuntime.symbolizeArgument(token, 0, "seed", "");
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject result = resultRows(results).get(0);
            assertEquals(0, result.getAsJsonArray(
                    "symbolizedInputs").size());
            assertEquals(0, result.getAsJsonArray(
                    "unresolvedInputs").size());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void nonNullNullableStringReplayPreservesFalseNullAttestation()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.NullableInput: void run(java.lang.String)>";
        String symbol = "REGION.NULLABLE.in.0";

        JsonObject activation = concreteActivation(
                "ACT.MODEL.NULLABLE.NON_NULL", root, 1);
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", root + ".param0:java.lang.String");
        action.addProperty("location", "ARGUMENT");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", 0);
        action.addProperty("javaType", "java.lang.String");
        addExecutableActions(activation, singleton(action));

        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "M_L_String_nullable");
        assignment.addProperty("solverSymbol", "sym__nullable_content");
        assignment.addProperty("nullnessSolverSymbol",
                "sym__nullable_is_null");
        assignment.addProperty("modelIsNull", false);
        assignment.addProperty("inputSymbol", symbol);
        assignment.addProperty("valueType", "STRING");
        assignment.addProperty("value", "\"modeled\"");
        assignment.addProperty("nullableStringEncodingAuthority",
                "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1");
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        assignment.add("target", action.deepCopy());
        activation.add("modelAssignments", singleton(assignment));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "concrete-model-test");
        try {
            long token = ConcolicRegionRuntime.enterRegionFrame(root,
                    new Object(), new Object[]{"seed"});
            assertTrue(token > 0L);
            assertEquals("modeled", ConcolicRegionRuntime
                    .materializeArgument(token, 0, "seed", ""));
            ConcolicRegionRuntime.exitRegionFrame(root, null, "");

            JsonObject result = resultRows(results).get(0);
            assertTrue(result.get("allModelAssignmentsApplied")
                    .getAsBoolean());
            JsonObject applied = result.getAsJsonArray(
                    "modelAssignmentsApplied").get(0).getAsJsonObject();
            assertTrue("explicit false is part of the replay attestation",
                    applied.has("modelIsNull"));
            assertFalse(applied.get("modelIsNull").getAsBoolean());
            assertEquals("java.lang.String",
                    applied.get("concreteValueClass").getAsString());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void valueRefWitnessSymbolIsActivationAndTokenScoped() {
        JsonObject first = ConcolicRegionRuntime
                .valueRefWitnessExpressionForTests("ACT.P", 103L);
        JsonObject otherActivation = ConcolicRegionRuntime
                .valueRefWitnessExpressionForTests("ACT.Q", 103L);
        JsonObject otherToken = ConcolicRegionRuntime
                .valueRefWitnessExpressionForTests("ACT.P", 104L);

        assertEquals("SymbolExpression", first.get("_type").getAsString());
        assertEquals("L", first.get("_java_type").getAsString());
        assertEquals("CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T103",
                first.get("_exp").getAsString());
        assertFalse(first.get("_exp").equals(otherActivation.get("_exp")));
        assertFalse(first.get("_exp").equals(otherToken.get("_exp")));
    }

    @Test
    public void gson22CompatibleJsonCopyIsDeepAndIndependent() {
        JsonObject original = new JsonObject();
        JsonObject nested = new JsonObject();
        nested.addProperty("value", 7);
        JsonArray values = new JsonArray();
        values.add("first");
        nested.add("values", values);
        original.add("nested", nested);

        JsonObject copy = ConcolicRegionRuntime.copyJsonTree(original);

        assertEquals(original, copy);
        assertNotSame(original, copy);
        assertNotSame(original.getAsJsonObject("nested"),
                copy.getAsJsonObject("nested"));
        assertNotSame(original.getAsJsonObject("nested")
                        .getAsJsonArray("values"),
                copy.getAsJsonObject("nested").getAsJsonArray("values"));

        copy.getAsJsonObject("nested").addProperty("value", 9);
        copy.getAsJsonObject("nested").getAsJsonArray("values")
                .add("second");
        assertEquals(7, original.getAsJsonObject("nested")
                .get("value").getAsInt());
        assertEquals(1, original.getAsJsonObject("nested")
                .getAsJsonArray("values").size());

        original.getAsJsonObject("nested").addProperty("originalOnly", true);
        assertFalse(copy.getAsJsonObject("nested").has("originalOnly"));
    }

    @Test
    public void runtimeSourceDoesNotCallVersionSensitiveGsonTreeCopy()
            throws Exception {
        Path source = Paths.get("src", "main", "java", "edu", "uva",
                "liftlab", "graphchecker", "runtime",
                "ConcolicRegionRuntime.java");
        assertTrue("runtime source must be available to the regression test",
                Files.isRegularFile(source));
        String text = new String(Files.readAllBytes(source),
                StandardCharsets.UTF_8);
        assertFalse("runtime must remain binary-compatible with Gson 2.2.x",
                text.matches("(?s).*\\.deepCopy\\s*\\(.*"));
    }

    @Test
    public void runtimeBytecodeOnlyUsesGson22JsonArrayAddSignature()
            throws Exception {
        final List<String> incompatibleCalls = new ArrayList<>();
        final int[] compatibleCalls = {0};
        List<Class<?>> pending = new ArrayList<>();
        pending.add(ConcolicRegionRuntime.class);
        for (int index = 0; index < pending.size(); index++) {
            final Class<?> type = pending.get(index);
            pending.addAll(Arrays.asList(type.getDeclaredClasses()));
            String resource = "/" + type.getName().replace('.', '/')
                    + ".class";
            ClassReader reader;
            try (InputStream bytecode = type.getResourceAsStream(resource)) {
                if (bytecode == null) {
                    throw new IllegalStateException(
                            "Missing runtime bytecode resource " + resource);
                }
                reader = new ClassReader(bytecode);
            }
            reader.accept(new ClassVisitor(Opcodes.ASM9) {
                @Override
                public MethodVisitor visitMethod(int access, String name,
                                                 String descriptor,
                                                 String signature,
                                                 String[] exceptions) {
                    final String method = name + descriptor;
                    return new MethodVisitor(Opcodes.ASM9) {
                        @Override
                        public void visitMethodInsn(int opcode, String owner,
                                                    String name,
                                                    String descriptor,
                                                    boolean isInterface) {
                            if ("com/google/gson/JsonArray".equals(owner)
                                    && "add".equals(name)) {
                                if ("(Lcom/google/gson/JsonElement;)V"
                                        .equals(descriptor)) {
                                    compatibleCalls[0]++;
                                } else {
                                    incompatibleCalls.add(type.getName()
                                            + "#" + method + " -> "
                                            + owner + "." + name
                                            + descriptor);
                                }
                            }
                        }
                    };
                }
            }, ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES);
        }

        assertTrue("the compatibility check must observe JsonArray.add "
                        + "calls", compatibleCalls[0] > 0);
        assertTrue("Gson 2.2.4 only exposes JsonArray.add(JsonElement): "
                        + incompatibleCalls,
                incompatibleCalls.isEmpty());
    }

    @Test
    public void allActivationSelectionRejectsAmbiguousRuntimeKey()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("ambiguous.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void handle()>";
        JsonObject first = concreteActivation("ACT.FIRST", root, 1);
        first.addProperty("test", "bundle-test");
        JsonObject second = concreteActivation("ACT.SECOND", root, 1);
        second.addProperty("test", "bundle-test");
        Files.write(plan, (first + "\n" + second + "\n").getBytes(
                StandardCharsets.UTF_8));
        String[] old = installPlan(plan, results, "bundle-test");
        try {
            try {
                ConcolicRegionRuntime.enterRegionFrame(root, new Object(),
                        new Object[0]);
                throw new AssertionError("ambiguous ALL bundle must fail");
            } catch (IllegalStateException expected) {
                assertTrue(expected.getMessage().contains(
                        "Ambiguous effective activation runtime key"));
                assertTrue(expected.getMessage().contains("ACT.FIRST"));
                assertTrue(expected.getMessage().contains("ACT.SECOND"));
                assertEquals("failed entry retains one placeholder until "
                                + "the injected catch-all runs", 1,
                        ConcolicRegionRuntime.regionFrameDepthForTests());
                ConcolicRegionRuntime.throwRegionFrame(root, expected);
                assertEquals(0,
                        ConcolicRegionRuntime.regionFrameDepthForTests());
            }

            System.setProperty("causynth.concolic.activation.id",
                    "ACT.SECOND");
            ConcolicRegionRuntime.resetForTests();
            long selectedToken = ConcolicRegionRuntime.enterRegionFrame(root,
                    new Object(), new Object[0]);
            assertTrue(selectedToken > 0L);
            assertEquals(1,
                    ConcolicRegionRuntime.regionFrameDepthForTests());
            ConcolicRegionRuntime.exitRegionFrame(root, null, "");
            assertEquals(0,
                    ConcolicRegionRuntime.regionFrameDepthForTests());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void invocationFramesKeepNestedNormalThrowAndMismatchesExact()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.RecursiveOwner: void run()>";
        String differentRoot = "<example.OtherOwner: void run()>";
        JsonObject activation = concreteActivation(
                "ACT.RECURSIVE.OUTER", root, 1);
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            long outerToken = ConcolicRegionRuntime.enterRegionFrame(root,
                    new Object(), new Object[0]);
            assertTrue(outerToken > 0L);
            assertEquals(1,
                    ConcolicRegionRuntime.regionFrameDepthForTests());

            // Recursive ordinal two is unselected but still owns an exact
            // zero-token frame.  Its normal cleanup cannot expose the caller.
            long nestedNormal = ConcolicRegionRuntime.enterRegionFrame(root,
                    new Object(), new Object[0]);
            assertEquals(0L, nestedNormal);
            assertEquals(2,
                    ConcolicRegionRuntime.regionFrameDepthForTests());
            ConcolicRegionRuntime.exitRegionFrame(root, null, "");
            assertEquals(1,
                    ConcolicRegionRuntime.regionFrameDepthForTests());

            long nestedThrow = ConcolicRegionRuntime.enterRegionFrame(root,
                    new Object(), new Object[0]);
            assertEquals(0L, nestedThrow);
            IllegalStateException nestedFailure =
                    new IllegalStateException("nested failure");
            ConcolicRegionRuntime.throwRegionFrame(root, nestedFailure);
            assertEquals(1,
                    ConcolicRegionRuntime.regionFrameDepthForTests());

            long differentToken = ConcolicRegionRuntime.enterRegionFrame(
                    differentRoot, new Object(), new Object[0]);
            assertEquals(0L, differentToken);
            assertEquals(2,
                    ConcolicRegionRuntime.regionFrameDepthForTests());

            // A malformed cleanup must validate the exact top root before
            // popping.  The different-root frame and selected outer survive.
            ConcolicRegionRuntime.exitRegionFrame(root, null, "");
            assertEquals(2,
                    ConcolicRegionRuntime.regionFrameDepthForTests());
            assertTrue(ConcolicRegionRuntime.activeTokenForTests(outerToken));
            ConcolicRegionRuntime.throwRegionFrame(differentRoot,
                    nestedFailure);
            assertEquals(1,
                    ConcolicRegionRuntime.regionFrameDepthForTests());

            assertTrue("nested cleanup must not finish the selected caller",
                    ConcolicRegionRuntime.activeTokenForTests(outerToken));
            assertEquals(1, ConcolicRegionRuntime
                    .concreteReplayActiveCountForTests());
            assertFalse(Files.exists(results));

            ConcolicRegionRuntime.exitRegionFrame(root, null, "");
            assertFalse(ConcolicRegionRuntime
                    .activeTokenForTests(outerToken));
            assertEquals(0,
                    ConcolicRegionRuntime.regionFrameDepthForTests());
            assertEquals(1, resultRows(results).size());

            // Empty-stack cleanup is also a no-throw no-op.
            ConcolicRegionRuntime.exitRegionFrame(root, null, "");
            ConcolicRegionRuntime.throwRegionFrame(root, nestedFailure);
            assertEquals(0,
                    ConcolicRegionRuntime.regionFrameDepthForTests());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void caughtSameRootEntryFailureKeepsSelectedOuterFrame()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.RecursiveOwner: void run()>";
        JsonObject outerActivation = concreteActivation(
                "ACT.RECURSIVE.OUTER", root, 1);
        Files.write(plan, (outerActivation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            long outerToken = ConcolicRegionRuntime.enterRegionFrame(root,
                    new Object(), new Object[0]);
            assertTrue(outerToken > 0L);
            assertEquals(1,
                    ConcolicRegionRuntime.regionFrameDepthForTests());

            JsonObject duplicateFirst = concreteActivation(
                    "ACT.FAIL.FIRST", root, 2);
            JsonObject duplicateSecond = concreteActivation(
                    "ACT.FAIL.SECOND", root, 2);
            Files.write(plan, (duplicateFirst + "\n" + duplicateSecond
                    + "\n").getBytes(StandardCharsets.UTF_8));
            java.lang.reflect.Field configuration =
                    ConcolicRegionRuntime.class.getDeclaredField(
                            "configuration");
            configuration.setAccessible(true);
            configuration.set(null, null);

            try {
                ConcolicRegionRuntime.enterRegionFrame(root, new Object(),
                        new Object[0]);
                throw new AssertionError("nested entry must reject ambiguity");
            } catch (IllegalStateException expected) {
                assertEquals(2,
                        ConcolicRegionRuntime.regionFrameDepthForTests());
                // Simulate an original same-root handler catching the entry
                // failure and returning normally.
                ConcolicRegionRuntime.exitRegionFrame(root, null, "");
            }
            assertEquals(1,
                    ConcolicRegionRuntime.regionFrameDepthForTests());
            assertTrue(ConcolicRegionRuntime.activeTokenForTests(outerToken));

            try {
                ConcolicRegionRuntime.enterRegionFrame(root, new Object(),
                        new Object[0]);
                throw new AssertionError("nested entry must reject ambiguity");
            } catch (IllegalStateException expected) {
                assertEquals(2,
                        ConcolicRegionRuntime.regionFrameDepthForTests());
                // Simulate the same original handler rethrowing instead.
                ConcolicRegionRuntime.throwRegionFrame(root, expected);
            }
            assertEquals(1,
                    ConcolicRegionRuntime.regionFrameDepthForTests());
            assertTrue(ConcolicRegionRuntime.activeTokenForTests(outerToken));
            assertFalse(Files.exists(results));

            Files.write(plan, (outerActivation + "\n").getBytes(
                    StandardCharsets.UTF_8));
            configuration.set(null, null);
            ConcolicRegionRuntime.exitRegionFrame(root, null, "");
            assertEquals(0,
                    ConcolicRegionRuntime.regionFrameDepthForTests());
            assertFalse(ConcolicRegionRuntime.activeTokenForTests(outerToken));
            assertEquals(1, resultRows(results).size());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void dynamicEngineSymbolRequiresExactVmFieldBoundary() {
        String dynamic = "REGION.0.in.5.field.0123456789ab.occ.2";
        assertTrue(ConcolicRegionRuntime.dynamicEngineSymbolMatchesForTests(
                dynamic, dynamic));
        assertTrue(ConcolicRegionRuntime.dynamicEngineSymbolMatchesForTests(
                "M_J_field_" + dynamic, dynamic));
        assertTrue(ConcolicRegionRuntime.dynamicEngineSymbolMatchesForTests(
                "M_Z_field_" + dynamic + "_java/lang/Boolean", dynamic));
        assertTrue(ConcolicRegionRuntime.dynamicEngineSymbolMatchesForTests(
                "M_J_field_" + dynamic
                        + "_org/apache/hadoop/hdfs/security/token/block/BlockKey",
                dynamic));

        assertFalse(ConcolicRegionRuntime.dynamicEngineSymbolMatchesForTests(
                "M_J_field_" + dynamic + "0_java/lang/Long", dynamic));
        assertFalse(ConcolicRegionRuntime.dynamicEngineSymbolMatchesForTests(
                "M_J_field_prefix_" + dynamic + "_java/lang/Long",
                dynamic));
        assertFalse(ConcolicRegionRuntime.dynamicEngineSymbolMatchesForTests(
                "M_Q_field_" + dynamic + "_java/lang/Long", dynamic));
        assertFalse(ConcolicRegionRuntime.dynamicEngineSymbolMatchesForTests(
                "M_J_field_" + dynamic + "_java.lang.Long", dynamic));
        assertFalse(ConcolicRegionRuntime.dynamicEngineSymbolMatchesForTests(
                "M_J_field_" + dynamic + "_java/lang/Long/", dynamic));
    }

    @Test
    public void normalizesReceiverFieldSignatureBeforeReflection() {
        assertEquals("allKeys", ConcolicRegionRuntime.runtimeFieldName(
                "<example.Manager: java.util.Map allKeys>", ""));
        assertEquals("keyId", ConcolicRegionRuntime.runtimeFieldName(
                "keyId", ""));
        assertEquals("allKeys", ConcolicRegionRuntime.runtimeFieldName(
                "", "@this: example.Manager#field:allKeys"));
    }

    @Test
    public void rejectsStaleTimeConditionForReferenceBranch() {
        assertFalse(ConcolicRegionRuntime.branchConditionMatches(
                "r25 != null", true, new JsonParser().parse(
                        "{\"_type\":\"BinaryExpression\","
                                + "\"_left\":{\"_type\":\"PlaceholderExpression\"},"
                                + "\"_op\":\"<\","
                                + "\"_right\":{\"_type\":\"ConstExpr\"}}")));
    }

    @Test
    public void acceptsMapResultNonNullCondition() {
        assertTrue(ConcolicRegionRuntime.branchConditionMatches(
                "r25 != null", true, new JsonParser().parse(
                        "{\"_type\":\"BinaryExpression\","
                                + "\"_left\":{\"_type\":\"SymbolExpression\","
                                + "\"_exp\":\"M_L_map_result\"},"
                                + "\"_op\":\"!=\","
                                + "\"_right\":{\"_type\":\"SymbolExpression\","
                                + "\"_exp\":\"N\"}}")));
    }

    @Test
    public void mapsJvmCompareTrichotomyToInclusiveJimpleBranch() {
        JsonElement greater = JsonParser.parseString(
                "{\"_type\":\"BinaryExpression\","
                        + "\"_left\":{\"_type\":\"PlaceholderExpression\"},"
                        + "\"_op\":\">\","
                        + "\"_right\":{\"_type\":\"ConstExpr\"}}");
        JsonElement equal = JsonParser.parseString(
                "{\"_type\":\"BinaryExpression\","
                        + "\"_left\":{\"_type\":\"PlaceholderExpression\"},"
                        + "\"_op\":\"==\","
                        + "\"_right\":{\"_type\":\"ConstExpr\"}}");
        JsonElement less = JsonParser.parseString(
                "{\"_type\":\"BinaryExpression\","
                        + "\"_left\":{\"_type\":\"PlaceholderExpression\"},"
                        + "\"_op\":\"<\","
                        + "\"_right\":{\"_type\":\"ConstExpr\"}}");

        assertTrue(ConcolicRegionRuntime.branchConditionMatches(
                "cmpResult >= 0", true, greater));
        assertTrue(ConcolicRegionRuntime.branchConditionMatches(
                "cmpResult >= 0", true, equal));
        assertFalse(ConcolicRegionRuntime.branchConditionMatches(
                "cmpResult >= 0", true, less));
        assertTrue(ConcolicRegionRuntime.branchConditionMatches(
                "cmpResult >= 0", false, less));
    }

    @Test
    public void mapsExactBooleanStringPredicateToJimpleZeroTest() {
        JsonElement containsFalse = JsonParser.parseString(
                "{\"_type\":\"OpStrExpression\","
                        + "\"_name\":\"contains\",\"_is_not\":true,"
                        + "\"_param_list\":[{},{}]}");
        JsonElement containsTrue = JsonParser.parseString(
                "{\"_type\":\"OpStrExpression\","
                        + "\"_name\":\"contains\",\"_is_not\":false,"
                        + "\"_param_list\":[{},{}]}");
        JsonElement stringLength = JsonParser.parseString(
                "{\"_type\":\"OpStrExpression\","
                        + "\"_name\":\"length\",\"_is_not\":false,"
                        + "\"_param_list\":[{}]}");

        assertTrue(ConcolicRegionRuntime.branchConditionMatches(
                "$z0 == 0", true, containsFalse));
        assertTrue(ConcolicRegionRuntime.branchConditionMatches(
                "$z0 == 0", false, containsTrue));
        assertTrue(ConcolicRegionRuntime.branchConditionMatches(
                "$z0 != 0", true, containsTrue));
        assertFalse(ConcolicRegionRuntime.branchConditionMatches(
                "$z0 == 0", true, containsTrue));
        assertFalse(ConcolicRegionRuntime.branchConditionMatches(
                "$z0 > 0", true, containsTrue));
        assertFalse(ConcolicRegionRuntime.branchConditionMatches(
                "$z0 == 1", true, containsTrue));
        assertFalse(ConcolicRegionRuntime.branchConditionMatches(
                "$z0 == 0", true, stringLength));
    }

    @Test
    public void exactVmEventSelectsOneOfTwoSameShapeBranchConditions()
            throws Exception {
        JsonObject mapping = runExactBranchEvent(false);

        assertTrue(mapping.get("vmBranchEventValidated").getAsBoolean());
        assertEquals(1, mapping.get("conditionIndex").getAsInt());
        assertEquals(1, mapping.get("branchConditionCandidateCount")
                .getAsInt());
        assertEquals("VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX",
                mapping.get("mappingPolicy").getAsString());
        assertEquals("VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX",
                mapping.get("conditionAuthority").getAsString());
        assertTrue(mapping.has("witness"));
        assertFalse(mapping.has("concreteObservation"));
        assertEquals(77L, mapping.get("vmThreadContextId").getAsLong());
        assertEquals(Thread.currentThread().getId(), mapping.get(
                "vmOwnerJavaThreadId").getAsLong());
        assertEquals(1, mapping.getAsJsonArray("vmConditionIndices")
                .get(0).getAsInt());
    }

    @Test
    public void exactVmEventWithForeignThreadOwnerFailsClosed()
            throws Exception {
        JsonObject mapping = runExactBranchEvent(true);

        assertFalse(mapping.get("vmBranchEventValidated").getAsBoolean());
        assertEquals(-1, mapping.get("conditionIndex").getAsInt());
        assertEquals(0, mapping.get("branchConditionCandidateCount")
                .getAsInt());
        assertEquals("UNRESOLVED_VM_EXACT_BRANCH_EVENT",
                mapping.get("conditionAuthority").getAsString());
        assertTrue(mapping.get("mappingWarning").getAsString().contains(
                "belongs to Java thread"));
        assertEquals("VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX",
                mapping.get("mappingPolicy").getAsString());
    }

    @Test
    public void exactZeroPcBranchIsObservationOnly() throws Exception {
        JsonObject mapping = runExactBranchEvent(false, true);

        assertTrue(mapping.get("vmBranchEventValidated").getAsBoolean());
        assertEquals(-1, mapping.get("conditionIndex").getAsInt());
        assertEquals(0, mapping.get("branchConditionCandidateCount")
                .getAsInt());
        assertEquals("VM_THREAD_CONTEXT_EXACT_CONCRETE_BRANCH_EVENT",
                mapping.get("conditionAuthority").getAsString());
        assertFalse(mapping.has("condition"));
        assertFalse(mapping.has("witness"));
        ExactConcreteBranchObservation observation =
                ExactConcreteBranchObservation.fromJson(
                        mapping.getAsJsonObject("concreteObservation"));
        assertEquals("<example.Target: java.lang.Object lookup(int)>#u7",
                observation.siteId());
        assertEquals(1, observation.occurrence());
        assertTrue(observation.sourceTakenOutcome());
        assertTrue(mapping.get("mappingWarning").getAsString().contains(
                "no newly added target-method condition"));
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
        JsonObject activation = concreteActivation("ACT.EXACT.BRANCH",
                method, 1);
        activation.addProperty("regionId", "REGION.EXACT.BRANCH");
        activation.addProperty("test", "exact-branch-test");
        activation.addProperty("concreteReplayOnly", false);
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
                    new Object());
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

    @Test
    public void selectedLookupSwitchOwnsExactCaseEquality() throws Exception {
        JsonObject mapping = runExactSwitchEvent("LOOKUP_SWITCH",
                "-100,7,1000", 1, 171, true,
                new int[]{7}, new String[]{"=="}, new int[]{0});

        assertTrue(mapping.get("vmBranchEventValidated").getAsBoolean());
        assertEquals(1, mapping.get("observedSuccessorIndex").getAsInt());
        assertEquals(0, mapping.get("conditionIndex").getAsInt());
        assertEquals(1, mapping.getAsJsonArray("conditionIndices").size());
        assertTrue(mapping.get("symbolicSwitchArmComplete").getAsBoolean());
        assertEquals("VM_THREAD_CONTEXT_EXACT_SWITCH_EVENT_PC_INDICES",
                mapping.get("conditionAuthority").getAsString());
    }

    @Test
    public void tableSwitchDefaultOwnsAllOrderedInequalities()
            throws Exception {
        JsonObject mapping = runExactSwitchEvent("TABLE_SWITCH", "1,2,3",
                3, 170, false, new int[]{1, 2, 3},
                new String[]{"!=", "!=", "!="}, new int[]{0, 1, 2});

        assertTrue(mapping.get("vmBranchEventValidated").getAsBoolean());
        assertEquals(-1, mapping.get("conditionIndex").getAsInt());
        assertEquals(3, mapping.getAsJsonArray("conditionIndices").size());
        assertEquals(3, mapping.getAsJsonArray("conditions").size());
        assertTrue(mapping.get("symbolicSwitchArmComplete").getAsBoolean());
        assertFalse(mapping.get(
                "successorAwarePathEnumerationComplete").getAsBoolean());
        assertEquals("MULTIWAY_SWITCH_SUCCESSOR_WORKLIST_REQUIRED",
                mapping.get("successorAwarePathEnumerationGap")
                        .getAsString());
    }

    @Test
    public void switchDefaultWithWrongKeyOrderFailsClosed()
            throws Exception {
        JsonObject mapping = runExactSwitchEvent("LOOKUP_SWITCH", "1,7,30",
                3, 171, false, new int[]{7, 1, 30},
                new String[]{"!=", "!=", "!="}, new int[]{0, 1, 2});

        assertFalse(mapping.get("vmBranchEventValidated").getAsBoolean());
        assertFalse(mapping.get("symbolicSwitchArmComplete").getAsBoolean());
        assertEquals("UNRESOLVED_VM_EXACT_SWITCH_EVENT",
                mapping.get("conditionAuthority").getAsString());
        assertTrue(mapping.get("mappingWarning").getAsString().contains(
                "selector != 1"));
    }

    @Test
    public void concreteSwitchEventIsExactButNotSymbolicClosure()
            throws Exception {
        JsonObject mapping = runExactSwitchEvent("LOOKUP_SWITCH", "1,7,30",
                1, 171, true, new int[0], new String[0], new int[0]);

        assertTrue(mapping.get("vmBranchEventValidated").getAsBoolean());
        assertFalse(mapping.get("symbolicSwitchArmComplete").getAsBoolean());
        assertEquals("VM_THREAD_CONTEXT_EXACT_CONCRETE_SWITCH_EVENT",
                mapping.get("conditionAuthority").getAsString());
        assertFalse(mapping.has("concreteObservation"));
        assertTrue(mapping.get("mappingWarning").getAsString().contains(
                "selector was concrete"));
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
        JsonObject activation = concreteActivation("ACT.EXACT.SWITCH",
                method, 1);
        activation.addProperty("regionId", "REGION.EXACT.SWITCH");
        activation.addProperty("test", "exact-switch-test");
        activation.addProperty("concreteReplayOnly", false);
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
                    new Object());
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
    public void solverScalarsAreCoercedForTheirRealJavaInputType() {
        assertEquals(7, ConcolicRegionRuntime.coerceModelValue(
                "INT", "7", int.class));
        assertEquals(-9L, ConcolicRegionRuntime.coerceModelValue(
                "INT", "-9", long.class));
        assertEquals(true, ConcolicRegionRuntime.coerceModelValue(
                "BOOL", "true", boolean.class));
        assertEquals("hello", ConcolicRegionRuntime.coerceModelValue(
                "STRING", "\"hello\"", String.class));
        assertNull(ConcolicRegionRuntime.coerceModelValue(
                "NULL", "null", String.class));
        assertEquals("null", ConcolicRegionRuntime.coerceModelValue(
                "STRING", "\"null\"", String.class));
        assertEquals(2.5d, ConcolicRegionRuntime.coerceModelValue(
                "REAL", "(/ 5.0 2.0)", double.class));
        assertEquals(-2.5d, ConcolicRegionRuntime.coerceModelValue(
                "REAL", "(- (/ 5.0 2.0))", double.class));
    }

    @Test
    public void resolvesOnlyTheConcreteOwnerOfARequestedNestedLeaf() {
        Envelope envelope = new Envelope();

        assertSame(envelope.payload, ConcolicRegionRuntime
                .resolveFieldPathLeafOwner(envelope,
                        Arrays.asList("payload", "entries")));
        assertSame(envelope.payload.current, ConcolicRegionRuntime
                .resolveFieldPathLeafOwner(envelope,
                        Arrays.asList("payload", "current", "id")));
        assertSame(envelope.payload.elements[1], ConcolicRegionRuntime
                .resolveFieldPathLeafOwner(envelope,
                        Arrays.asList("payload", "elements", "[1]", "id")));
    }

    @Test
    public void descendantArrayElementAssignmentsTargetTheOwningFieldAction() {
        String field = "<" + Payload.class.getName()
                + ": " + Current[].class.getName() + " elements>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.10.in.6");
        action.addProperty("cell", field);
        action.addProperty("location", "HEAP_OBJECT_FIELD");

        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "M_I_element_field");
        assignment.addProperty("inputSymbol", "REGION.10.in.6");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "9");
        assignment.add("materializationPath", JsonParser.parseString(
                "[\"elements\",\"[1]\",\"id\"]"));

        assertTrue(ConcolicRegionRuntime
                .modelAssignmentTargetsFieldForTests(action, assignment));
    }

    @Test
    public void mapClearModelMutatesTheRealUpstreamCollection() {
        Manager manager = new Manager();
        manager.allKeys.put("old", "value");
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "port__REGION_10_in_0");
        assignment.addProperty("inputSymbol", "REGION.10.in.0");
        assignment.addProperty("valueType", "MAP_STATE");
        assignment.addProperty("value", "emptyMapState");
        assignment.addProperty("modelOperation", "MAP_CLEAR");

        assertTrue(ConcolicRegionRuntime.writeModeledFieldForTests(
                manager, "allKeys", assignment));
        assertTrue(manager.allKeys.isEmpty());
    }

    @Test
    public void arrayDetachmentBreaksInputAliasesBeforeScalarProjection() {
        ArrayEnvelope envelope = new ArrayEnvelope();
        Current original = envelope.elements[0];
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "array__AL_6");
        assignment.addProperty("inputSymbol", "REGION.10.in.6");
        assignment.addProperty("valueType", "REF_ARRAY");
        assignment.addProperty("value", "FRESH_SHALLOW_COPIES");
        assignment.addProperty("modelOperation",
                "ARRAY_SHALLOW_COPY_ELEMENTS");

        assertTrue(ConcolicRegionRuntime.writeModeledFieldForTests(
                envelope, "elements", assignment));
        assertNotSame(original, envelope.elements[0]);
        assertEquals(original.id, envelope.elements[0].id);
    }

    @Test
    public void exactArrayModelWriteDoesNotSelectHiddenSubclassField() {
        HiddenArraySub owner = new HiddenArraySub();
        Current[] subclassValue = owner.values;
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "array__hidden");
        assignment.addProperty("inputSymbol", "REGION.ARRAY.in.hidden");
        assignment.addProperty("valueType", "NULL");
        assignment.addProperty("value", "null");
        String baseSignature = "<" + HiddenArrayBase.class.getName()
                + ": " + Current.class.getName() + "[] values>";

        assertTrue(ConcolicRegionRuntime.writeModeledExactFieldForTests(
                owner, baseSignature, assignment));
        assertEquals(null, ((HiddenArrayBase) owner).values);
        assertSame(subclassValue, owner.values);

        HiddenArraySub rejected = new HiddenArraySub();
        String wrongType = "<" + HiddenArrayBase.class.getName()
                + ": java.lang.Object[] values>";
        assertFalse(ConcolicRegionRuntime.writeModeledExactFieldForTests(
                rejected, wrongType, assignment));
        assertTrue(((HiddenArrayBase) rejected).values != null);
        assertTrue(rejected.values != null);
    }

    @Test
    public void fieldSymbolizationNeverAliasesAnOwnerlessSameNamedProjection() {
        String managerOwner = Manager.class.getName();
        String managerField = "<" + managerOwner
                + ": java.util.Map allKeys>";
        JsonObject exact = new JsonObject();
        exact.addProperty("symbol", "REGION.0.in.25");
        exact.addProperty("cell", managerField);
        exact.addProperty("location", "HEAP_OBJECT_FIELD");
        exact.addProperty("field", managerField);

        JsonObject ambiguous = new JsonObject();
        ambiguous.addProperty("symbol", "REGION.0.in.51");
        ambiguous.addProperty("cell", "<example.NamenodeProtocol: "
                + "example.ExportedKeys getBlockKeys()>.return#field:allKeys");
        ambiguous.addProperty("location", "HEAP_OBJECT_FIELD");

        Manager manager = new Manager();
        assertTrue(ConcolicRegionRuntime.symbolizeActionMatchesFieldForTests(
                exact, manager, managerField, "allKeys"));
        assertFalse(ConcolicRegionRuntime.symbolizeActionMatchesFieldForTests(
                ambiguous, manager, managerField, "allKeys"));
    }

    @Test
    public void runtimeDerivedFieldSiteRequiresExactSiteOwnerAndDeclaration() {
        String owner = Manager.class.getName();
        String signature = "<" + owner + ": java.util.Map allKeys>";
        String method = "<example.ManagerReader: void retrieve()>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.0.in.allKeys");
        action.addProperty("cell", signature + "#field:key");
        action.addProperty("field", signature);
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature", signature);
        action.addProperty("accessOwnerClass", owner);
        action.addProperty("accessFieldType", "java.util.Map");
        action.addProperty("accessField", "allKeys");
        action.addProperty("accessMethod", method);
        action.addProperty("accessUnitIndex", 7);
        action.addProperty("accessSiteId", method + "#u7");
        action.addProperty("accessSiteAuthority",
                "RUNTIME_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1");

        Manager manager = new Manager();
        assertTrue(ConcolicRegionRuntime
                .symbolizeActionMatchesFieldAtSiteForTests(action,
                        method, 7, manager, signature, "allKeys"));
        assertFalse(ConcolicRegionRuntime
                .symbolizeActionMatchesFieldAtSiteForTests(action,
                        method, 8, manager, signature, "allKeys"));
        assertFalse(ConcolicRegionRuntime
                .symbolizeActionMatchesFieldAtSiteForTests(action,
                        "<example.Other: void retrieve()>", 7,
                        manager, signature, "allKeys"));
        assertFalse(ConcolicRegionRuntime
                .symbolizeActionMatchesFieldAtSiteForTests(action,
                        method, 7, manager,
                        "<" + owner + ": java.util.SortedMap allKeys>",
                        "allKeys"));

        action.addProperty("accessOwnerClass", AssignmentOwner.class.getName());
        assertFalse(ConcolicRegionRuntime
                .symbolizeActionMatchesFieldAtSiteForTests(action,
                        method, 7, manager, signature, "allKeys"));
    }

    @Test
    public void promotedAccessorFieldRequiresItsRuntimeParentCallSite() {
        String owner = Manager.class.getName();
        String signature = "<" + owner + ": java.util.Map allKeys>";
        String caller = "<example.Handler: void run()>";
        String accessor = "<" + owner + ": java.util.Map getAllKeys()>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.0.in.expiry");
        action.addProperty("cell", signature);
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature", signature);
        action.addProperty("accessOwnerClass", owner);
        action.addProperty("accessFieldType", "java.util.Map");
        action.addProperty("accessField", "allKeys");
        action.addProperty("accessorCallerMethod", caller);
        action.addProperty("accessorCallSiteId", caller + "#u11");
        action.addProperty("accessorCallUnitIndex", 11);
        action.addProperty("accessorDeclaredCallee", accessor);
        action.addProperty("accessorImplementationMethod", accessor);
        action.addProperty("accessorImplementationAuthority",
                "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
        action.addProperty("accessorCallSiteAuthority",
                "STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                        + "ACCESSOR_CALLSITE_V1");

        Manager manager = new Manager();
        assertTrue(ConcolicRegionRuntime
                .symbolizeActionMatchesFieldAtAccessorCallSiteForTests(
                        action, accessor, 1, manager, signature, "allKeys",
                        true));
        assertFalse(ConcolicRegionRuntime
                .symbolizeActionMatchesFieldAtAccessorCallSiteForTests(
                        action, accessor, 1, manager, signature, "allKeys",
                        false));

        action.remove("accessorCallSiteAuthority");
        assertFalse(ConcolicRegionRuntime
                .symbolizeActionMatchesFieldAtAccessorCallSiteForTests(
                        action, accessor, 1, manager, signature, "allKeys",
                        true));
    }

    @Test
    public void lightweightAccessorContextIsActivationThreadReceiverNestedAndCleanupScoped()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Region: void run()>";
        String caller = "<example.Handler: void prune()>";
        String nestedCaller = "<example.Helper: void inspect()>";
        String owner = Manager.class.getName();
        String signature = "<" + owner + ": java.util.Map allKeys>";
        String accessor = "<" + owner + ": java.util.Map getAllKeys()>";
        JsonObject activation = concreteActivation(
                "ACT.ACCESSOR.CONTEXT", root, 1);
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.TEST.in.keys");
        action.addProperty("cell", signature);
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature", signature);
        action.addProperty("accessOwnerClass", owner);
        action.addProperty("accessFieldType", "java.util.Map");
        action.addProperty("accessField", "allKeys");
        action.addProperty("accessorCallerMethod", caller);
        action.addProperty("accessorCallSiteId", caller + "#u11");
        action.addProperty("accessorCallUnitIndex", 11);
        action.addProperty("accessorDeclaredCallee", accessor);
        action.addProperty("accessorImplementationMethod", accessor);
        action.addProperty("accessorImplementationAuthority",
                "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
        action.addProperty("accessorCallSiteAuthority",
                "STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                        + "ACCESSOR_CALLSITE_V1");

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            Manager selectedOwner = new Manager();
            Manager wrongOwner = new Manager();
            assertEquals(0L, ConcolicRegionRuntime.enterAccessorCallContext(
                    caller, 11, caller + "#u11", accessor,
                    selectedOwner));
            long regionToken = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            assertTrue(regionToken > 0L);

            long outer = ConcolicRegionRuntime.enterAccessorCallContext(
                    caller, 11, caller + "#u11", accessor,
                    selectedOwner);
            assertTrue(outer > 0L);
            assertEquals(Boolean.TRUE, ConcolicRegionRuntime
                    .lightweightAccessorContextMatchesForTests(caller, 11,
                            caller + "#u11", accessor, selectedOwner));
            assertEquals(Boolean.FALSE, ConcolicRegionRuntime
                    .lightweightAccessorContextMatchesForTests(caller, 12,
                            caller + "#u12", accessor, selectedOwner));
            assertTrue(ConcolicRegionRuntime
                    .symbolizeActionMatchesFieldAtSiteForTests(action,
                            accessor, 1, selectedOwner, signature,
                            "allKeys"));
            assertFalse("the right callsite on a different receiver must not "
                            + "fall back to recorder-only matching",
                    ConcolicRegionRuntime
                            .symbolizeActionMatchesFieldAtSiteForTests(action,
                                    accessor, 1, wrongOwner, signature,
                                    "allKeys"));

            final AtomicLong otherThreadToken = new AtomicLong(-1L);
            final java.util.concurrent.atomic.AtomicReference<Boolean>
                    otherThreadMatch = new java.util.concurrent.atomic
                    .AtomicReference<>();
            Thread other = new Thread(() -> {
                otherThreadMatch.set(ConcolicRegionRuntime
                        .lightweightAccessorContextMatchesForTests(caller,
                                11, caller + "#u11", accessor,
                                selectedOwner));
                otherThreadToken.set(ConcolicRegionRuntime
                        .enterAccessorCallContext(caller, 11,
                                caller + "#u11", accessor,
                                selectedOwner));
            });
            other.start();
            other.join();
            assertNull(otherThreadMatch.get());
            assertEquals(0L, otherThreadToken.get());

            long nested = ConcolicRegionRuntime.enterAccessorCallContext(
                    nestedCaller, 4, nestedCaller + "#u4", accessor,
                    wrongOwner);
            assertTrue(nested > 0L);
            assertEquals(Boolean.FALSE, ConcolicRegionRuntime
                    .lightweightAccessorContextMatchesForTests(caller, 11,
                            caller + "#u11", accessor, selectedOwner));
            assertEquals(Boolean.TRUE, ConcolicRegionRuntime
                    .lightweightAccessorContextMatchesForTests(nestedCaller,
                            4, nestedCaller + "#u4", accessor,
                            wrongOwner));
            ConcolicRegionRuntime.exitAccessorCallContext(nested);
            assertEquals(Boolean.TRUE, ConcolicRegionRuntime
                    .lightweightAccessorContextMatchesForTests(caller, 11,
                            caller + "#u11", accessor, selectedOwner));
            ConcolicRegionRuntime.exitAccessorCallContext(outer);
            assertNull(ConcolicRegionRuntime
                    .lightweightAccessorContextMatchesForTests(caller, 11,
                            caller + "#u11", accessor, selectedOwner));

            long leaked = ConcolicRegionRuntime.enterAccessorCallContext(
                    caller, 11, caller + "#u11", accessor,
                    selectedOwner);
            assertTrue(leaked > 0L);
            ConcolicRegionRuntime.exitRegion(regionToken, null, "");
            assertNull("region completion must clean a missed accessor exit",
                    ConcolicRegionRuntime
                            .lightweightAccessorContextMatchesForTests(caller,
                                    11, caller + "#u11", accessor,
                                    selectedOwner));
            ConcolicRegionRuntime.exitAccessorCallContext(leaked);
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void unwrapsEngineExpressionEnvelopeForRuntimeObservation() {
        JsonElement canonical = ConcolicRegionRuntime
                .canonicalEngineExpression("{\"schemaVersion\":1,"
                        + "\"active\":true,\"symbolic\":true,"
                        + "\"kind\":\"SYMBOLIC_OBJECT\","
                        + "\"expression\":{\"_type\":"
                        + "\"SymbolExpression\",\"_exp\":\"map\"}}");

        assertEquals("SymbolExpression", canonical.getAsJsonObject()
                .get("_type").getAsString());
        assertEquals("map", canonical.getAsJsonObject()
                .get("_exp").getAsString());
        assertEquals(null, ConcolicRegionRuntime.canonicalEngineExpression(
                "{\"schemaVersion\":1,\"active\":true,"
                        + "\"symbolic\":false,"
                        + "\"kind\":\"CONCRETE_OBJECT\","
                        + "\"expression\":null}"));
        assertEquals("an inactive VM envelope is not a bare expression",
                null, ConcolicRegionRuntime.canonicalEngineExpression(
                        "{\"schemaVersion\":1,\"active\":false,"
                                + "\"symbolic\":false,"
                                + "\"kind\":\"CONCOLIC_DISABLED\"}"));
    }

    @Test
    public void immutableIntegerEntryKeyFallbackIsComposerReadableAndEntryExpressionOptional() {
        JsonElement map = JsonParser.parseString(
                "{\"_type\":\"SymbolExpression\",\"_java_type\":\"L\","
                        + "\"_exp\":\"map\"}");
        JsonElement value = JsonParser.parseString(
                "{\"_type\":\"SymbolExpression\",\"_java_type\":"
                        + "\"example/Value\",\"_exp\":\"value\"}");
        JsonElement key = ConcolicRegionRuntime
                .immutableEntryKeyExpression(Integer.valueOf(7004));

        assertTrue(key.isJsonObject());
        assertEquals("ConstExpr", key.getAsJsonObject().get("_type")
                .getAsString());
        assertEquals("java/lang/Integer", key.getAsJsonObject()
                .get("_java_type").getAsString());
        assertEquals("Y_I_7004", key.getAsJsonObject().get("_exp")
                .getAsString());
        assertTrue("Map.Entry wrapper expression is optional when exact "
                        + "entry token and same-entry authorities are present",
                ConcolicRegionRuntime.completeMapEntryReadPayload(
                        map, key, value, null, 1L, 2L, 3L, 4L));
        assertFalse(ConcolicRegionRuntime.completeMapEntryReadPayload(
                map, key, null, null, 1L, 2L, 3L, 4L));
        assertFalse(ConcolicRegionRuntime.completeMapEntryReadPayload(
                map, key, value, null, 1L, 0L, 3L, 4L));
        JsonElement nullKey = JsonParser.parseString(
                "{\"_type\":\"SymbolExpression\","
                        + "\"_java_type\":\"L\",\"_exp\":\"N\"}");
        assertTrue("a known null Map key has no identity token but its exact "
                        + "N expression is complete",
                ConcolicRegionRuntime.completeMapEntryReadPayload(
                        map, nullKey, value, null, 1L, 0L, 3L, 4L));
    }

    @Test
    public void recordsCanonicalEntrySetObservationWithoutMutation()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void observe()>";
        JsonObject activation = concreteActivation(
                "ACT.OBSERVE.BACKED.VIEW", root, 1);
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            Manager manager = new Manager();
            manager.allKeys.put("expired", "value");
            long token = ConcolicRegionRuntime.enterRegion(root, manager);
            assertTrue(token > 0L);
            Object view = manager.allKeys.entrySet();
            ConcolicRegionRuntime.registerMapView(root, 3, manager.allKeys,
                    view, "ENTRY_SET");
            java.util.Iterator<?> iterator =
                    ((java.util.Set<?>) view).iterator();
            ConcolicRegionRuntime.registerMapViewIterator(root, 4, view,
                    iterator);
            Object entry = iterator.next();
            ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                    entry);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = JsonParser.parseString(new String(
                    Files.readAllBytes(results), StandardCharsets.UTF_8)
                    .trim()).getAsJsonObject();
            JsonArray observations = row.getAsJsonArray(
                    "runtimeHeapObservations");
            assertEquals(2, observations.size());
            JsonObject observation = observations.get(0).getAsJsonObject();
            JsonObject snapshot = observations.get(1).getAsJsonObject();
            assertFalse(row.has("runtimeHeapEffects"));
            assertEquals("MAP_ENTRY_READ",
                    observation.get("kind").getAsString());
            assertTrue(observation.get("complete").getAsBoolean());
            assertEquals(1L, observation.get("eventSequence").getAsLong());
            assertEquals("FINITE_MAP_ENTRY_SNAPSHOT",
                    snapshot.get("kind").getAsString());
            assertTrue(snapshot.get("complete").getAsBoolean());
            assertFalse(snapshot.has("preRemove"));
            assertEquals(1, snapshot.get("entryCount").getAsInt());
            assertEquals("java.util.HashMap", snapshot.get(
                    "mapImplementationClass").getAsString());
            assertEquals(observation.get("backingMapObjectToken").getAsLong(),
                    snapshot.get("backingMapObjectToken").getAsLong());
            assertEquals("ACT.OBSERVE.BACKED.VIEW",
                    snapshot.get("objectTokenScope").getAsString());
            assertEquals(1L, snapshot.get("eventSequence").getAsLong());
            assertEquals("SAME_ITERATOR_NEXT_AS_MAP_ENTRY_READ",
                    snapshot.get("eventSequenceAuthority").getAsString());
            assertEquals("Y_L_expired", snapshot.getAsJsonArray(
                    "keyExpressions").get(0).getAsJsonObject()
                    .get("_exp").getAsString());
            assertEquals(1, snapshot.getAsJsonArray("valueObjectTokens")
                    .size());
            assertEquals(1, snapshot.getAsJsonArray("valueExpressions")
                    .size());
            assertTrue(snapshot.get("keysDistinct").getAsBoolean());
            assertTrue(snapshot.get("sizeStable").getAsBoolean());
            assertTrue(snapshot.get("entrySetStable").getAsBoolean());
            assertTrue(snapshot.get("firstIteratorEntryMatched")
                    .getAsBoolean());
            assertTrue(snapshot.get("authority").getAsString().contains(
                    "AT_ITERATOR_NEXT_STABLE_SIZE"));
            assertEquals("value", manager.allKeys.get("expired"));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void recordsEntryReadAndDeepFieldOwner()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void retain()>";
        String owner = ExpiringValue.class.getName();
        String expiryField = "<" + owner + ": long expiry>";
        JsonObject fieldAction = new JsonObject();
        fieldAction.addProperty("symbol", "REGION.TEST.in.expiry");
        fieldAction.addProperty("cell", expiryField);
        fieldAction.addProperty("field", expiryField);
        fieldAction.addProperty("location", "HEAP_OBJECT_FIELD");
        fieldAction.addProperty("bindingMode", "FIELD_ACCESS");
        fieldAction.addProperty("accessOwnerClass", owner);
        fieldAction.addProperty("accessField", "expiry");
        fieldAction.addProperty("leafOwnerClass", owner);
        fieldAction.addProperty("leafField", "expiry");
        fieldAction.add("fieldPath",
                JsonParser.parseString("[\"expiry\"]"));
        JsonObject activation = concreteActivation(
                "ACT.OBSERVE.BACKED.VIEW.READ", root, 1);
        addExecutableActions(activation, singleton(fieldAction));
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            Manager manager = new Manager();
            Object key = Integer.valueOf(7004);
            ExpiringValue value = new ExpiringValue(17L);
            manager.allKeys.put(key, value);
            long token = ConcolicRegionRuntime.enterRegion(root, manager);
            assertTrue(token > 0L);
            Object view = manager.allKeys.entrySet();
            ConcolicRegionRuntime.registerMapView(root, 3, manager.allKeys,
                    view, "ENTRY_SET");
            java.util.Iterator<?> iterator =
                    ((java.util.Set<?>) view).iterator();
            ConcolicRegionRuntime.registerMapViewIterator(root, 4, view,
                    iterator);
            Object entry = iterator.next();
            ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                    entry);
            ConcolicRegionRuntime.materializeField(root, 6, value,
                    expiryField, "expiry");
            assertTrue(ConcolicRegionRuntime.resolveBranch(0L, 0L, root, 7,
                    "expiry >= now", true));
            // Entry observation is read-only; the backing map remains intact.
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = JsonParser.parseString(new String(
                    Files.readAllBytes(results), StandardCharsets.UTF_8)
                    .trim()).getAsJsonObject();
            assertFalse(row.has("runtimeHeapEffects"));
            JsonArray observations = row.getAsJsonArray(
                    "runtimeHeapObservations");
            assertEquals(2, observations.size());
            JsonObject observation = observations.get(0).getAsJsonObject();
            assertEquals("MAP_ENTRY_READ",
                    observation.get("kind").getAsString());
            assertEquals("ENTRY_SET",
                    observation.get("viewKind").getAsString());
            assertEquals("MAP_ENTRY_READ:" + root + "#u5#1",
                    observation.get("observationId").getAsString());
            assertEquals(1, observation.get("occurrence").getAsInt());
            assertEquals(1L, observation.get("eventSequence").getAsLong());
            assertEquals(0, observation.get("pcBoundary").getAsInt());
            assertTrue(observation.get("entryBindingComplete")
                    .getAsBoolean());
            assertTrue(observation.get("expressionBindingComplete")
                    .getAsBoolean());
            assertTrue(observation.get("complete").getAsBoolean());
            assertTrue(observation.has("mapExpression"));
            assertTrue(observation.has("keyExpression"));
            assertTrue(observation.has("valueExpression"));
            assertTrue(observation.has("entryExpression"));
            JsonObject snapshot = observations.get(1).getAsJsonObject();
            assertEquals("FINITE_MAP_ENTRY_SNAPSHOT",
                    snapshot.get("kind").getAsString());
            assertEquals(1, snapshot.get("entryCount").getAsInt());
            assertTrue(snapshot.get("complete").getAsBoolean());

            long mapToken = observation.get("backingMapObjectToken")
                    .getAsLong();
            long keyToken = observation.get("keyObjectToken").getAsLong();
            long valueToken = observation.get("valueObjectToken").getAsLong();
            long entryToken = observation.get("entryObjectToken").getAsLong();
            assertTrue(mapToken > 0L && keyToken > 0L
                    && valueToken > 0L && entryToken > 0L);
            assertTrue(mapToken != keyToken && mapToken != valueToken
                    && mapToken != entryToken && keyToken != valueToken
                    && keyToken != entryToken && valueToken != entryToken);

            JsonObject fieldObservation = row.getAsJsonArray(
                    "fieldObservations").get(0).getAsJsonObject();
            assertTrue(fieldObservation.get("available").getAsBoolean());
            assertEquals(valueToken, fieldObservation.get(
                    "accessOwnerObjectToken").getAsLong());
            assertEquals(valueToken, fieldObservation.get(
                    "leafOwnerObjectToken").getAsLong());
            assertTrue(fieldObservation.get("valueObjectToken").getAsLong()
                    > 0L);
            JsonObject finalObservation = row.getAsJsonArray(
                    "finalFieldObservations").get(0).getAsJsonObject();
            assertEquals(valueToken, finalObservation.get(
                    "leafOwnerObjectToken").getAsLong());
            assertSame(value, manager.allKeys.get(key));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void refreshesDelayedEntryValueExpressionAfterFieldSymbolization()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void retainSymbolic()>";
        String owner = ExpiringValue.class.getName();
        String expiryField = "<" + owner + ": long expiry>";
        JsonObject fieldAction = new JsonObject();
        fieldAction.addProperty("symbol", "REGION.TEST.in.expiry");
        fieldAction.addProperty("cell", expiryField);
        fieldAction.addProperty("field", expiryField);
        fieldAction.addProperty("location", "HEAP_OBJECT_FIELD");
        fieldAction.addProperty("bindingMode", "FIELD_ACCESS");
        fieldAction.addProperty("accessOwnerClass", owner);
        fieldAction.addProperty("accessField", "expiry");
        fieldAction.addProperty("leafOwnerClass", owner);
        fieldAction.addProperty("leafField", "expiry");
        fieldAction.add("fieldPath",
                JsonParser.parseString("[\"expiry\"]"));
        JsonObject activation = concreteActivation(
                "ACT.SYMBOLIC.DELAYED.VALUE", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(fieldAction));
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            Manager manager = new Manager();
            Integer key = Integer.valueOf(7004);
            ExpiringValue value = new ExpiringValue(23L);
            manager.allKeys.put(key, value);
            long token = ConcolicRegionRuntime.enterRegion(root, manager);
            assertTrue(token > 0L);
            Object view = manager.allKeys.entrySet();
            ConcolicRegionRuntime.registerMapView(root, 3, manager.allKeys,
                    view, "ENTRY_SET");
            java.util.Iterator<?> iterator =
                    ((java.util.Set<?>) view).iterator();
            ConcolicRegionRuntime.registerMapViewIterator(root, 4, view,
                    iterator);
            Object entry = iterator.next();
            ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                    entry);
            assertEquals("next() must observe the value before its field is "
                            + "symbolized", 1,
                    DelayedExpressionEngine.valueExpressionCalls);

            ConcolicRegionRuntime.materializeField(root, 6, value,
                    expiryField, "expiry");
            assertEquals("field symbolization must refresh the same entry "
                            + "value expression", 2,
                    DelayedExpressionEngine.valueExpressionCalls);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = JsonParser.parseString(new String(
                    Files.readAllBytes(results), StandardCharsets.UTF_8)
                    .trim()).getAsJsonObject();
            assertFalse(row.has("runtimeHeapEffects"));
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
            JsonObject observation = row.getAsJsonArray(
                    "runtimeHeapObservations").get(0).getAsJsonObject();
            assertTrue(observation.get("complete").getAsBoolean());
            assertTrue(observation.get("valueExpressionResolvedAfterRefresh")
                    .getAsBoolean());
            assertEquals("AFTER_MATCHED_FIELD_SYMBOLIZATION",
                    observation.get("valueExpressionAuthority").getAsString());
            assertEquals("AFTER_MATCHED_FIELD_SYMBOLIZATION",
                    observation.get("lastRefreshAuthority").getAsString());
            assertEquals(2, observation.get("refreshCount").getAsInt());
            assertEquals("CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT",
                    observation.get("keyExpressionAuthority").getAsString());
            assertEquals("ConstExpr", observation.getAsJsonObject(
                    "keyExpression").get("_type").getAsString());
            assertEquals("SymbolExpression", observation.getAsJsonObject(
                    "valueExpression").get("_type").getAsString());
            assertFalse("Map.Entry wrapper expression is optional",
                    observation.get("entryExpressionAvailable").getAsBoolean());
            String dynamic = ConcolicRegionRuntime
                    .dynamicFieldSymbolForTests("REGION.TEST.in.expiry",
                            root + "#u6", 1);
            assertEquals(dynamic, observation.getAsJsonArray(
                    "fieldSymbols").get(0).getAsString());
            assertEquals("DYNAMIC_FIELD:" + dynamic,
                    observation.get("dynamicBindingId").getAsString());
            JsonObject fieldObservation = row.getAsJsonArray(
                    "fieldObservations").get(0).getAsJsonObject();
            assertEquals(observation.get("valueObjectToken").getAsLong(),
                    fieldObservation.get("leafOwnerObjectToken").getAsLong());
            assertEquals(observation.get("observationId").getAsString(),
                    fieldObservation.getAsJsonArray(
                            "entryReadObservationIds").get(0).getAsString());
            assertSame(value, manager.allKeys.get(key));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void tokenScopedMapWitnessKeepsDeepEntryBindingExact()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void retainDeepSymbolic()>";
        String base = "REGION.TEST.in.enabled";
        JsonObject activation = concreteActivation(
                "ACT.MAP.REF.WITNESS", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(
                deepEnabledFieldAction(base)));
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            ExpiringValue value = new ExpiringValue(23L);
            java.util.LinkedHashMap<Integer, ExpiringValue> map =
                    new java.util.LinkedHashMap<>();
            map.put(7004, value);
            long token = ConcolicRegionRuntime.enterRegion(root, map);
            assertTrue(token > 0L);
            DelayedExpressionEngine.mapExpressionsAvailable = false;
            Object view = map.entrySet();
            ConcolicRegionRuntime.registerMapView(root, 3, map, view,
                    "ENTRY_SET");
            java.util.Iterator<?> iterator =
                    ((java.util.Set<?>) view).iterator();
            ConcolicRegionRuntime.registerMapViewIterator(root, 4, view,
                    iterator);
            Object entry = iterator.next();
            ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                    entry);
            ConcolicRegionRuntime.materializeField(root, 6, value,
                    deepStateFieldSignature(), "state");
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
            JsonObject observation = row.getAsJsonArray(
                    "runtimeHeapObservations").get(0).getAsJsonObject();
            assertTrue(observation.get("complete").getAsBoolean());
            assertEquals("ACTIVATION_LOCAL_MAP_OBJECT_TOKEN_REF_WITNESS_V1",
                    observation.get("expressionAuthority").getAsString());
            assertEquals(observation.get("backingMapObjectToken").getAsLong(),
                    observation.get("mapExpressionWitnessObjectToken")
                            .getAsLong());
            assertEquals("ACT.MAP.REF.WITNESS", observation.get(
                    "mapExpressionWitnessObjectTokenScope").getAsString());

            JsonObject binding = row.getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject();
            JsonObject field = row.getAsJsonArray(
                    "fieldObservations").get(0).getAsJsonObject();
            assertTrue(binding.get("complete").getAsBoolean());
            assertEquals(observation.get("valueObjectToken").getAsLong(),
                    binding.get("entryValueOwnerObjectToken").getAsLong());
            assertEquals(binding.get("entryValueOwnerObjectToken").getAsLong(),
                    field.get("accessOwnerObjectToken").getAsLong());
            assertEquals(binding.get("leafOwnerObjectToken").getAsLong(),
                    field.get("leafOwnerObjectToken").getAsLong());
            assertTrue(binding.get("entryValueOwnerObjectToken").getAsLong()
                    != binding.get("leafOwnerObjectToken").getAsLong());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void mapEntryFieldsUseIndependentDynamicSymbolsAndOccurrenceModel()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void dynamicEntries()>";
        String base = "REGION.TEST.in.expiry";
        JsonObject action = expiryFieldAction(base);
        String site = root + "#u6";
        String dynamicTwo = ConcolicRegionRuntime.dynamicFieldSymbolForTests(
                base, site, 2);
        JsonObject assignment = dynamicAssignment(base, dynamicTwo, site, 2,
                "91");
        String engineSymbol = "M_J_field_" + dynamicTwo
                + "_" + ExpiringValue.class.getName().replace('.', '/');
        assignment.addProperty("engineSymbol", engineSymbol);
        assignment.addProperty("solverSymbol",
                z3SolverSymbolForTest(engineSymbol));
        assignment.addProperty("entryReadObservationId",
                "MAP_ENTRY_READ:" + root + "#u5#2");
        assignment.add("expectedEntryKey",
                ConcolicRegionRuntime.immutableEntryKeyExpression(2));
        assignment.addProperty("expectedEntryKeyAuthority",
                "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        JsonObject activation = concreteActivation(
                "ACT.MODEL.DYNAMIC.ENTRIES", root, 1);
        addExecutableActions(activation, singleton(action));
        activation.add("modelAssignments", singleton(assignment));
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "concrete-model-test");
        try {
            java.util.LinkedHashMap<Integer, ExpiringValue> map =
                    new java.util.LinkedHashMap<>();
            ExpiringValue first = new ExpiringValue(11L);
            ExpiringValue second = new ExpiringValue(22L);
            map.put(1, first);
            map.put(2, second);
            long token = ConcolicRegionRuntime.enterRegion(root, map);
            assertTrue(token > 0L);
            Object view = map.entrySet();
            ConcolicRegionRuntime.registerMapView(root, 3, map, view,
                    "ENTRY_SET");
            java.util.Iterator<?> iterator =
                    ((java.util.Set<?>) view).iterator();
            ConcolicRegionRuntime.registerMapViewIterator(root, 4, view,
                    iterator);
            Object firstEntry = iterator.next();
            ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                    firstEntry);
            ConcolicRegionRuntime.materializeField(root, 6, first,
                    expiryFieldSignature(), "expiry");
            Object secondEntry = iterator.next();
            ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                    secondEntry);
            ConcolicRegionRuntime.materializeField(root, 6, second,
                    expiryFieldSignature(), "expiry");
            assertEquals(11L, first.expiry);
            assertEquals(91L, second.expiry);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            JsonArray bindings = row.getAsJsonArray("dynamicFieldBindings");
            assertEquals(2, bindings.size());
            JsonObject one = bindings.get(0).getAsJsonObject();
            JsonObject two = bindings.get(1).getAsJsonObject();
            String dynamicOne = ConcolicRegionRuntime
                    .dynamicFieldSymbolForTests(base, site, 1);
            assertEquals(1, one.get("materializationOccurrence").getAsInt());
            assertEquals(2, two.get("materializationOccurrence").getAsInt());
            assertEquals(dynamicOne,
                    one.get("dynamicFieldSymbol").getAsString());
            assertFalse(one.get("dynamicFieldSymbol").getAsString().equals(
                    two.get("dynamicFieldSymbol").getAsString()));
            assertEquals(dynamicTwo,
                    two.get("dynamicFieldSymbol").getAsString());
            assertTrue(one.get("complete").getAsBoolean());
            assertTrue(two.get("complete").getAsBoolean());
            assertEquals(1, row.getAsJsonArray(
                    "modelAssignmentsApplied").size());
            JsonObject applied = row.getAsJsonArray(
                    "modelAssignmentsApplied").get(0).getAsJsonObject();
            assertEquals("DYNAMIC_FIELD:" + dynamicTwo,
                    applied.get("dynamicBindingId").getAsString());
            assertEquals(base,
                    applied.get("baseInputSymbol").getAsString());
            assertEquals(2,
                    applied.get("materializationOccurrence").getAsInt());
            assertFalse("occurrence one must not inherit occurrence two's "
                            + "solver assignment",
                    ("DYNAMIC_FIELD:" + dynamicOne).equals(
                            applied.get("dynamicBindingId").getAsString()));
            assertEquals("INT", applied.get("valueType").getAsString());
            assertEquals("Z3_PATH_FLIP_MODEL",
                    applied.get("authority").getAsString());
            assertTrue(applied.get("materializeAtRealDefinition")
                    .getAsBoolean());
            assertFalse("runtime evidence must not invent a solver term",
                    applied.has("solverSymbol"));
            assertEquals(dynamicTwo, row.getAsJsonArray("fieldObservations")
                    .get(1).getAsJsonObject().get("symbol").getAsString());
            assertEquals("DYNAMIC_FIELD:" + dynamicTwo,
                    row.getAsJsonArray("runtimeHeapObservations").get(1)
                            .getAsJsonObject().get("dynamicBindingId")
                            .getAsString());

            // The real Runtime serialization, including baseInputSymbol and
            // the capture-time immutable-key selector, must be admitted by
            // the replay validator after an ordinary observed branch.
            JsonObject validationTask = new JsonObject();
            validationTask.addProperty("queryKey", "Q.DYNAMIC.RUNTIME");
            validationTask.addProperty("regionId", "REGION.TEST");
            validationTask.add("captureGoal",
                    RegionCaptureGoal.targetBranch().toJson());
            JsonObject desiredPredicate = testIntegerPredicate("==");
            JsonObject event = new JsonObject();
            event.addProperty("eventId", 1L);
            event.addProperty("contextId", 1L);
            BranchWitness sourceWitness = BranchWitness.vmPc("SITE.FLIP",
                    "<test.Runtime: void run()>", 1, 1, false,
                    BranchPredicateAlgebra.complement(desiredPredicate), 0,
                    event);
            validationTask.add("replayContract",
                    BranchReplayContract.flip(
                            Collections.<BranchWitness>emptyList(),
                            sourceWitness).toJson());
            validationTask.add("modelAssignments",
                    singleton(assignment.deepCopy()));
            JsonObject validationRaw = row.deepCopy();
            JsonObject mapping = new JsonObject();
            mapping.addProperty("siteId", "SITE.FLIP");
            mapping.addProperty("occurrence", 1);
            mapping.addProperty("observedOutcome", true);
            mapping.addProperty("overrideApplied", false);
            mapping.add("witness", BranchWitness.vmPc("SITE.FLIP",
                    "<test.Runtime: void run()>", 1, 1, true,
                    desiredPredicate, 0, event).toJson());
            validationRaw.add("branchMappings", singleton(mapping));
            JsonObject validation = ConcolicReplayValidator.validate(
                    validationTask, validationRaw);
            assertTrue(validation.toString(), validation.get("valid")
                    .getAsBoolean());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void oneStaticExpiryPortExpandsToFourEntrySpecificSymbols()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void fourEntries()>";
        String base = "REGION.TEST.in.expiry";
        String site = root + "#u6";
        JsonObject activation = concreteActivation(
                "ACT.OBSERVE.FOUR.DYNAMIC.ENTRIES", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(
                deepEnabledFieldAction(base)));
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            java.util.LinkedHashMap<Integer, ExpiringValue> map =
                    new java.util.LinkedHashMap<>();
            ExpiringValue[] values = new ExpiringValue[4];
            for (int index = 0; index < values.length; index++) {
                values[index] = new ExpiringValue(100L + index);
                map.put(7000 + index, values[index]);
            }

            long token = ConcolicRegionRuntime.enterRegion(root, map);
            assertTrue(token > 0L);
            Object view = map.entrySet();
            ConcolicRegionRuntime.registerMapView(root, 3, map, view,
                    "ENTRY_SET");
            java.util.Iterator<?> iterator =
                    ((java.util.Set<?>) view).iterator();
            ConcolicRegionRuntime.registerMapViewIterator(root, 4, view,
                    iterator);
            for (int index = 0; index < values.length; index++) {
                Object entry = iterator.next();
                ConcolicRegionRuntime.recordMapIteratorNext(root, 5,
                        iterator, entry);
                ConcolicRegionRuntime.materializeField(root, 6,
                        values[index], deepStateFieldSignature(), "state");
            }
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            JsonArray bindings = row.getAsJsonArray("dynamicFieldBindings");
            JsonArray entries = row.getAsJsonArray(
                    "runtimeHeapObservations");
            assertEquals(4, bindings.size());
            assertEquals(5, entries.size());
            assertEquals(4, row.getAsJsonArray("fieldObservations").size());
            assertEquals(4, row.getAsJsonArray(
                    "finalFieldObservations").size());
            assertEquals(4, row.getAsJsonArray("symbolizedInputs").size());
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());

            for (int index = 0; index < bindings.size(); index++) {
                int occurrence = index + 1;
                String dynamic = ConcolicRegionRuntime
                        .dynamicFieldSymbolForTests(base, site, occurrence);
                JsonObject binding = bindings.get(index).getAsJsonObject();
                JsonObject entry = entries.get(index).getAsJsonObject();
                assertEquals(base,
                        binding.get("baseInputSymbol").getAsString());
                assertEquals(occurrence, binding.get(
                        "materializationOccurrence").getAsInt());
                assertEquals(dynamic,
                        binding.get("dynamicFieldSymbol").getAsString());
                assertTrue(binding.get("complete").getAsBoolean());
                assertEquals("MAP_ENTRY_READ:" + root + "#u5#"
                                + occurrence,
                        binding.get("entryReadObservationId").getAsString());
                assertEquals("DYNAMIC_FIELD:" + dynamic,
                        entry.get("dynamicBindingId").getAsString());
                assertEquals(JsonParser.parseString(
                                "[\"state\",\"guard\",\"enabled\"]"),
                        binding.get("fieldPath"));
                assertEquals(deepEnabledFieldSignature(),
                        binding.get("fieldSignature").getAsString());
                assertEquals("Y_I_" + (7000 + index),
                        entry.getAsJsonObject("keyExpression")
                                .get("_exp").getAsString());
                assertFalse(DelayedExpressionEngine
                        .SYMBOLIC_FIELD_PREFIXES.containsKey(values[index]));
                assertFalse(DelayedExpressionEngine
                        .SYMBOLIC_FIELD_PREFIXES.containsKey(
                        values[index].state));
                assertEquals(dynamic, DelayedExpressionEngine
                        .SYMBOLIC_FIELD_PREFIXES.get(
                        values[index].state.guard));
            }
            JsonObject snapshot = entries.get(4).getAsJsonObject();
            assertEquals("FINITE_MAP_ENTRY_SNAPSHOT",
                    snapshot.get("kind").getAsString());
            assertEquals(4, snapshot.get("entryCount").getAsInt());
            assertEquals(4, snapshot.getAsJsonArray("keyExpressions")
                    .size());
            assertEquals(4, snapshot.getAsJsonArray("valueObjectTokens")
                    .size());
            assertTrue(snapshot.get("complete").getAsBoolean());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void repeatedReadOfSameEntryOwnerReusesFirstDynamicBinding()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void rereadEntry()>";
        JsonObject activation = concreteActivation(
                "ACT.OBSERVE.DYNAMIC.REREAD", root, 1);
        addExecutableActions(activation, singleton(expiryFieldAction(
                "REGION.TEST.in.expiry")));
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            java.util.LinkedHashMap<Integer, ExpiringValue> map =
                    new java.util.LinkedHashMap<>();
            ExpiringValue value = new ExpiringValue(17L);
            map.put(7, value);
            long token = ConcolicRegionRuntime.enterRegion(root, map);
            Object view = map.entrySet();
            ConcolicRegionRuntime.registerMapView(root, 3, map, view,
                    "ENTRY_SET");
            java.util.Iterator<?> iterator =
                    ((java.util.Set<?>) view).iterator();
            ConcolicRegionRuntime.registerMapViewIterator(root, 4, view,
                    iterator);
            Object entry = iterator.next();
            ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                    entry);
            ConcolicRegionRuntime.materializeField(root, 6, value,
                    expiryFieldSignature(), "expiry");
            ConcolicRegionRuntime.materializeField(root, 6, value,
                    expiryFieldSignature(), "expiry");
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(1, row.getAsJsonArray(
                    "dynamicFieldBindings").size());
            assertEquals(1, row.getAsJsonArray("fieldObservations").size());
            assertEquals(1, row.getAsJsonArray(
                    "finalFieldObservations").size());
            assertEquals(1, row.getAsJsonArray("dynamicFieldBindings").get(0)
                    .getAsJsonObject().get("materializationOccurrence")
                    .getAsInt());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void dynamicAssignmentKeyAndOccurrenceMismatchFailClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void rejectSelector()>";
        String base = "REGION.TEST.in.expiry";
        String site = root + "#u6";
        String dynamicOne = ConcolicRegionRuntime.dynamicFieldSymbolForTests(
                base, site, 1);
        JsonObject wrongKey = dynamicAssignment(base, dynamicOne, site, 1,
                "81");
        wrongKey.add("expectedEntryKey", concreteIntegerExpression(999));
        wrongKey.addProperty("expectedEntryKeyAuthority",
                "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT");
        String dynamicTwo = ConcolicRegionRuntime.dynamicFieldSymbolForTests(
                base, site, 2);
        JsonObject wrongOccurrence = dynamicAssignment(base, dynamicTwo,
                site, 2, "82");
        JsonArray assignments = new JsonArray();
        assignments.add(wrongKey);
        assignments.add(wrongOccurrence);
        JsonObject activation = concreteActivation(
                "ACT.MODEL.DYNAMIC.REJECT", root, 1);
        addExecutableActions(activation, singleton(expiryFieldAction(base)));
        activation.add("modelAssignments", assignments);
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "concrete-model-test");
        try {
            java.util.LinkedHashMap<Integer, ExpiringValue> map =
                    new java.util.LinkedHashMap<>();
            ExpiringValue value = new ExpiringValue(31L);
            map.put(7, value);
            long token = ConcolicRegionRuntime.enterRegion(root, map);
            Object view = map.entrySet();
            ConcolicRegionRuntime.registerMapView(root, 3, map, view,
                    "ENTRY_SET");
            java.util.Iterator<?> iterator =
                    ((java.util.Set<?>) view).iterator();
            ConcolicRegionRuntime.registerMapViewIterator(root, 4, view,
                    iterator);
            Object entry = iterator.next();
            ConcolicRegionRuntime.recordMapIteratorNext(root, 5, iterator,
                    entry);
            ConcolicRegionRuntime.materializeField(root, 6, value,
                    expiryFieldSignature(), "expiry");
            assertEquals(31L, value.expiry);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray(
                    "modelAssignmentsApplied").size());
            assertFalse(row.get("allModelAssignmentsApplied").getAsBoolean());
            assertTrue(row.getAsJsonArray("unresolvedInputs").toString()
                    .contains("expected entry key selector mismatch"));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void replayUsesStableSiteOccurrenceNotActivationLocalObjectToken()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void replayStableEntry()>";
        String base = "REGION.TEST.in.expiry";
        JsonObject firstActivation = concreteActivation(
                "ACT.OBSERVE.STABLE.1", root, 1);
        JsonObject secondActivation = concreteActivation(
                "ACT.OBSERVE.STABLE.2", root, 2);
        addExecutableActions(firstActivation,
                singleton(expiryFieldAction(base)));
        addExecutableActions(secondActivation,
                singleton(expiryFieldAction(base)));
        Files.write(plan, (firstActivation + "\n" + secondActivation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            java.util.LinkedHashMap<Integer, ExpiringValue> firstMap =
                    new java.util.LinkedHashMap<>();
            ExpiringValue firstValue = new ExpiringValue(41L);
            firstMap.put(7, firstValue);
            runEntryFieldActivation(root, firstMap, firstValue, false);

            java.util.LinkedHashMap<Integer, ExpiringValue> secondMap =
                    new java.util.LinkedHashMap<>();
            secondMap.put(99, new ExpiringValue(1L));
            ExpiringValue secondValue = new ExpiringValue(42L);
            secondMap.put(7, secondValue);
            runEntryFieldActivation(root, secondMap, secondValue, true);

            List<JsonObject> rows = resultRows(results);
            assertEquals(2, rows.size());
            JsonObject first = rows.get(0).getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject();
            JsonObject second = rows.get(1).getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject();
            assertEquals(first.get("dynamicFieldSymbol").getAsString(),
                    second.get("dynamicFieldSymbol").getAsString());
            assertEquals(1,
                    first.get("materializationOccurrence").getAsInt());
            assertEquals(1,
                    second.get("materializationOccurrence").getAsInt());
            assertFalse(first.get("leafOwnerObjectToken").getAsLong()
                    == second.get("leafOwnerObjectToken").getAsLong());
            assertEquals("ACT.OBSERVE.STABLE.1",
                    first.get("objectTokenScope").getAsString());
            assertEquals("ACT.OBSERVE.STABLE.2",
                    second.get("objectTokenScope").getAsString());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void freshReplayRebindsStaticOccurrenceAfterEntryKeyChanges()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Pruner: void replayFreshEntryKey()>";
        String base = "REGION.TEST.in.expiry";
        String site = root + "#u6";
        String dynamic = ConcolicRegionRuntime.dynamicFieldSymbolForTests(
                base, site, 1);

        JsonObject seed = concreteActivation(
                "ACT.OBSERVE.FRESH.KEY.SEED", root, 1);
        addExecutableActions(seed, singleton(expiryFieldAction(base)));
        JsonObject replay = concreteActivation(
                "ACT.OBSERVE.FRESH.KEY.REPLAY", root, 2);
        addExecutableActions(replay, singleton(expiryFieldAction(base)));
        JsonObject assignment = dynamicAssignment(base, dynamic, site, 1,
                "91");
        assignment.addProperty("dynamicReplayRebindingAuthority",
                "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                        + "FRESH_ENTRY_REBIND_V1");
        assignment.addProperty("sourceEntrySelectorRetained", false);
        replay.add("modelAssignments", singleton(assignment));
        Files.write(plan, (seed + "\n" + replay + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "concrete-overlap-test");
        try {
            java.util.LinkedHashMap<Integer, ExpiringValue> seedMap =
                    new java.util.LinkedHashMap<>();
            ExpiringValue seedValue = new ExpiringValue(41L);
            seedMap.put(7, seedValue);
            runEntryFieldActivation(root, seedMap, seedValue, false);

            java.util.LinkedHashMap<Integer, ExpiringValue> freshMap =
                    new java.util.LinkedHashMap<>();
            ExpiringValue freshValue = new ExpiringValue(42L);
            freshMap.put(99, freshValue);
            runEntryFieldActivation(root, freshMap, freshValue, false);

            assertEquals(91L, freshValue.expiry);
            List<JsonObject> rows = resultRows(results);
            assertEquals(2, rows.size());
            JsonObject seedBinding = rows.get(0).getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject();
            JsonObject freshBinding = rows.get(1).getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject();
            JsonObject seedObservation = rows.get(0).getAsJsonArray(
                    "runtimeHeapObservations").get(0).getAsJsonObject();
            JsonObject freshObservation = rows.get(1).getAsJsonArray(
                    "runtimeHeapObservations").get(0).getAsJsonObject();
            assertEquals(7, seedObservation.getAsJsonObject(
                    "keyExpression").get("value").getAsInt());
            assertEquals(99, freshObservation.getAsJsonObject(
                    "keyExpression").get("value").getAsInt());
            JsonObject applied = rows.get(1).getAsJsonArray(
                    "modelAssignmentsApplied").get(0).getAsJsonObject();
            assertFalse(applied.has("expectedEntryKey"));
            assertFalse(applied.get("sourceEntrySelectorRetained")
                    .getAsBoolean());
            assertFalse(applied.get("sameSeedEntryClaimed").getAsBoolean());
            assertTrue(applied.get("freshEntrySelectorCaptured")
                    .getAsBoolean());
            assertEquals(99, applied.getAsJsonObject(
                    "keyExpression").get("value").getAsInt());
            assertEquals(freshBinding.get("entryReadObservationId"),
                    applied.get("entryReadObservationId"));
            assertTrue(rows.get(1).get("allModelAssignmentsApplied")
                    .getAsBoolean());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void discoversArrayElementOwnersWithoutFoldingStaticFieldAction()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void discoverArrayFields()>";
        String base = "REGION.TEST.in.elementId";
        String container = "REGION.TEST.in.elements";
        JsonObject activation = concreteActivation(
                "ACT.DISCOVER.ARRAY.FIELD", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, genericArrayActions(base, container,
                root));
        activation.add("containerElementFieldBindings", singleton(
                genericArrayBinding("BIND.DISCOVER", base, container,
                        "DISCOVER_UNIQUE_IDENTITY_INDEX", -1, -1,
                        root + "#u6")));
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            GenericArrayEnvelope envelope = new GenericArrayEnvelope(4);
            runGenericArrayActivation(root, envelope,
                    Arrays.asList(envelope.elements));

            JsonObject row = resultRows(results).get(0);
            assertEquals(row.getAsJsonArray("unresolvedInputs").toString(),
                    0, row.getAsJsonArray("unresolvedInputs").size());
            JsonArray bindings = row.getAsJsonArray("dynamicFieldBindings");
            assertEquals(4, bindings.size());
            assertEquals(5, row.getAsJsonArray("symbolizedInputs").size());
            for (int index = 0; index < 4; index++) {
                JsonObject binding = bindings.get(index).getAsJsonObject();
                assertEquals(2, binding.get("schemaVersion").getAsInt());
                assertEquals("DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING",
                        binding.get("kind").getAsString());
                assertEquals(index + 1, binding.get(
                        "materializationOccurrence").getAsInt());
                JsonObject selector = binding.getAsJsonObject(
                        "containerSelector");
                assertEquals(index, selector.get("elementIndex").getAsInt());
                assertEquals(index + 1, selector.get(
                        "elementOccurrence").getAsInt());
                assertEquals("EXACT_ARRAY_INDEX", selector.get(
                        "selectorAuthority").getAsString());
                assertEquals("DISCOVER_UNIQUE_IDENTITY_INDEX", selector.get(
                        "resolvedFromSelectorAuthority").getAsString());
                assertTrue(selector.get("complete").getAsBoolean());
                String dynamic = ConcolicRegionRuntime
                        .dynamicFieldSymbolForTests(base, root + "#u6",
                                index + 1);
                assertEquals(dynamic,
                        binding.get("dynamicFieldSymbol").getAsString());
                assertEquals(dynamic, DelayedExpressionEngine
                        .SYMBOLIC_FIELD_PREFIXES.get(
                                envelope.elements[index]));
            }
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void materializesNestedArrayPutValueLeafFromContainerSnapshot()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void snapshotArrayValueFields()>";
        String base = "REGION.TEST.in.elementExpiry";
        String container = "REGION.TEST.in.elements";
        JsonObject activation = concreteActivation(
                "ACT.SNAPSHOT.ARRAY.VALUE.FIELD", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);

        JsonArray actions = genericArrayActions(base, container, root);
        JsonObject containerAction = actions.get(0).getAsJsonObject();
        containerAction.addProperty("bindingMode",
                "CONTAINER_INPUT_OBSERVATION");
        containerAction.addProperty("arrayFieldObservationOnly", true);
        containerAction.addProperty("containerObservationAuthority",
                "FIRST_MATCHING_CONTAINER_INSTANCE_APPROXIMATION_V1");
        JsonObject leafAction = actions.get(1).getAsJsonObject();
        leafAction.addProperty("cell", metadataExpiryFieldSignature());
        leafAction.addProperty("field", metadataExpiryFieldSignature());
        leafAction.addProperty("accessOwnerClass", Metadata.class.getName());
        leafAction.addProperty("accessField", "expiry");
        leafAction.addProperty("leafOwnerClass", Metadata.class.getName());
        leafAction.addProperty("leafField", "expiry");
        leafAction.add("fieldPath",
                JsonParser.parseString("[\"metadata\",\"expiry\"]"));
        activation.add("symbolize", actions);
        // Scheduler keeps the leaf in the declaration catalog but executes
        // only the container observation; the snapshot creates the leaf's
        // dynamic action after selecting the exact element identity.
        activation.add("materializations", singleton(
                containerAction.deepCopy()));

        JsonObject binding = genericArrayBinding("BIND.SNAPSHOT", base,
                container, "DISCOVER_UNIQUE_IDENTITY_INDEX", -1, -1,
                root + "#u18");
        binding.addProperty("schemaVersion", 2);
        binding.addProperty("materializationMode", "CONTAINER_SNAPSHOT");
        binding.add("fieldPath",
                JsonParser.parseString("[\"metadata\",\"expiry\"]"));
        binding.addProperty("declaredFieldSignature",
                metadataExpiryFieldSignature());
        binding.addProperty("declaredFieldOwnerClass",
                Metadata.class.getName());
        binding.addProperty("declaredFieldType", "long");
        activation.add("containerElementFieldBindings",
                singleton(binding));
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            GenericArrayEnvelope envelope = new GenericArrayEnvelope(4);
            GenericArrayEnvelope laterOuterLoopEnvelope =
                    new GenericArrayEnvelope(2);
            // No expiry getter/field hook is executed.  Observing the exact
            // post-getfield container snapshot must be sufficient to
            // materialize all four array-element leaf fields. Re-reading the
            // same reference is idempotent; a later distinct outer-loop
            // container is explicitly ignored by the bounded approximation.
            long token = ConcolicRegionRuntime.enterRegion(root, envelope);
            assertTrue(token > 0L);
            for (GenericArrayEnvelope observed : Arrays.asList(envelope,
                    envelope, laterOuterLoopEnvelope)) {
                ConcolicRegionRuntime.prepareFieldMaterialization(root, 2,
                        observed, genericArrayFieldSignature(), "elements");
                Current[] consumed = observed.elements;
                ConcolicRegionRuntime.materializeConsumedField(root, 2,
                        observed, genericArrayFieldSignature(), "elements",
                        consumed);
            }
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(row.getAsJsonArray("unresolvedInputs").toString(),
                    0, row.getAsJsonArray("unresolvedInputs").size());
            JsonArray dynamic = row.getAsJsonArray("dynamicFieldBindings");
            assertEquals(4, dynamic.size());
            for (int index = 0; index < dynamic.size(); index++) {
                JsonObject current = dynamic.get(index).getAsJsonObject();
                assertEquals("DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING",
                        current.get("kind").getAsString());
                JsonArray fieldPath = current.getAsJsonArray("fieldPath");
                assertEquals(2, fieldPath.size());
                assertEquals("metadata", fieldPath.get(0).getAsString());
                assertEquals("expiry", fieldPath.get(1).getAsString());
                JsonObject selector = current.getAsJsonObject(
                        "containerSelector");
                assertEquals(index,
                        selector.get("elementIndex").getAsInt());
                assertEquals(selector.get("elementObjectToken").getAsLong(),
                        current.get("materializationSiteBridgeElementObjectToken")
                                .getAsLong());
                assertTrue(selector.get("elementObjectToken").getAsLong()
                        != current.get("leafOwnerObjectToken").getAsLong());
                assertEquals("DISCOVER_UNIQUE_IDENTITY_INDEX",
                        selector.get("resolvedFromSelectorAuthority")
                                .getAsString());
                assertEquals(current.get("dynamicFieldSymbol").getAsString(),
                        DelayedExpressionEngine.SYMBOLIC_FIELD_PREFIXES.get(
                                envelope.elements[index].metadata));
            }
            for (Current ignored : laterOuterLoopEnvelope.elements) {
                assertFalse(DelayedExpressionEngine.SYMBOLIC_FIELD_PREFIXES
                        .containsKey(ignored.metadata));
            }
            JsonArray approximations = row.getAsJsonArray(
                    "runtimeApproximations");
            assertEquals(2, approximations.size());
            assertEquals("FIRST_MATCHING_CONTAINER_SELECTED",
                    approximations.get(0).getAsJsonObject().get("outcome")
                            .getAsString());
            assertEquals("LATER_DISTINCT_CONTAINER_IGNORED",
                    approximations.get(1).getAsJsonObject().get("outcome")
                            .getAsString());
            assertEquals("FIRST_MATCHING_CONTAINER_INSTANCE_"
                            + "APPROXIMATION_V1",
                    approximations.get(1).getAsJsonObject().get("authority")
                            .getAsString());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void exactArraySelectorReplaysModelOnlyToItsOwningElement()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void replayArrayFields()>";
        String base = "REGION.TEST.in.elementId";
        String container = "REGION.TEST.in.elements";
        String site = root + "#u6";
        JsonObject activation = concreteActivation(
                "ACT.MODEL.ARRAY.FIELD", root, 1);
        addExecutableActions(activation, genericArrayActions(base, container,
                root));
        JsonArray bindings = new JsonArray();
        for (int index = 0; index < 4; index++) {
            bindings.add(genericArrayBinding("BIND.EXACT." + index,
                    base, container, "EXACT_ARRAY_INDEX", index,
                    index + 1, root + "#u6"));
        }
        activation.add("containerElementFieldBindings", bindings);
        String dynamic = ConcolicRegionRuntime.dynamicFieldSymbolForTests(
                base, site, 3);
        JsonArray assignments = new JsonArray();
        assignments.add(genericArrayAssignment("BIND.EXACT.2", base,
                container, dynamic, site, 3, 2, "91"));
        String wrongDynamic = ConcolicRegionRuntime
                .dynamicFieldSymbolForTests(base, site, 4);
        assignments.add(genericArrayAssignment("BIND.EXACT.3", base,
                container, wrongDynamic, site, 4, 2, "92"));
        activation.add("modelAssignments", assignments);
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "concrete-model-test");
        try {
            GenericArrayEnvelope envelope = new GenericArrayEnvelope(4);
            runGenericArrayActivation(root, envelope,
                    Arrays.asList(envelope.elements));

            assertEquals(7, envelope.elements[0].id);
            assertEquals(7, envelope.elements[1].id);
            assertEquals(91, envelope.elements[2].id);
            assertEquals(7, envelope.elements[3].id);
            JsonObject row = resultRows(results).get(0);
            assertEquals(4, row.getAsJsonArray(
                    "dynamicFieldBindings").size());
            assertEquals(1, row.getAsJsonArray(
                    "modelAssignmentsApplied").size());
            assertFalse(row.get("allModelAssignmentsApplied").getAsBoolean());
            assertTrue(row.getAsJsonArray("unresolvedInputs").toString()
                    .contains("exact container selector mismatch"));
            JsonObject applied = row.getAsJsonArray(
                    "modelAssignmentsApplied").get(0).getAsJsonObject();
            JsonObject selector = applied.getAsJsonObject(
                    "containerSelector");
            assertEquals("BIND.EXACT.2",
                    selector.get("bindingId").getAsString());
            assertEquals(2, selector.get("elementIndex").getAsInt());
            assertEquals(3, selector.get("elementOccurrence").getAsInt());
            assertEquals("EXACT_ARRAY_INDEX",
                    selector.get("selectorAuthority").getAsString());
            assertEquals("EXACT_ARRAY_INDEX", selector.get(
                    "resolvedFromSelectorAuthority").getAsString());
            assertTrue(selector.get("containerObjectToken").getAsLong()
                    > 0L);
            assertTrue(selector.get("elementObjectToken").getAsLong()
                    > 0L);
            assertEquals("ACT.MODEL.ARRAY.FIELD",
                    selector.get("objectTokenScope").getAsString());
            assertEquals("ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN",
                    selector.get("objectTokenAuthority").getAsString());
            assertEquals("EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                            + "ACTIVATION_LOCAL_ELEMENT_IDENTITY",
                    selector.get("authority").getAsString());
            assertTrue(selector.get("complete").getAsBoolean());
            assertEquals("EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_"
                            + "LOCAL_IDENTITY_REBIND_V1",
                    applied.get("containerReplayRebindingAuthority")
                            .getAsString());
            assertFalse(applied.get("sourceContainerObjectTokensRetained")
                    .getAsBoolean());
            assertFalse(applied.get("sameSourceContainerIdentityClaimed")
                    .getAsBoolean());
            assertTrue(applied.get("currentContainerSelectorCaptured")
                    .getAsBoolean());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void identityDiscoveryFailsClosedForAbsentAndRepeatedOwner()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void rejectArrayIdentity()>";
        String base = "REGION.TEST.in.elementId";
        String container = "REGION.TEST.in.elements";
        JsonObject first = concreteActivation(
                "ACT.REJECT.ARRAY.ABSENT", root, 1);
        JsonObject second = concreteActivation(
                "ACT.REJECT.ARRAY.REPEATED", root, 2);
        for (JsonObject activation : Arrays.asList(first, second)) {
            addExecutableActions(activation, genericArrayActions(base,
                    container, root));
            activation.add("containerElementFieldBindings", singleton(
                    genericArrayBinding("BIND.DISCOVER", base, container,
                            "DISCOVER_UNIQUE_IDENTITY_INDEX", -1, -1,
                            root + "#u6")));
        }
        Files.write(plan, (first + "\n" + second + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            GenericArrayEnvelope absent = new GenericArrayEnvelope(2);
            runGenericArrayActivation(root, absent,
                    java.util.Collections.singletonList(new Current()));

            GenericArrayEnvelope repeated = new GenericArrayEnvelope(2);
            repeated.elements[1] = repeated.elements[0];
            runGenericArrayActivation(root, repeated,
                    java.util.Collections.singletonList(
                            repeated.elements[0]));

            List<JsonObject> rows = resultRows(results);
            assertEquals(2, rows.size());
            assertEquals(0, rows.get(0).getAsJsonArray(
                    "dynamicFieldBindings").size());
            assertEquals(0, rows.get(1).getAsJsonArray(
                    "dynamicFieldBindings").size());
            // The explicit container field itself is still observed; the
            // rejected element field must not add a legacy base observation.
            assertEquals(1, rows.get(0).getAsJsonArray(
                    "fieldObservations").size());
            assertEquals(1, rows.get(1).getAsJsonArray(
                    "fieldObservations").size());
            // An owner-wide hook may see an object outside this container;
            // discovery declarations have no exact index coverage promise.
            assertEquals(0, rows.get(0).getAsJsonArray(
                    "unresolvedInputs").size());
            assertTrue(rows.get(1).getAsJsonArray("unresolvedInputs")
                    .toString().contains("occurs more than once"));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void containerFieldDeclarationBridgesActualAndEffectiveSites()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void rejectArraySite()>";
        String base = "REGION.TEST.in.elementId";
        String container = "REGION.TEST.in.elements";
        JsonObject missing = concreteActivation(
                "ACT.REJECT.ARRAY.SITE.MISSING", root, 1);
        JsonObject mismatch = concreteActivation(
                "ACT.REJECT.ARRAY.SITE.MISMATCH", root, 2);
        for (JsonObject activation : Arrays.asList(missing, mismatch)) {
            addExecutableActions(activation, genericArrayActions(base,
                    container, root));
        }
        JsonObject missingBinding = genericArrayBinding("BIND.MISSING",
                base, container, "DISCOVER_UNIQUE_IDENTITY_INDEX", -1,
                -1, root + "#u6");
        missingBinding.remove("fieldMaterializationSiteId");
        missing.add("containerElementFieldBindings",
                singleton(missingBinding));
        mismatch.add("containerElementFieldBindings", singleton(
                genericArrayBinding("BIND.MISMATCH", base, container,
                        "DISCOVER_UNIQUE_IDENTITY_INDEX", -1, -1,
                        root + "#u99")));
        Files.write(plan, (missing + "\n" + mismatch + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            GenericArrayEnvelope first = new GenericArrayEnvelope(1);
            runGenericArrayActivation(root, first,
                    Collections.singletonList(first.elements[0]));
            GenericArrayEnvelope second = new GenericArrayEnvelope(1);
            runGenericArrayActivation(root, second,
                    Collections.singletonList(second.elements[0]));

            List<JsonObject> rows = resultRows(results);
            assertEquals(2, rows.size());
            assertEquals(0, rows.get(0).getAsJsonArray(
                    "dynamicFieldBindings").size());
            assertTrue(rows.get(0).getAsJsonArray("unresolvedInputs")
                    .toString().contains(
                            "field materialization site is missing"));

            assertEquals(0, rows.get(1).getAsJsonArray(
                    "unresolvedInputs").size());
            JsonObject bridged = rows.get(1).getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject();
            assertEquals(root + "#u99", bridged.get(
                    "materializationSiteId").getAsString());
            assertEquals(root + "#u6", bridged.get(
                    "actualHookSiteId").getAsString());
            assertEquals("STATIC_CONTAINER_SELECTOR_AND_ACTIVATION_LOCAL_"
                            + "EXACT_ELEMENT_IDENTITY_TO_DECLARED_FIELD_HOOK_V1",
                    bridged.get("materializationSiteBridgeAuthority")
                            .getAsString());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void exactArrayBindingsBridgeOneGetterHookToFourStaticSites()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void bridgeArrayFields()>";
        String getter = "<" + Current.class.getName() + ": int getId()>";
        String base = "REGION.TEST.in.elementId";
        String container = "REGION.TEST.in.elements";
        int[] units = new int[]{14, 20, 26, 32};
        JsonObject activation = concreteActivation(
                "ACT.BRIDGE.ARRAY.FIELD", root, 1);
        addExecutableActions(activation, genericArrayActions(base, container,
                root));
        JsonArray declarations = new JsonArray();
        for (int index = 0; index < units.length; index++) {
            declarations.add(genericArrayBinding("BIND.EXACT." + index,
                    base, container, "EXACT_ARRAY_INDEX", index, 1,
                    root + "#u" + units[index]));
        }
        activation.add("containerElementFieldBindings", declarations);
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            GenericArrayEnvelope envelope = new GenericArrayEnvelope(4);
            runGenericArrayActivation(root, envelope,
                    Arrays.asList(envelope.elements), getter, 1);

            JsonObject row = resultRows(results).get(0);
            assertEquals(row.getAsJsonArray("unresolvedInputs").toString(),
                    0, row.getAsJsonArray("unresolvedInputs").size());
            JsonArray bindings = row.getAsJsonArray(
                    "dynamicFieldBindings");
            assertEquals(4, bindings.size());
            for (int index = 0; index < bindings.size(); index++) {
                JsonObject binding = bindings.get(index).getAsJsonObject();
                assertEquals(root + "#u" + units[index], binding.get(
                        "effectiveMaterializationSiteId").getAsString());
                assertEquals(1, binding.get(
                        "effectiveMaterializationOccurrence").getAsInt());
                assertEquals(getter + "#u1", binding.get(
                        "actualHookSiteId").getAsString());
                assertEquals(index + 1, binding.get(
                        "actualHookOccurrence").getAsInt());
                assertEquals("BIND.EXACT." + index, binding.get(
                        "materializationSiteBridgeBindingId").getAsString());
                assertEquals(binding.get("leafOwnerObjectToken"),
                        binding.get(
                                "materializationSiteBridgeElementObjectToken"));
                assertEquals("ACT.BRIDGE.ARRAY.FIELD", binding.get(
                        "materializationSiteBridgeObjectTokenScope")
                                .getAsString());
            }
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void exactArrayBindingCoverageFailsWhenOneSelectedOwnerIsMissing()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void requireArrayFields()>";
        String base = "REGION.TEST.in.elementId";
        String container = "REGION.TEST.in.elements";
        JsonObject activation = concreteActivation(
                "ACT.REQUIRE.ARRAY.FIELD", root, 1);
        addExecutableActions(activation, genericArrayActions(base, container,
                root));
        JsonArray declarations = new JsonArray();
        for (int index = 0; index < 4; index++) {
            declarations.add(genericArrayBinding("BIND.EXACT." + index,
                    base, container, "EXACT_ARRAY_INDEX", index, 1,
                    root + "#u" + (14 + index)));
        }
        activation.add("containerElementFieldBindings", declarations);
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            GenericArrayEnvelope envelope = new GenericArrayEnvelope(4);
            runGenericArrayActivation(root, envelope,
                    Arrays.asList(envelope.elements).subList(0, 3),
                    root, 6);
            JsonObject row = resultRows(results).get(0);
            assertEquals(3, row.getAsJsonArray(
                    "dynamicFieldBindings").size());
            assertTrue(row.getAsJsonArray("unresolvedInputs").toString()
                    .contains("BIND.EXACT.3 produced 0 complete runtime "
                            + "bindings; expected 1"));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void foreignThreadCannotFinishOrReleaseSelectedRegion()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Owner: void run()>";
        JsonObject activation = concreteActivation(
                "ACT.OBSERVE.OWNER", root, 1);
        Files.write(plan, (activation + "\n")
                .getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concrete-overlap-test");
        try {
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            assertTrue(token > 0L);
            assertEquals(1, ConcolicRegionRuntime
                    .concreteReplayActiveCountForTests());
            Thread foreign = new Thread(() ->
                    ConcolicRegionRuntime.exitRegion(token, null, ""));
            foreign.start();
            foreign.join(5000L);

            assertTrue(ConcolicRegionRuntime.activeTokenForTests(token));
            assertEquals(1, ConcolicRegionRuntime
                    .concreteReplayActiveCountForTests());
            assertFalse(Files.exists(results));

            ConcolicRegionRuntime.exitRegion(token, null, "");
            assertFalse(ConcolicRegionRuntime.activeTokenForTests(token));
            assertEquals(0, ConcolicRegionRuntime
                    .concreteReplayActiveCountForTests());
            assertEquals(1, Files.readAllLines(results,
                    StandardCharsets.UTF_8).size());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void ordinaryJdkSkipsSelectedActivationWithoutBreakingTest() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void handle(java.lang.Object)>";
        String row = "{\"activationId\":\"ACT.0\","
                + "\"regionId\":\"REGION.0\","
                + "\"test\":\"bridge-test\","
                + "\"rootMethod\":\"" + root + "\","
                + "\"invocationOrdinal\":1,\"replayable\":true,"
                + "\"materializations\":[{\"symbol\":\"REGION.0.in.0\","
                + "\"cell\":\"arg0\",\"location\":\"ARGUMENT\","
                + "\"index\":0}]}\n";
        Files.write(plan, row.getBytes(StandardCharsets.UTF_8));

        String oldPlan = System.getProperty("causynth.concolic.activation.plan");
        String oldResults = System.getProperty("causynth.concolic.results");
        String oldTest = System.getProperty("causynth.trace.test");
        try {
            System.setProperty("causynth.concolic.activation.plan", plan.toString());
            System.setProperty("causynth.concolic.results", results.toString());
            System.setProperty("causynth.trace.test", "bridge-test");
            ConcolicRegionRuntime.resetForTests();

            long token = ConcolicRegionRuntime.enterRegion(root, new Object());

            assertEquals(0L, token);
            String output = new String(Files.readAllBytes(results),
                    StandardCharsets.UTF_8);
            assertTrue(output.contains("CONCOLIC_REGION_SKIPPED"));
            assertTrue(output.contains("custom concolic System API is unavailable"));
        } finally {
            restore("causynth.concolic.activation.plan", oldPlan);
            restore("causynth.concolic.results", oldResults);
            restore("causynth.trace.test", oldTest);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void capturesOnlyRequestedExactOutboundArgumentOccurrence()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Root: void run()>";
        String caller = "<example.Client: void send()>";
        String callee = "<example.Protocol: void accept(java.lang.String)>";
        String cell = callee + ".param0:java.lang.String";
        JsonObject activation = concreteActivation("ACT.OUTPUT.EXACT", root,
                1);
        activation.addProperty("test", "output-capture-test");
        activation.addProperty("concreteReplayOnly", false);
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId",
                "REGION.TEST.out.0.capture.0");
        capture.addProperty("outputPort", "REGION.TEST.out.0");
        capture.addProperty("outputCell", cell);
        capture.addProperty("callerMethod", caller);
        capture.addProperty("unitIndex", 7);
        capture.addProperty("siteId", caller + "#u7");
        capture.addProperty("calleeMethod", callee);
        capture.addProperty("argumentIndex", 0);
        capture.addProperty("occurrence", 2);
        activation.add("requestedOutputCapture", singleton(capture));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "output-capture-test");
        try {
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            assertTrue(token > 0L);
            ConcolicRegionRuntime.recordOutputCapture(caller, 7,
                    caller + "#u7", callee, 0, "REGION.TEST.out.0",
                    cell, "REGION.TEST.out.0.capture.0", 2,
                    "first", "");
            ConcolicRegionRuntime.recordOutputCapture(caller, 7,
                    caller + "#u7", callee, 0, "REGION.TEST.out.0",
                    cell, "REGION.TEST.out.0.capture.0", 2,
                    "second", "");
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            JsonArray captures = row.getAsJsonArray("outputCaptures");
            assertEquals(1, captures.size());
            JsonObject observed = captures.get(0).getAsJsonObject();
            assertEquals(2, observed.get("occurrence").getAsInt());
            assertEquals("REGION.TEST.out.0.capture.0",
                    observed.get("captureBindingId").getAsString());
            assertEquals("M_L_field_REGION.TEST.in.0_java/lang/String",
                    observed.getAsJsonObject("expression").get("_exp")
                            .getAsString());
            assertEquals(1, observed.get(
                    "expressionEnvelopeSchemaVersion").getAsInt());
            assertTrue(observed.get("expressionEnvelopeActive")
                    .getAsBoolean());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void capturesExactPostAssignmentRhsWithTokenAndIdentityProof()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Root: void run()>";
        String method = "<example.Heartbeat: void install(java.lang.Object)>";
        String field = "<" + AssignmentOwner.class.getName()
                + ": java.lang.Object assigned>";
        JsonObject activation = concreteActivation("ACT.FIELD.OUTPUT", root,
                1);
        activation.addProperty("test", "field-output-capture-test");
        activation.addProperty("concreteReplayOnly", false);
        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        capture.addProperty("captureBindingId",
                "REGION.TEST.out.field.capture.0");
        capture.addProperty("outputPort", "REGION.TEST.out.field");
        capture.addProperty("outputCell", field);
        capture.addProperty("method", method);
        capture.addProperty("unitIndex", 11);
        capture.addProperty("siteId", method + "#u11");
        capture.addProperty("fieldSignature", field);
        capture.addProperty("occurrence", 2);
        activation.add("requestedOutputCapture", singleton(capture));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "field-output-capture-test");
        try {
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            assertTrue(token > 0L);
            assertEquals(token, ConcolicRegionRuntime.activeToken());
            AssignmentOwner owner = new AssignmentOwner();

            owner.assigned = "ignored-wrong-token";
            ConcolicRegionRuntime.recordFieldAssignmentOutput(token + 1L,
                    method, 11, method + "#u11", field,
                    "REGION.TEST.out.field.capture.0",
                    "REGION.TEST.out.field", field, 2,
                    owner, owner.assigned, "");
            owner.assigned = "ignored-wrong-site";
            ConcolicRegionRuntime.recordFieldAssignmentOutput(token,
                    method, 11, method + "#wrong", field,
                    "REGION.TEST.out.field.capture.0",
                    "REGION.TEST.out.field", field, 2,
                    owner, owner.assigned, "");
            owner.assigned = "first";
            ConcolicRegionRuntime.recordFieldAssignmentOutput(token,
                    method, 11, method + "#u11", field,
                    "REGION.TEST.out.field.capture.0",
                    "REGION.TEST.out.field", field, 2,
                    owner, owner.assigned, "");
            owner.assigned = "second";
            ConcolicRegionRuntime.recordFieldAssignmentOutput(token,
                    method, 11, method + "#u11", field,
                    "REGION.TEST.out.field.capture.0",
                    "REGION.TEST.out.field", field, 2,
                    owner, owner.assigned, "");
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
            JsonArray captures = row.getAsJsonArray("outputCaptures");
            assertEquals(1, captures.size());
            JsonObject observed = captures.get(0).getAsJsonObject();
            assertEquals("FIELD_ASSIGNMENT_RHS",
                    observed.get("captureKind").getAsString());
            assertEquals(2, observed.get("occurrence").getAsInt());
            assertTrue(observed.get("declaredFieldOwnerVerified")
                    .getAsBoolean());
            assertTrue(observed.get("declaredFieldTypeVerified")
                    .getAsBoolean());
            assertTrue(observed.get("assignmentIdentityVerified")
                    .getAsBoolean());
            long ownerToken = observed.get("fieldOwnerObjectToken")
                    .getAsLong();
            long valueToken = observed.get("assignedValueObjectToken")
                    .getAsLong();
            assertTrue(ownerToken > 0L);
            assertTrue(valueToken > 0L);
            assertTrue(ownerToken != valueToken);
            assertEquals(valueToken,
                    observed.get("observedFieldValueObjectToken")
                            .getAsLong());
            assertEquals("M_L_field_REGION.TEST.in.0_java/lang/String",
                    observed.getAsJsonObject("expression").get("_exp")
                            .getAsString());
            assertEquals(1, observed.get(
                    "expressionEnvelopeSchemaVersion").getAsInt());
            assertTrue(observed.get("expressionEnvelopeActive")
                    .getAsBoolean());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void selectedActivationStillWaitsForRuntimeInvocationOrdinal()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Handler: void handle(java.lang.Object)>";
        String row = "{\"activationId\":\"ACT.ordinal\","
                + "\"regionId\":\"REGION.0\","
                + "\"test\":\"ordinal-test\","
                + "\"rootMethod\":\"" + root + "\","
                + "\"invocationOrdinal\":2,\"replayable\":true,"
                + "\"materializations\":[]}\n";
        Files.write(plan, row.getBytes(StandardCharsets.UTF_8));

        String oldPlan = System.getProperty("causynth.concolic.activation.plan");
        String oldActivation = System.getProperty("causynth.concolic.activation.id");
        String oldResults = System.getProperty("causynth.concolic.results");
        String oldTest = System.getProperty("causynth.trace.test");
        try {
            System.setProperty("causynth.concolic.activation.plan", plan.toString());
            System.setProperty("causynth.concolic.activation.id", "ACT.ordinal");
            System.setProperty("causynth.concolic.results", results.toString());
            System.setProperty("causynth.trace.test", "ordinal-test");
            ConcolicRegionRuntime.resetForTests();

            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root, new Object()));
            assertFalse(Files.exists(results));

            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root, new Object()));
            assertTrue(Files.exists(results));
            String output = new String(Files.readAllBytes(results),
                    StandardCharsets.UTF_8);
            assertTrue(output.contains("ACT.ordinal"));
            assertTrue(output.contains("CONCOLIC_REGION_SKIPPED"));
        } finally {
            restore("causynth.concolic.activation.plan", oldPlan);
            restore("causynth.concolic.activation.id", oldActivation);
            restore("causynth.concolic.results", oldResults);
            restore("causynth.trace.test", oldTest);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void stableRootContextFiltersBeforeContextRelativeArgumentOrdinal()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.WorkerThread: void run(java.lang.Object)>";
        JsonObject activation = concreteActivation("ACT.CONTEXT", root, 99);
        activation.addProperty("test", "stable-context-test");
        addStableRootContext(activation, ConsumerWorker.class.getName(),
                "pool-1-thread-2", 1);
        addRootArgumentSelector(activation, 1, 1,
                KeyUpdateCommand.class.getName());
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "stable-context-test");
        String oldThreadName = Thread.currentThread().getName();
        try {
            // Receiver class and executor thread ordinal remain exact context
            // parts; neither mismatch may advance its invocation ordinal.
            // The executor pool id is normalized between discovery/replay.
            Thread.currentThread().setName("pool-9-thread-2");
            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root,
                    new ProducerWorker(),
                    new Object[]{new KeyUpdateCommand()}));
            Thread.currentThread().setName("pool-9-thread-3");
            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root,
                    new ConsumerWorker(),
                    new Object[]{new KeyUpdateCommand()}));
            Thread.currentThread().setName("pool-9-thread-2");
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new ConsumerWorker(),
                    new Object[]{new KeyUpdateCommand()});
            assertTrue("global ordinal must not control a stable plan",
                    token > 0L);
            ConcolicRegionRuntime.exitRegion(token, null, "");
            String output = new String(Files.readAllBytes(results),
                    StandardCharsets.UTF_8);
            assertTrue(output.contains("ACT.CONTEXT"));
        } finally {
            Thread.currentThread().setName(oldThreadName);
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void stableRootContextRejectsJvmAssignedThreadId()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.WorkerThread: void run()>";
        JsonObject activation = concreteActivation("ACT.UNSTABLE.TID", root,
                1);
        activation.addProperty("test", "unstable-thread-id-test");
        addStableRootContext(activation, ConsumerWorker.class.getName(),
                "consumer-thread", 1);
        activation.addProperty("threadId", 41L);
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "unstable-thread-id-test");
        try {
            try {
                ConcolicRegionRuntime.enterRegion(root,
                        new ConsumerWorker());
                throw new AssertionError("JVM thread id selector must fail");
            } catch (IllegalStateException expected) {
                assertTrue(expected.getMessage().contains(
                        "Malformed stable runtime root context"));
                assertTrue(expected.getMessage().contains(
                        "ACT.UNSTABLE.TID"));
            }
            assertFalse(Files.exists(results));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void exactRootArgumentTypesUseWithinReceiverOrdinal()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Actor: void process(java.lang.Object,"
                + "java.lang.Object)>";
        JsonObject activation = concreteActivation("ACT.SELECTOR", root, 48);
        activation.addProperty("test", "selector-test");
        addRootArgumentSelector(activation, 2,
                KeyUpdateCommand.class.getName(), BPServiceActor.class.getName());
        Files.write(plan, (activation + "\n").getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "selector-test");
        try {
            Object receiver = new Object();
            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root, receiver,
                    new Object[]{new Object(), new BPServiceActor()}));
            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root, receiver,
                    new Object[]{new KeyUpdateCommand(), new Object()}));
            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root, receiver,
                    new Object[]{new KeyUpdateCommand(),
                            new BPServiceActor()}));
            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root, receiver,
                    new Object[]{null, new BPServiceActor()}));

            long token = ConcolicRegionRuntime.enterRegion(root, receiver,
                    new Object[]{new KeyUpdateCommand(),
                            new BPServiceActor()});
            assertTrue(token > 0L);
            ConcolicRegionRuntime.exitRegion(token, null, "");
            String output = new String(Files.readAllBytes(results),
                    StandardCharsets.UTF_8);
            assertTrue(output.contains("ACT.SELECTOR"));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void receiverScopedSelectorSeparatesSameTypedInstances()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Actor: void process(java.lang.Object,"
                + "java.lang.Object)>";
        JsonObject activation = concreteActivation("ACT.RECEIVER", root, 99);
        activation.addProperty("test", "receiver-selector-test");
        addRootArgumentSelector(activation, 2, 1,
                KeyUpdateCommand.class.getName(), BPServiceActor.class.getName());
        Files.write(plan, (activation + "\n").getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "receiver-selector-test");
        try {
            Object firstReceiver = new Object();
            Object secondReceiver = new Object();
            Object[] arguments = {new KeyUpdateCommand(),
                    new BPServiceActor()};
            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root,
                    firstReceiver, arguments));
            long token = ConcolicRegionRuntime.enterRegion(root,
                    secondReceiver, arguments);
            assertTrue(token > 0L);
            ConcolicRegionRuntime.exitRegion(token, null, "");
            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root,
                    firstReceiver, arguments));
            String output = new String(Files.readAllBytes(results),
                    StandardCharsets.UTF_8);
            assertTrue(output.contains("ACT.RECEIVER"));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void legacyV1SelectorRemainsPredicateGloballyRelative()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Actor: void process(java.lang.Object)>";
        JsonObject activation = concreteActivation("ACT.LEGACY.V1", root, 99);
        activation.addProperty("test", "legacy-selector-test");
        addLegacyRootArgumentSelector(activation, 2,
                KeyUpdateCommand.class.getName());
        Files.write(plan, (activation + "\n").getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "legacy-selector-test");
        try {
            assertEquals(0L, ConcolicRegionRuntime.enterRegion(root,
                    new Object(), new Object[]{new KeyUpdateCommand()}));
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object(), new Object[]{new KeyUpdateCommand()});
            assertTrue(token > 0L);
            ConcolicRegionRuntime.exitRegion(token, null, "");
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void receiverScopedSelectorAssignsConcurrentReceiversOnce()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Actor: void process(java.lang.Object)>";
        JsonObject activation = concreteActivation("ACT.CONCURRENT", root, 99);
        activation.addProperty("test", "concurrent-selector-test");
        final int threadCount = 24;
        addRootArgumentSelector(activation, threadCount, 1,
                KeyUpdateCommand.class.getName());
        Files.write(plan, (activation + "\n").getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "concurrent-selector-test");
        try {
            CountDownLatch ready = new CountDownLatch(threadCount);
            CountDownLatch start = new CountDownLatch(1);
            CountDownLatch done = new CountDownLatch(threadCount);
            AtomicLong selected = new AtomicLong();
            for (int index = 0; index < threadCount; index++) {
                Thread worker = new Thread(() -> {
                    ready.countDown();
                    try {
                        start.await();
                        long token = ConcolicRegionRuntime.enterRegion(root,
                                new Object(),
                                new Object[]{new KeyUpdateCommand()});
                        if (token > 0L) {
                            selected.incrementAndGet();
                            ConcolicRegionRuntime.exitRegion(token, null, "");
                        }
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                    } finally {
                        done.countDown();
                    }
                });
                worker.start();
            }
            assertTrue(ready.await(10, TimeUnit.SECONDS));
            start.countDown();
            assertTrue(done.await(10, TimeUnit.SECONDS));
            assertEquals(1L, selected.get());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void malformedRootArgumentSelectorFailsClosed() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Actor: void process(java.lang.Object)>";
        JsonObject activation = concreteActivation("ACT.MALFORMED", root, 1);
        activation.addProperty("test", "malformed-selector-test");
        JsonObject selector = new JsonObject();
        selector.addProperty("schema",
                RuntimeRegionPlanner.ROOT_ARGUMENT_SELECTOR_SCHEMA);
        selector.addProperty("authority",
                RuntimeRegionPlanner.ROOT_ARGUMENT_SELECTOR_AUTHORITY);
        selector.addProperty("receiverOrdinal", "1");
        selector.addProperty("matchOrdinalWithinReceiver", 1);
        JsonObject predicate = new JsonObject();
        predicate.addProperty("kind",
                RuntimeRegionPlanner.ROOT_ARGUMENT_PREDICATE_KIND);
        predicate.addProperty("argumentIndex", 0);
        predicate.addProperty("runtimeType", Object.class.getName());
        JsonArray predicates = new JsonArray();
        predicates.add(predicate);
        selector.add("predicates", predicates);
        activation.add("runtimeRootArgumentSelector", selector);
        Files.write(plan, (activation + "\n").getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results,
                "malformed-selector-test");
        try {
            try {
                ConcolicRegionRuntime.enterRegion(root, new Object(),
                        new Object[]{new Object()});
                throw new AssertionError("malformed selector must fail closed");
            } catch (IllegalStateException expected) {
                assertTrue(expected.getMessage().contains(
                        "Malformed runtime root argument selector"));
                assertTrue(expected.getMessage().contains("ACT.MALFORMED"));
            }
            assertFalse(Files.exists(results));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void runtimeKeyIncludesExactSelectorIdentity() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Actor: void process(java.lang.Object,"
                + "java.lang.Object)>";
        JsonObject keyUpdate = concreteActivation("ACT.KEY", root, 1);
        keyUpdate.addProperty("test", "selector-key-test");
        addRootArgumentSelector(keyUpdate, 1,
                KeyUpdateCommand.class.getName(), BPServiceActor.class.getName());
        JsonObject heartbeat = concreteActivation("ACT.HEARTBEAT", root, 1);
        heartbeat.addProperty("test", "selector-key-test");
        addRootArgumentSelector(heartbeat, 1,
                HeartbeatCommand.class.getName(), BPServiceActor.class.getName());
        Files.write(plan, (keyUpdate + "\n" + heartbeat + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "selector-key-test");
        try {
            long token = ConcolicRegionRuntime.enterRegion(root, new Object(),
                    new Object[]{new HeartbeatCommand(),
                            new BPServiceActor()});
            assertTrue(token > 0L);
            ConcolicRegionRuntime.exitRegion(token, null, "");
            String output = new String(Files.readAllBytes(results),
                    StandardCharsets.UTF_8);
            assertTrue(output.contains("ACT.HEARTBEAT"));
            assertFalse(output.contains("ACT.KEY"));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void overlappingSelectorFamiliesAdvanceBeforeActivationSelection()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Actor: void process(java.lang.Object,"
                + "java.lang.Object)>";
        JsonObject first = concreteActivation("ACT.OVERLAP.FIRST", root, 1);
        first.addProperty("test", "overlap-selector-test");
        addRootArgumentSelector(first, 1,
                KeyUpdateCommand.class.getName());
        JsonObject second = concreteActivation("ACT.OVERLAP.SECOND", root, 1);
        second.addProperty("test", "overlap-selector-test");
        addRootArgumentSelector(second, 2,
                KeyUpdateCommand.class.getName(), BPServiceActor.class.getName());
        Files.write(plan, (first + "\n" + second + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "overlap-selector-test");
        try {
            Object receiver = new Object();
            Object[] arguments = {new KeyUpdateCommand(),
                    new BPServiceActor()};
            long firstToken = ConcolicRegionRuntime.enterRegion(root,
                    receiver, arguments);
            assertTrue(firstToken > 0L);
            ConcolicRegionRuntime.exitRegion(firstToken, null, "");
            long secondToken = ConcolicRegionRuntime.enterRegion(root,
                    receiver, arguments);
            assertTrue(secondToken > 0L);
            ConcolicRegionRuntime.exitRegion(secondToken, null, "");
            String output = new String(Files.readAllBytes(results),
                    StandardCharsets.UTF_8);
            assertTrue(output.contains("ACT.OVERLAP.FIRST"));
            assertTrue(output.contains("ACT.OVERLAP.SECOND"));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void concreteReplayAppliesUpstreamModelWithoutCustomJdk()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.Producer: void apply()>";
        String owner = Manager.class.getName();
        String field = "<" + owner + ": java.util.Map allKeys>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.10.in.0");
        action.addProperty("cell", field);
        action.addProperty("field", field);
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessOwnerClass", owner);
        action.addProperty("accessField", "allKeys");
        action.addProperty("leafOwnerClass", owner);
        action.addProperty("leafField", "allKeys");
        action.add("fieldPath", JsonParser.parseString("[\"allKeys\"]"));
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "port__REGION_10_in_0");
        assignment.addProperty("inputSymbol", "REGION.10.in.0");
        assignment.addProperty("valueType", "MAP_STATE");
        assignment.addProperty("value", "emptyMapState");
        assignment.addProperty("modelOperation", "MAP_CLEAR");
        assignment.add("materializationPath",
                JsonParser.parseString("[\"allKeys\"]"));
        JsonObject activation = concreteActivation("ACT.MODEL.1", root, 1);
        addExecutableActions(activation, singleton(action));
        activation.add("modelAssignments", singleton(assignment));
        Files.write(plan, (activation + "\n").getBytes(StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "concrete-model-test");
        try {
            Manager manager = new Manager();
            manager.allKeys.put("old", "value");
            long token = ConcolicRegionRuntime.enterRegion(root, manager);
            assertTrue(token > 0L);
            ConcolicRegionRuntime.materializeField(root, 1, manager,
                    field, "allKeys");
            assertTrue(manager.allKeys.isEmpty());
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = JsonParser.parseString(new String(
                    Files.readAllBytes(results), StandardCharsets.UTF_8)
                    .trim()).getAsJsonObject();
            assertEquals("CONCRETE_REPLAY_ONLY",
                    row.get("executionMode").getAsString());
            assertTrue(row.get("allModelAssignmentsApplied").getAsBoolean());
            assertEquals(1, row.getAsJsonArray(
                    "modelAssignmentsApplied").size());
            assertEquals(0, row.getAsJsonObject("engineSummary")
                    .getAsJsonArray("pathCondition").size());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void missingOrInvalidInstrumentedBranchPolicyFailsClosedToExplore()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.PolicyTarget: void run()>";
        String declaredSite = root + "#u3";
        String invalidSite = root + "#u5";
        String missingSite = root + "#u7";
        JsonObject activation = concreteActivation(
                "ACT.BRANCH.POLICY.FAIL.CLOSED", root, 1);
        JsonArray branches = new JsonArray();
        JsonObject declared = new JsonObject();
        declared.addProperty("siteId", declaredSite);
        declared.addProperty("policy", "PATH_ASSUMPTION");
        branches.add(declared);
        JsonObject invalid = new JsonObject();
        invalid.addProperty("siteId", invalidSite);
        invalid.addProperty("policy", "IGNORE");
        branches.add(invalid);
        activation.add("branches", branches);
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "concrete-overlap-test");
        try {
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            assertTrue(token > 0L);
            assertTrue(ConcolicRegionRuntime.resolveBranch(0L, 0L,
                    root, 3, "declared", true));
            assertFalse(ConcolicRegionRuntime.resolveBranch(0L, 0L,
                    root, 5, "invalid", false));
            assertTrue(ConcolicRegionRuntime.resolveBranch(0L, 0L,
                    root, 7, "missing", true));
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject result = resultRows(results).get(0);
            JsonArray mappings = result.getAsJsonArray("branchMappings");
            assertEquals(3, mappings.size());

            JsonObject declaredMapping = mappings.get(0).getAsJsonObject();
            assertEquals("PATH_ASSUMPTION",
                    declaredMapping.get("policy").getAsString());
            assertTrue(declaredMapping.get("policyResolutionComplete")
                    .getAsBoolean());
            assertEquals("ACTIVATION_PLAN_EXACT_BRANCH_POLICY_V1",
                    declaredMapping.get("policyAuthority").getAsString());
            assertFalse(declaredMapping.has("policyGap"));

            JsonObject invalidMapping = mappings.get(1).getAsJsonObject();
            assertEquals("EXPLORE",
                    invalidMapping.get("policy").getAsString());
            assertFalse(invalidMapping.get("policyResolutionComplete")
                    .getAsBoolean());
            assertTrue(invalidMapping.get("policyGap").getAsString()
                    .contains("unsupported"));

            JsonObject missingMapping = mappings.get(2).getAsJsonObject();
            assertEquals("EXPLORE",
                    missingMapping.get("policy").getAsString());
            assertFalse(missingMapping.get("policyResolutionComplete")
                    .getAsBoolean());
            assertEquals(
                    "RUNTIME_INSTRUMENTED_BRANCH_FAIL_CLOSED_TO_EXPLORE_V1",
                    missingMapping.get("policyAuthority").getAsString());
            assertTrue(missingMapping.get("policyGap").getAsString()
                    .contains("no policy"));

            JsonArray unresolved = result.getAsJsonArray(
                    "unresolvedInputs");
            assertEquals(2, unresolved.size());
            assertTrue(unresolved.get(0).getAsString().contains(invalidSite));
            assertTrue(unresolved.get(1).getAsString().contains(missingSite));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            folder.delete();
        }
    }

    @Test
    public void capturesExactEngineArrayIdsForArgumentReceiverAndFieldInputs()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.ArrayInputs: void run(" + Current.class
                .getName() + "[])>";
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.INPUTS", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        JsonArray actions = new JsonArray();
        actions.add(engineArrayFieldAction("REGION.ARRAY.in.receiver",
                engineArrayReceiverFieldSignature(), "receiverValues",
                "RECEIVER_FIELD"));
        actions.add(engineArrayArgumentAction("REGION.ARRAY.in.argument",
                root, 0));
        actions.add(consumedFieldAction(engineArrayFieldAction(
                "REGION.ARRAY.in.field",
                engineArrayAccessFieldSignature(), "accessedValues",
                "HEAP_OBJECT_FIELD"), root, 8,
                "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                        + "PATH_PREFIX_REFERENCE_EQUALITY"));
        addExecutableActions(activation, actions);
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            EngineArrayInputOwner owner = new EngineArrayInputOwner();
            Current[] argument = {new Current(), new Current()};
            long token = ConcolicRegionRuntime.enterRegion(root, owner);
            assertTrue(token > 0L);
            ConcolicRegionRuntime.symbolizeArgument(token, 0, argument, "");
            ConcolicRegionRuntime.prepareFieldMaterialization(root, 8,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues");
            Current[] consumed = owner.accessedValues;
            ConcolicRegionRuntime.materializeConsumedField(root, 8,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues", consumed);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
            assertEquals(0,
                    DelayedExpressionEngine.arrayExpressionCallsOutsidePause);
            JsonArray bindings = row.getAsJsonArray(
                    "engineArrayInputBindings");
            assertEquals(3, bindings.size());
            java.util.Set<String> ids = new java.util.LinkedHashSet<>();
            java.util.Set<Long> tokens = new java.util.LinkedHashSet<>();
            for (JsonElement element : bindings) {
                JsonObject binding = element.getAsJsonObject();
                assertEquals(1, binding.get("schemaVersion").getAsInt());
                assertEquals("ENGINE_ARRAY_TO_INPUT_PORT",
                        binding.get("kind").getAsString());
                assertEquals("ACT.ENGINE.ARRAY.INPUTS", binding.get(
                        "sourceActivationId").getAsString());
                assertEquals(Current.class.getName() + "[]",
                        binding.get("inputJavaType").getAsString());
                assertEquals("[L" + Current.class.getName()
                                .replace('.', '/') + ";",
                        binding.get("inputJavaTypeDescriptor").getAsString());
                assertEquals("VM_ACTIVE_SYM_ARRAY_ID_V1", binding.get(
                        "engineArrayIdAuthority").getAsString());
                assertEquals(
                        "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN",
                        binding.get("objectTokenAuthority").getAsString());
                assertEquals("ACT.ENGINE.ARRAY.INPUTS",
                        binding.get("objectTokenScope").getAsString());
                assertEquals(
                        "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_"
                                + "SYMBOLIZATION",
                        binding.get("captureAuthority").getAsString());
                assertEquals(binding.get("inputPort").getAsString(),
                        binding.get("symbolizationPrefix").getAsString());
                assertEquals(
                        "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX",
                        binding.get("symbolizationMode").getAsString());
                assertEquals(binding.get("arrayObjectToken").getAsLong(),
                        binding.get("symbolizationArrayObjectToken")
                                .getAsLong());
                assertEquals(
                        "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                                + "EXPRESSION_CAPTURE",
                        binding.get("symbolizationIdentityAuthority")
                                .getAsString());
                assertTrue(binding.get("sameArrayObjectTokenVerified")
                        .getAsBoolean());
                assertTrue(binding.get("fieldPrePostReferenceVerified")
                        .getAsBoolean());
                assertTrue(binding.get("complete").getAsBoolean());
                assertTrue(ids.add(binding.get("engineArrayId")
                        .getAsString()));
                assertTrue(tokens.add(binding.get("arrayObjectToken")
                        .getAsLong()));
                JsonObject proof = binding.getAsJsonObject(
                        "arrayValueExpression");
                assertEquals("ArrayValueExpression",
                        proof.get("_type").getAsString());
                assertEquals("VM_EXACT_FINITE_ARRAY_VALUE_V1",
                        proof.get("_authority").getAsString());
                assertEquals(binding.get("engineArrayId").getAsString(),
                        proof.get("_engine_array_id").getAsString());
                assertTrue(proof.get("_elements_complete").getAsBoolean());
            }
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void engineArrayInputBindingRejectsIncompleteVmSnapshots()
            throws Exception {
        for (String mode : Arrays.asList("OPAQUE_ELEMENTS",
                "WRONG_LENGTH_EXPRESSION", "WRONG_PROVENANCE",
                "MISSING_ARRAY_ID", "MALFORMED_ARRAY_ID",
                "WRONG_ARRAY_ID_TYPE")) {
            JsonObject row = runEngineArrayInputFailure(mode, false);
            JsonArray bindings = row.getAsJsonArray(
                    "engineArrayInputBindings");
            assertEquals(mode, 1, bindings.size());
            JsonObject binding = bindings.get(0).getAsJsonObject();
            assertFalse(mode, binding.get("complete").getAsBoolean());
            assertTrue(mode, binding.has("problem"));
            assertTrue(mode, row.getAsJsonArray("unresolvedInputs")
                    .toString().contains("engine-array input binding failed "
                            + "closed"));
        }
    }

    @Test
    public void engineArrayInputBindingChecksPrimitiveConcreteLiteral()
            throws Exception {
        JsonObject accepted = runPrimitiveEngineArrayInput("NORMAL");
        assertTrue(accepted.getAsJsonArray("engineArrayInputBindings")
                .get(0).getAsJsonObject().get("complete").getAsBoolean());
        JsonObject rejected = runPrimitiveEngineArrayInput(
                "WRONG_PRIMITIVE_LITERAL");
        JsonObject binding = rejected.getAsJsonArray(
                "engineArrayInputBindings").get(0).getAsJsonObject();
        assertFalse(binding.get("complete").getAsBoolean());
        assertTrue(binding.get("problem").getAsString().contains(
                "primitive literal differs"));
    }

    @Test
    public void engineArrayInputBindingRejectsPortAndEngineIdAliasing()
            throws Exception {
        JsonObject samePort = runEngineArrayInputFailure("NORMAL", true);
        assertEquals(1, samePort.getAsJsonArray(
                "engineArrayInputBindings").size());
        assertFalse(samePort.getAsJsonArray("engineArrayInputBindings")
                .get(0).getAsJsonObject().get("complete").getAsBoolean());
        assertTrue(samePort.getAsJsonArray("unresolvedInputs").toString()
                .contains("more than one live array token or VM array id"));

        JsonObject sameId = runEngineArrayIdCollision();
        assertEquals(2, sameId.getAsJsonArray(
                "engineArrayInputBindings").size());
        for (JsonElement element : sameId.getAsJsonArray(
                "engineArrayInputBindings")) {
            assertFalse(element.getAsJsonObject().get("complete")
                    .getAsBoolean());
        }
        assertTrue(sameId.getAsJsonArray("unresolvedInputs").toString()
                .contains("aliases distinct live arrays"));
    }

    @Test
    public void nestedFieldPathUsesExactLeafArrayTypeAndCanonicalPrefix()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.NestedArray: void run("
                + NestedArrayInputRoot.class.getName() + ")>";
        String port = "REGION.ARRAY.in.nested";
        String leafSignature = "<" + NestedArrayInputPayload.class.getName()
                + ": " + Current.class.getName() + "[] values>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("cell", root + ".param0:"
                + NestedArrayInputRoot.class.getName());
        // For a selective field-path array port, javaType is the statically
        // declared leaf value type, not the root carrier type.
        action.addProperty("javaType", Current.class.getName() + "[]");
        action.addProperty("location", "ARGUMENT_FIELD_PATH");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", 0);
        action.add("fieldPaths", JsonParser.parseString(
                "[[\"payload\",\"values\"]]"));
        JsonObject leaf = new JsonObject();
        leaf.add("fieldPath", JsonParser.parseString(
                "[\"payload\",\"values\"]"));
        leaf.addProperty("fieldSignature", leafSignature);
        action.add("fieldPathLeafDeclarations", singleton(leaf));
        consumedFieldAction(action, root, 7,
                "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                        + "PATH_PREFIX_REFERENCE_EQUALITY");
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.NESTED", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(action));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            NestedArrayInputRoot input = new NestedArrayInputRoot();
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            ConcolicRegionRuntime.symbolizeArgument(token, 0, input, "");
            ConcolicRegionRuntime.prepareFieldMaterialization(root, 7,
                    input.payload, leafSignature, "values");
            Current[] consumed = input.payload.values;
            ConcolicRegionRuntime.materializeConsumedField(root, 7,
                    input.payload, leafSignature, "values", consumed);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals("[\"" + port + "\"]",
                    row.getAsJsonArray("symbolizedInputs").toString());
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
            JsonObject binding = row.getAsJsonArray(
                    "engineArrayInputBindings").get(0).getAsJsonObject();
            assertEquals(Current.class.getName() + "[]",
                    binding.get("inputJavaType").getAsString());
            assertEquals(port,
                    binding.get("symbolizationPrefix").getAsString());
            assertTrue(binding.get("fieldPrePostReferenceVerified")
                    .getAsBoolean());
            assertTrue(binding.get("complete").getAsBoolean());
            assertEquals(0, row.getAsJsonArray("fieldObservations").size());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void nestedConsumedFieldRejectsUnregisteredSameClassOwner()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.NestedArrayWrongOwner: void run("
                + NestedArrayInputRoot.class.getName() + ")>";
        String leafSignature = "<" + NestedArrayInputPayload.class.getName()
                + ": " + Current.class.getName() + "[] values>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.ARRAY.in.nested.owner");
        action.addProperty("cell", root + ".param0:"
                + NestedArrayInputRoot.class.getName());
        action.addProperty("javaType", Current.class.getName() + "[]");
        action.addProperty("location", "ARGUMENT_FIELD_PATH");
        action.addProperty("bindingMode", "ROOT_ENTRY");
        action.addProperty("index", 0);
        action.add("fieldPaths", JsonParser.parseString(
                "[[\"payload\",\"values\"]]"));
        JsonObject leaf = new JsonObject();
        leaf.add("fieldPath", JsonParser.parseString(
                "[\"payload\",\"values\"]"));
        leaf.addProperty("fieldSignature", leafSignature);
        action.add("fieldPathLeafDeclarations", singleton(leaf));
        consumedFieldAction(action, root, 13,
                "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                        + "PATH_PREFIX_REFERENCE_EQUALITY");
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.NESTED.WRONG.OWNER", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(action));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            NestedArrayInputRoot selected = new NestedArrayInputRoot();
            NestedArrayInputRoot unrelated = new NestedArrayInputRoot();
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            ConcolicRegionRuntime.symbolizeArgument(token, 0, selected, "");
            assertEquals("entry registration must not symbolize the leaf", 0,
                    DelayedExpressionEngine.SYMBOLIC_ARRAY_IDS.size());
            ConcolicRegionRuntime.prepareFieldMaterialization(root, 13,
                    unrelated.payload, leafSignature, "values");
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray(
                    "engineArrayInputBindings").size());
            assertEquals(0, row.getAsJsonArray("symbolizedInputs").size());
            assertTrue(row.getAsJsonArray("unresolvedInputs").toString()
                    .contains(
                            "ARRAY_VALUE_CONSUMED_OWNER_AUTHORITY_MISSING"));
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void directConsumedFieldUsesExactGetfieldBaseAsInputOwner()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.DirectArrayLeaf: void run()>";
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.DIRECT", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(consumedFieldAction(
                engineArrayFieldAction("REGION.ARRAY.in.direct",
                        engineArrayAccessFieldSignature(),
                        "accessedValues", "HEAP_OBJECT_FIELD"),
                root, 17,
                "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1")));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            EngineArrayInputOwner owner = new EngineArrayInputOwner();
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            ConcolicRegionRuntime.prepareFieldMaterialization(root, 17,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues");
            Current[] consumed = owner.accessedValues;
            ConcolicRegionRuntime.materializeConsumedField(root, 17,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues", consumed);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
            assertEquals("[\"REGION.ARRAY.in.direct\"]",
                    row.getAsJsonArray("symbolizedInputs").toString());
            assertTrue(row.getAsJsonArray("engineArrayInputBindings")
                    .get(0).getAsJsonObject().get("complete")
                    .getAsBoolean());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void consumedArrayFieldReadsExactDeclaringOwnerWhenSubclassHidesName()
            throws Exception {
        JsonObject row = runHiddenConsumedArrayField(false);
        assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
        assertEquals(1, row.getAsJsonArray(
                "engineArrayInputBindings").size());
        assertTrue(row.getAsJsonArray("engineArrayInputBindings").get(0)
                .getAsJsonObject().get("complete").getAsBoolean());
    }

    @Test
    public void consumedArrayFieldRejectsSubclassHiddenFieldForBaseSignature()
            throws Exception {
        JsonObject row = runHiddenConsumedArrayField(true);
        assertEquals(0, row.getAsJsonArray(
                "engineArrayInputBindings").size());
        assertTrue(row.getAsJsonArray("unresolvedInputs").toString(),
                row.getAsJsonArray("unresolvedInputs").toString().contains(
                        "ARRAY_VALUE_PREPARED_CONSUMED_REFERENCE_MISMATCH"));
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
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.HIDDEN."
                        + (consumeSubclassField ? "REJECT" : "EXACT"),
                root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
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
                    new Object());
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

    @Test
    public void localDefinitionRegistersNestedArrayLogicalRoot()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.LocalArrayLeaf: void run()>";
        JsonObject action = engineArrayFieldAction(
                "REGION.ARRAY.in.local",
                engineArrayAccessFieldSignature(), "accessedValues",
                "FIELD");
        action.addProperty("cell", root + "::carrier");
        action.addProperty("method", root);
        action.addProperty("local", "carrier");
        action.addProperty("bindingMode", "LOCAL_DEFINITION");
        consumedFieldAction(action, root, 19,
                "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_AND_"
                        + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY");
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.LOCAL", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(action));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            EngineArrayInputOwner owner = new EngineArrayInputOwner();
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
            assertSame(owner, ConcolicRegionRuntime.materializeReference(
                    root, "carrier", owner));
            assertEquals("carrier registration must not symbolize the leaf",
                    0, DelayedExpressionEngine.SYMBOLIC_ARRAY_IDS.size());
            ConcolicRegionRuntime.prepareFieldMaterialization(root, 19,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues");
            Current[] consumed = owner.accessedValues;
            ConcolicRegionRuntime.materializeConsumedField(root, 19,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues", consumed);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
            assertEquals("[\"REGION.ARRAY.in.local\"]",
                    row.getAsJsonArray("symbolizedInputs").toString());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void consumedFieldArraySurvivesReplacementAfterRealGetfield()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.ArrayMutation: void run()>";
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.FIELD.MUTATION", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(consumedFieldAction(
                engineArrayFieldAction(
                "REGION.ARRAY.in.mutable",
                engineArrayAccessFieldSignature(), "accessedValues",
                "HEAP_OBJECT_FIELD"), root, 9,
                "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                        + "PATH_PREFIX_REFERENCE_EQUALITY")));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            EngineArrayInputOwner owner = new EngineArrayInputOwner();
            Current[] original = owner.accessedValues;
            Current[] replacement = {new Current(), new Current()};
            long token = ConcolicRegionRuntime.enterRegion(root, owner);
            DelayedExpressionEngine.arrayFieldMutationOwner = owner;
            DelayedExpressionEngine.arrayFieldMutationName =
                    "accessedValues";
            DelayedExpressionEngine.arrayFieldMutationReplacement =
                    replacement;
            ConcolicRegionRuntime.prepareFieldMaterialization(root, 9,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues");
            Current[] consumed = owner.accessedValues;
            ConcolicRegionRuntime.materializeConsumedField(root, 9,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues", consumed);
            assertSame(replacement, owner.accessedValues);
            assertNotSame(original, owner.accessedValues);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            JsonObject binding = row.getAsJsonArray(
                    "engineArrayInputBindings").get(0).getAsJsonObject();
            assertTrue(binding.get("fieldPrePostReferenceVerified")
                    .getAsBoolean());
            assertTrue(binding.get("sameArrayObjectTokenVerified")
                    .getAsBoolean());
            assertEquals(binding.get("arrayObjectToken").getAsLong(),
                    binding.get("postReadArrayObjectToken").getAsLong());
            assertTrue(binding.get("complete").getAsBoolean());
            assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
        } finally {
            restorePlan(old);
            ConcolicRegionRuntime.resetForTests();
            DelayedExpressionEngine.reset();
            folder.delete();
        }
    }

    @Test
    public void consumedFieldArrayRejectsReplacementBeforeRealGetfield()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = "<example.ArrayPreReadMutation: void run()>";
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.FIELD.PRE.READ.MUTATION", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(consumedFieldAction(
                engineArrayFieldAction(
                "REGION.ARRAY.in.pre.read.mutable",
                engineArrayAccessFieldSignature(), "accessedValues",
                "HEAP_OBJECT_FIELD"), root, 10,
                "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                        + "PATH_PREFIX_REFERENCE_EQUALITY")));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));

        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            EngineArrayInputOwner owner = new EngineArrayInputOwner();
            Current[] original = owner.accessedValues;
            Current[] replacement = {new Current(), new Current()};
            long token = ConcolicRegionRuntime.enterRegion(root, owner);
            ConcolicRegionRuntime.prepareFieldMaterialization(root, 10,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues");
            owner.accessedValues = replacement;
            Current[] consumed = owner.accessedValues;
            assertNotSame(original, consumed);
            ConcolicRegionRuntime.materializeConsumedField(root, 10,
                    owner, engineArrayAccessFieldSignature(),
                    "accessedValues", consumed);
            ConcolicRegionRuntime.exitRegion(token, null, "");

            JsonObject row = resultRows(results).get(0);
            assertEquals(0, row.getAsJsonArray(
                    "engineArrayInputBindings").size());
            assertEquals(0, row.getAsJsonArray("symbolizedInputs").size());
            assertTrue(row.getAsJsonArray("unresolvedInputs").toString()
                    .contains(
                            "ARRAY_VALUE_PREPARED_CONSUMED_REFERENCE_MISMATCH"));
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
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.FAIL." + expressionMode, root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
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
                    new Object());
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
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.PRIMITIVE.ARRAY." + mode, root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
        addExecutableActions(activation, singleton(action));
        Files.write(plan, (activation + "\n").getBytes(
                StandardCharsets.UTF_8));
        String[] old = installPlan(plan, results, "mock-symbolic-test");
        try {
            DelayedExpressionEngine.reset();
            ConcolicRegionRuntime.installEngineApiForTests(
                    DelayedExpressionEngine.class);
            long token = ConcolicRegionRuntime.enterRegion(root,
                    new Object());
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
        JsonObject activation = concreteActivation(
                "ACT.ENGINE.ARRAY.ID.COLLISION", root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", false);
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
                    new Object());
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
        action.addProperty("consumedFieldSiteId",
                method + "#u" + unitIndex);
        action.addProperty("consumedFieldSiteAuthority",
                "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_OWNER_"
                        + "WITHIN_REGION_INSTANCE_V1");
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

    @Test
    public void symbolizesFiniteMapValuesAtEntryAndVerifiesExactOutputIndex()
            throws Exception {
        JsonObject row = runMapProjectionRuntimeCase(
                "ACT.MAP.PROJECTION.OK",
                "ROOT_RETURN_PROJECTED_FIELD", "IDENTICAL", null,
                false, true);

        assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
        JsonArray bindings = row.getAsJsonArray("dynamicFieldBindings");
        assertEquals(3, bindings.size());
        for (int index = 0; index < bindings.size(); index++) {
            JsonObject binding = bindings.get(index).getAsJsonObject();
            assertEquals(3, binding.get("schemaVersion").getAsInt());
            assertEquals(
                    "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING",
                    binding.get("kind").getAsString());
            assertEquals(mapProjectionElementFieldSignature(),
                    binding.get("fieldSignature").getAsString());
            assertEquals("[\"expiryDate\"]",
                    binding.getAsJsonArray("fieldPath").toString());
            assertTrue(binding.get("complete").getAsBoolean());
            assertEquals("ACT.MAP.PROJECTION.OK",
                    binding.get("objectTokenScope").getAsString());
            JsonObject selector = binding.getAsJsonObject(
                    "mapProjectionSelector");
            assertEquals(index, selector.get("outputIndex").getAsInt());
            assertEquals(index + 1,
                    selector.get("elementOccurrence").getAsInt());
            assertEquals(mapProjectionElementFieldSignature(),
                    selector.get("declaredFieldSignature").getAsString());
            assertEquals("ACT.MAP.PROJECTION.OK",
                    selector.get("objectTokenScope").getAsString());
            assertEquals("NONE", selector.get(
                    "crossExecutionOrdinalAuthority").getAsString());
            assertEquals("Y_I_" + (index + 1), selector.getAsJsonObject(
                    "expectedMapKey").get("_exp").getAsString());
            assertEquals(
                    "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT",
                    selector.get("expectedMapKeyAuthority").getAsString());
            assertEquals(
                    "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                            + "POSITIONAL_REFERENCE_EQUALITY",
                    selector.get("sourceOutputIndexAuthority").getAsString());
            assertEquals(
                    "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_"
                            + "EXACT_OUTPUT_IDENTITY",
                    selector.get("replaySelectionAuthority").getAsString());
            assertTrue(selector.get("outputIdentityVerified")
                    .getAsBoolean());
            assertEquals("java.util.LinkedHashMap", selector.get(
                    "mapImplementationClass").getAsString());
            assertEquals("EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_"
                            + "LINKEDHASHMAP_JAVA_EQUALS_HASHCODE_"
                            + "EXTENSIONAL_V1",
                    selector.get("mapImplementationAuthority")
                            .getAsString());
            assertTrue(selector.get("entryConcreteFieldValueCaptured")
                    .getAsBoolean());
            assertTrue(selector.get("noInterveningFieldWriteVerified")
                    .getAsBoolean());
            assertTrue(selector.get("outputFieldValueVerified")
                    .getAsBoolean());
            assertTrue(selector.get("outputArrayObjectToken").getAsLong()
                    > 0L);
        }

        JsonArray observations = row.getAsJsonArray(
                "mapValueElementProjectionObservations");
        assertEquals(2, observations.size());
        JsonObject entry = observations.get(0).getAsJsonObject();
        assertEquals("ENTRY_SNAPSHOT", entry.get("phase").getAsString());
        assertTrue(entry.get("entrySetViewOrderVerified").getAsBoolean());
        assertEquals(3, entry.getAsJsonArray(
                "snapshotEntryKeyExpressions").size());
        assertEquals(
                "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                        + "POSITIONAL_REFERENCE_EQUALITY",
                entry.get("entrySetViewOrderAuthority").getAsString());
        JsonObject output = observations.get(1).getAsJsonObject();
        assertEquals("OUTPUT_IDENTITY_VALIDATION",
                output.get("phase").getAsString());
        assertTrue(output.get("outputDeclaredFieldOwnerVerified")
                .getAsBoolean());
        assertTrue(output.get("outputDeclaredFieldTypeVerified")
                .getAsBoolean());
        assertTrue(output.get("outputIdentityVerified").getAsBoolean());
        assertTrue(output.get("outputFieldValueFlowVerified")
                .getAsBoolean());
        assertTrue(output.get("complete").getAsBoolean());

        JsonObject mapInput = row.getAsJsonArray(
                "runtimeHeapObservations").get(0).getAsJsonObject();
        assertEquals("MAP_STATE_INPUT_OBSERVATION",
                mapInput.get("kind").getAsString());
        assertTrue(mapInput.get("identityBindingComplete").getAsBoolean());
        assertTrue(mapInput.get("snapshotComplete").getAsBoolean());
        assertFalse(mapInput.get("vmReferenceSymbolized").getAsBoolean());
        assertEquals(3, mapInput.get("entryCount").getAsInt());
        assertEquals(3, mapInput.getAsJsonArray("entries").size());
        assertEquals(1, row.getAsJsonArray("runtimeApproximations").size());
    }

    @Test
    public void mapProjectionRejectsCrossThreadExactFieldWriteButNotNoise()
            throws Exception {
        JsonObject written = runMapProjectionRuntimeCase(
                "ACT.MAP.PROJECTION.CROSS.THREAD.WRITE",
                "ROOT_RETURN_PROJECTED_FIELD", "CROSS_THREAD_WRITE", null);
        assertTrue(written.getAsJsonArray("unresolvedInputs").toString(),
                written.getAsJsonArray("unresolvedInputs").toString()
                        .contains("assigned or changed"));
        JsonObject failedSelector = written.getAsJsonArray(
                "dynamicFieldBindings").get(0).getAsJsonObject()
                .getAsJsonObject("mapProjectionSelector");
        assertFalse(failedSelector.get("noInterveningFieldWriteVerified")
                .getAsBoolean());
        assertFalse(failedSelector.get("outputFieldValueVerified")
                .getAsBoolean());

        JsonObject noise = runMapProjectionRuntimeCase(
                "ACT.MAP.PROJECTION.CROSS.THREAD.NOISE",
                "ROOT_RETURN_PROJECTED_FIELD", "CROSS_THREAD_NOISE", null);
        assertEquals(noise.toString(), 0,
                noise.getAsJsonArray("unresolvedInputs").size());
        for (JsonElement element : noise.getAsJsonArray(
                "dynamicFieldBindings")) {
            JsonObject selector = element.getAsJsonObject()
                    .getAsJsonObject("mapProjectionSelector");
            assertTrue(selector.get("noInterveningFieldWriteVerified")
                    .getAsBoolean());
        }
    }

    @Test
    public void mapProjectionAcceptsExactHashMapAndRejectsIdentityMap()
            throws Exception {
        JsonObject hash = runMapProjectionRuntimeCase(
                "ACT.MAP.PROJECTION.HASH", "ROOT_RETURN_PROJECTED_FIELD",
                "HASH_MAP", null);
        assertEquals(hash.toString(), 0,
                hash.getAsJsonArray("unresolvedInputs").size());
        assertEquals("java.util.HashMap", hash.getAsJsonArray(
                "dynamicFieldBindings").get(0).getAsJsonObject()
                .getAsJsonObject("mapProjectionSelector").get(
                "mapImplementationClass").getAsString());

        JsonObject identity = runMapProjectionRuntimeCase(
                "ACT.MAP.PROJECTION.IDENTITY", "ROOT_RETURN_PROJECTED_FIELD",
                "IDENTITY_MAP", null);
        assertEquals(0, identity.getAsJsonArray(
                "dynamicFieldBindings").size());
        assertTrue(identity.getAsJsonArray("unresolvedInputs").toString(),
                identity.getAsJsonArray("unresolvedInputs").toString()
                        .contains("exact runtime class"));
    }

    @Test
    public void mapProjectionRejectsShadowedNameAndKeySetSchema3()
            throws Exception {
        JsonObject shadow = runMapProjectionRuntimeCase(
                "ACT.MAP.PROJECTION.SHADOW", "ROOT_RETURN_PROJECTED_FIELD",
                "SHADOW_FIELD", null);
        assertEquals(0, shadow.getAsJsonArray(
                "dynamicFieldBindings").size());
        assertTrue(shadow.getAsJsonArray("unresolvedInputs").toString(),
                shadow.getAsJsonArray("unresolvedInputs").toString()
                        .contains("cannot uniquely resolve"));

        JsonObject keySet = runMapProjectionRuntimeCase(
                "ACT.MAP.PROJECTION.KEYSET", "ROOT_RETURN_PROJECTED_FIELD",
                "KEY_SET_VIEW", null);
        assertEquals(0, keySet.getAsJsonArray(
                "dynamicFieldBindings").size());
        assertTrue(keySet.getAsJsonArray("unresolvedInputs").toString(),
                keySet.getAsJsonArray("unresolvedInputs").toString()
                        .contains("unsupported map projection operation"));
    }

    @Test
    public void mapProjectionFailsClosedWhenOutputArrayIsNotEntrySnapshot()
            throws Exception {
        for (String mutation : Arrays.asList(
                "REVERSED", "SHORTER", "REPLACED_IDENTITY")) {
            JsonObject row = runMapProjectionRuntimeCase(
                    "ACT.MAP.PROJECTION." + mutation,
                    "ROOT_RETURN_PROJECTED_FIELD", mutation, null);
            assertTrue(mutation, row.getAsJsonArray("unresolvedInputs")
                    .toString().contains("output"));
            JsonArray bindings = row.getAsJsonArray(
                    "dynamicFieldBindings");
            assertEquals(3, bindings.size());
            for (JsonElement element : bindings) {
                JsonObject binding = element.getAsJsonObject();
                assertFalse(mutation,
                        binding.get("complete").getAsBoolean());
                assertFalse(mutation, binding.getAsJsonObject(
                        "mapProjectionSelector").get(
                        "outputIdentityVerified").getAsBoolean());
            }
            JsonArray observations = row.getAsJsonArray(
                    "mapValueElementProjectionObservations");
            JsonObject verification = observations.get(
                    observations.size() - 1).getAsJsonObject();
            assertFalse(mutation,
                    verification.get("complete").getAsBoolean());
            assertTrue(mutation, verification.has("problem"));
        }
    }

    @Test
    public void exactMapProjectionCaptureIsRequiredAndCannotUseRootReturn()
            throws Exception {
        JsonObject row = runMapProjectionRuntimeCase(
                "ACT.MAP.PROJECTION.MISSING.CAPTURE",
                "EXACT_REQUESTED_OUTPUT_CAPTURE", "IDENTICAL", null);

        assertTrue(row.getAsJsonArray("unresolvedInputs").toString()
                .contains("required exact output capture hook was not "
                        + "observed"));
        for (JsonElement element : row.getAsJsonArray(
                "dynamicFieldBindings")) {
            assertFalse(element.getAsJsonObject().get("complete")
                    .getAsBoolean());
        }
    }

    @Test
    public void mapProjectionModelRejectsDownstreamObjectTokenScope()
            throws Exception {
        String activationId = "ACT.MAP.PROJECTION.MODEL.SCOPE";
        JsonObject assignment = mapProjectionAssignment(
                "ACT.DOWNSTREAM.INSTANCE", 0, "99");
        JsonObject row = runMapProjectionRuntimeCase(activationId,
                "ROOT_RETURN_PROJECTED_FIELD", "IDENTICAL", assignment);

        assertEquals(0, row.getAsJsonArray(
                "modelAssignmentsApplied").size());
        assertFalse(row.get("allModelAssignmentsApplied").getAsBoolean());
        assertTrue(row.toString(), row.getAsJsonArray("unresolvedInputs")
                .toString().contains("keyed map/output selector"));
        JsonObject binding = row.getAsJsonArray("dynamicFieldBindings")
                .get(0).getAsJsonObject();
        assertEquals(activationId,
                binding.get("objectTokenScope").getAsString());
        assertFalse("an invalid replay selector invalidates the composed "
                        + "runtime projection evidence",
                binding.get("complete").getAsBoolean());
    }

    @Test
    public void concreteReplayAppliesExactMapProjectionModelWithoutVm()
            throws Exception {
        String activationId = "ACT.MAP.PROJECTION.CONCRETE.MODEL";
        JsonObject row = runMapProjectionRuntimeCase(activationId,
                "ROOT_RETURN_PROJECTED_FIELD", "IDENTICAL",
                mapProjectionAssignment(activationId, 0, "99"), true);
        assertEquals("CONCRETE_REPLAY_ONLY",
                row.get("executionMode").getAsString());
        assertEquals(1, row.getAsJsonArray(
                "modelAssignmentsApplied").size());
        assertTrue(row.get("allModelAssignmentsApplied").getAsBoolean());
        assertEquals(0, row.getAsJsonArray("symbolizedInputs").size());
        assertEquals(0, row.getAsJsonArray("unresolvedInputs").size());
        assertTrue(row.getAsJsonArray("dynamicFieldBindings").get(0)
                .getAsJsonObject().get("complete").getAsBoolean());
    }

    @Test
    public void concreteReplayRejectsWrongMapScopeAndOutputIdentity()
            throws Exception {
        String activationId = "ACT.MAP.PROJECTION.CONCRETE.REJECT";
        JsonObject wrongScope = runMapProjectionRuntimeCase(activationId,
                "ROOT_RETURN_PROJECTED_FIELD", "IDENTICAL",
                mapProjectionAssignment("ACT.OTHER", 0, "99"), true);
        assertEquals(0, wrongScope.getAsJsonArray(
                "modelAssignmentsApplied").size());
        assertTrue(wrongScope.getAsJsonArray("unresolvedInputs").toString()
                .contains("selector mismatch"));

        JsonObject wrongOutput = runMapProjectionRuntimeCase(
                activationId + ".OUTPUT",
                "ROOT_RETURN_PROJECTED_FIELD", "REVERSED", null, true);
        assertTrue(wrongOutput.getAsJsonArray("unresolvedInputs").toString()
                .contains("output"));
        assertFalse(wrongOutput.getAsJsonArray("dynamicFieldBindings")
                .get(0).getAsJsonObject().get("complete").getAsBoolean());
    }

    @Test
    public void keyedMapReplayRejectsChangedLinkedHashMapOrder()
            throws Exception {
        String activationId = "ACT.MAP.PROJECTION.REORDERED.REPLAY";
        JsonObject row = runMapProjectionRuntimeCase(activationId,
                "ROOT_RETURN_PROJECTED_FIELD", "REORDERED_MAP",
                mapProjectionAssignment(activationId, 0, "99"), true);
        assertEquals(0, row.getAsJsonArray(
                "modelAssignmentsApplied").size());
        assertTrue(row.getAsJsonArray("unresolvedInputs").toString(),
                row.getAsJsonArray("unresolvedInputs").toString().contains(
                        "resolved to current index 1 but source output index "
                                + "was 0"));
        JsonObject entry = row.getAsJsonArray(
                "mapValueElementProjectionObservations").get(0)
                .getAsJsonObject();
        assertEquals(1, entry.get(
                "expectedMapKeyAssignmentCount").getAsInt());
        assertEquals(0, entry.get(
                "expectedMapKeyValidatedCount").getAsInt());
        assertFalse(entry.get(
                "expectedMapKeyAndSourceIndexValidated").getAsBoolean());
    }

    @Test
    public void mapProjectionRejectsFloatingPointEntryKey()
            throws Exception {
        JsonObject row = runMapProjectionRuntimeCase(
                "ACT.MAP.PROJECTION.FLOAT.KEY",
                "ROOT_RETURN_PROJECTED_FIELD", "FLOAT_KEY", null);
        assertEquals(0, row.getAsJsonArray(
                "dynamicFieldBindings").size());
        assertTrue(row.getAsJsonArray("unresolvedInputs").toString(),
                row.getAsJsonArray("unresolvedInputs").toString().contains(
                        "not an exact immutable boxed Z/B/C/S/I/J or String"));
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
            boolean concreteReplayOnly) throws Exception {
        return runMapProjectionRuntimeCase(activationId,
                outputValidationMode, mutation, assignment,
                concreteReplayOnly, false);
    }

    private static JsonObject runMapProjectionRuntimeCase(
            String activationId, String outputValidationMode,
            String mutation, JsonObject assignment,
            boolean concreteReplayOnly,
            boolean mapStateObservationOnly) throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        String root = mapProjectionRoot();
        JsonObject activation = concreteActivation(activationId, root, 1);
        activation.addProperty("test", "mock-symbolic-test");
        activation.addProperty("concreteReplayOnly", concreteReplayOnly);
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

            long token = ConcolicRegionRuntime.enterRegion(root, producer);
            assertTrue(token > 0L);
            ConcolicRegionRuntime.materializeField(root, 4, producer,
                    mapProjectionMapFieldSignature(), "values");

            // Assert this before output construction: symbols must be born at
            // producer entry, never synthesized by the output-capture hook.
            // Three recursive element-field symbols plus the existing
            // shallow backing-map field symbol.
            if (concreteReplayOnly) {
                assertEquals(0,
                        DelayedExpressionEngine.SYMBOLIC_FIELD_PREFIXES
                                .size());
            } else {
                boolean projectionRejectedAtEntry = Arrays.asList(
                        "FLOAT_KEY", "IDENTITY_MAP", "SHADOW_FIELD",
                        "KEY_SET_VIEW").contains(mutation);
                int mapReferenceSymbols = mapStateObservationOnly ? 0 : 1;
                assertEquals(projectionRejectedAtEntry
                                ? mapReferenceSymbols
                                : mapReferenceSymbols + 3,
                        DelayedExpressionEngine.SYMBOLIC_FIELD_PREFIXES
                                .size());
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
            }
            if (assignment != null && !concreteReplayOnly) {
                assertEquals("wrong-scope model must not mutate input", 11L,
                        first.expiryDate);
            }
            if (assignment != null && concreteReplayOnly
                    && "IDENTICAL".equals(mutation)
                    && activationId.equals(assignment.getAsJsonObject(
                    "mapProjectionSelector").get("objectTokenScope")
                    .getAsString())) {
                assertEquals(99L, first.expiryDate);
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
        declaration.addProperty("recursiveElementProjectionComposable",
                false);
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

    private static Thread concreteObserver(
            String root, String branchMethod, AtomicLong token,
            CountDownLatch entered, CountDownLatch release) {
        return new Thread(() -> {
            long value = ConcolicRegionRuntime.enterRegion(root, new Object());
            token.set(value);
            entered.countDown();
            try {
                release.await(5, TimeUnit.SECONDS);
                if (value > 0L) {
                    assertFalse(ConcolicRegionRuntime.resolveBranch(0L, 0L,
                            branchMethod, 8, "result != null", false));
                    ConcolicRegionRuntime.exitRegion(value, null, "");
                }
            } catch (InterruptedException exception) {
                Thread.currentThread().interrupt();
            }
        });
    }

    private static void runEntryFieldActivation(
            String root,
            java.util.LinkedHashMap<Integer, ExpiringValue> map,
            ExpiringValue target, boolean skipFirstEntry) {
        long token = ConcolicRegionRuntime.enterRegion(root, map);
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

    private static JsonObject concreteActivation(
            String id, String root, int ordinal) {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", id);
        activation.addProperty("regionId", "REGION.TEST");
        activation.addProperty("test", id.startsWith("ACT.MODEL")
                ? "concrete-model-test" : "concrete-overlap-test");
        activation.addProperty("rootMethod", root);
        activation.addProperty("invocationOrdinal", ordinal);
        activation.addProperty("replayable", true);
        activation.addProperty("concreteReplayOnly", true);
        activation.add("symbolize", new JsonArray());
        activation.add("materializations", new JsonArray());
        activation.add("modelAssignments", new JsonArray());
        activation.add("forcedBranches", new JsonArray());
        return activation;
    }

    private static void addExecutableActions(JsonObject activation,
                                             JsonArray actions) {
        activation.add("symbolize", actions.deepCopy());
        activation.add("materializations", actions);
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
        selector.addProperty("schema",
                RuntimeRegionPlanner.ROOT_ARGUMENT_SELECTOR_SCHEMA);
        selector.addProperty("authority",
                RuntimeRegionPlanner.ROOT_ARGUMENT_SELECTOR_AUTHORITY);
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
        activation.add("runtimeRootArgumentSelector", selector);
    }

    private static void addStableRootContext(
            JsonObject activation, String receiverRuntimeClass,
            String threadName, int ordinalWithinContext) {
        activation.addProperty("receiverRuntimeClass",
                receiverRuntimeClass);
        activation.addProperty("threadName", threadName);
        activation.addProperty("threadIdSelectionUsed", false);
        activation.addProperty("invocationOrdinalWithinContext",
                ordinalWithinContext);
        activation.addProperty("rootContextSelectionAuthority",
                RuntimeRegionPlanner.ROOT_CONTEXT_SELECTION_AUTHORITY);
    }

    private static void addLegacyRootArgumentSelector(
            JsonObject activation, int matchOrdinal,
            String... runtimeTypes) {
        JsonObject selector = new JsonObject();
        selector.addProperty("schema",
                RuntimeRegionPlanner.ROOT_ARGUMENT_SELECTOR_SCHEMA_V1);
        selector.addProperty("authority",
                RuntimeRegionPlanner.ROOT_ARGUMENT_SELECTOR_AUTHORITY_V1);
        selector.addProperty("matchOrdinal", matchOrdinal);
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
        activation.add("runtimeRootArgumentSelector", selector);
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
        container.addProperty("accessOwnerClass",
                GenericArrayEnvelope.class.getName());
        container.addProperty("accessField", "elements");
        container.addProperty("leafOwnerClass",
                GenericArrayEnvelope.class.getName());
        container.addProperty("leafField", "elements");
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
        elementField.addProperty("accessOwnerClass",
                Current.class.getName());
        elementField.addProperty("accessField", "id");
        elementField.addProperty("leafOwnerClass",
                Current.class.getName());
        elementField.addProperty("leafField", "id");
        elementField.add("fieldPath", JsonParser.parseString("[\"id\"]"));
        actions.add(elementField);
        return actions;
    }

    private static JsonObject genericArrayBinding(
            String bindingId, String baseSymbol, String containerSymbol,
            String selectorAuthority, int elementIndex,
            int elementOccurrence, String fieldMaterializationSiteId) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "ARRAY_ELEMENT_FIELD");
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
        binding.addProperty("declaredFieldOwnerClass",
                Current.class.getName());
        binding.addProperty("declaredFieldType", "int");
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
        selector.addProperty("declaredFieldOwnerClass",
                Current.class.getName());
        selector.addProperty("declaredFieldType", "int");
        assignment.add("containerSelector", selector);
        assignment.addProperty("containerReplayRebindingAuthority",
                "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                        + "IDENTITY_REBIND_V1");
        assignment.addProperty("sourceContainerObjectTokensRetained",
                false);
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
        long token = ConcolicRegionRuntime.enterRegion(root, envelope);
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

    private static JsonObject concreteIntegerExpression(int value) {
        JsonObject expression = new JsonObject();
        expression.addProperty("kind", "CONCRETE_RUNTIME_VALUE");
        expression.addProperty("symbolic", false);
        expression.addProperty("valueType", Integer.class.getName());
        expression.addProperty("value", value);
        return expression;
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

    private static String[] installPlan(Path plan, Path results, String test) {
        String[] old = {
                System.getProperty("causynth.concolic.activation.plan"),
                System.getProperty("causynth.concolic.activation.id"),
                System.getProperty("causynth.concolic.results"),
                System.getProperty("causynth.trace.test")};
        System.setProperty("causynth.concolic.activation.plan", plan.toString());
        System.clearProperty("causynth.concolic.activation.id");
        System.setProperty("causynth.concolic.results", results.toString());
        System.setProperty("causynth.trace.test", test);
        ConcolicRegionRuntime.resetForTests();
        return old;
    }

    private static void restorePlan(String[] old) {
        restore("causynth.concolic.activation.plan", old[0]);
        restore("causynth.concolic.activation.id", old[1]);
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
