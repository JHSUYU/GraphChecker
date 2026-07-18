package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.LongType;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.ArrayRef;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.LongConstant;
import soot.jimple.NewArrayExpr;
import soot.jimple.Stmt;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

public class CausynthPipelineTest {
    private String previousTraceInstrumentation;
    private String previousConcolicInstrumentation;
    private String previousActivationPlan;
    private String previousActivationId;
    private String previousRuntimeCallEdges;

    @Before
    public void rememberSystemProperties() {
        previousTraceInstrumentation =
                System.getProperty("causynth.instrument.trace");
        previousConcolicInstrumentation =
                System.getProperty("causynth.instrument.concolic");
        previousActivationPlan =
                System.getProperty("causynth.concolic.activation.plan");
        previousActivationId =
                System.getProperty("causynth.concolic.activation.id");
        previousRuntimeCallEdges =
                System.getProperty("causynth.runtime.call.edges");
    }

    @After
    public void resetSoot() {
        restoreProperty("causynth.instrument.trace",
                previousTraceInstrumentation);
        restoreProperty("causynth.instrument.concolic",
                previousConcolicInstrumentation);
        restoreProperty("causynth.concolic.activation.plan",
                previousActivationPlan);
        restoreProperty("causynth.concolic.activation.id",
                previousActivationId);
        restoreProperty("causynth.runtime.call.edges",
                previousRuntimeCallEdges);
        G.reset();
    }

    @Test
    public void projectedMethodResultUsesObservedConcreteFieldOwner() {
        JsonObject action = new JsonObject();
        action.addProperty("cell",
                "<example.Source: example.Keys getKeys()>.return"
                        + "#field:allKeys");
        action.addProperty("field",
                "<example.Manager: java.util.Map allKeys>");
        action.addProperty("accessField", "allKeys");
        JsonArray path = new JsonArray();
        path.add("allKeys");
        action.add("fieldPath", path);

        String[] target = CausynthPipeline.resolveConcolicFieldTarget(action);

        assertEquals("example.Manager", target[0]);
        assertEquals("allKeys", target[1]);

        action.remove("field");
        action.addProperty("accessOwnerClass", "   ");
        target = CausynthPipeline.resolveConcolicFieldTarget(action);
        assertEquals("", target[0]);
        assertEquals("allKeys", target[1]);
    }

    @Test
    public void arrayFieldReadUsesOneExactConsumedLocalAtNestedLeaf()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            G.reset();
            SootClass object = new SootClass("java.lang.Object",
                    Modifier.PUBLIC);
            Scene.v().addClass(object);
            SootClass nested = new SootClass("example.ArrayNested",
                    Modifier.PUBLIC);
            Scene.v().addClass(nested);
            SootField values = new SootField("values",
                    ArrayType.v(RefType.v("java.lang.Object"), 1),
                    Modifier.PUBLIC);
            nested.addField(values);
            SootClass root = new SootClass("example.ArrayRoot",
                    Modifier.PUBLIC);
            Scene.v().addClass(root);
            SootField child = new SootField("child",
                    RefType.v(nested.getName()), Modifier.PUBLIC);
            root.addField(child);

            SootClass region = new SootClass("example.ArrayRegion",
                    Modifier.PUBLIC);
            Scene.v().addClass(region);
            region.setApplicationClass();
            SootMethod method = new SootMethod("read",
                    Arrays.asList(RefType.v(root.getName()),
                            RefType.v(nested.getName())),
                    ArrayType.v(RefType.v("java.lang.Object"), 1),
                    Modifier.PUBLIC | Modifier.STATIC);
            region.addMethod(method);
            Body body = Jimple.v().newBody(method);
            method.setActiveBody(body);
            Local rootLocal = Jimple.v().newLocal("root",
                    RefType.v(root.getName()));
            Local childLocal = Jimple.v().newLocal("child",
                    RefType.v(nested.getName()));
            Local unrelated = Jimple.v().newLocal("unrelated",
                    RefType.v(nested.getName()));
            Local ignored = Jimple.v().newLocal("ignored",
                    ArrayType.v(RefType.v("java.lang.Object"), 1));
            Local result = Jimple.v().newLocal("result",
                    ArrayType.v(RefType.v("java.lang.Object"), 1));
            body.getLocals().add(rootLocal);
            body.getLocals().add(childLocal);
            body.getLocals().add(unrelated);
            body.getLocals().add(ignored);
            body.getLocals().add(result);
            body.getUnits().add(Jimple.v().newIdentityStmt(rootLocal,
                    Jimple.v().newParameterRef(rootLocal.getType(), 0)));
            body.getUnits().add(Jimple.v().newIdentityStmt(unrelated,
                    Jimple.v().newParameterRef(unrelated.getType(), 1)));
            AssignStmt readUnrelated = Jimple.v().newAssignStmt(ignored,
                    Jimple.v().newInstanceFieldRef(unrelated,
                            values.makeRef()));
            AssignStmt readChild = Jimple.v().newAssignStmt(childLocal,
                    Jimple.v().newInstanceFieldRef(rootLocal,
                            child.makeRef()));
            AssignStmt readValues = Jimple.v().newAssignStmt(result,
                    Jimple.v().newInstanceFieldRef(childLocal,
                            values.makeRef()));
            body.getUnits().add(readUnrelated);
            body.getUnits().add(readChild);
            body.getUnits().add(readValues);
            body.getUnits().add(Jimple.v().newReturnStmt(result));

            Path plan = folder.getRoot().toPath().resolve(
                    "array-field-activation.jsonl");
            JsonObject activation = new JsonObject();
            activation.addProperty("activationId", "ACT.ARRAY.FIELD");
            activation.addProperty("replayable", true);
            JsonObject action = new JsonObject();
            action.addProperty("symbol", "REGION.ARRAY.in.0");
            action.addProperty("bindingMode", "ROOT_ENTRY");
            action.addProperty("location", "ARGUMENT_FIELD_PATH");
            action.addProperty("index", 0);
            action.addProperty("cell", child.getSignature()
                    + "#field:values");
            action.addProperty("field", values.getSignature());
            action.addProperty("accessOwnerClass", root.getName());
            action.addProperty("accessField", child.getName());
            action.addProperty("accessFieldSignature", child.getSignature());
            action.addProperty("leafField", values.getName());
            action.addProperty("leafOwnerClass", nested.getName());
            action.addProperty("leafFieldSignature", values.getSignature());
            action.addProperty("javaType", "java.lang.Object[]");
            action.addProperty("consumedFieldMethod", method.getSignature());
            action.addProperty("consumedFieldUnitIndex", 4);
            action.addProperty("consumedFieldSiteId",
                    method.getSignature() + "#u4");
            action.addProperty("consumedFieldSiteAuthority",
                    "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_"
                            + "OWNER_WITHIN_REGION_INSTANCE_V1");
            action.addProperty("consumedFieldBindingComplete", true);
            action.addProperty("consumedFieldOccurrence", 1);
            action.addProperty("consumedFieldOccurrenceAuthority",
                    "UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1");
            action.addProperty("consumedFieldRootAuthority",
                    "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_"
                            + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY");
            JsonArray fieldPath = new JsonArray();
            fieldPath.add(child.getName());
            fieldPath.add(values.getName());
            JsonArray fieldPaths = new JsonArray();
            fieldPaths.add(fieldPath.deepCopy());
            action.add("fieldPaths", fieldPaths);
            JsonArray actions = new JsonArray();
            actions.add(action);
            activation.add("materializations", actions);
            Files.write(plan, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));

            Object selection = concolicMaterializationSelection(plan,
                    "ACT.ARRAY.FIELD");
            Object refs = concolicRegionRefs();
            assertEquals(1, instrumentConcolicMaterializations(selection,
                    refs));

            List<Unit> units = new ArrayList<>();
            for (Unit unit : body.getUnits()) units.add(unit);
            Unit exactGetField = null;
            Local consumed = null;
            Unit prepare = null;
            Unit post = null;
            int leafReads = 0;
            int intermediateReads = 0;
            int legacyHooks = 0;
            for (Unit unit : units) {
                if (unit instanceof AssignStmt
                        && ((AssignStmt) unit).getRightOp()
                        instanceof soot.jimple.InstanceFieldRef) {
                    soot.jimple.InstanceFieldRef field =
                            (soot.jimple.InstanceFieldRef) ((AssignStmt) unit)
                                    .getRightOp();
                    if (field.getFieldRef().getSignature().equals(
                            values.getSignature())) {
                        leafReads++;
                        Local destination = (Local) ((AssignStmt) unit)
                                .getLeftOp();
                        if (destination.getName().startsWith(
                                "$causynthConsumedArrayField")) {
                            exactGetField = unit;
                            consumed = destination;
                        }
                    } else if (field.getFieldRef().getSignature().equals(
                            child.getSignature())) {
                        intermediateReads++;
                    }
                }
                InvokeExpr invoke = invokeExpression(unit);
                if (invoke == null) continue;
                if ("prepareFieldMaterialization".equals(
                        invoke.getMethodRef().name())) {
                    prepare = unit;
                    assertEquals(values.getSignature(), invoke.getArg(3)
                            .toString().replace("\"", ""));
                    assertSame(childLocal, invoke.getArg(2));
                } else if ("materializeConsumedField".equals(
                        invoke.getMethodRef().name())) {
                    post = unit;
                    assertEquals(values.getSignature(), invoke.getArg(3)
                            .toString().replace("\"", ""));
                } else if ("materializeField".equals(
                        invoke.getMethodRef().name())) {
                    legacyHooks++;
                }
            }

            assertNotNull(prepare);
            assertNotNull(exactGetField);
            assertNotNull(consumed);
            assertNotNull(post);
            assertEquals("the unrelated same-class read remains the one raw "
                    + "getfield while only the selected site is split", 2,
                    leafReads);
            assertEquals(1, intermediateReads);
            assertEquals("nested path must not be materialized at its "
                    + "intermediate object field", 0, legacyHooks);
            assertSame(consumed, ((AssignStmt) readValues).getRightOp());
            assertTrue(readUnrelated.getRightOp()
                    instanceof soot.jimple.InstanceFieldRef);
            assertSame(consumed, invokeExpression(post).getArg(5));
            assertTrue(units.indexOf(prepare) < units.indexOf(exactGetField));
            assertTrue(units.indexOf(exactGetField) < units.indexOf(post));
            assertTrue(units.indexOf(post) < units.indexOf(readValues));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void selectedStaticArrayFieldFailsClosedDuringInstrumentation()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            G.reset();
            Scene.v().addClass(new SootClass("java.lang.Object",
                    Modifier.PUBLIC));
            SootClass holder = new SootClass("example.StaticArrayHolder",
                    Modifier.PUBLIC);
            Scene.v().addClass(holder);
            SootField values = new SootField("values",
                    ArrayType.v(RefType.v("java.lang.Object"), 1),
                    Modifier.PUBLIC | Modifier.STATIC);
            holder.addField(values);
            SootClass region = new SootClass("example.StaticArrayRegion",
                    Modifier.PUBLIC);
            Scene.v().addClass(region);
            region.setApplicationClass();
            SootMethod method = new SootMethod("read",
                    Collections.emptyList(),
                    ArrayType.v(RefType.v("java.lang.Object"), 1),
                    Modifier.PUBLIC | Modifier.STATIC);
            region.addMethod(method);
            Body body = Jimple.v().newBody(method);
            method.setActiveBody(body);
            Local result = Jimple.v().newLocal("result",
                    ArrayType.v(RefType.v("java.lang.Object"), 1));
            body.getLocals().add(result);
            body.getUnits().add(Jimple.v().newAssignStmt(result,
                    Jimple.v().newStaticFieldRef(values.makeRef())));
            body.getUnits().add(Jimple.v().newReturnStmt(result));

            Path plan = folder.getRoot().toPath().resolve(
                    "static-array-field-activation.jsonl");
            JsonObject activation = new JsonObject();
            activation.addProperty("activationId", "ACT.STATIC.ARRAY");
            activation.addProperty("replayable", true);
            JsonObject action = new JsonObject();
            action.addProperty("symbol", "REGION.STATIC.in.0");
            action.addProperty("bindingMode", "FIELD_ACCESS");
            action.addProperty("location", "HEAP_OBJECT_FIELD");
            action.addProperty("cell", values.getSignature());
            action.addProperty("field", values.getSignature());
            action.addProperty("accessOwnerClass", holder.getName());
            action.addProperty("accessField", values.getName());
            action.addProperty("leafField", values.getName());
            action.addProperty("leafFieldSignature", values.getSignature());
            action.addProperty("javaType", "java.lang.Object[]");
            action.addProperty("consumedFieldMethod", method.getSignature());
            action.addProperty("consumedFieldUnitIndex", 0);
            action.addProperty("consumedFieldSiteId",
                    method.getSignature() + "#u0");
            action.addProperty("consumedFieldSiteAuthority",
                    "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_"
                            + "OWNER_WITHIN_REGION_INSTANCE_V1");
            action.addProperty("consumedFieldBindingComplete", true);
            action.addProperty("consumedFieldOccurrence", 1);
            action.addProperty("consumedFieldOccurrenceAuthority",
                    "UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1");
            action.addProperty("consumedFieldRootAuthority",
                    "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1");
            JsonArray fieldPath = new JsonArray();
            fieldPath.add(values.getName());
            action.add("fieldPath", fieldPath);
            JsonArray actions = new JsonArray();
            actions.add(action);
            activation.add("materializations", actions);
            Files.write(plan, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));

            Object selection = concolicMaterializationSelection(plan,
                    "ACT.STATIC.ARRAY");
            try {
                instrumentConcolicMaterializations(selection,
                        concolicRegionRefs());
                throw new AssertionError("static ARRAY_VALUE field must fail "
                        + "closed");
            } catch (InvocationTargetException expected) {
                assertTrue(expected.getCause() instanceof IllegalStateException);
                assertTrue(expected.getCause().getMessage().contains(
                        "STATIC_FIELD_MATERIALIZATION_UNSUPPORTED"));
                assertTrue(expected.getCause().getMessage().contains(
                        values.getSignature()));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void arrayLeafRootAuthorityFollowsRootBindingNotPathLength()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            G.reset();
            Scene.v().addClass(new SootClass("java.lang.Object",
                    Modifier.PUBLIC));
            SootClass holder = new SootClass("example.AuthorityHolder",
                    Modifier.PUBLIC);
            Scene.v().addClass(holder);
            SootField values = new SootField("values",
                    ArrayType.v(RefType.v("java.lang.Object"), 1),
                    Modifier.PUBLIC);
            holder.addField(values);
            String method = "<example.AuthorityRegion: "
                    + "java.lang.Object[] read(example.AuthorityHolder)>";
            int unitIndex = 7;

            List<JsonObject> accepted = Arrays.asList(
                    exactArrayLeafAction(method, unitIndex,
                            "ROOT_ENTRY", "ARGUMENT_FIELD_PATH",
                            "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_"
                                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY",
                            values, Collections.singletonList("values")),
                    exactArrayLeafAction(method, unitIndex,
                            "ROOT_ENTRY", "RECEIVER_FIELD",
                            "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_"
                                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY",
                            values, Collections.singletonList("values")),
                    exactArrayLeafAction(method, unitIndex,
                            "FIELD_ACCESS", "HEAP_OBJECT_FIELD",
                            "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_"
                                    + "OWNER_V1",
                            values, Collections.singletonList("values")),
                    exactArrayLeafAction(method, unitIndex,
                            "FIELD_ACCESS", "HEAP_OBJECT_FIELD",
                            "ROOT_RECEIVER_IDENTITY_AT_REGION_ENTRY_AND_"
                                    + "LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY",
                            values, Collections.singletonList("values")),
                    exactArrayLeafAction(method, unitIndex,
                            "LOCAL_DEFINITION", "REGION_LIVE_IN",
                            "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_"
                                    + "SITE_AND_LOGICAL_PATH_PREFIX_"
                                    + "REFERENCE_EQUALITY",
                            values, Arrays.asList("holder", "values")));

            Path plan = folder.getRoot().toPath().resolve(
                    "array-root-authorities.jsonl");
            for (int index = 0; index < accepted.size(); index++) {
                JsonObject activation = new JsonObject();
                String activationId = "ACT.ROOT." + index;
                activation.addProperty("activationId", activationId);
                activation.addProperty("replayable", true);
                JsonArray actions = new JsonArray();
                actions.add(accepted.get(index));
                activation.add("materializations", actions);
                Files.write(plan, (activation + "\n").getBytes(
                        StandardCharsets.UTF_8));
                Object selection = concolicMaterializationSelection(plan,
                        activationId);
                assertTrue("root authority case " + index
                                + " must select its exact leaf site",
                        concolicSelectionMatchesField(selection, method,
                                unitIndex, values));
            }

            JsonObject localWithoutDefinition = exactArrayLeafAction(method,
                    unitIndex, "LOCAL_DEFINITION", "REGION_LIVE_IN",
                    "LOCAL_DEFINITION_IDENTITY_AT_EXACT_DEFINITION_SITE_"
                            + "AND_LOGICAL_PATH_PREFIX_REFERENCE_EQUALITY",
                    values, Arrays.asList("holder", "values"));
            localWithoutDefinition.remove("definitionSites");
            JsonObject multipleDeclaredArrayPaths = exactArrayLeafAction(
                    method, unitIndex, "ROOT_ENTRY", "ARGUMENT_FIELD_PATH",
                    "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                            + "PATH_PREFIX_REFERENCE_EQUALITY",
                    values, Arrays.asList("left", "values"));
            multipleDeclaredArrayPaths.remove("javaType");
            multipleDeclaredArrayPaths.remove("field");
            multipleDeclaredArrayPaths.remove("leafFieldSignature");
            multipleDeclaredArrayPaths.remove("accessFieldSignature");
            multipleDeclaredArrayPaths.addProperty("cell", method
                    + ".param0:example.AuthorityHolder");
            JsonArray multiplePaths = new JsonArray();
            multiplePaths.add(JsonParser.parseString(
                    "[\"left\",\"values\"]"));
            multiplePaths.add(JsonParser.parseString(
                    "[\"right\",\"values\"]"));
            multipleDeclaredArrayPaths.add("fieldPaths", multiplePaths);
            JsonArray declarations = new JsonArray();
            for (String prefix : Arrays.asList("left", "right")) {
                JsonObject declaration = new JsonObject();
                declaration.add("fieldPath", JsonParser.parseString(
                        "[\"" + prefix + "\",\"values\"]"));
                declaration.addProperty("fieldSignature",
                        values.getSignature());
                declarations.add(declaration);
            }
            multipleDeclaredArrayPaths.add("fieldPathLeafDeclarations",
                    declarations);
            List<JsonObject> rejected = Arrays.asList(
                    exactArrayLeafAction(method, unitIndex,
                            "ROOT_ENTRY", "ARGUMENT_FIELD_PATH",
                            "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_"
                                    + "OWNER_V1",
                            values, Collections.singletonList("values")),
                    exactArrayLeafAction(method, unitIndex,
                            "FIELD_ACCESS", "HEAP_OBJECT_FIELD",
                            "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_"
                                    + "OWNER_V1",
                            values, Arrays.asList("holder", "values")),
                    localWithoutDefinition, multipleDeclaredArrayPaths);
            for (int index = 0; index < rejected.size(); index++) {
                JsonObject activation = new JsonObject();
                String activationId = "ACT.WRONG.ROOT." + index;
                activation.addProperty("activationId", activationId);
                activation.addProperty("replayable", true);
                JsonArray actions = new JsonArray();
                actions.add(rejected.get(index));
                activation.add("materializations", actions);
                Files.write(plan, (activation + "\n").getBytes(
                        StandardCharsets.UTF_8));
                try {
                    concolicMaterializationSelection(plan, activationId);
                    throw new AssertionError("invalid root authority case "
                            + index + " must fail closed");
                } catch (InvocationTargetException expected) {
                    assertTrue(expected.getCause()
                            instanceof java.io.IOException);
                    assertTrue(expected.getCause().getMessage().contains(
                            "ARRAY_VALUE_FIELD_REQUIRES_EXACT_LEAF_"
                                    + "DECLARATION_AND_CONSUMED_SITE"));
                }
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void arrayLeafRequiresCompleteUniqueRuntimeConsumedRead()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            G.reset();
            Scene.v().addClass(new SootClass("java.lang.Object",
                    Modifier.PUBLIC));
            SootClass holder = new SootClass(
                    "example.ConsumedReadAuthorityHolder",
                    Modifier.PUBLIC);
            Scene.v().addClass(holder);
            SootField values = new SootField("values",
                    ArrayType.v(RefType.v("java.lang.Object"), 1),
                    Modifier.PUBLIC);
            holder.addField(values);
            String method = "<example.ConsumedReadRegion: "
                    + "java.lang.Object[] read(" + holder.getName() + ")>";
            JsonObject missingComplete = exactArrayLeafAction(method, 3,
                    "ROOT_ENTRY", "ARGUMENT_FIELD_PATH",
                    "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                            + "PATH_PREFIX_REFERENCE_EQUALITY",
                    values, Collections.singletonList("values"));
            missingComplete.remove("consumedFieldBindingComplete");
            JsonObject missingOccurrence = exactArrayLeafAction(method, 3,
                    "ROOT_ENTRY", "ARGUMENT_FIELD_PATH",
                    "ROOT_ARGUMENT_IDENTITY_AT_REGION_ENTRY_AND_LOGICAL_"
                            + "PATH_PREFIX_REFERENCE_EQUALITY",
                    values, Collections.singletonList("values"));
            missingOccurrence.remove("consumedFieldOccurrence");

            Path plan = folder.getRoot().toPath().resolve(
                    "incomplete-consumed-read.jsonl");
            List<JsonObject> rejected = Arrays.asList(missingComplete,
                    missingOccurrence);
            for (int index = 0; index < rejected.size(); index++) {
                String activationId = "ACT.INCOMPLETE.CONSUMED." + index;
                JsonObject activation = new JsonObject();
                activation.addProperty("activationId", activationId);
                activation.addProperty("replayable", true);
                JsonArray actions = new JsonArray();
                actions.add(rejected.get(index));
                activation.add("materializations", actions);
                Files.write(plan, (activation + "\n").getBytes(
                        StandardCharsets.UTF_8));
                try {
                    concolicMaterializationSelection(plan, activationId);
                    throw new AssertionError("incomplete runtime consumed "
                            + "read evidence must fail closed: " + index);
                } catch (InvocationTargetException expected) {
                    assertTrue(expected.getCause()
                            instanceof java.io.IOException);
                    assertTrue(expected.getCause().getMessage().contains(
                            "ARRAY_VALUE_FIELD_REQUIRES_EXACT_LEAF_"
                                    + "DECLARATION_AND_CONSUMED_SITE"));
                }
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void replayInstrumentationUsesOnlyRuntimeSelectedReadyRoots()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path plan = folder.getRoot().toPath().resolve("activations.jsonl");
            String selectedRoot = "<example.RuntimeRoot: void handle()>";
            String rows = "{\"activationId\":\"ACT.0\","
                    + "\"rootMethod\":\"" + selectedRoot + "\","
                    + "\"replayable\":true,\"symbolicReady\":true}\n"
                    + "{\"activationId\":\"ACT.1\","
                    + "\"rootMethod\":\"<example.NotReady: void run()>\","
                    + "\"replayable\":true,\"symbolicReady\":false}\n"
                    + "{\"activationId\":\"ACT.2\","
                    + "\"rootMethod\":\"<example.NotReplayable: void run()>\","
                    + "\"replayable\":false,\"symbolicReady\":true}\n";
            Files.write(plan, rows.getBytes(StandardCharsets.UTF_8));

            Set<String> roots = CausynthPipeline.readRuntimeSelectedRoots(plan, "");

            assertEquals(Collections.singleton(selectedRoot), roots);
            assertEquals(Collections.singleton(selectedRoot),
                    CausynthPipeline.readRuntimeSelectedRoots(plan, "ACT.0"));
            assertEquals(Collections.emptySet(),
                    CausynthPipeline.readRuntimeSelectedRoots(plan, "ACT.1"));
        } finally {
            folder.delete();
        }
    }

    @Test(expected = java.io.IOException.class)
    public void replayInstrumentationCannotSelectOneMemberOfAllBundle()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path plan = folder.getRoot().toPath().resolve("bundle.jsonl");
            String row = "{\"activationId\":\"ACT.BUNDLE\","
                    + "\"rootMethod\":\"<example.Root: void run()>\","
                    + "\"replayable\":true,\"symbolicReady\":true,"
                    + "\"activationSelectionRequired\":\"ALL\"}\n";
            Files.write(plan, row.getBytes(StandardCharsets.UTF_8));
            CausynthPipeline.readRuntimeSelectedRoots(plan, "ACT.BUNDLE");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void boundedOutputClosureMayUseExactScopedCoverageAuthority()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path plan = folder.getRoot().toPath().resolve("bounded.jsonl");
            JsonObject row = readyBoundedOutputClosure("ACT.OUTPUT.0");
            // Broad static input coverage is intentionally not an authority
            // for a runtime-refined requested-output closure.
            row.addProperty("staticInputSelectionComplete", false);
            Files.write(plan, (row + "\n").getBytes(StandardCharsets.UTF_8));

            assertTrue(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            "ACT.OUTPUT.0"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void boundedOutputClosureMayUseExactSolverPathFlipAuthority()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path plan = folder.getRoot().toPath().resolve("flip.jsonl");
            JsonObject row = readySolverOutputPathFlip();
            Files.write(plan, (row + "\n").getBytes(StandardCharsets.UTF_8));

            assertTrue(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            "ACT.PATH.3a35b5ac15765178"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void boundedSolverPathFlipCoverageAuthorityFailsClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path plan = folder.getRoot().toPath().resolve("flip.jsonl");
            String activation = "ACT.PATH.3a35b5ac15765178";

            JsonObject stringBoolean = readySolverOutputPathFlip();
            stringBoolean.getAsJsonObject("targetBranch")
                    .addProperty("validationOnly", "true");
            writePlanRow(plan, stringBoolean);
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            activation));

            JsonObject mixedAuthority = readySolverOutputPathFlip();
            JsonObject composed = solverPathFlipAssignment(
                    "M_I_second", "sym__second", "REGION.15.in.33");
            composed.addProperty("authority",
                    "Z3_BOUNDED_COMPOSED_MODEL_PROJECTION");
            mixedAuthority.getAsJsonArray("modelAssignments").add(composed);
            writePlanRow(plan, mixedAuthority);
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            activation));

            JsonObject targetOverride = readySolverOutputPathFlip();
            targetOverride.getAsJsonObject("targetBranch")
                    .addProperty("branchOverrideAllowed", true);
            writePlanRow(plan, targetOverride);
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            activation));

            JsonObject topLevelOverride = readySolverOutputPathFlip();
            topLevelOverride.addProperty("branchOverrideAllowed", true);
            writePlanRow(plan, topLevelOverride);
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            activation));

            JsonObject forcedOverride = readySolverOutputPathFlip();
            JsonObject forced = new JsonObject();
            forced.addProperty("siteId", "<example.Manager: void add()>#u14");
            forcedOverride.add("forcedBranches", singletonJsonArray(forced));
            writePlanRow(plan, forcedOverride);
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            activation));

            JsonObject bundleMismatch = readySolverOutputPathFlip();
            bundleMismatch.addProperty("activationBundleRootActivationId",
                    "ACT.PATH.other");
            writePlanRow(plan, bundleMismatch);
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            activation));

            JsonObject scheduleMismatch = readySolverOutputPathFlip();
            scheduleMismatch.addProperty("scheduleId", "SCHEDULE.PATH.other");
            scheduleMismatch.addProperty("activationBundleScheduleId",
                    "SCHEDULE.PATH.other");
            writePlanRow(plan, scheduleMismatch);
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            activation));

            JsonObject queryMismatch = readySolverOutputPathFlip();
            queryMismatch.addProperty("pathQueryKey",
                    "d3577f7f5002a09920e54b51105590f1093a902d0fcf8bdee74ce4516109f7b3");
            writePlanRow(plan, queryMismatch);
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            activation));

            JsonObject malformedPrefix = readySolverOutputPathFlip();
            malformedPrefix.getAsJsonArray("expectedBranchPrefix")
                    .get(0).getAsJsonObject().addProperty("outcome", "true");
            writePlanRow(plan, malformedPrefix);
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            activation));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void boundedOutputClosureCoverageAuthorityFailsClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path plan = folder.getRoot().toPath().resolve("bounded.jsonl");

            JsonObject targetBranch = readyBoundedOutputClosure("ACT.BAD");
            targetBranch.getAsJsonObject("captureGoal")
                    .addProperty("kind", "TARGET_BRANCH");
            Files.write(plan, (targetBranch + "\n").getBytes(
                    StandardCharsets.UTF_8));
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            "ACT.BAD"));

            JsonObject incomplete = readyBoundedOutputClosure("ACT.BAD");
            incomplete.getAsJsonObject("requestedOutputSlice")
                    .addProperty("runtimeRefinementComplete", false);
            Files.write(plan, (incomplete + "\n").getBytes(
                    StandardCharsets.UTF_8));
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            "ACT.BAD"));

            JsonObject stringBoolean = readyBoundedOutputClosure("ACT.BAD");
            stringBoolean.addProperty("schedulerReady", "true");
            Files.write(plan, (stringBoolean + "\n").getBytes(
                    StandardCharsets.UTF_8));
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            "ACT.BAD"));

            JsonObject ready = readyBoundedOutputClosure("ACT.BAD");
            Files.write(plan, ((ready + "\n") + (ready + "\n")).getBytes(
                    StandardCharsets.UTF_8));
            assertFalse(CausynthPipeline
                    .selectedBoundedOutputClosureCoverageReady(plan,
                            "ACT.BAD"));
        } finally {
            folder.delete();
        }
    }

    private static JsonObject readyBoundedOutputClosure(String activationId) {
        String outputPort = "REGION.15.out.122";
        String outputCell = "<example.Manager: java.util.Map allKeys>";
        String inputPort = "REGION.15.in.32";
        JsonObject row = new JsonObject();
        row.addProperty("activationId", activationId);
        row.addProperty("activationSelectionRequired", activationId);
        row.addProperty("activationBundleRootActivationId", activationId);
        row.addProperty("scheduleId", "SCHEDULE.0");
        row.addProperty("activationBundleScheduleId", "SCHEDULE.0");
        row.addProperty("activationBundleSize", 1);
        row.addProperty("activationBundleIndex", 0);
        row.addProperty("activationBundleMemberRole", "PRIMARY");
        row.addProperty("replayable", true);
        row.addProperty("boundaryReady", true);
        row.addProperty("symbolicReady", true);
        row.addProperty("schedulerReady", true);
        row.addProperty("materializationComplete", true);
        row.addProperty("runtimePathEvidenceComplete", true);
        row.addProperty("requestedOutputSliceComplete", true);
        row.addProperty("requestedOutputSliceRefinementComplete", true);
        row.addProperty("requestedOutputCaptureComplete", true);
        row.addProperty("branchOverrideProhibited", true);
        row.addProperty("targetReplayRequired", false);
        row.addProperty("pathSignatureTruncated", false);
        row.addProperty("containedCallTreeTruncated", false);
        row.addProperty("replayMode",
                "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
        row.addProperty("executionPhase", "CAPTURE_OUTPUT_PATH");
        row.addProperty("deferredMaterializationCount", 0);
        row.add("runtimeGaps", new JsonArray());

        JsonObject goal = new JsonObject();
        goal.addProperty("kind", "OUTPUT_CLOSURE");
        goal.addProperty("scope", "BOUNDED_OUTPUT_RELEVANT_PATHS");
        row.add("captureGoal", goal);

        JsonObject output = new JsonObject();
        output.addProperty("portId", outputPort);
        output.addProperty("cell", outputCell);
        output.addProperty("kind", "HEAP_STATE");
        row.add("requestedOutput", output);
        JsonObject outputDeclaration = new JsonObject();
        outputDeclaration.addProperty("symbol", outputPort);
        outputDeclaration.addProperty("cell", outputCell);
        outputDeclaration.addProperty("kind", "HEAP_STATE");
        JsonArray outputs = new JsonArray();
        outputs.add(outputDeclaration);
        row.add("outputs", outputs);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", outputCell);
        slice.addProperty("complete", true);
        slice.addProperty("structuralComplete", true);
        slice.addProperty("runtimeRefined", true);
        slice.addProperty("runtimeRefinementComplete", true);
        slice.addProperty("runtimeRefinementAuthority",
                "OBSERVED_REGION_CALL_TREE");
        slice.addProperty("unresolvedInputProvenanceComplete", true);
        slice.addProperty("captureBindingsComplete", true);
        slice.addProperty("captureBindingsRequired", false);
        slice.addProperty("methodBudgetTruncated", false);
        slice.addProperty("causalCellBudgetTruncated", false);
        slice.addProperty("regionTruncated", false);
        slice.addProperty("truncated", false);
        slice.add("unresolvedInputs", new JsonArray());
        slice.add("unresolvedInputDetails", new JsonArray());
        slice.add("truncationReasons", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("captureDischargedByHeapEffectTransformer", true);
        slice.addProperty("captureDischargeAuthority",
                "HEAP_EFFECT_STATE_TRANSFORMER");
        slice.addProperty("captureDischargeInputPort", inputPort);
        slice.addProperty("captureDischargeOutputPort", outputPort);
        slice.addProperty("captureDischargeOutputCell", outputCell);
        slice.addProperty("requestedStateTransformerContractApplicable", true);
        slice.addProperty("requestedStateTransformerContractComplete", true);
        slice.addProperty("requestedStateTransformerContractVersion", 1);
        slice.addProperty("requestedStateTransformerContractAuthority",
                "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1");
        slice.addProperty("requestedStateTransformerContractOutputPort",
                outputPort);
        slice.addProperty("requestedStateTransformerContractOutputCell",
                outputCell);
        slice.add("requestedStateTransformerContractIssues", new JsonArray());
        slice.addProperty("requestedStateTransformerObligationCount", 1);
        JsonObject obligation = new JsonObject();
        obligation.addProperty("siteId", "<example.Manager: void add()>#u1");
        obligation.addProperty("method", "<example.Manager: void add()>");
        obligation.addProperty("targetCell", outputCell);
        obligation.addProperty("authority", "STATIC_EXACT_TARGET_CELL");
        JsonArray obligations = new JsonArray();
        obligations.add(obligation);
        slice.add("requestedStateTransformerObligations", obligations);
        row.add("requestedOutputSlice", slice);

        JsonObject heapBinding = new JsonObject();
        heapBinding.addProperty("inputPort", inputPort);
        heapBinding.addProperty("outputPort", outputPort);
        heapBinding.addProperty("cell", outputCell);
        JsonArray heapBindings = new JsonArray();
        heapBindings.add(heapBinding);
        row.add("heapStateBindings", heapBindings);
        row.addProperty("requestedOutputCaptureRequired", false);
        row.add("requestedOutputCapture", new JsonArray());
        return row;
    }

    private static JsonObject readySolverOutputPathFlip() {
        String activation = "ACT.PATH.3a35b5ac15765178";
        JsonObject row = readyBoundedOutputClosure(activation);
        row.addProperty("scheduleId",
                "SCHEDULE.PATH.3a35b5ac15765178");
        row.addProperty("activationBundleScheduleId",
                "SCHEDULE.PATH.3a35b5ac15765178");
        row.addProperty("executionPhase", "REPLAY_OUTPUT_PATH_FLIP");
        row.addProperty("pathQueryKey",
                "c3577f7f5002a09920e54b51105590f1093a902d0fcf8bdee74ce4516109f7b3");

        JsonArray assignments = new JsonArray();
        assignments.add(solverPathFlipAssignment("M_Z_field_input",
                "sym__input", "REGION.15.in.32"));
        row.add("modelAssignments", assignments);

        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("siteId",
                "<example.Manager: void add()>#u14");
        targetBranch.addProperty("occurrence", 2);
        targetBranch.addProperty("desiredOutcome", false);
        targetBranch.addProperty("validationOnly", true);
        targetBranch.addProperty("branchOverrideAllowed", false);
        row.add("targetBranch", targetBranch);

        JsonObject prefix = new JsonObject();
        prefix.addProperty("siteId",
                "<example.Manager: void add()>#u14");
        prefix.addProperty("occurrence", 1);
        prefix.addProperty("outcome", true);
        prefix.addProperty("conditionIndex", 0);
        row.add("expectedBranchPrefix", singletonJsonArray(prefix));
        return row;
    }

    private static JsonObject solverPathFlipAssignment(
            String engineSymbol, String solverSymbol, String inputSymbol) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", engineSymbol);
        assignment.addProperty("solverSymbol", solverSymbol);
        assignment.addProperty("inputSymbol", inputSymbol);
        assignment.addProperty("valueType", "BOOL");
        assignment.addProperty("value", "true");
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        JsonObject target = new JsonObject();
        target.addProperty("symbol", inputSymbol);
        target.addProperty("cell", "<example.Keys: boolean enabled>");
        target.addProperty("sourceKind", "OPAQUE_CALL");
        assignment.add("target", target);
        return assignment;
    }

    private static JsonArray singletonJsonArray(JsonObject value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static void writePlanRow(Path plan, JsonObject row)
            throws Exception {
        Files.write(plan, (row + "\n").getBytes(StandardCharsets.UTF_8));
    }

    @Test
    public void instrumentsExactRequestedOutboundCallArgument()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            G.reset();
            System.setProperty("causynth.instrument.concolic", "true");
            Scene.v().addClass(new SootClass("java.lang.Throwable",
                    Modifier.PUBLIC));
            Scene.v().addClass(new SootClass("java.lang.String",
                    Modifier.PUBLIC));
            SootClass protocol = new SootClass("example.Protocol",
                    Modifier.PUBLIC);
            Scene.v().addClass(protocol);
            SootMethod accept = new SootMethod("accept",
                    Collections.singletonList(RefType.v("java.lang.String")),
                    VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
            protocol.addMethod(accept);

            SootClass owner = new SootClass("example.CaptureRegion",
                    Modifier.PUBLIC);
            Scene.v().addClass(owner);
            owner.setApplicationClass();
            SootMethod root = new SootMethod("run",
                    Collections.singletonList(RefType.v("java.lang.String")),
                    VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
            owner.addMethod(root);
            Body body = Jimple.v().newBody(root);
            root.setActiveBody(body);
            Local argument = Jimple.v().newLocal("arg",
                    RefType.v("java.lang.String"));
            body.getLocals().add(argument);
            body.getUnits().add(Jimple.v().newIdentityStmt(argument,
                    Jimple.v().newParameterRef(RefType.v("java.lang.String"),
                            0)));
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newStaticInvokeExpr(accept.makeRef(),
                            argument)));
            body.getUnits().add(Jimple.v().newReturnVoidStmt());

            String cell = accept.getSignature()
                    + ".param0:java.lang.String";
            Path plan = folder.getRoot().toPath().resolve("activation.jsonl");
            JsonObject activation = new JsonObject();
            activation.addProperty("activationId", "ACT.CAPTURE");
            activation.addProperty("rootMethod", root.getSignature());
            activation.addProperty("replayable", true);
            activation.addProperty("symbolicReady", true);
            JsonObject capture = new JsonObject();
            capture.addProperty("captureBindingId", "REGION.0.out.0.capture.0");
            capture.addProperty("outputPort", "REGION.0.out.0");
            capture.addProperty("outputCell", cell);
            capture.addProperty("callerMethod", root.getSignature());
            capture.addProperty("unitIndex", 1);
            capture.addProperty("siteId", root.getSignature() + "#u1");
            capture.addProperty("calleeMethod", accept.getSignature());
            capture.addProperty("argumentIndex", 0);
            capture.addProperty("occurrence", 1);
            JsonArray captures = new JsonArray();
            captures.add(capture);
            activation.add("requestedOutputCapture", captures);
            Files.write(plan, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));
            System.setProperty("causynth.concolic.activation.plan",
                    plan.toString());
            System.setProperty("causynth.concolic.activation.id",
                    "ACT.CAPTURE");

            Class<?> selectionClass = Class.forName(
                    CausynthPipeline.class.getName()
                            + "$ConcolicOutputCaptureSelection");
            Method from = selectionClass.getDeclaredMethod("from",
                    Path.class, String.class);
            from.setAccessible(true);
            Object selection = from.invoke(null, plan, "ACT.CAPTURE");
            Method targets = selectionClass.getDeclaredMethod("targets");
            targets.setAccessible(true);
            assertEquals(1, ((java.util.Collection<?>) targets.invoke(
                    selection)).size());
            Class<?> refsClass = Class.forName(
                    CausynthPipeline.class.getName() + "$ConcolicRegionRefs");
            Method create = refsClass.getDeclaredMethod("create");
            create.setAccessible(true);
            Object refs = create.invoke(null);
            Method instrument = CausynthPipeline.class.getDeclaredMethod(
                    "instrumentConcolicOutputCaptures", selectionClass,
                    refsClass);
            instrument.setAccessible(true);
            assertEquals(1, instrument.invoke(
                    new CausynthPipeline(null, 0, 0), selection, refs));

            InvokeExpr hook = null;
            for (Unit unit : body.getUnits()) {
                if (unit instanceof Stmt
                        && ((Stmt) unit).containsInvokeExpr()
                        && "recordOutputCapture".equals(((Stmt) unit)
                        .getInvokeExpr().getMethodRef().name())) {
                    hook = ((Stmt) unit).getInvokeExpr();
                }
            }
            assertNotNull(hook);
            assertEquals(root.getSignature(), hook.getArg(0).toString()
                    .replace("\"", ""));
            assertEquals(1, ((IntConstant) hook.getArg(1)).value);
            assertEquals(0, ((IntConstant) hook.getArg(4)).value);
        } finally {
            folder.delete();
        }
    }

    @Test
    public void instrumentsExactFieldAssignmentRhsAfterSuccessfulWrite()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            G.reset();
            Scene.v().addClass(new SootClass("java.lang.String",
                    Modifier.PUBLIC));
            SootClass holderClass = new SootClass("example.CaptureHolder",
                    Modifier.PUBLIC);
            Scene.v().addClass(holderClass);
            SootField field = new SootField("value",
                    RefType.v("java.lang.String"), Modifier.PUBLIC);
            holderClass.addField(field);

            SootClass owner = new SootClass("example.FieldCaptureRegion",
                    Modifier.PUBLIC);
            Scene.v().addClass(owner);
            owner.setApplicationClass();
            SootMethod root = new SootMethod("run", Arrays.asList(
                    RefType.v(holderClass.getName()),
                    RefType.v("java.lang.String")), VoidType.v(),
                    Modifier.PUBLIC | Modifier.STATIC);
            owner.addMethod(root);
            Body body = Jimple.v().newBody(root);
            root.setActiveBody(body);
            Local holder = Jimple.v().newLocal("holder",
                    RefType.v(holderClass.getName()));
            Local rhs = Jimple.v().newLocal("rhs",
                    RefType.v("java.lang.String"));
            body.getLocals().add(holder);
            body.getLocals().add(rhs);
            body.getUnits().add(Jimple.v().newIdentityStmt(holder,
                    Jimple.v().newParameterRef(holder.getType(), 0)));
            body.getUnits().add(Jimple.v().newIdentityStmt(rhs,
                    Jimple.v().newParameterRef(rhs.getType(), 1)));
            AssignStmt write = Jimple.v().newAssignStmt(
                    Jimple.v().newInstanceFieldRef(holder, field.makeRef()),
                    rhs);
            body.getUnits().add(write);
            body.getUnits().add(Jimple.v().newReturnVoidStmt());

            Path plan = folder.getRoot().toPath().resolve(
                    "field-activation.jsonl");
            JsonObject activation = new JsonObject();
            activation.addProperty("activationId", "ACT.FIELD.CAPTURE");
            activation.addProperty("rootMethod", root.getSignature());
            activation.addProperty("replayable", true);
            JsonObject capture = new JsonObject();
            capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
            capture.addProperty("captureBindingId",
                    "REGION.FIELD.out.0.capture.0");
            capture.addProperty("outputPort", "REGION.FIELD.out.0");
            capture.addProperty("outputCell", field.getSignature());
            capture.addProperty("method", root.getSignature());
            capture.addProperty("unitIndex", 2);
            capture.addProperty("siteId", root.getSignature() + "#u2");
            capture.addProperty("fieldSignature", field.getSignature());
            capture.addProperty("occurrence", 1);
            JsonArray captures = new JsonArray();
            captures.add(capture);
            activation.add("requestedOutputCapture", captures);
            Files.write(plan, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));

            Class<?> selectionClass = Class.forName(
                    CausynthPipeline.class.getName()
                            + "$ConcolicOutputCaptureSelection");
            Method from = selectionClass.getDeclaredMethod("from",
                    Path.class, String.class);
            from.setAccessible(true);
            Object selection = from.invoke(null, plan,
                    "ACT.FIELD.CAPTURE");
            Class<?> refsClass = Class.forName(
                    CausynthPipeline.class.getName()
                            + "$ConcolicRegionRefs");
            Method create = refsClass.getDeclaredMethod("create");
            create.setAccessible(true);
            Object refs = create.invoke(null);
            Method instrument = CausynthPipeline.class.getDeclaredMethod(
                    "instrumentConcolicOutputCaptures", selectionClass,
                    refsClass);
            instrument.setAccessible(true);
            assertEquals(1, instrument.invoke(
                    new CausynthPipeline(null, 0, 0), selection, refs));

            List<Unit> units = new ArrayList<>();
            for (Unit unit : body.getUnits()) units.add(unit);
            int writeIndex = units.indexOf(write);
            int activeTokenIndex = -1;
            int hookIndex = -1;
            InvokeExpr hook = null;
            for (int index = 0; index < units.size(); index++) {
                Unit unit = units.get(index);
                if (!(unit instanceof Stmt)
                        || !((Stmt) unit).containsInvokeExpr()) continue;
                InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
                if ("activeToken".equals(invoke.getMethodRef().name())) {
                    activeTokenIndex = index;
                } else if ("recordFieldAssignmentOutput".equals(
                        invoke.getMethodRef().name())) {
                    hookIndex = index;
                    hook = invoke;
                }
            }
            assertTrue(write.getRightOp() instanceof Local);
            assertTrue(writeIndex > 0);
            assertTrue(activeTokenIndex > writeIndex);
            assertTrue(hookIndex > activeTokenIndex);
            assertNotNull(hook);
            assertEquals(root.getSignature(), hook.getArg(1).toString()
                    .replace("\"", ""));
            assertEquals(2, ((IntConstant) hook.getArg(2)).value);
            assertEquals(field.getSignature(), hook.getArg(4).toString()
                    .replace("\"", ""));
            assertSame(holder, hook.getArg(9));
            assertSame(write.getRightOp(), hook.getArg(10));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void accessorContextInstrumentationWrapsOnlyExactCallAndCleansExceptionalExit()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            G.reset();
            Scene.v().addClass(new SootClass("java.lang.Throwable",
                    Modifier.PUBLIC));
            SootClass valueClass = new SootClass("example.ExpiringValue",
                    Modifier.PUBLIC);
            Scene.v().addClass(valueClass);
            SootField expiry = new SootField("expiry", LongType.v(),
                    Modifier.PUBLIC);
            valueClass.addField(expiry);
            SootMethod accessor = new SootMethod("getExpiry",
                    Collections.emptyList(), LongType.v(), Modifier.PUBLIC);
            valueClass.addMethod(accessor);

            SootClass callerClass = new SootClass("example.AccessorCaller",
                    Modifier.PUBLIC);
            Scene.v().addClass(callerClass);
            callerClass.setApplicationClass();
            SootMethod caller = new SootMethod("prune",
                    Collections.singletonList(RefType.v(
                            valueClass.getName())), VoidType.v(),
                    Modifier.PUBLIC | Modifier.STATIC);
            callerClass.addMethod(caller);
            Body body = Jimple.v().newBody(caller);
            caller.setActiveBody(body);
            Local owner = Jimple.v().newLocal("owner",
                    RefType.v(valueClass.getName()));
            Local firstResult = Jimple.v().newLocal("first", LongType.v());
            Local secondResult = Jimple.v().newLocal("second", LongType.v());
            body.getLocals().add(owner);
            body.getLocals().add(firstResult);
            body.getLocals().add(secondResult);
            body.getUnits().add(Jimple.v().newIdentityStmt(owner,
                    Jimple.v().newParameterRef(owner.getType(), 0)));
            AssignStmt selectedCall = Jimple.v().newAssignStmt(firstResult,
                    Jimple.v().newVirtualInvokeExpr(owner,
                            accessor.makeRef()));
            AssignStmt unselectedCall = Jimple.v().newAssignStmt(secondResult,
                    Jimple.v().newVirtualInvokeExpr(owner,
                            accessor.makeRef()));
            Unit originalReturn = Jimple.v().newReturnVoidStmt();
            body.getUnits().add(selectedCall);
            body.getUnits().add(unselectedCall);
            body.getUnits().add(originalReturn);

            String site = caller.getSignature() + "#u1";
            Path plan = folder.getRoot().toPath().resolve(
                    "accessor-context.jsonl");
            JsonObject activation = new JsonObject();
            activation.addProperty("activationId", "ACT.ACCESSOR");
            activation.addProperty("replayable", true);
            JsonObject action = new JsonObject();
            action.addProperty("symbol", "REGION.TEST.in.expiry");
            action.addProperty("cell", expiry.getSignature());
            action.addProperty("field", expiry.getSignature());
            action.addProperty("location", "HEAP_OBJECT_FIELD");
            action.addProperty("bindingMode", "FIELD_ACCESS");
            action.addProperty("accessOwnerClass", valueClass.getName());
            action.addProperty("accessField", expiry.getName());
            action.addProperty("accessFieldSignature",
                    expiry.getSignature());
            action.addProperty("accessorCallerMethod",
                    caller.getSignature());
            action.addProperty("accessorCallUnitIndex", 1);
            action.addProperty("accessorCallSiteId", site);
            action.addProperty("accessorDeclaredCallee",
                    accessor.getSignature());
            action.addProperty("accessorImplementationMethod",
                    accessor.getSignature());
            action.addProperty("accessorImplementationAuthority",
                    "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
            action.addProperty("accessorCallSiteAuthority",
                    "STATIC_UNIQUE_EXACT_DECLARED_FIELD_"
                            + "ACCESSOR_CALLSITE_V1");
            JsonArray actions = new JsonArray();
            actions.add(action);
            activation.add("materializations", actions);
            Files.write(plan, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));

            Object selection = concolicMaterializationSelection(plan,
                    "ACT.ACCESSOR");
            Object refs = concolicRegionRefs();
            assertEquals(1, instrumentConcolicAccessorCallContexts(
                    selection, refs));

            List<Unit> units = new ArrayList<>();
            for (Unit unit : body.getUnits()) units.add(unit);
            Unit enter = null;
            List<Unit> exits = new ArrayList<>();
            for (Unit unit : units) {
                InvokeExpr invoke = invokeExpression(unit);
                if (invoke == null) continue;
                if ("enterAccessorCallContext".equals(
                        invoke.getMethodRef().name())) {
                    enter = unit;
                    assertEquals(caller.getSignature(), invoke.getArg(0)
                            .toString().replace("\"", ""));
                    assertEquals(1,
                            ((IntConstant) invoke.getArg(1)).value);
                    assertEquals(site, invoke.getArg(2).toString()
                            .replace("\"", ""));
                    assertEquals(accessor.getSignature(), invoke.getArg(3)
                            .toString().replace("\"", ""));
                    assertSame(owner, invoke.getArg(4));
                } else if ("exitAccessorCallContext".equals(
                        invoke.getMethodRef().name())) {
                    exits.add(unit);
                }
            }
            assertNotNull(enter);
            assertEquals("one normal and one exceptional cleanup hook", 2,
                    exits.size());
            assertEquals("the same-callee call at the wrong site stays raw",
                    accessor.getSignature(), ((InvokeExpr) unselectedCall
                            .getRightOp()).getMethodRef().getSignature());
            assertEquals(1, body.getTraps().size());
            Trap cleanup = body.getTraps().getFirst();
            assertSame(selectedCall, cleanup.getBeginUnit());
            assertTrue("the exclusive trap end is the normal cleanup hook",
                    exits.contains(cleanup.getEndUnit()));
            assertTrue(cleanup.getHandlerUnit()
                    instanceof soot.jimple.IdentityStmt);
            assertTrue(units.indexOf(enter) < units.indexOf(selectedCall));
            assertEquals(units.indexOf(selectedCall) + 1,
                    units.indexOf(cleanup.getEndUnit()));
            assertTrue("normal flow must jump over the catch-and-rethrow",
                    units.get(units.indexOf(cleanup.getEndUnit()) + 1)
                            instanceof GotoStmt);
            assertTrue(units.indexOf(cleanup.getHandlerUnit())
                    < units.indexOf(unselectedCall));
            assertTrue("the exceptional cleanup must rethrow the original",
                    units.get(units.indexOf(cleanup.getHandlerUnit()) + 2)
                            instanceof soot.jimple.ThrowStmt);
            assertTrue(units.indexOf(unselectedCall)
                    < units.indexOf(originalReturn));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void regionExitAndThrowHooksUseTokenReturnedByEntry()
            throws Exception {
        G.reset();
        System.setProperty("causynth.instrument.concolic", "true");
        System.clearProperty("causynth.concolic.activation.plan");
        System.clearProperty("causynth.concolic.activation.id");

        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        SootClass owner = new SootClass("example.TokenRegion",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootMethod root = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(root);
        root.setActiveBody(Jimple.v().newBody(root));
        root.getActiveBody().getUnits().add(Jimple.v().newReturnVoidStmt());

        Object result = newAnalysisResultWithRoot(root.getSignature());
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicRegions", result.getClass());
        instrument.setAccessible(true);
        instrument.invoke(new CausynthPipeline(null, 0, 0), result);

        Local entryToken = null;
        Unit tokenInitialization = null;
        Unit entryCall = null;
        InvokeExpr exit = null;
        InvokeExpr thrown = null;
        boolean calledActiveVariant = false;
        for (Unit unit : root.getActiveBody().getUnits()) {
            if (unit instanceof AssignStmt
                    && ((AssignStmt) unit).getRightOp() instanceof InvokeExpr) {
                InvokeExpr invoke = (InvokeExpr) ((AssignStmt) unit).getRightOp();
                if ("enterRegion".equals(invoke.getMethodRef().name())) {
                    assertTrue(((AssignStmt) unit).getLeftOp() instanceof Local);
                    entryToken = (Local) ((AssignStmt) unit).getLeftOp();
                    entryCall = unit;
                }
            }
            if (unit instanceof AssignStmt
                    && ((AssignStmt) unit).getLeftOp() == entryToken
                    && ((AssignStmt) unit).getRightOp() instanceof LongConstant
                    && ((LongConstant) ((AssignStmt) unit).getRightOp()).value
                    == 0L) {
                tokenInitialization = unit;
            }
            if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
            String name = invoke.getMethodRef().name();
            if ("exitRegion".equals(name)) {
                exit = invoke;
            } else if ("throwRegion".equals(name)) {
                thrown = invoke;
            } else if ("exitActiveRegion".equals(name)
                    || "throwActiveRegion".equals(name)) {
                calledActiveVariant = true;
            }
        }

        assertNotNull("entry hook must store its token in a local", entryToken);
        // entryToken is learned while visiting the following enterRegion
        // assignment, so locate its preceding zero initialization explicitly.
        if (tokenInitialization == null) {
            for (Unit unit : root.getActiveBody().getUnits()) {
                if (unit instanceof AssignStmt
                        && ((AssignStmt) unit).getLeftOp() == entryToken
                        && ((AssignStmt) unit).getRightOp()
                        instanceof LongConstant
                        && ((LongConstant) ((AssignStmt) unit).getRightOp()).value
                        == 0L) {
                    tokenInitialization = unit;
                    break;
                }
            }
        }
        assertNotNull("region token must be initialized before the trap",
                tokenInitialization);
        assertNotNull("normal return must call exitRegion(long,...)", exit);
        assertNotNull("exception handler must call throwRegion(long,...)",
                thrown);
        assertEquals("long", exit.getMethodRef().parameterType(0).toString());
        assertEquals("long", thrown.getMethodRef().parameterType(0).toString());
        assertSame("exitRegion must use this root's entry token",
                entryToken, exit.getArg(0));
        assertSame("throwRegion must use this root's entry token",
                entryToken, thrown.getArg(0));
        assertFalse("region instrumentation must not use ambient active hooks",
                calledActiveVariant);
        assertEquals("one token-specific cleanup trap is expected", 1,
                root.getActiveBody().getTraps().size());
        Trap cleanup = root.getActiveBody().getTraps().getFirst();
        List<Unit> units = new ArrayList<>();
        for (Unit unit : root.getActiveBody().getUnits()) units.add(unit);
        assertSame("cleanup trap must begin at enterRegion, after the long "
                        + "token has a verifier-visible zero value",
                entryCall, cleanup.getBeginUnit());
        assertTrue("token initialization must precede the protected entry hook",
                units.indexOf(tokenInitialization) < units.indexOf(entryCall));
    }

    @Test
    public void primitiveRegionReturnIsBoxedBeforeObservationPause()
            throws Exception {
        G.reset();
        System.setProperty("causynth.instrument.concolic", "true");
        System.clearProperty("causynth.concolic.activation.plan");
        System.clearProperty("causynth.concolic.activation.id");

        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        SootClass string = new SootClass("java.lang.String",
                Modifier.PUBLIC);
        Scene.v().addClass(string);
        string.addMethod(new SootMethod("valueOf",
                Collections.<soot.Type>singletonList(IntType.v()),
                RefType.v("java.lang.String"),
                Modifier.PUBLIC | Modifier.STATIC | Modifier.NATIVE));
        SootClass integer = new SootClass("java.lang.Integer",
                Modifier.PUBLIC);
        Scene.v().addClass(integer);
        integer.addMethod(new SootMethod("valueOf",
                Collections.<soot.Type>singletonList(IntType.v()),
                RefType.v("java.lang.Integer"),
                Modifier.PUBLIC | Modifier.STATIC | Modifier.NATIVE));

        SootClass owner = new SootClass("example.PrimitiveReturnRegion",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootMethod root = new SootMethod("run", Collections.emptyList(),
                IntType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(root);
        Body body = Jimple.v().newBody(root);
        root.setActiveBody(body);
        body.getUnits().add(Jimple.v().newReturnStmt(IntConstant.v(1)));

        Object result = newAnalysisResultWithRoot(root.getSignature());
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicRegions", result.getClass());
        instrument.setAccessible(true);
        instrument.invoke(new CausynthPipeline(null, 0, 0), result);

        List<Unit> units = new ArrayList<>();
        Unit wrapperCall = null;
        Unit exitCall = null;
        Unit primitiveStringCall = null;
        for (Unit unit : body.getUnits()) {
            units.add(unit);
            InvokeExpr invoke = invokeExpression(unit);
            if (invoke == null) continue;
            String method = invoke.getMethodRef().name();
            String declaring = invoke.getMethodRef().declaringClass()
                    .getName();
            if ("valueOf".equals(method)
                    && "java.lang.Integer".equals(declaring)) {
                wrapperCall = unit;
            } else if ("valueOf".equals(method)
                    && "java.lang.String".equals(declaring)) {
                primitiveStringCall = unit;
            } else if ("exitRegion".equals(method)) {
                exitCall = unit;
            }
        }
        assertNotNull(wrapperCall);
        assertNotNull(primitiveStringCall);
        assertNotNull(exitCall);
        int wrapperIndex = units.indexOf(wrapperCall);
        int stringIndex = units.indexOf(primitiveStringCall);
        int exitIndex = units.indexOf(exitCall);
        assertTrue(wrapperIndex < stringIndex && stringIndex < exitIndex);
        Unit pause = units.get(wrapperIndex + 1);
        assertRuntimeInvoke(pause,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "pauseObservation");
        InvokeExpr exit = invokeExpression(exitCall);
        assertTrue(wrapperCall instanceof AssignStmt);
        assertSame(((AssignStmt) wrapperCall).getLeftOp(), exit.getArg(1));
        assertFalse("primitive return must not be serialized as null",
                exit.getArg(1) instanceof soot.jimple.NullConstant);
    }

    @Test
    public void regionEntryPassesExactReferenceArgumentsAndNullPrimitiveSlots()
            throws Exception {
        G.reset();
        System.setProperty("causynth.instrument.concolic", "true");
        System.clearProperty("causynth.concolic.activation.plan");
        System.clearProperty("causynth.concolic.activation.id");

        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.String",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.Integer",
                Modifier.PUBLIC));
        SootClass owner = new SootClass("example.ArgumentRegion",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootMethod root = new SootMethod("run", Arrays.asList(
                RefType.v("java.lang.String"), IntType.v(),
                ArrayType.v(RefType.v("java.lang.Object"), 1)),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(root);
        Body body = Jimple.v().newBody(root);
        root.setActiveBody(body);
        Local reference0 = Jimple.v().newLocal("reference0",
                RefType.v("java.lang.String"));
        Local primitive1 = Jimple.v().newLocal("primitive1", IntType.v());
        Local reference2 = Jimple.v().newLocal("reference2",
                ArrayType.v(RefType.v("java.lang.Object"), 1));
        body.getLocals().add(reference0);
        body.getLocals().add(primitive1);
        body.getLocals().add(reference2);
        body.getUnits().add(Jimple.v().newIdentityStmt(reference0,
                Jimple.v().newParameterRef(reference0.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(primitive1,
                Jimple.v().newParameterRef(primitive1.getType(), 1)));
        body.getUnits().add(Jimple.v().newIdentityStmt(reference2,
                Jimple.v().newParameterRef(reference2.getType(), 2)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());

        Object result = newAnalysisResultWithRoot(root.getSignature());
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicRegions", result.getClass());
        instrument.setAccessible(true);
        instrument.invoke(new CausynthPipeline(null, 0, 0), result);

        Local argumentArray = null;
        InvokeExpr entry = null;
        Map<Integer, Value> assigned = new LinkedHashMap<>();
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)) continue;
            AssignStmt assignment = (AssignStmt) unit;
            if (assignment.getRightOp() instanceof NewArrayExpr
                    && assignment.getLeftOp() instanceof Local
                    && "java.lang.Object[]".equals(
                    assignment.getLeftOp().getType().toString())) {
                argumentArray = (Local) assignment.getLeftOp();
            }
            if (assignment.getRightOp() instanceof InvokeExpr
                    && "enterRegion".equals(((InvokeExpr)
                    assignment.getRightOp()).getMethodRef().name())) {
                entry = (InvokeExpr) assignment.getRightOp();
            }
        }
        assertNotNull(argumentArray);
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)) continue;
            AssignStmt assignment = (AssignStmt) unit;
            if (!(assignment.getLeftOp() instanceof ArrayRef)) continue;
            ArrayRef array = (ArrayRef) assignment.getLeftOp();
            if (array.getBase() != argumentArray
                    || !(array.getIndex() instanceof IntConstant)) continue;
            assigned.put(((IntConstant) array.getIndex()).value,
                    assignment.getRightOp());
        }
        assertNotNull(entry);
        assertEquals(3, entry.getArgCount());
        assertSame(argumentArray, entry.getArg(2));
        assertEquals(2, assigned.size());
        assertSame(reference0, assigned.get(0));
        assertFalse("primitive slot must remain the new array's null value",
                assigned.containsKey(1));
        assertSame(reference2, assigned.get(2));
    }

    @Test
    public void combinedInstrumentationNeverRetagsSyntheticUnits()
            throws Exception {
        G.reset();
        SootClass owner = new SootClass("example.CombinedInstrumentation",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Unit originalReturn = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(originalReturn);

        Method tagOriginalUnits = CausynthPipeline.class.getDeclaredMethod(
                "tagOriginalUnits", List.class);
        tagOriginalUnits.setAccessible(true);
        tagOriginalUnits.invoke(null,
                new ArrayList<Unit>(Collections.singletonList(originalReturn)));

        // Models a trace hook inserted before the concolic pass starts.
        Unit syntheticTraceHook = Jimple.v().newNopStmt();
        body.getUnits().insertBefore(syntheticTraceHook, originalReturn);
        List<Unit> combinedSnapshot = new ArrayList<>();
        for (Unit unit : body.getUnits()) combinedSnapshot.add(unit);
        tagOriginalUnits.invoke(null, combinedSnapshot);

        Method originalUnitIndex = CausynthPipeline.class.getDeclaredMethod(
                "originalUnitIndex", Unit.class);
        originalUnitIndex.setAccessible(true);
        assertEquals(-1, originalUnitIndex.invoke(null, syntheticTraceHook));
        assertEquals(0, originalUnitIndex.invoke(null, originalReturn));

        Method originalUnit = CausynthPipeline.class.getDeclaredMethod(
                "originalUnit", Body.class, int.class);
        originalUnit.setAccessible(true);
        assertSame(originalReturn, originalUnit.invoke(null, body, 0));
        assertNull("a missing authoritative index must not fall back to the "
                        + "synthetic unit's current position",
                originalUnit.invoke(null, body, 1));
    }

    @Test
    public void combinedTraceBookkeepingIsOutsideConcolicObservation()
            throws Exception {
        G.reset();
        System.setProperty("causynth.instrument.trace", "true");
        System.setProperty("causynth.instrument.concolic", "true");
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        SootClass owner = new SootClass("example.CombinedTraceRegion",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        body.getUnits().add(Jimple.v().newReturnVoidStmt());

        Object result = newAnalysisResultWithRoot(method.getSignature());
        addAnalysisRow(result, "traceMethods", Collections.<String, Object>
                singletonMap("method", method.getSignature()));
        addAnalysisRow(result, "symbolicPlan", Collections.<String, Object>
                singletonMap("method", method.getSignature()));
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentRuntimeTrace", result.getClass());
        instrument.setAccessible(true);
        instrument.invoke(new CausynthPipeline(null, 0, 0), result);

        int isolationDepth = 0;
        int traceCalls = 0;
        for (Unit unit : body.getUnits()) {
            InvokeExpr invoke = null;
            if (unit instanceof AssignStmt
                    && ((AssignStmt) unit).getRightOp() instanceof InvokeExpr) {
                invoke = (InvokeExpr) ((AssignStmt) unit).getRightOp();
            } else if (unit instanceof Stmt
                    && ((Stmt) unit).containsInvokeExpr()) {
                invoke = ((Stmt) unit).getInvokeExpr();
            }
            if (invoke == null) {
                continue;
            }
            String declaringClass = invoke.getMethodRef().declaringClass()
                    .getName();
            String name = invoke.getMethodRef().name();
            if ("edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime"
                    .equals(declaringClass)) {
                if ("pauseObservation".equals(name)) {
                    isolationDepth++;
                } else if ("resumeObservation".equals(name)) {
                    isolationDepth--;
                    assertTrue("trace isolation depth must stay balanced",
                            isolationDepth >= 0);
                }
            } else if ("edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder"
                    .equals(declaringClass)) {
                traceCalls++;
                assertTrue("every recorder call must execute while custom-JDK "
                                + "path-condition recording is paused",
                        isolationDepth > 0);
            }
        }
        assertTrue(traceCalls > 0);
        assertEquals(0, isolationDepth);
    }

    @Test
    public void traceThenConcolicPassesPreserveOriginalBranchIdentityAndOrder()
            throws Exception {
        G.reset();
        System.setProperty("causynth.instrument.trace", "true");
        System.setProperty("causynth.instrument.concolic", "true");
        System.clearProperty("causynth.concolic.activation.plan");
        System.clearProperty("causynth.concolic.activation.id");

        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        installCombinedRuntimeStubs();
        SootClass owner = new SootClass("example.CombinedBranchRegion",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local flag = Jimple.v().newLocal("flag", IntType.v());
        body.getLocals().add(flag);
        Unit initialize = Jimple.v().newAssignStmt(flag, IntConstant.v(0));
        Unit falseReturn = Jimple.v().newReturnVoidStmt();
        Unit trueReturn = Jimple.v().newReturnVoidStmt();
        IfStmt originalBranch = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(flag, IntConstant.v(0)), trueReturn);
        body.getUnits().add(initialize);
        body.getUnits().add(originalBranch);
        body.getUnits().add(falseReturn);
        body.getUnits().add(trueReturn);
        List<Unit> originalUnits = new ArrayList<>(Arrays.asList(
                initialize, originalBranch, falseReturn, trueReturn));

        Object result = newAnalysisResultWithRoot(method.getSignature());
        addAnalysisRow(result, "traceMethods", Collections.<String, Object>
                singletonMap("method", method.getSignature()));
        addAnalysisRow(result, "symbolicPlan", Collections.<String, Object>
                singletonMap("method", method.getSignature()));
        Map<String, Object> guardEdge = new LinkedHashMap<>();
        guardEdge.put("method", method.getSignature());
        guardEdge.put("unitIndex", 1);
        guardEdge.put("transferKind", "GUARD");
        addAnalysisRow(result, "edges", guardEdge);
        addBranchPolicy(result, method.getSignature(), 1);

        CausynthPipeline pipeline = new CausynthPipeline(null, 0, 0);
        Method tracePass = CausynthPipeline.class.getDeclaredMethod(
                "instrumentRuntimeTrace", result.getClass());
        tracePass.setAccessible(true);
        tracePass.invoke(pipeline, result);

        List<Unit> traceUnits = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            if (!originalUnits.contains(unit)) {
                traceUnits.add(unit);
            }
        }
        assertFalse("the trace pass must add real synthetic units",
                traceUnits.isEmpty());

        Method concolicPass = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicRegions", result.getClass());
        concolicPass.setAccessible(true);
        concolicPass.invoke(pipeline, result);

        body.validate();

        Unit prepareHook = null;
        Unit nativeMarker = null;
        for (Unit unit : body.getUnits()) {
            InvokeExpr invoke = invokeExpression(unit);
            if (invoke == null) continue;
            if ("prepareBranch".equals(invoke.getMethodRef().name())) {
                prepareHook = unit;
            } else if ("markConcolicBranch".equals(
                    invoke.getMethodRef().name())) {
                nativeMarker = unit;
            }
        }
        assertNotNull(prepareHook);
        assertNotNull(nativeMarker);
        assertRuntimeInvoke(prepareHook,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "prepareBranch");
        assertRuntimeInvoke(nativeMarker, "java.lang.System",
                "markConcolicBranch");
        Unit afterNativeMarker = body.getUnits().getSuccOf(nativeMarker);
        assertTrue("the native marker may be followed only by an unconditional "
                        + "transfer to the original condition",
                afterNativeMarker instanceof GotoStmt);
        assertSame(originalBranch,
                ((GotoStmt) afterNativeMarker).getTarget());

        Method originalUnitIndex = CausynthPipeline.class.getDeclaredMethod(
                "originalUnitIndex", Unit.class);
        originalUnitIndex.setAccessible(true);
        for (int index = 0; index < originalUnits.size(); index++) {
            assertEquals("the original index namespace must survive both passes",
                    index, originalUnitIndex.invoke(null,
                            originalUnits.get(index)));
        }
        for (Unit traceUnit : traceUnits) {
            assertEquals("the concolic pass must not retag a trace hook as an "
                            + "original program unit",
                    -1, originalUnitIndex.invoke(null, traceUnit));
        }

        Unit concolicTrueEntry = originalBranch.getTarget();
        Unit truePause = body.getUnits().getSuccOf(concolicTrueEntry);
        Unit trueResolve = body.getUnits().getSuccOf(truePause);
        Unit trueResume = body.getUnits().getSuccOf(trueResolve);
        Unit trueDecision = body.getUnits().getSuccOf(trueResume);
        assertRuntimeInvoke(truePause,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "pauseObservation");
        assertRuntimeBooleanInvoke(trueResolve,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "resolveBranch", 5, 1);
        assertRuntimeInvoke(trueResume,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "resumeObservation");
        assertTrue(trueDecision instanceof IfStmt);

        Unit traceTrueEntry = ((IfStmt) trueDecision).getTarget();
        Unit traceTruePause = body.getUnits().getSuccOf(traceTrueEntry);
        Unit traceTrueRecord = body.getUnits().getSuccOf(traceTruePause);
        Unit traceTrueResume = body.getUnits().getSuccOf(traceTrueRecord);
        assertRuntimeInvoke(traceTruePause,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "pauseObservation");
        assertRuntimeBooleanInvoke(traceTrueRecord,
                "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder",
                "recordBranch", 4, 1);
        assertRuntimeInvoke(traceTrueResume,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "resumeObservation");

        Unit trueFallback = body.getUnits().getSuccOf(trueDecision);
        assertTrue(trueFallback instanceof GotoStmt);
        Unit traceFalsePause = ((GotoStmt) trueFallback).getTarget();
        Unit falsePause = body.getUnits().getSuccOf(originalBranch);
        Unit falseResolve = body.getUnits().getSuccOf(falsePause);
        Unit falseResume = body.getUnits().getSuccOf(falseResolve);
        Unit falseDecision = body.getUnits().getSuccOf(falseResume);
        assertRuntimeInvoke(falsePause,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "pauseObservation");
        assertRuntimeBooleanInvoke(falseResolve,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "resolveBranch", 5, 0);
        assertRuntimeInvoke(falseResume,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "resumeObservation");
        assertTrue(falseDecision instanceof IfStmt);
        assertSame("either resolver site must redirect to the traced true path",
                traceTrueEntry, ((IfStmt) falseDecision).getTarget());
        assertSame("the false resolver result must enter the traced false path",
                traceFalsePause, body.getUnits().getSuccOf(falseDecision));
        Unit traceFalseRecord = body.getUnits().getSuccOf(traceFalsePause);
        Unit traceFalseResume = body.getUnits().getSuccOf(traceFalseRecord);
        assertRuntimeInvoke(traceFalsePause,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "pauseObservation");
        assertRuntimeBooleanInvoke(traceFalseRecord,
                "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder",
                "recordBranch", 4, 0);
        assertRuntimeInvoke(traceFalseResume,
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                "resumeObservation");
    }

    @Test
    public void iteratorRemoveResolvesFieldThroughBackedCollectionViews()
            throws Exception {
        IteratorMutationFixture fixture = iteratorMutationFixture();
        Object analyzer = newStaticAnalyzer();
        List<?> facts = loadFacts(analyzer, fixture.method);

        Method fieldsMutatedByInvoke = analyzer.getClass().getDeclaredMethod(
                "fieldsMutatedByInvoke", List.class, int.class);
        fieldsMutatedByInvoke.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> fields = (Set<String>) fieldsMutatedByInvoke.invoke(
                analyzer, facts, fixture.removeUnitIndex);

        assertEquals("Iterator.remove must retain ownership through "
                        + "Map.entrySet() and Set.iterator()",
                Collections.singleton(fixture.field.getSignature()), fields);
    }

    @Test
    public void projectedEdgeRetainsMappingOnlyBaseAuthority()
            throws Exception {
        Object analyzer = newStaticAnalyzer();
        String method = "<example.MappingFixture: void bridge()>";
        String kind = "fixture_port_mapping";
        String from = method + "::outbound";
        String to = method + "::inbound";
        registerStaticPortMapping(analyzer, kind, method, from, to);

        Map<String, Object> base = emitSyntheticEdge(analyzer, kind, from,
                to, method, null);
        assertEquals(Boolean.TRUE, base.get("mappingOnly"));
        assertEquals("STATIC_FORMAT_AND_PORT_MAPPING",
                base.get("mappingAuthority"));

        String path = "#field:allKeys";
        Map<String, Object> projected = emitSyntheticEdge(analyzer,
                "projected_" + kind, from + path, to + path, method, base);

        assertEquals(Boolean.TRUE, projected.get("mappingOnly"));
        assertEquals("", projected.get("relation"));
        assertEquals("STATIC_FORMAT_AND_PORT_MAPPING",
                projected.get("mappingAuthority"));
        assertEquals(Boolean.FALSE,
                projected.get("semanticAssertionsAllowed"));
        assertEquals(Boolean.FALSE,
                projected.get("eligibleForAutomaticDerivation"));
        assertEquals(Boolean.FALSE,
                projected.get("eligibleForAutomaticSmt"));
        assertEquals(base.get("id"),
                projected.get("projectionBaseEdgeId"));
        assertEquals("PROJECTED_EDGE_CANNOT_EXCEED_BASE_EDGE_V1",
                projected.get("authorityInheritance"));
    }

    @Test
    public void projectedEdgeFailsClosedForFalseOrMissingBaseAuthority()
            throws Exception {
        Object analyzer = newStaticAnalyzer();
        String method = "<example.AuthorityFixture: void copy()>";

        Map<String, Object> smtBlockedBase = projectionBase(
                "BASE.SMT.BLOCKED", false, true, true, false);
        Map<String, Object> smtBlocked = emitSyntheticEdge(analyzer,
                "projected_fixture_field_transfer",
                method + "::blockedFrom#field:value",
                method + "::blockedTo#field:value", method,
                smtBlockedBase);
        assertEquals(Boolean.FALSE, smtBlocked.get("mappingOnly"));
        assertEquals(Boolean.TRUE,
                smtBlocked.get("semanticAssertionsAllowed"));
        assertEquals(Boolean.TRUE,
                smtBlocked.get("eligibleForAutomaticDerivation"));
        assertEquals(Boolean.FALSE,
                smtBlocked.get("eligibleForAutomaticSmt"));

        Map<String, Object> missingSmtBase = projectionBase(
                "BASE.SMT.MISSING", false, true, true, true);
        missingSmtBase.remove("eligibleForAutomaticSmt");
        Map<String, Object> missingSmt = emitSyntheticEdge(analyzer,
                "projected_fixture_field_transfer",
                method + "::missingFrom#field:value",
                method + "::missingTo#field:value", method,
                missingSmtBase);
        assertEquals(Boolean.FALSE,
                missingSmt.get("eligibleForAutomaticSmt"));

        Map<String, Object> missingMappingModeBase = projectionBase(
                "BASE.MODE.MISSING", false, true, true, true);
        missingMappingModeBase.remove("mappingOnly");
        Map<String, Object> missingMappingMode = emitSyntheticEdge(analyzer,
                "projected_fixture_field_transfer",
                method + "::modeFrom#field:value",
                method + "::modeTo#field:value", method,
                missingMappingModeBase);
        assertEquals(Boolean.TRUE, missingMappingMode.get("mappingOnly"));
        assertEquals(Boolean.FALSE,
                missingMappingMode.get("semanticAssertionsAllowed"));
        assertEquals(Boolean.FALSE,
                missingMappingMode.get("eligibleForAutomaticDerivation"));
        assertEquals(Boolean.FALSE,
                missingMappingMode.get("eligibleForAutomaticSmt"));
    }

    @Test
    public void exactGetterReturnLocalAndLateProjectionRetainCopyAuthority()
            throws Exception {
        G.reset();
        SootClass object = new SootClass("java.lang.Object",
                Modifier.PUBLIC);
        Scene.v().addClass(object);

        SootClass keys = new SootClass("example.DirectCopyKeys",
                Modifier.PUBLIC);
        keys.setSuperclass(object);
        keys.setApplicationClass();
        SootField allKeys = new SootField("allKeys",
                RefType.v("java.lang.Object"), Modifier.PUBLIC);
        keys.addField(allKeys);
        Scene.v().addClass(keys);

        SootClass command = new SootClass("example.DirectCopyCommand",
                Modifier.PUBLIC);
        command.setSuperclass(object);
        command.setApplicationClass();
        SootField payload = new SootField("keys", keys.getType(),
                Modifier.PRIVATE);
        command.addField(payload);
        Scene.v().addClass(command);

        SootMethod getter = new SootMethod("getKeys",
                Collections.emptyList(), keys.getType(), Modifier.PUBLIC);
        command.addMethod(getter);
        Body body = Jimple.v().newBody(getter);
        getter.setActiveBody(body);
        Local receiver = Jimple.v().newLocal("self", command.getType());
        Local loaded = Jimple.v().newLocal("loaded", keys.getType());
        Local local = Jimple.v().newLocal("keys", keys.getType());
        body.getLocals().addAll(Arrays.asList(receiver, loaded, local));
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(command.getType())));
        body.getUnits().add(Jimple.v().newAssignStmt(loaded,
                Jimple.v().newInstanceFieldRef(receiver,
                        payload.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(local, loaded));
        body.getUnits().add(Jimple.v().newReturnStmt(local));

        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, getter);
        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, getter.getSignature());
        String returned = getter.getSignature() + ".return";
        String loadedCell = getter.getSignature() + "::loaded";
        String localCell = getter.getSignature() + "::keys";
        relevantCells.add(returned);

        Method processMethod = analyzer.getClass().getDeclaredMethod(
                "processMethod", String.class);
        processMethod.setAccessible(true);
        for (int round = 0; round < 3; round++) {
            processMethod.invoke(analyzer, getter.getSignature());
        }

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        Map<String, Object> base = edges.stream().filter(edge ->
                "local_def_use".equals(edge.get("kind"))
                        && localCell.equals(edge.get("fromCell"))
                        && returned.equals(edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing exact return-local edge"));
        assertEquals("VALUE_PASS", base.get("transferKind"));
        assertEquals("value_flow", base.get("relation"));
        assertEquals("SOOT_EXACT_LOCAL_DIRECT_COPY_V1",
                base.get("valueFlowAuthority"));
        assertEquals("RETURN_LOCAL", base.get("directCopyKind"));

        Map<String, Object> assignmentBase = edges.stream().filter(edge ->
                "local_def_use".equals(edge.get("kind"))
                        && loadedCell.equals(edge.get("fromCell"))
                        && localCell.equals(edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing exact local-assignment edge"));
        assertEquals("VALUE_PASS", assignmentBase.get("transferKind"));
        assertEquals("value_flow", assignmentBase.get("relation"));
        assertEquals("SOOT_EXACT_LOCAL_DIRECT_COPY_V1",
                assignmentBase.get("valueFlowAuthority"));
        assertEquals("LOCAL_ASSIGN_LOCAL",
                assignmentBase.get("directCopyKind"));

        // Add the field demand only after the base edge was emitted.  The
        // projected pass now has no Fact and must inherit the explicit base
        // authority instead of guessing from its kind or rendered text.
        String path = "#field:allKeys";
        relevantCells.add(returned + path);
        Method propagate = analyzer.getClass().getDeclaredMethod(
                "propagateProjectedEdgesFromExistingEdges");
        propagate.setAccessible(true);
        for (int round = 0; round < 3; round++) {
            propagate.invoke(analyzer);
        }

        Map<String, Object> projected = edges.stream().filter(edge ->
                "projected_local_def_use".equals(edge.get("kind"))
                        && (localCell + path).equals(edge.get("fromCell"))
                        && (returned + path).equals(edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing late projected return-local edge"));
        assertEquals("VALUE_PASS", projected.get("transferKind"));
        assertEquals("value_flow", projected.get("relation"));
        assertEquals(
                "PROJECTED_FROM_SOOT_EXACT_LOCAL_DIRECT_COPY_V1",
                projected.get("valueFlowAuthority"));
        assertEquals(base.get("id"), projected.get("baseValueFlowEdgeId"));
        assertEquals("SOOT_EXACT_LOCAL_DIRECT_COPY_V1",
                projected.get("baseValueFlowAuthority"));
        assertEquals(Boolean.FALSE, projected.get("mappingOnly"));
        assertEquals(Boolean.TRUE,
                projected.get("semanticAssertionsAllowed"));
        assertEquals(Boolean.TRUE,
                projected.get("eligibleForAutomaticDerivation"));
        assertEquals(Boolean.TRUE,
                projected.get("eligibleForAutomaticSmt"));
        assertEquals(base.get("id"),
                projected.get("projectionBaseEdgeId"));
        assertEquals("PROJECTED_EDGE_CANNOT_EXCEED_BASE_EDGE_V1",
                projected.get("authorityInheritance"));
        assertTrue(String.valueOf(projected.get("siteId"))
                .contains("#synthetic:projected_local_def_use"));

        Map<String, Object> projectedAssignment = edges.stream()
                .filter(edge ->
                        "projected_local_def_use".equals(edge.get("kind"))
                                && (loadedCell + path).equals(
                                edge.get("fromCell"))
                                && (localCell + path).equals(
                                edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing late projected local-assignment edge"));
        assertEquals("value_flow", projectedAssignment.get("relation"));
        assertEquals(
                "PROJECTED_FROM_SOOT_EXACT_LOCAL_DIRECT_COPY_V1",
                projectedAssignment.get("valueFlowAuthority"));
        assertEquals(assignmentBase.get("id"),
                projectedAssignment.get("baseValueFlowEdgeId"));

        Map<String, Object> fieldRead = edges.stream().filter(edge ->
                "field_read".equals(edge.get("kind"))
                        && payload.getSignature().equals(edge.get("fromCell"))
                        && loadedCell.equals(edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing canonical field read"));
        assertEquals("value_flow", fieldRead.get("relation"));
        assertFalse("a heap read is exact for its own reason, not a local "
                        + "direct-copy proof",
                fieldRead.containsKey("valueFlowAuthority"));
    }

    @Test
    public void computedArrayFieldAndCastUsesDoNotGainDirectCopyAuthority()
            throws Exception {
        G.reset();
        SootClass object = new SootClass("java.lang.Object",
                Modifier.PUBLIC);
        Scene.v().addClass(object);
        SootClass owner = new SootClass("example.NonCopyOwner",
                Modifier.PUBLIC);
        owner.setSuperclass(object);
        owner.setApplicationClass();
        SootField count = new SootField("count", IntType.v(),
                Modifier.PUBLIC);
        owner.addField(count);
        Scene.v().addClass(owner);

        ArrayType ints = ArrayType.v(IntType.v(), 1);
        SootMethod method = new SootMethod("mix",
                Arrays.asList(owner.getType(), ints, IntType.v(),
                        IntType.v()), IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = Jimple.v().newLocal("owner", owner.getType());
        Local array = Jimple.v().newLocal("values", ints);
        Local left = Jimple.v().newLocal("left", IntType.v());
        Local right = Jimple.v().newLocal("right", IntType.v());
        Local sum = Jimple.v().newLocal("sum", IntType.v());
        Local element = Jimple.v().newLocal("element", IntType.v());
        Local fieldValue = Jimple.v().newLocal("fieldValue", IntType.v());
        Local widened = Jimple.v().newLocal("widened", LongType.v());
        body.getLocals().addAll(Arrays.asList(receiver, array, left, right,
                sum, element, fieldValue, widened));
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newParameterRef(owner.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(array,
                Jimple.v().newParameterRef(ints, 1)));
        body.getUnits().add(Jimple.v().newIdentityStmt(left,
                Jimple.v().newParameterRef(IntType.v(), 2)));
        body.getUnits().add(Jimple.v().newIdentityStmt(right,
                Jimple.v().newParameterRef(IntType.v(), 3)));
        body.getUnits().add(Jimple.v().newAssignStmt(sum,
                Jimple.v().newAddExpr(left, right)));
        body.getUnits().add(Jimple.v().newAssignStmt(element,
                Jimple.v().newArrayRef(array, IntConstant.v(0))));
        body.getUnits().add(Jimple.v().newAssignStmt(fieldValue,
                Jimple.v().newInstanceFieldRef(receiver,
                        count.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(widened,
                Jimple.v().newCastExpr(left, LongType.v())));
        body.getUnits().add(Jimple.v().newReturnStmt(sum));

        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, method);
        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, method.getSignature());
        String prefix = method.getSignature() + "::";
        relevantCells.add(method.getSignature() + ".return");
        relevantCells.add(prefix + "element");
        relevantCells.add(prefix + "fieldValue");
        relevantCells.add(prefix + "widened");

        Method processMethod = analyzer.getClass().getDeclaredMethod(
                "processMethod", String.class);
        processMethod.setAccessible(true);
        for (int round = 0; round < 3; round++) {
            processMethod.invoke(analyzer, method.getSignature());
        }
        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);

        List<String> nonCopyTargets = Arrays.asList(prefix + "sum",
                prefix + "element", prefix + "widened");
        for (String target : nonCopyTargets) {
            List<Map<String, Object>> dependencies = new ArrayList<>();
            for (Map<String, Object> edge : edges) {
                if ("local_def_use".equals(edge.get("kind"))
                        && target.equals(edge.get("toCell"))) {
                    dependencies.add(edge);
                }
            }
            assertFalse("missing non-copy dependency for " + target,
                    dependencies.isEmpty());
            assertTrue("computed/array/cast dependency gained exact-copy "
                            + "authority: " + dependencies,
                    dependencies.stream().allMatch(edge ->
                            "taint_depends_on".equals(edge.get("relation"))
                                    && !edge.containsKey(
                                    "valueFlowAuthority")));
        }

        Map<String, Object> fieldRead = edges.stream().filter(edge ->
                "field_read".equals(edge.get("kind"))
                        && count.getSignature().equals(edge.get("fromCell"))
                        && (prefix + "fieldValue").equals(
                        edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing exact field-read edge"));
        assertEquals("value_flow", fieldRead.get("relation"));
        assertFalse(fieldRead.containsKey("valueFlowAuthority"));
        assertFalse("field access must not be mislabeled as a local copy",
                edges.stream().anyMatch(edge ->
                        (prefix + "fieldValue").equals(edge.get("toCell"))
                                && "SOOT_EXACT_LOCAL_DIRECT_COPY_V1".equals(
                                edge.get("valueFlowAuthority"))));

        Map<String, Object> exactReturn = edges.stream().filter(edge ->
                "local_def_use".equals(edge.get("kind"))
                        && (prefix + "sum").equals(edge.get("fromCell"))
                        && (method.getSignature() + ".return").equals(
                        edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing final return-local copy"));
        assertEquals("value_flow", exactReturn.get("relation"));
        assertEquals("SOOT_EXACT_LOCAL_DIRECT_COPY_V1",
                exactReturn.get("valueFlowAuthority"));
    }

    @Test
    public void mapValuesToArrayClosesReceiverBackToMapField()
            throws Exception {
        CollectionProjectionFixture fixture = collectionProjectionFixture();
        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, fixture.exportMethod);

        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, fixture.exportMethod.getSignature());
        relevantCells.add(fixture.exportMethod.getSignature() + ".return");

        Method processMethod = analyzer.getClass().getDeclaredMethod(
                "processMethod", String.class);
        processMethod.setAccessible(true);
        for (int round = 0; round < 5; round++) {
            processMethod.invoke(analyzer,
                    fixture.exportMethod.getSignature());
        }

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        String method = fixture.exportMethod.getSignature();

        Map<String, Object> snapshot = edges.stream().filter(edge ->
                "container_snapshot_projection".equals(edge.get("kind"))
                        && (method + "::view").equals(edge.get("fromCell"))
                        && (method + "::array").equals(edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing Collection.toArray receiver dependency"));
        assertEquals("COLLECTION_TO_ARRAY",
                snapshot.get("containerProjectionOperation"));
        assertEquals("MODEL_TRANSFORM", snapshot.get("transferKind"));
        assertEquals(Boolean.TRUE,
                snapshot.get("receiverValueDependencyComplete"));
        assertEquals(Boolean.TRUE,
                snapshot.get("elementIdentityPreserving"));
        assertEquals("COLLECTION_ELEMENT_REFERENCE_IDENTITY",
                snapshot.get("elementRelation"));
        assertEquals(Boolean.FALSE,
                snapshot.get("containerEqualityAsserted"));

        Map<String, Object> view = edges.stream().filter(edge ->
                "container_backed_view_projection".equals(
                        edge.get("kind"))
                        && (method + "::map").equals(edge.get("fromCell"))
                        && (method + "::view").equals(edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing Map.values receiver dependency"));
        assertEquals("MAP_VALUES_VIEW",
                view.get("containerProjectionOperation"));
        assertEquals("MAP_VALUE_REFERENCE_IDENTITY",
                view.get("elementRelation"));
        assertEquals(Boolean.TRUE, view.get("backedView"));
        assertTrue(edges.stream().anyMatch(edge ->
                "field_read".equals(edge.get("kind"))
                        && fixture.field.getSignature().equals(
                        edge.get("fromCell"))
                        && (method + "::map").equals(edge.get("toCell"))));
    }

    @Test
    public void projectedArrayElementFieldsCloseBackToArrayPayload()
            throws Exception {
        ArrayPayloadFixture fixture = arrayPayloadFixture();
        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, fixture.consumeMethod);

        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, fixture.consumeMethod.getSignature());
        relevantCells.add(fixture.outputField.getSignature());

        Method processMethod = analyzer.getClass().getDeclaredMethod(
                "processMethod", String.class);
        processMethod.setAccessible(true);
        for (int round = 0; round < 8; round++) {
            processMethod.invoke(analyzer,
                    fixture.consumeMethod.getSignature());
        }
        Method expandMethodCallers = analyzer.getClass().getDeclaredMethod(
                "expandMethodCallers", String.class);
        expandMethodCallers.setAccessible(true);
        expandMethodCallers.invoke(analyzer,
                fixture.consumeMethod.getSignature());
        for (int round = 0; round < 3; round++) {
            processMethod.invoke(analyzer,
                    fixture.receiveMethod.getSignature());
        }

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        String method = fixture.consumeMethod.getSignature();
        String array = method + "::received";
        String element = method + "::key";
        String payload = method + "::payload";
        String formal = method + ".param0:" + fixture.payload.getName();

        assertTrue("the demanded element fields must retain the exact "
                        + "array-load provenance",
                edges.stream().anyMatch(edge ->
                        "local_def_use".equals(edge.get("kind"))
                                && array.equals(edge.get("fromCell"))
                                && element.equals(edge.get("toCell"))
                                && String.valueOf(edge.get("unit"))
                                .contains("received[0]")));
        assertTrue("getAllKeys must close the array local to its canonical "
                        + "declared payload field",
                edges.stream().anyMatch(edge ->
                        "accessor_field_return".equals(edge.get("kind"))
                                && fixture.payloadArrayField.getSignature()
                                .equals(edge.get("fromCell"))
                                && array.equals(edge.get("toCell"))));
        assertTrue("the payload argument must carry the allKeys projection "
                        + "toward an enclosing heartbeat/registration call",
                edges.stream().anyMatch(edge ->
                        "projected_local_def_use".equals(edge.get("kind"))
                                && (formal + "#field:allKeys").equals(
                                edge.get("fromCell"))
                                && (payload + "#field:allKeys").equals(
                                edge.get("toCell"))));
        assertTrue("the same projection must cross an ordinary enclosing "
                        + "caller without a workload-specific method name",
                edges.stream().anyMatch(edge ->
                        "projected_method_caller_argument".equals(
                                edge.get("kind"))
                                && (fixture.receiveMethod.getSignature()
                                + "::wire#field:allKeys").equals(
                                edge.get("fromCell"))
                                && (formal + "#field:allKeys").equals(
                                edge.get("toCell"))));
        assertTrue(edges.stream().anyMatch(edge ->
                "accessor_field_return".equals(edge.get("kind"))
                        && (element + "#field:keyId").equals(
                        edge.get("fromCell"))
                        && (method + "::keyId").equals(edge.get("toCell"))));
        assertTrue(edges.stream().anyMatch(edge ->
                "accessor_field_return".equals(edge.get("kind"))
                        && (element + "#field:expiryDate").equals(
                        edge.get("fromCell"))
                        && (method + "::expiry").equals(edge.get("toCell"))));
    }

    @Test
    public void runtimeSelectedInterfaceTargetRecursivelyCarriesFieldProjection()
            throws Exception {
        RuntimeDispatchFixture fixture = runtimeDispatchFixture();
        Path evidence = runtimeCallEdges(fixture,
                Collections.singletonList(
                        fixture.actualMethod.getSignature()));
        System.setProperty("causynth.runtime.call.edges",
                evidence.toString());

        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, fixture.callerMethod);
        Method parseMethodSig = CausynthPipeline.class.getDeclaredMethod(
                "parseMethodSig", String.class);
        parseMethodSig.setAccessible(true);
        Object declared = parseMethodSig.invoke(null,
                fixture.interfaceMethod.getSignature());
        Method resolveDispatchTargets = analyzer.getClass().getDeclaredMethod(
                "resolveDispatchTargets", declared.getClass());
        resolveDispatchTargets.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<String> hierarchyTargets = (List<String>)
                resolveDispatchTargets.invoke(analyzer, declared);
        assertTrue("static hierarchy must include the concrete runtime target: "
                        + hierarchyTargets,
                hierarchyTargets.contains(
                        fixture.actualMethod.getSignature()));
        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, fixture.callerMethod.getSignature());
        relevantCells.add(fixture.callerMethod.getSignature()
                + "::product#field:keyId");
        Field selectedField = analyzer.getClass().getDeclaredField(
                "selectedMethods");
        selectedField.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> selected = (Set<String>) selectedField.get(analyzer);
        selected.add(fixture.callerMethod.getSignature());

        Method runWorklist = analyzer.getClass().getDeclaredMethod(
                "runWorklist");
        runWorklist.setAccessible(true);
        runWorklist.invoke(analyzer);

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        String callerProduct = fixture.callerMethod.getSignature()
                + "::product";
        String actualReturn = fixture.actualMethod.getSignature()
                + ".return";

        Map<String, Object> dispatch = edges.stream().filter(edge ->
                "dispatch_return".equals(edge.get("kind"))
                        && actualReturn.equals(edge.get("fromCell"))
                        && callerProduct.equals(edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing runtime-selected concrete dispatch return; "
                                + "relevant=" + relevantCells
                                + "; edges=" + edges));
        assertEquals(Boolean.TRUE,
                dispatch.get("runtimeSelectedDispatch"));
        assertEquals("UNIQUE_CALLSITE_CORRELATED_ACTUAL_CALLEE_V1",
                dispatch.get("dispatchSelectionAuthority"));
        assertEquals(fixture.actualMethod.getSignature(),
                dispatch.get("runtimeActualCallee"));
        assertFalse("a runtime-selected dispatch must not retain a parallel "
                        + "opaque declared-interface return",
                edges.stream().anyMatch(edge ->
                        "call_return".equals(edge.get("kind"))
                                && (fixture.interfaceMethod.getSignature()
                                + ".return").equals(
                                edge.get("fromCell"))
                                && callerProduct.equals(
                                edge.get("toCell"))));
        assertFalse("an unobserved implementation must not be merged into "
                        + "the same call-site definition",
                edges.stream().anyMatch(edge ->
                        String.valueOf(edge.get("fromCell")).startsWith(
                                fixture.alternativeMethod.getSignature()
                                        + ".return")
                                && callerProduct.equals(
                                edge.get("toCell"))));
        assertTrue("the caller's demanded keyId projection must recurse "
                        + "through the selected implementation's cached field",
                edges.stream().anyMatch(edge ->
                        "projected_field_read".equals(edge.get("kind"))
                                && (fixture.actualCached.getSignature()
                                + "#field:keyId").equals(
                                edge.get("fromCell"))));

        Field recursiveField = analyzer.getClass().getDeclaredField(
                "runtimeRecursiveMethods");
        recursiveField.setAccessible(true);
        assertTrue(((Set<?>) recursiveField.get(analyzer)).contains(
                fixture.actualMethod.getSignature()));
    }

    @Test
    public void ambiguousRuntimeInterfaceTargetFailsClosed()
            throws Exception {
        RuntimeDispatchFixture fixture = runtimeDispatchFixture();
        Path evidence = runtimeCallEdges(fixture, Arrays.asList(
                fixture.actualMethod.getSignature(),
                fixture.alternativeMethod.getSignature()));
        System.setProperty("causynth.runtime.call.edges",
                evidence.toString());

        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, fixture.callerMethod);
        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, fixture.callerMethod.getSignature());
        relevantCells.add(fixture.callerMethod.getSignature()
                + "::product#field:keyId");
        Field selectedField = analyzer.getClass().getDeclaredField(
                "selectedMethods");
        selectedField.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> selected = (Set<String>) selectedField.get(analyzer);
        selected.add(fixture.callerMethod.getSignature());

        Method runWorklist = analyzer.getClass().getDeclaredMethod(
                "runWorklist");
        runWorklist.setAccessible(true);
        runWorklist.invoke(analyzer);

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        assertFalse("two actual callees at one exact runtime site cannot be "
                        + "asserted as one symbolic value",
                edges.stream().anyMatch(edge ->
                        String.valueOf(edge.get("kind"))
                                .contains("dispatch")
                                && fixture.callerMethod.getSignature().equals(
                                edge.get("method"))));
        Field blockedField = analyzer.getClass().getDeclaredField(
                "blockedRuntimeDispatchSites");
        blockedField.setAccessible(true);
        assertTrue("blocked=" + blockedField.get(analyzer)
                        + "; relevant=" + relevantCells + "; edges=" + edges,
                String.valueOf(blockedField.get(analyzer)).contains(
                        "AMBIGUOUS_RUNTIME_ACTUAL_CALLEE"));
    }

    @Test
    public void unsupportedLibrarySnapshotDoesNotGainReceiverValueFlow()
            throws Exception {
        CollectionProjectionFixture fixture = collectionProjectionFixture();
        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, fixture.unsupportedMethod);

        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, fixture.unsupportedMethod.getSignature());
        relevantCells.add(fixture.unsupportedMethod.getSignature()
                + ".return");

        Method processMethod = analyzer.getClass().getDeclaredMethod(
                "processMethod", String.class);
        processMethod.setAccessible(true);
        for (int round = 0; round < 3; round++) {
            processMethod.invoke(analyzer,
                    fixture.unsupportedMethod.getSignature());
        }

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        String method = fixture.unsupportedMethod.getSignature();
        assertFalse("an unsupported value-producing library call must keep "
                        + "its receiver unrelated to the result",
                edges.stream().anyMatch(edge ->
                        (method + "::view").equals(edge.get("fromCell"))
                                && (method + "::array").equals(
                                edge.get("toCell"))));
        assertTrue("the unsupported result must remain an opaque call-return "
                        + "frontier",
                edges.stream().anyMatch(edge ->
                        "call_return".equals(edge.get("kind"))
                                && fixture.unsupportedCallee.getSignature()
                                .concat(".return").equals(
                                edge.get("fromCell"))
                                && (method + "::array").equals(
                                edge.get("toCell"))));
    }

    @Test
    public void containerProjectionWhitelistCoversExactMapViewsAndToArray()
            throws Exception {
        CollectionProjectionFixture fixture = collectionProjectionFixture();
        Object analyzer = newStaticAnalyzer();
        Class<?> pipeline = CausynthPipeline.class;
        Method parse = pipeline.getDeclaredMethod("parseMethodSig",
                String.class);
        parse.setAccessible(true);
        Class<?> signature = Class.forName(CausynthPipeline.class.getName()
                + "$MethodSig");
        Method operation = analyzer.getClass().getDeclaredMethod(
                "semanticContainerProjectionOperation", signature);
        operation.setAccessible(true);

        assertEquals("MAP_VALUES_VIEW", operation.invoke(analyzer,
                parse.invoke(null, "<java.util.Map: java.util.Collection "
                        + "values()>")));
        assertEquals("MAP_KEY_SET_VIEW", operation.invoke(analyzer,
                parse.invoke(null, "<java.util.Map: java.util.Set "
                        + "keySet()>")));
        assertEquals("MAP_ENTRY_SET_VIEW", operation.invoke(analyzer,
                parse.invoke(null, "<java.util.Map: java.util.Set "
                        + "entrySet()>")));
        assertEquals("COLLECTION_TO_ARRAY", operation.invoke(analyzer,
                parse.invoke(null, "<java.util.Collection: java.lang.Object[] "
                        + "toArray(java.lang.Object[])>")));
        assertEquals("", operation.invoke(analyzer,
                parse.invoke(null, "<third.party.MapLike: java.util.Collection "
                        + "values()>")));
        assertNotNull(fixture.exportMethod);
    }

    @Test
    public void voidIteratorMutationRetainsItsDominatingHeapGuard()
            throws Exception {
        IteratorMutationFixture fixture = iteratorMutationFixture();
        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, fixture.method);

        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, fixture.method.getSignature());
        relevantCells.add(fixture.field.getSignature());

        Method processMethod = analyzer.getClass().getDeclaredMethod(
                "processMethod", String.class);
        processMethod.setAccessible(true);
        // The first pass discovers the mutation and its guard operands; the
        // second closes those operands back through their identity bindings.
        processMethod.invoke(analyzer, fixture.method.getSignature());
        processMethod.invoke(analyzer, fixture.method.getSignature());

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);

        assertTrue("Iterator.remove must become a write of the owning map field",
                edges.stream().anyMatch(edge ->
                        "field_mutation".equals(edge.get("kind"))
                                && fixture.field.getSignature().equals(
                                edge.get("toCell"))
                                && fixture.removeUnitIndex == intValue(
                                edge.get("unitIndex"))));

        String method = fixture.method.getSignature();
        assertTrue("expiry must control the void heap mutation",
                hasHeapMutationGuard(edges, method + "::expiry",
                        fixture.field.getSignature(), fixture.guardUnitIndex));
        assertTrue("now must control the void heap mutation",
                hasHeapMutationGuard(edges, method + "::now",
                        fixture.field.getSignature(), fixture.guardUnitIndex));
        Map<String, Object> expiryGuard = edges.stream().filter(edge ->
                "heap_mutation_path_guard".equals(edge.get("kind"))
                        && (method + "::expiry").equals(edge.get("fromCell"))
                        && fixture.field.getSignature().equals(
                        edge.get("toCell"))).findFirst().orElseThrow(
                () -> new AssertionError("missing expiry mutation guard"));
        assertEquals(method + "#u" + fixture.guardUnitIndex,
                expiryGuard.get("guardSiteId"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> guardedMutations =
                (List<Map<String, Object>>) expiryGuard.get(
                        "guardedMutations");
        assertEquals("deduped guard/state edge must retain both writes", 2,
                guardedMutations.size());
        Map<String, Object> removeGuard = guardedMutations.stream()
                .filter(item -> (method + "#u" + fixture.removeUnitIndex)
                        .equals(item.get("guardedMutationSiteId")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing Iterator.remove guarded site"));
        assertEquals(Boolean.FALSE, removeGuard.get("requiredOutcome"));

        Map<String, Object> compactReference = new LinkedHashMap<>();
        compactReference.put("edgeId", expiryGuard.get("id"));
        compactReference.put("kind", expiryGuard.get("kind"));
        Map<String, Object> outputSlice = new LinkedHashMap<>();
        outputSlice.put("causalEdges",
                Collections.singletonList(compactReference));
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("outputSlices", Collections.singletonList(outputSlice));
        CausynthPipeline.enrichHeapMutationGuardMetadata(
                Collections.singletonList(region), edges);
        assertEquals(method + "#u" + fixture.guardUnitIndex,
                compactReference.get("guardSiteId"));
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> sliceMutations =
                (List<Map<String, Object>>) compactReference.get(
                        "guardedMutations");
        assertTrue("static output slice must expose expiry guard -> remove",
                sliceMutations.stream().anyMatch(item ->
                        (method + "#u" + fixture.removeUnitIndex).equals(
                                item.get("guardedMutationSiteId"))
                                && Boolean.FALSE.equals(
                                item.get("requiredOutcome"))));
        assertTrue("guard operands must close to the method input frontier",
                edges.stream().anyMatch(edge ->
                        (method + ".param0:long").equals(edge.get("fromCell"))
                                && (method + "::expiry").equals(
                                edge.get("toCell")))
                        && edges.stream().anyMatch(edge ->
                        (method + ".param1:long").equals(edge.get("fromCell"))
                                && (method + "::now").equals(
                                edge.get("toCell"))));
        assertFalse("a Jimple cmp expression is derived from its leaf uses, "
                        + "not an independent symbolic frontier",
                edges.stream().anyMatch(edge ->
                        String.valueOf(edge.get("fromCell")).contains(" cmp ")));
    }

    @Test
    public void loopMutationGuardIsScopedToTheCurrentIteration()
            throws Exception {
        LoopIteratorMutationFixture fixture = loopIteratorMutationFixture();
        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, fixture.method);

        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, fixture.method.getSignature());
        relevantCells.add(fixture.field.getSignature());

        Method processMethod = analyzer.getClass().getDeclaredMethod(
                "processMethod", String.class);
        processMethod.setAccessible(true);
        processMethod.invoke(analyzer, fixture.method.getSignature());
        processMethod.invoke(analyzer, fixture.method.getSignature());

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        String method = fixture.method.getSignature();

        Map<String, Object> expiryGuard = edges.stream().filter(edge ->
                "heap_mutation_path_guard".equals(edge.get("kind"))
                        && (method + "::expiry").equals(edge.get("fromCell"))
                        && fixture.expiryGuardUnitIndex == intValue(
                        edge.get("unitIndex"))).findFirst().orElseThrow(
                () -> new AssertionError("missing loop expiry guard"));
        assertEquals("the skip successor may reach remove only by revisiting "
                        + "this predicate in another iteration",
                Boolean.FALSE, expiryGuard.get("requiredOutcome"));
        assertEquals(method + "#u" + fixture.removeUnitIndex,
                expiryGuard.get("guardedMutationSiteId"));

        Map<String, Object> loopGuard = edges.stream().filter(edge ->
                "heap_mutation_path_guard".equals(edge.get("kind"))
                        && (method + "::hasNext").equals(edge.get("fromCell"))
                        && fixture.loopGuardUnitIndex == intValue(
                        edge.get("unitIndex"))).findFirst().orElseThrow(
                () -> new AssertionError("missing structural loop guard"));
        assertEquals(Boolean.FALSE, loopGuard.get("requiredOutcome"));
    }

    @Test
    public void inheritedAccessorUsesCanonicalDeclaredFieldOwner()
            throws Exception {
        InheritedAccessorFixture fixture = inheritedAccessorFixture();
        Object analyzer = newStaticAnalyzer();
        loadFacts(analyzer, fixture.method);

        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> relevantCells = (Set<String>) relevant.invoke(
                analyzer, fixture.method.getSignature());
        String result = fixture.method.getSignature() + "::expiry";
        relevantCells.add(result);

        Method processMethod = analyzer.getClass().getDeclaredMethod(
                "processMethod", String.class);
        processMethod.setAccessible(true);
        processMethod.invoke(analyzer, fixture.method.getSignature());

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        String canonical = fixture.field.getSignature();
        Map<String, Object> declaredRead = edges.stream().filter(edge ->
                "accessor_field_return".equals(edge.get("kind"))
                        && canonical.equals(edge.get("fromCell"))
                        && result.equals(edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing canonical inherited accessor field"));

        assertEquals("HEAP_READ", declaredRead.get("transferKind"));
        assertEquals(fixture.base.getName(),
                declaredRead.get("declaredFieldOwner"));
        assertEquals("long", declaredRead.get("declaredFieldType"));
        assertEquals("expiryDate", declaredRead.get("declaredFieldName"));
        assertEquals(canonical, declaredRead.get("declaredFieldSignature"));
        assertEquals("<example.DelegationKey: long getExpiryDate()>",
                declaredRead.get("accessorImplementationMethod"));
        assertEquals("SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY",
                declaredRead.get("accessorImplementationAuthority"));
        assertFalse("the invocation subclass must not be fabricated as the "
                        + "field declaration owner",
                edges.stream().anyMatch(edge ->
                        ("<" + fixture.child.getName()
                                + ": long expiryDate>").equals(
                                edge.get("fromCell"))));
        assertTrue("receiver-local provenance remains available in parallel",
                edges.stream().anyMatch(edge ->
                        "accessor_field_return".equals(edge.get("kind"))
                                && (fixture.method.getSignature()
                                + "::key#field:expiryDate").equals(
                                edge.get("fromCell"))
                                && "PROJECTION".equals(
                                edge.get("transferKind"))));
    }

    @Test
    public void hdfsScopedIndexRecursesThroughConstantSetterAndCallerGuard()
            throws Exception {
        RecursiveFieldWriterFixture fixture = recursiveFieldWriterFixture();
        Object analyzer = newStaticAnalyzer("hdfs_block_key");

        // Reproduce the fast-path failure mode: only the downstream reader is
        // retained initially. The writer, setter caller, and guard-producing
        // method are application methods but are absent from factsByMethod.
        loadFacts(analyzer, fixture.reader);
        Method relevant = analyzer.getClass().getDeclaredMethod(
                "relevant", String.class);
        relevant.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> readerRelevant = (Set<String>) relevant.invoke(
                analyzer, fixture.reader.getSignature());
        readerRelevant.add(fixture.reader.getSignature() + ".return");
        Field selectedField = analyzer.getClass().getDeclaredField(
                "selectedMethods");
        selectedField.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> selected = (Set<String>) selectedField.get(analyzer);
        selected.add(fixture.reader.getSignature());

        Method runWorklist = analyzer.getClass().getDeclaredMethod(
                "runWorklist");
        runWorklist.setAccessible(true);
        runWorklist.invoke(analyzer);

        Field factsField = analyzer.getClass().getDeclaredField(
                "factsByMethod");
        factsField.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<String, List<?>> facts =
                (Map<String, List<?>>) factsField.get(analyzer);
        assertTrue("global writer discovery must load the previously absent setter",
                facts.containsKey(fixture.setter.getSignature()));
        assertTrue("constant setter calls must still select their guarded caller",
                facts.containsKey(fixture.monitor.getSignature()));
        assertTrue("the caller guard result must recurse into its producer",
                facts.containsKey(fixture.shouldUpdate.getSignature()));
        assertTrue(selected.contains(fixture.setter.getSignature()));
        assertTrue(selected.contains(fixture.monitor.getSignature()));
        assertTrue(selected.contains(fixture.shouldUpdate.getSignature()));

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        String setterFormal = fixture.setter.getSignature()
                + ".param0:boolean";
        String monitorGuard = fixture.monitor.getSignature()
                + "::shouldUpdate";

        Map<String, Object> literal = edges.stream().filter(edge ->
                "method_caller_literal_argument".equals(edge.get("kind"))
                        && setterFormal.equals(edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing exact typed true literal provenance"));
        assertEquals(fixture.monitor.getSignature() + "#u5",
                literal.get("fromCell"));
        assertEquals("boolean", literal.get("literalJavaType"));
        assertEquals("true", literal.get("literalValue"));
        assertEquals(Boolean.FALSE, literal.get("literalIsSymbolicInput"));
        assertEquals("JIMPLE_TYPED_CONSTANT_AT_EXACT_CALLSITE_V1",
                literal.get("literalAuthority"));

        Map<String, Object> effectGuard = edges.stream().filter(edge ->
                "receiver_field_effect_path_guard".equals(edge.get("kind"))
                        && monitorGuard.equals(edge.get("fromCell"))
                        && fixture.field.getSignature().equals(
                        edge.get("toCell")))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "missing caller-side control dependence for field effect"));
        assertEquals("GUARD", effectGuard.get("transferKind"));
        assertEquals(Boolean.FALSE, effectGuard.get("requiredOutcome"));
        assertEquals(fixture.setter.getSignature(),
                effectGuard.get("calleeMethod"));
        assertEquals(fixture.monitor.getSignature() + "#u5",
                effectGuard.get("effectSiteId"));
        assertTrue("shouldUpdate result must close to the monitor guard local",
                edges.stream().anyMatch(edge ->
                        "call_return".equals(edge.get("kind"))
                                && (fixture.shouldUpdate.getSignature()
                                + ".return").equals(edge.get("fromCell"))
                                && monitorGuard.equals(edge.get("toCell"))));
        assertTrue("setter formal must still flow into the shared field",
                edges.stream().anyMatch(edge ->
                        "field_write".equals(edge.get("kind"))
                                && fixture.field.getSignature().equals(
                                edge.get("toCell"))));

        Field candidateCount = analyzer.getClass().getDeclaredField(
                "globalStaticIndexCandidateMethodCount");
        candidateCount.setAccessible(true);
        assertEquals("the HDFS scoped working set must not scope the global index",
                4, candidateCount.getInt(analyzer));
        Field truncatedWriters = analyzer.getClass().getDeclaredField(
                "truncatedFieldWriterIndexFields");
        truncatedWriters.setAccessible(true);
        assertTrue(((Set<?>) truncatedWriters.get(analyzer)).isEmpty());
        Field truncatedCallers = analyzer.getClass().getDeclaredField(
                "truncatedMethodCallerIndexMethods");
        truncatedCallers.setAccessible(true);
        assertTrue(((Set<?>) truncatedCallers.get(analyzer)).isEmpty());
    }

    @Test
    public void instrumentsApplicationOriginForBackedViewIteratorRemoval()
            throws Exception {
        IteratorMutationFixture fixture = iteratorMutationFixture();
        Class<?> refsClass = Class.forName(
                CausynthPipeline.class.getName() + "$ConcolicRegionRefs");
        Method create = refsClass.getDeclaredMethod("create");
        create.setAccessible(true);
        Object refs = create.invoke(null);
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicBackedViewMutations", Set.class,
                refsClass);
        instrument.setAccessible(true);

        int count = (Integer) instrument.invoke(
                new CausynthPipeline(null, 0, 0),
                Collections.singleton(fixture.method.getSignature()), refs);

        assertEquals(4, count);
        Map<String, InvokeExpr> hooks = new LinkedHashMap<>();
        for (Unit unit : fixture.method.getActiveBody().getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
            String name = invoke.getMethodRef().name();
            if (name.startsWith("registerMapView")
                    || name.startsWith("recordMapIterator")) {
                hooks.put(name, invoke);
            }
        }
        assertTrue(hooks.containsKey("registerMapView"));
        assertTrue(hooks.containsKey("registerMapViewIterator"));
        assertTrue(hooks.containsKey("recordMapIteratorNext"));
        assertTrue(hooks.containsKey("recordMapIteratorRemove"));
        InvokeExpr remove = hooks.get("recordMapIteratorRemove");
        assertEquals(fixture.method.getSignature(),
                remove.getArg(0).toString().replace("\"", ""));
        assertEquals(fixture.removeUnitIndex,
                ((soot.jimple.IntConstant) remove.getArg(1)).value);
        List<Unit> ordered = new ArrayList<>();
        Unit originalRemove = null;
        Unit removeHook = null;
        for (Unit unit : fixture.method.getActiveBody().getUnits()) {
            ordered.add(unit);
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            String name = ((Stmt) unit).getInvokeExpr()
                    .getMethodRef().name();
            String owner = ((Stmt) unit).getInvokeExpr()
                    .getMethodRef().declaringClass().getName();
            if ("remove".equals(name)
                    && "java.util.Iterator".equals(owner)) {
                originalRemove = unit;
            } else if ("recordMapIteratorRemove".equals(name)) {
                removeHook = unit;
            }
        }
        assertNotNull(originalRemove);
        assertNotNull(removeHook);
        assertTrue("remove provenance must be a normal-return post hook",
                ordered.indexOf(originalRemove) < ordered.indexOf(removeHook));
    }

    private static boolean hasHeapMutationGuard(
            List<Map<String, Object>> edges, String source, String target,
            int guardUnitIndex) {
        return edges.stream().anyMatch(edge ->
                "heap_mutation_path_guard".equals(edge.get("kind"))
                        && "GUARD".equals(edge.get("transferKind"))
                        && source.equals(edge.get("fromCell"))
                        && target.equals(edge.get("toCell"))
                        && guardUnitIndex == intValue(edge.get("unitIndex")));
    }

    private static int intValue(Object value) {
        return value instanceof Number ? ((Number) value).intValue() : -1;
    }

    private static void registerStaticPortMapping(Object analyzer,
                                                  String kind,
                                                  String method,
                                                  String from,
                                                  String to)
            throws Exception {
        Method register = analyzer.getClass().getDeclaredMethod(
                "addStaticPortMapping", String.class, String.class,
                String.class, String.class, String.class, String.class);
        register.setAccessible(true);
        register.invoke(analyzer, kind, method, from, method, to,
                "test static port mapping");
    }

    private static Map<String, Object> emitSyntheticEdge(
            Object analyzer, String kind, String from, String to,
            String method, Map<String, Object> projectionBase)
            throws Exception {
        Method emitter = Arrays.stream(analyzer.getClass()
                        .getDeclaredMethods())
                .filter(candidate -> "addEdgeInternal".equals(
                        candidate.getName()))
                .filter(candidate -> candidate.getParameterTypes().length
                        == 8)
                .findFirst().orElseThrow(AssertionError::new);
        emitter.setAccessible(true);
        assertEquals(Boolean.TRUE, emitter.invoke(analyzer, kind, from, to,
                method, null, "test projected authority", false,
                projectionBase));

        Field edgesField = analyzer.getClass().getDeclaredField("edges");
        edgesField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> edges =
                (List<Map<String, Object>>) edgesField.get(analyzer);
        return edges.stream().filter(edge -> kind.equals(edge.get("kind"))
                        && from.equals(edge.get("fromCell"))
                        && to.equals(edge.get("toCell")))
                .findFirst().orElseThrow(AssertionError::new);
    }

    private static Map<String, Object> projectionBase(
            String id, boolean mappingOnly, boolean semanticAllowed,
            boolean derivationAllowed, boolean smtAllowed) {
        Map<String, Object> base = new LinkedHashMap<>();
        base.put("id", id);
        base.put("kind", "fixture_field_transfer");
        base.put("relation", "value_flow");
        base.put("mappingOnly", mappingOnly);
        base.put("mappingAuthority", mappingOnly
                ? "STATIC_FORMAT_AND_PORT_MAPPING" : "");
        base.put("semanticAssertionsAllowed", semanticAllowed);
        base.put("eligibleForAutomaticDerivation", derivationAllowed);
        base.put("eligibleForAutomaticSmt", smtAllowed);
        return base;
    }

    private static Object newStaticAnalyzer() throws Exception {
        return newStaticAnalyzer("");
    }

    private static Object newStaticAnalyzer(String analysisScope)
            throws Exception {
        Class<?> targetClass = Class.forName(
                CausynthPipeline.class.getName() + "$TargetContext");
        Constructor<?> targetConstructor = targetClass.getDeclaredConstructor(
                Path.class, Path.class, Path.class, Path.class, List.class,
                String.class, String.class, String.class);
        targetConstructor.setAccessible(true);
        Path current = Paths.get(".").toAbsolutePath().normalize();
        Object target = targetConstructor.newInstance(current, current,
                current, current, Collections.emptyList(), null, null,
                analysisScope);
        Class<?> analyzerClass = Class.forName(
                CausynthPipeline.class.getName()
                        + "$SeedBackwardStaticAnalyzer");
        Constructor<?> constructor = analyzerClass.getDeclaredConstructor(
                targetClass);
        constructor.setAccessible(true);
        return constructor.newInstance(target);
    }

    private static List<?> loadFacts(Object analyzer, SootMethod method)
            throws Exception {
        Method loadMethod = analyzer.getClass().getDeclaredMethod(
                "loadMethod", SootMethod.class);
        loadMethod.setAccessible(true);
        assertEquals(Boolean.TRUE, loadMethod.invoke(analyzer, method));

        Field factsField = analyzer.getClass().getDeclaredField(
                "factsByMethod");
        factsField.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<String, List<?>> facts =
                (Map<String, List<?>>) factsField.get(analyzer);
        return facts.get(method.getSignature());
    }

    private static RecursiveFieldWriterFixture recursiveFieldWriterFixture() {
        G.reset();

        SootClass descriptor = new SootClass(
                "org.apache.hadoop.hdfs.server.blockmanagement.DatanodeDescriptor",
                Modifier.PUBLIC);
        Scene.v().addClass(descriptor);
        descriptor.setApplicationClass();
        SootField needKeyUpdate = new SootField("needKeyUpdate",
                BooleanType.v(), Modifier.PUBLIC);
        descriptor.addField(needKeyUpdate);
        SootMethod setter = new SootMethod("setNeedKeyUpdate",
                Collections.singletonList(BooleanType.v()), VoidType.v(),
                Modifier.PUBLIC);
        descriptor.addMethod(setter);
        Body setterBody = Jimple.v().newBody(setter);
        setter.setActiveBody(setterBody);
        Local setterThis = Jimple.v().newLocal("self", descriptor.getType());
        Local enabled = Jimple.v().newLocal("enabled", BooleanType.v());
        setterBody.getLocals().addAll(Arrays.asList(setterThis, enabled));
        setterBody.getUnits().add(Jimple.v().newIdentityStmt(setterThis,
                Jimple.v().newThisRef(descriptor.getType())));
        setterBody.getUnits().add(Jimple.v().newIdentityStmt(enabled,
                Jimple.v().newParameterRef(BooleanType.v(), 0)));
        setterBody.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(setterThis,
                        needKeyUpdate.makeRef()), enabled));
        setterBody.getUnits().add(Jimple.v().newReturnVoidStmt());

        SootClass blockManager = new SootClass(
                "org.apache.hadoop.hdfs.server.blockmanagement.BlockManager",
                Modifier.PUBLIC);
        Scene.v().addClass(blockManager);
        blockManager.setApplicationClass();
        SootMethod shouldUpdate = new SootMethod("shouldUpdateBlockKey",
                Collections.singletonList(BooleanType.v()), BooleanType.v(),
                Modifier.PUBLIC);
        blockManager.addMethod(shouldUpdate);
        Body shouldBody = Jimple.v().newBody(shouldUpdate);
        shouldUpdate.setActiveBody(shouldBody);
        Local shouldThis = Jimple.v().newLocal("self",
                blockManager.getType());
        Local due = Jimple.v().newLocal("due", BooleanType.v());
        shouldBody.getLocals().addAll(Arrays.asList(shouldThis, due));
        shouldBody.getUnits().add(Jimple.v().newIdentityStmt(shouldThis,
                Jimple.v().newThisRef(blockManager.getType())));
        shouldBody.getUnits().add(Jimple.v().newIdentityStmt(due,
                Jimple.v().newParameterRef(BooleanType.v(), 0)));
        shouldBody.getUnits().add(Jimple.v().newReturnStmt(due));

        SootMethod reader = new SootMethod("addKeyUpdateCommand",
                Collections.singletonList(descriptor.getType()),
                BooleanType.v(), Modifier.PUBLIC | Modifier.STATIC);
        blockManager.addMethod(reader);
        Body readerBody = Jimple.v().newBody(reader);
        reader.setActiveBody(readerBody);
        Local readerDescriptor = Jimple.v().newLocal("datanode",
                descriptor.getType());
        Local observed = Jimple.v().newLocal("observed",
                BooleanType.v());
        readerBody.getLocals().addAll(Arrays.asList(readerDescriptor,
                observed));
        readerBody.getUnits().add(Jimple.v().newIdentityStmt(readerDescriptor,
                Jimple.v().newParameterRef(descriptor.getType(), 0)));
        readerBody.getUnits().add(Jimple.v().newAssignStmt(observed,
                Jimple.v().newInstanceFieldRef(readerDescriptor,
                        needKeyUpdate.makeRef())));
        readerBody.getUnits().add(Jimple.v().newReturnStmt(observed));

        SootClass monitorClass = new SootClass(
                "org.apache.hadoop.hdfs.server.blockmanagement.HeartbeatManager$Monitor",
                Modifier.PUBLIC);
        Scene.v().addClass(monitorClass);
        monitorClass.setApplicationClass();
        SootMethod monitor = new SootMethod("run",
                Arrays.asList(blockManager.getType(), descriptor.getType(),
                        BooleanType.v()), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        monitorClass.addMethod(monitor);
        Body monitorBody = Jimple.v().newBody(monitor);
        monitor.setActiveBody(monitorBody);
        Local manager = Jimple.v().newLocal("manager",
                blockManager.getType());
        Local monitorDescriptor = Jimple.v().newLocal("datanode",
                descriptor.getType());
        Local monitorDue = Jimple.v().newLocal("due", BooleanType.v());
        Local should = Jimple.v().newLocal("shouldUpdate",
                BooleanType.v());
        monitorBody.getLocals().addAll(Arrays.asList(manager,
                monitorDescriptor, monitorDue, should));
        monitorBody.getUnits().add(Jimple.v().newIdentityStmt(manager,
                Jimple.v().newParameterRef(blockManager.getType(), 0)));
        monitorBody.getUnits().add(Jimple.v().newIdentityStmt(
                monitorDescriptor,
                Jimple.v().newParameterRef(descriptor.getType(), 1)));
        monitorBody.getUnits().add(Jimple.v().newIdentityStmt(monitorDue,
                Jimple.v().newParameterRef(BooleanType.v(), 2)));
        monitorBody.getUnits().add(Jimple.v().newAssignStmt(should,
                Jimple.v().newVirtualInvokeExpr(manager,
                        shouldUpdate.makeRef(), monitorDue)));
        Stmt done = Jimple.v().newReturnVoidStmt();
        monitorBody.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(should, IntConstant.v(0)), done));
        monitorBody.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newVirtualInvokeExpr(monitorDescriptor,
                        setter.makeRef(), IntConstant.v(1))));
        monitorBody.getUnits().add(done);

        return new RecursiveFieldWriterFixture(reader, setter, monitor,
                shouldUpdate, needKeyUpdate);
    }

    private static CollectionProjectionFixture collectionProjectionFixture() {
        G.reset();

        SootClass map = new SootClass("java.util.Map",
                Modifier.PUBLIC | Modifier.INTERFACE);
        SootClass collection = new SootClass("java.util.Collection",
                Modifier.PUBLIC | Modifier.INTERFACE);
        Scene.v().addClass(map);
        Scene.v().addClass(collection);
        ArrayType objectArray = ArrayType.v(
                RefType.v("java.lang.Object"), 1);
        SootMethod values = new SootMethod("values",
                Collections.emptyList(), RefType.v("java.util.Collection"),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod toArray = new SootMethod("toArray",
                Collections.singletonList(objectArray), objectArray,
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod unsupported = new SootMethod("snapshot",
                Collections.emptyList(), objectArray,
                Modifier.PUBLIC | Modifier.ABSTRACT);
        map.addMethod(values);
        collection.addMethod(toArray);
        collection.addMethod(unsupported);

        SootClass owner = new SootClass("example.CollectionProjectionOwner",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootField field = new SootField("allKeys",
                RefType.v("java.util.Map"), Modifier.PRIVATE);
        owner.addField(field);

        SootMethod exportMethod = new SootMethod("exportKeys",
                Collections.emptyList(), objectArray, Modifier.PUBLIC);
        owner.addMethod(exportMethod);
        Body exportBody = Jimple.v().newBody(exportMethod);
        exportMethod.setActiveBody(exportBody);
        Local receiver = Jimple.v().newLocal("self", owner.getType());
        Local mapLocal = Jimple.v().newLocal("map",
                RefType.v("java.util.Map"));
        Local viewLocal = Jimple.v().newLocal("view",
                RefType.v("java.util.Collection"));
        Local templateLocal = Jimple.v().newLocal("template", objectArray);
        Local arrayLocal = Jimple.v().newLocal("array", objectArray);
        exportBody.getLocals().addAll(Arrays.asList(receiver, mapLocal,
                viewLocal, templateLocal, arrayLocal));
        exportBody.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(owner.getType())));
        exportBody.getUnits().add(Jimple.v().newAssignStmt(mapLocal,
                Jimple.v().newInstanceFieldRef(receiver, field.makeRef())));
        exportBody.getUnits().add(Jimple.v().newAssignStmt(viewLocal,
                Jimple.v().newInterfaceInvokeExpr(mapLocal,
                        values.makeRef())));
        exportBody.getUnits().add(Jimple.v().newAssignStmt(templateLocal,
                Jimple.v().newNewArrayExpr(RefType.v("java.lang.Object"),
                        IntConstant.v(0))));
        exportBody.getUnits().add(Jimple.v().newAssignStmt(arrayLocal,
                Jimple.v().newInterfaceInvokeExpr(viewLocal,
                        toArray.makeRef(), templateLocal)));
        exportBody.getUnits().add(Jimple.v().newReturnStmt(arrayLocal));

        SootMethod unsupportedMethod = new SootMethod(
                "unsupportedSnapshot",
                Collections.singletonList(RefType.v("java.util.Collection")),
                objectArray, Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(unsupportedMethod);
        Body unsupportedBody = Jimple.v().newBody(unsupportedMethod);
        unsupportedMethod.setActiveBody(unsupportedBody);
        Local unsupportedView = Jimple.v().newLocal("view",
                RefType.v("java.util.Collection"));
        Local unsupportedArray = Jimple.v().newLocal("array", objectArray);
        unsupportedBody.getLocals().addAll(Arrays.asList(unsupportedView,
                unsupportedArray));
        unsupportedBody.getUnits().add(Jimple.v().newIdentityStmt(
                unsupportedView, Jimple.v().newParameterRef(
                        RefType.v("java.util.Collection"), 0)));
        unsupportedBody.getUnits().add(Jimple.v().newAssignStmt(
                unsupportedArray, Jimple.v().newInterfaceInvokeExpr(
                        unsupportedView, unsupported.makeRef())));
        unsupportedBody.getUnits().add(Jimple.v().newReturnStmt(
                unsupportedArray));

        return new CollectionProjectionFixture(exportMethod,
                unsupportedMethod, unsupported, field);
    }

    private static ArrayPayloadFixture arrayPayloadFixture() {
        G.reset();

        SootClass key = new SootClass("example.ArrayPayloadKey",
                Modifier.PUBLIC);
        Scene.v().addClass(key);
        key.setApplicationClass();
        SootField keyId = new SootField("keyId", IntType.v(),
                Modifier.PRIVATE);
        SootField expiryDate = new SootField("expiryDate", LongType.v(),
                Modifier.PRIVATE);
        key.addField(keyId);
        key.addField(expiryDate);
        SootMethod getKeyId = new SootMethod("getKeyId",
                Collections.emptyList(), IntType.v(), Modifier.PUBLIC);
        SootMethod getExpiryDate = new SootMethod("getExpiryDate",
                Collections.emptyList(), LongType.v(), Modifier.PUBLIC);
        key.addMethod(getKeyId);
        key.addMethod(getExpiryDate);

        ArrayType keyArray = ArrayType.v(key.getType(), 1);
        SootClass payload = new SootClass("example.ArrayPayload",
                Modifier.PUBLIC);
        Scene.v().addClass(payload);
        payload.setApplicationClass();
        SootField payloadArray = new SootField("allKeys", keyArray,
                Modifier.PRIVATE);
        payload.addField(payloadArray);
        SootMethod getAllKeys = new SootMethod("getAllKeys",
                Collections.emptyList(), keyArray, Modifier.PUBLIC);
        payload.addMethod(getAllKeys);

        SootClass store = new SootClass("example.ArrayPayloadStore",
                Modifier.PUBLIC | Modifier.INTERFACE);
        Scene.v().addClass(store);
        store.setApplicationClass();
        SootMethod putById = new SootMethod("put",
                Arrays.asList(IntType.v(), key.getType()), VoidType.v(),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod putByExpiry = new SootMethod("put",
                Arrays.asList(LongType.v(), key.getType()), VoidType.v(),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        store.addMethod(putById);
        store.addMethod(putByExpiry);

        SootClass consumer = new SootClass("example.ArrayPayloadConsumer",
                Modifier.PUBLIC);
        Scene.v().addClass(consumer);
        consumer.setApplicationClass();
        SootField output = new SootField("allKeys", store.getType(),
                Modifier.PRIVATE);
        consumer.addField(output);
        SootMethod consume = new SootMethod("consume",
                Collections.singletonList(payload.getType()), VoidType.v(),
                Modifier.PUBLIC);
        consumer.addMethod(consume);
        Body body = Jimple.v().newBody(consume);
        consume.setActiveBody(body);
        Local receiver = Jimple.v().newLocal("self", consumer.getType());
        Local payloadLocal = Jimple.v().newLocal("payload",
                payload.getType());
        Local storeLocal = Jimple.v().newLocal("store", store.getType());
        Local received = Jimple.v().newLocal("received", keyArray);
        Local keyLocal = Jimple.v().newLocal("key", key.getType());
        Local keyIdLocal = Jimple.v().newLocal("keyId", IntType.v());
        Local expiryLocal = Jimple.v().newLocal("expiry", LongType.v());
        body.getLocals().addAll(Arrays.asList(receiver, payloadLocal,
                storeLocal, received, keyLocal, keyIdLocal, expiryLocal));
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(consumer.getType())));
        body.getUnits().add(Jimple.v().newIdentityStmt(payloadLocal,
                Jimple.v().newParameterRef(payload.getType(), 0)));
        body.getUnits().add(Jimple.v().newAssignStmt(storeLocal,
                Jimple.v().newInstanceFieldRef(receiver,
                        output.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(received,
                Jimple.v().newVirtualInvokeExpr(payloadLocal,
                        getAllKeys.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(keyLocal,
                Jimple.v().newArrayRef(received, IntConstant.v(0))));
        body.getUnits().add(Jimple.v().newAssignStmt(keyIdLocal,
                Jimple.v().newVirtualInvokeExpr(keyLocal,
                        getKeyId.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(expiryLocal,
                Jimple.v().newVirtualInvokeExpr(keyLocal,
                        getExpiryDate.makeRef())));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(storeLocal,
                        putById.makeRef(), keyIdLocal, keyLocal)));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(storeLocal,
                        putByExpiry.makeRef(), expiryLocal, keyLocal)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());

        SootMethod receive = new SootMethod("receive",
                Collections.singletonList(payload.getType()), VoidType.v(),
                Modifier.PUBLIC);
        consumer.addMethod(receive);
        Body receiveBody = Jimple.v().newBody(receive);
        receive.setActiveBody(receiveBody);
        Local receiveThis = Jimple.v().newLocal("self", consumer.getType());
        Local wire = Jimple.v().newLocal("wire", payload.getType());
        receiveBody.getLocals().addAll(Arrays.asList(receiveThis, wire));
        receiveBody.getUnits().add(Jimple.v().newIdentityStmt(receiveThis,
                Jimple.v().newThisRef(consumer.getType())));
        receiveBody.getUnits().add(Jimple.v().newIdentityStmt(wire,
                Jimple.v().newParameterRef(payload.getType(), 0)));
        receiveBody.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newVirtualInvokeExpr(receiveThis,
                        consume.makeRef(), wire)));
        receiveBody.getUnits().add(Jimple.v().newReturnVoidStmt());

        return new ArrayPayloadFixture(consume, receive, payload, payloadArray,
                output);
    }

    private static Path runtimeCallEdges(RuntimeDispatchFixture fixture,
                                         List<String> actualCallees)
            throws Exception {
        Path path = Files.createTempFile("causynth-runtime-dispatch-",
                ".jsonl");
        List<String> rows = new ArrayList<>();
        for (String actual : actualCallees) {
            JsonObject row = new JsonObject();
            row.addProperty("event", "RUNTIME_CALL_EDGE");
            row.addProperty("caller",
                    fixture.callerMethod.getSignature());
            row.addProperty("siteId",
                    fixture.callerMethod.getSignature() + "#u"
                            + fixture.callUnitIndex);
            row.addProperty("declaredCallee",
                    fixture.interfaceMethod.getSignature());
            row.addProperty("actualCallee", actual);
            row.addProperty("evidenceLevel", "CALLSITE_CORRELATED");
            rows.add(row.toString());
        }
        Files.write(path, rows, StandardCharsets.UTF_8);
        path.toFile().deleteOnExit();
        return path;
    }

    private static RuntimeDispatchFixture runtimeDispatchFixture() {
        G.reset();
        SootClass object = new SootClass("java.lang.Object",
                Modifier.PUBLIC);
        Scene.v().addClass(object);

        SootClass product = new SootClass("example.RuntimeProduct",
                Modifier.PUBLIC);
        product.setSuperclass(object);
        Scene.v().addClass(product);
        product.setApplicationClass();
        product.addField(new SootField("keyId", IntType.v(),
                Modifier.PUBLIC));

        SootClass factory = new SootClass("example.RuntimeKeyFactory",
                Modifier.PUBLIC | Modifier.INTERFACE | Modifier.ABSTRACT);
        Scene.v().addClass(factory);
        factory.setApplicationClass();
        SootMethod interfaceMethod = new SootMethod("newKey",
                Collections.emptyList(), RefType.v(product.getName()),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        factory.addMethod(interfaceMethod);

        SootClass actual = new SootClass("example.RuntimeActualFactory",
                Modifier.PUBLIC);
        actual.setSuperclass(object);
        actual.addInterface(factory);
        Scene.v().addClass(actual);
        actual.setApplicationClass();
        SootField actualCached = new SootField("cached",
                RefType.v(product.getName()), Modifier.PUBLIC);
        actual.addField(actualCached);
        SootMethod actualMethod = dispatchImplementation(actual,
                actualCached, product);

        SootClass alternative = new SootClass(
                "example.RuntimeAlternativeFactory", Modifier.PUBLIC);
        alternative.setSuperclass(object);
        alternative.addInterface(factory);
        Scene.v().addClass(alternative);
        alternative.setApplicationClass();
        SootField alternativeCached = new SootField("cached",
                RefType.v(product.getName()), Modifier.PUBLIC);
        alternative.addField(alternativeCached);
        SootMethod alternativeMethod = dispatchImplementation(alternative,
                alternativeCached, product);

        SootClass caller = new SootClass("example.RuntimeDispatchCaller",
                Modifier.PUBLIC);
        caller.setSuperclass(object);
        Scene.v().addClass(caller);
        caller.setApplicationClass();
        SootMethod callerMethod = new SootMethod("call",
                Collections.singletonList(RefType.v(factory.getName())),
                RefType.v(product.getName()),
                Modifier.PUBLIC | Modifier.STATIC);
        caller.addMethod(callerMethod);
        Body body = Jimple.v().newBody(callerMethod);
        callerMethod.setActiveBody(body);
        Local factoryLocal = Jimple.v().newLocal("factory",
                RefType.v(factory.getName()));
        Local productLocal = Jimple.v().newLocal("product",
                RefType.v(product.getName()));
        body.getLocals().add(factoryLocal);
        body.getLocals().add(productLocal);
        body.getUnits().add(Jimple.v().newIdentityStmt(factoryLocal,
                Jimple.v().newParameterRef(factoryLocal.getType(), 0)));
        body.getUnits().add(Jimple.v().newAssignStmt(productLocal,
                Jimple.v().newInterfaceInvokeExpr(factoryLocal,
                        interfaceMethod.makeRef())));
        body.getUnits().add(Jimple.v().newReturnStmt(productLocal));

        return new RuntimeDispatchFixture(interfaceMethod, actualMethod,
                alternativeMethod, callerMethod, actualCached, 1);
    }

    private static SootMethod dispatchImplementation(SootClass owner,
                                                     SootField cached,
                                                     SootClass product) {
        SootMethod method = new SootMethod("newKey",
                Collections.emptyList(), RefType.v(product.getName()),
                Modifier.PUBLIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = Jimple.v().newLocal("r0",
                RefType.v(owner.getName()));
        Local value = Jimple.v().newLocal("value",
                RefType.v(product.getName()));
        body.getLocals().add(receiver);
        body.getLocals().add(value);
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(RefType.v(owner.getName()))));
        body.getUnits().add(Jimple.v().newAssignStmt(value,
                Jimple.v().newInstanceFieldRef(receiver,
                        cached.makeRef())));
        body.getUnits().add(Jimple.v().newReturnStmt(value));
        return method;
    }

    private static IteratorMutationFixture iteratorMutationFixture() {
        G.reset();

        SootClass map = new SootClass("java.util.Map",
                Modifier.PUBLIC | Modifier.INTERFACE);
        SootClass set = new SootClass("java.util.Set",
                Modifier.PUBLIC | Modifier.INTERFACE);
        SootClass iterator = new SootClass("java.util.Iterator",
                Modifier.PUBLIC | Modifier.INTERFACE);
        Scene.v().addClass(map);
        Scene.v().addClass(set);
        Scene.v().addClass(iterator);

        SootMethod entrySet = new SootMethod("entrySet",
                Collections.emptyList(), RefType.v("java.util.Set"),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod iteratorMethod = new SootMethod("iterator",
                Collections.emptyList(), RefType.v("java.util.Iterator"),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod remove = new SootMethod("remove",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod clear = new SootMethod("clear",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod next = new SootMethod("next",
                Collections.emptyList(), RefType.v("java.lang.Object"),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        map.addMethod(entrySet);
        map.addMethod(clear);
        set.addMethod(iteratorMethod);
        iterator.addMethod(remove);
        iterator.addMethod(next);

        SootClass owner = new SootClass("example.IteratorMutationOwner",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootField field = new SootField("entries", RefType.v("java.util.Map"),
                Modifier.PRIVATE);
        owner.addField(field);
        SootMethod method = new SootMethod("prune",
                Arrays.asList(LongType.v(), LongType.v()), VoidType.v(),
                Modifier.PUBLIC);
        owner.addMethod(method);

        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = Jimple.v().newLocal("self", owner.getType());
        Local expiry = Jimple.v().newLocal("expiry", LongType.v());
        Local now = Jimple.v().newLocal("now", LongType.v());
        Local mapLocal = Jimple.v().newLocal("map", RefType.v("java.util.Map"));
        Local setLocal = Jimple.v().newLocal("view", RefType.v("java.util.Set"));
        Local iteratorLocal = Jimple.v().newLocal("iterator",
                RefType.v("java.util.Iterator"));
        Local entryLocal = Jimple.v().newLocal("entry",
                RefType.v("java.lang.Object"));
        body.getLocals().addAll(Arrays.asList(receiver, expiry, now, mapLocal,
                setLocal, iteratorLocal, entryLocal));

        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(owner.getType())));
        body.getUnits().add(Jimple.v().newIdentityStmt(expiry,
                Jimple.v().newParameterRef(LongType.v(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(now,
                Jimple.v().newParameterRef(LongType.v(), 1)));
        body.getUnits().add(Jimple.v().newAssignStmt(mapLocal,
                Jimple.v().newInstanceFieldRef(receiver, field.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(setLocal,
                Jimple.v().newInterfaceInvokeExpr(mapLocal,
                        entrySet.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(iteratorLocal,
                Jimple.v().newInterfaceInvokeExpr(setLocal,
                        iteratorMethod.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(entryLocal,
                Jimple.v().newInterfaceInvokeExpr(iteratorLocal,
                        next.makeRef())));

        Stmt skip = Jimple.v().newReturnVoidStmt();
        IfStmt guard = Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(expiry, now), skip);
        Stmt removeCall = Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(iteratorLocal,
                        remove.makeRef()));
        body.getUnits().add(guard);
        body.getUnits().add(removeCall);
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(mapLocal,
                        clear.makeRef())));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        body.getUnits().add(skip);

        return new IteratorMutationFixture(method, field, 7, 8);
    }

    private static LoopIteratorMutationFixture loopIteratorMutationFixture() {
        G.reset();

        SootClass map = new SootClass("java.util.Map",
                Modifier.PUBLIC | Modifier.INTERFACE);
        SootClass set = new SootClass("java.util.Set",
                Modifier.PUBLIC | Modifier.INTERFACE);
        SootClass iterator = new SootClass("java.util.Iterator",
                Modifier.PUBLIC | Modifier.INTERFACE);
        Scene.v().addClass(map);
        Scene.v().addClass(set);
        Scene.v().addClass(iterator);
        SootMethod entrySet = new SootMethod("entrySet",
                Collections.emptyList(), RefType.v("java.util.Set"),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod iteratorMethod = new SootMethod("iterator",
                Collections.emptyList(), RefType.v("java.util.Iterator"),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod next = new SootMethod("next", Collections.emptyList(),
                RefType.v("java.lang.Object"),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod remove = new SootMethod("remove", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.ABSTRACT);
        map.addMethod(entrySet);
        set.addMethod(iteratorMethod);
        iterator.addMethod(next);
        iterator.addMethod(remove);

        SootClass owner = new SootClass("example.LoopMutationOwner",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootField field = new SootField("entries", RefType.v("java.util.Map"),
                Modifier.PRIVATE);
        owner.addField(field);
        SootMethod method = new SootMethod("prune",
                Arrays.asList(BooleanType.v(), LongType.v(), LongType.v()),
                VoidType.v(), Modifier.PUBLIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);

        Local receiver = Jimple.v().newLocal("self", owner.getType());
        Local hasNext = Jimple.v().newLocal("hasNext", BooleanType.v());
        Local expiry = Jimple.v().newLocal("expiry", LongType.v());
        Local now = Jimple.v().newLocal("now", LongType.v());
        Local mapLocal = Jimple.v().newLocal("map", RefType.v("java.util.Map"));
        Local setLocal = Jimple.v().newLocal("view", RefType.v("java.util.Set"));
        Local iteratorLocal = Jimple.v().newLocal("iterator",
                RefType.v("java.util.Iterator"));
        Local entryLocal = Jimple.v().newLocal("entry",
                RefType.v("java.lang.Object"));
        body.getLocals().addAll(Arrays.asList(receiver, hasNext, expiry, now,
                mapLocal, setLocal, iteratorLocal, entryLocal));
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(owner.getType())));
        body.getUnits().add(Jimple.v().newIdentityStmt(hasNext,
                Jimple.v().newParameterRef(BooleanType.v(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(expiry,
                Jimple.v().newParameterRef(LongType.v(), 1)));
        body.getUnits().add(Jimple.v().newIdentityStmt(now,
                Jimple.v().newParameterRef(LongType.v(), 2)));
        body.getUnits().add(Jimple.v().newAssignStmt(mapLocal,
                Jimple.v().newInstanceFieldRef(receiver, field.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(setLocal,
                Jimple.v().newInterfaceInvokeExpr(mapLocal,
                        entrySet.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(iteratorLocal,
                Jimple.v().newInterfaceInvokeExpr(setLocal,
                        iteratorMethod.makeRef())));

        Stmt done = Jimple.v().newReturnVoidStmt();
        IfStmt loopGuard = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(hasNext, IntConstant.v(0)), done);
        body.getUnits().add(loopGuard);
        body.getUnits().add(Jimple.v().newAssignStmt(entryLocal,
                Jimple.v().newInterfaceInvokeExpr(iteratorLocal,
                        next.makeRef())));
        IfStmt expiryGuard = Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(expiry, now), loopGuard);
        body.getUnits().add(expiryGuard);
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(iteratorLocal,
                        remove.makeRef())));
        GotoStmt backEdge = Jimple.v().newGotoStmt(loopGuard);
        body.getUnits().add(backEdge);
        body.getUnits().add(done);

        return new LoopIteratorMutationFixture(method, field, 7, 9, 10);
    }

    private static InheritedAccessorFixture inheritedAccessorFixture() {
        G.reset();
        SootClass base = new SootClass("example.DelegationKey",
                Modifier.PUBLIC);
        SootClass child = new SootClass("example.BlockKey", Modifier.PUBLIC);
        child.setSuperclass(base);
        Scene.v().addClass(base);
        Scene.v().addClass(child);
        base.setApplicationClass();
        child.setApplicationClass();
        SootField expiryDate = new SootField("expiryDate", LongType.v(),
                Modifier.PRIVATE);
        base.addField(expiryDate);
        SootMethod getter = new SootMethod("getExpiryDate",
                Collections.emptyList(), LongType.v(), Modifier.PUBLIC);
        base.addMethod(getter);
        Body getterBody = Jimple.v().newBody(getter);
        getter.setActiveBody(getterBody);
        Local receiver = Jimple.v().newLocal("r0", base.getType());
        Local value = Jimple.v().newLocal("expiry", LongType.v());
        getterBody.getLocals().addAll(Arrays.asList(receiver, value));
        getterBody.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(base.getType())));
        getterBody.getUnits().add(Jimple.v().newAssignStmt(value,
                Jimple.v().newInstanceFieldRef(receiver,
                        expiryDate.makeRef())));
        getterBody.getUnits().add(Jimple.v().newReturnStmt(value));

        SootClass reader = new SootClass("example.AccessorReader",
                Modifier.PUBLIC);
        Scene.v().addClass(reader);
        reader.setApplicationClass();
        SootMethod method = new SootMethod("read",
                Collections.singletonList(child.getType()), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        reader.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local key = Jimple.v().newLocal("key", child.getType());
        Local expiry = Jimple.v().newLocal("expiry", LongType.v());
        body.getLocals().addAll(Arrays.asList(key, expiry));
        body.getUnits().add(Jimple.v().newIdentityStmt(key,
                Jimple.v().newParameterRef(child.getType(), 0)));
        soot.SootMethodRef inherited = Scene.v().makeMethodRef(child,
                "getExpiryDate", Collections.emptyList(), LongType.v(), false);
        body.getUnits().add(Jimple.v().newAssignStmt(expiry,
                Jimple.v().newVirtualInvokeExpr(key, inherited)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return new InheritedAccessorFixture(method, expiryDate, base, child);
    }

    private static final class IteratorMutationFixture {
        private final SootMethod method;
        private final SootField field;
        private final int guardUnitIndex;
        private final int removeUnitIndex;

        private IteratorMutationFixture(SootMethod method, SootField field,
                                        int guardUnitIndex,
                                        int removeUnitIndex) {
            this.method = method;
            this.field = field;
            this.guardUnitIndex = guardUnitIndex;
            this.removeUnitIndex = removeUnitIndex;
        }
    }

    private static final class RecursiveFieldWriterFixture {
        private final SootMethod reader;
        private final SootMethod setter;
        private final SootMethod monitor;
        private final SootMethod shouldUpdate;
        private final SootField field;

        private RecursiveFieldWriterFixture(SootMethod reader,
                                            SootMethod setter,
                                            SootMethod monitor,
                                            SootMethod shouldUpdate,
                                            SootField field) {
            this.reader = reader;
            this.setter = setter;
            this.monitor = monitor;
            this.shouldUpdate = shouldUpdate;
            this.field = field;
        }
    }

    private static final class CollectionProjectionFixture {
        private final SootMethod exportMethod;
        private final SootMethod unsupportedMethod;
        private final SootMethod unsupportedCallee;
        private final SootField field;

        private CollectionProjectionFixture(SootMethod exportMethod,
                                            SootMethod unsupportedMethod,
                                            SootMethod unsupportedCallee,
                                            SootField field) {
            this.exportMethod = exportMethod;
            this.unsupportedMethod = unsupportedMethod;
            this.unsupportedCallee = unsupportedCallee;
            this.field = field;
        }
    }

    private static final class ArrayPayloadFixture {
        private final SootMethod consumeMethod;
        private final SootMethod receiveMethod;
        private final SootClass payload;
        private final SootField payloadArrayField;
        private final SootField outputField;

        private ArrayPayloadFixture(SootMethod consumeMethod,
                                    SootMethod receiveMethod,
                                    SootClass payload,
                                    SootField payloadArrayField,
                                    SootField outputField) {
            this.consumeMethod = consumeMethod;
            this.receiveMethod = receiveMethod;
            this.payload = payload;
            this.payloadArrayField = payloadArrayField;
            this.outputField = outputField;
        }
    }

    private static final class RuntimeDispatchFixture {
        private final SootMethod interfaceMethod;
        private final SootMethod actualMethod;
        private final SootMethod alternativeMethod;
        private final SootMethod callerMethod;
        private final SootField actualCached;
        private final int callUnitIndex;

        private RuntimeDispatchFixture(SootMethod interfaceMethod,
                                       SootMethod actualMethod,
                                       SootMethod alternativeMethod,
                                       SootMethod callerMethod,
                                       SootField actualCached,
                                       int callUnitIndex) {
            this.interfaceMethod = interfaceMethod;
            this.actualMethod = actualMethod;
            this.alternativeMethod = alternativeMethod;
            this.callerMethod = callerMethod;
            this.actualCached = actualCached;
            this.callUnitIndex = callUnitIndex;
        }
    }

    private static final class LoopIteratorMutationFixture {
        private final SootMethod method;
        private final SootField field;
        private final int loopGuardUnitIndex;
        private final int expiryGuardUnitIndex;
        private final int removeUnitIndex;

        private LoopIteratorMutationFixture(SootMethod method, SootField field,
                                            int loopGuardUnitIndex,
                                            int expiryGuardUnitIndex,
                                            int removeUnitIndex) {
            this.method = method;
            this.field = field;
            this.loopGuardUnitIndex = loopGuardUnitIndex;
            this.expiryGuardUnitIndex = expiryGuardUnitIndex;
            this.removeUnitIndex = removeUnitIndex;
        }
    }

    private static final class InheritedAccessorFixture {
        private final SootMethod method;
        private final SootField field;
        private final SootClass base;
        private final SootClass child;

        private InheritedAccessorFixture(SootMethod method, SootField field,
                                         SootClass base, SootClass child) {
            this.method = method;
            this.field = field;
            this.base = base;
            this.child = child;
        }
    }

    private static void assertRuntimeInvoke(Unit unit, String owner,
                                            String method) {
        InvokeExpr invoke = invokeExpression(unit);
        assertNotNull("expected " + owner + "." + method + " at " + unit,
                invoke);
        assertEquals(owner, invoke.getMethodRef().declaringClass().getName());
        assertEquals(method, invoke.getMethodRef().name());
    }

    private static void assertRuntimeBooleanInvoke(Unit unit, String owner,
                                                   String method,
                                                   int argumentIndex,
                                                   int expectedValue) {
        assertRuntimeInvoke(unit, owner, method);
        InvokeExpr invoke = invokeExpression(unit);
        assertTrue(invoke.getArg(argumentIndex) instanceof IntConstant);
        assertEquals(expectedValue,
                ((IntConstant) invoke.getArg(argumentIndex)).value);
    }

    private static Object concolicMaterializationSelection(
            Path plan, String activationId) throws Exception {
        Class<?> selectionClass = Class.forName(
                CausynthPipeline.class.getName()
                        + "$ConcolicMaterializationSelection");
        Method from = selectionClass.getDeclaredMethod("from", Path.class,
                String.class);
        from.setAccessible(true);
        return from.invoke(null, plan, activationId);
    }

    private static JsonObject exactArrayLeafAction(
            String method, int unitIndex, String bindingMode,
            String location, String rootAuthority, SootField field,
            List<String> fieldPath) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.AUTHORITY.in.0");
        action.addProperty("bindingMode", bindingMode);
        action.addProperty("location", location);
        action.addProperty("index", 0);
        action.addProperty("method", method);
        action.addProperty("local", "root");
        action.addProperty("cell", field.getSignature());
        action.addProperty("field", field.getSignature());
        action.addProperty("accessOwnerClass",
                field.getDeclaringClass().getName());
        action.addProperty("accessField", field.getName());
        action.addProperty("accessFieldSignature", field.getSignature());
        action.addProperty("leafOwnerClass",
                field.getDeclaringClass().getName());
        action.addProperty("leafField", field.getName());
        action.addProperty("leafFieldSignature", field.getSignature());
        action.addProperty("javaType", "java.lang.Object[]");
        action.addProperty("consumedFieldMethod", method);
        action.addProperty("consumedFieldUnitIndex", unitIndex);
        action.addProperty("consumedFieldSiteId", method + "#u"
                + unitIndex);
        action.addProperty("consumedFieldSiteAuthority",
                "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_"
                        + "OWNER_WITHIN_REGION_INSTANCE_V1");
        action.addProperty("consumedFieldBindingComplete", true);
        action.addProperty("consumedFieldOccurrence", 1);
        action.addProperty("consumedFieldOccurrenceAuthority",
                "UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1");
        action.addProperty("consumedFieldRootAuthority", rootAuthority);
        if ("LOCAL_DEFINITION".equals(bindingMode)) {
            JsonObject definition = new JsonObject();
            definition.addProperty("method", method);
            definition.addProperty("local", "root");
            definition.addProperty("unitIndex", 1);
            JsonArray definitions = new JsonArray();
            definitions.add(definition);
            action.add("definitionSites", definitions);
        }
        JsonArray path = new JsonArray();
        for (String segment : fieldPath) path.add(segment);
        JsonArray paths = new JsonArray();
        paths.add(path);
        action.add("fieldPaths", paths);
        return action;
    }

    private static boolean concolicSelectionMatchesField(
            Object selection, String method, int unitIndex, SootField field)
            throws Exception {
        Method matches = selection.getClass().getDeclaredMethod("matches",
                String.class, int.class, soot.SootFieldRef.class);
        matches.setAccessible(true);
        return (Boolean) matches.invoke(selection, method, unitIndex,
                field.makeRef());
    }

    private static Object concolicRegionRefs() throws Exception {
        Class<?> refsClass = Class.forName(
                CausynthPipeline.class.getName() + "$ConcolicRegionRefs");
        Method create = refsClass.getDeclaredMethod("create");
        create.setAccessible(true);
        return create.invoke(null);
    }

    private static int instrumentConcolicMaterializations(
            Object selection, Object refs) throws Exception {
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicMaterializations", selection.getClass(),
                refs.getClass());
        instrument.setAccessible(true);
        return (Integer) instrument.invoke(new CausynthPipeline(null, 0, 0),
                selection, refs);
    }

    private static int instrumentConcolicAccessorCallContexts(
            Object selection, Object refs) throws Exception {
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicAccessorCallContexts",
                selection.getClass(), refs.getClass());
        instrument.setAccessible(true);
        return (Integer) instrument.invoke(
                new CausynthPipeline(null, 0, 0), selection, refs);
    }

    private static InvokeExpr invokeExpression(Unit unit) {
        if (unit instanceof AssignStmt
                && ((AssignStmt) unit).getRightOp() instanceof InvokeExpr) {
            return (InvokeExpr) ((AssignStmt) unit).getRightOp();
        }
        if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()) {
            return ((Stmt) unit).getInvokeExpr();
        }
        return null;
    }

    private static void installCombinedRuntimeStubs() {
        TypeFixture fixture = new TypeFixture();
        SootClass recorder = fixture.runtimeClass(
                "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder");
        fixture.staticMethod(recorder, "enterMethod",
                Arrays.asList(fixture.string, fixture.object), LongType.v());
        fixture.staticMethod(recorder, "recordBranch",
                Arrays.asList(LongType.v(), fixture.string, IntType.v(),
                        fixture.string, BooleanType.v()), VoidType.v());
        fixture.staticMethod(recorder, "exitActiveMethod",
                Arrays.asList(fixture.object, fixture.string), VoidType.v());
        fixture.staticMethod(recorder, "throwActiveMethod",
                Collections.singletonList(fixture.throwable), VoidType.v());

        SootClass concolic = fixture.runtimeClass(
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime");
        fixture.staticMethod(concolic, "enterRegion",
                Arrays.asList(fixture.string, fixture.object,
                        ArrayType.v(fixture.object, 1)), LongType.v());
        fixture.staticMethod(concolic, "pauseObservation",
                Collections.emptyList(), VoidType.v());
        fixture.staticMethod(concolic, "resumeObservation",
                Collections.emptyList(), VoidType.v());
        fixture.staticMethod(concolic, "prepareBranch",
                Arrays.asList(fixture.string, IntType.v(), fixture.string),
                LongType.v());
        fixture.staticMethod(concolic, "resolveBranch",
                Arrays.asList(LongType.v(), LongType.v(), fixture.string,
                        IntType.v(), fixture.string,
                        BooleanType.v()), BooleanType.v());
        fixture.staticMethod(concolic, "exitRegion",
                Arrays.asList(LongType.v(), fixture.object, fixture.string),
                VoidType.v());
        fixture.staticMethod(concolic, "throwRegion",
                Arrays.asList(LongType.v(), fixture.throwable), VoidType.v());
        SootClass system = Scene.v().getSootClassUnsafe("java.lang.System");
        if (system == null) {
            system = fixture.runtimeClass("java.lang.System");
        }
        fixture.staticMethod(system, "markConcolicBranch",
                Arrays.asList(fixture.string, IntType.v()), LongType.v());
    }

    private static final class TypeFixture {
        private final RefType string = RefType.v("java.lang.String");
        private final RefType object = RefType.v("java.lang.Object");
        private final RefType throwable = RefType.v("java.lang.Throwable");

        private SootClass runtimeClass(String name) {
            SootClass value = new SootClass(name, Modifier.PUBLIC);
            Scene.v().addClass(value);
            return value;
        }

        private void staticMethod(SootClass owner, String name,
                                  List<? extends soot.Type> parameters,
                                  soot.Type returnType) {
            owner.addMethod(new SootMethod(name,
                    new ArrayList<soot.Type>(parameters), returnType,
                    Modifier.PUBLIC | Modifier.STATIC | Modifier.NATIVE));
        }
    }

    private static Object newAnalysisResultWithRoot(String rootSignature)
            throws Exception {
        Class<?> resultClass = Class.forName(
                CausynthPipeline.class.getName() + "$AnalysisResult");
        Constructor<?> constructor = resultClass.getDeclaredConstructor();
        constructor.setAccessible(true);
        Object result = constructor.newInstance();

        Field regionsField = resultClass.getDeclaredField("symbolicRegions");
        regionsField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> regions =
                (List<Map<String, Object>>) regionsField.get(result);
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("staticRootCandidate", rootSignature);
        regions.add(region);
        return result;
    }

    private static void addBranchPolicy(Object result, String method,
                                        int unitIndex) throws Exception {
        Field regionsField = result.getClass().getDeclaredField(
                "symbolicRegions");
        regionsField.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> regions =
                (List<Map<String, Object>>) regionsField.get(result);
        Map<String, Object> policy = new LinkedHashMap<>();
        policy.put("method", method);
        policy.put("unitIndex", unitIndex);
        regions.get(0).put("branchPolicies",
                Collections.singletonList(policy));
    }

    private static void addAnalysisRow(Object result, String fieldName,
                                       Map<String, Object> row)
            throws Exception {
        Field field = result.getClass().getDeclaredField(fieldName);
        field.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> rows =
                (List<Map<String, Object>>) field.get(result);
        rows.add(new LinkedHashMap<>(row));
    }

    private static void restoreProperty(String name, String value) {
        if (value == null) {
            System.clearProperty(name);
        } else {
            System.setProperty(name, value);
        }
    }
}
