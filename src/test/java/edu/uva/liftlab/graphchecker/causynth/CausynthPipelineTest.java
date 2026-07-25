package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.Body;
import soot.G;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.Stmt;

import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

public class CausynthPipelineTest {
    private String previousConcolicInstrumentation;
    private String previousTaskPlan;
    private String previousTaskId;

    @Test
    public void derivesOutputSliceCompletenessWithoutWireMirror() {
        Map<String, Object> slice = new LinkedHashMap<>();
        slice.put("truncationReasons", Collections.emptyList());
        slice.put("causalEdgeIds", Collections.singletonList("DF.1"));
        slice.put("inputGaps", Collections.emptyList());
        slice.put("captureBindingsComplete", true);

        assertTrue(SymbolicRegionPlanner.completeOutputSlice(slice));
        slice.put("inputGaps", Collections.singletonList(
                Collections.singletonMap("reason", "MISSING_INPUT")));
        assertFalse(SymbolicRegionPlanner.completeOutputSlice(slice));
    }

    @Before
    public void rememberSystemProperties() {
        previousConcolicInstrumentation =
                System.getProperty("causynth.instrument.concolic");
        previousTaskPlan =
                System.getProperty("causynth.concolic.task.plan");
        previousTaskId =
                System.getProperty("causynth.concolic.task.id");
    }

    @After
    public void resetSoot() {
        restoreProperty("causynth.instrument.concolic",
                previousConcolicInstrumentation);
        restoreProperty("causynth.concolic.task.plan", previousTaskPlan);
        restoreProperty("causynth.concolic.task.id", previousTaskId);
        G.reset();
    }

    private static JsonArray singletonJsonArray(JsonObject value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray singletonJsonArray(String value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static void attachDirectOutputClosure(
            JsonObject activation, String regionId, long rootCallId,
            JsonArray captures, String... descriptors) {
        if (captures.size() != descriptors.length) {
            throw new IllegalArgumentException(
                    "capture and descriptor counts differ");
        }
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", regionId);
        producer.addProperty("regionInstanceId",
                regionId + "@TEST#call" + rootCallId);
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
            slice.add("inputPorts", new JsonArray());
            slice.add("sites", new JsonArray());
            slice.add("staticSites", new JsonArray());
            slice.add("methods", new JsonArray());
            slice.add("causalEdgeIds", new JsonArray());
            slice.addProperty("captureBindingsRequired", true);
            slice.addProperty("captureBindingsComplete", true);
            slice.add("captureBindings",
                    singletonJsonArray(capture.deepCopy()));

            JsonObject member = new JsonObject();
            member.add("output", output);
            member.add("slice", slice);
            members.add(member);
        }
        activation.add("inputActions", new JsonArray());
        activation.addProperty("goalId", outputGoalId(activation));
        activation.addProperty("goalKind", "OUTPUT_RELATION_CLOSURE");
        envelope.add("members", members);
        activation.add("outputClosure", envelope);
    }

    private static String outputGoalId(JsonObject activation) {
        return activation.get("taskId").getAsString()
                + ".GOAL.OUTPUT";
    }

    private static void writePlanRow(Path plan, JsonObject row)
            throws Exception {
        Files.write(plan, (row + "\n").getBytes(StandardCharsets.UTF_8));
    }

    private static void admitExecutable(JsonObject activation, String mode) {
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        admission.addProperty("mode", mode);
        admission.add("blockers", new JsonArray());
        activation.add("admission", admission);
    }

    @Test
    public void outputCaptureSelectionFlattensJointClosureAndFailsClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path plan = folder.getRoot().toPath().resolve(
                    "joint-captures.jsonl");
            String caller = "<example.JointProducer: void run()>";
            String callee = "<example.Sink: void take(int)>";
            String cell = callee + ".param0:int";

            JsonObject activation = new JsonObject();
            activation.addProperty("taskId", "TASK.JOINT.CAPTURE");
            addGlobalRootSelector(activation, caller);
            admitExecutable(activation,
                    "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
            JsonArray captures = new JsonArray();
            for (int index = 0; index < 2; index++) {
                JsonObject capture = new JsonObject();
                capture.addProperty("captureKind", "CALL_ARGUMENT");
                capture.addProperty("captureBindingId",
                        "REGION.JOINT.out." + index + ".capture.0");
                capture.addProperty("outputPort",
                        "REGION.JOINT.out." + index);
                capture.addProperty("outputCell", cell);
                capture.addProperty("callerMethod", caller);
                capture.addProperty("unitIndex", index + 1);
                capture.addProperty("siteId",
                        caller + "#u" + (index + 1));
                capture.addProperty("calleeMethod", callee);
                capture.addProperty("argumentIndex", 0);
                capture.addProperty("argumentCell", "arg0");
                capture.addProperty("occurrence", 1);
                captures.add(capture);
            }
            attachDirectOutputClosure(activation, "REGION.JOINT", 0,
                    captures, "I", "I");
            writePlanRow(plan, activation);

            ConcolicInstrumentationSelections
                    .ConcolicOutputCaptureSelection selection =
                    ConcolicInstrumentationSelections
                            .InstrumentationPlan.from(
                            plan, "TASK.JOINT.CAPTURE")
                            .outputCaptures();
            assertEquals(2, selection.targets().size());

            Files.write(plan, Arrays.asList(activation.toString(),
                    activation.toString()), StandardCharsets.UTF_8);
            boolean duplicateActivationRejected = false;
            try {
                ConcolicInstrumentationSelections.InstrumentationPlan.from(
                        plan, "TASK.JOINT.CAPTURE");
            } catch (java.io.IOException expected) {
                duplicateActivationRejected = true;
            }
            assertTrue(duplicateActivationRejected);

            JsonObject malformed = activation.deepCopy();
            malformed.getAsJsonObject("outputClosure")
                    .getAsJsonArray("members").get(0).getAsJsonObject()
                    .getAsJsonObject("slice")
                    .getAsJsonArray("captureBindings").get(0)
                    .getAsJsonObject().addProperty("occurrence", 0);
            writePlanRow(plan, malformed);
            boolean malformedRejected = false;
            try {
                ConcolicInstrumentationSelections
                        .InstrumentationPlan.from(
                        plan, "TASK.JOINT.CAPTURE").outputCaptures();
            } catch (java.io.IOException expected) {
                malformedRejected = true;
            }
            assertTrue(malformedRejected);

            JsonObject duplicate = activation.deepCopy();
            JsonArray duplicateMembers = duplicate.getAsJsonObject(
                    "outputClosure").getAsJsonArray("members");
            duplicateMembers.get(1).getAsJsonObject()
                    .getAsJsonObject("slice")
                    .getAsJsonArray("captureBindings").get(0)
                    .getAsJsonObject().addProperty("captureBindingId",
                    "REGION.JOINT.out.0.capture.0");
            writePlanRow(plan, duplicate);
            boolean duplicateRejected = false;
            try {
                ConcolicInstrumentationSelections
                        .InstrumentationPlan.from(
                        plan, "TASK.JOINT.CAPTURE").outputCaptures();
            } catch (java.io.IOException expected) {
                duplicateRejected = true;
            }
            assertTrue(duplicateRejected);

            JsonObject singularOnly = activation.deepCopy();
            singularOnly.remove("outputClosure");
            singularOnly.add("requestedOutputCapture", captures.deepCopy());
            singularOnly.addProperty(
                    "requestedOutputCaptureRequired", true);
            singularOnly.addProperty(
                    "requestedOutputCaptureComplete", true);
            writePlanRow(plan, singularOnly);
            boolean singularRejected = false;
            try {
                ConcolicInstrumentationSelections.InstrumentationPlan.from(
                        plan, "TASK.JOINT.CAPTURE");
            } catch (java.io.IOException expected) {
                singularRejected = true;
            }
            assertTrue(singularRejected);
        } finally {
            folder.delete();
        }
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
            activation.addProperty("taskId", "TASK.CAPTURE");
            addGlobalRootSelector(activation, root.getSignature());
            admitExecutable(activation,
                    "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
            JsonObject capture = new JsonObject();
            capture.addProperty("captureKind", "CALL_ARGUMENT");
            capture.addProperty("captureBindingId", "REGION.0.out.0.capture.0");
            capture.addProperty("outputPort", "REGION.0.out.0");
            capture.addProperty("outputCell", cell);
            capture.addProperty("callerMethod", root.getSignature());
            capture.addProperty("unitIndex", 1);
            capture.addProperty("siteId", root.getSignature() + "#u1");
            capture.addProperty("calleeMethod", accept.getSignature());
            capture.addProperty("argumentIndex", 0);
            capture.addProperty("argumentCell", cell);
            capture.addProperty("occurrence", 1);
            JsonArray captures = new JsonArray();
            captures.add(capture);
            attachDirectOutputClosure(activation, "REGION.0", 0,
                    captures, "Ljava/lang/String;");
            Files.write(plan, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));
            System.setProperty("causynth.concolic.task.plan",
                    plan.toString());
            System.setProperty("causynth.concolic.task.id",
                    "TASK.CAPTURE");

            ConcolicInstrumentationSelections
                    .ConcolicOutputCaptureSelection selection =
                    ConcolicInstrumentationSelections
                            .InstrumentationPlan.from(
                            plan, "TASK.CAPTURE").outputCaptures();
            assertEquals(1, selection.targets().size());
            Class<?> refsClass = Class.forName(
                    CausynthPipeline.class.getName() + "$ConcolicRegionRefs");
            Method create = refsClass.getDeclaredMethod("create");
            create.setAccessible(true);
            Object refs = create.invoke(null);
            Method instrument = CausynthPipeline.class.getDeclaredMethod(
                    "instrumentConcolicOutputCaptures",
                    ConcolicInstrumentationSelections
                            .ConcolicOutputCaptureSelection.class,
                    refsClass);
            instrument.setAccessible(true);
            instrument.invoke(new CausynthPipeline(null), selection, refs);

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
            activation.addProperty("taskId", "TASK.FIELD.CAPTURE");
            addGlobalRootSelector(activation, root.getSignature());
            admitExecutable(activation,
                    "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
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
            attachDirectOutputClosure(activation, "REGION.FIELD", 0,
                    captures, "Ljava/lang/String;");
            Files.write(plan, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicInstrumentationSelections
                    .ConcolicOutputCaptureSelection selection =
                    ConcolicInstrumentationSelections
                            .InstrumentationPlan.from(
                            plan, "TASK.FIELD.CAPTURE")
                            .outputCaptures();
            Class<?> refsClass = Class.forName(
                    CausynthPipeline.class.getName()
                            + "$ConcolicRegionRefs");
            Method create = refsClass.getDeclaredMethod("create");
            create.setAccessible(true);
            Object refs = create.invoke(null);
            Method instrument = CausynthPipeline.class.getDeclaredMethod(
                    "instrumentConcolicOutputCaptures",
                    ConcolicInstrumentationSelections
                            .ConcolicOutputCaptureSelection.class,
                    refsClass);
            instrument.setAccessible(true);
            instrument.invoke(new CausynthPipeline(null), selection, refs);

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

    private static void restoreProperty(String name, String value) {
        if (value == null) {
            System.clearProperty(name);
        } else {
            System.setProperty(name, value);
        }
    }

    private static void addGlobalRootSelector(JsonObject activation,
                                              String method) {
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("method", method);
        selector.addProperty("ordinal", 1);
        activation.add("rootSelector", selector);
    }
}
