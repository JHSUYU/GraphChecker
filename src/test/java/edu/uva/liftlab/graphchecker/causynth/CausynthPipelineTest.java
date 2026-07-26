package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.Body;
import soot.G;
import soot.Local;
import soot.LongType;
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
import java.util.Collection;
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
        slice.put("captureBindingIssues", Collections.emptyList());

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
        envelope.addProperty("schemaVersion", 2);
        envelope.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", regionId);
        producer.addProperty("regionInstanceId",
                regionId + "@TEST#call" + rootCallId);
        producer.addProperty("rootCallId", rootCallId);
        envelope.add("producer", producer);
        envelope.add("causalEdges", new JsonArray());
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
            slice.add("captureBindings",
                    singletonJsonArray(capture.deepCopy()));
            slice.add("captureBindingIssues", new JsonArray());

            JsonObject member = new JsonObject();
            member.add("output", output);
            member.add("slice", slice);
            members.add(member);
        }
        activation.add("inputActions", new JsonArray());
        activation.addProperty("goalId", outputGoalId(activation));
        activation.addProperty("goalKind", "OUTPUT_RELATION_CLOSURE");
        activation.addProperty("regionId", regionId);
        activation.addProperty("regionInstanceId",
                regionId + "@TEST#call" + rootCallId);
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

            JsonObject activation = new JsonObject();
            activation.addProperty("taskId", "TASK.JOINT.CAPTURE");
            addGlobalRootSelector(activation, caller);
            admitExecutable(activation,
                    "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
            JsonArray captures = new JsonArray();
            for (int index = 0; index < 2; index++) {
                JsonObject capture = new JsonObject();
                capture.addProperty("captureBindingId",
                        "REGION.JOINT.out." + index + ".capture.0");
                capture.addProperty("outputPort",
                        "REGION.JOINT.out." + index);
                String field = "<example.JointProducer: int value"
                        + index + ">";
                capture.addProperty("outputCell", field);
                capture.addProperty("accessRootInputPort",
                        "REGION.JOINT.in." + index);
                capture.add("fieldPath",
                        singletonJsonArray("value" + index));
                capture.addProperty("fieldSignature", field);
                capture.addProperty("javaType", "int");
                captures.add(capture);
            }
            attachDirectOutputClosure(activation, "REGION.JOINT", 0,
                    captures, "I", "I");
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", caller + "#u7");
            activation.add("branches", singletonJsonArray(branch));
            writePlanRow(plan, activation);

            ConcolicInstrumentationSelections.InstrumentationPlan
                    instrumentation =
                    ConcolicInstrumentationSelections
                            .InstrumentationPlan.from(
                            plan, "TASK.JOINT.CAPTURE");
            List<OutputCaptureSpec> selection =
                    instrumentation.outputCaptures();
            assertEquals(2, selection.size());
            assertEquals(Collections.singleton(7),
                    instrumentation.branches().units(caller));

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
                    .getAsJsonObject().addProperty(
                    "captureKind", "CALL_ARGUMENT");
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
    public void capturesExactFieldStateAtNormalRegionExit()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            G.reset();
            Scene.v().addClass(new SootClass("java.lang.String",
                    Modifier.PUBLIC));
            SootClass owner = new SootClass("example.FieldCaptureRegion",
                    Modifier.PUBLIC);
            Scene.v().addClass(owner);
            owner.setApplicationClass();
            SootField field = new SootField("value",
                    RefType.v("java.lang.String"), Modifier.PUBLIC);
            owner.addField(field);
            SootMethod root = new SootMethod("run",
                    Collections.singletonList(RefType.v("java.lang.String")),
                    VoidType.v(), Modifier.PUBLIC);
            owner.addMethod(root);
            Body body = Jimple.v().newBody(root);
            root.setActiveBody(body);
            Local receiver = Jimple.v().newLocal("receiver",
                    RefType.v(owner.getName()));
            Local rhs = Jimple.v().newLocal("rhs",
                    RefType.v("java.lang.String"));
            body.getLocals().add(receiver);
            body.getLocals().add(rhs);
            body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                    Jimple.v().newThisRef(
                            (RefType) receiver.getType())));
            body.getUnits().add(Jimple.v().newIdentityStmt(rhs,
                    Jimple.v().newParameterRef(rhs.getType(), 0)));
            AssignStmt write = Jimple.v().newAssignStmt(
                    Jimple.v().newInstanceFieldRef(receiver, field.makeRef()),
                    rhs);
            body.getUnits().add(write);
            Unit exit = Jimple.v().newReturnVoidStmt();
            body.getUnits().add(exit);

            Path plan = folder.getRoot().toPath().resolve(
                    "field-activation.jsonl");
            JsonObject activation = new JsonObject();
            activation.addProperty("taskId", "TASK.FIELD.CAPTURE");
            addGlobalRootSelector(activation, root.getSignature());
            admitExecutable(activation,
                    "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
            JsonObject capture = new JsonObject();
            capture.addProperty("captureBindingId",
                    "REGION.FIELD.out.0.exit-field");
            capture.addProperty("outputPort", "REGION.FIELD.out.0");
            capture.addProperty("outputCell", field.getSignature());
            capture.addProperty("accessRootInputPort",
                    "REGION.FIELD.in.0");
            capture.add("fieldPath", singletonJsonArray("value"));
            capture.addProperty("fieldSignature", field.getSignature());
            capture.addProperty("javaType", "java.lang.String");
            JsonArray captures = new JsonArray();
            captures.add(capture);
            attachDirectOutputClosure(activation, "REGION.FIELD", 0,
                    captures, "Ljava/lang/String;");
            JsonObject accessRoot = new JsonObject();
            accessRoot.addProperty("symbol", "REGION.FIELD.in.0");
            accessRoot.addProperty("location", "RECEIVER_FIELD");
            accessRoot.addProperty("mode", "SYMBOLIC");
            activation.add("inputActions",
                    singletonJsonArray(accessRoot));
            Files.write(plan, (activation + "\n").getBytes(
                    StandardCharsets.UTF_8));

            List<OutputCaptureSpec> selection =
                    ConcolicInstrumentationSelections
                            .InstrumentationPlan.from(
                            plan, "TASK.FIELD.CAPTURE")
                            .outputCaptures();
            Class<?> refsClass = Class.forName(
                    CausynthPipeline.class.getName()
                            + "$HookCatalog");
            Method create = refsClass.getDeclaredMethod("concolic");
            create.setAccessible(true);
            Object refs = create.invoke(null);
            Method instrument = CausynthPipeline.class.getDeclaredMethod(
                    "instrumentRegionExitFieldCaptures",
                    Body.class, Unit.class, Local.class, soot.Value.class,
                    String.class,
                    Collection.class,
                    refsClass);
            instrument.setAccessible(true);
            Local token = Jimple.v().newLocal("$token", LongType.v());
            body.getLocals().add(token);
            instrument.invoke(new CausynthPipeline(null), body, exit,
                    token, receiver, owner.getName(), selection, refs);

            List<Unit> units = new ArrayList<>();
            for (Unit unit : body.getUnits()) units.add(unit);
            int writeIndex = units.indexOf(write);
            int hookIndex = -1;
            InvokeExpr hook = null;
            for (int index = 0; index < units.size(); index++) {
                Unit unit = units.get(index);
                if (!(unit instanceof Stmt)
                        || !((Stmt) unit).containsInvokeExpr()) continue;
                InvokeExpr invoke = ((Stmt) unit).getInvokeExpr();
                if ("recordRegionExitFieldOutput".equals(
                        invoke.getMethodRef().name())) {
                    hookIndex = index;
                    hook = invoke;
                }
            }
            assertTrue(write.getRightOp() instanceof Local);
            assertTrue(writeIndex > 0);
            assertTrue(hookIndex > writeIndex);
            assertTrue(hookIndex < units.indexOf(exit));
            assertNotNull(hook);
            assertEquals("REGION.FIELD.out.0.exit-field",
                    hook.getArg(0).toString()
                    .replace("\"", ""));
            assertEquals(field.getSignature(), hook.getArg(3).toString()
                    .replace("\"", ""));
            assertSame(receiver, hook.getArg(4));
            assertTrue(hook.getArg(5) instanceof Local);
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
