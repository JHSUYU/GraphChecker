package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.ByteType;
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
import soot.baf.BafASMBackend;
import soot.jimple.AssignStmt;
import soot.jimple.ArrayRef;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.LongConstant;
import soot.jimple.NewArrayExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.options.Options;

import java.io.ByteArrayOutputStream;
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
    private String previousStaticMaxMethods;
    private String previousStaticMaxEdges;

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
        previousStaticMaxMethods =
                System.getProperty("causynth.static.max.methods");
        previousStaticMaxEdges =
                System.getProperty("causynth.static.max.edges");
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
        restoreProperty("causynth.static.max.methods",
                previousStaticMaxMethods);
        restoreProperty("causynth.static.max.edges",
                previousStaticMaxEdges);
        G.reset();
    }

    private static JsonObject executableActivationRow(
            String activationId, JsonObject declaration) {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", activationId);
        admitExecutable(activation,
                "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
        activation.add("symbolize",
                singletonJsonArray(declaration.deepCopy()));
        return activation;
    }

    private static JsonObject readyBoundedOutputClosure(String activationId) {
        String outputPort = "REGION.15.out.122";
        String outputCell = "<example.Manager: java.util.Map allKeys>";
        String inputPort = "REGION.15.in.32";
        JsonObject row = new JsonObject();
        row.addProperty("activationId", activationId);
        addGlobalRootSelector(row, "<example.Manager: void add()>");
        row.addProperty("scheduleId", "SCHEDULE.0");
        JsonObject bundle = new JsonObject();
        bundle.addProperty("rootActivationId", activationId);
        bundle.addProperty("scheduleId", "SCHEDULE.0");
        bundle.addProperty("size", 1);
        bundle.addProperty("index", 0);
        bundle.addProperty("role", "PRIMARY");
        bundle.addProperty("selection", activationId);
        row.add("bundle", bundle);
        row.addProperty("regionId", "REGION.15");
        row.addProperty("regionInstanceId", "REGION.15@TEST#call0");
        row.addProperty("rootCallId", 0);
        row.addProperty("requestedOutputCaptureComplete", true);
        admitExecutable(row, "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
        row.addProperty("executionPhase", "CAPTURE_OUTPUT_PATH");
        row.add("materializations", new JsonArray());

        JsonObject goal = new JsonObject();
        goal.addProperty("kind", "OUTPUT_CLOSURE");
        goal.addProperty("scope", "BOUNDED_OUTPUT_RELEVANT_PATHS");
        row.add("captureGoal", goal);

        JsonObject output = new JsonObject();
        output.addProperty("portId", outputPort);
        output.addProperty("cell", outputCell);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("selectionAuthority",
                "TEST_EXACT_REQUESTED_OUTPUT");
        row.add("requestedOutput", output);
        JsonObject outputDeclaration = new JsonObject();
        outputDeclaration.addProperty("symbol", outputPort);
        outputDeclaration.addProperty("cell", outputCell);
        outputDeclaration.addProperty("kind", "HEAP_STATE");
        outputDeclaration.addProperty("location",
                "RETURN_OR_HEAP_EFFECT");
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
        slice.addProperty("captureBindingsComplete", true);
        slice.add("inputPorts", singletonJsonArray(inputPort));
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
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
        OutputClosureCodec.writeTo(row, OutputClosureCodec.singleton(
                "REGION.15", "REGION.15@TEST#call0", 0,
                outputPort, outputCell, "HEAP_STATE",
                "TEST_EXACT_REQUESTED_OUTPUT", slice));
        return row;
    }

    private static JsonObject readySolverOutputPathFlip() {
        String activation = "ACT.PATH.3a35b5ac15765178";
        JsonObject row = readyBoundedOutputClosure(activation);
        row.addProperty("scheduleId",
                "SCHEDULE.PATH.3a35b5ac15765178");
        row.getAsJsonObject("bundle").addProperty("scheduleId",
                "SCHEDULE.PATH.3a35b5ac15765178");
        row.addProperty("executionPhase", "REPLAY_OUTPUT_PATH_FLIP");
        row.addProperty("pathQueryKey",
                "c3577f7f5002a09920e54b51105590f1093a902d0fcf8bdee74ce4516109f7b3");

        JsonArray assignments = new JsonArray();
        assignments.add(solverPathFlipAssignment("M_Z_field_input",
                "sym__input", "REGION.15.in.32"));
        row.add("modelAssignments", assignments);

        BranchWitness prefix = branchWitness(1, true,
                branchPredicate("REGION.15.in.32", ">"), 0);
        BranchWitness source = branchWitness(2, true,
                branchPredicate("REGION.15.in.32", ">"), 1);
        row.add("replayContract", BranchReplayContract.flip(
                Collections.singletonList(prefix), source).toJson());
        return row;
    }

    private static BranchWitness branchWitness(int occurrence,
                                               boolean outcome,
                                               JsonElement predicate,
                                               int pcIndex) {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", pcIndex + 1L);
        event.addProperty("contextId", 1L);
        return BranchWitness.vmPc(
                "<example.Manager: void add()>#u14",
                "<example.Manager: void add()>", 14, occurrence,
                outcome, predicate, pcIndex, event);
    }

    private static JsonObject branchPredicate(String input,
                                              String operator) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "Z");
        left.addProperty("_exp", input);
        JsonObject zero = new JsonObject();
        zero.addProperty("_type", "ConstExpr");
        zero.addProperty("_java_type", "I");
        zero.addProperty("_exp", "Y_I_0");
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", zero);
        return expression;
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
        activation.add("materializations", new JsonArray());
        envelope.add("members", members);
        activation.add("outputClosure", envelope);
    }

    private static void writePlanRow(Path plan, JsonObject row)
            throws Exception {
        Files.write(plan, (row + "\n").getBytes(StandardCharsets.UTF_8));
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
            activation.addProperty("activationId", "ACT.JOINT.CAPTURE");
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
                            plan, "ACT.JOINT.CAPTURE").outputCaptures();
            assertEquals(2, selection.targets().size());

            Files.write(plan, Arrays.asList(activation.toString(),
                    activation.toString()), StandardCharsets.UTF_8);
            boolean duplicateActivationRejected = false;
            try {
                ConcolicInstrumentationSelections.InstrumentationPlan.from(
                        plan, "ACT.JOINT.CAPTURE");
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
                        plan, "ACT.JOINT.CAPTURE").outputCaptures();
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
                        plan, "ACT.JOINT.CAPTURE").outputCaptures();
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
                        plan, "ACT.JOINT.CAPTURE");
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
            activation.addProperty("activationId", "ACT.CAPTURE");
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
            System.setProperty("causynth.concolic.activation.plan",
                    plan.toString());
            System.setProperty("causynth.concolic.activation.id",
                    "ACT.CAPTURE");

            ConcolicInstrumentationSelections
                    .ConcolicOutputCaptureSelection selection =
                    ConcolicInstrumentationSelections
                            .InstrumentationPlan.from(
                            plan, "ACT.CAPTURE").outputCaptures();
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
            activation.addProperty("activationId", "ACT.FIELD.CAPTURE");
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
                            plan, "ACT.FIELD.CAPTURE").outputCaptures();
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

    private static String deepMessage(Throwable failure) {
        StringBuilder result = new StringBuilder();
        Throwable current = failure;
        while (current != null) {
            if (current.getMessage() != null) {
                result.append(current.getMessage()).append('\n');
            }
            current = current.getCause();
        }
        return result.toString();
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
        base.put("schemaVersion", 2);
        base.put("kind", "fixture_field_transfer");
        base.put("relation", "value_flow");
        base.put("semanticMode", mappingOnly ? "MAPPING_ONLY"
                : semanticAllowed && derivationAllowed && smtAllowed
                ? "ASSERTABLE" : "RUNTIME_VALIDATION_REQUIRED");
        base.put("mappingAuthority", mappingOnly
                ? "STATIC_FORMAT_AND_PORT_MAPPING" : "");
        return base;
    }

    private static void admitExecutable(JsonObject activation,
                                        String mode) {
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        admission.addProperty("mode", mode);
        admission.add("blockers", new JsonArray());
        activation.add("admission", admission);
    }

    private static Object newStaticAnalyzer() throws Exception {
        return newStaticAnalyzer("");
    }

    private static Object newStaticAnalyzer(String analysisScope)
            throws Exception {
        Path current = Paths.get(".").toAbsolutePath().normalize();
        CausynthTargetContext target = new CausynthTargetContext(
                current, current, null, null, analysisScope);
        Class<?> analyzerClass = SeedBackwardStaticAnalyzer.class;
        Constructor<?> constructor = analyzerClass.getDeclaredConstructor(
                CausynthTargetContext.class);
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
        SootMethod getKeyId = addPureFieldMethod(key, keyId, "getKeyId");
        SootMethod getExpiryDate = addPureFieldMethod(key, expiryDate,
                "getExpiryDate");

        ArrayType keyArray = ArrayType.v(key.getType(), 1);
        SootClass payload = new SootClass("example.ArrayPayload",
                Modifier.PUBLIC);
        Scene.v().addClass(payload);
        payload.setApplicationClass();
        SootField payloadArray = new SootField("allKeys", keyArray,
                Modifier.PRIVATE);
        payload.addField(payloadArray);
        SootMethod getAllKeys = addPureFieldMethod(payload, payloadArray,
                "getAllKeys");

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

    private static StructuralAccessorShapeFixture
    structuralAccessorShapeFixture() {
        G.reset();
        SootClass owner = new SootClass("example.StructuralRecord",
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootField mark = new SootField("mark", LongType.v(),
                Modifier.PRIVATE);
        owner.addField(mark);

        SootMethod pure = addPureFieldMethod(owner, mark,
                "extractMark");
        SootMethod constant = addConstantLongMethod(owner,
                "getConstant", 7L);

        SootMethod computed = new SootMethod("getComputed",
                Collections.emptyList(), LongType.v(), Modifier.PUBLIC);
        owner.addMethod(computed);
        Body computedBody = Jimple.v().newBody(computed);
        computed.setActiveBody(computedBody);
        Local computedReceiver = Jimple.v().newLocal("r0", owner.getType());
        Local fieldValue = Jimple.v().newLocal("fieldValue", LongType.v());
        Local computedValue = Jimple.v().newLocal("computed", LongType.v());
        computedBody.getLocals().addAll(Arrays.asList(computedReceiver,
                fieldValue, computedValue));
        computedBody.getUnits().add(Jimple.v().newIdentityStmt(
                computedReceiver, Jimple.v().newThisRef(owner.getType())));
        computedBody.getUnits().add(Jimple.v().newAssignStmt(fieldValue,
                Jimple.v().newInstanceFieldRef(computedReceiver,
                        mark.makeRef())));
        computedBody.getUnits().add(Jimple.v().newAssignStmt(computedValue,
                Jimple.v().newAddExpr(fieldValue, LongConstant.v(1L))));
        computedBody.getUnits().add(Jimple.v().newReturnStmt(computedValue));

        SootMethod helper = addConstantLongMethod(owner, "helperValue", 9L);
        SootMethod called = new SootMethod("getCalled",
                Collections.emptyList(), LongType.v(), Modifier.PUBLIC);
        owner.addMethod(called);
        Body calledBody = Jimple.v().newBody(called);
        called.setActiveBody(calledBody);
        Local calledReceiver = Jimple.v().newLocal("r0", owner.getType());
        Local calledValue = Jimple.v().newLocal("called", LongType.v());
        calledBody.getLocals().addAll(Arrays.asList(calledReceiver,
                calledValue));
        calledBody.getUnits().add(Jimple.v().newIdentityStmt(calledReceiver,
                Jimple.v().newThisRef(owner.getType())));
        calledBody.getUnits().add(Jimple.v().newAssignStmt(calledValue,
                Jimple.v().newVirtualInvokeExpr(calledReceiver,
                        helper.makeRef())));
        calledBody.getUnits().add(Jimple.v().newReturnStmt(calledValue));

        SootMethod branched = new SootMethod("getBranched",
                Collections.emptyList(), LongType.v(), Modifier.PUBLIC);
        owner.addMethod(branched);
        Body branchedBody = Jimple.v().newBody(branched);
        branched.setActiveBody(branchedBody);
        Local branchedReceiver = Jimple.v().newLocal("r0", owner.getType());
        Local branchedValue = Jimple.v().newLocal("value", LongType.v());
        branchedBody.getLocals().addAll(Arrays.asList(branchedReceiver,
                branchedValue));
        branchedBody.getUnits().add(Jimple.v().newIdentityStmt(
                branchedReceiver, Jimple.v().newThisRef(owner.getType())));
        branchedBody.getUnits().add(Jimple.v().newAssignStmt(branchedValue,
                Jimple.v().newInstanceFieldRef(branchedReceiver,
                        mark.makeRef())));
        Stmt zeroReturn = Jimple.v().newReturnStmt(LongConstant.v(0L));
        branchedBody.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(branchedValue, LongConstant.v(0L)),
                zeroReturn));
        branchedBody.getUnits().add(Jimple.v().newReturnStmt(branchedValue));
        branchedBody.getUnits().add(zeroReturn);

        SootMethod writing = new SootMethod("getWriting",
                Collections.emptyList(), LongType.v(), Modifier.PUBLIC);
        owner.addMethod(writing);
        Body writingBody = Jimple.v().newBody(writing);
        writing.setActiveBody(writingBody);
        Local writingReceiver = Jimple.v().newLocal("r0", owner.getType());
        Local writtenValue = Jimple.v().newLocal("value", LongType.v());
        writingBody.getLocals().addAll(Arrays.asList(writingReceiver,
                writtenValue));
        writingBody.getUnits().add(Jimple.v().newIdentityStmt(writingReceiver,
                Jimple.v().newThisRef(owner.getType())));
        writingBody.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(writingReceiver,
                        mark.makeRef()), LongConstant.v(11L)));
        writingBody.getUnits().add(Jimple.v().newAssignStmt(writtenValue,
                Jimple.v().newInstanceFieldRef(writingReceiver,
                        mark.makeRef())));
        writingBody.getUnits().add(Jimple.v().newReturnStmt(writtenValue));

        SootMethod parameterizedGet = new SootMethod("get",
                Collections.singletonList(LongType.v()), LongType.v(),
                Modifier.PUBLIC);
        owner.addMethod(parameterizedGet);
        Body parameterizedBody = Jimple.v().newBody(parameterizedGet);
        parameterizedGet.setActiveBody(parameterizedBody);
        Local parameterizedReceiver = Jimple.v().newLocal("r0",
                owner.getType());
        Local parameter = Jimple.v().newLocal("parameter", LongType.v());
        parameterizedBody.getLocals().addAll(Arrays.asList(
                parameterizedReceiver, parameter));
        parameterizedBody.getUnits().add(Jimple.v().newIdentityStmt(
                parameterizedReceiver,
                Jimple.v().newThisRef(owner.getType())));
        parameterizedBody.getUnits().add(Jimple.v().newIdentityStmt(parameter,
                Jimple.v().newParameterRef(LongType.v(), 0)));
        parameterizedBody.getUnits().add(Jimple.v().newReturnStmt(parameter));

        SootClass caller = new SootClass("example.StructuralCaller",
                Modifier.PUBLIC);
        Scene.v().addClass(caller);
        caller.setApplicationClass();
        SootMethod parameterizedCaller = new SootMethod("callGet",
                Arrays.asList(owner.getType(), LongType.v()), LongType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        caller.addMethod(parameterizedCaller);
        Body callerBody = Jimple.v().newBody(parameterizedCaller);
        parameterizedCaller.setActiveBody(callerBody);
        Local callerReceiver = Jimple.v().newLocal("record", owner.getType());
        Local callerArgument = Jimple.v().newLocal("argument", LongType.v());
        Local callerResult = Jimple.v().newLocal("result", LongType.v());
        callerBody.getLocals().addAll(Arrays.asList(callerReceiver,
                callerArgument, callerResult));
        callerBody.getUnits().add(Jimple.v().newIdentityStmt(callerReceiver,
                Jimple.v().newParameterRef(owner.getType(), 0)));
        callerBody.getUnits().add(Jimple.v().newIdentityStmt(callerArgument,
                Jimple.v().newParameterRef(LongType.v(), 1)));
        callerBody.getUnits().add(Jimple.v().newAssignStmt(callerResult,
                Jimple.v().newVirtualInvokeExpr(callerReceiver,
                        parameterizedGet.makeRef(), callerArgument)));
        callerBody.getUnits().add(Jimple.v().newReturnStmt(callerResult));

        SootClass base = new SootClass("example.AmbiguousRecord",
                Modifier.PUBLIC);
        SootClass child = new SootClass("example.OverridingRecord",
                Modifier.PUBLIC);
        child.setSuperclass(base);
        Scene.v().addClass(base);
        Scene.v().addClass(child);
        base.setApplicationClass();
        child.setApplicationClass();
        SootField baseValue = new SootField("baseValue", LongType.v(),
                Modifier.PRIVATE);
        SootField childValue = new SootField("childValue", LongType.v(),
                Modifier.PRIVATE);
        base.addField(baseValue);
        child.addField(childValue);
        SootMethod ambiguousBase = addPureFieldMethod(base, baseValue,
                "readValue");
        addPureFieldMethod(child, childValue, "readValue");

        return new StructuralAccessorShapeFixture(pure,
                Arrays.asList(constant, computed, called, branched, writing,
                        parameterizedGet, ambiguousBase),
                parameterizedGet, parameterizedCaller);
    }

    private static SootMethod addPureFieldMethod(SootClass owner,
                                                  SootField field,
                                                  String name) {
        SootMethod method = new SootMethod(name, Collections.emptyList(),
                field.getType(), Modifier.PUBLIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = Jimple.v().newLocal("r0", owner.getType());
        Local value = Jimple.v().newLocal("value", field.getType());
        body.getLocals().addAll(Arrays.asList(receiver, value));
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(owner.getType())));
        body.getUnits().add(Jimple.v().newAssignStmt(value,
                Jimple.v().newInstanceFieldRef(receiver, field.makeRef())));
        body.getUnits().add(Jimple.v().newReturnStmt(value));
        return method;
    }

    private static SootMethod addConstantLongMethod(SootClass owner,
                                                     String name,
                                                     long value) {
        SootMethod method = new SootMethod(name, Collections.emptyList(),
                LongType.v(), Modifier.PUBLIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = Jimple.v().newLocal("r0", owner.getType());
        body.getLocals().add(receiver);
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(owner.getType())));
        body.getUnits().add(Jimple.v().newReturnStmt(LongConstant.v(value)));
        return method;
    }

    private static InheritedAccessorFixture inheritedAccessorFixture() {
        G.reset();
        SootClass base = new SootClass("example.RecordState",
                Modifier.PUBLIC);
        SootClass child = new SootClass("example.SpecializedRecord",
                Modifier.PUBLIC);
        child.setSuperclass(base);
        Scene.v().addClass(base);
        Scene.v().addClass(child);
        base.setApplicationClass();
        child.setApplicationClass();
        SootField stamp = new SootField("stamp", LongType.v(),
                Modifier.PRIVATE);
        base.addField(stamp);
        SootMethod getter = addPureFieldMethod(base, stamp, "readStamp");

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
                "readStamp", Collections.emptyList(), LongType.v(), false);
        body.getUnits().add(Jimple.v().newAssignStmt(expiry,
                Jimple.v().newVirtualInvokeExpr(key, inherited)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return new InheritedAccessorFixture(method, stamp, base, child);
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

    private static final class StructuralAccessorShapeFixture {
        private final SootMethod pure;
        private final List<SootMethod> rejected;
        private final SootMethod parameterizedGet;
        private final SootMethod parameterizedCaller;

        private StructuralAccessorShapeFixture(SootMethod pure,
                                               List<SootMethod> rejected,
                                               SootMethod parameterizedGet,
                                               SootMethod parameterizedCaller) {
            this.pure = pure;
            this.rejected = rejected;
            this.parameterizedGet = parameterizedGet;
            this.parameterizedCaller = parameterizedCaller;
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
        return ConcolicInstrumentationSelections
                .InstrumentationPlan.from(plan, activationId)
                .materializations();
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
        return ((ConcolicInstrumentationSelections
                .ConcolicMaterializationSelection) selection).matches(
                method, unitIndex, field.makeRef());
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
        return (Integer) instrument.invoke(new CausynthPipeline(null),
                selection, refs);
    }

    private static int instrumentConcolicAccessorCallContexts(
            Object selection, Object refs) throws Exception {
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicAccessorCallContexts",
                selection.getClass(), refs.getClass());
        instrument.setAccessible(true);
        return (Integer) instrument.invoke(
                new CausynthPipeline(null), selection, refs);
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
        fixture.staticMethod(concolic, "enterRegionFrame",
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
        fixture.staticMethod(concolic, "exitRegionFrame",
                Arrays.asList(fixture.string, fixture.object,
                        fixture.string), VoidType.v());
        fixture.staticMethod(concolic, "throwRegionFrame",
                Arrays.asList(fixture.string, fixture.throwable),
                VoidType.v());
        SootClass system = Scene.v().getSootClassUnsafe("java.lang.System");
        if (system == null) {
            system = fixture.runtimeClass("java.lang.System");
        }
        fixture.staticMethod(system, "pauseConcolicPathCondition",
                Collections.emptyList(), VoidType.v());
        fixture.staticMethod(system, "resumeConcolicPathCondition",
                Collections.emptyList(), VoidType.v());
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
        CausynthAnalysisResult result = new CausynthAnalysisResult();
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("staticRootCandidate", rootSignature);
        result.symbolicRegions.add(region);
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

    private static void addGlobalRootSelector(JsonObject activation,
                                              String method) {
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("method", method);
        selector.addProperty("ordinal", 1);
        activation.add("rootSelector", selector);
    }
}
