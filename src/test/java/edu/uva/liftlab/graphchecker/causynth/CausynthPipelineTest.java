package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.After;
import org.junit.Test;
import soot.Body;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.IdentityStmt;
import soot.jimple.Jimple;
import soot.jimple.Stmt;
import soot.tagkit.Tag;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class CausynthPipelineTest {
    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void skeletonPassRecordsOnlyBalancedMethodEnvelope()
            throws Exception {
        SootMethod method = targetMethod();
        StaticProgram program = selected(method);

        invoke("instrumentRegionSkeletonTrace", program);

        List<String> hooks = hookNames(method.getActiveBody());
        assertTrue(hooks.contains("enterMethodLite"));
        assertTrue(hooks.contains("exitActiveMethodLite"));
        assertTrue(hooks.contains("throwActiveMethodLite"));
        assertFalse(hooks.contains("recordField"));
        assertFalse(hooks.contains("recordBranch"));
        assertFalse(hooks.contains("recordMethodArgument"));
    }

    @Test
    public void statePassRecordsEveryDirectFieldAndBranchInSelectedMethod()
            throws Exception {
        SootMethod method = targetMethod();
        StaticProgram program = selected(method);

        invoke("instrumentRuntimeState", program);

        List<String> hooks = hookNames(method.getActiveBody());
        assertTrue(hooks.contains("enterMethod"));
        assertTrue(hooks.contains("recordBranch"));
        assertEquals(4, count(hooks, "recordField"));
        assertFalse(hooks.contains("enterMethodLite"));
    }

    @Test
    public void concolicLoopBoundSplitsEveryOriginalCfgBackedge()
            throws Exception {
        SootMethod method = methodWithGotoAndConditionalBackedges();
        Body body = method.getActiveBody();
        int originalIfCount = countUnits(body, soot.jimple.IfStmt.class);

        int bounded = new CausynthPipeline(null)
                .instrumentConcolicLoopBounds(
                        Collections.singleton(method.getSignature()),
                        LoopBoundPolicy.cfgBackedges(8));

        assertEquals(2, bounded);
        assertEquals(2, count(hookNames(body), "recordLoopBackedge"));
        assertEquals(2, count(hookNames(body), "checkLoopBodyEntry"));
        assertEquals(0, count(hookNames(body), "checkLoopBackedge"));
        // Synthetic loop-accounting invokes create no branch eligible for
        // symbolic-PC instrumentation.
        assertEquals(originalIfCount,
                countUnits(body, soot.jimple.IfStmt.class));
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()
                    || !("recordLoopBackedge".equals(((Stmt) unit)
                    .getInvokeExpr().getMethodRef().name())
                    || "checkLoopBodyEntry".equals(((Stmt) unit)
                    .getInvokeExpr().getMethodRef().name()))) {
                continue;
            }
            assertFalse(hasOriginalUnitTag(unit));
            assertEquals(8, ((IntConstant) ((Stmt) unit).getInvokeExpr()
                    .getArg(1)).value);
        }
        body.validate();
    }

    @Test
    public void mutationStateHookRunsAfterExactMutatorCall()
            throws Exception {
        G.reset();
        addCoreReferenceClasses();
        SootClass container = new SootClass("example.Container",
                Modifier.PUBLIC);
        container.setApplicationClass();
        Scene.v().addClass(container);
        SootMethod mutate = new SootMethod("mutate",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        container.addMethod(mutate);
        SootClass owner = new SootClass("example.MutationOwner",
                Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootField state = new SootField("state", container.getType(),
                Modifier.PUBLIC);
        owner.addField(state);
        SootMethod method = new SootMethod("run",
                Collections.singletonList(container.getType()),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local value = Jimple.v().newLocal("value", container.getType());
        body.getLocals().add(value);
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef(container.getType(), 0)));
        Stmt call = Jimple.v().newInvokeStmt(Jimple.v()
                .newVirtualInvokeExpr(value, mutate.makeRef()));
        body.getUnits().add(call);
        Stmt completion = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(completion);

        instrumentExactHeapCapture(exactCapture(
                OutputCaptureSpec.MUTATION_STATE,
                method.getSignature(), 1, mutate.getSignature(),
                state.getSignature(), "example.Container"));

        Unit entryPause = body.getUnits().getSuccOf(
                body.getUnits().getFirst());
        assertEquals("pauseObservation", hookName(entryPause));
        Unit entryBegin = body.getUnits().getSuccOf(entryPause);
        assertEquals("beginMutationMethodStateOutput",
                hookName(entryBegin));
        assertEquals("resumeObservation", hookName(
                body.getUnits().getSuccOf(entryBegin)));
        assertEquals("pauseObservation", hookName(
                body.getUnits().getSuccOf(call)));
        Unit record = body.getUnits().getSuccOf(
                body.getUnits().getSuccOf(call));
        assertEquals("recordMutationStateOutput", hookName(record));
        assertEquals("resumeObservation", hookName(
                body.getUnits().getSuccOf(record)));
        Unit completionResume = body.getUnits().getPredOf(completion);
        assertEquals("resumeObservation", hookName(completionResume));
        Unit completionRecord = body.getUnits().getPredOf(completionResume);
        assertEquals("recordMutationMethodExitStateOutput",
                hookName(completionRecord));
        assertEquals("pauseObservation", hookName(
                body.getUnits().getPredOf(completionRecord)));
    }

    @Test
    public void fieldWriteStateHookRunsAfterExactAssignment()
            throws Exception {
        G.reset();
        addCoreReferenceClasses();
        SootClass owner = new SootClass("example.FieldOwner",
                Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootField state = new SootField("state",
                RefType.v("java.lang.Object"), Modifier.PUBLIC);
        owner.addField(state);
        SootMethod method = new SootMethod("write",
                Collections.<soot.Type>singletonList(
                        RefType.v("java.lang.Object")),
                VoidType.v(), Modifier.PUBLIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = Jimple.v().newLocal("receiver", owner.getType());
        Local value = Jimple.v().newLocal("value",
                RefType.v("java.lang.Object"));
        body.getLocals().add(receiver);
        body.getLocals().add(value);
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(owner.getType())));
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef(
                        RefType.v("java.lang.Object"), 0)));
        Stmt assignment = Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(receiver, state.makeRef()),
                value);
        body.getUnits().add(assignment);
        body.getUnits().add(Jimple.v().newReturnVoidStmt());

        instrumentExactHeapCapture(exactCapture(
                OutputCaptureSpec.FIELD_WRITE_STATE,
                method.getSignature(), 2, "", state.getSignature(),
                "java.lang.Object"));

        assertEquals("pauseObservation", hookName(
                body.getUnits().getSuccOf(assignment)));
        assertTrue(hookNames(body).contains("recordFieldWriteStateOutput"));
        assertEquals("resumeObservation",
                hookNames(body).get(hookNames(body).indexOf(
                        "recordFieldWriteStateOutput") + 1));
    }

    private static SootMethod targetMethod() {
        G.reset();
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.String",
                Modifier.PUBLIC));
        SootClass owner = new SootClass("example.SelectedState",
                Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootField left = new SootField("left", IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        SootField right = new SootField("right", IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addField(left);
        owner.addField(right);
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local a = Jimple.v().newLocal("a", IntType.v());
        Local b = Jimple.v().newLocal("b", IntType.v());
        body.getLocals().add(a);
        body.getLocals().add(b);
        body.getUnits().add(Jimple.v().newAssignStmt(a,
                Jimple.v().newStaticFieldRef(left.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(b,
                Jimple.v().newStaticFieldRef(right.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newStaticFieldRef(left.makeRef()), a));
        body.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newStaticFieldRef(right.makeRef()), b));
        Unit exit = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(a, IntConstant.v(0)), exit));
        body.getUnits().add(exit);
        return method;
    }

    private static SootMethod methodWithGotoAndConditionalBackedges() {
        G.reset();
        SootClass runtime = new SootClass(
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                Modifier.PUBLIC);
        runtime.addMethod(new SootMethod("checkLoopBackedge",
                java.util.Arrays.asList(RefType.v("java.lang.String"),
                        IntType.v()), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC));
        runtime.addMethod(new SootMethod("recordLoopBackedge",
                java.util.Arrays.asList(RefType.v("java.lang.String"),
                        IntType.v()), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC));
        runtime.addMethod(new SootMethod("checkLoopBodyEntry",
                java.util.Arrays.asList(RefType.v("java.lang.String"),
                        IntType.v()), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC));
        Scene.v().addClass(runtime);
        SootClass owner = new SootClass("example.BoundedLoops",
                Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local i = Jimple.v().newLocal("i", IntType.v());
        body.getLocals().add(i);

        Unit firstHead = Jimple.v().newNopStmt();
        Unit firstExit = Jimple.v().newNopStmt();
        body.getUnits().add(Jimple.v().newAssignStmt(i, IntConstant.v(0)));
        body.getUnits().add(firstHead);
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(i, IntConstant.v(1)), firstExit));
        body.getUnits().add(Jimple.v().newAssignStmt(i,
                Jimple.v().newAddExpr(i, IntConstant.v(1))));
        body.getUnits().add(Jimple.v().newGotoStmt(firstHead));
        body.getUnits().add(firstExit);

        Unit secondHead = Jimple.v().newNopStmt();
        body.getUnits().add(secondHead);
        body.getUnits().add(Jimple.v().newAssignStmt(i,
                Jimple.v().newSubExpr(i, IntConstant.v(1))));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newGtExpr(i, IntConstant.v(0)), secondHead));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static void addCoreReferenceClasses() {
        Scene.v().addClass(new SootClass("java.lang.Object",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.String",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.System",
                Modifier.PUBLIC));
    }

    private static Object exactCapture(
            String captureKind, String method, int unitIndex,
            String declaredCallee, String fieldSignature, String javaType)
            throws Exception {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.test");
        capture.addProperty("captureKind", captureKind);
        capture.addProperty("outputPort", "REGION.P.out.state");
        capture.addProperty("outputCell", fieldSignature);
        capture.addProperty("fieldSignature", fieldSignature);
        capture.addProperty("javaType", javaType);
        capture.addProperty("definitionMethod", method);
        capture.addProperty("definitionUnitIndex", unitIndex);
        if (!declaredCallee.isEmpty()) {
            capture.addProperty("declaredCallee", declaredCallee);
        }
        String outputSite = captureKind + ":" + method + "#u"
                + unitIndex + ":" + declaredCallee + ":" + fieldSignature;
        capture.addProperty("outputSiteId", outputSite);
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);
        if (OutputCaptureSpec.MUTATION_STATE.equals(captureKind)) {
            capture.addProperty("occurrenceScope",
                    OutputCaptureSpec.DEFINITION_INVOCATION_SCOPE);
        }

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.P.out.state");
        slice.addProperty("outputCell", fieldSignature);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        JsonArray staticSites = new JsonArray();
        staticSites.add(method + "#u" + unitIndex);
        slice.add("staticSites", staticSites);
        JsonArray methods = new JsonArray();
        methods.add(method);
        slice.add("methods", methods);
        slice.add("causalEdgeIds", new JsonArray());
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());
        slice.add("causalEdges", new JsonArray());
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REGION.P", "REGION.P@test#call1", 1,
                "REGION.P.out.state", fieldSignature,
                "HEAP_STATE", javaType, slice);
        OutputCaptureSpec spec = OutputClosureCodec.captureSpecs(closure)
                .get(0);
        Constructor<?> constructor =
                ConcolicInstrumentationSelections.ExactHeapOutputCapture.class
                        .getDeclaredConstructor(OutputCaptureSpec.class);
        constructor.setAccessible(true);
        return constructor.newInstance(spec);
    }

    private static void instrumentExactHeapCapture(Object capture)
            throws Exception {
        Method tag = CausynthPipeline.class.getDeclaredMethod(
                "tagOriginalUnits", List.class);
        tag.setAccessible(true);
        ConcolicInstrumentationSelections.ExactHeapOutputCapture typed =
                (ConcolicInstrumentationSelections.ExactHeapOutputCapture)
                        capture;
        SootMethod target = Scene.v().getMethod(typed.method());
        tag.invoke(null, new ArrayList<>(target.getActiveBody().getUnits()));

        Class<?> catalog = Class.forName(
                CausynthPipeline.class.getName() + "$HookCatalog");
        Method concolic = catalog.getDeclaredMethod("concolic");
        concolic.setAccessible(true);
        Object hooks = concolic.invoke(null);
        Method instrument = CausynthPipeline.class.getDeclaredMethod(
                "instrumentConcolicExactHeapOutputs",
                java.util.Collection.class, catalog);
        instrument.setAccessible(true);
        instrument.invoke(new CausynthPipeline(null),
                Collections.singletonList(typed), hooks);
    }

    private static String hookName(Unit unit) {
        return unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()
                ? ((Stmt) unit).getInvokeExpr().getMethodRef().name()
                : "";
    }

    private static StaticProgram selected(SootMethod method) {
        StaticProgram program = new StaticProgram();
        program.traceMethods.add(method.getSignature());
        return program;
    }

    private static void invoke(String name, StaticProgram program)
            throws Exception {
        Method method = CausynthPipeline.class.getDeclaredMethod(name,
                StaticProgram.class);
        method.setAccessible(true);
        method.invoke(new CausynthPipeline(null), program);
    }

    private static List<String> hookNames(Body body) {
        List<String> result = new ArrayList<>();
        for (Unit unit : body.getUnits()) {
            if (unit instanceof Stmt
                    && ((Stmt) unit).containsInvokeExpr()) {
                result.add(((Stmt) unit).getInvokeExpr()
                        .getMethodRef().name());
            }
        }
        return result;
    }

    private static int count(List<String> values, String expected) {
        int result = 0;
        for (String value : values) {
            if (expected.equals(value)) {
                result++;
            }
        }
        return result;
    }

    private static int countUnits(Body body, Class<?> type) {
        int result = 0;
        for (Unit unit : body.getUnits()) {
            if (type.isInstance(unit)) result++;
        }
        return result;
    }

    private static boolean hasOriginalUnitTag(Unit unit) {
        for (Tag tag : unit.getTags()) {
            if ("CausynthOriginalUnitIndex".equals(tag.getName())) {
                return true;
            }
        }
        return false;
    }
}
