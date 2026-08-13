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
import soot.ArrayType;
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
import java.util.Set;

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
    public void statePassRecordsOnlyReferenceArrayElements()
            throws Exception {
        SootMethod method = methodWithReferenceAndPrimitiveArrays();
        invoke("instrumentRuntimeState", selected(method));

        List<String> hooks = hookNames(method.getActiveBody());
        assertEquals(2, count(hooks, "recordArrayElement"));
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
    public void replayEntrySkipsConcretePrefixAtProvedCommonCaller() {
        G.reset();
        addCoreReferenceClasses();
        SootClass service = new SootClass("example.ReplayService",
                Modifier.PUBLIC);
        service.setSuperclass(Scene.v().getSootClass("java.lang.Object"));
        service.setApplicationClass();
        Scene.v().addClass(service);
        service.setApplicationClass();
        SootClass writer = new SootClass("example.ReplayWriter",
                Modifier.PUBLIC);
        writer.setSuperclass(Scene.v().getSootClass("java.lang.Object"));
        writer.setApplicationClass();
        Scene.v().addClass(writer);
        writer.setApplicationClass();

        SootMethod run = staticVoidMethod(service, "run");
        SootMethod connect = staticVoidMethod(service, "connect");
        SootMethod offer = staticVoidMethod(service, "offer");
        SootMethod target = staticVoidMethod(service, "target");
        SootMethod output = staticVoidMethod(writer, "output");
        run.getActiveBody().getUnits().insertBefore(Jimple.v()
                        .newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                                connect.makeRef())),
                run.getActiveBody().getUnits().getLast());
        run.getActiveBody().getUnits().insertBefore(Jimple.v()
                        .newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                                offer.makeRef())),
                run.getActiveBody().getUnits().getLast());
        offer.getActiveBody().getUnits().insertBefore(Jimple.v()
                        .newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                                target.makeRef())),
                offer.getActiveBody().getUnits().getLast());
        offer.getActiveBody().getUnits().insertBefore(Jimple.v()
                        .newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                                output.makeRef())),
                offer.getActiveBody().getUnits().getLast());

        assertTrue(service.isApplicationClass());
        assertTrue(offer.isConcrete());
        assertTrue(CausynthPipeline.compatibleReplayEntry(run, offer));
        Set<SootMethod> runCallees = CausynthPipeline
                .directApplicationCallees(run);
        Set<SootMethod> offerCallees = CausynthPipeline
                .directApplicationCallees(offer);
        assertTrue(runCallees.toString(), runCallees.contains(offer));
        assertTrue(offerCallees.toString(), offerCallees
                .containsAll(Arrays.asList(target, output)));

        SootMethod selected = CausynthPipeline.selectConcolicReplayEntry(
                run, Arrays.asList(target.getSignature(),
                        output.getSignature()));

        assertEquals(offer, selected);
    }

    @Test
    public void delayedReplayArmRequiresOneExactUndemandedTargetCall() {
        G.reset();
        addCoreReferenceClasses();
        SootClass service = new SootClass("example.DelayedReplayService",
                Modifier.PUBLIC);
        service.setSuperclass(Scene.v().getSootClass("java.lang.Object"));
        service.setApplicationClass();
        Scene.v().addClass(service);
        service.setApplicationClass();
        SootMethod offer = staticVoidMethod(service, "offer");
        SootMethod target = staticVoidMethod(service, "target");
        Stmt targetCall = Jimple.v().newInvokeStmt(Jimple.v()
                .newStaticInvokeExpr(target.makeRef()));
        offer.getActiveBody().getUnits().insertBefore(targetCall,
                offer.getActiveBody().getUnits().getLast());

        assertEquals(targetCall,
                CausynthPipeline.selectDelayedReplayArmCall(offer,
                        target.getSignature(),
                        Collections.singleton(offer.getSignature()),
                        true, true));
        assertEquals(null,
                CausynthPipeline.selectDelayedReplayArmCall(offer,
                        target.getSignature(),
                        Collections.singleton(target.getSignature()),
                        true, true));
        assertEquals(null,
                CausynthPipeline.selectDelayedReplayArmCall(offer,
                        target.getSignature(), Collections.emptySet(),
                        false, true));
        assertEquals(targetCall,
                CausynthPipeline.selectPreTargetReplayArmCall(offer,
                        target.getSignature(),
                        Collections.singleton(target.getSignature()),
                        true, true));
        assertEquals(null,
                CausynthPipeline.selectPreTargetReplayArmCall(offer,
                        target.getSignature(),
                        Collections.singleton(offer.getSignature()),
                        true, true));

        SootMethod output = staticVoidMethod(service, "output");
        target.getActiveBody().getUnits().insertBefore(Jimple.v()
                        .newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                                output.makeRef())),
                target.getActiveBody().getUnits().getLast());
        assertTrue(CausynthPipeline.directApplicationCallees(target)
                .contains(output));
        assertEquals(null,
                CausynthPipeline.selectDelayedReplayArmCall(offer,
                        target.getSignature(),
                        Collections.singleton(output.getSignature()),
                        true, true));
        assertEquals(targetCall,
                CausynthPipeline.selectPreTargetReplayArmCall(offer,
                        target.getSignature(),
                        Collections.singleton(output.getSignature()),
                        true, true));

        offer.getActiveBody().getUnits().insertBefore(Jimple.v()
                        .newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                                target.makeRef())),
                offer.getActiveBody().getUnits().getLast());
        assertEquals(null,
                CausynthPipeline.selectDelayedReplayArmCall(offer,
                        target.getSignature(), Collections.emptySet(),
                        true, true));
        assertEquals(null,
                CausynthPipeline.selectPreTargetReplayArmCall(offer,
                        target.getSignature(),
                        Collections.singleton(output.getSignature()),
                        true, true));
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
        assertEquals(-1, indexOfHook(new ArrayList<>(body.getUnits()),
                "prepareAtomicMutationStateOutput"));
    }

    @Test
    public void atomicMutationPreparesExactValueBeforeRmwCall()
            throws Exception {
        G.reset();
        addCoreReferenceClasses();
        SootClass atomic = new SootClass(
                "java.util.concurrent.atomic.AtomicInteger",
                Modifier.PUBLIC);
        atomic.setApplicationClass();
        Scene.v().addClass(atomic);
        SootMethod decrement = new SootMethod("getAndDecrement",
                Collections.emptyList(), IntType.v(), Modifier.PUBLIC);
        atomic.addMethod(decrement);

        SootClass owner = new SootClass("example.AtomicMutationOwner",
                Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootField state = new SootField("state", atomic.getType(),
                Modifier.PUBLIC);
        owner.addField(state);
        SootMethod method = new SootMethod("run",
                Collections.singletonList(atomic.getType()),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local value = Jimple.v().newLocal("value", atomic.getType());
        body.getLocals().add(value);
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef(atomic.getType(), 0)));
        Stmt call = Jimple.v().newInvokeStmt(Jimple.v()
                .newVirtualInvokeExpr(value, decrement.makeRef()));
        body.getUnits().add(call);
        body.getUnits().add(Jimple.v().newReturnVoidStmt());

        instrumentExactHeapCapture(exactCapture(
                OutputCaptureSpec.MUTATION_STATE,
                method.getSignature(), 1, decrement.getSignature(),
                state.getSignature(), atomic.getName()));

        Unit resume = body.getUnits().getPredOf(call);
        assertEquals("resumeObservation", hookName(resume));
        Unit prepare = body.getUnits().getPredOf(resume);
        assertEquals("prepareAtomicMutationStateOutput",
                hookName(prepare));
        assertEquals("pauseObservation", hookName(
                body.getUnits().getPredOf(prepare)));
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

    @Test
    public void nestedFieldWriteStateHookUsesCarrierAssignment()
            throws Exception {
        G.reset();
        addCoreReferenceClasses();
        Scene.v().addClass(new SootClass("java.lang.Integer",
                Modifier.PUBLIC));
        SootClass carrier = new SootClass("example.NestedCarrier",
                Modifier.PUBLIC);
        carrier.setApplicationClass();
        Scene.v().addClass(carrier);
        SootField primitiveLeaf = new SootField("primitiveLeaf",
                IntType.v(), Modifier.PUBLIC);
        carrier.addField(primitiveLeaf);
        SootClass owner = new SootClass("example.NestedOwner",
                Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootField carrierField = new SootField("carrier",
                carrier.getType(), Modifier.PUBLIC);
        owner.addField(carrierField);
        SootMethod method = new SootMethod("write",
                Collections.<soot.Type>singletonList(carrier.getType()),
                VoidType.v(), Modifier.PUBLIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = Jimple.v().newLocal("receiver", owner.getType());
        Local value = Jimple.v().newLocal("value", carrier.getType());
        body.getLocals().add(receiver);
        body.getLocals().add(value);
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef(owner.getType())));
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef(carrier.getType(), 0)));
        Stmt carrierAssignment = Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(receiver,
                        carrierField.makeRef()), value);
        body.getUnits().add(carrierAssignment);
        Stmt leafAssignment = Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(value,
                        primitiveLeaf.makeRef()), IntConstant.v(7));
        body.getUnits().add(leafAssignment);
        body.getUnits().add(Jimple.v().newReturnVoidStmt());

        instrumentExactHeapCapture(exactCapture(
                OutputCaptureSpec.FIELD_WRITE_STATE,
                method.getSignature(), 2, "",
                primitiveLeaf.getSignature(), "int",
                carrierField.getSignature(), primitiveLeaf.getSignature(),
                Arrays.asList("carrier", "primitiveLeaf")));

        List<Unit> units = new ArrayList<>(body.getUnits());
        int record = indexOfHook(units, "recordFieldWriteStateOutput");
        assertEquals(1, count(hookNames(body),
                "recordFieldWriteStateOutput"));
        assertTrue(units.indexOf(carrierAssignment) < record);
        assertTrue(record < units.indexOf(leafAssignment));
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

    private static SootMethod methodWithReferenceAndPrimitiveArrays() {
        G.reset();
        addCoreReferenceClasses();
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        SootClass owner = new SootClass("example.ArrayState",
                Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        ArrayType references = ArrayType.v(
                RefType.v("java.lang.Object"), 1);
        ArrayType primitives = ArrayType.v(IntType.v(), 1);
        SootMethod method = new SootMethod("run", Arrays.asList(
                references, RefType.v("java.lang.Object"), primitives),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local array = Jimple.v().newLocal("array", references);
        Local value = Jimple.v().newLocal("value",
                RefType.v("java.lang.Object"));
        Local loaded = Jimple.v().newLocal("loaded",
                RefType.v("java.lang.Object"));
        Local ints = Jimple.v().newLocal("ints", primitives);
        Local integer = Jimple.v().newLocal("integer", IntType.v());
        body.getLocals().add(array);
        body.getLocals().add(value);
        body.getLocals().add(loaded);
        body.getLocals().add(ints);
        body.getLocals().add(integer);
        body.getUnits().add(Jimple.v().newIdentityStmt(array,
                Jimple.v().newParameterRef(references, 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef(
                        RefType.v("java.lang.Object"), 1)));
        body.getUnits().add(Jimple.v().newIdentityStmt(ints,
                Jimple.v().newParameterRef(primitives, 2)));
        body.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newArrayRef(array, IntConstant.v(0)), value));
        body.getUnits().add(Jimple.v().newAssignStmt(loaded,
                Jimple.v().newArrayRef(array, IntConstant.v(0))));
        body.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newArrayRef(ints, IntConstant.v(0)),
                IntConstant.v(1)));
        body.getUnits().add(Jimple.v().newAssignStmt(integer,
                Jimple.v().newArrayRef(ints, IntConstant.v(0))));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static SootMethod staticVoidMethod(
            SootClass owner, String name) {
        SootMethod method = new SootMethod(name, Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
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
        return exactCapture(captureKind, method, unitIndex, declaredCallee,
                fieldSignature, javaType, "", "",
                Collections.<String>emptyList());
    }

    private static Object exactCapture(
            String captureKind, String method, int unitIndex,
            String declaredCallee, String fieldSignature, String javaType,
            String definitionFieldSignature, String leafFieldSignature,
            List<String> fieldPath) throws Exception {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.test");
        capture.addProperty("captureKind", captureKind);
        capture.addProperty("outputPort", "REGION.P.out.state");
        capture.addProperty("outputCell", fieldSignature);
        capture.addProperty("fieldSignature", fieldSignature);
        capture.addProperty("javaType", javaType);
        capture.addProperty("definitionMethod", method);
        capture.addProperty("definitionUnitIndex", unitIndex);
        if (!definitionFieldSignature.isEmpty()) {
            capture.addProperty("definitionFieldSignature",
                    definitionFieldSignature);
            capture.addProperty("leafFieldSignature", leafFieldSignature);
            JsonArray path = new JsonArray();
            for (String field : fieldPath) path.add(field);
            capture.add("fieldPath", path);
        }
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
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL.REGION.P", "REGION.P", "CONTRACT.TEST",
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

    private static int indexOfHook(List<Unit> units, String name) {
        for (int index = 0; index < units.size(); index++) {
            if (name.equals(hookName(units.get(index)))) return index;
        }
        return -1;
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
