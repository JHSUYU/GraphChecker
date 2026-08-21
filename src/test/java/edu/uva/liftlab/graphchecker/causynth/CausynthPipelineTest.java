package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
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
import soot.jimple.Jimple;
import soot.jimple.Stmt;
import soot.tagkit.Tag;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class CausynthPipelineTest {

    @After
    public void resetSoot() {
        G.reset();
    }

    /**
     * Each instrumentation pass records exactly what its stage is for.
     *
     * <p>The skeleton pass records a balanced method envelope and nothing
     * else, in the candidate regions and nowhere else; the state pass records
     * every direct field access and branch of a selected method; and the
     * concolic pass splits every original CFG backedge into an accounted body
     * entry without adding a branch of its own or claiming to be original
     * program code.</p>
     */
    @Test
    public void everyInstrumentationPassRecordsOnlyItsOwnStage()
            throws Exception {
        // The slice below holds three methods and one candidate region claims
        // one of them, so the others are in scope for the analysis and out of
        // scope for the skeleton trace.
        StaticProgram scope = new StaticProgram();
        scope.traceMethods.add("<a.Selected: void run()>");
        scope.traceMethods.add("<a.Unselected: void run()>");
        scope.regions.add(region("<a.Selected: void run()>",
                "<a.Selected: void run()>", "<a.Unsliced: void helper()>"));

        assertEquals(Collections.singleton("<a.Selected: void run()>"),
                CausynthPipeline.skeletonCandidateMethods(scope));

        // The annotated target survives both filters: no candidate region on
        // the HDFS checkout encloses it, and a pass that reported nothing
        // about the method the run exists to observe would be no evidence.
        scope.targetResolved.put("method", "<a.Target: void fail()>");
        assertTrue(CausynthPipeline.skeletonCandidateMethods(scope)
                .contains("<a.Target: void fail()>"));

        SootMethod skeleton = targetMethod();
        invoke("instrumentRegionSkeletonTrace", selected(skeleton));
        List<String> skeletonHooks = hookNames(skeleton.getActiveBody());
        assertTrue(skeletonHooks.contains("enterMethodLite"));
        assertTrue(skeletonHooks.contains("exitActiveMethodLite"));
        assertTrue(skeletonHooks.contains("throwActiveMethodLite"));
        assertFalse(skeletonHooks.contains("recordField"));
        assertFalse(skeletonHooks.contains("recordBranch"));
        assertFalse(skeletonHooks.contains("recordMethodArgument"));

        SootMethod state = targetMethod();
        invoke("instrumentRuntimeState", selected(state));
        List<String> stateHooks = hookNames(state.getActiveBody());
        assertTrue(stateHooks.contains("enterMethod"));
        assertTrue(stateHooks.contains("recordBranch"));
        assertEquals(4, count(stateHooks, "recordField"));
        assertFalse(stateHooks.contains("enterMethodLite"));

        SootMethod loops = methodWithGotoAndConditionalBackedges();
        Body body = loops.getActiveBody();
        int originalIfCount = countUnits(body, soot.jimple.IfStmt.class);

        int bounded = new CausynthPipeline(null)
                .instrumentConcolicLoopBounds(
                        Collections.singleton(loops.getSignature()),
                        LoopBoundPolicy.cfgBackedges(8));

        assertEquals(2, bounded);
        assertEquals(2, count(hookNames(body), "checkLoopBackedge"));
        // Synthetic loop-accounting invokes create no branch eligible for
        // symbolic-PC instrumentation.
        assertEquals(originalIfCount,
                countUnits(body, soot.jimple.IfStmt.class));
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()
                    || !"checkLoopBackedge".equals(((Stmt) unit)
                    .getInvokeExpr().getMethodRef().name())) {
                continue;
            }
            assertFalse(hasOriginalUnitTag(unit));
            assertEquals(8, ((IntConstant) ((Stmt) unit).getInvokeExpr()
                    .getArg(1)).value);
        }
        body.validate();
    }

    private static SootMethod targetMethod() {
        G.reset();
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.String",
                Modifier.PUBLIC));
        SootClass owner = new SootClass("example.SelectedState",
                Modifier.PUBLIC);
        // Scene.addClass() makes what it admits a library class, so the
        // application scope this method is selected under is stated after it.
        Scene.v().addClass(owner);
        owner.setApplicationClass();
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

    private static Map<String, Object> region(String root,
                                              String... methods) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("kind", "REGION_SKELETON");
        row.put("rootMethod", root);
        row.put("methods", Arrays.asList(methods));
        return row;
    }

    private static StaticProgram selected(SootMethod method) {
        StaticProgram program = new StaticProgram();
        program.traceMethods.add(method.getSignature());
        program.regions.add(region(method.getSignature(),
                method.getSignature()));
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
