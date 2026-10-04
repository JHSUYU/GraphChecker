package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Test;
import soot.Body;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.UnitBox;
import soot.jimple.Stmt;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;

/**
 * Where one iteration of a loop can open its frame for a demanded call
 * (IDENTITY §1, LOOP_BODY_ROOT): SEED states it and INSTRUMENT asks the same
 * function, so a loop body SEED names is one the weave can open.
 */
public class LoopBodyEntryTest {
    private SootMethod work;

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void anIterationOpensWhereItHoldsTheCallOrNowhere() {
        SootClass owner = new SootClass("a.Loops", Modifier.PUBLIC);
        Scene.v().addClass(owner);
        work = new SootMethod("work", Collections.<Type>emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(work);

        // hdfs-adhoc-41, INodesInPath.getExistingINodes: the loop returns a
        // call from inside it.  The call is on the exit path: no member.
        Unit[] exitPath = new Unit[8];
        SootMethod exiting = method(owner, "exitPath", exitPath, (l, u) -> {
            u[1] = Jimple.v().newIfStmt(Jimple.v().newLeExpr(l[0],
                    IntConstant.v(0)), u[7]);
            u[2] = Jimple.v().newIfStmt(Jimple.v().newNeExpr(l[1],
                    IntConstant.v(0)), u[6]);
            u[3] = Jimple.v().newAssignStmt(l[0], Jimple.v().newSubExpr(l[0],
                    IntConstant.v(1)));
            u[4] = Jimple.v().newGotoStmt(u[1]);
            u[6] = call();
        });
        // The call in the body, after both controls: the outermost control
        // edge whose target holds it, the second control's entry.
        Unit[] inBody = new Unit[8];
        SootMethod body = method(owner, "inBody", inBody, (l, u) -> {
            u[1] = Jimple.v().newIfStmt(Jimple.v().newLeExpr(l[0],
                    IntConstant.v(0)), u[7]);
            u[2] = Jimple.v().newIfStmt(Jimple.v().newNeExpr(l[1],
                    IntConstant.v(0)), u[7]);
            u[3] = call();
            u[4] = Jimple.v().newAssignStmt(l[0], Jimple.v().newSubExpr(l[0],
                    IntConstant.v(1)));
            u[5] = Jimple.v().newGotoStmt(u[1]);
        });
        // A while (true) whose work comes before its only control: each turn
        // is the header's.
        Unit[] beforeControls = new Unit[8];
        SootMethod before = method(owner, "beforeControls", beforeControls,
                (l, u) -> {
            u[1] = call();
            u[2] = Jimple.v().newIfStmt(Jimple.v().newGtExpr(l[0],
                    IntConstant.v(0)), u[7]);
            u[3] = Jimple.v().newAssignStmt(l[0], Jimple.v().newAddExpr(l[0],
                    IntConstant.v(1)));
            u[4] = Jimple.v().newGotoStmt(u[1]);
        });
        // Two controls enter the call alike: no one entry is proved.
        Unit[] alike = new Unit[10];
        SootMethod twice = method(owner, "alike", alike, (l, u) -> {
            u[1] = Jimple.v().newIfStmt(Jimple.v().newGtExpr(l[0],
                    IntConstant.v(0)), u[4]);
            u[2] = Jimple.v().newIfStmt(Jimple.v().newLeExpr(l[1],
                    IntConstant.v(0)), u[6]);
            u[3] = Jimple.v().newGotoStmt(u[9]);
            u[4] = Jimple.v().newIfStmt(Jimple.v().newLeExpr(l[0],
                    IntConstant.v(9)), u[6]);
            u[5] = Jimple.v().newGotoStmt(u[9]);
            u[6] = call();
            u[7] = Jimple.v().newAssignStmt(l[0], Jimple.v().newSubExpr(l[0],
                    IntConstant.v(1)));
            u[8] = Jimple.v().newGotoStmt(u[1]);
        });

        Object[][] rows = {
            // name, method, the demanded call, the entry's target (null: none)
            {"a call on the loop's exit path", exiting, exitPath[6], null},
            {"a call in the body after the controls", body, inBody[3],
                    inBody[2]},
            {"work before every control", before, beforeControls[1],
                    beforeControls[1]},
            {"a call two controls enter alike", twice, alike[6], null},
        };
        for (Object[] row : rows) {
            List<CfgLoopControl.RetainedLoop> loops =
                    CfgLoopControl.retainedLoops(CfgLoopControl.loopCfg(
                            ((SootMethod) row[1]).getActiveBody()));
            assertEquals((String) row[0], 1, loops.size());
            CfgLoopControl.Edge entry = CfgLoopControl.bodyEntry(
                    loops.get(0).natural, loops.get(0).guards, (Unit) row[2]);
            if (row[3] == null) {
                assertNull((String) row[0], entry);
            } else {
                assertSame((String) row[0], row[3], entry.target);
            }
        }
    }

    private interface Shape {
        void build(Local[] locals, Unit[] units);
    }

    /**
     * {@code static void name(int i0, int i1)}: its identities, then the
     * units the shape sets in slots 1..n-2, then a return in the last slot.
     * A branch may name a slot the shape sets later.
     */
    private static SootMethod method(SootClass owner, String name,
                                     Unit[] units, Shape shape) {
        SootMethod method = new SootMethod(name,
                Arrays.<Type>asList(IntType.v(), IntType.v()), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local[] locals = {Jimple.v().newLocal("i0", IntType.v()),
                Jimple.v().newLocal("i1", IntType.v())};
        body.getLocals().addAll(Arrays.asList(locals));
        Unit[] holes = new Unit[units.length];
        for (int index = 0; index < units.length; index++) {
            holes[index] = Jimple.v().newNopStmt();
            units[index] = holes[index];
        }
        units[units.length - 1] = Jimple.v().newReturnVoidStmt();
        shape.build(locals, units);
        body.getUnits().add(Jimple.v().newIdentityStmt(locals[0],
                Jimple.v().newParameterRef(IntType.v(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(locals[1],
                Jimple.v().newParameterRef(IntType.v(), 1)));
        for (int index = 1; index < units.length; index++) {
            if (units[index] != holes[index]) body.getUnits().add(units[index]);
        }
        for (Unit unit : body.getUnits()) {
            for (UnitBox box : unit.getUnitBoxes()) {
                for (int index = 0; index < holes.length; index++) {
                    if (box.getUnit() == holes[index]) {
                        box.setUnit(units[index]);
                    }
                }
            }
        }
        return method;
    }

    /** {@code staticinvoke work()}: the demanded call. */
    private Stmt call() {
        return Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
                work.makeRef()));
    }
}
