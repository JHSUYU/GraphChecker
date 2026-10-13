package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Test;
import soot.Body;
import soot.G;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.VoidType;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;

/**
 * A work start passes what the work was submitted to ({@code
 * Identity#handsOff} reads an executor's queue from it): the submission's
 * receiver, and null for a static call that starts work.
 */
public class WorkStartWeaveTest {
    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aStartPassesTheReceiverItWasSubmittedTo() {
        SootClass runnable = library("java.lang.Runnable", true);
        SootClass executor = library("java.util.concurrent.Executor", true);
        SootClass pools = library("a.Pools", false);
        SootClass owner = new SootClass("a.Submitter", Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootMethod method = new SootMethod("submit", Arrays.<Type>asList(
                executor.getType(), runnable.getType()), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local pool = local(body, "r0", executor.getType(), 0);
        Local task = local(body, "r1", runnable.getType(), 1);
        List<Type> runs = Collections.<Type>singletonList(runnable.getType());
        // pool.execute(task); a.Pools.execute(task);
        Stmt submitted = Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(pool, Scene.v()
                        .makeMethodRef(executor, "execute", runs,
                                VoidType.v(), false), task));
        Stmt helper = Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(Scene.v().makeMethodRef(
                        pools, "execute", runs, VoidType.v(), true), task));
        body.getUnits().add(submitted);
        body.getUnits().add(helper);
        body.getUnits().add(Jimple.v().newReturnVoidStmt());

        CausynthPipeline.HookCatalog refs =
                CausynthPipeline.HookCatalog.concolic();
        Object[][] table = {
                // the start, its site, what it passes as submitted to
                {submitted, "<a.Submitter: void submit()>#u2", pool},
                {helper, "<a.Submitter: void submit()>#u3", NullConstant.v()},
        };
        for (Object[] row : table) {
            Stmt start = (Stmt) row[0];
            assertEquals(1, CausynthPipeline.fileStarts(body, start,
                    (String) row[1], refs));
            InvokeExpr filed = startWorkBefore(body, start);
            assertSame(start.toString(), task, filed.getArg(1));
            assertEquals(start.toString(), row[2], filed.getArg(2));
        }
    }

    private static SootClass library(String name, boolean isInterface) {
        SootClass type = new SootClass(name, Modifier.PUBLIC
                | (isInterface ? Modifier.INTERFACE : 0));
        Scene.v().addClass(type);
        type.setLibraryClass();
        return type;
    }

    private static Local local(Body body, String name, RefType type,
                               int parameter) {
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        body.getUnits().add(Jimple.v().newIdentityStmt(local,
                Jimple.v().newParameterRef(type, parameter)));
        return local;
    }

    /** The startWork call woven before {@code start}: the last before it. */
    private static InvokeExpr startWorkBefore(Body body, Stmt start) {
        List<Unit> units = new ArrayList<>(body.getUnits());
        for (int at = units.indexOf(start) - 1; at >= 0; at--) {
            Unit unit = units.get(at);
            if (unit instanceof InvokeStmt && "startWork".equals(
                    ((InvokeStmt) unit).getInvokeExpr().getMethodRef()
                            .getName())) {
                return ((InvokeStmt) unit).getInvokeExpr();
            }
        }
        throw new AssertionError("no startWork before " + start);
    }
}
