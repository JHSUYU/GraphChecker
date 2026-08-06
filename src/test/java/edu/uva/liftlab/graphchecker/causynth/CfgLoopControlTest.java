package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import soot.Body;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.toolkits.graph.BriefUnitGraph;

import java.util.Collections;
import java.util.Set;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class CfgLoopControlTest {
    @Before
    public void resetBefore() {
        soot.G.reset();
    }

    @After
    public void resetAfter() {
        soot.G.reset();
    }

    @Test
    public void naturalLoopExitIsControlButBodyPredicateIsSemantic() {
        SootClass owner = new SootClass("example.Loop", Modifier.PUBLIC);
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local running = Jimple.v().newLocal("running", IntType.v());
        Local expiry = Jimple.v().newLocal("expiry", IntType.v());
        Local now = Jimple.v().newLocal("now", IntType.v());
        Local changed = Jimple.v().newLocal("changed", IntType.v());
        body.getLocals().add(running);
        body.getLocals().add(expiry);
        body.getLocals().add(now);
        body.getLocals().add(changed);

        Unit exit = Jimple.v().newReturnVoidStmt();
        Unit loopGuard = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(running, IntConstant.v(0)), exit);
        Unit latch = Jimple.v().newGotoStmt(loopGuard);
        Unit semanticGuard = Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(expiry, now), latch);
        body.getUnits().add(loopGuard);
        body.getUnits().add(semanticGuard);
        body.getUnits().add(Jimple.v().newAssignStmt(
                changed, IntConstant.v(1)));
        body.getUnits().add(latch);
        body.getUnits().add(exit);

        Set<Unit> guards = CfgLoopControl.guards(body,
                new BriefUnitGraph(body));
        assertTrue(guards.contains(loopGuard));
        assertFalse(guards.contains(semanticGuard));
    }

    @Test
    public void caughtLoopBodyStillHasNaturalContinuationGuard() {
        SootClass throwable = new SootClass("java.lang.Throwable",
                Modifier.PUBLIC);
        soot.Scene.v().addClass(throwable);
        SootClass exception = new SootClass("java.lang.Exception",
                Modifier.PUBLIC);
        exception.setSuperclass(throwable);
        soot.Scene.v().addClass(exception);
        SootClass owner = new SootClass("example.CaughtLoop",
                Modifier.PUBLIC);
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local running = Jimple.v().newLocal("running", IntType.v());
        Local expiry = Jimple.v().newLocal("expiry", IntType.v());
        Local now = Jimple.v().newLocal("now", IntType.v());
        Local failure = Jimple.v().newLocal("failure",
                RefType.v(exception));
        Local caught = Jimple.v().newLocal("caught",
                RefType.v(exception));
        body.getLocals().add(running);
        body.getLocals().add(expiry);
        body.getLocals().add(now);
        body.getLocals().add(failure);
        body.getLocals().add(caught);

        Unit exit = Jimple.v().newReturnVoidStmt();
        Unit loopGuard = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(running, IntConstant.v(0)), exit);
        Unit latch = Jimple.v().newGotoStmt(loopGuard);
        Unit semanticGuard = Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(expiry, now), latch);
        Unit throwing = Jimple.v().newThrowStmt(failure);
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        body.getUnits().add(loopGuard);
        body.getUnits().add(semanticGuard);
        body.getUnits().add(throwing);
        body.getUnits().add(handler);
        body.getUnits().add(latch);
        body.getUnits().add(exit);
        body.getTraps().add(Jimple.v().newTrap(exception, throwing,
                handler, handler));

        Set<Unit> guards = CfgLoopControl.guards(body,
                new BriefUnitGraph(body));
        assertTrue(guards.contains(loopGuard));
        assertFalse(guards.contains(semanticGuard));
    }
}
