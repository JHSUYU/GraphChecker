package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.EqExpr;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.NeExpr;
import soot.jimple.NopStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.SwitchStmt;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * A guard testing a boolean a helper returned, where the helper's value is
 * one of its own branches materialized as constants: {@code return now >
 * expiry;} compiles to two arms returning 1 and 0.  The VM tracks the
 * helper's comparison but not the constant it returns, so the guard decides
 * concretely; the helper's branch, at the arm that makes the guard take its
 * arm, decides it.  One branch with straight-line arms only: a helper of
 * several branches has no decider.
 */
final class BooleanReturns {
    /** How many units an arm may run before its return. */
    private static final int MAX_ARM = 16;

    private BooleanReturns() {
    }

    /** The helper branch deciding {@code guard} to take {@code arm}, or
     *  null. */
    static StaticScopeMap.Guard decider(Body body, Unit guard, boolean arm) {
        if (!(guard instanceof IfStmt)) return null;
        Value condition = ((IfStmt) guard).getCondition();
        if (!(condition instanceof EqExpr || condition instanceof NeExpr)) {
            return null;
        }
        BinopExpr test = (BinopExpr) condition;
        boolean constantFirst = test.getOp1() instanceof IntConstant;
        Value tested = constantFirst ? test.getOp2() : test.getOp1();
        Value constant = constantFirst ? test.getOp1() : test.getOp2();
        if (!(tested instanceof Local) || !(constant instanceof IntConstant)) {
            return null;
        }
        SootMethod helper = onlyCallDefining(body, (Local) tested);
        Body helperBody = helper == null ? null
                : CausynthStaticFacts.activeBody(helper);
        if (helperBody == null) return null;
        IfStmt decision = null;
        for (Unit unit : helperBody.getUnits()) {
            if (unit instanceof SwitchStmt) return null;
            if (!(unit instanceof IfStmt)) continue;
            if (decision != null) return null;
            decision = (IfStmt) unit;
        }
        if (decision == null) return null;
        Integer taken = returned(helperBody, decision.getTarget());
        Integer fallen = returned(helperBody,
                helperBody.getUnits().getSuccOf(decision));
        if (taken == null || fallen == null || taken.equals(fallen)) {
            return null;
        }
        // The guard jumps iff (value == c) == (condition is ==).
        int c = ((IntConstant) constant).value;
        boolean equality = condition instanceof EqExpr;
        boolean takenReaches = ((taken == c) == equality) == arm;
        boolean fallenReaches = ((fallen == c) == equality) == arm;
        if (takenReaches == fallenReaches) return null;
        return new StaticScopeMap.Guard(SiteId.of(helper.getSignature(),
                SiteControlDependence.originalIndex(helperBody, decision)),
                takenReaches);
    }

    /** The one method the local's one defining call can run -- a static,
     *  private or final one, or one no loaded class overrides -- or null. */
    private static SootMethod onlyCallDefining(Body body, Local local) {
        InvokeExpr call = null;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)
                    || ((AssignStmt) unit).getLeftOp() != local) {
                continue;
            }
            Value defined = ((AssignStmt) unit).getRightOp();
            if (call != null || !(defined instanceof InvokeExpr)) return null;
            call = (InvokeExpr) defined;
        }
        if (call == null) return null;
        SootMethod helper = CausynthStaticFacts.method(
                call.getMethodRef().getSignature());
        if (helper == null || !helper.isConcrete()) return null;
        if (helper.isStatic() || helper.isPrivate() || helper.isFinal()) {
            return helper;
        }
        Set<SootMethod> targets;
        try {
            targets = Scene.v().getOrMakeFastHierarchy()
                    .resolveAbstractDispatch(helper.getDeclaringClass(),
                            helper);
        } catch (RuntimeException unresolved) {
            // A phantom supertype: the overrides are unknown.
            return null;
        }
        return targets.size() == 1 && targets.contains(helper) ? helper
                : null;
    }

    /** The constant an arm returns, walking only constant stores and jumps;
     *  null for anything else. */
    private static Integer returned(Body body, Unit start) {
        Map<Value, Integer> constants = new HashMap<Value, Integer>();
        Unit unit = start;
        for (int step = 0; unit != null && step < MAX_ARM; step++) {
            if (unit instanceof ReturnStmt) {
                Value op = ((ReturnStmt) unit).getOp();
                return op instanceof IntConstant
                        ? ((IntConstant) op).value : constants.get(op);
            }
            if (unit instanceof GotoStmt) {
                unit = ((GotoStmt) unit).getTarget();
                continue;
            }
            if (unit instanceof AssignStmt
                    && ((AssignStmt) unit).getRightOp()
                    instanceof IntConstant) {
                constants.put(((AssignStmt) unit).getLeftOp(),
                        ((IntConstant) ((AssignStmt) unit).getRightOp())
                                .value);
            } else if (!(unit instanceof NopStmt)) {
                return null;
            }
            unit = body.getUnits().getSuccOf(unit);
        }
        return null;
    }
}
