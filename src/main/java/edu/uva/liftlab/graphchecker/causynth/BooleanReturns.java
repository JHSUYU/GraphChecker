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
import soot.jimple.Constant;
import soot.jimple.EqExpr;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.NeExpr;
import soot.jimple.NopStmt;
import soot.jimple.NullConstant;
import soot.jimple.ReturnStmt;
import soot.jimple.SwitchStmt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A guard testing a constant a helper returned, where the helper's own
 * branches choose which constant: {@code return now > expiry;} compiles to
 * two arms returning 1 and 0; {@code isSufficientlyReplicated} returns true
 * on one arm of a test of {@code hasMinStorage}'s return and a comparison's
 * outcome on the other; a lookup returns null where its loop ends.  The VM
 * tracks the helper's comparisons but not the constant it returns, so the
 * guard decides concretely, and the helper branch whose arm ran to the
 * return decides it.
 *
 * <p>The deciders of a guard {@code v ==/!= c} -- {@code c} an int or
 * null, {@code v} the result of one call of an application helper -- are
 * the helper's branch arms that run straight (constant stores, jumps, at
 * most {@link #MAX_ARM} units) to a return of a constant of {@code c}'s
 * kind; a branch whose two arms return constants the guard takes alike
 * decides nothing.  A decider that is itself such a guard on a nested
 * helper's return carries that helper's deciders, {@link #MAX_DEPTH}
 * helpers deep.  A helper with a switch has none.  At run time the
 * decision that chose the return is the latest one in the helper's method
 * before the guard, when it is a decider arm ({@code
 * runtime.RowPublication#decidedBy}).</p>
 */
final class BooleanReturns {
    /** How many units an arm may run before its return. */
    private static final int MAX_ARM = 16;
    /** How many helpers deep a decider's own deciders go. */
    private static final int MAX_DEPTH = 3;

    private BooleanReturns() {
    }

    /** The helper branch arms deciding {@code guard}; empty for none. */
    static List<StaticScopeMap.Guard> deciders(Body body, Unit guard) {
        return deciders(body, guard, 1);
    }

    private static List<StaticScopeMap.Guard> deciders(Body body, Unit guard,
                                                       int depth) {
        List<StaticScopeMap.Guard> found =
                new ArrayList<StaticScopeMap.Guard>();
        if (!(guard instanceof IfStmt)) return found;
        Value condition = ((IfStmt) guard).getCondition();
        if (!(condition instanceof EqExpr || condition instanceof NeExpr)) {
            return found;
        }
        BinopExpr test = (BinopExpr) condition;
        boolean constantFirst = constant(test.getOp1());
        Value tested = constantFirst ? test.getOp2() : test.getOp1();
        Value compared = constantFirst ? test.getOp1() : test.getOp2();
        if (!(tested instanceof Local) || !constant(compared)) return found;
        SootMethod helper = onlyCallDefining(body, (Local) tested);
        Body helperBody = helper == null
                || !helper.getDeclaringClass().isApplicationClass() ? null
                : CausynthStaticFacts.activeBody(helper);
        if (helperBody == null) return found;
        List<IfStmt> branches = new ArrayList<IfStmt>();
        for (Unit unit : helperBody.getUnits()) {
            if (unit instanceof SwitchStmt) return found;
            if (unit instanceof IfStmt) branches.add((IfStmt) unit);
        }
        for (IfStmt branch : branches) {
            Constant taken = sameKind(returned(helperBody,
                    branch.getTarget()), compared);
            Constant fallen = sameKind(returned(helperBody,
                    helperBody.getUnits().getSuccOf(branch)), compared);
            if (taken == null && fallen == null
                    || taken != null && fallen != null
                    && taken.equivTo(compared) == fallen.equivTo(compared)) {
                continue;
            }
            List<StaticScopeMap.Guard> nested = depth < MAX_DEPTH
                    ? deciders(helperBody, branch, depth + 1)
                    : Collections.<StaticScopeMap.Guard>emptyList();
            String site = SiteId.of(helper.getSignature(),
                    SiteControlDependence.originalIndex(helperBody, branch));
            if (taken != null) {
                found.add(new StaticScopeMap.Guard(site, true, nested));
            }
            if (fallen != null) {
                found.add(new StaticScopeMap.Guard(site, false, nested));
            }
        }
        return found;
    }

    /** Whether a value is a constant a guard may test a return against. */
    private static boolean constant(Value value) {
        return value instanceof IntConstant || value instanceof NullConstant;
    }

    /** {@code returned}, if it is of {@code compared}'s kind; else null. */
    private static Constant sameKind(Constant returned, Value compared) {
        return returned != null && (returned instanceof IntConstant
                == compared instanceof IntConstant) ? returned : null;
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

    /** The constant an arm returns, an int or null, walking only constant
     *  stores and jumps; null for anything else. */
    private static Constant returned(Body body, Unit start) {
        Map<Value, Constant> constants = new HashMap<Value, Constant>();
        Unit unit = start;
        for (int step = 0; unit != null && step < MAX_ARM; step++) {
            if (unit instanceof ReturnStmt) {
                Value op = ((ReturnStmt) unit).getOp();
                return constant(op) ? (Constant) op : constants.get(op);
            }
            if (unit instanceof GotoStmt) {
                unit = ((GotoStmt) unit).getTarget();
                continue;
            }
            if (unit instanceof AssignStmt
                    && constant(((AssignStmt) unit).getRightOp())) {
                constants.put(((AssignStmt) unit).getLeftOp(),
                        (Constant) ((AssignStmt) unit).getRightOp());
            } else if (!(unit instanceof NopStmt)) {
                return null;
            }
            unit = body.getUnits().getSuccOf(unit);
        }
        return null;
    }
}
