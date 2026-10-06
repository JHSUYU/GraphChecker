package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import soot.Body;
import soot.BooleanType;
import soot.Local;
import soot.Modifier;
import soot.Scene;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.EqExpr;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.NeExpr;
import soot.jimple.NopStmt;
import soot.jimple.NullConstant;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
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
 * outcome on the other; a lookup returns null where its loop ends; {@code
 * getBlockUCState} returns the enum constant {@code COMPLETE} where {@code
 * uc} is null and the feature's state otherwise.  The VM tracks the
 * helper's comparisons but not the constant it returns, so the guard
 * decides concretely, and the helper branch whose arm ran to the return
 * decides it.
 *
 * <p>A constant is an int, null, or an enum constant (a static field an
 * enum declares for one of its values, {@link Modifier#ENUM}).  The
 * deciders of a guard {@code v ==/!= c} -- {@code c} such a constant,
 * {@code v} the result of one call of an application helper -- are the
 * helper's branches with an arm that runs straight (constant stores, jumps,
 * at most {@link #MAX_ARM} units) to a return of a constant of {@code c}'s
 * kind, each arm stated with its {@code verdict}: whether the guard's
 * condition holds when that arm runs, null for an OPEN arm, one that runs
 * on to a value no constant states.  A branch whose two arms are open, or
 * whose two constant arms the guard takes alike, decides nothing.  A
 * helper with no branch that returns {@code h2().equals(c)} -- an enum's
 * {@code equals} is identity -- is the guard {@code h2() == c}, its
 * deciders' verdicts read through the boolean it returns
 * ({@code isComplete()}).  A decider that is itself such a guard on a
 * nested helper's return carries that helper's deciders, {@link #MAX_DEPTH}
 * helpers deep.  A helper with a switch has none.  At run time the guard's
 * condition is {@code ite(decider, the arm's verdict, the other arm's)},
 * an open arm's being the condition the run itself stated when it took it
 * ({@code runtime.RowPublication#decided}).</p>
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
        if (!(guard instanceof IfStmt)) {
            return Collections.<StaticScopeMap.Guard>emptyList();
        }
        Value condition = ((IfStmt) guard).getCondition();
        if (!(condition instanceof EqExpr || condition instanceof NeExpr)) {
            return Collections.<StaticScopeMap.Guard>emptyList();
        }
        BinopExpr test = (BinopExpr) condition;
        Kept first = kept(body, test.getOp1());
        Value tested = first == null ? test.getOp1() : test.getOp2();
        Kept compared = first == null ? kept(body, test.getOp2()) : first;
        if (!(tested instanceof Local) || compared == null) {
            return Collections.<StaticScopeMap.Guard>emptyList();
        }
        return tested(body, (Local) tested, compared,
                condition instanceof EqExpr, false, depth);
    }

    /** The deciders of the test {@code tested ==} (or {@code !=}) {@code
     *  compared}, {@code tested} the result of one helper call; {@code
     *  nullThrows}: the test is {@code tested.equals(c)}, so an arm returning
     *  null throws there and is open. */
    private static List<StaticScopeMap.Guard> tested(Body body, Local tested,
                                                     Kept compared,
                                                     boolean equal,
                                                     boolean nullThrows,
                                                     int depth) {
        List<StaticScopeMap.Guard> found =
                new ArrayList<StaticScopeMap.Guard>();
        SootMethod helper = onlyCallDefining(body, tested);
        Body helperBody = helper == null
                || !helper.getDeclaringClass().isApplicationClass() ? null
                : CausynthStaticFacts.activeBody(helper);
        if (helperBody == null) return found;
        List<IfStmt> branches = new ArrayList<IfStmt>();
        for (Unit unit : helperBody.getUnits()) {
            if (unit instanceof SwitchStmt) return found;
            if (unit instanceof IfStmt) branches.add((IfStmt) unit);
        }
        if (branches.isEmpty()) {
            return forwarded(helperBody, compared, equal, depth);
        }
        for (IfStmt branch : branches) {
            Boolean taken = verdict(returned(helperBody, branch.getTarget()),
                    compared, equal, nullThrows);
            Boolean fallen = verdict(returned(helperBody,
                    helperBody.getUnits().getSuccOf(branch)), compared, equal,
                    nullThrows);
            if (taken == null && fallen == null
                    || taken != null && taken.equals(fallen)) {
                continue;
            }
            List<StaticScopeMap.Guard> nested = depth < MAX_DEPTH
                    ? deciders(helperBody, branch, depth + 1)
                    : Collections.<StaticScopeMap.Guard>emptyList();
            String site = SiteId.of(helper.getSignature(),
                    SiteControlDependence.originalIndex(helperBody, branch));
            found.add(new StaticScopeMap.Guard(site, true, taken, nested));
            found.add(new StaticScopeMap.Guard(site, false, fallen, nested));
        }
        return found;
    }

    /**
     * A helper with no branch whose return is {@code h2().equals(c)}, {@code
     * c} an enum constant: the deciders of {@code h2() == c}, each verdict
     * read through the boolean the helper returns to the test {@code
     * returned ==} (or {@code !=}) {@code compared}.
     */
    private static List<StaticScopeMap.Guard> forwarded(Body helperBody,
                                                        Kept compared,
                                                        boolean equal,
                                                        int depth) {
        List<StaticScopeMap.Guard> found =
                new ArrayList<StaticScopeMap.Guard>();
        InvokeExpr equals = null;
        for (Unit unit : helperBody.getUnits()) {
            if (!(unit instanceof ReturnStmt)) continue;
            Value op = ((ReturnStmt) unit).getOp();
            InvokeExpr call = op instanceof Local
                    ? definingCall(helperBody, (Local) op) : null;
            if (equals != null || call == null || !identityEquals(call)) {
                return found;
            }
            equals = call;
        }
        if (equals == null) return found;
        Value base = ((InstanceInvokeExpr) equals).getBase();
        Value argument = equals.getArg(0);
        Kept constant = kept(helperBody, argument);
        Value tested = constant == null ? argument : base;
        if (constant == null) constant = kept(helperBody, base);
        if (constant == null || constant.kind != Kept.Kind.ENUM
                || !(tested instanceof Local)) {
            return found;
        }
        // h2().equals(c) throws where h2() returned null; c.equals(h2()) is
        // false there.
        for (StaticScopeMap.Guard inner : tested(helperBody, (Local) tested,
                constant, true, tested == base, depth)) {
            Boolean verdict = inner.verdict() == null ? null
                    : verdict(Kept.ofInt(inner.verdict() ? 1 : 0), compared,
                    equal, false);
            found.add(new StaticScopeMap.Guard(inner.siteId(),
                    inner.outcome(), verdict, inner.deciders()));
        }
        return found;
    }

    /** Whether a call is {@code equals(Object)} answering a boolean: on an
     *  enum constant, identity. */
    private static boolean identityEquals(InvokeExpr call) {
        return call instanceof InstanceInvokeExpr
                && "equals".equals(call.getMethodRef().getName())
                && call.getArgCount() == 1
                && call.getMethodRef().getReturnType()
                instanceof BooleanType;
    }

    /** Whether the guard's condition holds when an arm returns {@code
     *  returned}; null for no constant, one of another kind, or a null that
     *  throws ({@code nullThrows}). */
    private static Boolean verdict(Kept returned, Kept compared,
                                   boolean equal, boolean nullThrows) {
        if (returned == null || returned.reference() != compared.reference()
                || nullThrows && returned.kind == Kept.Kind.NULL) {
            return null;
        }
        return Boolean.valueOf(equal == returned.equals(compared));
    }

    /** A constant: an int, null, or an enum constant. */
    private static final class Kept {
        enum Kind { INT, NULL, ENUM }

        final Kind kind;
        final String value;

        private Kept(Kind kind, String value) {
            this.kind = kind;
            this.value = value;
        }

        static Kept ofInt(int value) {
            return new Kept(Kind.INT, String.valueOf(value));
        }

        boolean reference() {
            return kind != Kind.INT;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Kept && ((Kept) other).kind == kind
                    && ((Kept) other).value.equals(value);
        }

        @Override
        public int hashCode() {
            return kind.hashCode() * 31 + value.hashCode();
        }
    }

    /** The constant a value is: itself, or a local the body assigns once,
     *  from an enum constant; else null. */
    private static Kept kept(Body body, Value value) {
        Kept direct = constant(value);
        if (direct != null || !(value instanceof Local)) return direct;
        Kept found = null;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)
                    || ((AssignStmt) unit).getLeftOp() != value) {
                continue;
            }
            if (found != null) return null;
            found = enumConstant(((AssignStmt) unit).getRightOp());
            if (found == null) return null;
        }
        return found;
    }

    /** An int or null constant; else null. */
    private static Kept constant(Value value) {
        if (value instanceof IntConstant) {
            return Kept.ofInt(((IntConstant) value).value);
        }
        return value instanceof NullConstant ? new Kept(Kept.Kind.NULL, "")
                : null;
    }

    /** A read of an enum constant -- a static field its enum declares for
     *  one of its values -- as a constant; else null. */
    private static Kept enumConstant(Value value) {
        if (!(value instanceof StaticFieldRef)) return null;
        SootFieldRef ref = ((StaticFieldRef) value).getFieldRef();
        SootField field;
        try {
            field = ref.resolve();
        } catch (RuntimeException unresolved) {
            // A phantom field: what it holds is unknown.
            return null;
        }
        return field != null && field.isStatic()
                && (field.getModifiers() & Modifier.ENUM) != 0
                ? new Kept(Kept.Kind.ENUM, field.getSignature()) : null;
    }

    /** The one method the local's one defining call can run -- a static,
     *  private or final one, or one no loaded class overrides -- or null. */
    private static SootMethod onlyCallDefining(Body body, Local local) {
        InvokeExpr call = definingCall(body, local);
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

    /** The call the body's one assignment of {@code local} makes, or null. */
    private static InvokeExpr definingCall(Body body, Local local) {
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
        return call;
    }

    /** The constant an arm returns, walking only constant stores and
     *  jumps; null for anything else. */
    private static Kept returned(Body body, Unit start) {
        Map<Value, Kept> constants = new HashMap<Value, Kept>();
        Unit unit = start;
        for (int step = 0; unit != null && step < MAX_ARM; step++) {
            if (unit instanceof ReturnStmt) {
                Value op = ((ReturnStmt) unit).getOp();
                Kept direct = constant(op);
                return direct != null ? direct : constants.get(op);
            }
            if (unit instanceof GotoStmt) {
                unit = ((GotoStmt) unit).getTarget();
                continue;
            }
            Kept stored = unit instanceof AssignStmt
                    ? constantOrEnum(((AssignStmt) unit).getRightOp()) : null;
            if (stored != null) {
                constants.put(((AssignStmt) unit).getLeftOp(), stored);
            } else if (!(unit instanceof NopStmt)) {
                return null;
            }
            unit = body.getUnits().getSuccOf(unit);
        }
        return null;
    }

    private static Kept constantOrEnum(Value value) {
        Kept direct = constant(value);
        return direct != null ? direct : enumConstant(value);
    }
}
