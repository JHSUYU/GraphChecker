package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import soot.Body;
import soot.BooleanType;
import soot.FastHierarchy;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.EqExpr;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.NeExpr;
import soot.jimple.NewExpr;
import soot.jimple.NopStmt;
import soot.jimple.NullConstant;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.SwitchStmt;
import soot.jimple.ThrowStmt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

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
 *
 * <p>A helper with no branch may return its constant by whether one call
 * threw ({@link #thrown}): solr-adhoc-09's {@code waitForCoreNodeGone}
 * returns false from {@code catch (TimeoutException)} around {@code
 * waitForState}, and true after it, so the deciders are {@code
 * waitForState}'s own branches -- an arm that throws a new {@code
 * TimeoutException} has the catch's verdict, one that returns the normal
 * path's ({@code if (!latch.await(..)) throw}, the TIMED_WAIT door's
 * decision).  Each decider states its {@code via}: the method its helper
 * is called from, past synthetic hops ({@link JvmNames#syntheticHop}), as
 * the run names a call's caller.</p>
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
        // A guard in a lambda's body: the run names its caller past the
        // lambda, which no static frame names, so its deciders state no via
        // and are forced in any call (the over-approximation).
        String method = body.getMethod().getSignature();
        return deciders(body, guard, 1,
                JvmNames.syntheticHop(method) ? "" : method);
    }

    /** {@code via}: the method a call in {@code body} is called from, as a
     *  decider states it ({@link #calleeVia}). */
    private static List<StaticScopeMap.Guard> deciders(Body body, Unit guard,
                                                       int depth,
                                                       String via) {
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
                condition instanceof EqExpr, false, depth, via);
    }

    /** The deciders of the test {@code tested ==} (or {@code !=}) {@code
     *  compared}, {@code tested} the result of one helper call; {@code
     *  nullThrows}: the test is {@code tested.equals(c)}, so an arm returning
     *  null throws there and is open. */
    private static List<StaticScopeMap.Guard> tested(Body body, Local tested,
                                                     Kept compared,
                                                     boolean equal,
                                                     boolean nullThrows,
                                                     int depth, String via) {
        return helperDeciders(body, tested, compared, equal, nullThrows,
                false, depth, via);
    }

    /** The {@code via} of the deciders in a method {@code caller} calls:
     *  {@code caller} itself, unless it is a synthetic hop, which the run
     *  never names as a caller: then the method {@code caller} was called
     *  from, {@code via}. */
    private static String calleeVia(Body caller, String via) {
        String method = caller.getMethod().getSignature();
        return JvmNames.syntheticHop(method) ? via : method;
    }

    /**
     * The deciders of the test on {@code tested}, the result of one call --
     * or, {@code tested} a {@code Boolean}'s {@code booleanValue()}, the
     * result of the call that returned that {@code Boolean}, its constant
     * arms {@code Boolean.TRUE} and {@code FALSE} read as 1 and 0 ({@code
     * boxed}): {@code if (!callable.call())}, solr-adhoc-09's
     * DeleteReplicaCmd.java:277.
     */
    private static List<StaticScopeMap.Guard> helperDeciders(
            Body body, Local tested, Kept compared, boolean equal,
            boolean nullThrows, boolean boxed, int depth, String via) {
        List<StaticScopeMap.Guard> found =
                new ArrayList<StaticScopeMap.Guard>();
        Local unboxed = boxed ? null : unboxed(body, tested);
        if (unboxed != null) {
            return helperDeciders(body, unboxed, compared, equal, nullThrows,
                    true, depth, via);
        }
        String helperVia = calleeVia(body, via);
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
            return forwarded(helperBody, compared, equal, nullThrows, boxed,
                    depth, helperVia);
        }
        for (IfStmt branch : branches) {
            Boolean taken = verdict(returned(helperBody, branch.getTarget(),
                    boxed), compared, equal, nullThrows);
            Boolean fallen = verdict(returned(helperBody,
                    helperBody.getUnits().getSuccOf(branch), boxed), compared,
                    equal, nullThrows);
            if (taken == null && fallen == null
                    || taken != null && taken.equals(fallen)) {
                continue;
            }
            List<StaticScopeMap.Guard> nested = depth < MAX_DEPTH
                    ? deciders(helperBody, branch, depth + 1, helperVia)
                    : Collections.<StaticScopeMap.Guard>emptyList();
            String site = SiteId.of(helper.getSignature(),
                    SiteControlDependence.originalIndex(helperBody, branch));
            found.add(new StaticScopeMap.Guard(site, true, taken, nested,
                    helperVia));
            found.add(new StaticScopeMap.Guard(site, false, fallen, nested,
                    helperVia));
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
                                                        boolean nullThrows,
                                                        boolean boxed,
                                                        int depth,
                                                        String via) {
        List<StaticScopeMap.Guard> found = thrown(helperBody, compared,
                equal, nullThrows, boxed, depth, via);
        if (!found.isEmpty()) return found;
        InvokeExpr equals = null;
        Local returned = null;
        for (Unit unit : helperBody.getUnits()) {
            if (!(unit instanceof ReturnStmt)) continue;
            Value op = ((ReturnStmt) unit).getOp();
            InvokeExpr call = op instanceof Local
                    ? definingCall(helperBody, (Local) op) : null;
            if (equals != null || returned != null || call == null) {
                return found;
            }
            if (identityEquals(call)) {
                equals = call;
            } else {
                returned = (Local) op;
            }
        }
        // A forwarder: it returns what one call returned (Soot's desugared
        // lambda's call() running the lambda's body, lambda$m$N), so the
        // deciders are that call's, one helper deeper.
        // A synthetic forwarder (the lambda class's call()) is no helper
        // level, as it is no caller for via: the lambda's body is.
        if (returned != null) {
            boolean hop = JvmNames.syntheticHop(
                    helperBody.getMethod().getSignature());
            return hop || depth < MAX_DEPTH ? helperDeciders(helperBody,
                    returned, compared, equal, nullThrows, boxed,
                    hop ? depth : depth + 1, via) : found;
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
                constant, true, tested == base, depth, via)) {
            Boolean verdict = inner.verdict() == null ? null
                    : verdict(Kept.ofInt(inner.verdict() ? 1 : 0), compared,
                    equal, false);
            found.add(new StaticScopeMap.Guard(inner.siteId(),
                    inner.outcome(), verdict, inner.deciders(), inner.via()));
        }
        return found;
    }

    /**
     * A branchless helper whose constant says whether one call threw: a trap
     * catching a checked exception {@code E} -- never {@code Exception},
     * {@code Throwable} or a {@code RuntimeException}, which code anywhere
     * below could throw -- whose handler runs straight to a constant return,
     * around exactly one call {@code g} that declares {@code E} (or a
     * subtype or supertype of it), the path after {@code g} running straight
     * to another constant.  The deciders are {@code g}'s own branches: an arm
     * that runs straight to a throw of a {@code new E'} assignable to
     * {@code E} that no handler of {@code g} keeps (a {@code finally}'s
     * rethrow lets it go) has the handler's verdict, an arm that runs
     * straight to {@code g}'s return the normal path's, any other arm is
     * open.  Exact only where {@code E} comes from {@code g}'s own throws:
     * a {@code g} any of whose calls declares {@code E} or a subtype decides
     * nothing; one level of exception only, and {@code g} is a helper deeper
     * ({@link #MAX_DEPTH}).
     */
    private static List<StaticScopeMap.Guard> thrown(Body helperBody,
                                                     Kept compared,
                                                     boolean equal,
                                                     boolean nullThrows,
                                                     boolean boxed,
                                                     int depth, String via) {
        List<StaticScopeMap.Guard> found =
                new ArrayList<StaticScopeMap.Guard>();
        if (depth >= MAX_DEPTH) return found;
        // Each handler once, in the exception table's order: the traps of
        // one try range javac split share their handler.
        Set<Unit> handlers = new LinkedHashSet<Unit>();
        for (Trap trap : helperBody.getTraps()) {
            SootClass caught = trap.getException();
            Unit catching = trap.getHandlerUnit();
            if (!checkedNarrow(caught) || !handlers.add(catching)) continue;
            Unit handler = catching instanceof IdentityStmt
                    ? helperBody.getUnits().getSuccOf(catching) : catching;
            Boolean onThrow = verdict(returned(helperBody, handler, boxed),
                    compared, equal, nullThrows);
            Unit call = guardedCall(helperBody, catching, caught);
            Boolean onReturn = call == null ? null : verdict(returned(
                    helperBody, helperBody.getUnits().getSuccOf(call), boxed),
                    compared, equal, nullThrows);
            if (onThrow == null || onReturn == null
                    || onThrow.equals(onReturn)) {
                continue;
            }
            // A throw is this handler's only where the JVM picks it: the
            // first trap covering the call that catches what was thrown
            // (catch (SubE) before catch (E) takes a new SubE).
            Predicate<SootClass> caughtHere = thrown -> {
                Trap first = firstCatching(helperBody, call, thrown);
                return first != null && first.getHandlerUnit() == catching;
            };
            SootMethod g = onlyCall(helperBody,
                    ((Stmt) call).getInvokeExpr());
            Body gBody = g == null || !g.getDeclaringClass()
                    .isApplicationClass() ? null
                    : CausynthStaticFacts.activeBody(g);
            if (gBody == null || anyCallMayThrow(gBody, caught)) continue;
            String gVia = calleeVia(helperBody, via);
            List<IfStmt> branches = new ArrayList<IfStmt>();
            for (Unit unit : gBody.getUnits()) {
                if (unit instanceof SwitchStmt) return found;
                if (unit instanceof IfStmt) branches.add((IfStmt) unit);
            }
            for (IfStmt branch : branches) {
                Boolean taken = exit(gBody, branch.getTarget(), caughtHere,
                        onThrow, onReturn);
                Boolean fallen = exit(gBody,
                        gBody.getUnits().getSuccOf(branch), caughtHere,
                        onThrow, onReturn);
                if (taken == null && fallen == null
                        || taken != null && taken.equals(fallen)) {
                    continue;
                }
                List<StaticScopeMap.Guard> nested = depth + 1 < MAX_DEPTH
                        ? deciders(gBody, branch, depth + 2, gVia)
                        : Collections.<StaticScopeMap.Guard>emptyList();
                String site = SiteId.of(g.getSignature(),
                        SiteControlDependence.originalIndex(gBody, branch));
                found.add(new StaticScopeMap.Guard(site, true, taken, nested,
                        gVia));
                found.add(new StaticScopeMap.Guard(site, false, fallen,
                        nested, gVia));
            }
            return found;
        }
        return found;
    }

    /** A checked exception narrower than {@code Exception}: what only a
     *  declared throw can raise. */
    private static boolean checkedNarrow(SootClass caught) {
        if (caught == null || "java.lang.Exception".equals(caught.getName())
                || "java.lang.Throwable".equals(caught.getName())) {
            return false;
        }
        try {
            return FaultPropagation.checked(caught.getType());
        } catch (RuntimeException unresolved) {
            // A phantom hierarchy: what it catches is unknown.
            return false;
        }
    }

    /** The one unit in the ranges of the traps that share {@code handler}
     *  whose call may throw {@code caught}, or null for none or several. */
    private static Unit guardedCall(Body body, Unit handler,
                                    SootClass caught) {
        Unit found = null;
        for (Trap trap : body.getTraps()) {
            if (trap.getHandlerUnit() != handler) continue;
            for (Unit at = trap.getBeginUnit(); at != null
                    && at != trap.getEndUnit();
                 at = body.getUnits().getSuccOf(at)) {
                if (!(at instanceof Stmt)
                        || !((Stmt) at).containsInvokeExpr()
                        || !mayThrow(((Stmt) at).getInvokeExpr(), caught)
                        || at == found) {
                    continue;
                }
                if (found != null) return null;
                found = at;
            }
        }
        return found;
    }

    /** The first trap of {@code body}, in its exception table's order,
     *  covering {@code call} and catching {@code thrown}: the one the JVM
     *  runs; null for none. */
    private static Trap firstCatching(Body body, Unit call,
                                      SootClass thrown) {
        for (Trap trap : body.getTraps()) {
            if (FaultPropagation.covers(body, trap, call)
                    && assignable(thrown, trap.getException())) {
                return trap;
            }
        }
        return null;
    }

    /** Whether a call's method declares an exception {@code caught} or one
     *  of its subtypes would be; an unresolved method may throw anything. */
    private static boolean mayThrow(InvokeExpr call, SootClass caught) {
        SootMethod method;
        try {
            method = call.getMethod();
        } catch (RuntimeException unresolved) {
            return true;
        }
        if (method.isPhantom() || method.getExceptionsUnsafe() == null) {
            return method.isPhantom();
        }
        FastHierarchy hierarchy = Scene.v().getOrMakeFastHierarchy();
        RefType type = caught.getType();
        for (SootClass declared : method.getExceptionsUnsafe()) {
            if (hierarchy.canStoreType(type, declared.getType())
                    || hierarchy.canStoreType(declared.getType(), type)) {
                return true;
            }
        }
        return false;
    }

    /** Whether any call in {@code body} may throw {@code caught}. */
    private static boolean anyCallMayThrow(Body body, SootClass caught) {
        for (Unit unit : body.getUnits()) {
            if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()
                    && mayThrow(((Stmt) unit).getInvokeExpr(), caught)) {
                return true;
            }
        }
        return false;
    }

    /**
     * How an arm of {@code g} leaves it, as the helper's guard takes it: a
     * throw of a {@code new E'} the arm made, not kept by a handler of
     * {@code g}, that the helper's handler at hand catches first ({@code
     * caughtHere}) is {@code onThrow}; a return is {@code onReturn}; null
     * (open) for anything else.  The arm runs straight -- stores to locals,
     * calls, jumps, a branch both of whose arms leave alike -- at most
     * {@link #MAX_ARM} units.
     */
    private static Boolean exit(Body g, Unit start,
                                Predicate<SootClass> caughtHere,
                                Boolean onThrow, Boolean onReturn) {
        return exit(g, start, caughtHere, onThrow, onReturn,
                new HashMap<Value, SootClass>(), MAX_ARM);
    }

    private static Boolean exit(Body g, Unit start,
                                Predicate<SootClass> caughtHere,
                                Boolean onThrow, Boolean onReturn,
                                Map<Value, SootClass> made, int budget) {
        Unit unit = start;
        for (int step = 0; unit != null && step < budget; step++) {
            if (unit instanceof ReturnStmt || unit instanceof ReturnVoidStmt) {
                return onReturn;
            }
            if (unit instanceof ThrowStmt) {
                SootClass thrown = made.get(((ThrowStmt) unit).getOp());
                return thrown != null && caughtHere.test(thrown)
                        && escapes(g, unit, thrown) ? onThrow : null;
            }
            if (unit instanceof GotoStmt) {
                unit = ((GotoStmt) unit).getTarget();
                continue;
            }
            if (unit instanceof IfStmt) {
                Boolean taken = exit(g, ((IfStmt) unit).getTarget(),
                        caughtHere, onThrow, onReturn,
                        new HashMap<Value, SootClass>(made),
                        budget - step - 1);
                Boolean fallen = exit(g, g.getUnits().getSuccOf(unit),
                        caughtHere, onThrow, onReturn,
                        new HashMap<Value, SootClass>(made),
                        budget - step - 1);
                return taken != null && taken.equals(fallen) ? taken : null;
            }
            if (unit instanceof AssignStmt
                    && ((AssignStmt) unit).getLeftOp() instanceof Local) {
                Value right = ((AssignStmt) unit).getRightOp();
                if (right instanceof NewExpr) {
                    made.put(((AssignStmt) unit).getLeftOp(),
                            ((NewExpr) right).getBaseType().getSootClass());
                } else {
                    made.remove(((AssignStmt) unit).getLeftOp());
                }
            } else if (!(unit instanceof InvokeStmt)
                    && !(unit instanceof NopStmt)) {
                return null;
            }
            unit = g.getUnits().getSuccOf(unit);
        }
        return null;
    }

    private static boolean assignable(SootClass thrown, SootClass caught) {
        try {
            return Scene.v().getOrMakeFastHierarchy().canStoreType(
                    thrown.getType(), caught.getType());
        } catch (RuntimeException unresolved) {
            return false;
        }
    }

    /** Whether a throw of {@code thrown} at {@code at} leaves {@code g}: no
     *  trap covering it catches it, but one whose handler runs straight to
     *  rethrowing what it caught (javac's {@code finally}). */
    private static boolean escapes(Body g, Unit at, SootClass thrown) {
        for (Trap trap : g.getTraps()) {
            if (!FaultPropagation.covers(g, trap, at)
                    || !assignable(thrown, trap.getException())) {
                continue;
            }
            if (!rethrows(g, trap.getHandlerUnit())) return false;
        }
        return true;
    }

    /** Whether a handler runs straight -- calls, local stores, a branch
     *  both of whose arms do (a {@code finally}'s {@code if
     *  (log.isDebugEnabled())}) -- to throwing the exception it caught. */
    private static boolean rethrows(Body g, Unit handler) {
        return handler instanceof IdentityStmt && rethrows(g,
                g.getUnits().getSuccOf(handler),
                ((IdentityStmt) handler).getLeftOp(), MAX_ARM);
    }

    private static boolean rethrows(Body g, Unit start, Value caught,
                                    int budget) {
        Unit unit = start;
        for (int step = 0; unit != null && step < budget; step++) {
            if (unit instanceof ThrowStmt) {
                return ((ThrowStmt) unit).getOp() == caught;
            }
            if (unit instanceof IfStmt) {
                return rethrows(g, ((IfStmt) unit).getTarget(), caught,
                        budget - step - 1) && rethrows(g,
                        g.getUnits().getSuccOf(unit), caught,
                        budget - step - 1);
            }
            if (unit instanceof AssignStmt
                    && ((AssignStmt) unit).getLeftOp() instanceof Local
                    && ((AssignStmt) unit).getLeftOp() != caught
                    || unit instanceof InvokeStmt
                    || unit instanceof NopStmt) {
                unit = g.getUnits().getSuccOf(unit);
                continue;
            }
            if (unit instanceof GotoStmt) {
                unit = ((GotoStmt) unit).getTarget();
                continue;
            }
            return false;
        }
        return false;
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
        return onlyCall(body, definingCall(body, local));
    }

    /** The one method {@code call}, made in {@code body}, can run, or
     *  null ({@link #onlyCallDefining}). */
    private static SootMethod onlyCall(Body body, InvokeExpr call) {
        if (call == null) return null;
        // An interface or virtual call on an object the body created: the
        // method its class runs ({@link CreatedFrom}), a lambda's included.
        if (call instanceof InstanceInvokeExpr
                && ((InstanceInvokeExpr) call).getBase() instanceof Local) {
            Set<SootClass> created = CreatedFrom.classes(body.getUnits(),
                    (Local) ((InstanceInvokeExpr) call).getBase());
            if (created.size() == 1) {
                SootMethod runs = CreatedFrom.implementation(
                        created.iterator().next(),
                        call.getMethodRef().getSubSignature().getString());
                if (runs != null) return runs;
            }
        }
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

    /**
     * The constant an arm returns, walking constant stores, jumps, calls
     * that store nothing, and a branch both of whose arms return the same
     * constant (javac's inlined {@code finally { if (onComplete != null)
     * onComplete.run(); }} before each return); null for anything else.
     * {@code boxed}: {@code Boolean.TRUE} and {@code FALSE} are 1 and 0.
     */
    private static Kept returned(Body body, Unit start, boolean boxed) {
        return returned(body, start, new HashMap<Value, Kept>(), boxed,
                MAX_ARM);
    }

    private static Kept returned(Body body, Unit start,
                                 Map<Value, Kept> constants, boolean boxed,
                                 int budget) {
        Unit unit = start;
        for (int step = 0; unit != null && step < budget; step++) {
            if (unit instanceof ReturnStmt) {
                Value op = ((ReturnStmt) unit).getOp();
                Kept direct = constant(op);
                return direct != null ? direct : constants.get(op);
            }
            if (unit instanceof GotoStmt) {
                unit = ((GotoStmt) unit).getTarget();
                continue;
            }
            if (unit instanceof IfStmt) {
                Kept taken = returned(body, ((IfStmt) unit).getTarget(),
                        new HashMap<Value, Kept>(constants), boxed,
                        budget - step - 1);
                Kept fallen = returned(body, body.getUnits().getSuccOf(unit),
                        new HashMap<Value, Kept>(constants), boxed,
                        budget - step - 1);
                return taken != null && taken.equals(fallen) ? taken : null;
            }
            Kept stored = unit instanceof AssignStmt
                    ? constantOrEnum(((AssignStmt) unit).getRightOp(), boxed)
                    : null;
            if (stored != null) {
                constants.put(((AssignStmt) unit).getLeftOp(), stored);
            } else if (!(unit instanceof NopStmt)
                    && !(unit instanceof InvokeStmt)) {
                return null;
            }
            unit = body.getUnits().getSuccOf(unit);
        }
        return null;
    }

    /** {@code Boolean.TRUE} or {@code FALSE}, or {@code Boolean.valueOf}
     *  of a constant (javac's boxing of {@code return true;}), as the int a
     *  {@code booleanValue()} unboxes it to; else null. */
    private static Kept booleanConstant(Value value) {
        if (value instanceof StaticInvokeExpr) {
            InvokeExpr call = (InvokeExpr) value;
            return "java.lang.Boolean".equals(call.getMethodRef()
                    .getDeclaringClass().getName())
                    && "valueOf".equals(call.getMethodRef().getName())
                    && call.getArgCount() == 1
                    && call.getArg(0) instanceof IntConstant
                    && call.getMethodRef().getParameterType(0)
                    instanceof BooleanType
                    ? Kept.ofInt(((IntConstant) call.getArg(0)).value) : null;
        }
        if (!(value instanceof StaticFieldRef)) return null;
        SootFieldRef ref = ((StaticFieldRef) value).getFieldRef();
        if (!"java.lang.Boolean".equals(ref.declaringClass().getName())) {
            return null;
        }
        return "TRUE".equals(ref.name()) ? Kept.ofInt(1)
                : "FALSE".equals(ref.name()) ? Kept.ofInt(0) : null;
    }

    /** The {@code Boolean} a local's one definition unboxes, {@code
     *  b.booleanValue()} -- b's cast, {@code (Boolean) o}, passed to o --
     *  or null. */
    private static Local unboxed(Body body, Local local) {
        InvokeExpr call = definingCall(body, local);
        if (!(call instanceof InstanceInvokeExpr)
                || !"booleanValue".equals(call.getMethodRef().getName())
                || !"java.lang.Boolean".equals(call.getMethodRef()
                .getDeclaringClass().getName())
                || !(((InstanceInvokeExpr) call).getBase() instanceof Local)) {
            return null;
        }
        Local boxed = (Local) ((InstanceInvokeExpr) call).getBase();
        Value cast = definition(body, boxed);
        return cast instanceof CastExpr && ((CastExpr) cast).getOp()
                instanceof Local ? (Local) ((CastExpr) cast).getOp() : boxed;
    }

    /** The right side of the body's one assignment of {@code local}, or
     *  null. */
    private static Value definition(Body body, Local local) {
        Value found = null;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)
                    || ((AssignStmt) unit).getLeftOp() != local) {
                continue;
            }
            if (found != null) return null;
            found = ((AssignStmt) unit).getRightOp();
        }
        return found;
    }

    private static Kept constantOrEnum(Value value, boolean boxed) {
        Kept direct = constant(value);
        if (direct != null) return direct;
        Kept unboxed = boxed ? booleanConstant(value) : null;
        return unboxed != null ? unboxed : enumConstant(value);
    }
}
