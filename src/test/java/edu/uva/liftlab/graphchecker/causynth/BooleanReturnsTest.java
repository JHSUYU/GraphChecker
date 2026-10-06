package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.After;
import org.junit.Test;
import soot.Body;
import soot.BooleanType;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.NullConstant;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * The deciders of a guard on a helper's constant return (SYMBOL-SCOPE §3):
 * both arms of every helper branch with an arm that runs straight to a
 * constant return of the guard's kind -- an int, null or an enum constant
 * -- each with its verdict (open where it runs on), and the deciders of the
 * nested helper return it tests.  hdfs-adhoc-40's {@code
 * !isSufficientlyReplicated(b)}: the helper returns true on one arm of its
 * test of {@code hasMinStorage}'s return and a comparison's outcome on the
 * other.  hdfs-adhoc-15's {@code isComplete()}: {@code
 * getBlockUCState().equals(COMPLETE)}, which returns {@code COMPLETE} where
 * {@code uc} is null and the feature's state otherwise.
 */
public class BooleanReturnsTest {
    private static final String OWNER = "a.Helpers";

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aGuardOnAHelpersConstantReturnIsDecidedByTheArmsThatRanToIt() {
        SootClass owner = new SootClass(OWNER, Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootClass library = new SootClass("j.Lib", Modifier.PUBLIC);
        Scene.v().addClass(library);
        library.setLibraryClass();

        SootClass state = new SootClass("a.State", Modifier.PUBLIC
                | Modifier.ENUM);
        Scene.v().addClass(state);
        state.setApplicationClass();
        SootClass object = new SootClass("java.lang.Object",
                Modifier.PUBLIC);
        Scene.v().addClass(object);
        object.setLibraryClass();
        for (String value : new String[]{"COMPLETE", "COMMITTED"}) {
            state.addField(new SootField(value, state.getType(),
                    Modifier.PUBLIC | Modifier.STATIC | Modifier.FINAL
                            | Modifier.ENUM));
        }

        SootMethod min = twoConstants(owner, "hasMinStorage", 1, 0);
        SootMethod alike = twoConstants(owner, "alike", 1, 1);
        SootMethod outside = twoConstants(library, "outside", 1, 0);
        SootMethod sufficient = sufficient(owner, min);
        SootMethod lookup = lookup(owner);
        SootMethod switched = switched(owner);
        SootMethod uc = ucState(owner, state, min);
        SootMethod complete = complete(owner, state, uc, object);

        String suff = sig(sufficient);
        String has = sig(min);
        String hasArms = "[" + has + "#u1=true:true[], " + has
                + "#u1=false:false[]]";
        // getState tests min's return with != 0: the verdicts turn.
        String notHasArms = "[" + has + "#u1=true:false[], " + has
                + "#u1=false:true[]]";
        Object[][] rows = {
            {"one branch, two constant arms: both arms", min, null, true,
                Arrays.asList(has + "#u1=true:true[]",
                        has + "#u1=false:false[]")},
            {"a branch of a nested helper's return carries its deciders, a"
                    + " comparison both of its arms; the arm that runs on to"
                    + " the comparison is open", sufficient, null, true,
                Arrays.asList(suff + "#u2=true:open" + hasArms,
                    suff + "#u2=false:false" + hasArms,
                    suff + "#u4=true:true[]", suff + "#u4=false:false[]")},
            {"a null return decides a null test, the other arm open",
                lookup, NullConstant.v(), true,
                Arrays.asList(sig(lookup) + "#u1=true:open[]",
                        sig(lookup) + "#u1=false:true[]")},
            {"an enum constant decides a test of another, the arm that"
                    + " reads the state open", uc, "COMMITTED", true,
                Arrays.asList(sig(uc) + "#u2=true:open" + notHasArms,
                        sig(uc) + "#u2=false:false" + notHasArms)},
            {"a helper returning h2().equals(c) is the guard h2() == c, its"
                    + " verdicts read through what it returns", complete,
                null, false,
                Arrays.asList(sig(uc) + "#u2=true:open" + notHasArms,
                        sig(uc) + "#u2=false:true" + notHasArms)},
            {"two arms the guard takes alike decide nothing", alike, null,
                true, Collections.emptyList()},
            {"a helper with a switch has none", switched, null, true,
                Collections.emptyList()},
            {"a library helper's branches are no application's",
                outside, null, true, Collections.emptyList()},
        };
        for (Object[] row : rows) {
            Object compared = row[2];
            Body caller = caller(owner, (SootMethod) row[1],
                    compared instanceof String ? Jimple.v().newStaticFieldRef(
                            state.getFieldByName((String) compared).makeRef())
                            : (Value) compared, (Boolean) row[3]);
            Unit guard = null;
            for (Unit unit : caller.getUnits()) {
                if (unit instanceof soot.jimple.IfStmt) guard = unit;
            }
            List<StaticScopeMap.Guard> found =
                    BooleanReturns.deciders(caller, guard);
            assertEquals((String) row[0], row[4], render(found));
            // The plan states them as the map does, verdicts included.
            assertEquals((String) row[0], row[4], render(
                    StaticScopeMap.guardsOf(StaticScopeMap.guardsJson(found))));
        }
    }

    private static List<String> render(List<StaticScopeMap.Guard> guards) {
        List<String> rendered = new ArrayList<String>();
        for (StaticScopeMap.Guard guard : guards) {
            rendered.add(guard + ":" + (guard.verdict() == null ? "open"
                    : guard.verdict()) + render(guard.deciders()));
        }
        return rendered;
    }

    private static String sig(SootMethod method) {
        return method.getSignature();
    }

    /** {@code if (h(i0) == c) return} (or {@code !=}): the guard, c 0,
     *  {@code null} or an enum constant read into a local first. */
    private static Body caller(SootClass owner, SootMethod helper,
                               Value compared, boolean equal) {
        SootMethod method = method(owner, "caller" + owner.getMethodCount(),
                soot.VoidType.v());
        Body body = method.getActiveBody();
        Local result = local(body, "$r", helper.getReturnType());
        Unit end = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newAssignStmt(result,
                Jimple.v().newStaticInvokeExpr(helper.makeRef(),
                        body.getParameterLocal(0))));
        Value against = compared == null ? IntConstant.v(0) : compared;
        if (compared instanceof soot.jimple.StaticFieldRef) {
            against = local(body, "$c", compared.getType());
            body.getUnits().add(Jimple.v().newAssignStmt(against, compared));
        }
        body.getUnits().add(Jimple.v().newIfStmt(equal
                ? Jimple.v().newEqExpr(result, against)
                : Jimple.v().newNeExpr(result, against), end));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(helper.makeRef(),
                        IntConstant.v(1))));
        body.getUnits().add(end);
        return body;
    }

    /** {@code if (i0 <= 0) return b; return a;} */
    private static SootMethod twoConstants(SootClass owner, String name,
                                           int a, int b) {
        SootMethod method = method(owner, name, BooleanType.v());
        Body body = method.getActiveBody();
        Unit low = Jimple.v().newReturnStmt(IntConstant.v(b));
        body.getUnits().add(Jimple.v().newIfStmt(Jimple.v().newLeExpr(
                body.getParameterLocal(0), IntConstant.v(0)), low));
        body.getUnits().add(Jimple.v().newReturnStmt(IntConstant.v(a)));
        body.getUnits().add(low);
        return method;
    }

    /** {@code if (min(i0)) return true; return i0 >= 5;} as javac emits it. */
    private static SootMethod sufficient(SootClass owner, SootMethod min) {
        SootMethod method = method(owner, "isSufficientlyReplicated",
                BooleanType.v());
        Body body = method.getActiveBody();
        Local has = local(body, "$z0", BooleanType.v());
        Local outcome = local(body, "$z1", BooleanType.v());
        Local live = body.getParameterLocal(0);
        Unit compare = Jimple.v().newIfStmt(Jimple.v().newLtExpr(live,
                IntConstant.v(5)), Jimple.v().newNopStmt());
        Unit low = Jimple.v().newAssignStmt(outcome, IntConstant.v(0));
        Unit done = Jimple.v().newReturnStmt(outcome);
        ((soot.jimple.IfStmt) compare).setTarget(low);
        body.getUnits().add(Jimple.v().newAssignStmt(has,
                Jimple.v().newStaticInvokeExpr(min.makeRef(), live)));
        body.getUnits().add(Jimple.v().newIfStmt(Jimple.v().newEqExpr(has,
                IntConstant.v(0)), compare));
        body.getUnits().add(Jimple.v().newReturnStmt(IntConstant.v(1)));
        body.getUnits().add(compare);
        body.getUnits().add(Jimple.v().newAssignStmt(outcome,
                IntConstant.v(1)));
        body.getUnits().add(Jimple.v().newGotoStmt(done));
        body.getUnits().add(low);
        body.getUnits().add(done);
        return method;
    }

    /** {@code if (min(i0)) return state(i0); return State.COMPLETE;}, as
     *  {@code getBlockUCState}'s {@code uc == null ? COMPLETE :
     *  uc.getBlockUCState()} compiles. */
    private static SootMethod ucState(SootClass owner, SootClass state,
                                      SootMethod min) {
        SootMethod read = new SootMethod("state",
                Collections.<Type>singletonList(IntType.v()),
                state.getType(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(read);
        SootMethod method = method(owner, "getState", state.getType());
        Body body = method.getActiveBody();
        Local has = local(body, "$z0", BooleanType.v());
        Local held = local(body, "$r1", state.getType());
        Unit open = Jimple.v().newAssignStmt(held,
                Jimple.v().newStaticInvokeExpr(read.makeRef(),
                        body.getParameterLocal(0)));
        Unit done = Jimple.v().newReturnStmt(held);
        body.getUnits().add(Jimple.v().newAssignStmt(has,
                Jimple.v().newStaticInvokeExpr(min.makeRef(),
                        body.getParameterLocal(0))));
        body.getUnits().add(Jimple.v().newIfStmt(Jimple.v().newNeExpr(has,
                IntConstant.v(0)), open));
        body.getUnits().add(Jimple.v().newAssignStmt(held,
                Jimple.v().newStaticFieldRef(state.getFieldByName("COMPLETE")
                        .makeRef())));
        body.getUnits().add(Jimple.v().newGotoStmt(done));
        body.getUnits().add(open);
        body.getUnits().add(done);
        return method;
    }

    /** {@code return getState(i0).equals(State.COMPLETE);}, as {@code
     *  isComplete} compiles. */
    private static SootMethod complete(SootClass owner, SootClass state,
                                       SootMethod uc, SootClass object) {
        SootMethod method = method(owner, "isComplete", BooleanType.v());
        Body body = method.getActiveBody();
        Local held = local(body, "$r1", state.getType());
        Local constant = local(body, "$r2", state.getType());
        Local equal = local(body, "$z0", BooleanType.v());
        body.getUnits().add(Jimple.v().newAssignStmt(held,
                Jimple.v().newStaticInvokeExpr(uc.makeRef(),
                        body.getParameterLocal(0))));
        body.getUnits().add(Jimple.v().newAssignStmt(constant,
                Jimple.v().newStaticFieldRef(state.getFieldByName("COMPLETE")
                        .makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(equal,
                Jimple.v().newVirtualInvokeExpr(held, Scene.v().makeMethodRef(
                        object, "equals", Collections.<Type>singletonList(
                                RefType.v("java.lang.Object")),
                        BooleanType.v(), false), constant)));
        body.getUnits().add(Jimple.v().newReturnStmt(equal));
        return method;
    }

    /** {@code if (i0 > 0) return this; return null;} */
    private static SootMethod lookup(SootClass owner) {
        SootMethod method = method(owner, "lookup",
                RefType.v("java.lang.Object"));
        Body body = method.getActiveBody();
        Local found = local(body, "r1", RefType.v("java.lang.Object"));
        Unit hit = Jimple.v().newAssignStmt(found,
                Jimple.v().newNewExpr(RefType.v("java.lang.Object")));
        body.getUnits().add(Jimple.v().newIfStmt(Jimple.v().newGtExpr(
                body.getParameterLocal(0), IntConstant.v(0)), hit));
        body.getUnits().add(Jimple.v().newReturnStmt(NullConstant.v()));
        body.getUnits().add(hit);
        body.getUnits().add(Jimple.v().newReturnStmt(found));
        return method;
    }

    /** {@code switch (i0) { case 1: return true; default: return false; }} */
    private static SootMethod switched(SootClass owner) {
        SootMethod method = method(owner, "switched", BooleanType.v());
        Body body = method.getActiveBody();
        Unit one = Jimple.v().newReturnStmt(IntConstant.v(1));
        Unit other = Jimple.v().newReturnStmt(IntConstant.v(0));
        body.getUnits().add(Jimple.v().newLookupSwitchStmt(
                body.getParameterLocal(0),
                Collections.singletonList(IntConstant.v(1)),
                Collections.singletonList(one), other));
        body.getUnits().add(one);
        body.getUnits().add(other);
        return method;
    }

    /** {@code static <type> name(int i0)}, its identity unit first. */
    private static SootMethod method(SootClass owner, String name,
                                     Type returned) {
        SootMethod method = new SootMethod(name,
                Collections.<Type>singletonList(IntType.v()), returned,
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local parameter = local(body, "i0", IntType.v());
        body.getUnits().add(Jimple.v().newIdentityStmt(parameter,
                Jimple.v().newParameterRef(IntType.v(), 0)));
        return method;
    }

    private static Local local(Body body, String name, Type type) {
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        return local;
    }
}
