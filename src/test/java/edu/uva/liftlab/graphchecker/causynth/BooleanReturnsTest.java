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
        SootMethod nullable = nullOrComplete(owner, state);
        SootMethod completeOrThrow = complete(owner, state, nullable, object);

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
            {"h2().equals(c) throws where h2() returned null: that arm is"
                    + " open", completeOrThrow, null, false,
                Arrays.asList(sig(nullable) + "#u1=true:open[]",
                        sig(nullable) + "#u1=false:true[]")},
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

    /**
     * {@code if (!callable.call())} (solr-adhoc-09, DeleteReplicaCmd.java:277):
     * the guard unboxes a {@code Boolean} an interface call returned; the
     * object is Soot's desugared lambda its {@code bootstrap$} made, whose
     * {@code call()} forwards to the lambda's body; the body's arms return
     * {@code Boolean.TRUE} or {@code FALSE} through javac's inlined {@code
     * finally} (a null test, a call), which decides nothing.  body(int i0):
     * u1 if i0 <= 0 goto u6; u2 b = TRUE; u3 if i0 == 7 goto u5; u4 noop();
     * u5 return b; u6 b = FALSE; u7 if i0 == 7 goto u9; u8 noop(); u9
     * return b.
     */
    @Test
    public void aGuardOnALambdasBooleanIsDecidedByTheLambdasArms() {
        SootClass owner = new SootClass(OWNER, Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootClass object = library("java.lang.Object");
        SootClass bool = library("java.lang.Boolean");
        SootClass callable = library("java.util.concurrent.Callable");
        callable.setModifiers(Modifier.PUBLIC | Modifier.INTERFACE);
        Jimple j = Jimple.v();
        RefType boolType = bool.getType();

        SootMethod noop = method(owner, "noop", soot.VoidType.v());
        noop.getActiveBody().getUnits().add(j.newReturnVoidStmt());
        SootMethod body = method(owner, "lambda$run$0", boolType);
        Body lambdaBody = body.getActiveBody();
        Local i0 = lambdaBody.getParameterLocal(0);
        Local b = local(lambdaBody, "b", boolType);
        Unit returnTrue = j.newReturnStmt(b);
        Unit returnFalse = j.newReturnStmt(b);
        Unit falseArm = j.newAssignStmt(b, j.newStaticFieldRef(
                Scene.v().makeFieldRef(bool, "FALSE", boolType, true)));
        lambdaBody.getUnits().addAll(Arrays.asList(
                j.newIfStmt(j.newLeExpr(i0, IntConstant.v(0)), falseArm),
                j.newAssignStmt(b, j.newStaticFieldRef(
                        Scene.v().makeFieldRef(bool, "TRUE", boolType, true))),
                j.newIfStmt(j.newEqExpr(i0, IntConstant.v(7)), returnTrue),
                j.newInvokeStmt(j.newStaticInvokeExpr(noop.makeRef(), i0)),
                returnTrue,
                falseArm,
                j.newIfStmt(j.newEqExpr(i0, IntConstant.v(7)), returnFalse),
                j.newInvokeStmt(j.newStaticInvokeExpr(noop.makeRef(), i0)),
                returnFalse));

        SootClass lambda = new SootClass(OWNER + "$lambda_run_0__1",
                Modifier.PUBLIC);
        lambda.setSuperclass(object);
        lambda.addInterface(callable);
        Scene.v().addClass(lambda);
        lambda.setApplicationClass();
        SootMethod call = new SootMethod("call",
                Collections.<Type>emptyList(), object.getType(),
                Modifier.PUBLIC);
        lambda.addMethod(call);
        Body forward = j.newBody(call);
        call.setActiveBody(forward);
        Local self = local(forward, "this", lambda.getType());
        Local result = local(forward, "$r", boolType);
        forward.getUnits().addAll(Arrays.asList(
                j.newIdentityStmt(self, j.newThisRef(lambda.getType())),
                j.newAssignStmt(result, j.newStaticInvokeExpr(body.makeRef(),
                        IntConstant.v(1))),
                j.newReturnStmt(result)));
        SootMethod bootstrap = new SootMethod("bootstrap$",
                Collections.<Type>emptyList(), callable.getType(),
                Modifier.PUBLIC | Modifier.STATIC);
        lambda.addMethod(bootstrap);

        SootMethod run = method(owner, "run", soot.VoidType.v());
        Body caller = run.getActiveBody();
        Local made = local(caller, "$f", callable.getType());
        Local answer = local(caller, "$o", object.getType());
        Local boxed = local(caller, "$b", boolType);
        Local value = local(caller, "$z", BooleanType.v());
        Unit end = j.newReturnVoidStmt();
        Unit guard = j.newIfStmt(j.newNeExpr(value, IntConstant.v(0)), end);
        caller.getUnits().addAll(Arrays.asList(
                j.newAssignStmt(made, j.newStaticInvokeExpr(
                        bootstrap.makeRef())),
                j.newAssignStmt(answer, j.newInterfaceInvokeExpr(made,
                        Scene.v().makeMethodRef(callable, "call",
                                Collections.<Type>emptyList(),
                                object.getType(), false))),
                j.newAssignStmt(boxed, j.newCastExpr(answer, boolType)),
                j.newAssignStmt(value, j.newVirtualInvokeExpr(boxed,
                        Scene.v().makeMethodRef(bool, "booleanValue",
                                Collections.<Type>emptyList(),
                                BooleanType.v(), false))),
                guard,
                end));
        assertEquals("the lambda body's test, each arm with whether the "
                        + "guard holds there; its finally decides nothing",
                Arrays.asList(sig(body) + "#u1=true:false[]",
                        sig(body) + "#u1=false:true[]"),
                render(BooleanReturns.deciders(caller, guard)));
    }

    /**
     * A branchless helper returning by whether one call threw
     * (solr-adhoc-09's {@code waitForCoreNodeGone}: false from {@code catch
     * (TimeoutException)} around {@code waitForState}, true after it): the
     * guard is decided by the called method's own arms, an arm throwing a
     * new {@code E} with the catch's verdict, one returning with the normal
     * path's, any other open, each called from the helper ({@code via}).
     * A trap on {@code Exception} decides nothing (code anywhere below may
     * throw one), nor a called method one of whose calls declares {@code
     * E}.  waitFor(int i0): u1 if i0 <= 0 goto u7; u2 z = await(i0); u3 if z
     * != 0 goto u7; u4 e = new TimedOut; u5 e.<init>(); u6 throw e; u7
     * return.  gone(int i0): u1 waitFor(i0) [caught: TimedOut -> u3];
     * u2 goto u5; u3 caught; u4 return 0; u5 return 1.
     */
    @Test
    public void aGuardOnAHelperThatReturnsFromACatchIsDecidedByTheCallsThrowArm() {
        SootClass owner = new SootClass(OWNER, Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootClass object = library("java.lang.Object");
        SootClass throwable = library("java.lang.Throwable");
        throwable.setSuperclass(object);
        SootClass exception = library("java.lang.Exception");
        exception.setSuperclass(throwable);
        SootClass runtime = library("java.lang.RuntimeException");
        runtime.setSuperclass(exception);
        SootClass timedOut = library("j.TimedOut");
        timedOut.setSuperclass(exception);
        SootMethod init = new SootMethod("<init>",
                Collections.<Type>emptyList(), soot.VoidType.v(),
                Modifier.PUBLIC);
        timedOut.addMethod(init);
        SootClass lib = library("j.Lib");
        lib.setSuperclass(object);
        SootMethod await = new SootMethod("await",
                Collections.<Type>singletonList(IntType.v()),
                BooleanType.v(), Modifier.PUBLIC | Modifier.STATIC);
        lib.addMethod(await);
        SootMethod awaitThrowing = new SootMethod("awaitThrowing",
                Collections.<Type>singletonList(IntType.v()),
                BooleanType.v(), Modifier.PUBLIC | Modifier.STATIC);
        awaitThrowing.addException(timedOut);
        lib.addMethod(awaitThrowing);

        SootMethod waitFor = waitFor(owner, "waitFor", await, timedOut,
                init);
        SootMethod waitForDeep = waitFor(owner, "waitForDeep", awaitThrowing,
                timedOut, init);
        Object[][] rows = {
            {"the called method's own arms decide", gone(owner, "gone",
                    waitFor, timedOut), Arrays.asList(
                    sig(waitFor) + "#u1=true:false[]",
                    sig(waitFor) + "#u1=false:open[]",
                    sig(waitFor) + "#u3=true:false[]",
                    sig(waitFor) + "#u3=false:true[]")},
            {"a trap on Exception decides nothing", gone(owner, "goneAny",
                    waitFor, exception),
                    Collections.<String>emptyList()},
            {"nor a called method a call of which declares E", gone(owner,
                    "goneDeep", waitForDeep, timedOut),
                    Collections.<String>emptyList()}};
        for (Object[] row : rows) {
            SootMethod helper = (SootMethod) row[1];
            List<StaticScopeMap.Guard> found = BooleanReturns.deciders(
                    caller(owner, helper, null, true), callerGuard(owner));
            assertEquals((String) row[0], row[2], render(found));
            for (StaticScopeMap.Guard decider : found) {
                assertEquals("called from the helper", sig(helper),
                        decider.via());
            }
        }
    }

    /**
     * {@code Boolean.valueOf} of a constant (javac's boxing of {@code return
     * true;} in a method returning {@code Boolean}) is the constant, as
     * {@code Boolean.TRUE} is.  boxed(int i0): u1 if i0 <= 0 goto u4; u2 b =
     * valueOf(1); u3 return b; u4 b = valueOf(0); u5 return b.
     */
    @Test
    public void aBooleanValueOfAConstantIsThatConstant() {
        SootClass owner = new SootClass(OWNER, Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootClass bool = library("java.lang.Boolean");
        RefType boolType = bool.getType();
        Jimple j = Jimple.v();
        SootMethod boxed = method(owner, "boxed", boolType);
        Body body = boxed.getActiveBody();
        Local b = local(body, "b", boolType);
        Unit low = j.newAssignStmt(b, j.newStaticInvokeExpr(
                Scene.v().makeMethodRef(bool, "valueOf",
                        Collections.<Type>singletonList(BooleanType.v()),
                        boolType, true), IntConstant.v(0)));
        body.getUnits().addAll(Arrays.asList(
                j.newIfStmt(j.newLeExpr(body.getParameterLocal(0),
                        IntConstant.v(0)), low),
                j.newAssignStmt(b, j.newStaticInvokeExpr(
                        Scene.v().makeMethodRef(bool, "valueOf",
                                Collections.<Type>singletonList(
                                        BooleanType.v()), boolType, true),
                        IntConstant.v(1))),
                j.newReturnStmt(b),
                low,
                j.newReturnStmt(b)));
        SootMethod run = method(owner, "run", soot.VoidType.v());
        Body caller = run.getActiveBody();
        Local answer = local(caller, "$b", boolType);
        Local value = local(caller, "$z", BooleanType.v());
        Unit end = j.newReturnVoidStmt();
        Unit guard = j.newIfStmt(j.newEqExpr(value, IntConstant.v(0)), end);
        caller.getUnits().addAll(Arrays.asList(
                j.newAssignStmt(answer, j.newStaticInvokeExpr(boxed.makeRef(),
                        caller.getParameterLocal(0))),
                j.newAssignStmt(value, j.newVirtualInvokeExpr(answer,
                        Scene.v().makeMethodRef(bool, "booleanValue",
                                Collections.<Type>emptyList(),
                                BooleanType.v(), false))),
                guard,
                end));
        assertEquals(Arrays.asList(sig(boxed) + "#u1=true:true[]",
                        sig(boxed) + "#u1=false:false[]"),
                render(BooleanReturns.deciders(caller, guard)));
    }

    /**
     * solr-adhoc-09 whole: {@code if (!callable.call())}, the callable a
     * desugared lambda whose body returns {@code Boolean.TRUE} where {@code
     * gone(i0)} -- a branchless helper returning by whether {@code waitFor}
     * threw -- answered true: the body's test is decided by {@code
     * waitFor}'s arms, called from {@code gone}.  The lambda class's
     * forwarding {@code call()} is no helper level (as it is no caller for
     * via), so the four helpers fit {@code MAX_DEPTH}.  body(int i0): u1 z =
     * gone(i0); u2 if z == 0 goto u5; u3 b = TRUE; u4 return b; u5 b =
     * FALSE; u6 return b.
     */
    @Test
    public void aLambdasTestOfAHelperThatReturnsFromACatchIsDecidedBelow() {
        SootClass owner = new SootClass(OWNER, Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootClass object = library("java.lang.Object");
        SootClass throwable = library("java.lang.Throwable");
        throwable.setSuperclass(object);
        SootClass exception = library("java.lang.Exception");
        exception.setSuperclass(throwable);
        SootClass runtime = library("java.lang.RuntimeException");
        runtime.setSuperclass(exception);
        SootClass timedOut = library("j.TimedOut");
        timedOut.setSuperclass(exception);
        SootMethod init = new SootMethod("<init>",
                Collections.<Type>emptyList(), soot.VoidType.v(),
                Modifier.PUBLIC);
        timedOut.addMethod(init);
        SootClass lib = library("j.Lib");
        lib.setSuperclass(object);
        SootMethod await = new SootMethod("await",
                Collections.<Type>singletonList(IntType.v()),
                BooleanType.v(), Modifier.PUBLIC | Modifier.STATIC);
        lib.addMethod(await);
        SootClass bool = library("java.lang.Boolean");
        bool.setSuperclass(object);
        SootClass callable = library("java.util.concurrent.Callable");
        callable.setModifiers(Modifier.PUBLIC | Modifier.INTERFACE);
        Jimple j = Jimple.v();
        RefType boolType = bool.getType();
        SootMethod waitFor = waitFor(owner, "waitFor", await, timedOut,
                init);
        SootMethod gone = gone(owner, "gone", waitFor, timedOut);

        SootMethod body = method(owner, "lambda$run$0", boolType);
        Body lambdaBody = body.getActiveBody();
        Local z = local(lambdaBody, "z", BooleanType.v());
        Local b = local(lambdaBody, "b", boolType);
        Unit falseArm = j.newAssignStmt(b, j.newStaticFieldRef(
                Scene.v().makeFieldRef(bool, "FALSE", boolType, true)));
        lambdaBody.getUnits().addAll(Arrays.asList(
                j.newAssignStmt(z, j.newStaticInvokeExpr(gone.makeRef(),
                        lambdaBody.getParameterLocal(0))),
                j.newIfStmt(j.newEqExpr(z, IntConstant.v(0)), falseArm),
                j.newAssignStmt(b, j.newStaticFieldRef(
                        Scene.v().makeFieldRef(bool, "TRUE", boolType, true))),
                j.newReturnStmt(b),
                falseArm,
                j.newReturnStmt(b)));

        SootClass lambda = new SootClass(OWNER + "$lambda_run_0__1",
                Modifier.PUBLIC);
        lambda.setSuperclass(object);
        lambda.addInterface(callable);
        Scene.v().addClass(lambda);
        lambda.setApplicationClass();
        SootMethod call = new SootMethod("call",
                Collections.<Type>emptyList(), object.getType(),
                Modifier.PUBLIC);
        lambda.addMethod(call);
        Body forward = j.newBody(call);
        call.setActiveBody(forward);
        Local self = local(forward, "this", lambda.getType());
        Local result = local(forward, "$r", boolType);
        forward.getUnits().addAll(Arrays.asList(
                j.newIdentityStmt(self, j.newThisRef(lambda.getType())),
                j.newAssignStmt(result, j.newStaticInvokeExpr(body.makeRef(),
                        IntConstant.v(1))),
                j.newReturnStmt(result)));
        SootMethod bootstrap = new SootMethod("bootstrap$",
                Collections.<Type>emptyList(), callable.getType(),
                Modifier.PUBLIC | Modifier.STATIC);
        lambda.addMethod(bootstrap);

        SootMethod run = method(owner, "run", soot.VoidType.v());
        Body caller = run.getActiveBody();
        Local made = local(caller, "$f", callable.getType());
        Local answer = local(caller, "$o", object.getType());
        Local boxed = local(caller, "$b", boolType);
        Local value = local(caller, "$z", BooleanType.v());
        Unit end = j.newReturnVoidStmt();
        Unit guard = j.newIfStmt(j.newNeExpr(value, IntConstant.v(0)), end);
        caller.getUnits().addAll(Arrays.asList(
                j.newAssignStmt(made, j.newStaticInvokeExpr(
                        bootstrap.makeRef())),
                j.newAssignStmt(answer, j.newInterfaceInvokeExpr(made,
                        Scene.v().makeMethodRef(callable, "call",
                                Collections.<Type>emptyList(),
                                object.getType(), false))),
                j.newAssignStmt(boxed, j.newCastExpr(answer, boolType)),
                j.newAssignStmt(value, j.newVirtualInvokeExpr(boxed,
                        Scene.v().makeMethodRef(bool, "booleanValue",
                                Collections.<Type>emptyList(),
                                BooleanType.v(), false))),
                guard,
                end));
        String below = "[" + sig(waitFor) + "#u1=true:false[], "
                + sig(waitFor) + "#u1=false:open[], "
                + sig(waitFor) + "#u3=true:false[], "
                + sig(waitFor) + "#u3=false:true[]]";
        List<StaticScopeMap.Guard> found =
                BooleanReturns.deciders(caller, guard);
        assertEquals(Arrays.asList(sig(body) + "#u2=true:false" + below,
                        sig(body) + "#u2=false:true" + below),
                render(found));
        assertEquals("the lambda's arms: called from run (past the "
                + "lambda class and body)", sig(run), found.get(0).via());
        assertEquals("waitFor's: called from gone", sig(gone),
                found.get(0).deciders().get(0).via());
    }

    /** waitFor(int i0), void, declaring {@code thrown}: see the test. */
    private static SootMethod waitFor(SootClass owner, String name,
                                      SootMethod await, SootClass thrown,
                                      SootMethod init) {
        SootMethod method = method(owner, name, soot.VoidType.v());
        method.addException(thrown);
        Body body = method.getActiveBody();
        Jimple j = Jimple.v();
        Local z = local(body, "z", BooleanType.v());
        Local e = local(body, "e", thrown.getType());
        Unit done = j.newReturnVoidStmt();
        body.getUnits().addAll(Arrays.asList(
                j.newIfStmt(j.newLeExpr(body.getParameterLocal(0),
                        IntConstant.v(0)), done),
                j.newAssignStmt(z, j.newStaticInvokeExpr(await.makeRef(),
                        body.getParameterLocal(0))),
                j.newIfStmt(j.newNeExpr(z, IntConstant.v(0)), done),
                j.newAssignStmt(e, j.newNewExpr(thrown.getType())),
                j.newInvokeStmt(j.newSpecialInvokeExpr(e, init.makeRef())),
                j.newThrowStmt(e),
                done));
        return method;
    }

    /** gone(int i0): false where {@code waitFor} threw {@code caught}, true
     *  after it: see the test. */
    private static SootMethod gone(SootClass owner, String name,
                                   SootMethod waitFor, SootClass caught) {
        SootMethod method = method(owner, name, BooleanType.v());
        Body body = method.getActiveBody();
        Jimple j = Jimple.v();
        Local e = local(body, "e", caught.getType());
        Unit call = j.newInvokeStmt(j.newStaticInvokeExpr(waitFor.makeRef(),
                body.getParameterLocal(0)));
        Unit yes = j.newReturnStmt(IntConstant.v(1));
        Unit after = j.newGotoStmt(yes);
        Unit handler = j.newIdentityStmt(e, j.newCaughtExceptionRef());
        body.getUnits().addAll(Arrays.asList(call, after, handler,
                j.newReturnStmt(IntConstant.v(0)), yes));
        body.getTraps().add(j.newTrap(caught, call, after, handler));
        return method;
    }

    /** The guard {@link #caller} made last: its one if. */
    private static Unit callerGuard(SootClass owner) {
        SootMethod last = owner.getMethodByName("caller"
                + (owner.getMethodCount() - 1));
        for (Unit unit : last.getActiveBody().getUnits()) {
            if (unit instanceof soot.jimple.IfStmt) return unit;
        }
        return null;
    }

    private static SootClass library(String name) {
        SootClass type = new SootClass(name, Modifier.PUBLIC);
        Scene.v().addClass(type);
        type.setLibraryClass();
        return type;
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

    /** {@code if (i0 <= 0) return null; return State.COMPLETE;} */
    private static SootMethod nullOrComplete(SootClass owner,
                                             SootClass state) {
        SootMethod method = method(owner, "nullOrComplete", state.getType());
        Body body = method.getActiveBody();
        Local held = local(body, "$r1", state.getType());
        Unit low = Jimple.v().newReturnStmt(NullConstant.v());
        body.getUnits().add(Jimple.v().newIfStmt(Jimple.v().newLeExpr(
                body.getParameterLocal(0), IntConstant.v(0)), low));
        body.getUnits().add(Jimple.v().newAssignStmt(held,
                Jimple.v().newStaticFieldRef(state.getFieldByName("COMPLETE")
                        .makeRef())));
        body.getUnits().add(Jimple.v().newReturnStmt(held));
        body.getUnits().add(low);
        return method;
    }

    /** {@code return getState(i0).equals(State.COMPLETE);}, as {@code
     *  isComplete} compiles. */
    private static SootMethod complete(SootClass owner, SootClass state,
                                       SootMethod uc, SootClass object) {
        SootMethod method = method(owner, "isComplete"
                + owner.getMethodCount(), BooleanType.v());
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
