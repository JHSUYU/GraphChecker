package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.After;
import org.junit.Test;
import soot.Body;
import soot.G;
import soot.Unit;

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
    private static final String STATE = "a.State";
    private static final String BOOL = "java.lang.Boolean";
    private static final String CALLABLE = "java.util.concurrent.Callable";
    private static final String LAMBDA = OWNER + "$lambda_run_0__1";
    private static final String TIMED_OUT = "j.TimedOut";

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aGuardOnAHelpersConstantReturnIsDecidedByTheArmsThatRanToIt() {
        String complete = "<" + STATE + ": " + STATE + " COMPLETE>";
        String has = sig("boolean hasMinStorage");
        String suff = sig("boolean isSufficientlyReplicated");
        String lookup = sig("java.lang.Object lookup");
        String uc = sig(STATE + " getState");
        String nullable = sig(STATE + " nullOrComplete");
        Object[][] rows = {
            {"one branch, two constant arms: both arms", has, "0", "==",
                Arrays.asList(has + "#u1=true:true[]",
                        has + "#u1=false:false[]")},
            {"a branch of a nested helper's return carries its deciders, a"
                    + " comparison both of its arms; the arm that runs on to"
                    + " the comparison is open", suff, "0", "==", null},
            {"a null return decides a null test, the other arm open",
                lookup, "null", "==", Arrays.asList(lookup + "#u1=true:open[]",
                        lookup + "#u1=false:true[]")},
            {"an enum constant decides a test of another, the arm that"
                    + " reads the state open", uc, "COMMITTED", "==", null},
            {"a helper returning h2().equals(c) is the guard h2() == c, its"
                    + " verdicts read through what it returns",
                sig("boolean isComplete7"), "0", "!=", null},
            {"h2().equals(c) throws where h2() returned null: that arm is"
                    + " open", sig("boolean isComplete9"), "0", "!=",
                Arrays.asList(nullable + "#u1=true:open[]",
                        nullable + "#u1=false:true[]")},
            {"two arms the guard takes alike decide nothing",
                sig("boolean alike"), "0", "==", Collections.emptyList()},
            {"a helper with a switch has none", sig("boolean switched"), "0",
                "==", Collections.emptyList()},
            {"a library helper's branches are no application's",
                "<j.Lib: boolean outside(int)>", "0", "==",
                Collections.emptyList()},
        };
        String hasArms = "[" + has + "#u1=true:true[], " + has
                + "#u1=false:false[]]";
        // getState tests min's return with != 0: the verdicts turn.
        String notHasArms = "[" + has + "#u1=true:false[], " + has
                + "#u1=false:true[]]";
        rows[1][4] = Arrays.asList(suff + "#u2=true:open" + hasArms,
                suff + "#u2=false:false" + hasArms, suff + "#u4=true:true[]",
                suff + "#u4=false:false[]");
        rows[3][4] = Arrays.asList(uc + "#u2=true:open" + notHasArms,
                uc + "#u2=false:false" + notHasArms);
        rows[4][4] = Arrays.asList(uc + "#u2=true:open" + notHasArms,
                uc + "#u2=false:true" + notHasArms);
        StringBuilder callers = new StringBuilder();
        for (int k = 0; k < rows.length; k++) {
            callers.append(caller("caller" + k, (String) rows[k][1],
                    (String) rows[k][2], (String) rows[k][3]));
        }
        String isComplete = " int i0; " + STATE + " $r1, $r2; boolean $z0;"
                + " i0 := @parameter0: int; $r1 = staticinvoke ";
        String equals = "(i0); $r2 = " + complete + "; $z0 = virtualinvoke"
                + " $r1.<java.lang.Object: boolean equals(java.lang.Object)>"
                + "($r2); return $z0; }";
        JimpleScene.add("application public class " + OWNER + " {"
                        + twoConstants("hasMinStorage", 1, 0)
                        + twoConstants("alike", 1, 1)
                        // if (min(i0)) return true; return i0 >= 5; as javac
                        // emits it.
                        + " public static boolean isSufficientlyReplicated("
                        + "int) { int i0; boolean $z0, $z1;"
                        + " i0 := @parameter0: int; $z0 = staticinvoke " + has
                        + "(i0); if $z0 == 0 goto label1; return 1;"
                        + " label1: if i0 < 5 goto label2; $z1 = 1;"
                        + " goto label3; label2: $z1 = 0; label3: return $z1;"
                        + " }"
                        // if (i0 > 0) return this; return null;
                        + " public static java.lang.Object lookup(int) {"
                        + " int i0; java.lang.Object r1; i0 := @parameter0:"
                        + " int; if i0 > 0 goto label1; return null;"
                        + " label1: r1 = new java.lang.Object; return r1; }"
                        // switch (i0) { case 1: return true; default: return
                        // false; }
                        + " public static boolean switched(int) { int i0;"
                        + " i0 := @parameter0: int; lookupswitch(i0) {"
                        + " case 1: goto label1; default: goto label2; };"
                        + " label1: return 1; label2: return 0; }"
                        // if (min(i0)) return state(i0); return
                        // State.COMPLETE;, as getBlockUCState's uc == null ?
                        // COMPLETE : uc.getBlockUCState() compiles.
                        + " public static " + STATE + " state(int) { }"
                        + " public static " + STATE + " getState(int) {"
                        + " int i0; boolean $z0; " + STATE + " $r1;"
                        + " i0 := @parameter0: int; $z0 = staticinvoke " + has
                        + "(i0); if $z0 != 0 goto label1; $r1 = " + complete
                        + "; goto label2; label1: $r1 = staticinvoke "
                        + sig(STATE + " state") + "(i0); label2: return $r1;"
                        + " }"
                        // return getState(i0).equals(State.COMPLETE);, as
                        // isComplete compiles.
                        + " public static boolean isComplete7(int) {"
                        + isComplete + uc + equals
                        // if (i0 <= 0) return null; return State.COMPLETE;
                        + " public static " + STATE + " nullOrComplete(int) {"
                        + " int i0; " + STATE + " $r1; i0 := @parameter0: int;"
                        + " if i0 <= 0 goto label1; $r1 = " + complete + ";"
                        + " return $r1; label1: return null; }"
                        + " public static boolean isComplete9(int) {"
                        + isComplete + nullable + equals + callers + " }",
                "public class j.Lib {" + twoConstants("outside", 1, 0) + " }",
                "application public enum class " + STATE + " {"
                        + " public static final enum " + STATE + " COMPLETE;"
                        + " public static final enum " + STATE + " COMMITTED;"
                        + " }",
                "public class java.lang.Object { }");
        JimpleScene.method(sig(STATE + " state")).releaseActiveBody();
        for (int k = 0; k < rows.length; k++) {
            Object[] row = rows[k];
            Body caller = JimpleScene.method(sig("void caller" + k))
                    .getActiveBody();
            List<StaticScopeMap.Guard> found =
                    BooleanReturns.deciders(caller, guard(caller));
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
        String noop = " staticinvoke " + sig("void noop") + "(i0);";
        lambdaScene(" public static void noop(int) { int i0;"
                + " i0 := @parameter0: int; return; }",
                "if i0 <= 0 goto label2; b = " + bool("TRUE")
                        + "; if i0 == 7 goto label1;" + noop
                        + " label1: return b; label2: b = " + bool("FALSE")
                        + "; if i0 == 7 goto label3;" + noop
                        + " label3: return b;");
        Body caller = JimpleScene.method(sig("void run")).getActiveBody();
        String body = sig(BOOL + " lambda$run$0");
        assertEquals("the lambda body's test, each arm with whether the "
                        + "guard holds there; its finally decides nothing",
                Arrays.asList(body + "#u1=true:false[]",
                        body + "#u1=false:true[]"),
                render(BooleanReturns.deciders(caller, guard(caller))));
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
        String waitFor = sig("void waitFor");
        String waitForSub = sig("void waitForSub");
        String waitForSwallowed = sig("void waitForSwallowed");
        Object[][] rows = {
            {"the called method's own arms decide", gone("gone", waitFor,
                    TIMED_OUT), Arrays.asList(waitFor + "#u1=true:false[]",
                    waitFor + "#u1=false:open[]", waitFor + "#u3=true:false[]",
                    waitFor + "#u3=false:true[]")},
            {"a trap on Exception decides nothing", gone("goneAny", waitFor,
                    "java.lang.Exception"), Collections.<String>emptyList()},
            {"nor a called method a call of which declares E", gone(
                    "goneDeep", sig("void waitForDeep"), TIMED_OUT),
                    Collections.<String>emptyList()},
            {"nor a trap on a RuntimeException", gone("goneRuntime", waitFor,
                    "java.lang.RuntimeException"),
                    Collections.<String>emptyList()},
            {"catch (SubE) before catch (E): a new SubE is the first trap's"
                    + " (true, as the normal path), so that arm is open",
                    " public static boolean goneSubFirst(int) { int i0;"
                            + " j.SubTimedOut e; " + TIMED_OUT + " f;"
                            + " i0 := @parameter0: int; label1: staticinvoke "
                            + waitForSub + "(i0); label2: goto label5;"
                            + " label3: e := @caughtexception; return 1;"
                            + " label4: f := @caughtexception; return 0;"
                            + " label5: return 1; catch j.SubTimedOut from"
                            + " label1 to label2 with label3; catch "
                            + TIMED_OUT + " from label1 to label2 with label4;"
                            + " }",
                    Arrays.asList(waitForSub + "#u1=true:false[]",
                            waitForSub + "#u1=false:open[]",
                            waitForSub + "#u3=true:false[]",
                            waitForSub + "#u3=false:open[]")},
            {"a throw a finally swallows never leaves: open", gone(
                    "goneSwallowed", waitForSwallowed, TIMED_OUT),
                    Arrays.asList(waitForSwallowed + "#u1=true:false[]",
                            waitForSwallowed + "#u1=false:open[]",
                            waitForSwallowed + "#u3=true:false[]",
                            waitForSwallowed + "#u3=false:open[]")}};
        StringBuilder helpers = new StringBuilder();
        for (int k = 0; k < rows.length; k++) {
            String helper = (String) rows[k][1];
            helpers.append(helper).append(caller("caller" + k, sig("boolean "
                    + nameOf(helper)), "0", "=="));
        }
        catchScene(waitFor("waitFor", "await", TIMED_OUT, true)
                + waitFor("waitForDeep", "awaitThrowing", TIMED_OUT, true)
                + waitFor("waitForSub", "await", "j.SubTimedOut", true)
                + waitFor("waitForSwallowed", "await", TIMED_OUT, false)
                + helpers);
        for (int k = 0; k < rows.length; k++) {
            Object[] row = rows[k];
            String helper = (String) row[1];
            Body caller = JimpleScene.method(sig("void caller" + k))
                    .getActiveBody();
            List<StaticScopeMap.Guard> found =
                    BooleanReturns.deciders(caller, guard(caller));
            assertEquals((String) row[0], row[2], render(found));
            for (StaticScopeMap.Guard decider : found) {
                assertEquals("called from the helper", sig("boolean "
                        + nameOf(helper)), decider.via());
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
        String valueOf = " staticinvoke <" + BOOL + ": " + BOOL + " valueOf("
                + "boolean)>";
        String boxed = sig(BOOL + " boxed");
        JimpleScene.add("application public class " + OWNER + " {"
                + " public static " + BOOL + " boxed(int) { int i0; " + BOOL
                + " b; i0 := @parameter0: int; if i0 <= 0 goto label1; b ="
                + valueOf + "(1); return b; label1: b =" + valueOf + "(0);"
                + " return b; } public static void run(int) { int i0; " + BOOL
                + " $b; boolean $z; i0 := @parameter0: int; $b = staticinvoke "
                + boxed + "(i0); $z = virtualinvoke $b.<" + BOOL + ": boolean"
                + " booleanValue()>(); if $z == 0 goto label1; label1: return;"
                + " } }", "public class " + BOOL + " { }");
        Body caller = JimpleScene.method(sig("void run")).getActiveBody();
        assertEquals(Arrays.asList(boxed + "#u1=true:true[]",
                        boxed + "#u1=false:false[]"),
                render(BooleanReturns.deciders(caller, guard(caller))));
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
        String waitFor = sig("void waitFor");
        catchScene(waitFor("waitFor", "await", TIMED_OUT, true)
                + gone("gone", waitFor, TIMED_OUT));
        lambdaScene("", "z = staticinvoke " + sig("boolean gone")
                + "(i0); if z == 0 goto label1; b = " + bool("TRUE")
                + "; return b; label1: b = " + bool("FALSE") + "; return b;");
        Body caller = JimpleScene.method(sig("void run")).getActiveBody();
        String below = "[" + waitFor + "#u1=true:false[], "
                + waitFor + "#u1=false:open[], "
                + waitFor + "#u3=true:false[], "
                + waitFor + "#u3=false:true[]]";
        String body = sig(BOOL + " lambda$run$0");
        List<StaticScopeMap.Guard> found =
                BooleanReturns.deciders(caller, guard(caller));
        assertEquals(Arrays.asList(body + "#u2=true:false" + below,
                        body + "#u2=false:true" + below),
                render(found));
        assertEquals("the lambda's arms: called from run (past the "
                        + "lambda class and body)", sig("void run"),
                found.get(0).via());
        assertEquals("waitFor's: called from gone", sig("boolean gone"),
                found.get(0).deciders().get(0).via());
    }

    /**
     * A guard in a lambda's body: the run names a call's caller past the
     * lambda, which no static frame names, so its deciders state no via and
     * are forced in any call (the over-approximation).
     */
    @Test
    public void aGuardInALambdasBodyStatesNoVia() {
        JimpleScene.add("application public class " + OWNER + " {"
                + twoConstants("expired", 1, 0) + " public static void"
                + " lambda$check$0(int) { int i0; boolean $r;"
                + " i0 := @parameter0: int; $r = staticinvoke "
                + sig("boolean expired") + "(i0); if $r == 0 goto label1;"
                + " label1: return; } }");
        Body body = JimpleScene.method(sig("void lambda$check$0"))
                .getActiveBody();
        List<StaticScopeMap.Guard> found =
                BooleanReturns.deciders(body, guard(body));
        assertEquals(2, found.size());
        for (StaticScopeMap.Guard decider : found) {
            assertEquals("", decider.via());
        }
    }

    /** The scene of a catch: the exceptions, {@code j.Lib}'s awaits, and
     *  the helpers in {@code a.Helpers}. */
    private static void catchScene(String helpers) {
        JimpleScene.add("application public class " + OWNER + " {" + helpers
                        + " }",
                "public class java.lang.Object { }",
                "public class java.lang.Throwable extends java.lang.Object"
                        + " { }",
                "public class java.lang.Exception extends java.lang.Throwable"
                        + " { }",
                "public class java.lang.RuntimeException extends"
                        + " java.lang.Exception { }",
                "public class " + TIMED_OUT + " extends java.lang.Exception"
                        + " { public void <init>() { } }",
                "public class j.Lib extends java.lang.Object {"
                        + " public static boolean await(int) { }"
                        + " public static boolean awaitThrowing(int) throws "
                        + TIMED_OUT + " { } }",
                "public class j.SubTimedOut extends " + TIMED_OUT
                        + " { public void <init>() { } }");
        for (String bodiless : new String[] {"<" + TIMED_OUT + ": void"
                + " <init>()>", "<j.Lib: boolean await(int)>",
                "<j.Lib: boolean awaitThrowing(int)>",
                "<j.SubTimedOut: void <init>()>"}) {
            JimpleScene.method(bodiless).releaseActiveBody();
        }
    }

    /**
     * A desugared lambda's scene: {@code lambda$run$0(int i0)} running
     * {@code body} over {@code z} and {@code b}, its class's {@code call()}
     * forwarding to it and {@code bootstrap$} making it, and {@code run}'s
     * {@code if (!callable.call())}; {@code helpers} beside them.
     */
    private static void lambdaScene(String helpers, String body) {
        JimpleScene.add("application public class " + OWNER + " {" + helpers
                        + " public static " + BOOL + " lambda$run$0(int) {"
                        + " int i0; boolean z; " + BOOL + " b;"
                        + " i0 := @parameter0: int; " + body + " }"
                        + " public static void run(int) { int i0; " + CALLABLE
                        + " $f; java.lang.Object $o; " + BOOL + " $b;"
                        + " boolean $z; i0 := @parameter0: int;"
                        + " $f = staticinvoke <" + LAMBDA + ": " + CALLABLE
                        + " bootstrap$()>(); $o = interfaceinvoke $f.<"
                        + CALLABLE + ": java.lang.Object call()>();"
                        + " $b = (" + BOOL + ") $o; $z = virtualinvoke $b.<"
                        + BOOL + ": boolean booleanValue()>();"
                        + " if $z != 0 goto label1; label1: return; } }",
                "public class java.lang.Object { }",
                "public class " + BOOL + " extends java.lang.Object { }",
                "public interface " + CALLABLE + " { }",
                "application public class " + LAMBDA + " extends"
                        + " java.lang.Object implements " + CALLABLE + " {"
                        + " public java.lang.Object call() { " + LAMBDA
                        + " r0; " + BOOL + " $r; r0 := @this: " + LAMBDA + ";"
                        + " $r = staticinvoke " + sig(BOOL + " lambda$run$0")
                        + "(1); return $r; }"
                        + " public static " + CALLABLE + " bootstrap$() { } }");
        JimpleScene.method("<" + LAMBDA + ": " + CALLABLE + " bootstrap$()>")
                .releaseActiveBody();
    }

    /** waitFor(int i0), void, declaring {@code thrown}: see the test; its
     *  finally rethrows, or ({@code rethrows} false) swallows. */
    private static String waitFor(String name, String await, String thrown,
                                  boolean rethrows) {
        // What the finally catches: two levels above what it throws.
        String caught = thrown.equals(TIMED_OUT) ? "java.lang.Throwable"
                : "java.lang.Exception";
        String awaits = "staticinvoke <j.Lib: boolean " + await + "(int)>(i0)";
        return " public static void " + name + "(int) throws " + thrown
                + " { int i0; boolean z; " + thrown + " e; " + caught + " t;"
                + " i0 := @parameter0: int; if i0 <= 0 goto label1; z = "
                + awaits + "; if z != 0 goto label1; label2: e = new " + thrown
                + "; specialinvoke e.<" + thrown + ": void <init>()>();"
                + " throw e; label1: return; label3: t := @caughtexception;"
                // A finally around the throw: it rethrows what it caught,
                // past its own `if (log.isDebugEnabled())` -- or swallows it.
                + (rethrows ? " if i0 == 7 goto label4; " + awaits
                + "; label4: throw t;" : " return;") + " catch " + caught
                + " from label2 to label1 with label3; }";
    }

    /** gone(int i0): false where {@code waitFor} threw {@code caught}, true
     *  after it: see the test. */
    private static String gone(String name, String waitFor, String caught) {
        return " public static boolean " + name + "(int) { int i0; " + caught
                + " e; i0 := @parameter0: int; label1: staticinvoke " + waitFor
                + "(i0); label2: goto label4; label3: e := @caughtexception;"
                + " return 0; label4: return 1; catch " + caught + " from"
                + " label1 to label2 with label3; }";
    }

    /** {@code if (h(i0) == c) return} (or {@code !=}): the guard, c 0,
     *  {@code null} or an enum constant read into a local first. */
    private static String caller(String name, String helper, String compared,
                                 String test) {
        String returned = helper.substring(helper.indexOf(": ") + 2,
                helper.lastIndexOf(' '));
        boolean constant = compared.equals("COMMITTED");
        return " public static void " + name + "(int) { int i0; " + returned
                + " $r;" + (constant ? " " + STATE + " $c;" : "")
                + " i0 := @parameter0: int; $r = staticinvoke " + helper
                + "(i0);" + (constant ? " $c = <" + STATE + ": " + STATE + " "
                + compared + ">;" : "") + " if $r " + test + " "
                + (constant ? "$c" : compared) + " goto label1; staticinvoke "
                + helper + "(1); label1: return; }";
    }

    /** {@code if (i0 <= 0) return b; return a;} */
    private static String twoConstants(String name, int a, int b) {
        return " public static boolean " + name + "(int) { int i0;"
                + " i0 := @parameter0: int; if i0 <= 0 goto label1; return "
                + a + "; label1: return " + b + "; }";
    }

    /** The name a method's text declares. */
    private static String nameOf(String method) {
        String head = method.substring(0, method.indexOf('('));
        return head.substring(head.lastIndexOf(' ') + 1);
    }

    /** {@code <a.Helpers: <declaration>(int)>}. */
    private static String sig(String declaration) {
        return "<" + OWNER + ": " + declaration + "(int)>";
    }

    /** {@code Boolean}'s constant {@code name}. */
    private static String bool(String name) {
        return "<" + BOOL + ": " + BOOL + " " + name + ">";
    }

    /** The guard of a body: its last if. */
    private static Unit guard(Body body) {
        Unit guard = null;
        for (Unit unit : body.getUnits()) {
            if (unit instanceof soot.jimple.IfStmt) guard = unit;
        }
        return guard;
    }

    private static List<String> render(List<StaticScopeMap.Guard> guards) {
        List<String> rendered = new ArrayList<String>();
        for (StaticScopeMap.Guard guard : guards) {
            rendered.add(guard + ":" + (guard.verdict() == null ? "open"
                    : guard.verdict()) + render(guard.deciders()));
        }
        return rendered;
    }
}
