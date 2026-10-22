package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Test;
import soot.Body;
import soot.G;
import soot.Local;
import soot.Scene;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

public class WeaveTest {
    private static final String PAUSE = "pauseConcolicPathCondition";
    private static final String RESUME = "resumeConcolicPathCondition";
    private static final String WORK =
            " staticinvoke <a.Loops: void work()>();";

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aStartPassesTheReceiverItWasSubmittedTo() {
        String executor = "java.util.concurrent.Executor";
        JimpleScene.load("public interface java.lang.Runnable { }",
                "public interface " + executor + " { }",
                "public class a.Pools { }",
                "application public class a.Submitter { public static void"
                        + " submit(" + executor + ", java.lang.Runnable) { "
                        + executor + " r0; java.lang.Runnable r1;"
                        + " r0 := @parameter0: " + executor + ";"
                        + " r1 := @parameter1: java.lang.Runnable;"
                        + " interfaceinvoke r0.<" + executor + ": void execute("
                        + "java.lang.Runnable)>(r1); staticinvoke <a.Pools:"
                        + " void execute(java.lang.Runnable)>(r1); return; }"
                        + " }");
        Body body = JimpleScene.method("<a.Submitter: void submit(" + executor
                + ",java.lang.Runnable)>").getActiveBody();
        List<Unit> units = new ArrayList<>(body.getUnits());
        Stmt submitted = (Stmt) units.get(2);
        Stmt helper = (Stmt) units.get(3);
        Local pool = body.getParameterLocal(0);
        Local task = body.getParameterLocal(1);

        CausynthPipeline.HookCatalog refs =
                CausynthPipeline.HookCatalog.concolic();
        Object[][] table = {
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

    @Test
    public void aContinuationIsCarriedAndStartedWhereItIsRegistered()
            throws Exception {
        String future = "java.util.concurrent.CompletableFuture";
        String action = "java.util.function.BiConsumer";
        JimpleScene.load("public interface java.util.concurrent.CompletionStage"
                        + " { }",
                "public class " + future + " extends java.lang.Object"
                        + " implements java.util.concurrent.CompletionStage { }",
                "public interface " + action + " { }",
                "application public class a.Listener { public static void"
                        + " listen(" + future + ", " + action + ") { " + future
                        + " r0; " + action + " r1; r0 := @parameter0: " + future
                        + "; r1 := @parameter1: " + action + "; virtualinvoke"
                        + " r0.<" + future + ": " + future + " whenComplete("
                        + action + ")>(r1); return; } }");
        Body body = JimpleScene.method("<a.Listener: void listen(" + future
                + "," + action + ")>").getActiveBody();
        Stmt registered = (Stmt) new ArrayList<>(body.getUnits()).get(2);
        Local registrant = body.getParameterLocal(0);
        assertEquals(1, CausynthPipeline.fileStarts(body, registered,
                "<a.Listener: void listen()>#u2",
                CausynthPipeline.HookCatalog.concolic()));
        InvokeExpr filed = startWorkBefore(body, registered);
        Value carried = registered.getInvokeExpr().getArg(0);
        assertSame(carried, filed.getArg(1));
        assertSame(registrant, filed.getArg(2));
        Stmt carrying = null;
        for (Unit unit : body.getUnits()) {
            if (unit instanceof AssignStmt && ((AssignStmt) unit).getLeftOp()
                    == carried) {
                carrying = (Stmt) unit;
            }
        }
        assertEquals("carry", carrying.getInvokeExpr().getMethodRef()
                .getName());
        assertSame(body.getParameterLocal(1),
                carrying.getInvokeExpr().getArg(0));
        assertNotNull(Class.forName(carrying.getInvokeExpr().getMethodRef()
                .getDeclaringClass().getName()).getMethod("carry",
                Class.forName(action)));
    }

    @Test
    public void aLoggingApisCallIsPausedAndReleasedOnEveryExit() {
        Object[][] rows = {
                {"org.slf4j.Logger", true},
                {"org.apache.logging.log4j.Logger", true},
                {"org.apache.log4j.Category", true},
                {"org.apache.log4j.Logger", true},
                {"java.util.logging.Logger", true},
                {"org.apache.commons.logging.Log", true},
                {"org.slf4j.LoggerFactory", false},
                {"org.apache.solr.common.cloud.SolrZkClient", false},
        };
        JimpleScene.add("public class java.lang.Throwable { }");
        CausynthPipeline.HookCatalog refs =
                CausynthPipeline.HookCatalog.concolic();
        for (Object[] row : rows) {
            String api = (String) row[0];
            boolean logging = (Boolean) row[1];
            Body body = callerOf(api);
            InvokeStmt call = onlyCall(body);
            assertEquals(api, logging,
                    CausynthPipeline.loggingCall(call.getInvokeExpr()));
            if (!logging) continue;
            CausynthPipeline.pauseAround(body, call, refs);
            List<Unit> units = new ArrayList<>(body.getUnits());
            int at = units.indexOf(call);
            assertEquals(api, PAUSE, callee(units.get(at - 1)));
            assertEquals(api, RESUME, callee(units.get(at + 1)));
            assertEquals(api, 1, body.getTraps().size());
            Trap trap = body.getTraps().getFirst();
            assertTrue(api, trap.getBeginUnit() == call
                    && trap.getEndUnit() == units.get(at + 1));
            int handler = units.indexOf(trap.getHandlerUnit());
            assertEquals(api, RESUME, callee(units.get(handler + 1)));
            assertTrue(api, units.get(handler + 2) instanceof ThrowStmt);
        }
    }

    @Test
    public void aThrowLeavingTheLoopBodyClosesItAtTheMethodsOwnHandler() {
        JimpleScene.load("public class java.lang.Throwable { }",
                "public class a.Loops { public static void work() { }"
                + " public static void serve(int, int) { int i0, i1;"
                + " java.lang.Throwable $r0, $r1, $r2;"
                + " i0 := @parameter0: int; i1 := @parameter1: int;"
                + " label1: if i0 <= 0 goto label4; label2:" + WORK
                + " label3: i0 = i0 - 1; goto label1;"
                + " label5: $r1 := @caughtexception; i0 = i0 - 1;"
                + " goto label1; label4:" + WORK + " label7: return;"
                + " label6: $r0 := @caughtexception; return;"
                + " label8: $r2 := @caughtexception; return;"
                + " catch java.lang.Throwable from label2 to label3"
                + " with label5;"
                + " catch java.lang.Throwable from label1 to label4"
                + " with label6;"
                + " catch java.lang.Throwable from label4 to label7"
                + " with label8; } }");
        Body body = JimpleScene.method("<a.Loops: void serve(int,int)>")
                .getActiveBody();
        CausynthPipeline.tagOriginalUnits(
                CausynthPipeline.snapshotUnits(body));
        List<CfgLoopControl.RetainedLoop> loops = CfgLoopControl
                .retainedLoops(CfgLoopControl.loopCfg(body));
        assertEquals(1, loops.size());
        List<Unit> handlers = new ArrayList<>();
        for (Trap trap : body.getTraps()) handlers.add(trap.getHandlerUnit());
        assertEquals(1, CausynthPipeline.closeAtOuterHandlers(body,
                loops.get(0).natural.members(),
                CausynthPipeline.HookCatalog.concolic(),
                NullConstant.v(), NullConstant.v()));
        String[] closes = {"an inner catch that continues the loop", "",
                "the method's catch the throw leaves the body for",
                "throwRegionFrame",
                "a catch of code past the loop", ""};
        for (int k = 0; k < handlers.size(); k++) {
            List<Unit> units = new ArrayList<>(body.getUnits());
            String after = "";
            for (Unit unit : units.subList(units.indexOf(handlers.get(k)) + 1,
                    Math.min(units.size(),
                            units.indexOf(handlers.get(k)) + 4))) {
                if ("throwRegionFrame".equals(callee(unit))) {
                    after = callee(unit);
                }
            }
            assertEquals(closes[2 * k], closes[2 * k + 1], after);
        }
    }

    private static Body callerOf(String api) {
        String owner = "a.Caller" + Math.abs(api.hashCode());
        if (!Scene.v().containsClass(api)) {
            JimpleScene.add("public interface " + api + " { }");
        }
        JimpleScene.add("application public class " + owner + " { public"
                + " static void log(" + api + ") { " + api + " r0;"
                + " r0 := @parameter0: " + api + "; interfaceinvoke r0.<" + api
                + ": void info(java.lang.String)>(\"x\"); return; } }");
        return JimpleScene.method("<" + owner + ": void log(" + api + ")>")
                .getActiveBody();
    }

    @Test
    public void anIterationOpensWhereItHoldsTheCallOrNowhere() {
        JimpleScene.load("public class a.Loops { public static void work() { }"
                + loop("exitPath", "label1: if i0 <= 0 goto label3;"
                        + " if i1 != 0 goto label2; i0 = i0 - 1; goto label1;"
                        + " label2:" + WORK + " label3:")
                + loop("inBody", "label1: if i0 <= 0 goto label2;"
                        + " if i1 != 0 goto label2;" + WORK + " i0 = i0 - 1;"
                        + " goto label1; label2:")
                + loop("beforeControls", "label1:" + WORK
                        + " if i0 > 0 goto label2; i0 = i0 + 1; goto label1;"
                        + " label2:")
                + loop("alike", "label1: if i0 > 0 goto label2;"
                        + " if i1 <= 0 goto label3; goto label4;"
                        + " label2: if i0 <= 9 goto label3; goto label4;"
                        + " label3:" + WORK + " i0 = i0 - 1; goto label1;"
                        + " label4:") + " }");
        Object[][] rows = {
            {"a call on the loop's exit path", "exitPath", 6, -1, 0},
            {"a call in the body after the controls", "inBody", 4, 3, 1},
            {"work before every control", "beforeControls", 2, 2, 1},
            {"a call two controls enter alike", "alike", 7, 7, 2},
        };
        for (Object[] row : rows) {
            String name = (String) row[0];
            List<Unit> units = new ArrayList<>(JimpleScene.method(
                    "<a.Loops: void " + row[1] + "(int,int)>")
                    .getActiveBody().getUnits());
            List<CfgLoopControl.RetainedLoop> loops =
                    CfgLoopControl.retainedLoops(CfgLoopControl.loopCfg(
                            JimpleScene.method("<a.Loops: void " + row[1]
                                    + "(int,int)>").getActiveBody()));
            assertEquals(name, 1, loops.size());
            CfgLoopControl.BodyEntry entry = CfgLoopControl.bodyEntry(
                    loops.get(0).natural, loops.get(0).guards,
                    units.get((Integer) row[2]));
            if ((Integer) row[3] < 0) {
                assertNull(name, entry);
            } else {
                assertSame(name, units.get((Integer) row[3]), entry.target);
                assertEquals(name, row[4], entry.edges.size());
            }
        }
    }

    @Test
    public void aDrawOnTheMethodsOwnSeededRandomStaysTheProgramsOwn() {
        String random = "java.util.Random";
        String seeded = " specialinvoke r2.<" + random + ": void <init>(long)>"
                + "(l3);";
        String xor = " l3 = l0 ^ 3007405056L;";
        Object[][] rows = {
            {"own", xor + seeded, "", true},
            {"copied", xor + seeded + " r4 = r2;", "r4", true},
            {"clock", " l3 = staticinvoke <java.lang.System: long nanoTime()>();"
                    + seeded, "", false},
            {"unseeded", " specialinvoke r2.<" + random + ": void <init>()>();",
                    "", false},
            {"stored", xor + seeded + " <a.Draws: " + random + " held> = r2;",
                    "", false},
            {"passed", xor + seeded + " staticinvoke <a.Draws: void use("
                    + random + ")>(r2);", "", false},
        };
        StringBuilder methods = new StringBuilder();
        for (Object[] row : rows) {
            String drawer = ((String) row[2]).isEmpty() ? "r2" : (String) row[2];
            methods.append(" public static void ").append(row[0])
                    .append("(long, byte[]) { long l0, l3; byte[] r1; ")
                    .append(random).append(" r2, r4; l0 := @parameter0: long;")
                    .append(" r1 := @parameter1: byte[]; r2 = new ")
                    .append(random).append(";").append(row[1])
                    .append(" virtualinvoke ").append(drawer).append(".<")
                    .append(random).append(": void nextBytes(byte[])>(r1);")
                    .append(" return; }");
        }
        JimpleScene.load(JimpleScene.OBJECT, "public class " + random
                + " extends java.lang.Object { }",
                "application public class a.Draws { static " + random
                + " held; public static void use(" + random + ") { " + random
                + " r0; r0 := @parameter0: " + random + "; return; }"
                + methods + " }");
        for (Object[] row : rows) {
            Body body = JimpleScene.method("<a.Draws: void " + row[0]
                    + "(long,byte[])>").getActiveBody();
            CausynthPipeline.tagOriginalUnits(
                    CausynthPipeline.snapshotUnits(body));
            Stmt draw = null;
            for (Unit unit : body.getUnits()) {
                if ("nextBytes".equals(callee(unit))) draw = (Stmt) unit;
            }
            Value drawer = ((soot.jimple.InstanceInvokeExpr)
                    draw.getInvokeExpr()).getBase();
            CausynthPipeline.replaceRandom(body, draw,
                    "<a.Draws: void " + row[0] + "()>#u9");
            assertEquals((String) row[0], row[3], drawer
                    == ((soot.jimple.InstanceInvokeExpr) draw.getInvokeExpr())
                    .getBase());
        }
    }

    private static InvokeExpr startWorkBefore(Body body, Stmt start) {
        List<Unit> units = new ArrayList<>(body.getUnits());
        for (int at = units.indexOf(start) - 1; at >= 0; at--) {
            if ("startWork".equals(callee(units.get(at)))) {
                return ((InvokeStmt) units.get(at)).getInvokeExpr();
            }
        }
        throw new AssertionError("no startWork before " + start);
    }

    private static InvokeStmt onlyCall(Body body) {
        for (Unit unit : body.getUnits()) {
            if (unit instanceof InvokeStmt) return (InvokeStmt) unit;
        }
        throw new AssertionError("no call");
    }

    private static String callee(Unit unit) {
        if (!(unit instanceof InvokeStmt)) return "";
        InvokeExpr invoke = ((InvokeStmt) unit).getInvokeExpr();
        return invoke.getMethodRef().getName();
    }

    private static String loop(String name, String loop) {
        return " public static void " + name + "(int, int) { int i0, i1;"
                + " i0 := @parameter0: int; i1 := @parameter1: int; " + loop
                + " return; }";
    }
}
