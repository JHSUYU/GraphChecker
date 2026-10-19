package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Test;
import soot.Body;
import soot.G;
import soot.Local;
import soot.Scene;
import soot.Trap;
import soot.Unit;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
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
