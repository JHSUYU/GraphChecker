package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Test;
import soot.Body;
import soot.G;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
import soot.Type;
import soot.Unit;
import soot.VoidType;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.StringConstant;
import soot.jimple.ThrowStmt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A logging call runs under the VM's pause (RULES: IO only on the traced
 * flow): the calls whose callee a logging API names are paused, nothing
 * else; the pause is taken before the call and released after it, on a
 * throw too, before the rethrow.
 */
public class LoggingPauseTest {
    private static final String PAUSE = "pauseConcolicPathCondition";
    private static final String RESUME = "resumeConcolicPathCondition";

    @After
    public void resetSoot() {
        G.reset();
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
        // The catch-all the release on a throw is woven under.
        SootClass throwable = new SootClass("java.lang.Throwable",
                Modifier.PUBLIC);
        Scene.v().addClass(throwable);
        throwable.setLibraryClass();
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

    /** {@code static void log(<api> logger) { logger.info("x"); return; }} */
    private static Body callerOf(String api) {
        SootClass owner = new SootClass("a.Caller" + Math.abs(api.hashCode()),
                Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootClass logger = Scene.v().containsClass(api)
                ? Scene.v().getSootClass(api)
                : new SootClass(api, Modifier.PUBLIC | Modifier.INTERFACE);
        if (!Scene.v().containsClass(api)) {
            Scene.v().addClass(logger);
            logger.setLibraryClass();
        }
        SootMethod method = new SootMethod("log",
                Collections.<Type>singletonList(logger.getType()),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local held = Jimple.v().newLocal("r0", logger.getType());
        body.getLocals().add(held);
        body.getUnits().add(Jimple.v().newIdentityStmt(held,
                Jimple.v().newParameterRef(logger.getType(), 0)));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(held,
                        Scene.v().makeMethodRef(logger, "info",
                                Collections.<Type>singletonList(
                                        RefType.v("java.lang.String")),
                                VoidType.v(), false),
                        StringConstant.v("x"))));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return body;
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
}
