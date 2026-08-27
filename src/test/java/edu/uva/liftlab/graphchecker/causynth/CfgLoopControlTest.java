package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Test;
import soot.ArrayType;
import soot.Body;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.TrapUnitGraph;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * README section 5: a loop is discovered, proved, and bounded on one CFG.
 *
 * <p>Every loop of the HDFS-11741 slice sits in a method with a
 * {@code try}/{@code catch}, so the two halves pinned here are the ones that
 * decide whether those service loops enter the bounded model at all.</p>
 */
public class CfgLoopControlTest {

    @After
    public void resetSoot() {
        G.reset();
    }

    /**
     * A reducible loop whose body contains a caught operation is discovered
     * from the same loop CFG it is instrumented from, and the iteration
     * guard proved for it belongs to the loop that was bounded.
     */
    @Test
    public void catchHandlerLoopIsProvedAndBoundedFromOneGraph() {
        SootMethod method = serviceLoopWithCatchHandler();
        Body body = method.getActiveBody();
        Unit header = unit(body, 1);
        Unit latch = unit(body, 6);

        // The defect this pins: the ordinary transfer graph alone cannot
        // prove the loop, because the handler has no predecessor in it and
        // therefore reaches the latch as a second CFG entry.
        assertFalse(new MHGDominatorsFinder<Unit>(new BriefUnitGraph(body))
                .isDominatedBy(latch, header));

        CfgLoopControl.LoopCfg loopCfg = CfgLoopControl.loopCfg(body,
                new BriefUnitGraph(body));
        assertTrue(loopCfg.isDominatedBy(latch, header));
        assertEquals(Collections.singleton(header),
                new LinkedHashSet<>(CfgLoopControl.guards(loopCfg)));

        int bounded = new CausynthPipeline(null).instrumentConcolicLoopBounds(
                Collections.singleton(method.getSignature()),
                LoopBoundPolicy.cfgBackedges(8),
                Collections.<String>emptySet());

        // One backedge, and the loop it was charged to is the loop whose
        // guard was proved above: both name header u1.
        assertEquals(1, bounded);
        assertEquals(Collections.singleton(
                        method.getSignature() + "#loop:u1"),
                boundedLoops(body));
        body.validate();
    }

    /**
     * A trap whose range covers its own handler -- what javac emits for a
     * {@code synchronized} block -- is a cycle only over trap edges.  It is
     * not an iteration, no bound can be installed on an abrupt transfer, and
     * the boundary is named rather than assumed away.
     */
    @Test
    public void trapOnlyCycleIsNamedAndCarriesNoBound() {
        SootMethod method = selfProtectingHandler();
        Body body = method.getActiveBody();
        CfgLoopControl.LoopCfg loopCfg = CfgLoopControl.loopCfg(body,
                new BriefUnitGraph(body));

        assertTrue(CfgLoopControl.guards(loopCfg).isEmpty());
        assertEquals(0, new CausynthPipeline(null)
                .instrumentConcolicLoopBounds(
                        Collections.singleton(method.getSignature()),
                        LoopBoundPolicy.cfgBackedges(8),
                        Collections.<String>emptySet()));
        assertTrue(boundedLoops(body).isEmpty());
        body.validate();

        // A caller cannot re-open the question by handing in a graph whose
        // successors already include exception edges.
        try {
            CfgLoopControl.loopCfg(body, new TrapUnitGraph(body));
            fail("an exceptional graph is not a transfer graph");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage().startsWith(
                    "LOOP_CFG_TRANSFERS_MUST_BE_UNEXCEPTIONAL"));
        }
    }

    /**
     * README's loop authority: an array-backed indexed {@code for} remains
     * {@code FIXED_COUNT_INDEXED} when one guarded local path exits early.
     * The array fixes the available iteration slots; the branch guard in the
     * region case decides which slots that path reaches.
     */
    @Test
    public void anArrayIndexedForRemainsFixedCountAcrossEarlyExit() {
        Body counted = arrayIndexedLoop(false).getActiveBody();
        String indexed = CfgLoopControl.classify(
                CfgLoopControl.loopCfg(counted, new BriefUnitGraph(counted)))
                .get(unit(counted, 3));
        assertEquals(LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, indexed);
        assertEquals(LoopBoundPolicy.LOOP_CLASSIFIED_ARRAY_INDEXED,
                CfgLoopControl.classificationAuthority(indexed));
        G.reset();
        Body broken = arrayIndexedLoop(true).getActiveBody();
        String escaped = CfgLoopControl.classify(
                CfgLoopControl.loopCfg(broken, new BriefUnitGraph(broken)))
                .get(unit(broken, 3));
        assertEquals(LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, escaped);
        assertEquals(LoopBoundPolicy.LOOP_CLASSIFIED_ARRAY_INDEXED,
                CfgLoopControl.classificationAuthority(escaped));
    }

    /**
     * The fixed-array producer reads the unique {@code lengthof} local and
     * closes its dynamic occurrence on every normal exit, including break.
     */
    @Test
    public void fixedArrayInstrumentationPublishesExactDynamicN() {
        SootMethod method = arrayIndexedLoop(true);
        Body body = method.getActiveBody();
        String guardSite = method.getSignature() + "#u3";

        new CausynthPipeline(null).instrumentConcolicLoopBounds(
                Collections.singleton(method.getSignature()),
                LoopBoundPolicy.cfgBackedges(8),
                Collections.singleton(guardSite));

        int records = 0;
        int completions = 0;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) continue;
            Stmt statement = (Stmt) unit;
            String hook = statement.getInvokeExpr().getMethodRef().name();
            if ("recordLoopCardinality".equals(hook)) {
                records++;
                assertEquals("len", ((Local) statement.getInvokeExpr()
                        .getArg(1)).getName());
            } else if ("completeLoopCardinality".equals(hook)) {
                completions++;
            }
        }
        assertEquals(1, records);
        // The array guard's exhaustion exit and the early break are separate
        // dynamic-loop terminals and both close the same invocation.
        assertEquals(2, completions);
        body.validate();
    }

    // ------------------------------------------------------------------
    // Fixture
    // ------------------------------------------------------------------

    /**
     * <pre>
     * u0 i = 0
     * u1 a = newarray (java.lang.String)[3]
     * u2 $len = lengthof a       // header
     * u3 if i &gt;= $len goto u7  // the index test, and the only exit
     * u4 if i == 1 goto u7       // the break, only when asked for
     * u5 i = i + 1
     * u6 goto u2                 // latch
     * u7 return
     * </pre>
     */
    private static SootMethod arrayIndexedLoop(boolean withBreak) {
        SootClass owner = concolicScene("example.IndexedLoop");
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local i = Jimple.v().newLocal("i", IntType.v());
        Local array = Jimple.v().newLocal("a",
                ArrayType.v(RefType.v("java.lang.String"), 1));
        Local length = Jimple.v().newLocal("len", IntType.v());
        body.getLocals().addAll(Arrays.asList(i, array, length));

        Unit exit = Jimple.v().newReturnVoidStmt();
        Unit header = Jimple.v().newAssignStmt(length,
                Jimple.v().newLengthExpr(array));
        Unit guard = Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(i, length), exit);
        body.getUnits().add(Jimple.v().newAssignStmt(i, IntConstant.v(0)));
        body.getUnits().add(Jimple.v().newAssignStmt(array,
                Jimple.v().newNewArrayExpr(RefType.v("java.lang.String"),
                        IntConstant.v(3))));
        body.getUnits().add(header);
        body.getUnits().add(guard);
        body.getUnits().add(withBreak
                ? Jimple.v().newIfStmt(
                        Jimple.v().newEqExpr(i, IntConstant.v(1)), exit)
                : Jimple.v().newNopStmt());
        body.getUnits().add(Jimple.v().newAssignStmt(i,
                Jimple.v().newAddExpr(i, IntConstant.v(1))));
        body.getUnits().add(Jimple.v().newGotoStmt(header));
        body.getUnits().add(exit);
        return method;
    }

    /**
     * <pre>
     * u0 i = 0
     * u1 if i &gt;= 5 goto u7      // header and iteration guard
     * u2 i = i + 1               // protected
     * u3 goto u6                 // protected
     * u4 $e := @caughtexception  // handler, inside the loop
     * u5 nop
     * u6 goto u1                 // latch
     * u7 return
     * </pre>
     */
    private static SootMethod serviceLoopWithCatchHandler() {
        SootClass owner = concolicScene("example.CaughtLoop");
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local i = Jimple.v().newLocal("i", IntType.v());
        Local caught = Jimple.v().newLocal("caught",
                RefType.v("java.lang.Throwable"));
        body.getLocals().add(i);
        body.getLocals().add(caught);

        Unit exit = Jimple.v().newReturnVoidStmt();
        Unit header = Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(i, IntConstant.v(5)), exit);
        Unit protectedWork = Jimple.v().newAssignStmt(i,
                Jimple.v().newAddExpr(i, IntConstant.v(1)));
        Unit latch = Jimple.v().newGotoStmt(header);
        Unit skipHandler = Jimple.v().newGotoStmt(latch);
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        Unit handled = Jimple.v().newNopStmt();

        body.getUnits().add(Jimple.v().newAssignStmt(i, IntConstant.v(0)));
        body.getUnits().add(header);
        body.getUnits().add(protectedWork);
        body.getUnits().add(skipHandler);
        body.getUnits().add(handler);
        body.getUnits().add(handled);
        body.getUnits().add(latch);
        body.getUnits().add(exit);
        body.getTraps().add(Jimple.v().newTrap(
                Scene.v().getSootClass("java.lang.Throwable"),
                protectedWork, handler, handler));
        return method;
    }

    /**
     * <pre>
     * u0 i = 0
     * u1 i = i + 1               // protected
     * u2 $e := @caughtexception  // handler, protected by its own trap
     * u3 return
     * </pre>
     */
    private static SootMethod selfProtectingHandler() {
        SootClass owner = concolicScene("example.SelfProtectingHandler");
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local i = Jimple.v().newLocal("i", IntType.v());
        Local caught = Jimple.v().newLocal("caught",
                RefType.v("java.lang.Throwable"));
        body.getLocals().add(i);
        body.getLocals().add(caught);

        Unit protectedWork = Jimple.v().newAssignStmt(i,
                Jimple.v().newAddExpr(i, IntConstant.v(1)));
        Unit handler = Jimple.v().newIdentityStmt(caught,
                Jimple.v().newCaughtExceptionRef());
        Unit exit = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newAssignStmt(i, IntConstant.v(0)));
        body.getUnits().add(protectedWork);
        body.getUnits().add(handler);
        body.getUnits().add(exit);
        body.getTraps().add(Jimple.v().newTrap(
                Scene.v().getSootClass("java.lang.Throwable"),
                protectedWork, exit, handler));
        return method;
    }

    /** A scene holding the loop-accounting hooks and one application class. */
    private static SootClass concolicScene(String name) {
        G.reset();
        Scene.v().addClass(new SootClass("java.lang.Throwable",
                Modifier.PUBLIC));
        Scene.v().addClass(new SootClass("java.lang.String",
                Modifier.PUBLIC));
        SootClass runtime = new SootClass(
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                Modifier.PUBLIC);
        for (String hook : Arrays.asList("checkLoopBackedge",
                "checkReplayLoopBody", "recordLoopCardinality")) {
            runtime.addMethod(new SootMethod(hook,
                    Arrays.asList(RefType.v("java.lang.String"),
                            IntType.v()), VoidType.v(),
                    Modifier.PUBLIC | Modifier.STATIC));
        }
        runtime.addMethod(new SootMethod("completeLoopCardinality",
                Collections.singletonList(RefType.v("java.lang.String")),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC));
        Scene.v().addClass(runtime);
        SootClass owner = new SootClass(name, Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        return owner;
    }

    private static Unit unit(Body body, int index) {
        int position = 0;
        for (Unit unit : body.getUnits()) {
            if (position++ == index) return unit;
        }
        throw new AssertionError("no unit " + index);
    }

    /** The loop identities the bound pass charged this body's hooks to. */
    private static Set<String> boundedLoops(Body body) {
        Set<String> result = new LinkedHashSet<>();
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof Stmt)
                    || !((Stmt) unit).containsInvokeExpr()) {
                continue;
            }
            String hook = ((Stmt) unit).getInvokeExpr().getMethodRef().name();
            if (!"checkLoopBackedge".equals(hook)) {
                continue;
            }
            result.add(((StringConstant) ((Stmt) unit).getInvokeExpr()
                    .getArg(0)).value);
        }
        return result;
    }
}
