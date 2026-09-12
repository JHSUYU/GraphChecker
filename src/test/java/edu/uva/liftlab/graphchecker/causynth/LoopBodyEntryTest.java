package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.SiteId;
import org.junit.After;
import org.junit.Test;
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
import soot.toolkits.graph.BriefUnitGraph;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

public class LoopBodyEntryTest {

    @After
    public void resetSoot() {
        G.reset();
    }

    /** Multiple exits name one loop; the outer guard opens the iteration. */
    @Test
    public void demandedUnitSelectsOutermostDominatingControlEdge()
            throws Exception {
        SootMethod method = loopWithThreeExitControls();
        Body body = method.getActiveBody();
        List<Unit> units = new ArrayList<>(body.getUnits());
        // The same bytecode may acquire one extra Jimple lowering statement
        // under the instrumentation campaign's application-class union. The
        // frozen plan still names the logical controls as u2/u4/u6.
        body.getUnits().insertBeforeNoRedirect(Jimple.v().newNopStmt(),
                units.get(4));
        tagOriginalUnits(new ArrayList<>(body.getUnits()));
        assertEquals(1, new CausynthPipeline(null)
                .instrumentConcolicLoopBounds(
                        Collections.singleton(method.getSignature()),
                        LoopBoundPolicy.cfgBackedges(8),
                        Collections.<String>emptySet()));
        CfgLoopControl.NaturalLoop loop = onlyLoop(body);

        Set<String> controls = new LinkedHashSet<>();
        // Deliberately state the later controls first: declaration order is
        // not an entry-selection rule.
        controls.add(site(method, 6));
        controls.add(site(method, 4));
        controls.add(site(method, 2));

        CfgLoopControl.Edge entry = CausynthPipeline.loopBodyEntry(
                body, loop, controls, 5);

        assertSame(units.get(2), entry.source);
        assertSame(units.get(3), entry.target);

        Unit firstEntry = Jimple.v().newNopStmt();
        CausynthPipeline.insertLoopBodyEntry(body, method, loop, entry,
                Collections.singletonList(firstEntry), loop.identity(method));
        CfgLoopControl.Edge secondEdge = CausynthPipeline.loopBodyEntry(
                body, loop, controls, 5);
        // Selection crosses the first task's transparent gate and appends the
        // second entry toward the same original body unit.
        assertSame(firstEntry, secondEdge.source);
        assertSame(units.get(3), secondEdge.target);
        Unit secondEntry = Jimple.v().newNopStmt();
        CausynthPipeline.insertLoopBodyEntry(body, method, loop, secondEdge,
                Collections.singletonList(secondEntry), loop.identity(method));
        assertSame(firstEntry, body.getUnits().getSuccOf(units.get(2)));
        assertSame(secondEntry, body.getUnits().getSuccOf(firstEntry));
        assertSame(units.get(3), body.getUnits().getSuccOf(secondEntry));

        Unit firstExit = Jimple.v().newNopStmt();
        CfgLoopControl.Edge backedge = CausynthPipeline.loopBodyClosingEdges(
                method, loop, controls).get(0);
        CausynthPipeline.insertLoopBodyExit(body, method,
                backedge,
                Collections.singletonList(firstExit), loop.identity(method));
        Unit secondExit = Jimple.v().newNopStmt();
        backedge = CausynthPipeline.loopBodyClosingEdges(
                method, loop, controls).get(0);
        CausynthPipeline.insertLoopBodyExit(body, method,
                backedge,
                Collections.singletonList(secondExit), loop.identity(method));
        List<Unit> closingPath = uniquePath(body, units.get(8), units.get(1));
        // Entries open first then second; every boundary closes second then
        // first, as required by the runtime's activation stack.
        assertTrue(closingPath.indexOf(secondExit) >= 0);
        assertTrue(closingPath.indexOf(firstExit)
                > closingPath.indexOf(secondExit));
        body.validate();
    }

    /** A state writer nested in a task also owns replayable write occurrences. */
    @Test
    public void nestedStateWriterKeepsItsOwnEntryRoot() {
        String task = "<example.Task: void run()>";
        String writer = "<example.Store: void update(int)>";
        String target = "<example.Target: void fail()>";
        String state = "<example.Store: java.util.Map values>";
        StaticProgram program = new StaticProgram();
        program.executionContextAuthorities.put(task, "TASK_ENTRY");
        program.targetResolved.put("method", target);
        program.edges.add(edge(task, "VALUE_PASS", task + "::input",
                writer + ".param0:int", writer));
        program.edges.add(edge(writer, "HEAP_WRITE", writer + "::input",
                state, ""));
        program.edges.add(edge(target, "HEAP_READ", state,
                target + "::value", ""));
        program.edges.add(edge(target, "GUARD", target + "::value",
                target + "#u7#exception:Failure", ""));

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(task, writer, target));

        int writerRegions = 0;
        Map<String, Object> writerRoot = null;
        for (Map<String, Object> region : program.regions) {
            if (((List<?>) region.get("methods")).contains(writer)) {
                writerRegions++;
            }
            if (writer.equals(region.get("rootMethod"))) {
                writerRoot = region;
            }
        }
        assertEquals(2, writerRegions);
        assertEquals(SymbolicRegionPlanner.STATE_WRITER_ENTRY,
                writerRoot == null ? null : writerRoot.get("rootAuthority"));
    }

    /**
     * <pre>
     * u1: header
     * u2: if outerExit goto u9   // body edge u2 -> u3
     * u4: if nestedExit goto u9  // body edge u4 -> demanded u5
     * u5: demanded
     * u6: if lateExit goto u9    // occurs after demanded
     * u8: goto u1
     * </pre>
     */
    private static SootMethod loopWithThreeExitControls() {
        SootClass runtime = new SootClass(
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime",
                Modifier.PUBLIC);
        runtime.addMethod(new SootMethod("checkLoopBackedge",
                Arrays.asList(RefType.v("java.lang.String"), IntType.v()),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC));
        Scene.v().addClass(runtime);
        SootClass owner = new SootClass("example.MultiControlLoop",
                Modifier.PUBLIC);
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local i = Jimple.v().newLocal("i", IntType.v());
        body.getLocals().add(i);

        Unit header = Jimple.v().newNopStmt();
        Unit exit = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newAssignStmt(i, IntConstant.v(0)));
        body.getUnits().add(header);
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(i, IntConstant.v(10)), exit));
        body.getUnits().add(Jimple.v().newAssignStmt(i,
                Jimple.v().newAddExpr(i, IntConstant.v(1))));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(i, IntConstant.v(3)), exit));
        body.getUnits().add(Jimple.v().newAssignStmt(i,
                Jimple.v().newAddExpr(i, IntConstant.v(2))));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(i, IntConstant.v(7)), exit));
        body.getUnits().add(Jimple.v().newAssignStmt(i,
                Jimple.v().newAddExpr(i, IntConstant.v(1))));
        body.getUnits().add(Jimple.v().newGotoStmt(header));
        body.getUnits().add(exit);
        return method;
    }

    private static CfgLoopControl.NaturalLoop onlyLoop(Body body) {
        List<Unit> units = new ArrayList<>(body.getUnits());
        Map<Unit, Integer> positions = new IdentityHashMap<>();
        for (int index = 0; index < units.size(); index++) {
            positions.put(units.get(index), index);
        }
        List<CfgLoopControl.NaturalLoop> loops = CfgLoopControl.naturalLoops(
                CfgLoopControl.loopCfg(body),
                unit -> positions.getOrDefault(unit, -1));
        assertEquals(1, loops.size());
        return loops.get(0);
    }

    private static String site(SootMethod method, int unitIndex) {
        return SiteId.of(method.getSignature(),
                unitIndex);
    }

    private static Map<String, Object> edge(
            String method, String transfer, String from, String to,
            String invoke) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("method", method);
        edge.put("transferKind", transfer);
        edge.put("kind", transfer.toLowerCase());
        edge.put("fromCell", from);
        edge.put("toCell", to);
        if (!invoke.isEmpty()) edge.put("invoke", invoke);
        return edge;
    }

    private static List<Unit> uniquePath(Body body, Unit start, Unit end) {
        BriefUnitGraph graph = new BriefUnitGraph(body);
        List<Unit> path = new ArrayList<>();
        Unit current = start;
        for (int remaining = body.getUnits().size(); remaining > 0;
                remaining--) {
            path.add(current);
            if (current == end) return path;
            List<Unit> successors = graph.getSuccsOf(current);
            assertEquals(1, successors.size());
            current = successors.get(0);
        }
        throw new AssertionError("path did not reach loop header");
    }

    private static void tagOriginalUnits(List<Unit> units) throws Exception {
        Method tag = CausynthPipeline.class.getDeclaredMethod(
                "tagOriginalUnits", List.class);
        tag.setAccessible(true);
        tag.invoke(null, units);
    }
}
