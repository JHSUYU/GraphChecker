package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import soot.Body;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.toolkits.graph.BriefUnitGraph;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SymbolicRegionPlannerTest {
    @Before
    public void resetBefore() {
        soot.G.reset();
    }

    @After
    public void resetAfter() {
        soot.G.reset();
    }

    private static final String ROOT = "<example.Root: void run()>";
    private static final String TARGET = "<example.Target: void fail()>";
    private static final String ASYNC = "<example.Worker: void run()>";
    private static final String COMMUNICATION =
            "<example.Client: int request()>";
    private static final String CALLBACK =
            "<example.Callback: void handle(java.lang.Object)>";
    private static final String WRITER = "<example.Store: void update(int)>";
    private static final String STATE = "<example.Store: int state>";

    @Test
    public void partitionsMethodsAndStopsBeforeStatePlanning() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, TARGET, "VALUE_PASS", "local", "x",
                "y"));
        program.edges.add(edge(TARGET, "", "GUARD", "exception_guard",
                "guard", TARGET + "#u7#exception:Failure"));
        program.edges.add(edge(TARGET, ASYNC, "DYNAMIC_DISPATCH", "dispatch",
                "task", "receiver"));
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");
        program.executionContextAuthorities.put(ASYNC, "TASK_ENTRY");
        program.targetResolved.put("method", TARGET);

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, TARGET, ASYNC));

        // The exact target is a boundary, so the execution-context envelope
        // cannot absorb the complete path leading to the failure.
        assertEquals(3, program.regions.size());
        Map<String, Object> target = regionContaining(program, TARGET);
        assertEquals(3, target.get("schemaVersion"));
        assertEquals("REGION_SKELETON", target.get("kind"));
        assertEquals(TARGET, target.get("rootMethod"));
        assertEquals("FAILURE_TARGET_ENTRY", target.get("rootAuthority"));
        assertEquals(TARGET, target.get("anchorMethod"));
        assertEquals(Collections.singletonList(TARGET),
                target.get("methods"));
        assertFalse(target.containsKey("symbolicInputs"));
        assertFalse(target.containsKey("outputs"));
        assertFalse(target.containsKey("branchPolicies"));
        assertFalse(target.containsKey("fieldPath"));
        Map<String, Object> async = regionContaining(program, ASYNC);
        assertEquals("AUTHORITY_ENVELOPE", async.get("selection"));
        assertTrue(program.regionEdges.isEmpty());

        // A target only a platform callback reaches has no execution-context
        // entry above it, so its own activation is the region.
        StaticProgram unreached = new StaticProgram();
        unreached.edges.add(edge(CALLBACK, TARGET, "VALUE_PASS", "local", "x",
                "y"));
        unreached.edges.add(edge(TARGET, "", "GUARD", "exception_guard",
                "guard", TARGET + "#u7#exception:Failure"));
        unreached.targetResolved.put("method", TARGET);

        SymbolicRegionPlanner.planSelectedSkeleton(unreached,
                Arrays.asList(CALLBACK, TARGET));

        assertEquals(1, unreached.regions.size());
        Map<String, Object> activation = unreached.regions.get(0);
        assertEquals(TARGET, activation.get("rootMethod"));
        assertEquals("FAILURE_TARGET_ENTRY", activation.get("rootAuthority"));
        assertEquals(TARGET, activation.get("anchorMethod"));
        assertEquals("EXCEPTION_CONTEXT", activation.get("selection"));
        assertEquals(Collections.singletonList(TARGET),
                activation.get(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE));

        // Folded from CfgLoopControlTest#naturalLoopExitIsControlButBodyPredicateIsSemantic:
        // the loop-control contract.
        SootClass owner = new SootClass("example.Loop", Modifier.PUBLIC);
        SootMethod method = new SootMethod("run", Collections.emptyList(),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local running = Jimple.v().newLocal("running", IntType.v());
        Local expiry = Jimple.v().newLocal("expiry", IntType.v());
        Local now = Jimple.v().newLocal("now", IntType.v());
        Local changed = Jimple.v().newLocal("changed", IntType.v());
        body.getLocals().add(running);
        body.getLocals().add(expiry);
        body.getLocals().add(now);
        body.getLocals().add(changed);

        Unit exit = Jimple.v().newReturnVoidStmt();
        Unit loopGuard = Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(running, IntConstant.v(0)), exit);
        Unit latch = Jimple.v().newGotoStmt(loopGuard);
        Unit semanticGuard = Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(expiry, now), latch);
        body.getUnits().add(loopGuard);
        body.getUnits().add(semanticGuard);
        body.getUnits().add(Jimple.v().newAssignStmt(
                changed, IntConstant.v(1)));
        body.getUnits().add(latch);
        body.getUnits().add(exit);

        Set<Unit> guards = CfgLoopControl.guards(
                CfgLoopControl.loopCfg(body, new BriefUnitGraph(body)));
        assertTrue(guards.contains(loopGuard));
        assertFalse(guards.contains(semanticGuard));
    }

    @Test
    @SuppressWarnings("unchecked")
    public void targetBoundarySeparatesCommunicationDemand() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, TARGET, "VALUE_PASS", "local", "x",
                "y"));
        program.edges.add(edge(ROOT, COMMUNICATION, "VALUE_PASS", "local",
                "request", "reply"));
        program.edges.add(edge(TARGET, "", "GUARD", "exception_guard",
                "guard", TARGET + "#u7#exception:Failure"));
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");
        program.targetResolved.put("method", TARGET);
        Map<String, Object> communication = new LinkedHashMap<>();
        Map<String, Object> producer = new LinkedHashMap<>();
        producer.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                COMMUNICATION);
        communication.put(WireFlowCatalog.PRODUCER, producer);
        program.communicationCallSites.add(communication);

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, TARGET, COMMUNICATION));

        Map<String, Object> region = regionContaining(program, COMMUNICATION);
        assertTrue(((List<String>) region.get("methods"))
                .contains(COMMUNICATION));
        List<String> demanded = (List<String>) region.get(
                RuntimeSelectedRegionFinalizer.DEMAND_SCOPE);
        assertTrue(demanded.contains(ROOT));
        assertTrue(demanded.contains(COMMUNICATION));
        assertFalse(demanded.contains(TARGET));
        assertEquals(TARGET,
                regionContaining(program, TARGET).get("rootMethod"));
    }

    @Test
    public void rootsAnUnownedFailureRelevantStateWriter() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(TARGET, "", "HEAP_READ", "field_read",
                STATE, TARGET + "::value"));
        program.edges.add(edge(TARGET, "", "GUARD", "exception_guard",
                TARGET + "::value", TARGET + "#u7#exception:Failure"));
        program.edges.add(edge(WRITER, "", "HEAP_WRITE", "field_write",
                WRITER + ".param0:int", STATE));
        program.targetResolved.put("method", TARGET);

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(TARGET, WRITER));

        Map<String, Object> writer = regionContaining(program, WRITER);
        assertEquals(SymbolicRegionPlanner.STATE_WRITER_ENTRY,
                writer.get("rootAuthority"));
        assertEquals("STATE_CONTEXT", writer.get("selection"));
        assertEquals(Collections.singletonList(WRITER),
                writer.get("methods"));
    }

    private static Map<String, Object> edge(
            String method, String invoke, String transfer, String kind,
            String from, String to) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("schemaVersion", 3);
        result.put("method", method);
        if (!invoke.isEmpty()) {
            result.put("invoke", invoke);
        }
        result.put("transferKind", transfer);
        result.put("kind", kind);
        result.put("fromCell", from);
        result.put("toCell", to);
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> regionContaining(
            StaticProgram program, String method) {
        for (Map<String, Object> region : program.regions) {
            if (((java.util.List<String>) region.get("methods"))
                    .contains(method)) {
                return region;
            }
        }
        throw new AssertionError("missing region for " + method);
    }
}
