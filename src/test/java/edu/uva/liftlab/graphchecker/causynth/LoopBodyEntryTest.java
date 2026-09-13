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
     * A wire producer called from a loop body is rooted at the loop, not at
     * the endpoint: one iteration exports one value, so the endpoint alone
     * would be entered once per value with nothing but a process-wide
     * ordinal to tell the activations apart.
     */
    @Test
    public void wireProducerInALoopBodyRootsAtTheLoopHoldingCaller() {
        StaticProgram program = wireProducerSlice();

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(TASK, EXPORTER, ELEMENT, RECEIVER, TARGET));

        Map<String, Object> producerRegion = null;
        for (Map<String, Object> region : program.regions) {
            assertTrue("no region may be rooted at the endpoint itself",
                    !ELEMENT.equals(region.get("rootMethod")));
            if (EXPORTER.equals(region.get("rootMethod"))) {
                producerRegion = region;
            }
        }
        assertEquals("COMMUNICATION_ENTRY",
                producerRegion == null ? null
                        : producerRegion.get("rootAuthority"));
        assertTrue(((List<?>) producerRegion.get("methods"))
                .contains(ELEMENT));
        assertEquals(1, ((List<?>) producerRegion.get(
                RuntimeSelectedRegionFinalizer.RETAINED_LOOPS)).size());
        assertEquals(1, ((List<?>) producerRegion.get(
                RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS)).size());
    }

    /** A producer no loop calls keeps the endpoint as its own root. */
    @Test
    public void wireProducerOutsideAnyLoopKeepsTheEndpointRoot() {
        StaticProgram program = wireProducerSlice();
        program.retainedLoops.clear();

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(TASK, EXPORTER, ELEMENT, RECEIVER, TARGET));

        Map<String, Object> endpointRegion = null;
        for (Map<String, Object> region : program.regions) {
            if (ELEMENT.equals(region.get("rootMethod"))) {
                endpointRegion = region;
            }
        }
        assertEquals("COMMUNICATION_ENTRY",
                endpointRegion == null ? null
                        : endpointRegion.get("rootAuthority"));
    }

    /**
     * An exactly-counted loop names its iteration only when the slice demands
     * that iteration: a wire port the body produces, or a declared field the
     * body writes.  An indexed walk that carries neither stays what its
     * javadoc says it is -- not a service loop.
     */
    @Test
    public void exactlyCountedLoopIsAServiceLoopOnlyWhenItCarriesDemand() {
        assertEquals(EXPORTER, rootLoopMethod(
                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, true, false));
        assertEquals(EXPORTER, rootLoopMethod(
                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, false, true));
        assertEquals(null, rootLoopMethod(
                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED, false, false));
        // The condition-bounded rule is unchanged: it needs no demand.
        assertEquals(EXPORTER, rootLoopMethod(
                LoopBoundPolicy.LOOP_CONDITION_BOUNDED, false, false));
    }

    private static final String TASK = "<example.Task: void run()>";
    private static final String EXPORTER =
            "<example.Wire: example.Message convert(java.util.List)>";
    private static final String ELEMENT =
            "<example.Wire: example.Element convert(example.Key)>";
    private static final String RECEIVER =
            "<example.Wire: example.Key convert(example.Element)>";
    private static final String TARGET = "<example.Target: void fail()>";
    private static final String STATE = "<example.Store: int value>";
    private static final String SETTER =
            "<example.Element$Builder: void setId(int)>";
    private static final String PORT = "XCH.test.resp.element-id";

    /**
     * The producer half runs on the far side of the wire, so no execution
     * context of the failing node holds it: {@code convert(List)} walks its
     * elements and each iteration calls {@code convert(Key)}, which captures
     * one wire value.
     */
    private static StaticProgram wireProducerSlice() {
        StaticProgram program = new StaticProgram();
        program.executionContextAuthorities.put(TASK, "TASK_ENTRY");
        program.targetResolved.put("method", TARGET);
        program.edges.add(callEdge(TASK, RECEIVER, 1));
        program.edges.add(callEdge(TASK, TARGET, 2));
        program.edges.add(callEdge(EXPORTER, ELEMENT, 5));
        Map<String, Object> read = edge(ELEMENT, "HEAP_READ", STATE,
                ELEMENT + "::id", "");
        read.put("unitIndex", 8);
        program.edges.add(read);
        program.edges.add(edge(TARGET, "HEAP_READ", STATE,
                TARGET + "::value", ""));
        program.edges.add(edge(TARGET, "GUARD", TARGET + "::value",
                TARGET + "#u7#exception:Failure", ""));
        program.communicationCallSites.add(wireFlow());
        program.communicationCallSiteCallees.add(SETTER);
        program.retainedLoops.add(loop(
                LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED));
        return program;
    }

    /** One declared response value produced per loop iteration. */
    private static Map<String, Object> wireFlow() {
        Map<String, Object> producer = new LinkedHashMap<>();
        producer.put(CommunicationCatalogContract.CALL_SITE_ID,
                SiteId.of(ELEMENT, 9));
        producer.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                ELEMENT);
        producer.put(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT);
        producer.put(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX,
                9);
        producer.put(CommunicationCatalogContract.DECLARED_CALLEE, SETTER);
        producer.put(CommunicationCatalogContract.PORT_ARGUMENT_INDEX, 0);
        Map<String, Object> consumer = new LinkedHashMap<>(producer);
        consumer.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                RECEIVER);
        consumer.put(CommunicationCatalogContract.CALL_SITE_ID,
                SiteId.of(RECEIVER, 2));
        Map<String, Object> flow = new LinkedHashMap<>();
        flow.put(CommunicationCatalogContract.PORT_ID, PORT);
        flow.put(CommunicationCatalogContract.PORT_NAME, "element-id");
        flow.put(CommunicationCatalogContract.PORT_JAVA_TYPE, "int");
        flow.put(CommunicationCatalogContract.TRANSPORT, "TEST_RPC");
        flow.put(CommunicationCatalogContract.PORT_DIRECTION,
                CommunicationCatalogContract.DIRECTION_RESPONSE);
        flow.put(CommunicationCatalogContract.EXCHANGE_SITE_KEY, "XCH.test");
        flow.put(CommunicationCatalogContract.CALL_SITE_ID,
                SiteId.of(ELEMENT, 9));
        flow.put("javaType", "int");
        flow.put(WireFlowCatalog.PRODUCER, producer);
        flow.put(WireFlowCatalog.CONSUMER, consumer);
        return flow;
    }

    private static Map<String, Object> loop(String classification) {
        Map<String, Object> loop = new LinkedHashMap<>();
        loop.put("schemaVersion", 4);
        loop.put("kind", "RETAINED_LOOP");
        loop.put("enclosingMethod", EXPORTER);
        loop.put(LoopBoundPolicy.LOOP_SITE_ID, SiteId.of(EXPORTER, 4));
        loop.put(LoopBoundPolicy.RUNTIME_LOOP_ID, EXPORTER + "#loop:u4");
        loop.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS,
                Collections.singletonList(SiteId.of(EXPORTER, 4)));
        loop.put(LoopBoundPolicy.LOOP_LATCH_UNIT_INDEX, 8);
        loop.put(LoopBoundPolicy.LOOP_CLASSIFICATION, classification);
        return loop;
    }

    /**
     * The method {@link StaticProgram#loopBodyRoot} names for a region whose
     * only loop has {@code classification}, or {@code null} when it names
     * none.
     */
    private static String rootLoopMethod(String classification,
                                         boolean declaresPort,
                                         boolean writesField) {
        StaticProgram program = new StaticProgram();
        String regionId = "REGION.test";
        Map<String, Object> call = callEdge(EXPORTER, ELEMENT, 5);
        call.put("regionIds", Collections.singletonList(regionId));
        List<Map<String, Object>> graph = new ArrayList<>();
        graph.add(call);
        if (writesField) {
            Map<String, Object> write = edge(EXPORTER, "HEAP_WRITE",
                    EXPORTER + "::id", STATE, "");
            write.put("unitIndex", 6);
            write.put("regionIds", Collections.singletonList(regionId));
            graph.add(write);
        }
        program.refinedGraph = graph;

        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion",
                RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION);
        row.put("kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND);
        row.put("regionId", regionId);
        row.put("rootMethod", EXPORTER);
        row.put("rootAuthority", "COMMUNICATION_ENTRY");
        row.put("anchorMethod", ELEMENT);
        row.put("methods", Arrays.asList(ELEMENT, EXPORTER));
        row.put(RuntimeSelectedRegionFinalizer.RETAINED_LOOPS,
                Collections.singletonList(loop(classification)));
        if (declaresPort) {
            Map<String, Object> port = new LinkedHashMap<>();
            port.put(CommunicationCatalogContract.PORT_ID, PORT);
            port.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                    ELEMENT);
            row.put(RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS,
                    Collections.singletonList(port));
        }
        StaticProgram.RegionRow skeleton = StaticProgram.regionRows(
                Collections.singletonList(row),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                "test").get(0);

        Map<String, Object> activation = new LinkedHashMap<>();
        activation.put("regionId", regionId);
        activation.put("callIds", Collections.singletonList(11L));
        List<Map<String, Object>> branches = new ArrayList<>();
        for (int decision = 0; decision < 2; decision++) {
            Map<String, Object> observation = new LinkedHashMap<>();
            observation.put("siteId", SiteId.of(EXPORTER, 4));
            observation.put("callId", 11L);
            branches.add(observation);
        }
        Map<String, Object> rootLoop = program.loopBodyRoot(skeleton,
                Collections.singletonList(activation), branches);
        return rootLoop == null ? null
                : String.valueOf(rootLoop.get(
                        LoopBoundPolicy.ROOT_LOOP_METHOD));
    }

    private static Map<String, Object> callEdge(String caller, String callee,
                                                int unitIndex) {
        Map<String, Object> edge = edge(caller, "VALUE_PASS",
                caller + "::argument", callee + ".param0:int", callee);
        edge.put("unitIndex", unitIndex);
        return edge;
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
