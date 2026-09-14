package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.AutomaticRegionEdge;
import edu.uva.liftlab.graphchecker.concolic.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.SiteId;
import edu.uva.liftlab.graphchecker.runtime.OccurrenceMinter;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
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
import org.junit.After;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.ByteType;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.StringConstant;
import soot.toolkits.graph.BriefUnitGraph;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * The region graph joins on an address, and refuses anything else.
 *
 * <p>These joins decide which rows belong to one occurrence.  They did it by
 * string equality on {@code occurrenceId}, which is correct exactly while
 * every id they see is a planned address, and silently merges two activations
 * the moment one carries an {@code #a<n>} suffix -- the address drops the
 * suffix and the string does not.  Refusing is the point: a merge here is
 * invisible, and a graph that cannot be built says so.</p>
 */
public class RegionGraphOccurrenceKeyTest {
    private static final String PLANNED =
            "hdfs-17960/nn0#epoch1/region/"
                    + "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d#1";

    /** A planned address keys as itself: the migration is byte-neutral. */
    @Test
    public void regionGraphOccurrenceKeyRules() throws Exception {
        aPlannedAddressKeysAsItself();
        anAbsentIdIsNotAnError();
        anActivationSuffixIsRefused();
        anUnreadableIdIsRefused();
        RecordedExchangeEdgeIdentityTest t0 =
                new RecordedExchangeEdgeIdentityTest();
        t0.recordedExchangeEdgeIdentityRules();
        LoopBodyEntryTest t1 =
                new LoopBodyEntryTest();
        try {
            t1.wireProducerInALoopBodyRootsAtTheLoopHoldingCaller();
        } finally {
            t1.resetSoot();
        }
        ConcolicAtomicCarrierSelectionTest t2 =
                new ConcolicAtomicCarrierSelectionTest();
        t2.explicitFaultIsAControlRootOutsideFatalValueSlice();
        RuntimeSelectedRegionFinalizerAccessorTest t3 =
                new RuntimeSelectedRegionFinalizerAccessorTest();
        t3.runtimeSelectedRegionFinalizerAccessorRules();
    }

    private void aPlannedAddressKeysAsItself() {
        assertEquals(PLANNED,
                RuntimeSelectedRegionFinalizer.occurrenceKey(PLANNED));
    }

    /** An absent id is still absent, so the callers' early returns stand. */
    private void anAbsentIdIsNotAnError() {
        assertEquals("", RuntimeSelectedRegionFinalizer.occurrenceKey(null));
        assertEquals("", RuntimeSelectedRegionFinalizer.occurrenceKey(""));
    }

    /** A per-activation id is refused rather than merged onto its address. */
    private void anActivationSuffixIsRefused() {
        refuses(PLANNED + "#a1");
    }

    /** So is anything that does not spell an address at all. */
    private void anUnreadableIdIsRefused() {
        refuses("REGION.9492ec77");
        refuses("hdfs-17960/nn0#epoch1/region/REGION.1");
        refuses("hdfs-17960/nn0#epoch1/region/REGION.1#0");
    }

    private static void refuses(String occurrenceId) {
        try {
            RuntimeSelectedRegionFinalizer.occurrenceKey(occurrenceId);
            fail("expected a refusal for " + occurrenceId);
        } catch (IllegalArgumentException refused) {
            assertEquals(true, refused.getMessage().contains(occurrenceId));
        }
    }

    /**
     * What names a recorded exchange edge across two recordings of one workload.
     *
     * <p>An {@code RPC.} producer edge and the {@code CTRL.} request-control edge
     * that depends on it used to be named from the wire transaction the exchange
     * ran on: Hadoop's IPC client id and call number
     * ({@code hadoop-ipc-f76d5ada...-21}) or a SASL negotiation uuid
     * ({@code hdfs-sasl-e21aa975-...}).  The workload mints those fresh in every
     * run, so two recordings of hdfs-17899/bug3 published a different
     * {@code RPC.}/{@code CTRL.} id for the same exchange, and the 25 plan rows
     * that bind those edges differed by name alone.</p>
     *
     * <p>The transaction stays on the edge as recorded transport evidence.  It is
     * no longer part of the edge's name: the producing and consuming occurrence,
     * the port, the direction and an ordinal counted over that tuple say which
     * exchange this is in terms the next recording reproduces.</p>
     */
    static final class RecordedExchangeEdgeIdentityTest {
        private static final String SITE =
                "hdfs-17899/nn0#epoch0/region/REGION.a#1\n"
                        + "hdfs-17899/source-dn#epoch0/region/REGION.b#1\n"
                        + "REGION.b.in.port\nREQUEST";
        private static final String OTHER_SITE =
                "hdfs-17899/nn0#epoch0/region/REGION.a#2\n"
                        + "hdfs-17899/source-dn#epoch0/region/REGION.b#1\n"
                        + "REGION.b.in.port\nREQUEST";

        /** The one transaction of one exchange site is exchange number one. */
        public void recordedExchangeEdgeIdentityRules() throws Exception {
            twoRecordingsNumberOneExchangeAlike();
            requestControlEdgeIdIgnoresTheWireTransaction();
        }

        private void twoRecordingsNumberOneExchangeAlike() {
            assertNotEquals("the wire transactions of two recordings are "
                            + "expected to differ",
                    "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0",
                    "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0");

            assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                    new LinkedHashMap<>(), SITE,
                    "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0"));
            assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                    new LinkedHashMap<>(), SITE,
                    "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0"));
        }

        /**
         * A request-control edge is named by the response edge, not the wire.
         *
         * <p>The response edge already names the exchange from content, and it
         * names it more exactly than the transaction does, because each retry of
         * one logical request has its own response edge.</p>
         */
        private void requestControlEdgeIdIgnoresTheWireTransaction() throws Exception {
            String first = controlEdgeId(
                    "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0");
            String second = controlEdgeId(
                    "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0");

            assertEquals("two recordings of one request fault must publish one "
                    + "control edge name", first, second);
        }

        private static String controlEdgeId(String transaction) throws Exception {
            return controlEdgeId(transaction, "RPC.response");
        }

        @SuppressWarnings("unchecked")
        private static String controlEdgeId(String transaction,
                                            String responseEdgeId)
                throws Exception {
            Method edge = RuntimeSelectedRegionFinalizer.class
                    .getDeclaredMethod("requestFaultControlEdge", Map.class,
                            Map.class, Map.class, Map.class, Map.class,
                            String.class, String.class, long.class, long.class,
                            long.class, long.class, long.class);
            edge.setAccessible(true);
            Map<String, Object> result = (Map<String, Object>) edge.invoke(null,
                    row("occurrenceId", "hdfs-17899/nn0#epoch0/region/REGION.f#1",
                            "regionId", "REGION.f", "rootCallId", 11L),
                    row("occurrenceId", "hdfs-17899/nn0#epoch0/region/REGION.c#1",
                            "regionId", "REGION.c", "rootCallId", 12L),
                    row("portId", "REGION.c.in.port", "symbolicName", "S1"),
                    row("edgeId", "RPC.request", "requestKey", "rk",
                            "attemptId", "a1"),
                    row("edgeId", responseEdgeId),
                    transaction, "hdfs-17899/nn0#epoch0",
                    1L, 2L, 3L, 4L, 5L);
            return String.valueOf(result.get("edgeId"));
        }

        private static Map<String, Object> row(Object... fields) {
            Map<String, Object> result = new LinkedHashMap<>();
            for (int index = 0; index < fields.length; index += 2) {
                result.put((String) fields[index], fields[index + 1]);
            }
            return result;
        }
    }


    static final class LoopBodyEntryTest {

        public void resetSoot() {
            G.reset();
        }

        /**
         * A wire producer called from a loop body is rooted at the loop, not at
         * the endpoint: one iteration exports one value, so the endpoint alone
         * would be entered once per value with nothing but a process-wide
         * ordinal to tell the activations apart.
         */
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


    static final class ConcolicAtomicCarrierSelectionTest {
        private static final String INT_VALUE =
                "<java.util.concurrent.atomic.AtomicInteger: int value>";
        private static final String LONG_VALUE =
                "<java.util.concurrent.atomic.AtomicLong: long value>";

        public void explicitFaultIsAControlRootOutsideFatalValueSlice()
                throws Exception {
            soot.G.reset();
            System.clearProperty(WireFlowCatalog.PROPERTY);
            try {
                SootClass object = type("java.lang.Object", null, false);
                SootClass string = type("java.lang.String", object, false);
                SootClass runtimeException = type("java.lang.RuntimeException",
                        object, false);
                SootMethod runtimeConstructor = constructor(runtimeException,
                        null);
                SootClass failure = type("example.RootFailure",
                        runtimeException, true);
                SootMethod failureConstructor = constructor(failure,
                        runtimeConstructor);

                SootClass debug = type(
                        "edu.uva.liftlab.graphchecker.annotation.Debug",
                        object, false);
                SootMethod marker = new SootMethod("makeSymbolicBoolean",
                        Collections.singletonList(RefType.v(string.getName())),
                        BooleanType.v(), Modifier.PUBLIC | Modifier.STATIC);
                debug.addMethod(marker);

                SootClass owner = type("example.ExplicitFaultComponent",
                        object, true);
                SootMethod target = unconditionalFailure(owner, "target",
                        failure, failureConstructor);
                SootMethod fault = explicitFaultFailure(owner, marker,
                        failure, failureConstructor);
                ExceptionTargetSite site = new ExceptionTargetSite(
                        "explicit-fault-root", owner.getName(),
                        target.getName(), "()V", target.getSignature(),
                        failure.getName(), 0);

                StaticProgram program = new SeedBackwardStaticAnalyzer(
                        new CausynthTargetContext(null, site.id, site))
                        .analyze();

                String faultCell = fault.getSignature() + "::fault";
                assertTrue(program.traceMethods.contains(fault.getSignature()));
                assertTrue(program.edges.stream().anyMatch(edge ->
                        Boolean.TRUE.equals(edge.get("explicitSymbolicFault"))
                                && fault.getSignature().equals(
                                edge.get("method"))
                                && faultCell.equals(edge.get("toCell"))));
                assertTrue(program.edges.stream().anyMatch(edge ->
                        "guard_dependency".equals(edge.get("kind"))
                                && fault.getSignature().equals(
                                edge.get("method"))
                                && faultCell.equals(edge.get("fromCell"))));

                SymbolicRegionPlanner.planSelectedSkeleton(program,
                        program.traceMethods);
                assertTrue(program.regions.stream().anyMatch(region ->
                        fault.getSignature().equals(region.get("rootMethod"))
                                && SymbolicRegionPlanner.EXPLICIT_FAULT_ENTRY
                                .equals(region.get("rootAuthority"))
                                && "EXPLICIT_FAULT_CONTEXT".equals(
                                region.get("selection"))));
            } finally {
                System.clearProperty(WireFlowCatalog.PROPERTY);
                soot.G.reset();
            }
        }

        private static ConcolicInstrumentationSelections
                .ConcolicMaterializationSelection selection(
                String owner, String name, String descriptor) throws Exception {
            JsonObject carrier = carrier(owner, name, descriptor);
            JsonArray carriers = new JsonArray();
            carriers.add(carrier);
            ConcolicInstrumentationSelections.ConcolicMaterializationSelection
                    selection = new ConcolicInstrumentationSelections
                    .ConcolicMaterializationSelection();
            selection.addSharedCarrierTargets(carriers, new JsonArray());
            return selection;
        }

        private static JsonObject carrier(
                String owner, String name, String descriptor) {
            JsonObject carrier = new JsonObject();
            carrier.addProperty("kind", "DECLARED_FIELD");
            carrier.addProperty("declaringClass", owner);
            carrier.addProperty("fieldName", name);
            carrier.addProperty("descriptor", descriptor);
            carrier.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
            carrier.add("fieldPath", new JsonArray());
            return carrier;
        }

        private static JsonObject concreteFieldRead(
                String fieldSignature, String site) {
            JsonObject action = new JsonObject();
            action.addProperty("mode", "CONCRETE");
            action.addProperty("bindingMode", "FIELD_ACCESS");
            action.addProperty("location", "HEAP_OBJECT_FIELD");
            action.addProperty("accessFieldSignature", fieldSignature);
            action.addProperty("staticAccessSiteId", site);
            return action;
        }

        private static SootMethod lookupTarget(
                SootClass owner, SootClass stateType, SootClass mapType,
                SootClass memberType, SootField entries, SootField value,
                SootMethod get, SootClass failure, SootMethod failureConstructor) {
            SootMethod method = new SootMethod("failWhenMissing", Arrays.asList(
                    RefType.v(stateType.getName()), RefType.v("java.lang.Object")),
                    VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
            owner.addMethod(method);
            Body body = Jimple.v().newBody(method);
            method.setActiveBody(body);
            Local state = local(body, "state", RefType.v(stateType.getName()));
            Local key = local(body, "key", RefType.v("java.lang.Object"));
            Local map = local(body, "map", RefType.v(mapType.getName()));
            Local raw = local(body, "raw", RefType.v("java.lang.Object"));
            Local member = local(body, "member", RefType.v(memberType.getName()));
            Local primitive = local(body, "primitive", IntType.v());
            Local thrown = local(body, "thrown", RefType.v(failure.getName()));
            body.getUnits().add(Jimple.v().newIdentityStmt(state,
                    Jimple.v().newParameterRef((RefType) state.getType(), 0)));
            body.getUnits().add(Jimple.v().newIdentityStmt(key,
                    Jimple.v().newParameterRef((RefType) key.getType(), 1)));
            body.getUnits().add(Jimple.v().newAssignStmt(map,
                    Jimple.v().newInstanceFieldRef(state, entries.makeRef())));
            body.getUnits().add(Jimple.v().newAssignStmt(raw,
                    Jimple.v().newInterfaceInvokeExpr(map, get.makeRef(), key)));
            body.getUnits().add(Jimple.v().newAssignStmt(member,
                    Jimple.v().newCastExpr(raw, member.getType())));
            Unit dereference = Jimple.v().newAssignStmt(primitive,
                    Jimple.v().newInstanceFieldRef(member, value.makeRef()));
            body.getUnits().add(Jimple.v().newIfStmt(
                    Jimple.v().newNeExpr(member, soot.jimple.NullConstant.v()),
                    dereference));
            body.getUnits().add(Jimple.v().newAssignStmt(thrown,
                    Jimple.v().newNewExpr(RefType.v(failure.getName()))));
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newSpecialInvokeExpr(thrown,
                            failureConstructor.makeRef())));
            body.getUnits().add(Jimple.v().newThrowStmt(thrown));
            body.getUnits().add(dereference);
            body.getUnits().add(Jimple.v().newReturnVoidStmt());
            return method;
        }

        private static SootMethod unconditionalFailure(
                SootClass owner, String name, SootClass failure,
                SootMethod failureConstructor) {
            SootMethod method = new SootMethod(name, Collections.emptyList(),
                    VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
            owner.addMethod(method);
            Body body = Jimple.v().newBody(method);
            method.setActiveBody(body);
            Local thrown = local(body, "targetThrown",
                    RefType.v(failure.getName()));
            body.getUnits().add(Jimple.v().newAssignStmt(thrown,
                    Jimple.v().newNewExpr(RefType.v(failure.getName()))));
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newSpecialInvokeExpr(thrown,
                            failureConstructor.makeRef())));
            body.getUnits().add(Jimple.v().newThrowStmt(thrown));
            return method;
        }

        private static SootMethod explicitFaultFailure(
                SootClass owner, SootMethod marker, SootClass failure,
                SootMethod failureConstructor) {
            SootMethod method = new SootMethod("transport",
                    Collections.emptyList(), VoidType.v(),
                    Modifier.PUBLIC | Modifier.STATIC);
            owner.addMethod(method);
            Body body = Jimple.v().newBody(method);
            method.setActiveBody(body);
            Local fault = local(body, "fault", BooleanType.v());
            Local thrown = local(body, "faultThrown",
                    RefType.v(failure.getName()));
            Unit normal = Jimple.v().newReturnVoidStmt();
            body.getUnits().add(Jimple.v().newAssignStmt(fault,
                    Jimple.v().newStaticInvokeExpr(marker.makeRef(),
                            StringConstant.v("transport-fault"))));
            body.getUnits().add(Jimple.v().newIfStmt(
                    Jimple.v().newEqExpr(fault, soot.jimple.IntConstant.v(0)),
                    normal));
            body.getUnits().add(Jimple.v().newAssignStmt(thrown,
                    Jimple.v().newNewExpr(RefType.v(failure.getName()))));
            body.getUnits().add(Jimple.v().newInvokeStmt(
                    Jimple.v().newSpecialInvokeExpr(thrown,
                            failureConstructor.makeRef())));
            body.getUnits().add(Jimple.v().newThrowStmt(thrown));
            body.getUnits().add(normal);
            return method;
        }

        private static SootClass type(String name, SootClass parent,
                                      boolean application) {
            SootClass result = new SootClass(name, Modifier.PUBLIC);
            if (parent != null) result.setSuperclass(parent);
            Scene.v().addClass(result);
            if (application) result.setApplicationClass();
            else result.setLibraryClass();
            return result;
        }

        private static SootMethod constructor(SootClass owner,
                                              SootMethod parent) {
            SootMethod constructor = new SootMethod("<init>",
                    Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
            owner.addMethod(constructor);
            if (parent != null) {
                Body body = Jimple.v().newBody(constructor);
                constructor.setActiveBody(body);
                Local self = local(body, "this", RefType.v(owner.getName()));
                body.getUnits().add(Jimple.v().newIdentityStmt(self,
                        Jimple.v().newThisRef((RefType) self.getType())));
                body.getUnits().add(Jimple.v().newInvokeStmt(
                        Jimple.v().newSpecialInvokeExpr(self, parent.makeRef())));
                body.getUnits().add(Jimple.v().newReturnVoidStmt());
            }
            return constructor;
        }

        private static Local local(Body body, String name, soot.Type type) {
            Local local = Jimple.v().newLocal(name, type);
            body.getLocals().add(local);
            return local;
        }
    }


    static final class RuntimeSelectedRegionFinalizerAccessorTest {
        private static final String REGION = "REGION.reader";
        private static final String METHOD = "<example.Reader: void run()>";
        private static final String CALLEE = "<example.Value: long getValue()>";
        private static final String SITE = METHOD + "#u12";
        private static final String RETURN = CALLEE + ".return";
        private static final String LOCAL = METHOD + "::$l1";

        private static final String FAULT_OCCURRENCE =
                "source/region/REGION.fault#1";
        private static final String CONSUMER_OCCURRENCE =
                "source/region/REGION.consumer#1";
        private static final String TARGET_OCCURRENCE =
                "target/region/REGION.target#1";
        private static final String TARGET_FAULT_OCCURRENCE =
                "target/region/REGION.fault#1";
        private static final String TARGET_STATE_OCCURRENCE =
                "target/region/REGION.consumer#1";
        private static final List<String> TWO_SIDED_FAULT_RETAINED =
                Arrays.asList("RPC.response", "RPC.target-input",
                        "RPC.target-state-response");

        /**
         * One request whose response supplies the value the fatal target checks,
         * and one request on the target's own node whose response maintains
         * target-local state.  Both fire the same fault marker.
         */
        private static StaticProgram twoSidedFaultProgram() {
            String faultOccurrence = FAULT_OCCURRENCE;
            String unrelatedOccurrence = "source/region/REGION.fault#2";
            String earlyOccurrence = "source/region/REGION.fault#3";
            String consumerOccurrence = CONSUMER_OCCURRENCE;
            String targetOccurrence = TARGET_OCCURRENCE;
            String targetFaultOccurrence = TARGET_FAULT_OCCURRENCE;
            String targetStateOccurrence = TARGET_STATE_OCCURRENCE;
            StaticProgram program = new StaticProgram();
            program.activations.put(faultOccurrence, activation(
                    "AF", "REGION.fault", faultOccurrence, "source", 10L));
            program.activations.put(unrelatedOccurrence, activation(
                    "AU", "REGION.fault", unrelatedOccurrence, "source", 20L));
            program.activations.put(earlyOccurrence, activation(
                    "AE", "REGION.fault", earlyOccurrence, "source", 25L));
            program.activations.put(consumerOccurrence, activation(
                    "AC", "REGION.consumer", consumerOccurrence, "source",
                    30L));
            Map<String, Object> target = activation(
                    "AT", "REGION.target", targetOccurrence, "target", 40L);
            target.put("selection", "EXCEPTION_CONTEXT");
            target.put("observedFatalTargets", Collections.singletonList(
                    row("eventSeq", 100L)));
            program.activations.put(targetOccurrence, target);
            program.activations.put(targetFaultOccurrence, activation(
                    "TF", "REGION.fault", targetFaultOccurrence, "target",
                    50L));
            program.activations.put(targetStateOccurrence, activation(
                    "TC", "REGION.consumer", targetStateOccurrence, "target",
                    60L));
            program.regions.add(row(
                    "regionId", "REGION.fault",
                    "symbolicInputs", Arrays.asList(
                            faultPort(faultOccurrence, "PORT.fault", 2L),
                            faultPort(unrelatedOccurrence, "PORT.unrelated", 12L),
                            faultPort(earlyOccurrence, "PORT.early", 1L),
                            faultPort(targetFaultOccurrence,
                                    "PORT.target-state", 7L))));
            program.regions.add(row(
                    "regionId", "REGION.consumer",
                    "symbolicInputs", Collections.emptyList()));
            program.regions.add(row(
                    "regionId", "REGION.target",
                    "symbolicInputs", Collections.emptyList()));
            program.regionEdges.add(row(
                    "schemaVersion", 3,
                    "edgeId", "RPC.response",
                    "kind", "RUNTIME_PROTOCOL_FLOW",
                    "direction", "RESPONSE",
                    "fromOccurrenceId", "source/region/REGION.server#1",
                    "toOccurrenceId", consumerOccurrence,
                    "toRegion", "REGION.consumer",
                    "exchangeLeg", "exchange\n1\nRESPONSE",
                    "requestKey", "REQUEST.1",
                    "requestApi", "api",
                    "transportKind", "RPC",
                    "attemptId", "1",
                    "senderEventSeq", 4L,
                    "receiverEventSeq", 5L));
            program.regionEdges.add(row(
                    "schemaVersion", 3,
                    "edgeId", "RPC.target-input",
                    "kind", "RUNTIME_PROTOCOL_FLOW",
                    "direction", "REQUEST",
                    "dependencyRole", "VALUE_FRONTIER",
                    "fromOccurrenceId", consumerOccurrence,
                    "toOccurrenceId", targetOccurrence,
                    "fromRegion", "REGION.consumer",
                    "toRegion", "REGION.target"));
            program.regionEdges.add(row(
                    "schemaVersion", 3,
                    "edgeId", "RPC.target-state-response",
                    "kind", "RUNTIME_PROTOCOL_FLOW",
                    "direction", "RESPONSE",
                    "fromOccurrenceId", "target/region/REGION.server#1",
                    "toOccurrenceId", targetStateOccurrence,
                    "toRegion", "REGION.consumer",
                    "exchangeLeg", "target-state\n1\nRESPONSE",
                    "requestKey", "REQUEST.target-state",
                    "requestApi", "api",
                    "transportKind", "RPC",
                    "attemptId", "1",
                    "senderEventSeq", 9L,
                    "receiverEventSeq", 10L));
            return program;
        }

        private static List<Map<String, Object>> twoSidedFaultLinks() {
            return Arrays.asList(
                    requestLink("AF", "exchange\n1\nREQUEST", "REQUEST.1",
                            1L, 3L),
                    requestLink("AE", "exchange\n1\nREQUEST", "REQUEST.1",
                            1L, 3L),
                    requestLink("AU", "other\n1\nREQUEST", "REQUEST.2",
                            11L, 13L),
                    requestLink("TF", "target-state\n1\nREQUEST",
                            "REQUEST.target-state", 6L, 8L));
        }

        private static StaticProgram twoSidedFaultProgramWith(
                Map<String, Object> extraEdge) {
            StaticProgram program = twoSidedFaultProgram();
            program.regionEdges.add(extraEdge);
            return program;
        }

        /**
         * The care set is the intersection of the two conditions: a field must
         * appear on the backward slice AND be forward-reachable from a symbolic
         * root.  A field the slice names but no root reaches is a constant for
         * this failure and stays out.
         */
        public void runtimeSelectedRegionFinalizerAccessorRules() throws Exception {
            careSetKeepsOnlySliceFieldsASymbolicRootReaches();
            careSetTreatsWireHandoffAsASymbolicRoot();
        }

        private void careSetKeepsOnlySliceFieldsASymbolicRootReaches() {
            List<Map<String, Object>> graph = Arrays.asList(
                    // The fault symbol enters at the wire and flows to a cell
                    // that reads the rolled key.
                    row("kind", "explicit_symbolic_fault",
                            "explicitSymbolicFault", true,
                            "fromCell", "cell.fault", "toCell", "cell.request"),
                    row("kind", "field_read", "fromCell", "cell.request",
                            "toCell", "cell.key",
                            "declaredFieldSignature",
                            "<example.Owner: example.Key currentKey>"),
                    // On the slice, but nothing symbolic reaches it: a harness
                    // setter writing its own island.
                    row("kind", "field_write", "fromCell", "cell.harness",
                            "toCell", "cell.interval",
                            "declaredFieldSignature",
                            "<example.Owner: long keyUpdateInterval>"));

            Set<String> cared = RuntimeSelectedRegionFinalizer
                    .caredSharedLocations(graph);
            assertTrue(cared.contains("example.Owner#currentKey"));
            assertFalse(cared.contains("example.Owner#keyUpdateInterval"));
        }

        /** A wire attach point is a symbolic root of the same standing. */
        private void careSetTreatsWireHandoffAsASymbolicRoot() {
            List<Map<String, Object>> graph = Arrays.asList(
                    row("kind", "wire_handoff", "fromCell", "cell.send",
                            "toCell", "cell.receive"),
                    row("kind", "field_write", "fromCell", "cell.receive",
                            "toCell", "cell.keys",
                            "fieldPathDeclarations", Collections.singletonList(
                                    "<example.Owner: java.util.Map allKeys>")));
            assertTrue(RuntimeSelectedRegionFinalizer.caredSharedLocations(graph)
                    .contains("example.Owner#allKeys"));
        }

        private static Map<String, Object> demandActivation(
                String activationId, String regionId, String occurrenceId,
                String sourceKey) {
            return row(
                    "activationId", activationId,
                    "regionId", regionId,
                    "occurrenceId", occurrenceId,
                    "sourceKey", sourceKey);
        }

        private static Map<String, Object> fieldFlow(
                String edgeId, String writer, String reader, String readPort,
                String location) {
            return row(
                    "schemaVersion", 3,
                    "kind", "RUNTIME_FIELD_FLOW",
                    "edgeId", edgeId,
                    "fromOccurrenceId", writer,
                    "toOccurrenceId", reader,
                    "toPort", readPort,
                    SharedFieldFlow.EDGE_LOCATION, location);
        }

        private static Map<String, Object> activation(
                String activationId, String regionId, String occurrenceId,
                String sourceKey, long rootCallId) {
            return row(
                    "activationId", activationId,
                    "regionId", regionId,
                    "occurrenceId", occurrenceId,
                    "rootCallId", rootCallId,
                    "rootAuthority", "REGION.fault".equals(regionId)
                            ? "EXPLICIT_FAULT_ENTRY" : "FAILURE_TARGET_ENTRY",
                    "sourceKey", sourceKey);
        }

        private static Map<String, Object> faultPort(
                String occurrenceId, String portId, long eventSeq) {
            return row(
                    "occurrenceId", occurrenceId,
                    "portId", portId,
                    "sourceKind", "EXPLICIT_SYMBOLIC_FAULT",
                    "symbolicName", "requestFails",
                    "eventSeq", eventSeq);
        }

        private static Map<String, Object> requestLink(
                String activationId, String exchangeLeg, String requestKey,
                long sender, long receiver) {
            return row(
                    "authority", "RECORDED_EXCHANGE_OCCURRENCE_LINK_V1",
                    "fromActivationId", activationId,
                    "direction", "REQUEST",
                    "exchangeLeg", exchangeLeg,
                    "requestKey", requestKey,
                    "requestApi", "api",
                    "transport", "RPC",
                    "attemptId", "1",
                    "senderEventSeq", sender,
                    "receiverEventSeq", receiver);
        }

        private static StaticProgram programWithExactAccessor(long eventSeq) {
            Map<String, Object> callReturn = row(
                    "id", "DF.return",
                    "kind", "call_return",
                    "transferKind", "FUNCTION_RETURN",
                    "runtimeObserved", true,
                    "regionIds", Collections.singletonList(REGION),
                    "method", METHOD,
                    "unitIndex", 12,
                    "siteId", SITE,
                    "invoke", CALLEE,
                    "fromCell", RETURN,
                    "toCell", LOCAL);
            Map<String, Object> accessorBinding = row(
                    "authority", "EXACT_RUNTIME_ACCESSOR_RECEIVER_RETURN_V1",
                    "regionId", REGION,
                    "siteId", SITE,
                    "declaredCallee", CALLEE,
                    "callId", 77L,
                    "eventSeq", eventSeq);
            Map<String, Object> accessor = row(
                    "id", "DF.accessor",
                    "kind", "accessor_field_return",
                    "transferKind", "HEAP_READ",
                    "runtimeObserved", true,
                    "regionIds", Collections.singletonList(REGION),
                    "method", METHOD,
                    "unitIndex", 12,
                    "siteId", SITE,
                    "invoke", CALLEE,
                    "fromCell", "<example.Value: long value>",
                    "toCell", LOCAL,
                    "runtimeAccessorBindings",
                    Collections.singletonList(accessorBinding));
            StaticProgram program = new StaticProgram();
            program.refinedGraph = Arrays.asList(callReturn, accessor);
            program.activations.put("node/region/REGION.reader#1", row(
                    "callIds", Collections.singletonList(77L)));
            return program;
        }

        private static Map<String, Object> returnObservation(long eventSeq) {
            return returnObservation(77L, eventSeq);
        }

        private static Map<String, Object> returnObservation(long callId,
                                                             long eventSeq) {
            return row(
                    "kind", "CALL_SITE_RETURN",
                    "siteId", SITE,
                    "declaredCallee", CALLEE,
                    "callId", callId,
                    "eventSeq", eventSeq,
                    "primitiveValue", "5");
        }

        private static Map<String, Object> communicationCapture(
                String side, String port, String exchange, long eventSeq,
                long transportEventSeq) {
            return row(
                    "side", side,
                    "portId", port,
                    "exchangeLeg", exchange,
                    "eventSeq", eventSeq,
                    "transportEventSeq", transportEventSeq);
        }

        private static Map<String, Object> communicationPort(
                String port, String direction) {
            return row(
                    "portId", port,
                    "sourceKind", RuntimeSelectedRegionFinalizer
                            .COMMUNICATION_SITE_PORT,
                    "direction", direction,
                    "dependencyRole", "VALUE_FRONTIER",
                    "javaType", "long");
        }

        private static Map<String, Object> row(Object... fields) {
            Map<String, Object> result = new LinkedHashMap<>();
            for (int index = 0; index < fields.length; index += 2) {
                result.put((String) fields[index], fields[index + 1]);
            }
            return result;
        }
    }

}
