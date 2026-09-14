package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.SiteId;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.After;
import org.junit.Test;
import soot.G;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The region graph joins on an address, and refuses anything else.
 *
 * <p>String equality on {@code occurrenceId} merges two activations the
 * moment one carries an {@code #a<n>} suffix, and a merge here is
 * invisible, so a graph that cannot be built says so.  The graph only
 * scopes: it never decides what matters, picks an arm, or names a
 * writer.</p>
 */
public class RegionGraphOccurrenceKeyTest {
    private static final String PLANNED =
            "hdfs-17960/nn0#epoch1/region/"
                    + "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d#1";

    @After
    public void resetSoot() {
        G.reset();
    }

    /**
     * A planned address keys as itself: the migration is byte-neutral.  An
     * absent id is still absent, so the callers' early returns stand.  A
     * per-activation id, and anything that does not spell an address at all,
     * is refused rather than merged onto the address it resembles.
     */
    @Test
    public void aPlannedAddressKeysAsItselfAndAnythingElseIsRefused() {
        assertEquals(PLANNED,
                RuntimeSelectedRegionFinalizer.occurrenceKey(PLANNED));
        assertEquals("", RuntimeSelectedRegionFinalizer.occurrenceKey(null));
        assertEquals("", RuntimeSelectedRegionFinalizer.occurrenceKey(""));
        for (String unreadable : new String[] {
                PLANNED + "#a1",
                "REGION.9492ec77",
                "hdfs-17960/nn0#epoch1/region/REGION.1",
                "hdfs-17960/nn0#epoch1/region/REGION.1#0"}) {
            refuses(unreadable);
        }
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
     * <p>The wire transaction is minted fresh in every run, so it cannot
     * name the edge; it stays on it as transport evidence.  The name is the
     * producing and consuming occurrence, the port, the direction and an
     * ordinal over that tuple.</p>
     */
    @Test
    public void aRecordedExchangeEdgeIsNamedFromContentNotTheWire()
            throws Exception {
        assertNotEquals("the wire transactions of two recordings are "
                        + "expected to differ",
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0",
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0");

        // The one transaction of one exchange site is exchange number one,
        // whichever transaction the recording happened to mint.
        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                new LinkedHashMap<>(), SITE,
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0"));
        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                new LinkedHashMap<>(), SITE,
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0"));

        // A request-control edge is named by the response edge, not the wire:
        // the response edge already names the exchange from content, and it
        // names it more exactly than the transaction does, because each retry
        // of one logical request has its own response edge.
        String first = controlEdgeId(
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0");
        String second = controlEdgeId(
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0");
        assertEquals("two recordings of one request fault must publish one "
                + "control edge name", first, second);
    }

    private static final String SITE =
            "hdfs-17899/nn0#epoch0/region/REGION.a#1\n"
                    + "hdfs-17899/source-dn#epoch0/region/REGION.b#1\n"
                    + "REGION.b.in.port\nREQUEST";

    @SuppressWarnings("unchecked")
    private static String controlEdgeId(String transaction) throws Exception {
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
                row("edgeId", "RPC.response"),
                transaction, "hdfs-17899/nn0#epoch0",
                1L, 2L, 3L, 4L, 5L);
        return String.valueOf(result.get("edgeId"));
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

    private static Map<String, Object> callEdge(String caller, String callee,
                                                int unitIndex) {
        Map<String, Object> edge = edge(caller, "VALUE_PASS",
                caller + "::argument", callee + ".param0:int", callee);
        edge.put("unitIndex", unitIndex);
        return edge;
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

    /**
     * The care set is the intersection of the two conditions: a field must
     * appear on the backward slice AND be forward-reachable from a symbolic
     * root.  A field the slice names but no root reaches is a constant for
     * this failure and stays out.  An explicit fault marker and a wire attach
     * point are symbolic roots of the same standing.
     */
    @Test
    public void careSetKeepsOnlySliceFieldsASymbolicRootReaches() {
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

        List<Map<String, Object>> handoff = Arrays.asList(
                row("kind", "wire_handoff", "fromCell", "cell.send",
                        "toCell", "cell.receive"),
                row("kind", "field_write", "fromCell", "cell.receive",
                        "toCell", "cell.keys",
                        "fieldPathDeclarations", Collections.singletonList(
                                "<example.Owner: java.util.Map allKeys>")));
        assertTrue(RuntimeSelectedRegionFinalizer.caredSharedLocations(handoff)
                .contains("example.Owner#allKeys"));
    }

    private static Map<String, Object> row(Object... fields) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < fields.length; index += 2) {
            result.put((String) fields[index], fields[index + 1]);
        }
        return result;
    }
}
