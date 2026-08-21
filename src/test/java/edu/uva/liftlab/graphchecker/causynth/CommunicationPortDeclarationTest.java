package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

/**
 * README section 3's composition shape needs both ends of every cut equality
 * to be a declared port of some region:
 *
 * <pre>
 * T_C0(Input, Live_out, Req_out)
 * AND Req_in = Req_out AND T_S(Req_in, Resp_out)
 * AND Resp_in = Resp_out AND Live_in = Live_out
 * AND T_C1(Live_in, Resp_in, Target)
 * </pre>
 *
 * <p>These pin where each of those ports is declared, and that a side which
 * cannot be resolved becomes a named gap rather than a silent absence.</p>
 */
public class CommunicationPortDeclarationTest {

    private static final String CLIENT_ROOT = "<example.Client: void run()>";
    private static final String CLIENT_CUT = "<example.Client: int call()>";
    private static final String TRANSPORT =
            "<example.Transport: int carry()>";
    private static final String SERVER_ROOT = "<example.Server: void run()>";
    private static final String SERVER_ENTRY =
            "<example.Handler: int serve(int)>";
    private static final String OTHER_ENTRY =
            "<example.OtherHandler: int serve(int)>";
    private static final String CALLEE =
            "<example.Channel: int callServer(int)>";

    @Test
    public void requestPortIsAClientOutputAndAServerInput() {
        StaticProgram program = twoRegionSlice();
        CommunicationCallSite site = resolvedCut();
        program.communicationCallSites.add(site.row());

        plan(program);

        String request = CommunicationCatalogContract.requestPortId(
                site.exchangeSiteKey, "p0");
        String response = CommunicationCatalogContract.responsePortId(
                site.exchangeSiteKey);
        Map<String, Object> client = regionContaining(program, CLIENT_CUT);
        Map<String, Object> server = regionContaining(program, SERVER_ENTRY);

        // Req_out is stated by the client prefix, Req_in is consumed by the
        // server fragment; the equality joins one region's output to the
        // other's input.
        assertEquals("int", declared(client, "OUT", request)
                .get("javaType"));
        assertEquals(CommunicationCatalogContract.DIRECTION_REQUEST,
                declared(client, "OUT", request).get(
                        CommunicationCatalogContract.PORT_DIRECTION));
        assertNotNull(declared(server, "IN", request));
        assertNull(declared(client, "IN", request));
        assertNull(declared(server, "OUT", request));

        // Resp_out is the server's, Resp_in is the continuation's.
        assertNotNull(declared(server, "OUT", response));
        assertNotNull(declared(client, "IN", response));
        assertNull(declared(client, "OUT", response));
    }

    /**
     * {@code Req_out} is read at the cut argument, in the client's own frame.
     *
     * <p>An output relation must contain the method that defines its output.
     * A request output anchored on the transport's own field write therefore
     * pulls the transport frame into {@code T_C0}; anchored on the cut
     * argument it stays inside the client prefix, whose export site the cut
     * unit already is.</p>
     */
    @Test
    public void requestOutputIsCapturedAtTheCutArgument() {
        StaticProgram program = twoRegionSlice();
        CommunicationCallSite site = resolvedCut();
        program.communicationCallSites.add(site.row());

        plan(program);

        String request = CommunicationCatalogContract.requestPortId(
                site.exchangeSiteKey, "p0");
        Map<String, Object> out = declared(
                regionContaining(program, CLIENT_CUT), "OUT", request);
        assertEquals(CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT,
                out.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        // Segment-local: the defining method is the client's, not the callee.
        assertEquals(CLIENT_CUT, out.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        assertEquals(14, out.get(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX));
        assertEquals(0, out.get(
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX));
        assertEquals(CALLEE, out.get(
                CommunicationCatalogContract.DECLARED_CALLEE));
    }

    /**
     * {@code Req_in} is the server entry's own parameter, and the delivery
     * frame it came out of is named beside it.
     *
     * <p>The consuming half of {@code Req_in = Req_out} is a port like any
     * other: it needs a site inside the fragment that reads it.  Without one
     * the server fragment's only offer is the transport's own heap read, in a
     * frame its window excludes, so {@code T_S} is either anchored across the
     * cut or has no input at all.</p>
     */
    @Test
    public void requestInputIsCapturedAtTheServerEntryParameter() {
        StaticProgram program = twoRegionSlice();
        CommunicationCallSite site = resolvedCut();
        program.communicationCallSites.add(site.row());

        plan(program);

        Map<String, Object> in = declared(
                regionContaining(program, SERVER_ENTRY), "IN",
                CommunicationCatalogContract.requestPortId(
                        site.exchangeSiteKey, "p0"));
        assertEquals(CommunicationCatalogContract.CAPTURE_ENTRY_PARAMETER,
                in.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        // Segment-local: the defining method is the handler's, not the
        // transport frame that delivered the value to it.
        assertEquals(SERVER_ENTRY, in.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        assertEquals(0, in.get(
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX));
        // The delivery frame, so a heap read recorded inside it can be
        // matched to this declaration instead of taken for the server's own
        // state.  It is not the cut's declared callee: the server's request
        // is returned by the delivery, not passed to it.
        assertNull(in.get(CommunicationCatalogContract.DECLARED_CALLEE));
    }

    /** {@code Resp_out} is the entry's return; {@code Resp_in} the cut's. */
    @Test
    public void responsePortIsCapturedOnBothSidesOfTheCut() {
        StaticProgram program = twoRegionSlice();
        CommunicationCallSite site = resolvedCut();
        program.communicationCallSites.add(site.row());

        plan(program);

        String response = CommunicationCatalogContract.responsePortId(
                site.exchangeSiteKey);
        Map<String, Object> out = declared(
                regionContaining(program, SERVER_ENTRY), "OUT", response);
        assertEquals(CommunicationCatalogContract.CAPTURE_ENTRY_RETURN,
                out.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        assertEquals(SERVER_ENTRY, out.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));

        Map<String, Object> in = declared(
                regionContaining(program, CLIENT_CUT), "IN", response);
        assertEquals(CommunicationCatalogContract.CAPTURE_CALL_RETURN,
                in.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND));
        assertEquals(CLIENT_CUT, in.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD));
        assertEquals(14, in.get(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX));
    }

    @Test
    public void encodedParentIsConcreteAndComponentsAreSymbolicLeaves() {
        StaticProgram program = twoRegionSlice();
        Map<String, Object> site = resolvedCut().row();
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> declaredRequest =
                (List<Map<String, Object>>) site.get(
                        CommunicationCatalogContract.REQUEST_PORTS);
        List<Map<String, Object>> request = new ArrayList<>(declaredRequest);
        String exchange = String.valueOf(site.get(
                CommunicationCatalogContract.EXCHANGE_SITE_KEY));
        String parentId = CommunicationCatalogContract.requestPortId(
                exchange, "p0");
        Map<String, Object> component = new LinkedHashMap<>();
        component.put(CommunicationCatalogContract.PORT_ID,
                CommunicationCatalogContract.requestPortId(exchange,
                        "keyId"));
        component.put(CommunicationCatalogContract.PORT_NAME, "keyId");
        component.put(CommunicationCatalogContract.PORT_JAVA_TYPE, "int");
        component.put(CommunicationCatalogContract.PORT_DIRECTION,
                CommunicationCatalogContract.DIRECTION_REQUEST);
        component.put(CommunicationCatalogContract.PORT_COMPONENT_OF,
                parentId);
        component.put(CommunicationCatalogContract.PORT_ENCODING_AUTHORITY,
                "EXAMPLE_ENCODING_V1");
        component.put(CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                "WIRE/keyId");
        request.add(component);
        site.put(CommunicationCatalogContract.REQUEST_PORTS, request);
        program.communicationCallSites.add(site);

        plan(program);

        Map<String, Object> client = regionContaining(program, CLIENT_CUT);
        Map<String, Object> server = regionContaining(program, SERVER_ENTRY);
        String leafId = CommunicationCatalogContract.requestPortId(exchange,
                "keyId");
        assertEquals(DependencyRole.CONCRETE_STRUCTURE_CARRIER,
                declared(client, "OUT", parentId).get("dependencyRole"));
        assertEquals(DependencyRole.CONCRETE_STRUCTURE_CARRIER,
                declared(server, "IN", parentId).get("dependencyRole"));
        assertEquals(DependencyRole.VALUE_FRONTIER,
                declared(client, "OUT", leafId).get("dependencyRole"));
        assertEquals(DependencyRole.VALUE_FRONTIER,
                declared(server, "IN", leafId).get("dependencyRole"));
    }

    @Test
    public void responseComponentKeepsConcreteParentAndExactReturnSites() {
        StaticProgram program = twoRegionSlice();
        CommunicationCallSite cut = resolvedCut();
        Map<String, Object> site = cut.row();
        String parent = CommunicationCatalogContract.responsePortId(
                cut.exchangeSiteKey);
        String component = CommunicationCatalogContract
                .responseComponentPortId(cut.exchangeSiteKey, "keyId");
        Map<String, Object> leaf = new LinkedHashMap<>();
        leaf.put(CommunicationCatalogContract.PORT_ID, component);
        leaf.put(CommunicationCatalogContract.PORT_NAME, "keyId");
        leaf.put(CommunicationCatalogContract.PORT_JAVA_TYPE, "int");
        leaf.put(CommunicationCatalogContract.PORT_DIRECTION,
                CommunicationCatalogContract.DIRECTION_RESPONSE);
        leaf.put(CommunicationCatalogContract.PORT_COMPONENT_OF, parent);
        leaf.put(CommunicationCatalogContract.PORT_ENCODING_AUTHORITY,
                "CONFIGURED_RESPONSE_FIELD_PATH_V1");
        leaf.put(CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                "resp/currentKey/keyId");
        leaf.put(CommunicationCatalogContract.PORT_HANDOFF_PATH,
                Arrays.asList(pathField(
                        "<example.Response: example.Key currentKey>"),
                        pathField("<example.Key: int keyId>")));
        site.put(CommunicationCatalogContract.RESPONSE_COMPONENT_PORTS,
                Collections.singletonList(leaf));
        program.communicationCallSites.add(site);

        plan(program);

        Map<String, Object> client = regionContaining(program, CLIENT_CUT);
        Map<String, Object> server = regionContaining(program, SERVER_ENTRY);
        assertEquals(DependencyRole.CONCRETE_STRUCTURE_CARRIER,
                declared(client, "IN", parent).get("dependencyRole"));
        assertEquals(DependencyRole.CONCRETE_STRUCTURE_CARRIER,
                declared(server, "OUT", parent).get("dependencyRole"));
        assertEquals(DependencyRole.VALUE_FRONTIER,
                declared(client, "IN", component).get("dependencyRole"));
        assertEquals(DependencyRole.VALUE_FRONTIER,
                declared(server, "OUT", component).get("dependencyRole"));
        assertEquals(CommunicationCatalogContract.CAPTURE_CALL_RETURN,
                declared(client, "IN", component).get(
                        CommunicationCatalogContract
                                .PORT_OUTPUT_CAPTURE_KIND));
        assertEquals(CommunicationCatalogContract.CAPTURE_ENTRY_RETURN,
                declared(server, "OUT", component).get(
                        CommunicationCatalogContract
                                .PORT_OUTPUT_CAPTURE_KIND));
        assertEquals(leaf.get(
                        CommunicationCatalogContract.PORT_HANDOFF_PATH),
                declared(server, "OUT", component).get(
                        CommunicationCatalogContract
                                .PORT_HANDOFF_PATH));
    }

    private static Map<String, Object> pathField(String declaration) {
        Map<String, Object> step = new LinkedHashMap<>();
        step.put("kind", "FIELD");
        step.put("declaration", declaration);
        return step;
    }

    @Test
    public void cutBehindTransportBelongsToTheOuterCoarseRegion() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(CLIENT_ROOT, TRANSPORT));
        program.edges.add(edge(TRANSPORT, CLIENT_CUT));
        program.edges.add(failure(CLIENT_ROOT));
        program.edges.add(edge(SERVER_ROOT, SERVER_ENTRY));
        program.edges.add(failure(SERVER_ENTRY));
        program.executionContextAuthorities.put(CLIENT_ROOT, "TASK_ENTRY");
        program.executionContextAuthorities.put(SERVER_ROOT, "TASK_ENTRY");
        program.regionEnvelopeExclusions.add(TRANSPORT);
        program.targetResolved.put("method", CLIENT_ROOT);
        CommunicationCallSite site = resolvedCut();
        program.communicationCallSites.add(site.row());

        SymbolicRegionPlanner.planSelectedSkeleton(program, Arrays.asList(
                CLIENT_ROOT, TRANSPORT, CLIENT_CUT,
                SERVER_ROOT, SERVER_ENTRY));

        Map<String, Object> client = regionContaining(program, CLIENT_ROOT);
        @SuppressWarnings("unchecked")
        List<String> methods = (List<String>) client.get("methods");
        assertFalse(methods.contains(TRANSPORT));
        assertFalse(methods.contains(CLIENT_CUT));
        assertNotNull(declared(client, "OUT",
                CommunicationCatalogContract.requestPortId(
                        site.exchangeSiteKey, "p0")));
        assertNotNull(declared(client, "IN",
                CommunicationCatalogContract.responsePortId(
                        site.exchangeSiteKey)));
        assertNull(gap(program,
                CommunicationCatalogContract.GAP_REQUEST_PORT_UNRESOLVED));
    }

    /**
     * The candidate set is published even when it does not resolve.
     *
     * <p>{@code serverEntryMethod} is an answer and the candidate list is a
     * bound; discovery established the bound, so stating it claims nothing it
     * did not prove. The gap stays, because an admissible set larger than one
     * is still an unresolved static pairing.</p>
     */
    @Test
    public void serverEntryCandidatesArePublishedWhenUnresolved() {
        CommunicationCallSite resolved = resolvedCut();
        assertEquals(Collections.singletonList(SERVER_ENTRY),
                resolved.row().get(CommunicationCatalogContract.SERVER_ENTRY_CANDIDATES));

        CommunicationCallSite ambiguous = new CommunicationCallSite(
                CLIENT_CUT, 14, "HADOOP",
                CommunicationCatalogContract.TRANSPORT_HADOOP_IPC,
                "P", CALLEE, Arrays.asList(SERVER_ENTRY, OTHER_ENTRY),
                true, "int", Collections.singletonList(
                        new CommunicationCallSite.RequestPort("p0", 0, 0,
                                "int")), Collections
                .<CommunicationCallSite.ResponseComponentPort>emptyList());
        Map<String, Object> row = ambiguous.row();
        assertEquals("", row.get(
                CommunicationCatalogContract.SERVER_ENTRY_METHOD));
        assertEquals(Arrays.asList(SERVER_ENTRY, OTHER_ENTRY),
                row.get(CommunicationCatalogContract.SERVER_ENTRY_CANDIDATES));
    }

    @Test
    public void unresolvedServerEntryStillDeclaresTheClientSide() {
        StaticProgram program = twoRegionSlice();
        // Two compatible handlers and nothing static that separates them:
        // README section 1 forbids call order and a static endpoint match from
        // deciding it, so the entry stays unresolved.
        CommunicationCallSite site = new CommunicationCallSite(
                CLIENT_CUT, 14, "HADOOP",
                CommunicationCatalogContract.TRANSPORT_HADOOP_IPC,
                "P", CALLEE, Arrays.asList(SERVER_ENTRY, OTHER_ENTRY),
                true, "int", Collections.singletonList(
                        new CommunicationCallSite.RequestPort("p0", 0, 0,
                                "int")), Collections
                .<CommunicationCallSite.ResponseComponentPort>emptyList());
        assertEquals("", site.serverEntryMethod);
        program.communicationCallSites.add(site.row());

        plan(program);

        String request = CommunicationCatalogContract.requestPortId(
                site.exchangeSiteKey, "p0");
        String response = CommunicationCatalogContract.responsePortId(
                site.exchangeSiteKey);
        Map<String, Object> client = regionContaining(program, CLIENT_CUT);
        Map<String, Object> server = regionContaining(program, SERVER_ENTRY);
        // One unresolved server cut does not suppress the resolved half.
        assertNotNull(declared(client, "OUT", request));
        assertNotNull(declared(client, "IN", response));
        assertEquals(0, countDeclarations(server, request));
        assertEquals(0, countDeclarations(server, response));

        Map<String, Object> gap = gap(program,
                CommunicationCatalogContract.GAP_SERVER_CUT_UNRESOLVED);
        assertNotNull(String.valueOf(program.communicationGaps), gap);
        assertEquals("SERVER_SIDE_PORTS_UNDECLARED",
                gap.get(CommunicationCatalogContract.GAP_REASON));
        assertEquals(request + "," + response,
                gap.get(CommunicationCatalogContract.GAP_DETAIL));
    }

    // ---- fixture -------------------------------------------------------

    /** A client region and a server region that share no method. */
    private static StaticProgram twoRegionSlice() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(CLIENT_ROOT, CLIENT_CUT));
        program.edges.add(failure(CLIENT_CUT));
        program.edges.add(edge(SERVER_ROOT, SERVER_ENTRY));
        program.edges.add(failure(SERVER_ENTRY));
        program.executionContextAuthorities.put(CLIENT_ROOT, "TASK_ENTRY");
        program.executionContextAuthorities.put(SERVER_ROOT, "TASK_ENTRY");
        program.targetResolved.put("method", CLIENT_CUT);
        return program;
    }

    private static void plan(StaticProgram program) {
        SymbolicRegionPlanner.planSelectedSkeleton(program, Arrays.asList(
                CLIENT_ROOT, CLIENT_CUT, SERVER_ROOT, SERVER_ENTRY));
    }

    private static CommunicationCallSite resolvedCut() {
        return new CommunicationCallSite(CLIENT_CUT, 14, "HADOOP",
                CommunicationCatalogContract.TRANSPORT_HADOOP_IPC, "P",
                CALLEE, Collections.singletonList(SERVER_ENTRY), true, "int",
                Collections.singletonList(
                        new CommunicationCallSite.RequestPort("p0", 0, 0,
                                "int")), Collections
                .<CommunicationCallSite.ResponseComponentPort>emptyList());
    }

    private static Map<String, Object> edge(String method, String invoke) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("schemaVersion", 3);
        result.put("method", method);
        result.put("invoke", invoke);
        result.put("transferKind", "VALUE_PASS");
        result.put("kind", "local");
        result.put("fromCell", "x");
        result.put("toCell", "y");
        return result;
    }

    private static Map<String, Object> failure(String method) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("schemaVersion", 3);
        result.put("method", method);
        result.put("transferKind", "GUARD");
        result.put("kind", "exception_guard");
        result.put("fromCell", "guard");
        result.put("toCell", method + "#u7#exception:Failure");
        return result;
    }

    // ---- assertions ----------------------------------------------------

    private static Map<String, Object> declared(Map<String, Object> region,
                                                String side, String portId) {
        for (Map<String, Object> port : ports(region)) {
            if (portId.equals(port.get("portId"))
                    && side.equals(port.get(RuntimeSelectedRegionFinalizer
                    .REGION_PORT_SIDE))) {
                return port;
            }
        }
        return null;
    }

    private static int countDeclarations(Map<String, Object> region,
                                         String portId) {
        int count = 0;
        for (Map<String, Object> port : ports(region)) {
            if (portId.equals(port.get("portId"))) count++;
        }
        return count;
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> ports(
            Map<String, Object> region) {
        Object declared = region.get(
                RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS);
        return declared instanceof List
                ? (List<Map<String, Object>>) declared
                : Collections.<Map<String, Object>>emptyList();
    }

    private static Map<String, Object> gap(StaticProgram program,
                                           String kind) {
        for (Map<String, Object> row : program.communicationGaps) {
            if (kind.equals(row.get(
                    CommunicationCatalogContract.GAP_KIND))) {
                return row;
            }
        }
        return null;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> regionContaining(StaticProgram program,
                                                        String method) {
        for (Map<String, Object> region : program.regions) {
            if (((List<String>) region.get("methods")).contains(method)) {
                return region;
            }
        }
        throw new AssertionError("missing region for " + method);
    }
}
