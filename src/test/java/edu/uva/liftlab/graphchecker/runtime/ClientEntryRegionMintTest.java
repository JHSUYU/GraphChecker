package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The client half of an exchange has no execution-context authority of its
 * own, so a workload that drives a component as a library drops every static
 * region that would have carried it.  These pin the one region the selection
 * stage mints in that case, and every refusal that keeps it from minting
 * anything the run did not state.
 */
public class ClientEntryRegionMintTest {
    private static final String OWNER =
            "<example.Client: void <init>(example.Peer)>";
    private static final String CALL_SITE = OWNER + "#u8";
    private static final String EXCHANGE = "XCH.example-exchange";
    private static final String CALLEE =
            "<example.Peer: example.Keys fetch()>";
    private static final String SHARED_A = "<example.Store: void addKeys()>";
    private static final String SHARED_B = "<example.Clock: long now()>";
    private static final String OUTER =
            "<example.Connector: void <init>(example.Peer)>";
    private static final String REQUEST = "app/client#epoch0/request/work#1";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    // ---------------------------------------------------------------- mint

    @Test
    public void interchangeableHoldersCollapseToOneMintedRegion() {
        List<JsonObject> candidates = holders(3);
        List<JsonObject> minted = mint(candidates, noneSelected(),
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L)));

        assertEquals(1, minted.size());
        JsonObject region = minted.get(0);
        assertEquals(OWNER, region.get("rootMethod").getAsString());
        assertEquals(RuntimeRegionPlanner.COMMUNICATION_CLIENT_ENTRY,
                region.get("rootAuthority").getAsString());
        assertEquals(OWNER, region.get("anchorMethod").getAsString());
        // The scope is the slice the holders share, not any holder's root.
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                OWNER, SHARED_A, SHARED_B)),
                strings(region, "methods"));
        assertEquals(strings(region, "methods"),
                strings(region, RuntimeSelectedRegionFinalizer.DEMAND_SCOPE));
        assertEquals(2, region.getAsJsonArray(
                RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS).size());
        JsonObject reroot = region.getAsJsonObject(
                RuntimeRegionPlanner.CLIENT_ENTRY_REROOT);
        assertEquals("OBSERVED_RPC_SEND_CLIENT_ENDPOINT_V2",
                reroot.get("authority").getAsString());
        assertEquals("exchange-1", reroot.getAsJsonArray("observedRpcSends")
                .get(0).getAsJsonObject().get("exchangeId").getAsString());
    }

    @Test
    public void aNestedTransportSendBindsThroughTheExactEntryInvocation() {
        String transport = "<example.Transport: void send()>";
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                frame(1, 0, OWNER, REQUEST, 1L),
                frame(2, 1, 101, transport, REQUEST, 1L));
        List<JsonObject> minted = mint(holders(3), noneSelected(), methods,
                Collections.singletonList(
                        site(10, 1, 101, CALL_SITE, CALLEE)),
                Collections.singletonList(send(20, "SEND", "exchange-1",
                        "REQUEST", 2, 999)));

        assertEquals(1, minted.size());
        assertEquals(OWNER,
                minted.get(0).get("rootMethod").getAsString());
    }

    @Test
    public void theMintedIdentityIsAnchorDerivedAndDistinctFromEveryHolder() {
        List<JsonObject> candidates = holders(3);
        List<RuntimeRegionPlanner.MethodEvent> trace = Arrays.asList(
                frame(1, 0, OWNER, REQUEST, 1L));
        String first = mint(candidates, noneSelected(), trace).get(0)
                .get("regionId").getAsString();

        // Stable across runs, and never one of the holders it stands for.
        assertEquals(first, mint(holders(3), noneSelected(), trace).get(0)
                .get("regionId").getAsString());
        for (JsonObject holder : candidates) {
            assertNotEquals(holder.get("regionId").getAsString(), first);
        }
        // Which holders happened to declare the endpoint is not part of it.
        assertEquals(first, mint(holders(7), noneSelected(), trace).get(0)
                .get("regionId").getAsString());
        // The anchor site is.
        List<JsonObject> moved = holders(3);
        for (JsonObject holder : moved) {
            for (com.google.gson.JsonElement port : holder.getAsJsonArray(
                    RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS)) {
                port.getAsJsonObject().addProperty(
                        CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                        EXCHANGE + ".other");
            }
        }
        assertNotEquals(first, mint(moved, noneSelected(), trace).get(0)
                .get("regionId").getAsString());
    }

    @Test
    public void theMintedRootIsTheOutermostObservedFrameInsideTheScope() {
        // A caller the shared slice holds becomes the root; the same caller
        // outside the slice stops the walk at the call site's own frame.
        List<JsonObject> inScope = holders(3);
        for (JsonObject holder : inScope) {
            holder.getAsJsonArray(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE)
                    .add(OUTER);
        }
        List<RuntimeRegionPlanner.MethodEvent> nested = Arrays.asList(
                frame(9, 0, OUTER, REQUEST, 1L),
                frame(1, 9, OWNER, REQUEST, 1L));

        assertEquals(OUTER, mint(inScope, noneSelected(), nested).get(0)
                .get("rootMethod").getAsString());
        assertEquals(OWNER, mint(holders(3), noneSelected(), nested).get(0)
                .get("rootMethod").getAsString());
    }

    @Test
    public void theWalkStopsWhereTheRequestOrTheLaneChanges() {
        List<JsonObject> inScope = holders(3);
        for (JsonObject holder : inScope) {
            holder.getAsJsonArray(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE)
                    .add(OUTER);
        }
        assertEquals(OWNER, mint(inScope, noneSelected(), Arrays.asList(
                frame(9, 0, OUTER, "app/other#epoch0/request/work#1", 1L),
                frame(1, 9, OWNER, REQUEST, 1L))).get(0)
                .get("rootMethod").getAsString());
        assertEquals(OWNER, mint(inScope, noneSelected(), Arrays.asList(
                frame(9, 0, OUTER, REQUEST, 2L),
                frame(1, 9, OWNER, REQUEST, 1L))).get(0)
                .get("rootMethod").getAsString());
    }

    // ------------------------------------------------------------- refusals

    @Test
    public void anObservedOwnerWithoutASendMintsNothing() {
        List<RuntimeRegionPlanner.MethodEvent> methods =
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L));
        assertEquals(Collections.emptyList(), mint(holders(3), noneSelected(),
                methods, defaultExecution(methods),
                Collections.<RuntimeRegionPlanner.ProtocolEvent>emptyList()));
    }

    @Test
    public void aReceiveWithoutASendMintsNothing() {
        List<RuntimeRegionPlanner.MethodEvent> methods =
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L));
        assertEquals(Collections.emptyList(), mint(holders(3), noneSelected(),
                methods, defaultExecution(methods),
                Collections.singletonList(send(20, "RECEIVE", "exchange-1",
                        "REQUEST", 1, 101))));
    }

    @Test
    public void aSendAtTheWrongCallSiteMintsNothing() {
        List<RuntimeRegionPlanner.MethodEvent> methods =
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L));
        assertEquals(Collections.emptyList(), mint(holders(3), noneSelected(),
                methods,
                Collections.singletonList(site(10, 1, 101,
                        OWNER + "#u9", CALLEE)),
                defaultProtocol(methods)));
    }

    @Test
    public void aSendForTheWrongDeclaredCalleeMintsNothing() {
        List<RuntimeRegionPlanner.MethodEvent> methods =
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L));
        assertEquals(Collections.emptyList(), mint(holders(3), noneSelected(),
                methods,
                Collections.singletonList(site(10, 1, 101, CALL_SITE,
                        "<example.Other: example.Keys fetch()>")),
                defaultProtocol(methods)));
    }

    @Test
    public void aSendWithoutAnExchangeIdentityMintsNothing() {
        List<RuntimeRegionPlanner.MethodEvent> methods =
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L));
        assertEquals(Collections.emptyList(), mint(holders(3), noneSelected(),
                methods, defaultExecution(methods),
                Collections.singletonList(send(20, "SEND", "", "REQUEST",
                        1, 101))));
    }

    @Test
    public void aSendFromAnotherInvocationMintsNothing() {
        List<RuntimeRegionPlanner.MethodEvent> methods =
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L));
        assertEquals(Collections.emptyList(), mint(holders(3), noneSelected(),
                methods, defaultExecution(methods),
                Collections.singletonList(send(20, "SEND", "exchange-2",
                        "REQUEST", 1, 999))));
    }

    @Test
    public void aResponseSendCannotAuthorizeAClientRequestEntry() {
        List<RuntimeRegionPlanner.MethodEvent> methods =
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L));
        assertEquals(Collections.emptyList(), mint(holders(3), noneSelected(),
                methods, defaultExecution(methods),
                Collections.singletonList(send(20, "SEND", "exchange-1",
                        "RESPONSE", 1, 101))));
    }

    @Test
    public void aRunThatEnteredAnyHolderMintsNothing() {
        List<JsonObject> candidates = holders(3);
        Set<String> selected = new LinkedHashSet<>(Collections.singletonList(
                candidates.get(2).get("regionId").getAsString()));
        assertEquals(Collections.emptyList(), mint(candidates, selected,
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L))));
    }

    @Test
    public void anAnchorOutsideAnyRegisteredRequestMintsNothing() {
        assertEquals(Collections.emptyList(), mint(holders(3),
                noneSelected(),
                Arrays.asList(frame(1, 0, OWNER, "", 1L))));
    }

    @Test
    public void anUnobservedAnchorMintsNothing() {
        assertEquals(Collections.emptyList(), mint(holders(3),
                noneSelected(),
                Arrays.asList(frame(1, 0, SHARED_A, REQUEST, 1L))));
        assertEquals(Collections.emptyList(), mint(holders(3),
                noneSelected(),
                Collections.<RuntimeRegionPlanner.MethodEvent>emptyList()));
    }

    @Test
    public void anAmbiguousRootMintsNothing() {
        List<JsonObject> inScope = holders(3);
        for (JsonObject holder : inScope) {
            holder.getAsJsonArray(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE)
                    .add(OUTER);
        }
        // One occurrence nested in a scope caller, one not: the run states
        // two different client entries, so it states none.
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                frame(9, 0, OUTER, REQUEST, 1L),
                frame(1, 9, OWNER, REQUEST, 1L),
                frame(2, 0, OWNER, REQUEST, 1L));
        assertEquals(Collections.emptyList(), mint(inScope, noneSelected(),
                methods,
                Arrays.asList(site(10, 1, 101, CALL_SITE, CALLEE),
                        site(11, 2, 102, CALL_SITE, CALLEE)),
                Arrays.asList(send(20, "SEND", "exchange-1", "REQUEST",
                                1, 101),
                        send(21, "SEND", "exchange-2", "REQUEST", 2, 102))));
    }

    @Test
    public void anEmptySharedSliceMintsNothing() {
        List<JsonObject> candidates = holders(2);
        candidates.get(1).add(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE,
                encode(Arrays.asList("<example.Other: void run()>")));
        assertEquals(Collections.emptyList(), mint(candidates,
                noneSelected(),
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L))));
    }

    @Test
    public void holdersThatDisagreeOnTheEndpointMintNothing() {
        List<JsonObject> candidates = holders(2);
        candidates.get(1).getAsJsonArray(
                RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS)
                .remove(1);
        assertEquals(Collections.emptyList(), mint(candidates,
                noneSelected(),
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L))));
    }

    @Test
    public void holdersThatDisagreeOnADeclaredSourceMintNothing() {
        List<JsonObject> candidates = holders(2);
        JsonArray declared = new JsonArray();
        JsonArray other = new JsonArray();
        other.add("<example.Hook: boolean symbolize()>");
        candidates.get(0).add(
                edu.uva.liftlab.graphchecker.contract
                        .ConfiguredSourcePhaseContract.TRACE_METHODS_FIELD,
                declared);
        candidates.get(1).add(
                edu.uva.liftlab.graphchecker.contract
                        .ConfiguredSourcePhaseContract.TRACE_METHODS_FIELD,
                other);
        assertEquals(Collections.emptyList(), mint(candidates,
                noneSelected(),
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L))));
    }

    @Test
    public void aRootAlreadyClaimedByASelectedRegionMintsNothing() {
        List<RuntimeRegionPlanner.MethodEvent> methods =
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L));
        assertEquals(Collections.emptyList(),
                CausynthTraceRecorder.mintedClientEntryRegionsForTests(
                        holders(3), noneSelected(),
                        Collections.singletonList(OWNER),
                        methods, defaultExecution(methods),
                        defaultProtocol(methods)));
    }

    // ------------------------------------------------------ pass-1 evidence

    @Test
    public void skeletonPassRetainsOnlyTheProtocolAuthenticationDomain()
            throws Exception {
        JsonObject method = traceRow("METHOD_ENTER", 1);
        method.addProperty("method", OWNER);
        method.addProperty("callId", 1);
        method.addProperty("threadName", "main");
        method.addProperty("tid", 1);
        method.addProperty("laneId", 1);
        method.addProperty("requestKey", REQUEST);
        method.addProperty("requestApi", "work");

        JsonObject call = traceRow("CALL_SITE_ENTER", 10);
        call.addProperty("method", OWNER);
        call.addProperty("callId", 1);
        call.addProperty("invocationId", 101);
        call.addProperty("siteId", CALL_SITE);
        call.addProperty("declaredCallee", CALLEE);

        JsonObject branch = traceRow("BRANCH", 11);
        branch.addProperty("method", OWNER);
        branch.addProperty("callId", 1);
        branch.addProperty("siteId", OWNER + "#u7");
        branch.addProperty("outcome", true);

        JsonObject send = traceRow("RPC_SEND", 20);
        send.addProperty("transport", "HADOOP_IPC");
        send.addProperty("correlationId", "exchange-1");
        send.addProperty("attemptId", "0");
        send.addProperty("half", "REQUEST");
        send.addProperty("threadName", "main");
        send.addProperty("tid", 1);
        send.addProperty("method", OWNER);
        send.addProperty("callId", 1);
        send.addProperty("invocationId", 101);
        send.addProperty("declaredCallee", CALLEE);
        send.addProperty("requestKey", REQUEST);
        send.addProperty("requestApi", "work");

        CausynthTraceRecorder.TraceData trace =
                CausynthTraceRecorder.parseSkeletonTraceLinesForTests(
                        Arrays.asList(method.toString(), call.toString(),
                                branch.toString(), send.toString()));

        assertEquals(1, trace.methods.size());
        assertEquals(1, trace.execution.size());
        assertEquals("CALL_SITE_ENTER", trace.execution.get(0).kind);
        assertEquals(1, trace.protocol.size());
        assertEquals("SEND", trace.protocol.get(0).direction);
        assertEquals(1, mint(holders(3), noneSelected(), trace.methods,
                trace.execution, trace.protocol).size());
    }

    // ------------------------------------------------------- pass-2 binding

    @Test
    public void aMintedClientEntryBindsItsObservedActivation()
            throws Exception {
        JsonObject region = mint(holders(3), noneSelected(),
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L))).get(0);
        File file = folder.newFile("selected.jsonl");
        Files.write(file.toPath(), (region.toString() + "\n")
                .getBytes(StandardCharsets.UTF_8));

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(file, Arrays.asList(
                        frame(1, 0, OWNER, REQUEST, 1L),
                        frame(2, 1, SHARED_A, REQUEST, 1L)));

        assertEquals(1, result.runtimeInstances.size());
        assertEquals(region.get("regionId").getAsString(),
                result.runtimeInstances.iterator().next().get("regionId"));
        assertEquals(RuntimeRegionPlanner.COMMUNICATION_CLIENT_ENTRY,
                result.runtimeInstances.iterator().next()
                        .get("rootAuthority"));
    }

    @Test
    public void anExecutionContextRootIsStillNeverAConstructor()
            throws Exception {
        JsonObject region = mint(holders(3), noneSelected(),
                Arrays.asList(frame(1, 0, OWNER, REQUEST, 1L))).get(0);
        region.addProperty("rootAuthority", "TASK_ENTRY");
        File file = folder.newFile("relabelled.jsonl");
        Files.write(file.toPath(), (region.toString() + "\n")
                .getBytes(StandardCharsets.UTF_8));
        try {
            RuntimeRegionPlanner.planSkeletonGraph(file, Arrays.asList(
                    frame(1, 0, OWNER, REQUEST, 1L)));
            fail("a task entry rooted at a constructor must be refused");
        } catch (IllegalArgumentException refused) {
            assertTrue(String.valueOf(refused.getMessage()).contains(
                    "authoritative execution "));
        }
    }

    // -------------------------------------------------------------- helpers

    private static List<JsonObject> mint(
            List<JsonObject> candidates, Set<String> selected,
            List<RuntimeRegionPlanner.MethodEvent> methods) {
        return mint(candidates, selected, methods,
                defaultExecution(methods), defaultProtocol(methods));
    }

    private static List<JsonObject> mint(
            List<JsonObject> candidates, Set<String> selected,
            List<RuntimeRegionPlanner.MethodEvent> methods,
            List<RuntimeRegionPlanner.RuntimeEvent> execution,
            List<RuntimeRegionPlanner.ProtocolEvent> protocol) {
        return CausynthTraceRecorder.mintedClientEntryRegionsForTests(
                candidates, selected,
                Collections.<String>emptyList(), methods, execution, protocol);
    }

    private static List<RuntimeRegionPlanner.RuntimeEvent> defaultExecution(
            List<RuntimeRegionPlanner.MethodEvent> methods) {
        for (RuntimeRegionPlanner.MethodEvent method : methods) {
            if (OWNER.equals(method.method)) {
                return Collections.singletonList(site(10, method.callId,
                        101, CALL_SITE, CALLEE));
            }
        }
        return Collections.emptyList();
    }

    private static List<RuntimeRegionPlanner.ProtocolEvent> defaultProtocol(
            List<RuntimeRegionPlanner.MethodEvent> methods) {
        for (RuntimeRegionPlanner.MethodEvent method : methods) {
            if (OWNER.equals(method.method)) {
                return Collections.singletonList(send(20, "SEND",
                        "exchange-1", "REQUEST", method.callId, 101));
            }
        }
        return Collections.emptyList();
    }

    private static Set<String> noneSelected() {
        return Collections.emptySet();
    }

    /** {@code count} interchangeable holders: one declared root each, one
     *  shared demand slice, one identical client endpoint. */
    private static List<JsonObject> holders(int count) {
        List<JsonObject> rows = new ArrayList<>();
        for (int index = 0; index < count; index++) {
            String root = "<example.Tool" + index
                    + ": void main(java.lang.String[])>";
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion",
                    RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION);
            row.addProperty("kind",
                    RuntimeSelectedRegionFinalizer.SKELETON_KIND);
            row.addProperty("regionId", "REGION.holder-" + index);
            row.addProperty("rootMethod", root);
            row.addProperty("rootAuthority", "MAIN_ENTRY");
            row.addProperty("anchorMethod", OWNER);
            row.add("anchorMethods", encode(Arrays.asList(
                    OWNER, SHARED_A, "<example.Tool" + index
                            + ": void helper()>")));
            row.add("methods", encode(Arrays.asList(
                    root, OWNER, SHARED_A, SHARED_B, OUTER)));
            row.add(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE,
                    encode(Arrays.asList(root, OWNER, SHARED_A, SHARED_B)));
            row.addProperty("selection", "COMMUNICATION_CONTEXT");
            JsonArray ports = new JsonArray();
            ports.add(port("resp", "CONCRETE_STRUCTURE_CARRIER"));
            ports.add(port("resp.keyId", "VALUE_FRONTIER"));
            row.add(RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS,
                    ports);
            rows.add(row);
        }
        return rows;
    }

    private static JsonObject port(String suffix, String role) {
        JsonObject port = new JsonObject();
        port.addProperty("portId", EXCHANGE + "." + suffix);
        port.addProperty("regionPortSide", "IN");
        port.addProperty("dependencyRole", role);
        port.addProperty("direction", "RESPONSE");
        port.addProperty(RuntimeSelectedRegionFinalizer.PORT_ROLE,
                RuntimeSelectedRegionFinalizer.PORT_ROLE_CLIENT);
        port.addProperty(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                EXCHANGE);
        port.addProperty(CommunicationCatalogContract.CALL_SITE_ID,
                CALL_SITE);
        port.addProperty(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD, OWNER);
        port.addProperty("definitionUnitIndex", 8);
        port.addProperty("declaredCallee", CALLEE);
        return port;
    }

    private static JsonArray encode(Collection<String> values) {
        JsonArray array = new JsonArray();
        for (String value : values) {
            array.add(value);
        }
        return array;
    }

    private static JsonObject traceRow(String event, long seq) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 3);
        row.addProperty("event", event);
        row.addProperty("seq", seq);
        return row;
    }

    private static Set<String> strings(JsonObject row, String field) {
        Set<String> values = new LinkedHashSet<>();
        for (com.google.gson.JsonElement element
                : row.getAsJsonArray(field)) {
            values.add(element.getAsString());
        }
        return values;
    }

    private static RuntimeRegionPlanner.RuntimeEvent site(
            long seq, long callId, long invocationId, String siteId,
            String callee) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, "CALL_SITE_ENTER",
                OWNER, callId, invocationId, 0L, siteId, callee,
                -1, "", 0, "", null, null, "", "");
    }

    private static RuntimeRegionPlanner.ProtocolEvent send(
            long seq, String direction, String exchange, String half,
            long callId, long invocationId) {
        return new RuntimeRegionPlanner.ProtocolEvent(seq, direction,
                "HADOOP_IPC", exchange, "0", half, "main", 1L,
                OWNER, callId, invocationId, CALLEE, 1L, 1L, 0L, 0L,
                null, REQUEST, "work");
    }

    private static RuntimeRegionPlanner.MethodEvent frame(
            long callId, long parentCallId, String method, String request,
            long lane) {
        return frame(callId, parentCallId, 0L, method, request, lane);
    }

    private static RuntimeRegionPlanner.MethodEvent frame(
            long callId, long parentCallId, long parentSiteId, String method,
            String request, long lane) {
        return new RuntimeRegionPlanner.MethodEvent(callId, "test", "main",
                1L, method, 0, "", callId, parentCallId, parentSiteId,
                lane, 0L, 0L, 0L, null, false, request, "work");
    }
}
