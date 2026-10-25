package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.Fixtures.json;
import static java.util.Collections.singletonList;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import java.io.InputStreamReader;
import java.io.Reader;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Set;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

@RunWith(FreshStatics.class)
public class OccurrenceAddressIsNotARequestTest {
    private static final String PLAN_ROW =
            "plans/hdfs-17899-bug3-loop-body-producer.json";
    private static final String BALANCER = "hdfs-11741/balancer#epoch0";
    private static final String BALANCER_REGION = "REGION.r";
    private static final String PORT = "XCH.1.resp.block-key-array";
    private static final String NN0 = "hdfs/nn0";
    private static final String CLIENT = "hdfs/client0";
    private static final String SNAPSHOT_REGION = "REGION.9492ec77";
    private static final String SNAPSHOT_ROOT =
            "<a.Manager: void deleteSnapshot()>";
    private static final String NAMENODE = "hdfs-17899/nn0";
    private static final String TARGET = "hdfs-17899/target-dn";
    private static final String SPS = "hdfs-17899/sps";

    @Before
    public void startFromNoIdentity() {
        Lineage.resetForTests();
        RuntimeTraceContext.resetForTests();
    }

    @After
    public void clearRuntimeState() {
        SymbolicMessageEnvelope.clear();
        RuntimeTraceContext.resetForTests();
    }

    @Test
    @FreshStatics.Rows(2)
    public void theAddressIsTheOnlyAdmission() throws Exception {
        ConcolicTaskPlan.RuntimeTask task = handoffTask(3);
        assertTrue("the planned occurrence has an IN handoff",
                task.attachSite(PORT) != null);
        assertTrue("its own address answers it",
                task.acceptsRootInvocation(balancerAddress(3)));
        assertFalse("another activation of it does not",
                task.acceptsRootInvocation(balancerAddress(2)));
        assertFalse("nor an address no activation has",
                task.acceptsRootInvocation(balancerAddress(0)));
        assertFalse(task.acceptsRootInvocation(null));
        String oneIteration = task.addressDifference(balancerAddress(2));
        assertTrue(oneIteration, oneIteration.startsWith("differs in frame 0 "
                + "of 1, o.a.h.h.s.b.Balancer#dispatch#4, at iteration 2 and "
                + "not the planned 3; planned "));
        assertTrue("both addresses whole: " + oneIteration, oneIteration
                .contains("planned " + balancerAddress(3).render()
                        + ", ran at " + balancerAddress(2).render()));
        assertEquals("the activation ran where this run cannot name it",
                task.addressDifference(null));
        String noFrames = task.addressDifference(balancerAddress(0));
        assertTrue(noFrames, noFrames.startsWith("differs in its causal "
                + "context (planned " + balancerAddress(3).context().render()
                + ", ran " + balancerAddress(0).context().render() + ") and "
                + "its execution index depth (planned 1 frames, ran 0); "
                + "planned "));
        Endpoint sender = producerAt(1);
        Endpoint resent = producerAt(2);
        if (FreshStatics.row() == 0) {
            Interactions.sent("IPC", "corr-1", "REQUEST", sender);
            Interactions.sent("IPC", "corr-2", "REQUEST", resent);
            String onTheAnchor = anchoredTask(sender).addressDifference(
                    anchoredAddress(resent));
            assertTrue(onTheAnchor, onTheAnchor.startsWith("differs in its "
                    + "anchor's producer site index (planned "
                    + sender.siteIndex().render() + ", ran "
                    + resent.siteIndex().render() + "); planned "));
            return;
        }
        String neverMinted = anchoredTask(sender).addressDifference(
                anchoredAddress(resent));
        assertTrue(neverMinted, neverMinted.startsWith("differs in its "
                + "causal anchor (planned " + sender.id() + ", which no "
                + "message of this run minted; ran " + resent.id() + ", which"
                + " no message of this run minted); planned "));
        assertTrue(SymbolicMessageEnvelope.stage(PORT, 41L, null));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());
        assertTrue(task.acceptsRootInvocation(balancerAddress(3)));
        assertFalse(task.acceptsRootInvocation(balancerAddress(4)));

        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NN0, 1L));
        ConcolicTaskPlan.RuntimeTask unobserved = runtime(encoded("TASK.1",
                NN0 + "#epoch1", SNAPSHOT_REGION, SNAPSHOT_ROOT, address(
                        NN0 + "#epoch1", SNAPSHOT_REGION, CausalContext.of(
                                Role.UNKNOWN)).render(), 1));
        assertNotNull("the address is the whole admission",
                select(plan(unobserved), unobserved, node));
        RecordingWindow.open();
        Object client = new Object();
        RuntimeTraceContext.registerSource(client,
                new SourceRef("CLIENT", "client", CLIENT, 0L));
        long call = RuntimeTraceContext.beginRequest(client, "failover");
        try {
            OccurrenceAddress ran = Identity.occurrence(CLIENT + "#epoch0",
                    SNAPSHOT_REGION, false);
            ConcolicTaskPlan.RuntimeTask atClient = runtime(encoded(
                    "TASK.client", CLIENT + "#epoch0", SNAPSHOT_REGION,
                    SNAPSHOT_ROOT, ran.render(), 1));
            assertEquals("its address answers it", atClient,
                    select(plan(atClient), atClient, node));
            assertNull("a task at the receiver's node is another address",
                    select(plan(unobserved), unobserved, node));
        } finally {
            RuntimeTraceContext.endRequest(call);
        }
        try {
            JsonObject loop = encoded("TASK.loop", NN0 + "#epoch1",
                    BALANCER_REGION, SNAPSHOT_ROOT,
                    NN0 + "#epoch1/region/" + BALANCER_REGION, 1);
            loop.addProperty("rootAuthority", "LOOP_BODY_ROOT");
            runtime(loop);
            fail("expected a plan refusal");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().startsWith(
                    "ROOT_LOOP_OCCURRENCE_UNADDRESSED"));
        }
        ConcolicTaskPlan.RuntimeTask deferred = loopBodyTask(1);
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Arrays.asList(deferred, loopBodyTask(2)));
        RuntimeTraceContext.resetForTests();
        RecordingWindow.open();
        Object caller = new Object();
        RuntimeTraceContext.registerSource(caller,
                new SourceRef("DATANODE", "dn", TARGET, 0L));
        long request = RuntimeTraceContext.beginRequest(caller, "heartbeat");
        try {
            Set<String> admitted = plan.addressLoopRootInvocation(
                    deferred.rootMethod, deferred.rootMethod, null,
                    new Object[0], 11L).admitted;
            assertTrue("an activation of another node is no occurrence of "
                    + "this one: " + admitted, admitted.isEmpty());
            assertTrue(deferred.unansweredAddress(), deferred
                    .unansweredAddress().startsWith(
                            "1 compatible activation(s)"));
        } finally {
            RuntimeTraceContext.endRequest(request);
        }
        assertTrue("the invocation it was admitted for, every sibling hook "
                + "of it", deferred.claimsEnclosingInvocation(11L));
        assertEquals(11L, deferred.enclosingInvocationEvent());
        assertFalse("a second enclosing invocation is not this occurrence",
                deferred.claimsEnclosingInvocation(12L));
        assertEquals(11L, deferred.enclosingInvocationEvent());
    }

    @Test
    public void executionContextIsNotProvenance() throws Exception {
        Object nameNode = new Object();
        Object targetDn = new Object();
        RuntimeTraceContext.registerSource(nameNode,
                new SourceRef("NAMENODE", "nn", NAMENODE, 0L));
        RuntimeTraceContext.registerSource(targetDn,
                new SourceRef("DATANODE", "dn", TARGET, 0L));
        long request = RuntimeTraceContext.beginRequest(nameNode, "heartbeat");
        String header = RuntimeTraceContext.outboundHeader(nameNode, null);
        RuntimeTraceContext.endRequest(request);
        assertNotNull(header);
        long dnRequest = RuntimeTraceContext.beginRequest(targetDn,
                "block-report");
        assertEquals(TARGET + "#epoch0",
                RuntimeTraceContext.currentSource().key());
        long inbound = RuntimeTraceContext.enterInbound(header, "IPC",
                "corr-1", "attempt-1", "REQUEST", new Object(), "");
        assertEquals("the thread still runs as the DataNode",
                TARGET + "#epoch0", RuntimeTraceContext.currentSource().key());
        RuntimeTraceContext.exitInbound(inbound);
        RuntimeTraceContext.endRequest(dnRequest);

        RuntimeTraceContext.resetForTests();
        Object nnc = new Object();
        RuntimeTraceContext.registerSource(nnc,
                new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));
        long scope = RuntimeTraceContext.beginRequest(nnc,
                "refresh-block-keys");
        try {
            assertEquals(SPS + "#epoch0",
                    RuntimeTraceContext.currentSource().key());
            String envelope = RuntimeTraceContext.outboundHeader(nnc, null);
            assertTrue(envelope, envelope.startsWith("1|"));
            assertEquals("source, request key and api, all present",
                    8, envelope.split("\\|", -1).length);
            assertEquals(SPS + "#epoch0",
                    RuntimeTraceContext.activationSource(null).key());
        } finally {
            RuntimeTraceContext.endRequest(scope);
        }
        assertEquals("the unregistered source, as the planner counts it",
                RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                RuntimeTraceContext.activationSource(null).key());
        refuses("no request scope, no envelope",
                () -> RuntimeTraceContext.outboundHeader(nnc, null),
                "requestKey", "requestApi", "!no source");
        refuses("no scope, no envelope",
                () -> RuntimeTraceContext.outboundHeader(nnc, null),
                "the call carried no scope at all",
                "the thread it is sent on carries no", "requestKey",
                "!" + Thread.currentThread().getName());
        Identity.enterFrame("<a.Nnc: void run()>", nnc);
        RuntimeTraceContext.enterRoot(nnc);
        Object partial = RuntimeTraceContext.captureScope();
        refuses("a node is not a request",
                () -> RuntimeTraceContext.outboundHeader(nnc, partial),
                "a partial scope holding only", "source=" + SPS + "#epoch0",
                "!requestKey=");
    }

    @Test
    public void aContextAnswersItsOwnOccurrenceWhoseCountsAloneDiffer() {
        RecordingWindow.open();
        Object client = new Object();
        RuntimeTraceContext.registerSource(client,
                new SourceRef("CLIENT", "client", CLIENT, 0L));
        long call = RuntimeTraceContext.beginRequest(client, "failover");
        try {
            Identity.enterFrame("a.WorkerReceiver#run#292", client);
            OccurrenceAddress ran = Identity.occurrence(CLIENT + "#epoch0",
                    SNAPSHOT_REGION, false);
            assertEquals(1, ran.index().frames().size());
            Frame turn = ran.index().frames().get(0);
            CausalContext other = CausalContext.of(Role.of("CLIENT"),
                    "failover", 7);
            assertEquals("another context of the same shape",
                    ScheduleLog.shape(ran.context()),
                    ScheduleLog.shape(other));
            ConcolicTaskPlan.RuntimeTask own = shaped("TASK.own", ran,
                    ran.context(), turn.iteration() + 1, 2L, true);
            ConcolicTaskPlan alone = new ConcolicTaskPlan(null,
                    singletonList(own));
            assertEquals("the recording opened the region in this context"
                    + " once: the turn it ran under is the planned one", own,
                    alone.select(own.rootHookGroup, SNAPSHOT_ROOT, client,
                            new Object[0]));
            assertTrue(alone.answeredByShape(own));

            ConcolicTaskPlan.RuntimeTask loop = shaped("TASK.loop", ran,
                    ran.context(), turn.iteration() + 1, 2L, false);
            assertNull("in a context the recording opened the region in"
                    + " again, an invocation whose counts differ may be any"
                    + " of them", new ConcolicTaskPlan(null,
                    singletonList(loop)).select(loop.rootHookGroup,
                    SNAPSHOT_ROOT, client, new Object[0]));

            ConcolicTaskPlan.RuntimeTask first = shaped("TASK.first", ran,
                    ran.context(), turn.iteration() + 1, 2L, true);
            ConcolicTaskPlan.RuntimeTask second = shaped("TASK.second", ran,
                    ran.context(), turn.iteration() + 2, 3L, true);
            assertNull("two tasks of the context: neither is answered",
                    new ConcolicTaskPlan(null, Arrays.asList(first, second))
                            .select(first.rootHookGroup, SNAPSHOT_ROOT,
                                    client, new Object[0]));

            ConcolicTaskPlan.RuntimeTask elsewhere = shaped("TASK.elsewhere",
                    ran, other, turn.iteration(), 1L, true);
            ConcolicTaskPlan.RuntimeTask here = shaped("TASK.here", ran,
                    ran.context(), turn.iteration() + 1, 2L, true);
            ConcolicTaskPlan both = new ConcolicTaskPlan(null,
                    Arrays.asList(elsewhere, here));
            assertEquals("its own context's task, not the earlier task of"
                    + " another context", here, both.select(
                    here.rootHookGroup, SNAPSHOT_ROOT, client, new Object[0]));

            ConcolicTaskPlan.RuntimeTask done = shaped("TASK.done", ran,
                    ran.context(), turn.iteration() + 1, 2L, true);
            done.reserveCompletedEvidence();
            ConcolicTaskPlan.RuntimeTask open = shaped("TASK.open", ran,
                    other, turn.iteration(), 1L, true);
            assertNull("a context whose task is done answers no other task",
                    new ConcolicTaskPlan(null, Arrays.asList(open, done))
                            .select(open.rootHookGroup, SNAPSHOT_ROOT, client,
                                    new Object[0]));
            assertTrue(open.unansweredAddress(), open.unansweredAddress()
                    .startsWith("1 compatible activation(s)"));
        } finally {
            RuntimeTraceContext.endRequest(call);
        }
    }

    private static ConcolicTaskPlan.RuntimeTask shaped(String taskId,
            OccurrenceAddress ran, CausalContext context, int turn,
            long rootCall, boolean alone) {
        Frame frame = ran.index().frames().get(0);
        OccurrenceAddress planned = OccurrenceAddress.of(ran.node(),
                ran.regionId(), context, ExecutionIndex.of(singletonList(
                        Frame.of(frame.callSite(), turn))));
        JsonObject row = encoded(taskId, CLIENT + "#epoch0", SNAPSHOT_REGION,
                SNAPSHOT_ROOT, planned.render(), 1);
        JsonArray shape = new JsonArray();
        for (String hop : ScheduleLog.shape(context)) shape.add(hop);
        row.add("contextShape", shape);
        row.add("recordedBeside", new JsonArray());
        row.addProperty("aloneInContext", alone);
        row.addProperty("rootCallId", rootCall);
        return runtime(row);
    }

    private static void refuses(String why, Runnable send, String... says) {
        try {
            send.run();
            fail(why);
        } catch (IllegalStateException refused) {
            String said = String.valueOf(refused.getMessage());
            for (String fragment : says) {
                assertTrue(said, fragment.startsWith("!")
                        ? !said.contains(fragment.substring(1))
                        : said.contains(fragment));
            }
        }
    }

    private static ConcolicTaskPlan.RuntimeTask select(ConcolicTaskPlan plan,
            ConcolicTaskPlan.RuntimeTask asked, Object node) {
        return plan.select(asked.rootHookGroup, SNAPSHOT_ROOT, node,
                new Object[0]);
    }

    private static ConcolicTaskPlan plan(ConcolicTaskPlan.RuntimeTask task) {
        return new ConcolicTaskPlan(null, singletonList(task));
    }

    private static ConcolicTaskPlan.RuntimeTask runtime(JsonObject row) {
        return Fixtures.runtimeTask(row);
    }

    private static OccurrenceAddress address(String node, String region,
                                             CausalContext context) {
        return OccurrenceAddress.of(NodeId.parse(node), region, context,
                ExecutionIndex.empty());
    }

    private static OccurrenceAddress balancerAddress(int ordinal) {
        if (ordinal <= 0) {
            return address(BALANCER, BALANCER_REGION,
                    CausalContext.of(Role.UNKNOWN));
        }
        return OccurrenceAddress.of(NodeId.parse(BALANCER), BALANCER_REGION,
                CausalContext.of(Role.of("BALANCER"), "", 1),
                ExecutionIndex.of(singletonList(Frame.of(
                        "o.a.h.h.s.b.Balancer#dispatch#4", ordinal))));
    }

    private static Endpoint producerAt(int iteration) {
        return Endpoint.of(balancerAddress(3), PORT, ExecutionIndex.of(
                singletonList(Frame.of("a.P#send#2", iteration))), 0);
    }

    private static OccurrenceAddress anchoredAddress(Endpoint producer) {
        return OccurrenceAddress.of(NodeId.parse(BALANCER), BALANCER_REGION,
                CausalContext.of(producer.id(), "a.B#run#9"),
                ExecutionIndex.of(singletonList(Frame.of(
                        "o.a.h.h.s.b.Balancer#dispatch#4", 1))));
    }

    private static ConcolicTaskPlan.RuntimeTask anchoredTask(
            Endpoint producer) {
        return runtime(encoded("TASK.anchor", BALANCER, BALANCER_REGION,
                "<a.B: void run()>", anchoredAddress(producer).render(), 1));
    }

    private static ConcolicTaskPlan.RuntimeTask loopBodyTask(int ordinal)
            throws Exception {
        JsonObject encoded = row();
        encoded.addProperty("taskId", "TASK.SEED.occurrence" + ordinal);
        encoded.addProperty("occurrenceId", OccurrenceAddress.of(
                NodeId.parse(NAMENODE + "#epoch0"),
                encoded.get("regionId").getAsString(),
                CausalContext.of(Role.of("BP_SERVICE_ACTOR"), "", 1),
                ExecutionIndex.of(singletonList(Frame.of(
                        "o.a.h.h.s.b.BlockTokenSecretManager#updateKeys#7",
                        ordinal)))).render());
        encoded.getAsJsonObject("rootSelector")
                .addProperty("invocationOrdinal", ordinal);
        return runtime(encoded);
    }

    private static ConcolicTaskPlan.RuntimeTask handoffTask(int ordinal) {
        JsonObject encoded = encoded("TASK.SEED.address", BALANCER,
                BALANCER_REGION, "<a.B: void run()>",
                balancerAddress(ordinal).render(), ordinal);
        encoded.add("communicationHandoffs", json("{'s':[{'portId':'" + PORT
                + "','handoffLeafPath':'" + PORT + "','side':'IN','javaType':"
                + "'int','captureKind':'CALL_RETURN','definitionUnitIndex':2,"
                + "'declaredCallee':'<a.P: int getKeyId()>',"
                + "'definitionMethod':'<a.B: void run()>'}]}")
                .getAsJsonArray("s"));
        return runtime(encoded);
    }

    private static JsonObject encoded(String taskId, String sourceKey,
            String regionId, String rootMethod, String occurrenceId,
            int ordinal) {
        return json("{'taskId':'" + taskId + "','goalId':'GOAL.1',"
                + "'goalKind':'REGION_PATH_CLOSURE','regionId':'" + regionId
                + "','relationKey':'REL.1','sourceKey':'" + sourceKey
                + "','occurrenceId':'" + occurrenceId + "','rootMethod':'"
                + rootMethod + "','instrumentationSelector':'sel',"
                + "'admission':{'state':'EXECUTABLE'},'inputActions':[],"
                + "'loopBound':{'schemaVersion':1,'defaultBackedgeTraversals'"
                + ":8},'rootSelector':{'kind':'GLOBAL_INVOCATION','method':'"
                + rootMethod + "','invocationOrdinal':" + ordinal
                + ",'causalAnchor':{'sourceKey':'" + sourceKey + "','kind':"
                + "'REGISTERED_SOURCE'}}}");
    }

    private static JsonObject row() throws Exception {
        try (Reader bytes = new InputStreamReader(
                OccurrenceAddressIsNotARequestTest.class.getClassLoader()
                        .getResourceAsStream(PLAN_ROW),
                StandardCharsets.UTF_8)) {
            return JsonParser.parseReader(bytes).getAsJsonObject();
        }
    }
}
