package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.Fixtures.json;
import static java.util.Collections.singleton;
import static java.util.Collections.singletonList;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

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

/**
 * An occurrence is (node, epoch, region, k-th activation) -- not a request.
 * The difference a request makes is still described; it does not withhold
 * the address.
 */
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

    /** The address a select computes reads the thread's identity and
     *  lineage: another test's must not leak into it. */
    @Before
    public void startFromNoIdentity() {
        Identity.resetForTests();
        Lineage.resetForTests();
        RuntimeTraceContext.resetForTests();
    }

    @After
    public void clearRuntimeState() {
        SymbolicMessageEnvelope.clear();
        RuntimeTraceContext.resetForTests();
        Interactions.resetForTests();
        ScheduleLog.resetForTests();
    }

    /**
     * An occurrence is its address, and admission asks nothing else: the
     * message an activation was reached by is provenance, not a second
     * identity that may veto the first.  The refusal names the component
     * that parted BEFORE the two addresses (hdfs-17960 #3: 13 rows differed
     * in one number inside ~2500 identical characters), an anchor's
     * differing INPUT read back from the producer this run filed; the
     * address is minted where the attribution rule says the root ran
     * (IDENTITY §5; b20h: startActiveServices under the test's
     * transitionToActive); a loop body naming no k is refused at PLAN; a
     * receiver this run never registered leaves the address to decide, the
     * task keeping the one invocation it was admitted for.
     */
    @Test
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
        Interactions.sent("IPC", "corr-1", "REQUEST", sender);
        Interactions.sent("IPC", "corr-2", "REQUEST", resent);
        String onTheAnchor = anchoredTask(sender).addressDifference(
                anchoredAddress(resent));
        assertTrue(onTheAnchor, onTheAnchor.startsWith("differs in its "
                + "anchor's producer site index (planned "
                + sender.siteIndex().render() + ", ran "
                + resent.siteIndex().render() + "); planned "));
        Interactions.resetForTests();
        String neverMinted = anchoredTask(sender).addressDifference(
                anchoredAddress(resent));
        assertTrue(neverMinted, neverMinted.startsWith("differs in its "
                + "causal anchor (planned " + sender.id() + ", which no "
                + "message of this run minted; ran " + resent.id() + ", which"
                + " no message of this run minted); planned "));
        // An envelope decides which v_H the attach mints, never which
        // activation this is.
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
        // A unique planner-authored OUT anchor once excused the missing
        // registration and let any invocation under the planned request
        // answer any k of that region.
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

    /**
     * Every planned occurrence is also answered by its shape (IDENTITY §9):
     * an activation of its region on its node, under a chain of its shape,
     * at an address no task plans, takes the planned address -- of the
     * earliest open task of that shape by recorded root call, one task per
     * activation.  An address a task plans is that task's, whatever the
     * plan's order (the second call of a planned handshake answers no other
     * handshake's question: hdfs-11741 K2); an address the recording opened
     * is that occurrence; a task stating no shape is answered by its address
     * alone.
     */
    @Test
    public void aPlannedOccurrenceIsAnsweredByItsShape() {
        RecordingWindow.open();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("NAMENODE", "nn", NN0, 0L));
        long request = RuntimeTraceContext.beginRequest(node, "check");
        try {
            OccurrenceAddress ran = checkAddress(1);
            OccurrenceAddress declared = checkAddress(2);
            JsonObject row = shapedRow("TASK.declared", declared, -1L);
            ConcolicTaskPlan.RuntimeTask asked = runtime(row);
            ConcolicTaskPlan.RuntimeTask planned = runtime(encoded("TASK.ran",
                    NN0 + "#epoch0", SNAPSHOT_REGION, SNAPSHOT_ROOT,
                    ran.render(), 1));
            assertEquals("one woven entry offers both occurrences",
                    asked.rootHookGroup, planned.rootHookGroup);
            assertTrue("a turn of the same root answers it",
                    asked.answers(ran, ScheduleLog::shape));
            assertFalse("a task stating no shape answers by address only",
                    planned.answers(declared, ScheduleLog::shape));
            ConcolicTaskPlan both = new ConcolicTaskPlan(null,
                    Arrays.asList(asked, planned));
            assertEquals("the address it ran at is a planned task's",
                    planned, select(both, asked, node));
            OccurrenceAddress sibling = OccurrenceAddress.of(ran.node(),
                    ran.regionId(), ran.context(), ExecutionIndex.of(
                            singletonList(Frame.of("<a.B: void m()>", 1))));
            assertTrue(both.occupies(asked.rootHookGroup, sibling));
            assertFalse(plan(asked).occupies(asked.rootHookGroup, sibling));
            // The region entry opens the run's own address; the admission
            // gives it the declared one.
            Identity.occurrence(NN0 + "#epoch0", SNAPSHOT_REGION, true);
            JsonObject knowing = row.deepCopy();
            knowing.add("recordedBeside", json("{'s':['" + ran.id()
                    + "']}").getAsJsonArray("s"));
            ConcolicTaskPlan.RuntimeTask knows = runtime(knowing);
            assertNull("the recording's own occurrence answers nothing",
                    select(plan(knows), knows, node));
            assertTrue(knows.unansweredAddress(), knows.unansweredAddress()
                    .contains("the recording opened this address itself"));
            ConcolicTaskPlan alone = plan(asked);
            assertEquals(asked, select(alone, asked, node));
            assertTrue(alone.answeredByShape(asked));
            assertEquals(ran, Identity.answer(declared));
            assertEquals(declared, Identity.currentOccurrence(NN0
                    + "#epoch0"));
            // Activations of one shape take its open tasks earliest
            // recorded root call first, whatever the plan's order.
            ConcolicTaskPlan.RuntimeTask late = runtime(shapedRow("TASK.late",
                    checkAddress(2), 200L));
            ConcolicTaskPlan.RuntimeTask early = runtime(shapedRow(
                    "TASK.early", checkAddress(3), 100L));
            ConcolicTaskPlan order = new ConcolicTaskPlan(null,
                    Arrays.asList(late, early));
            for (Object expected : new Object[] {early, late, null}) {
                assertEquals(expected, select(order, late, node));
            }
            assertTrue(order.answeredByShape(early)
                    && order.answeredByShape(late));
        } finally {
            RuntimeTraceContext.endRequest(request);
        }
    }

    /**
     * A planned loop body is answered by its shape where its occurrence
     * opens, at its loop root's enclosing entry: the entry binds it, its
     * bodies run under it, and the entry's occurrence takes the planned
     * address once.  A second enclosing entry is another activation
     * (hdfs-adhoc-29: block recovery under another heartbeat's response).
     */
    @Test
    public void aPlannedLoopOccurrenceIsAnsweredAtItsEnclosingEntry()
            throws Exception {
        RecordingWindow.open();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("NAMENODE", "nn", NAMENODE, 0L));
        long request = RuntimeTraceContext.beginRequest(node, "heartbeat");
        try {
            JsonObject row = row();
            String regionId = row.get("regionId").getAsString();
            OccurrenceAddress ran = heartbeatAddress(regionId, 1);
            OccurrenceAddress declared = heartbeatAddress(regionId, 2);
            row.addProperty("occurrenceId", declared.render());
            row.add("contextShape", json("{'s':['Root:CLIENT/heartbeat']}")
                    .getAsJsonArray("s"));
            ConcolicTaskPlan.RuntimeTask asked = runtime(row);
            ConcolicTaskPlan plan = plan(asked);
            Identity.occurrence(NAMENODE + "#epoch0", regionId, true);
            ConcolicTaskPlan.LoopRootAdmission first =
                    plan.addressLoopRootInvocation(asked.loopRootHookGroup,
                            asked.rootMethod, node, new Object[0], 21L);
            assertEquals(asked, first.answered);
            assertEquals(singleton(asked.taskId), first.admitted);
            assertEquals(21L, asked.enclosingInvocationEvent());
            assertEquals(ran, Identity.answer(declared));
            assertEquals(declared,
                    Identity.currentOccurrence(NAMENODE + "#epoch0"));
            ConcolicTaskPlan.LoopRootAdmission second =
                    plan.addressLoopRootInvocation(asked.loopRootHookGroup,
                            asked.rootMethod, node, new Object[0], 22L);
            assertNull(second.answered);
            assertTrue(second.admitted.isEmpty());
            assertTrue(asked.unansweredAddress(), asked.unansweredAddress()
                    .contains("a second enclosing invocation"));
        } finally {
            RuntimeTraceContext.endRequest(request);
        }
    }

    /**
     * A value arriving over the wire does not say where the receiver ran:
     * execution context is set by execution-scope events only, never by the
     * SENDER's source out of the message header; the scope the workload
     * opens is what the send hangs off, and a refusal names which of
     * source, request key and request api was absent -- never the thread
     * (the refusal is a GapRow, and a row keyed by a pool thread compares
     * across no two replays).
     */
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
        // The value arrives through an owner nobody registered.
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
        // The root activation's own frame carries its receiver (rule 2).
        Identity.enterFrame("<a.Nnc: void run()>", nnc);
        RuntimeTraceContext.enterRoot(nnc);
        Object partial = RuntimeTraceContext.captureScope();
        refuses("a node is not a request",
                () -> RuntimeTraceContext.outboundHeader(nnc, partial),
                "a partial scope holding only", "source=" + SPS + "#epoch0",
                "!requestKey=");
    }

    /** The send refuses, naming each fragment ({@code !x}: not naming it). */
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

    /** The occurrence of {@code regionId} on the NameNode under the k-th
     *  heartbeat request. */
    private static OccurrenceAddress heartbeatAddress(String regionId,
                                                      int k) {
        return address(NAMENODE + "#epoch0", regionId,
                CausalContext.of(Role.of("CLIENT"), "heartbeat", k));
    }

    /** The occurrence of the snapshot region under the k-th check. */
    private static OccurrenceAddress checkAddress(int k) {
        return address(NN0 + "#epoch0", SNAPSHOT_REGION,
                CausalContext.of(Role.of("CLIENT"), "check", k));
    }

    /** A task of the snapshot region at {@code address}, of the shape of
     *  every check, the recording's root call {@code rootCall} (-1: none). */
    private static JsonObject shapedRow(String taskId,
                                        OccurrenceAddress address,
                                        long rootCall) {
        JsonObject row = encoded(taskId, NN0 + "#epoch0", SNAPSHOT_REGION,
                SNAPSHOT_ROOT, address.render(), 1);
        row.add("contextShape", json("{'s':['Root:CLIENT/check']}")
                .getAsJsonArray("s"));
        if (rootCall >= 0L) row.addProperty("rootCallId", rootCall);
        return row;
    }

    /**
     * One occurrence of the balancer region, distinguished by where it ran:
     * identity v3 has no activation ordinal, so the fixture varies the
     * index.  Index 0 is the address no activation has -- an empty index
     * under an unattributable scope.
     */
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

    /** One producer endpoint of the balancer, at its {@code k}-th send. */
    private static Endpoint producerAt(int iteration) {
        return Endpoint.of(balancerAddress(3), PORT, ExecutionIndex.of(
                singletonList(Frame.of("a.P#send#2", iteration))), 0);
    }

    /** The occurrence a message from {@code producer} anchors. */
    private static OccurrenceAddress anchoredAddress(Endpoint producer) {
        return OccurrenceAddress.of(NodeId.parse(BALANCER), BALANCER_REGION,
                CausalContext.of(producer.id(), "a.B#run#9"),
                ExecutionIndex.of(singletonList(Frame.of(
                        "o.a.h.h.s.b.Balancer#dispatch#4", 1))));
    }

    /** One task planned at that anchored occurrence. */
    private static ConcolicTaskPlan.RuntimeTask anchoredTask(
            Endpoint producer) {
        return runtime(encoded("TASK.anchor", BALANCER, BALANCER_REGION,
                "<a.B: void run()>", anchoredAddress(producer).render(), 1));
    }

    /** The lane's own producer plan row, addressed at one enclosing
     *  invocation. */
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

    /** One planned occurrence with one selected IN communication handoff. */
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

    /** One plan row: the fields {@code ExecutionTask.decode} requires. */
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
