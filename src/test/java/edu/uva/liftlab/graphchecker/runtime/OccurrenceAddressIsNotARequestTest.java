package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Collections;
import java.util.Set;

import static java.util.Collections.singleton;
import static java.util.Collections.singletonList;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * An occurrence is (node, epoch, region, k-th activation) -- not a request.
 *
 * <p>The difference a request makes is still described; it does not withhold
 * the address.</p>
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
    private static final String TARGET_DN = TARGET + "#epoch0";
    private static final String SPS = "hdfs-17899/sps";

    private final Object nameNode = new Object();
    private final Object targetDn = new Object();

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
    }

    /**
     * An occurrence is its address, and admission asks nothing else.
     *
     * <p>The message an activation was reached by is provenance, not a
     * second identity that may veto the first -- not an IN envelope, an OUT
     * anchor, or a causal anchor.</p>
     */
    @Test
    public void theAddressIsTheOnlyAdmission() throws Exception {
        ConcolicTaskPlan.RuntimeTask task = handoffTask(3);
        SymbolicMessageEnvelope.clear();

        assertTrue("the planned occurrence has an IN handoff",
                task.attachSite(PORT) != null);
        assertTrue("its own address answers it",
                task.acceptsRootInvocation(balancerAddress(3)));
        assertFalse("another activation of it does not",
                task.acceptsRootInvocation(balancerAddress(2)));
        assertFalse("nor does an address no activation has",
                task.acceptsRootInvocation(balancerAddress(0)));
        assertFalse("nor does nothing at all",
                task.acceptsRootInvocation(null));

        // And the refusal names the component that parted BEFORE it prints
        // the two addresses.  The 13 OCCURRENCE_ANCHOR_UNMATCHED rows of
        // hdfs-17960 verification #3 differed in one number -- frame 5 of 8,
        // planned iteration 3, ran 0 -- inside ~2500 otherwise identical
        // characters, and reading that took a script over the gap file.
        String oneIteration = task.addressDifference(balancerAddress(2));
        assertTrue(oneIteration, oneIteration.startsWith("differs in frame 0 "
                + "of 1, o.a.h.h.s.b.Balancer#dispatch#4, at iteration 2 and "
                + "not the planned 3; planned "));
        assertTrue("and still carries both addresses whole: " + oneIteration,
                oneIteration.contains("planned "
                        + balancerAddress(3).render() + ", ran at "
                        + balancerAddress(2).render()));
        assertEquals("nothing to name when there is no observed address",
                "the activation ran where this run cannot name it",
                task.addressDifference(null));

        // Two components part, and both are named in address order.
        String noFrames = task.addressDifference(balancerAddress(0));
        assertTrue(noFrames, noFrames.startsWith("differs in its causal "
                + "context (planned " + balancerAddress(3).context().render()
                + ", ran " + balancerAddress(0).context().render() + ") and "
                + "its execution index depth (planned 1 frames, ran 0); "
                + "planned "));

        // An anchor travels as a digest, so the differing INPUT is named,
        // read back from the producer this run filed.
        Endpoint sender = producerAt(1);
        Endpoint resent = producerAt(2);
        Interactions.sent("IPC", "corr-1", "REQUEST", sender);
        Interactions.sent("IPC", "corr-2", "REQUEST", resent);
        String onTheAnchor = anchoredTask(sender)
                .addressDifference(anchoredAddress(resent));
        assertTrue(onTheAnchor, onTheAnchor.startsWith("differs in its "
                + "anchor's producer site index (planned "
                + sender.siteIndex().render() + ", ran "
                + resent.siteIndex().render() + "); planned "));

        // An anchor no message of this run minted is stated as that.
        Interactions.resetForTests();
        String neverMinted = anchoredTask(sender)
                .addressDifference(anchoredAddress(resent));
        assertTrue(neverMinted, neverMinted.startsWith("differs in its "
                + "causal anchor (planned " + sender.id()
                + ", which no message of this run minted; ran " + resent.id()
                + ", which no message of this run minted); planned "));

        // An envelope changes nothing either way: it decides which v_H the
        // attach mints, never which activation this is.
        assertTrue(SymbolicMessageEnvelope.stage(PORT, 41L, null));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertTrue("the address still answers",
                task.acceptsRootInvocation(balancerAddress(3)));
        assertFalse("and still refuses every other occurrence",
                task.acceptsRootInvocation(balancerAddress(4)));


        // Nothing about a source phase is asked, and nothing was observed.
        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NN0, 1L));
        ConcolicTaskPlan.RuntimeTask unobserved = nodeTask(NN0 + "#epoch1", 1);
        assertNotNull("the address is the whole admission",
                plan(unobserved).select(unobserved.rootHookGroup,
                        SNAPSHOT_ROOT, node, new Object[0]));

        // The address is minted where the attribution rule says the root
        // ran (IDENTITY §5), and nothing else says it: the workload calling
        // a NameNode's object on its own thread ran in its own scope, as the
        // recording addressed it, whatever node the receiver is registered
        // to (b20h: FSNamesystem#startActiveServices under the test's
        // transitionToActive).
        RecordingWindow.open();
        Object client = new Object();
        RuntimeTraceContext.registerSource(client,
                new SourceRef("CLIENT", "client", CLIENT, 0L));
        long call = RuntimeTraceContext.beginRequest(client, "failover");
        try {
            OccurrenceAddress ran = Identity.occurrence(CLIENT + "#epoch0",
                    SNAPSHOT_REGION, false);
            ConcolicTaskPlan.RuntimeTask atClient = new ConcolicTaskPlan
                    .RuntimeTask(ExecutionTask.decode(encoded("TASK.client",
                    CLIENT + "#epoch0", SNAPSHOT_REGION, SNAPSHOT_ROOT,
                    ran.render(), 1, "REGISTERED_SOURCE")));
            assertEquals("its address answers it", atClient,
                    plan(atClient).select(atClient.rootHookGroup,
                            SNAPSHOT_ROOT, node, new Object[0]));
            assertNull("a task at the receiver's node is another address",
                    plan(unobserved).select(unobserved.rootHookGroup,
                            SNAPSHOT_ROOT, node, new Object[0]));
        } finally {
            RuntimeTraceContext.endRequest(call);
        }

        // A loop-body task whose occurrence names no k is refused at PLAN.
        try {
            unaddressedLoopTask();
            fail("expected a plan refusal");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().startsWith(
                    "ROOT_LOOP_OCCURRENCE_UNADDRESSED"));
        }

        // A receiver this run never registered is an attribution fact, not a
        // deferred admission: the address decides, the refusal is named, and
        // the task keeps the one invocation it was admitted for and no other.
        // A unique planner-authored OUT anchor used to excuse the missing
        // registration here and be confirmed at close, which let any
        // invocation under the planned request answer any k of that region.
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
            assertTrue(deferred.unansweredAddress(),
                    deferred.unansweredAddress().startsWith(
                            "1 compatible activation(s)"));
        } finally {
            RuntimeTraceContext.endRequest(request);
        }

        assertTrue("the invocation it was admitted for",
                deferred.claimsEnclosingInvocation(11L));
        assertTrue("and every sibling hook of that same entry",
                deferred.claimsEnclosingInvocation(11L));
        assertEquals(11L, deferred.enclosingInvocationEvent());
        assertTrue("a second enclosing invocation is not this occurrence",
                !deferred.claimsEnclosingInvocation(12L));
        assertEquals("and it did not take it either", 11L,
                deferred.enclosingInvocationEvent());
    }

    /**
     * Every planned occurrence is also answered by its shape (IDENTITY §9):
     * an activation of its region on its node, under a chain of its shape,
     * at an address no task plans, takes the planned address -- of the
     * earliest open task of that shape by recorded root call, one task per
     * activation, one activation per task.  An address a task plans is that
     * task's, whatever the plan's order; an address the recording opened is
     * that occurrence; a task stating no shape is answered by its address
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
            JsonObject row = encoded("TASK.declared", NN0 + "#epoch0",
                    SNAPSHOT_REGION, SNAPSHOT_ROOT, declared.render(), 1,
                    "REGISTERED_SOURCE");
            row.add("contextShape", json("{'s':['Root:CLIENT/check']}")
                    .getAsJsonArray("s"));
            ConcolicTaskPlan.RuntimeTask asked = new ConcolicTaskPlan
                    .RuntimeTask(ExecutionTask.decode(row));
            ConcolicTaskPlan.RuntimeTask planned = new ConcolicTaskPlan
                    .RuntimeTask(ExecutionTask.decode(encoded("TASK.ran",
                    NN0 + "#epoch0", SNAPSHOT_REGION, SNAPSHOT_ROOT,
                    ran.render(), 1, "REGISTERED_SOURCE")));

            assertEquals("one woven entry offers both occurrences of the root",
                    asked.rootHookGroup, planned.rootHookGroup);
            assertTrue("a turn of the same root answers it",
                    asked.answers(ran, ScheduleLog::shape));
            assertFalse("a task stating no shape answers by address only",
                    planned.answers(declared, ScheduleLog::shape));
            assertEquals("the address it ran at is a planned task's",
                    planned, new ConcolicTaskPlan(null,
                            Arrays.asList(asked, planned)).select(
                            asked.rootHookGroup, SNAPSHOT_ROOT, node,
                            new Object[0]));
            // And so is every other invocation under that task's anchor:
            // the second call of a planned handshake answers no other
            // handshake's question (hdfs-11741 K2).
            OccurrenceAddress sibling = OccurrenceAddress.of(ran.node(),
                    ran.regionId(), ran.context(), ExecutionIndex.of(
                            singletonList(Frame.of("<a.B: void m()>", 1))));
            assertTrue(new ConcolicTaskPlan(null, Arrays.asList(asked,
                    planned)).occupies(asked.rootHookGroup, sibling));
            assertFalse(plan(asked).occupies(asked.rootHookGroup,
                    sibling));

            // The region entry opens the run's own address; the admission
            // gives it the declared one.
            Identity.occurrence(NN0 + "#epoch0", SNAPSHOT_REGION, true);
            JsonObject knowing = row.deepCopy();
            knowing.add("recordedBeside", json("{'s':['" + ran.id()
                    + "']}").getAsJsonArray("s"));
            ConcolicTaskPlan.RuntimeTask knows = new ConcolicTaskPlan
                    .RuntimeTask(ExecutionTask.decode(knowing));
            assertEquals("the recording's own occurrence answers nothing",
                    null, plan(knows).select(knows.rootHookGroup,
                            SNAPSHOT_ROOT, node, new Object[0]));
            assertTrue(knows.unansweredAddress(), knows.unansweredAddress()
                    .contains("the recording opened this address itself"));
            ConcolicTaskPlan alone = plan(asked);
            assertEquals(asked, alone.select(asked.rootHookGroup,
                    SNAPSHOT_ROOT, node, new Object[0]));
            assertTrue(alone.answeredByShape(asked));
            assertEquals(ran, Identity.answer(declared));
            assertEquals(declared,
                    Identity.currentOccurrence(NN0 + "#epoch0"));

            // The order: activations of one shape take its open tasks
            // earliest recorded root call first, whatever the plan's order,
            // until none is open.
            ConcolicTaskPlan.RuntimeTask late = shaped("TASK.late",
                    checkAddress(2), 200L);
            ConcolicTaskPlan.RuntimeTask early = shaped("TASK.early",
                    checkAddress(3), 100L);
            ConcolicTaskPlan order = new ConcolicTaskPlan(null,
                    Arrays.asList(late, early));
            Object[] answered = {early, late, null};
            for (Object expected : answered) {
                assertEquals(expected, order.select(late.rootHookGroup,
                        SNAPSHOT_ROOT, node, new Object[0]));
            }
            assertTrue(order.answeredByShape(early)
                    && order.answeredByShape(late));
        } finally {
            RuntimeTraceContext.endRequest(request);
            ScheduleLog.resetForTests();
        }
    }

    /**
     * A planned loop body is answered by its shape where its occurrence
     * opens, at its loop root's enclosing entry (no root entry admits a
     * body): the entry binds it, its bodies run under it, and the entry's
     * occurrence takes the planned address once.  A second enclosing entry
     * is another activation (hdfs-adhoc-29: block recovery under another
     * heartbeat's response than the recorded one).
     */
    @Test
    public void aPlannedLoopOccurrenceIsAnsweredAtItsEnclosingEntry() {
        RecordingWindow.open();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("NAMENODE", "nn", NAMENODE, 0L));
        long request = RuntimeTraceContext.beginRequest(node, "heartbeat");
        try {
            JsonObject row = row(PLAN_ROW);
            String regionId = row.get("regionId").getAsString();
            OccurrenceAddress ran = heartbeatAddress(regionId, 1);
            OccurrenceAddress declared = heartbeatAddress(regionId, 2);
            row.addProperty("occurrenceId", declared.render());
            row.add("contextShape", json("{'s':['Root:CLIENT/heartbeat']}")
                    .getAsJsonArray("s"));
            ConcolicTaskPlan.RuntimeTask asked = new ConcolicTaskPlan
                    .RuntimeTask(ExecutionTask.decode(row));
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
            ScheduleLog.resetForTests();
        }
    }

    /** The occurrence of {@code regionId} on the NameNode under the k-th
     *  heartbeat request. */
    private static OccurrenceAddress heartbeatAddress(String regionId,
                                                      int k) {
        return OccurrenceAddress.of(NodeId.parse(NAMENODE + "#epoch0"),
                regionId, CausalContext.of(Role.of("CLIENT"), "heartbeat", k),
                ExecutionIndex.empty());
    }

    /** A task of the snapshot region at {@code address}, of the shape of
     *  every check, the recording's root call {@code rootCall}. */
    private static ConcolicTaskPlan.RuntimeTask shaped(String taskId,
            OccurrenceAddress address, long rootCall) {
        JsonObject row = encoded(taskId, NN0 + "#epoch0", SNAPSHOT_REGION,
                SNAPSHOT_ROOT, address.render(), 1, "REGISTERED_SOURCE");
        row.add("contextShape", json("{'s':['Root:CLIENT/check']}")
                .getAsJsonArray("s"));
        row.addProperty("rootCallId", rootCall);
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(row));
    }

    /** The occurrence of the snapshot region under the k-th check. */
    private static OccurrenceAddress checkAddress(int k) {
        return OccurrenceAddress.of(NodeId.parse(NN0 + "#epoch0"),
                SNAPSHOT_REGION, CausalContext.of(Role.of("CLIENT"), "check",
                        k), ExecutionIndex.empty());
    }

    /**
     * A value arriving over the wire does not say where the receiver ran.
     *
     * <p>Execution context is set by execution-scope events only, never by
     * the SENDER's source out of the message header; the scope the workload
     * opens is what the send hangs off, and a refusal names which of
     * source, request key and request api was absent.</p>
     */
    @Test
    public void executionContextIsNotProvenance() throws Exception {
        RuntimeTraceContext.resetForTests();
        RuntimeTraceContext.registerSource(nameNode,
                new SourceRef("NAMENODE", "nn", NAMENODE, 0L));
        RuntimeTraceContext.registerSource(targetDn,
                new SourceRef("DATANODE", "dn", TARGET, 0L));

        // The NameNode sends; the header states its source, as provenance.
        long request = RuntimeTraceContext.beginRequest(nameNode, "heartbeat");
        String header = RuntimeTraceContext.outboundHeader(nameNode, null);
        RuntimeTraceContext.endRequest(request);
        assertNotNull(header);

        // The DataNode thread is executing as the DataNode.
        long dnRequest = RuntimeTraceContext.beginRequest(targetDn,
                "block-report");
        assertEquals(TARGET_DN, RuntimeTraceContext.currentSource().key());

        // The value arrives through an owner nobody registered: a connection.
        long inbound = RuntimeTraceContext.enterInbound(header, "IPC",
                "corr-1", "attempt-1", "REQUEST", new Object(), "");

        assertEquals("the thread still runs as the DataNode", TARGET_DN,
                RuntimeTraceContext.currentSource().key());

        RuntimeTraceContext.exitInbound(inbound);
        RuntimeTraceContext.endRequest(dnRequest);

        RuntimeTraceContext.resetForTests();
        final Object nnc = new Object();
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
            // And the activation here is that source's, by the ambient arm.
            assertEquals(SPS + "#epoch0",
                    RuntimeTraceContext.activationSource(null).key());
        } finally {
            RuntimeTraceContext.endRequest(scope);
        }

        // Outside it again: nothing attributed.
        assertEquals("the unregistered source, as the planner counts it",
                RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                RuntimeTraceContext.activationSource(null).key());

        // A refused envelope names what was missing, and separates what the
        // call carried from what the thread holds -- different owners.
        refuses("no request scope, no envelope",
                () -> RuntimeTraceContext.outboundHeader(nnc, null),
                "requestKey", "requestApi", "!no source");
        // The thread half is named, the thread is not: this refusal is
        // published as a GapRow (RowRuntime.messageContextRefused), and a
        // row keyed by which pool thread performed the write is a row no
        // two replays can be compared on.
        refuses("no scope, no envelope",
                () -> RuntimeTraceContext.outboundHeader(nnc, null),
                "the call carried no scope at all",
                "the thread it is sent on carries no", "requestKey",
                "!" + Thread.currentThread().getName());
        // The root activation's own frame carries its receiver, as the weave
        // stands it up at every application method: that is what attributes
        // it (Attribution, rule 2).
        Identity.enterFrame("<a.Nnc: void run()>", nnc);
        RuntimeTraceContext.enterRoot(nnc);
        final Object partial = RuntimeTraceContext.captureScope();
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

    /**
     * One occurrence of the balancer region, distinguished by where it ran.
     *
     * <p>Identity v3 has no activation ordinal: two runs of one region are
     * two occurrences because their execution indexes differ, so the fixture
     * varies the index rather than a k.  Index 0 is the address no
     * activation has -- an empty index under an unattributable scope.</p>
     */
    private static OccurrenceAddress balancerAddress(int ordinal) {
        if (ordinal <= 0) {
            return OccurrenceAddress.of(NodeId.parse(BALANCER),
                    BALANCER_REGION,
                    CausalContext.of(Role.UNKNOWN), ExecutionIndex.empty());
        }
        return OccurrenceAddress.of(NodeId.parse(BALANCER), BALANCER_REGION,
                CausalContext.of(Role.of("BALANCER"), "", 1),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of("o.a.h.h.s.b.Balancer#dispatch#4",
                                ordinal))));
    }

    /** One producer endpoint of the balancer, at its {@code k}-th send. */
    private static Endpoint producerAt(int iteration) {
        return Endpoint.of(balancerAddress(3), PORT,
                ExecutionIndex.of(singletonList(
                        Frame.of("a.P#send#2", iteration))), 0);
    }

    /** The occurrence a message from {@code producer} anchors. */
    private static OccurrenceAddress anchoredAddress(Endpoint producer) {
        return OccurrenceAddress.of(NodeId.parse(BALANCER), BALANCER_REGION,
                CausalContext.of(producer.id(), "a.B#run#9"),
                ExecutionIndex.of(singletonList(
                        Frame.of("o.a.h.h.s.b.Balancer#dispatch#4", 1))));
    }

    /** One task planned at that anchored occurrence. */
    private static ConcolicTaskPlan.RuntimeTask anchoredTask(
            Endpoint producer) {
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(
                encoded("TASK.anchor", BALANCER, BALANCER_REGION,
                        "<a.B: void run()>",
                        anchoredAddress(producer).render(), 1,
                        "REGISTERED_SOURCE")));
    }

    private static ConcolicTaskPlan plan(ConcolicTaskPlan.RuntimeTask task) {
        return new ConcolicTaskPlan(null, Collections.singletonList(task));
    }

    /** The lane's own producer plan row, addressed at one enclosing
     *  invocation. */
    private static ConcolicTaskPlan.RuntimeTask loopBodyTask(int ordinal) {
        JsonObject encoded = row(PLAN_ROW);
        String regionId = encoded.get("regionId").getAsString();
        encoded.addProperty("taskId", "TASK.SEED.occurrence" + ordinal);
        encoded.addProperty("occurrenceId", OccurrenceAddress.of(
                NodeId.parse(NAMENODE + "#epoch0"), regionId,
                CausalContext.of(Role.of("BP_SERVICE_ACTOR"), "", 1),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of("o.a.h.h.s.b.BlockTokenSecretManager"
                                + "#updateKeys#7", ordinal)))).render());
        encoded.getAsJsonObject("rootSelector")
                .addProperty("invocationOrdinal", ordinal);
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(encoded));
    }

    /** One planned occurrence with one selected IN communication handoff. */
    private static ConcolicTaskPlan.RuntimeTask handoffTask(int ordinal) {
        JsonObject encoded = encoded("TASK.SEED.address", BALANCER,
                BALANCER_REGION, "<a.B: void run()>",
                balancerAddress(ordinal).render(),
                ordinal, "REGISTERED_SOURCE");
        JsonArray handoffs = new JsonArray();
        handoffs.add(json("{'portId':'" + PORT + "','handoffLeafPath':'" + PORT
                + "','side':'IN','javaType':'int',"
                + "'captureKind':'CALL_RETURN','definitionUnitIndex':2,"
                + "'declaredCallee':'<a.P: int getKeyId()>',"
                + "'definitionMethod':'<a.B: void run()>'}"));
        encoded.add("communicationHandoffs", handoffs);
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(encoded));
    }

    /**
     * One task planned at the address this test's thread actually runs at.
     *
     * <p>No frames are pushed here, so the activation enters at the empty
     * execution index under a scope nobody attributed -- and the plan has to
     * address exactly that, because identity v3 admits an activation by
     * where it was and not by a count of the ones before it.</p>
     */
    private static ConcolicTaskPlan.RuntimeTask nodeTask(String sourceKey,
            int ordinal) {
        String occurrence = OccurrenceAddress.of(NodeId.parse(sourceKey),
                SNAPSHOT_REGION, CausalContext.of(Role.UNKNOWN),
                ExecutionIndex.empty()).render();
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(
                encoded("TASK." + ordinal, sourceKey, SNAPSHOT_REGION,
                        SNAPSHOT_ROOT, occurrence, ordinal,
                        "REGISTERED_SOURCE")));
    }

    /** One loop-body task whose planned occurrence carries no k. */
    private static ConcolicTaskPlan.RuntimeTask unaddressedLoopTask() {
        JsonObject encoded = encoded("TASK.loop", NN0 + "#epoch1",
                BALANCER_REGION, SNAPSHOT_ROOT,
                // No "#k": the occurrence names a region and no activation.
                NN0 + "#epoch1/region/" + BALANCER_REGION, 1,
                "REGISTERED_SOURCE");
        encoded.addProperty("rootAuthority", "LOOP_BODY_ROOT");
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(encoded));
    }

    /** One plan row: the fields {@code ExecutionTask.decode} requires. */
    private static JsonObject encoded(String taskId, String sourceKey,
            String regionId, String rootMethod, String occurrenceId,
            int ordinal, String anchorKind) {
        return json("{'taskId':'" + taskId + "','goalId':'GOAL.1',"
                + "'goalKind':'REGION_PATH_CLOSURE','regionId':'" + regionId
                + "','relationKey':'REL.1','sourceKey':'" + sourceKey
                + "','occurrenceId':'" + occurrenceId + "','rootMethod':'"
                + rootMethod + "','instrumentationSelector':'sel',"
                + "'admission':{'state':'EXECUTABLE'},"
                + "'inputActions':[],'loopBound':{'schemaVersion':1,'defaultBackedgeTraversals':8},"
                + "'rootSelector':{'kind':'GLOBAL_INVOCATION','method':'"
                + rootMethod + "','invocationOrdinal':" + ordinal
                + ",'causalAnchor':{'sourceKey':'" + sourceKey + "','kind':'"
                + anchorKind + "'}}}");
    }

    /** Gson reads single quotes leniently, so one row is a few lines. */
    private static JsonObject json(String row) {
        return new JsonParser().parse(row).getAsJsonObject();
    }

    private static JsonObject row(String resource) {
        try (InputStream bytes = OccurrenceAddressIsNotARequestTest.class
                .getClassLoader().getResourceAsStream(resource)) {
            if (bytes == null) {
                throw new IllegalStateException("missing " + resource);
            }
            return new JsonParser().parse(new InputStreamReader(bytes,
                    StandardCharsets.UTF_8)).getAsJsonObject();
        } catch (Exception failure) {
            throw new IllegalStateException(failure);
        }
    }
}
