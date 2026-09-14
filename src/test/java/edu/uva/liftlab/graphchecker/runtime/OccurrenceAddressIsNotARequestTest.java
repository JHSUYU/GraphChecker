package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import org.junit.After;
import org.junit.Test;

import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static java.util.Collections.singletonList;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
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
    private static final String SNAPSHOT_REGION = "REGION.9492ec77";
    private static final String SNAPSHOT_ROOT =
            "<a.Manager: void deleteSnapshot()>";
    private static final String NAMENODE = "hdfs-17899/nn0";
    private static final String TARGET = "hdfs-17899/target-dn";
    private static final String NN = NAMENODE + "#epoch0";
    private static final String SOURCE_DN = "hdfs-17899/source-dn#epoch0";
    private static final String TARGET_DN = TARGET + "#epoch0";
    private static final String KEYS_REGION = "REGION.16ba41cf";
    private static final String STATIC_ROOT =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: "
                    + "ExportedBlockKeys convert(ExportedBlockKeysProto)>";
    private static final String SPS = "hdfs-17899/sps";

    private final Object nameNode = new Object();
    private final Object sourceDn = new Object();
    private final Object targetDn = new Object();

    @After
    public void clearRuntimeState() {
        SymbolicMessageEnvelope.clear();
        RuntimeTraceContext.resetForTests();
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
                task.communicationHandoff(PORT, false) != null);
        assertTrue("its own address answers it",
                task.acceptsRootInvocation(balancerAddress(3)));
        assertFalse("another activation of it does not",
                task.acceptsRootInvocation(balancerAddress(2)));
        assertFalse("nor does an unnamed address",
                task.acceptsRootInvocation(balancerAddress(0)));

        // An envelope naming another producer changes nothing either way: it
        // decides which v_H the attach mints, never which activation this is.
        assertTrue(SymbolicMessageEnvelope.stage(PORT, 41L, "task-x",
                "some-other-producer#9", singletonList("some-consumer#4")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertTrue("the address still answers",
                task.acceptsRootInvocation(balancerAddress(3)));
        assertFalse("and still refuses every other k",
                task.acceptsRootInvocation(balancerAddress(4)));

        // Noting the request an activation entered is not a refusal.
        ConcolicTaskPlan.RuntimeTask producer = task();
        producer.noteRequestContext("matching root entered request "
                + "client#epoch0/record-ordered-deletes#1 instead of "
                + "nn0#epoch1/restart-namenode#1");
        assertTrue("a request note leaves the address answered",
                producer.unansweredAddress().startsWith(
                        "0 compatible activation(s)"));

        // Nothing about a source phase is asked, and nothing was observed.
        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NN0, 1L));
        ConcolicTaskPlan.RuntimeTask unobserved = nodeTask(NN0 + "#epoch1", 1);
        assertNotNull("the address is the whole admission",
                plan(unobserved).select(unobserved.rootHookGroupKey(),
                        SNAPSHOT_ROOT, node, new Object[0]));

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
        CausynthTraceRecorder.setRecordingStartedForTests(true);
        Object caller = new Object();
        RuntimeTraceContext.registerSource(caller,
                new SourceRef("DATANODE", "dn", TARGET, 0L));
        long request = RuntimeTraceContext.beginRequest(caller, "heartbeat");
        try {
            Map<String, Integer> admitted = plan.addressLoopRootInvocation(
                    deferred.rootMethod, deferred.rootMethod, null,
                    new Object[0], 11L);

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
     * The k in "k-th activation" is counted inside one epoch and inside one
     * request family.
     *
     * <p>One JVM runs both lifecycles of a node it restarts, and one region
     * answers two request families; each activation is the k-th of its own
     * epoch and family.  The epoch refusal is on evidence, not on
     * registration order.</p>
     */
    @Test
    public void kIsCountedInsideOneEpochAndOneFamily() throws Exception {
        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NN0, 0L));
        ConcolicTaskPlan.RuntimeTask epochOne = nodeTask(NN0 + "#epoch1", 1);
        ConcolicTaskPlan plan = plan(epochOne);

        assertNull("the first pre-restart activation is epoch 0's first",
                plan.select(epochOne.rootHookGroupKey(), SNAPSHOT_ROOT, node,
                        new Object[0]));
        assertNull("and the second is epoch 0's second",
                plan.select(epochOne.rootHookGroupKey(), SNAPSHOT_ROOT, node,
                        new Object[0]));

        RuntimeTraceContext.restartSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NN0, 1L));

        assertNotNull("the third activation is epoch 1's first",
                plan.select(epochOne.rootHookGroupKey(), SNAPSHOT_ROOT, node,
                        new Object[0]));

        // An epoch-0 activation is declined because it ran at epoch 0, an
        // epoch-1 one is answered whenever it arrives, and an activation
        // nothing attributed is still the occurrence.
        String declined = ConcolicTaskPlan.lifecycleMismatch(NN0 + "#epoch1",
                Collections.singleton(NN0 + "#epoch0"));
        assertFalse("an epoch-0 activation is not the epoch-1 occurrence",
                declined.isEmpty());
        assertTrue(declined, declined.contains(NN0 + "#epoch0"));
        assertTrue(declined, declined.contains(NN0 + "#epoch1"));
        assertEquals("the epoch-1 activation answers", "",
                ConcolicTaskPlan.lifecycleMismatch(NN0 + "#epoch1",
                        Collections.singleton(NN0 + "#epoch1")));
        assertEquals("an activation nothing attributed is still it", "",
                ConcolicTaskPlan.lifecycleMismatch(NN0 + "#epoch1",
                        Collections.<String>emptySet()));
        assertNotEquals("epoch 0 is another bucket",
                epochOne.invocationCounterKey(NN0 + "#epoch1"),
                epochOne.invocationCounterKey(NN0 + "#epoch0"));

        // Counting and matching use one scope, and the request is in
        // neither: which request an activation was reached under is
        // information about it, and information does not partition a count.
        ConcolicTaskPlan.RuntimeTask task = task();
        assertFalse("the request key is not in the bucket",
                task.invocationCounterKey().contains("/request/"));
        assertEquals("nor is the request family it used to be folded to",
                task.invocationCounterKey(task.sourceKey),
                task.invocationCounterKey());

        // The k-th activation of one region on one node and epoch, counted
        // in one bucket whatever request each arrived under.
        Map<String, Integer> counted = new LinkedHashMap<>();
        counted.put(task.invocationCounterKey(task.sourceKey), 2);
        OccurrenceAddress observed = task.observedAddress(task.sourceKey,
                counted);

        assertEquals(2, observed.ordinal());
        assertTrue("and it is the address the same bucket is keyed on",
                observed.matches(OccurrenceAddress.parse(
                        observed.render())));
    }

    /**
     * An activation is counted, and addressed, where it RAN.
     *
     * <p>Three nodes in one JVM enter through a static decoder that belongs
     * to no node, so what says where an activation ran is the execution
     * context its thread carries.  The gate is evidence: another node
     * refuses, the planned node decides, and an absence says nothing at
     * all -- a flip replay carries no inherited context.</p>
     */
    @Test
    public void anActivationIsCountedWhereItRan() throws Exception {
        registerCluster();
        ConcolicTaskPlan.RuntimeTask sourceTask =
                sharedRootTask("TASK.source", SOURCE_DN);
        ConcolicTaskPlan.RuntimeTask targetTask =
                sharedRootTask("TASK.target", TARGET_DN);
        // Plan order is the campaign's: source-dn's task is offered first.
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Arrays.asList(sourceTask, targetTask));

        assertNull("the NameNode's decode of target-dn's heartbeat is nn0's",
                decode(plan, sourceTask, nameNode));
        assertSame("target-dn's own decode is target-dn's first activation",
                targetTask, decode(plan, sourceTask, targetDn));
        assertNull("the NameNode's decode of source-dn's heartbeat is nn0's",
                decode(plan, sourceTask, nameNode));
        assertSame("source-dn's own decode is source-dn's first activation",
                sourceTask, decode(plan, sourceTask, sourceDn));
        assertNull("an activation no node claimed is nobody's occurrence",
                decode(plan, sourceTask, null));

        // Lane B2: a heartbeat runs before the workload registers the DataNode,
        // so this run can name no node for it.  It is the unregistered source's
        // activation -- the planner's third arm -- so the heartbeat that does
        // carry the node is still target-dn's FIRST.
        registerCluster();
        ConcolicTaskPlan.RuntimeTask target =
                sharedRootTask("TASK.target", TARGET_DN);
        ConcolicTaskPlan targetPlan = plan(target);

        assertNull("an activation nobody attributed is not target-dn's",
                decode(targetPlan, target, null));
        assertSame("the unstamped one took no k from target-dn",
                target, decode(targetPlan, target, targetDn));

        // And the refusal says which node the run attributed the activation to:
        // "activation 2, not 1" read identically for the planned node's real
        // second and for one nobody could name a node for.
        assertNull(decode(targetPlan, target, targetDn));
        assertTrue(target.unansweredAddress(),
                target.unansweredAddress().contains(
                        "(attributed to " + TARGET_DN + ")"));

        // The bucket is the node that ran it, whatever the plan names.
        assertEquals("the NameNode's activation counts as the NameNode's",
                NN, ConcolicTaskPlan.countedLifecycle(target,
                        RuntimeTraceContext.sourceFor(nameNode)));
        assertEquals("an activation nothing attributed counts in the "
                        + "unregistered source, as the planner counts it",
                RuntimeTraceContext.UNREGISTERED_SOURCE.key(),
                ConcolicTaskPlan.countedLifecycle(target, null));

        // The gate, on the plan row the campaign carries.
        ConcolicTaskPlan.RuntimeTask planned = task();
        assertEquals("an absent inherited source is not a mismatch", "",
                ConcolicTaskPlan.sourceMismatch(planned, null,
                        RuntimeTraceContext.current()));
        assertEquals("a registration naming the planned source decides", "",
                ConcolicTaskPlan.sourceMismatch(planned,
                        RuntimeTraceContext.sourceFor(nameNode),
                        RuntimeTraceContext.current()));
        Object elsewhere = new Object();
        RuntimeTraceContext.registerSource(elsewhere,
                new SourceRef("DATANODE", "dn", "hdfs-17899/dn9", 0L));
        String refusal = ConcolicTaskPlan.sourceMismatch(planned,
                RuntimeTraceContext.sourceFor(elsewhere),
                RuntimeTraceContext.current());
        assertTrue(refusal, refusal.contains("receiver belonged to"));
        assertTrue(refusal, refusal.contains("hdfs-17899/dn9"));

        String unattributed = planned.rootContextSelector.unconfirmed(
                Collections.<String>emptySet());
        assertTrue(unattributed, unattributed.contains("nothing attributed it"
                + " to any node"));
        assertTrue(unattributed, unattributed.contains(planned.sourceKey));
        String otherNode = planned.rootContextSelector.unconfirmed(
                Collections.singleton(SOURCE_DN));
        assertTrue(otherNode, otherNode.contains("occurrence ran on"));
        assertTrue(otherNode, otherNode.contains("source-dn"));
    }

    /**
     * The counting window opens when the workload starts recording.
     *
     * <p>The plan counts what the recording saw; a replay that counts what
     * the process did beforehand numbers a different population, and an
     * activation before the window is compared against no ordinal.</p>
     */
    @Test
    public void theCountingWindowOpensWhenTheWorkloadRecords() {
        RuntimeTraceContext.resetForTests();
        CausynthTraceRecorder.setRecordingStartedForTests(false);
        ConcolicTaskPlan.RuntimeTask task = task();
        ConcolicTaskPlan plan = plan(task);
        // Outside the window means before the workload started recording, not
        // before it named a source.
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("NAMENODE", "nn", NAMENODE, 0L));

        assertFalse("a named source is state, not the window",
                RuntimeTraceContext.recordingWindowOpen());
        assertTrue("the cluster start is outside the window",
                plan.addressLoopRootInvocation(task.rootMethod,
                        task.rootMethod, node, new Object[0], 11L).isEmpty());
        assertTrue("and it is not a candidate that failed to answer",
                task.unansweredAddress().startsWith(
                        "0 compatible activation(s)"));
        assertFalse("nothing is compared against a null ordinal",
                task.unansweredAddress().contains("invocation null"));

        CausynthTraceRecorder.startRecording();

        assertTrue("the workload opens the window by recording",
                RuntimeTraceContext.recordingWindowOpen());
        assertEquals("the first activation the recording saw is occurrence 1",
                Collections.singletonMap(task.taskId, 1),
                plan.addressLoopRootInvocation(task.rootMethod,
                        task.rootMethod, node, new Object[0], 12L));
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
        String header = RuntimeTraceContext.outboundHeader(nameNode);
        RuntimeTraceContext.endRequest(request);
        assertNotNull(header);

        // The DataNode thread is executing as the DataNode.
        long dnRequest = RuntimeTraceContext.beginRequest(targetDn,
                "block-report");
        assertEquals(TARGET_DN, RuntimeTraceContext.currentSource().key());

        // The value arrives through an owner nobody registered: a connection.
        long inbound = RuntimeTraceContext.enterInbound(header, "IPC",
                "corr-1", "attempt-1", "REQUEST", new Object());

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
            String envelope = RuntimeTraceContext.outboundHeader(nnc);
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
                RuntimeTraceContext.UNREGISTERED_SOURCE.key(),
                RuntimeTraceContext.activationSource(null).key());

        // A refused envelope names what was missing, and separates what the
        // call carried from what the thread holds -- different owners.
        refuses("no request scope, no envelope",
                () -> RuntimeTraceContext.outboundHeader(nnc),
                "requestKey", "requestApi", "!no source");
        refuses("no scope, no envelope",
                () -> RuntimeTraceContext.outboundHeader(nnc, null),
                "the call carried no scope at all",
                "thread " + Thread.currentThread().getName(), "requestKey");
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

    /** The cluster of lane VM9: three nodes, one JVM. */
    private void registerCluster() {
        RuntimeTraceContext.resetForTests();
        RuntimeTraceContext.registerSource(nameNode,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NAMENODE, 0L));
        RuntimeTraceContext.registerSource(sourceDn,
                new SourceRef("CLUSTER_NODE", "DATANODE",
                        "hdfs-17899/source-dn", 0L));
        RuntimeTraceContext.registerSource(targetDn,
                new SourceRef("CLUSTER_NODE", "DATANODE", TARGET, 0L));
    }

    /** Enters the root once, inside {@code node}'s request scope if any. */
    private ConcolicTaskPlan.RuntimeTask decode(ConcolicTaskPlan plan,
            ConcolicTaskPlan.RuntimeTask any, Object node) {
        long request = node == null ? 0L
                : RuntimeTraceContext.beginRequest(node, "heartbeat");
        try {
            return plan.select(any.rootHookGroupKey(), any.rootMethod, null,
                    new Object[0]);
        } finally {
            if (node != null) RuntimeTraceContext.endRequest(request);
        }
    }

    private static OccurrenceAddress balancerAddress(int ordinal) {
        return OccurrenceAddress.of(BALANCER, BALANCER_REGION, ordinal);
    }

    private static ConcolicTaskPlan plan(ConcolicTaskPlan.RuntimeTask task) {
        return new ConcolicTaskPlan(null, Collections.singletonList(task));
    }

    /** The lane's own producer plan row, as the campaign carries it. */
    private static ConcolicTaskPlan.RuntimeTask task() {
        return new ConcolicTaskPlan.RuntimeTask(
                ExecutionTask.decode(row(PLAN_ROW)));
    }

    /** The same plan row, addressed at one enclosing invocation. */
    private static ConcolicTaskPlan.RuntimeTask loopBodyTask(int ordinal) {
        JsonObject encoded = row(PLAN_ROW);
        String regionId = encoded.get("regionId").getAsString();
        encoded.addProperty("taskId", "TASK.SEED.occurrence" + ordinal);
        encoded.addProperty("occurrenceId", NAMENODE + "#epoch0/region/"
                + regionId + "#" + ordinal);
        encoded.getAsJsonObject("rootSelector")
                .addProperty("invocationOrdinal", ordinal);
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(encoded));
    }

    /** One planned occurrence with one selected IN communication handoff. */
    private static ConcolicTaskPlan.RuntimeTask handoffTask(int ordinal) {
        JsonObject encoded = encoded("TASK.SEED.address", BALANCER,
                BALANCER_REGION, "<a.B: void run()>",
                BALANCER + "/region/" + BALANCER_REGION + "#" + ordinal,
                ordinal, "REGISTERED_SOURCE");
        JsonArray handoffs = new JsonArray();
        handoffs.add(json("{'portId':'" + PORT + "','handoffLeafPath':'" + PORT
                + "','side':'IN','direction':'RESPONSE','javaType':'int',"
                + "'captureKind':'CALL_RETURN','definitionUnitIndex':2,"
                + "'declaredCallee':'<a.P: int getKeyId()>',"
                + "'definitionMethod':'<a.B: void run()>'}"));
        encoded.add("communicationHandoffs", handoffs);
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(encoded));
    }

    /** One planned activation of the snapshot region on {@code sourceKey}. */
    private static ConcolicTaskPlan.RuntimeTask nodeTask(String sourceKey,
            int ordinal) {
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(
                encoded("TASK." + ordinal, sourceKey, SNAPSHOT_REGION,
                        SNAPSHOT_ROOT, sourceKey + "/region/" + SNAPSHOT_REGION
                                + "#" + ordinal, ordinal,
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

    /**
     * One occurrence of a root belonging to no node, named as the planner mints
     * it: the address carries the recording's request family, (source, api)
     * and no request ordinal, and the anchor is the thread's context.
     */
    private static ConcolicTaskPlan.RuntimeTask sharedRootTask(String taskId,
            String sourceKey) {
        JsonObject encoded = encoded(taskId, sourceKey, KEYS_REGION,
                STATIC_ROOT, sourceKey + "/region/" + KEYS_REGION + "@"
                        + sourceKey + "/heartbeat#1", 1, "INHERITED_CONTEXT");
        JsonObject anchor = encoded.getAsJsonObject("rootSelector")
                .getAsJsonObject("causalAnchor");
        anchor.addProperty("requestApi", "heartbeat");
        anchor.addProperty("requestKey", sourceKey + "/request/heartbeat#1");
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
                + "'admission':{'state':'EXECUTABLE'},'branches':[],"
                + "'inputActions':[],'loopBound':{'schemaVersion':1},"
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
