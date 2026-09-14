package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * An activation is counted, and addressed, where it RAN.
 *
 * <p>Lane VM9's shape: hdfs-17899 bug3 runs nn0, source-dn and target-dn in
 * one JVM, and the regions that fail there enter through code that belongs to
 * no node -- a static protobuf decoder ({@code PBHelper.convert}) and one IPC
 * connection object shared by both DataNodes.  Neither has a registration of
 * its own, so the only thing that says which node an activation ran on is the
 * execution context its thread carries, which is what the recording stamped
 * on {@code METHOD_ENTER} and what the planner named and counted the
 * occurrence by.</p>
 *
 * <p>The replay asked a different question of the same inputs.  Its bucket
 * was the receiver's registration, else the thread's context <em>only when
 * that context already named the planned node</em>, else the plan's own key
 * -- so every activation the run attributed to another node fell into the
 * planned node's bucket, and the address compared nothing but k.  Two
 * consequences, both in lane VM9's rows:</p>
 *
 * <ul>
 *   <li>{@code REGION.16ba41cf#1} on target-dn: five activations of the
 *   static decoder (nn0, target-dn, nn0, source-dn, unattributed) all counted
 *   in target-dn's bucket, so the planned first was answered by "invocation 2
 *   instead of 1", and 3, 4 and 5 after it.</li>
 *   <li>{@code REGION.763d087e#1}: the one activation that ran under
 *   target-dn was ordinal 1 in source-dn's bucket too, and the source-dn task
 *   is earlier in the plan, so it claimed target-dn's occurrence -- leaving
 *   target-dn's task with no candidate at all
 *   ({@code REGION_ROOT_NEVER_EXECUTED}) and the stolen activation refused at
 *   close ("occurrence ran on [hdfs-17899/target-dn#epoch0], but its anchor
 *   names hdfs-17899/source-dn#epoch0").</li>
 * </ul>
 */
public class ActivationIsCountedWhereItRanTest {
    private static final String NN = "hdfs-17899/nn0#epoch0";
    private static final String SOURCE_DN = "hdfs-17899/source-dn#epoch0";
    private static final String TARGET_DN = "hdfs-17899/target-dn#epoch0";
    private static final String REGION = "REGION.16ba41cf";
    private static final String STATIC_ROOT =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper: "
                    + "ExportedBlockKeys convert(ExportedBlockKeysProto)>";
    private static final String CONNECTION_ROOT =
            "<org.apache.hadoop.ipc.Client$Connection: void sendRpcRequest("
                    + "org.apache.hadoop.ipc.Client$Call)>";

    private final Object nameNode = new Object();
    private final Object sourceDn = new Object();
    private final Object targetDn = new Object();

    @After
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
    }

    private void registerCluster() {
        RuntimeTraceContext.resetForTests();
        RuntimeTraceContext.registerSource(nameNode,
                new SourceRef("CLUSTER_NODE", "NAMENODE",
                        "hdfs-17899/nn0", 0L));
        RuntimeTraceContext.registerSource(sourceDn,
                new SourceRef("CLUSTER_NODE", "DATANODE",
                        "hdfs-17899/source-dn", 0L));
        RuntimeTraceContext.registerSource(targetDn,
                new SourceRef("CLUSTER_NODE", "DATANODE",
                        "hdfs-17899/target-dn", 0L));
    }

    /**
     * The five decodes of lane VM9, in the order the recording holds them.
     *
     * <p>Each task addresses the first activation on its own node, and gets
     * exactly the one that ran there.  The NameNode's own two are nobody's
     * occurrence here: no task in this plan is addressed to nn0.</p>
     */
    @Test
    public void eachNodesFirstActivationAnswersOnlyThatNodesTask() {
        registerCluster();
        ConcolicTaskPlan.RuntimeTask sourceTask =
                task("TASK.source", SOURCE_DN, STATIC_ROOT);
        ConcolicTaskPlan.RuntimeTask targetTask =
                task("TASK.target", TARGET_DN, STATIC_ROOT);
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
        assertNull("an activation no node claimed counts where the plan says,"
                        + " which is that node's second",
                decode(plan, sourceTask, null));
    }

    /**
     * One receiver, two nodes: the task whose node ran it gets it.
     *
     * <p>{@code REGION.763d087e}'s root is a method on one IPC connection
     * object that both DataNodes use and neither registered, so the thread's
     * execution context is the only evidence.  The source-dn task is earlier
     * in the plan and must still decline target-dn's activation.</p>
     */
    @Test
    public void anUnregisteredSharedReceiverIsNotOneNodesOccurrence() {
        registerCluster();
        Object connection = new Connection();
        ConcolicTaskPlan.RuntimeTask sourceTask =
                task("TASK.source", SOURCE_DN, CONNECTION_ROOT,
                        Connection.class.getName());
        ConcolicTaskPlan.RuntimeTask targetTask =
                task("TASK.target", TARGET_DN, CONNECTION_ROOT,
                        Connection.class.getName());
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Arrays.asList(sourceTask, targetTask));

        assertSame("target-dn's request ran it, so it is target-dn's",
                targetTask, send(plan, sourceTask, targetDn, connection));
        assertSame("and source-dn's own is still source-dn's first",
                sourceTask, send(plan, sourceTask, sourceDn, connection));
    }

    /**
     * An ordinal refusal says which node the run attributed the activation
     * to -- or that it attributed it to none.
     *
     * <p>Lane B2's question. The DataNode's heartbeat there runs on its own
     * BPServiceActor thread, whose stamp the workload opens with
     * {@code beginRequestIfRegistered(dn.getDatanodeId(), "heartbeat")}, so
     * whether a given heartbeat carries the node at all depends on when the
     * workload registered that object. "occurrence is activation 2, not 1"
     * reads identically for an activation that really was the planned
     * node's second and for one this run could name no node for, which was
     * counted in the planned node's bucket by the fallback -- two findings
     * with two different owners, and the row could not tell them apart.</p>
     */
    @Test
    public void anUnattributedActivationTakesNoKFromThePlannedNode() {
        registerCluster();
        ConcolicTaskPlan.RuntimeTask targetTask =
                task("TASK.target", TARGET_DN, STATIC_ROOT);
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Arrays.asList(targetTask));

        // Lane B2: two heartbeats run before the workload registers the
        // DataNode, so this run can name no node for them.  They are the
        // unregistered source's activations -- the third arm of the one
        // attribution function, which the planner runs too -- so they are
        // not offered target-dn's address at all.
        assertNull("an activation nobody attributed is not target-dn's",
                decode(plan, targetTask, null));
        assertNull("nor is the next one", decode(plan, targetTask, null));

        // And the heartbeat that does carry the node is still target-dn's
        // FIRST: nothing before it took a k in that bucket.
        assertSame("the unstamped ones took no k from target-dn",
                targetTask, decode(plan, targetTask, targetDn));
    }

    /** And names the node when there was one. */
    @Test
    public void anOrdinalRefusalNamesTheAttributedNode() {
        registerCluster();
        ConcolicTaskPlan.RuntimeTask targetTask =
                task("TASK.target", TARGET_DN, STATIC_ROOT);
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Arrays.asList(targetTask));

        assertSame(targetTask, decode(plan, targetTask, targetDn));
        assertNull(decode(plan, targetTask, targetDn));

        assertTrue(targetTask.unansweredAddress(),
                targetTask.unansweredAddress().contains(
                        "(attributed to " + TARGET_DN + ")"));
    }

    /** The bucket is the node that ran it, whatever the plan names. */
    @Test
    public void theBucketIsTheAttributedNode() {
        registerCluster();
        ConcolicTaskPlan.RuntimeTask targetTask =
                task("TASK.target", TARGET_DN, STATIC_ROOT);

        assertEquals("the NameNode's activation counts as the NameNode's",
                NN, ConcolicTaskPlan.countedLifecycle(targetTask,
                        RuntimeTraceContext.sourceFor(nameNode)));
        assertEquals("an activation nothing attributed counts in the "
                        + "unregistered source, as the planner counts it",
                RuntimeTraceContext.UNREGISTERED_SOURCE.key(),
                ConcolicTaskPlan.countedLifecycle(targetTask, null));
        assertNotEquals("and those are two buckets, not one",
                targetTask.invocationCounterKey(NN, ""),
                targetTask.invocationCounterKey(TARGET_DN, ""));
    }

    /** One static-root activation, run under {@code node}'s request. */
    private ConcolicTaskPlan.RuntimeTask decode(
            ConcolicTaskPlan plan, ConcolicTaskPlan.RuntimeTask any,
            Object node) {
        return send(plan, any, node, null);
    }

    /**
     * Enters the root once, inside {@code node}'s request scope when there
     * is one, exactly as the workload's own heartbeat does.
     */
    private ConcolicTaskPlan.RuntimeTask send(
            ConcolicTaskPlan plan, ConcolicTaskPlan.RuntimeTask any,
            Object node, Object receiver) {
        long request = node == null ? 0L
                : RuntimeTraceContext.beginRequest(node, "heartbeat");
        try {
            return plan.select(any.rootHookGroupKey(), any.rootMethod,
                    receiver, new Object[0]);
        } finally {
            if (node != null) RuntimeTraceContext.endRequest(request);
        }
    }

    /** Stands in for the shared {@code Client$Connection}. */
    private static final class Connection {
    }

    private static ConcolicTaskPlan.RuntimeTask task(String taskId,
                                                     String sourceKey,
                                                     String rootMethod) {
        return task(taskId, sourceKey, rootMethod, "");
    }

    private static ConcolicTaskPlan.RuntimeTask task(String taskId,
                                                     String sourceKey,
                                                     String rootMethod,
                                                     String receiverClass) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", taskId);
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", REGION);
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", sourceKey);
        // As the planner mints it: the address carries the request family
        // the recording stamped on the activation, (source, api) and no
        // request ordinal.
        encoded.addProperty("occurrenceId",
                sourceKey + "/region/" + REGION + "@" + sourceKey
                        + "/heartbeat#1");
        encoded.addProperty("rootMethod", rootMethod);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", receiverClass.isEmpty()
                ? "GLOBAL_INVOCATION" : "RECEIVER_CONTEXT");
        if (!receiverClass.isEmpty()) {
            selector.addProperty("receiverClass", receiverClass);
        }
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", rootMethod);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", sourceKey);
        // The recording named these occurrences by the thread's context:
        // neither root has a receiver the workload registered.
        anchor.addProperty("kind", "INHERITED_CONTEXT");
        anchor.addProperty("requestApi", "heartbeat");
        anchor.addProperty("requestKey", sourceKey + "/request/heartbeat#1");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branches", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        return new ConcolicTaskPlan.RuntimeTask(
                ExecutionTask.decode(encoded));
    }
}
