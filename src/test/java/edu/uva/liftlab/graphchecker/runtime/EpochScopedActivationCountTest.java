package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.nio.file.Path;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The k in "k-th activation" is counted inside one epoch.
 *
 * <p>One JVM runs both lifecycles of a node it restarts.  On hdfs-17960 the
 * two {@code deleteSnapshot} activations before the NameNode restart took
 * ordinals 1 and 2 of a bucket keyed on the <em>planned</em> epoch, so the
 * two after it -- the ones the plan addresses as epoch 1's first and second
 * -- took 3 and 4 and matched nothing.  Both planned tasks on the only
 * root-dependent region were then answered by no run, which is
 * {@code PUBLICATION_TASK_ANSWERED_BY_NO_RUN} and, downstream, unsat.</p>
 *
 * <p>The planner counts each activation under its own observed source, so
 * this is the replay counting the population the plan counted.</p>
 */
public class EpochScopedActivationCountTest {
    private static final String NODE = "hdfs/nn0";
    private static final String REGION = "REGION.9492ec77";
    private static final String ROOT = "<a.Manager: void deleteSnapshot()>";

    @After
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
    }

    /**
     * Twice before the restart, twice after: epoch 1's first is the third.
     */
    @Test
    public void theEpochOneAddressMatchesTheThirdActivation() {
        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 0L));

        ConcolicTaskPlan.RuntimeTask task = task(NODE + "#epoch1", 1);
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Collections.singletonList(task));

        assertNull("the first pre-restart activation is epoch 0's first",
                plan.select(task.rootHookGroupKey(), ROOT, node,
                        new Object[0]));
        assertNull("and the second is epoch 0's second",
                plan.select(task.rootHookGroupKey(), ROOT, node,
                        new Object[0]));

        RuntimeTraceContext.restartSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));

        assertNotNull("the third activation is epoch 1's first",
                plan.select(task.rootHookGroupKey(), ROOT, node,
                        new Object[0]));
    }

    /** Epoch 1's second address is the fourth activation, not the second. */
    @Test
    public void theEpochOneSecondAddressMatchesTheFourthActivation() {
        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 0L));

        ConcolicTaskPlan.RuntimeTask task = task(NODE + "#epoch1", 2);
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Collections.singletonList(task));

        plan.select(task.rootHookGroupKey(), ROOT, node, new Object[0]);
        plan.select(task.rootHookGroupKey(), ROOT, node, new Object[0]);
        RuntimeTraceContext.restartSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));

        assertNull("epoch 1's first is not the addressed occurrence",
                plan.select(task.rootHookGroupKey(), ROOT, node,
                        new Object[0]));
        assertNotNull("epoch 1's second is",
                plan.select(task.rootHookGroupKey(), ROOT, node,
                        new Object[0]));
    }

    /** The bucket is the observed epoch's, and the two do not share one. */
    @Test
    public void twoEpochsAreTwoBuckets() {
        ConcolicTaskPlan.RuntimeTask task = task(NODE + "#epoch1", 1);

        assertEquals("the planned bucket is the default",
                task.invocationCounterKey(),
                task.invocationCounterKey(NODE + "#epoch1", ""));
        org.junit.Assert.assertNotEquals("epoch 0 is another bucket",
                task.invocationCounterKey(NODE + "#epoch1", ""),
                task.invocationCounterKey(NODE + "#epoch0", ""));
        // And the request family partitions it the same way the epoch does:
        // two requests running against one node are two populations, so an
        // activation inside one takes no k from the other.
        org.junit.Assert.assertNotEquals("a family is another bucket",
                task.invocationCounterKey(NODE + "#epoch1", ""),
                task.invocationCounterKey(NODE + "#epoch1",
                        "hdfs-17960/client#epoch0/checkpoint-namespace"));
    }

    /**
     * An activation nothing attributed counts in the unregistered source.
     *
     * <p>The planner's last arm, which the replay now runs too: an
     * activation with no stamp of its own and no unique stamp among its
     * frames belongs to {@code workload/unregistered}, and it is counted in
     * that population rather than in the planned node's.  The replay used to
     * count it in the plan's own key, which is how hdfs-17899 bug2's
     * pre-registration heartbeats took target-dn's k=1.</p>
     */
    @Test
    public void anUnattributedActivationCountsInTheUnregisteredSource() {
        RuntimeTraceContext.resetForTests();
        ConcolicTaskPlan.RuntimeTask task = task(NODE + "#epoch1", 1);

        assertEquals(RuntimeTraceContext.UNREGISTERED_SOURCE.key(),
                ConcolicTaskPlan.countedLifecycle(task, null));
    }

    /**
     * An activation is addressed by where it RAN, not by where its values
     * came from.
     *
     * <p>Lane VM7's shape: bug3 runs nn0, source-dn and target-dn in one JVM,
     * and a DataNode region's values derive from the NameNode's mint, so the
     * thread carries nn0's context while the activation runs on source-dn.
     * Refusing on that inherited context cost five tasks --
     * "matching root inherited hdfs-17899/nn0#epoch0 instead of
     * hdfs-17899/source-dn#epoch0" -- and five
     * PUBLICATION_TASK_ANSWERED_BY_NO_RUN behind them.</p>
     */
    @Test
    public void aRegisteredReceiverDecidesWhereTheActivationRan() {
        RuntimeTraceContext.resetForTests();
        Object sourceDn = new Object();
        RuntimeTraceContext.registerSource(sourceDn,
                new SourceRef("DATANODE", "dn", "hdfs-17899/source-dn", 0L));
        Object nameNode = new Object();
        RuntimeTraceContext.registerSource(nameNode,
                new SourceRef("NAMENODE", "nn", "hdfs-17899/nn0", 0L));

        ConcolicTaskPlan.RuntimeTask task =
                task("hdfs-17899/source-dn#epoch0", 1);
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Collections.singletonList(task));

        // Two activations of the same region on the NameNode run first; they
        // are another node's and must neither answer nor be counted here.
        assertNull(plan.select(task.rootHookGroupKey(), ROOT, nameNode,
                new Object[0]));
        assertNull(plan.select(task.rootHookGroupKey(), ROOT, nameNode,
                new Object[0]));

        assertEquals("the bucket is the node that decided",
                "hdfs-17899/source-dn#epoch0",
                ConcolicTaskPlan.countedLifecycle(task,
                        RuntimeTraceContext.activationSource(sourceDn)));
        assertNotNull("source-dn's first activation is its occurrence 1",
                plan.select(task.rootHookGroupKey(), ROOT, sourceDn,
                        new Object[0]));
    }

    /** With no registration, the thread's context answers, then the
     *  unregistered source. */
    @Test
    public void anUnregisteredReceiverFallsBackToTheThreadsContext() {
        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("DATANODE", "dn", "hdfs-17899/source-dn", 0L));

        ConcolicTaskPlan.RuntimeTask task =
                task("hdfs-17899/source-dn#epoch0", 1);

        assertEquals("nothing registered, nothing observed: the "
                        + "unregistered source, as the planner counts it",
                RuntimeTraceContext.UNREGISTERED_SOURCE.key(),
                ConcolicTaskPlan.countedLifecycle(task, null));
        assertEquals("a registration decides over the plan's own",
                "hdfs-17899/source-dn#epoch0",
                ConcolicTaskPlan.countedLifecycle(task,
                        RuntimeTraceContext.activationSource(node)));
    }

    /** An inherited context that names another node records, never refuses. */
    @Test
    public void anInheritedContradictionIsRecordedNotRefused() {
        RuntimeTraceContext.resetForTests();
        ConcolicTaskPlan.RuntimeTask task =
                task("hdfs-17899/source-dn#epoch0", 1);

        assertEquals("", ConcolicTaskPlan.sourceMismatch(task, null,
                RuntimeTraceContext.current()));
    }

    /**
     * A region that never executes a mint site is admitted by its address.
     *
     * <p>Lane BI's shape.  Five loop-body regions declare a causal anchor on
     * {@code SnapshotManager.isSnapshotDeletionOrdered()#u1}; only
     * {@code REGION.9492ec77}'s activations execute it, so the five carried
     * no observation of it and were skipped as
     * {@code REGION_CAUSAL_ANCHOR_NOT_OBSERVED} -- taking the target region
     * with them.  "This activation must itself have observed phase P" is a
     * second admission condition, deciding which activation matters outside
     * the address, and it is gone: an activation is admitted by (node,
     * epoch, region, k) and by nothing else.</p>
     */
    @Test
    public void aRegionThatNeverExecutesTheSiteIsAdmittedByItsAddress() {
        RuntimeTraceContext.resetForTests();
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));

        ConcolicTaskPlan.RuntimeTask task = task(NODE + "#epoch1", 1);
        ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                Collections.singletonList(task));

        // Nothing about a source phase is asked, and nothing was observed.
        assertNotNull("the address is the whole admission",
                plan.select(task.rootHookGroupKey(), ROOT, node,
                        new Object[0]));
    }

    /** A loop-body task whose occurrence names no k is refused at PLAN. */
    @Test
    public void aRootLoopTaskWithoutKIsRefusedAtPlan() {
        try {
            loopTask("REGION.r");
            org.junit.Assert.fail("expected a plan refusal");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().startsWith(
                            "ROOT_LOOP_OCCURRENCE_UNADDRESSED"));
        }
    }

    /** One loop-body task whose planned occurrence carries no k. */
    private static ConcolicTaskPlan.RuntimeTask loopTask(String regionId) {
        com.google.gson.JsonObject encoded = new com.google.gson.JsonObject();
        encoded.addProperty("taskId", "TASK.loop");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", regionId);
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", NODE + "#epoch1");
        // No "#k": the occurrence names a region and no activation of it.
        encoded.addProperty("occurrenceId",
                NODE + "#epoch1/region/" + regionId);
        encoded.addProperty("rootMethod", ROOT);
        encoded.addProperty("instrumentationSelector", "sel");
        encoded.addProperty("rootAuthority", "LOOP_BODY_ROOT");
        com.google.gson.JsonObject admission = new com.google.gson.JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        com.google.gson.JsonObject selector = new com.google.gson.JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", ROOT);
        com.google.gson.JsonObject anchor = new com.google.gson.JsonObject();
        anchor.addProperty("sourceKey", NODE + "#epoch1");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branches", new com.google.gson.JsonArray());
        encoded.add("inputActions", new com.google.gson.JsonArray());
        com.google.gson.JsonObject loopBound = new com.google.gson.JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        return new ConcolicTaskPlan.RuntimeTask(
                edu.uva.liftlab.graphchecker.contract.ExecutionTask.decode(
                        encoded));
    }

    private static ConcolicTaskPlan.RuntimeTask task(String sourceKey,


                                                     int ordinal) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK." + ordinal);
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", REGION);
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", sourceKey);
        encoded.addProperty("occurrenceId",
                sourceKey + "/region/" + REGION + "#" + ordinal);
        encoded.addProperty("rootMethod", ROOT);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", ordinal);
        selector.addProperty("method", ROOT);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", sourceKey);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
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
