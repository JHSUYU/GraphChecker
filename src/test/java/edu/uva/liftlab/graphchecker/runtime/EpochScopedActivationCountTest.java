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
                task.invocationCounterKey(NODE + "#epoch1"));
        org.junit.Assert.assertNotEquals("epoch 0 is another bucket",
                task.invocationCounterKey(NODE + "#epoch1"),
                task.invocationCounterKey(NODE + "#epoch0"));
    }

    /** An unattributed activation counts exactly where it counted before. */
    @Test
    public void anUnattributedActivationCountsWhereThePlanSays() {
        RuntimeTraceContext.resetForTests();
        ConcolicTaskPlan.RuntimeTask task = task(NODE + "#epoch1", 1);

        assertEquals(NODE + "#epoch1", ConcolicTaskPlan.countedLifecycle(
                task, null, RuntimeTraceContext.current()));
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
