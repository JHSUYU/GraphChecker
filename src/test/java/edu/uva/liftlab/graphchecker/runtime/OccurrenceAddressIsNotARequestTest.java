package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import org.junit.Test;

import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.Collections;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * An occurrence is (node, epoch, region, k-th activation) -- not a request.
 *
 * <p>The request an activation was reached under used to veto the match.  That
 * was the stitcher's addressing: it merged replays and needed the RPC exchange
 * to tell two runs of one region apart.  It refused flip replays whose
 * activation is the seed's own -- same node, same region, same ordinal --
 * because the workload arrived there under a different request the second time,
 * and on hdfs-17960 that skipped every activation whose decisions are the ones
 * over the root.</p>
 *
 * <p>The difference is still described, because where an occurrence was
 * reached from is worth saying; it just no longer withholds the address.</p>
 */
public class OccurrenceAddressIsNotARequestTest {

    /** Noting the request an activation entered is not a refusal. */
    @Test
    public void aDifferentRequestDoesNotUnaddressTheOccurrence() {
        ConcolicTaskPlan.RuntimeTask task = task();

        task.noteRequestContext("matching root entered request "
                + "client#epoch0/record-ordered-deletes#1 instead of "
                + "nn0#epoch1/restart-namenode#1");

        assertTrue("a request note leaves the address answered",
                task.unansweredAddress().startsWith(
                        "0 compatible activation(s)"));
    }

    /** A candidate that really was not this address still says so. */
    @Test
    public void anUnaddressedCandidateStillCounts() {
        ConcolicTaskPlan.RuntimeTask task = task();

        task.noteUnaddressedCandidate("matching root ran on another node");

        assertTrue(task.unansweredAddress().startsWith(
                "1 compatible activation(s)"));
        assertTrue(task.unansweredAddress().contains("another node"));
    }

    /** The planned occurrence still names node, epoch, region and ordinal. */
    @Test
    public void theAddressIsNodeEpochRegionAndOrdinal() {
        assertEquals("hdfs-17899/nn0#epoch0/region/"
                        + "REGION.2392e4b7-aa01-3487-85a3-ac776965f7f7#1",
                task().occurrenceId);
    }

    /**
     * An absent inherited source is not evidence of another occurrence.
     *
     * <p>Inheriting a <em>different</em> source says this activation belongs
     * elsewhere.  Inheriting <em>none</em> says nothing at all, and a flip
     * replay reaches the planned activation by a path that carries no
     * inherited context -- so refusing it there withheld the occurrence over
     * a fact nobody established.</p>
     */
    @Test
    public void anAbsentInheritedSourceIsNotAMismatch() {
        ConcolicTaskPlan.RuntimeTask task = task();

        assertEquals("", ConcolicTaskPlan.sourceMismatch(task, null,
                RuntimeTraceContext.current()));
    }

    /**
     * An activation nothing attributed to a node is still the occurrence.
     *
     * <p>The exact row lane AY refused: a seed replay's target activation
     * with no registered trace source, whose anchor names the node and epoch
     * it ran on.  Refusing it at close simply moved the refusal that was
     * removed at entry -- and on 17960 it left the run with no TARGET_REACH
     * occurrence at all, because every target task was skipped this way.
     * Evidence that the activation ran somewhere <em>else</em> still
     * refuses; evidence nobody offered does not.</p>
     */
    @Test
    public void anUnattributedActivationIsStillTheOccurrence() {
        ConcolicTaskPlan.RuntimeTask task = task();

        assertEquals("", task.rootContextSelector.unconfirmed(
                Collections.<String>emptySet()));
    }

    /** An activation attributed to another node is refused, as before. */
    @Test
    public void anActivationOnAnotherNodeIsRefused() {
        ConcolicTaskPlan.RuntimeTask task = task();

        String refusal = task.rootContextSelector.unconfirmed(
                Collections.singleton("hdfs-17899/source-dn#epoch0"));

        assertTrue(refusal, refusal.contains("occurrence ran on"));
        assertTrue(refusal, refusal.contains("source-dn"));
    }

    /**
     * Two activations under two requests are the first and the second.
     *
     * <p>Counting and matching use one scope.  Partitioning the count by the
     * exchange while matching ignored it handed out ordinal 1 in several
     * buckets, and any of them satisfied a planned ordinal of 1 -- on
     * hdfs-17960 that matched the checkpoint region's planned occurrence to
     * the process's first saveNamespace, which serialized no snapshots and
     * decided none of the branches the goal needs.</p>
     */
    @Test
    public void activationsAreCountedAcrossEveryRequest() {
        ConcolicTaskPlan.RuntimeTask task = task();

        assertEquals("one region on one node is one bucket",
                task.invocationCounterKey(), task.invocationCounterKey());
        assertFalse("the request is not in the bucket",
                task.invocationCounterKey().contains("request"));
    }

    /** The bucket is the node, the region and the root, and nothing else. */
    @Test
    public void theBucketIsNodeRegionAndRoot() {
        ConcolicTaskPlan.RuntimeTask task = task();
        String bucket = task.invocationCounterKey();

        assertTrue(bucket.startsWith(task.sourceKey));
        assertTrue(bucket.contains(task.regionId));
        assertTrue(bucket.contains(task.rootMethod));
        assertEquals("node, region, root -- three parts", 3,
                bucket.split("\n", -1).length);
    }

    /**
     * The planned k-th occurrence is the k-th activation, not the first.
     *
     * <p>An ordinal is only an address if the same activation answers to it
     * on both sides.  A plan that names activation 2 must not be satisfied
     * by activation 1 because 1 was the first of some other bucket.</p>
     */
    @Test
    public void aPlannedSecondOccurrenceIsNotTheFirstActivation() {
        ConcolicTaskPlan.RuntimeTask task = task();
        assertTrue("activation 1 answers the planned ordinal",
                task.acceptsRootInvocation(OccurrenceAddress.of(
                        task.sourceKey, task.regionId, 1), false));
        assertFalse("activation 2 does not",
                task.acceptsRootInvocation(OccurrenceAddress.of(
                        task.sourceKey, task.regionId, 2), false));
        assertFalse("and another node's first activation does not",
                task.acceptsRootInvocation(OccurrenceAddress.of(
                        "hdfs-17899/source-dn#epoch0", task.regionId, 1),
                        false));
    }

    /**
     * The window opens when the workload names its first source.
     *
     * <p>A workload starts its cluster, names its sources, then does the
     * thing being recorded.  The plan counts what the recording saw; a
     * replay that counts what the process did beforehand numbers a
     * different population.  On hdfs-17960 the first saveNamespace runs 38
     * seconds before the workload begins -- the recording never saw it, but
     * the replay counted it as activation 1 and the checkpoint activation
     * the plan means became 2.</p>
     *
     * <p>Only the opening direction is asserted.  The registry is process
     * global and has no reset, so "closed before" holds in a fresh replay
     * JVM but not in a suite where another test has already registered
     * something; asserting it here would pin test order rather than
     * behaviour.</p>
     */
    @Test
    public void theWindowOpensWhenTheWorkloadNamesItsFirstSource() {
        RuntimeTraceContext.registerSource(new Object(),
                new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs/nn0", 0L));

        assertTrue("a named source is a recording window",
                RuntimeTraceContext.recordingWindowOpen());
    }

    /**
     * A pre-window activation is neither counted nor offered.
     *
     * <p>The counting pass already skips what ran before the workload named
     * its first source.  The admitting pass used to run anyway, look that
     * activation's ordinal up in a table the counting pass never wrote, and
     * refuse it as "matching enclosing root was invocation null instead of
     * 1" -- a comparison against an ordinal nobody assigned.  Lane BB shows
     * the shape: the flip replay throws inside the workload before it
     * restarts the NameNode, so the only {@code loadFSImage} activation it
     * offers is the cluster start that happens before the window opens.
     * The two passes now share one predicate, so such an activation is
     * simply not a candidate and the run says the planned root did not
     * execute.</p>
     */
    @Test
    public void aPreWindowActivationIsNeitherCountedNorOffered() {
        RuntimeTraceContext.resetForTests();
        ConcolicTaskPlan.RuntimeTask task = task();

        Set<String> admitted = plan(task).addressLoopRootInvocation(
                task.rootMethod, task.rootMethod, null, new Object[0]);

        assertTrue("nothing outside the window is admitted",
                admitted.isEmpty());
        assertFalse("and nothing is compared against a null ordinal",
                task.unansweredAddress().contains("invocation null"));
    }

    /**
     * A flip replay counts and matches the activation the seed did.
     *
     * <p>Both runs start the cluster before the workload names its source,
     * so both offer one activation outside the recording window first.  The
     * plan counted neither of them, and neither replay may let that
     * activation take ordinal 1 from the activation the recording actually
     * saw.  Running the identical sequence twice pins the property the
     * refusals turned on: the window opens at the same moment on both
     * sides, so the same physical activation answers the same address.</p>
     */
    @Test
    public void aFlipReplayCountsAndMatchesLikeTheSeed() {
        assertEquals("the flip admits what the seed admitted",
                replayOnce(), replayOnce());
    }

    /**
     * One replay: a cluster start outside the window, then the workload.
     *
     * <p>The node is registered on the object the activation runs on, which
     * is how a workload names its sources and how the recording attributed
     * the activation the plan addresses.  An activation with no stamp at all
     * is the unregistered source's -- the planner counts it there and so
     * does the replay -- so it could not answer this address in either run
     * and would not pin anything about the window.</p>
     */
    private static Set<String> replayOnce() {
        RuntimeTraceContext.resetForTests();
        ConcolicTaskPlan.RuntimeTask task = task();
        ConcolicTaskPlan plan = plan(task);
        Object node = new Object();

        assertTrue("the cluster start is outside the window",
                plan.addressLoopRootInvocation(task.rootMethod,
                        task.rootMethod, node, new Object[0]).isEmpty());
        assertTrue("and it is not a candidate that failed to answer",
                task.unansweredAddress().startsWith(
                        "0 compatible activation(s)"));

        RuntimeTraceContext.registerSource(node,
                new SourceRef("NAMENODE", "nn", "hdfs-17899/nn0", 0L));

        Set<String> admitted = plan.addressLoopRootInvocation(
                task.rootMethod, task.rootMethod, node, new Object[0]);
        assertEquals("the first activation the recording saw is occurrence 1",
                Collections.singleton(task.taskId), admitted);
        return admitted;
    }

    private static ConcolicTaskPlan plan(
            ConcolicTaskPlan.RuntimeTask task) {
        return new ConcolicTaskPlan(null,
                Collections.singletonList(task));
    }

    /**
     * Two epochs of one node: each run answers its own epoch's tasks.
     *
     * <p>The mint site is reached once per node lifecycle and the model names
     * the site, so the epoch is what tells the two apart.  On hdfs-17960 the
     * flip replay threw inside the workload before it restarted the NameNode:
     * every activation it offered was epoch 0, and {@code root=false} was
     * written at the mint the recording made before the restart, rewriting
     * the recorded execution at a point the solver said nothing about.</p>
     *
     * <p>The refusal is on evidence, not on registration order.  Lane BD
     * showed why that matters: an arm that refused "this run has not
     * registered epoch 1 yet" turned a fact about a moment into a verdict
     * about the run, and one seed replay both published five regions at
     * epoch 1 and told eight tasks the run never reached it.  So an epoch-0
     * activation is declined because it ran at epoch 0, an epoch-1
     * activation is answered whenever it arrives, and an activation nothing
     * attributed is still the occurrence.</p>
     */
    @Test
    public void eachEpochAnswersItsOwnTasks() {
        RuntimeTraceContext.resetForTests();
        RuntimeTraceContext.registerSource(new Object(),
                new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs/nn0", 0L));

        // The epoch-0 run, before any restart: an activation of this node is
        // declined, and the decline says which epoch it actually ran in.
        String declined = ConcolicTaskPlan.lifecycleMismatch("hdfs/nn0#epoch1",
                Collections.singleton("hdfs/nn0#epoch0"));
        assertFalse("an epoch-0 activation is not the epoch-1 occurrence",
                declined.isEmpty());
        assertTrue(declined, declined.contains("hdfs/nn0#epoch0"));
        assertTrue(declined, declined.contains("hdfs/nn0#epoch1"));

        assertEquals("and a task of its own epoch is answered", "",
                ConcolicTaskPlan.lifecycleMismatch("hdfs/nn0#epoch0",
                        Collections.singleton("hdfs/nn0#epoch0")));

        // The same run after the restart registers the next epoch.  The
        // epoch-1 activations answer; nothing about the earlier refusals
        // carries over, because the refusal was never about the run.
        RuntimeTraceContext.registerSource(new Object(),
                new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs/nn0", 1L));

        assertEquals("the epoch-1 activation answers", "",
                ConcolicTaskPlan.lifecycleMismatch("hdfs/nn0#epoch1",
                        Collections.singleton("hdfs/nn0#epoch1")));
        assertFalse("and the epoch-0 one still does not",
                ConcolicTaskPlan.lifecycleMismatch("hdfs/nn0#epoch1",
                        Collections.singleton("hdfs/nn0#epoch0")).isEmpty());
        assertEquals("an activation nothing attributed is still it", "",
                ConcolicTaskPlan.lifecycleMismatch("hdfs/nn0#epoch1",
                        Collections.<String>emptySet()));
    }

    /**
     * A task addressed to an epoch this run has not reached yet is not
     * refused for that reason.
     *
     * <p>This is lane BD exactly: the activations that precede the restart
     * are refused because they ran at epoch 0, and the address stays open for
     * the activations that follow it.</p>
     */
    @Test
    public void anEpochNotYetReachedIsNotARefusal() {
        RuntimeTraceContext.resetForTests();
        RuntimeTraceContext.registerSource(new Object(),
                new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs/nn0", 0L));

        assertEquals("nothing attributed, nothing to refuse", "",
                ConcolicTaskPlan.lifecycleMismatch("hdfs/nn0#epoch1",
                        Collections.<String>emptySet()));
        assertEquals("another node's epochs say nothing", "",
                ConcolicTaskPlan.lifecycleMismatch("hdfs/dn0#epoch1",
                        Collections.<String>emptySet()));
    }

    /** The counting bucket is the address's, so two epochs are two buckets. */
    @Test
    public void twoEpochsAreTwoCountingBuckets() {
        ConcolicTaskPlan.RuntimeTask task = task();

        assertEquals(task.address.counterScope(task.rootMethod),
                task.invocationCounterKey());
        assertFalse(task.invocationCounterKey().equals(
                edu.uva.liftlab.graphchecker.contract.OccurrenceAddress.of(
                        "hdfs-17899/nn0#epoch1", task.regionId, 1)
                        .counterScope(task.rootMethod)));
    }

    // ---------- the jobs the deleted predicates used to do ----------

    /** A receiver the application registered elsewhere refuses, as before. */
    @Test
    public void aReceiverRegisteredToAnotherNodeIsRefused() {
        ConcolicTaskPlan.RuntimeTask task = task();
        Object receiver = new Object();
        RuntimeTraceContext.registerSource(receiver,
                new SourceRef("DATANODE", "dn", "hdfs-17899/dn9", 0L));

        String refusal = ConcolicTaskPlan.sourceMismatch(task,
                RuntimeTraceContext.sourceFor(receiver),
                RuntimeTraceContext.current());

        assertTrue(refusal, refusal.contains("receiver belonged to"));
        assertTrue(refusal, refusal.contains("hdfs-17899/dn9"));
    }

    /**
     * A registration that names the planned source decides, on its own.
     *
     * <p>This was the registered-source arm's job: the receiver's own
     * registration is authoritative and an inherited context that disagrees
     * does not override it.</p>
     */
    @Test
    public void aRegistrationThatNamesThePlannedSourceDecides() {
        ConcolicTaskPlan.RuntimeTask task = task();
        Object receiver = new Object();
        RuntimeTraceContext.registerSource(receiver,
                new SourceRef("NAMENODE", "nn", "hdfs-17899/nn0", 0L));

        assertEquals("", ConcolicTaskPlan.sourceMismatch(task,
                RuntimeTraceContext.sourceFor(receiver),
                RuntimeTraceContext.current()));
    }

    /**
     * No evidence at all is not a refusal, whatever the anchor kind was.
     *
     * <p>The registered-source arm refused an activation that carried no
     * registration and no inherited context, with "its anchor names ...".
     * That is the absence of evidence, and the inherited arm had already
     * stopped treating it as a contradiction; the two arms now ask one
     * question and give one answer.</p>
     */
    @Test
    public void noEvidenceAtAllIsNotARefusal() {
        assertEquals("", ConcolicTaskPlan.sourceMismatch(task(), null,
                RuntimeTraceContext.current()));
    }

    /** The circumstances are described, and describing is not vetoing. */
    @Test
    public void theCircumstancesAreRecordedNotConsulted() {
        ConcolicTaskPlan.RuntimeTask task = task();

        assertEquals("the request is not compared by the address", "",
                ConcolicTaskPlan.sourceMismatch(task, null,
                        RuntimeTraceContext.current()));
        assertFalse("the bucket carries no circumstance",
                task.invocationCounterKey().contains("request"));
    }

    /** The transcript ends here; the helpers follow. */
    private static ConcolicTaskPlan.RuntimeTask task() {
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(
                row("plans/hdfs-17899-bug3-loop-body-producer.json")));
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
