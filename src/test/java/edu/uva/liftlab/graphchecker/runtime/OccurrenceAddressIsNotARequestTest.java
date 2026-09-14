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
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import com.google.gson.JsonArray;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.UUID;
import org.junit.After;
import static java.util.Collections.singletonList;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;

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
    public void occurrenceAddressIsNotARequestRules() throws Exception {
        aDifferentRequestDoesNotUnaddressTheOccurrence();
        anUnaddressedCandidateStillCounts();
        theAddressIsNodeEpochRegionAndOrdinal();
        anAbsentInheritedSourceIsNotAMismatch();
        anUnattributedActivationIsTheUnregisteredSourcesOccurrence();
        aTaskAddressedToTheUnregisteredSourceIsAnsweredByOne();
        anActivationOnAnotherNodeIsRefused();
        eachRequestFamilyCountsItsOwnActivations();
        theBucketIsNodeRegionAndRoot();
        aPlannedSecondOccurrenceIsNotTheFirstActivation();
        theWindowOpensWhenTheWorkloadStartsRecording();
        aPreWindowActivationIsNeitherCountedNorOffered();
        aFlipReplayCountsAndMatchesLikeTheSeed();
        eachEpochAnswersItsOwnTasks();
        anEpochNotYetReachedIsNotARefusal();
        twoEpochsAreTwoCountingBuckets();
        aReceiverRegisteredToAnotherNodeIsRefused();
        aRegistrationThatNamesThePlannedSourceDecides();
        noEvidenceAtAllIsNotARefusal();
        theCircumstancesAreRecordedNotConsulted();
        AddressIsTheOnlyAdmissionTest t0 =
                new AddressIsTheOnlyAdmissionTest();
        try {
            t0.addressIsTheOnlyAdmissionRules();
        } finally {
            t0.clearMessageState();
        }
        EpochScopedActivationCountTest t1 =
                new EpochScopedActivationCountTest();
        try {
            t1.epochScopedActivationCountRules();
        } finally {
            t1.clearRegistry();
        }
        ActivationIsCountedWhereItRanTest t2 =
                new ActivationIsCountedWhereItRanTest();
        try {
            t2.activationIsCountedWhereItRanRules();
        } finally {
            t2.clearRegistry();
        }
        ActivationIdentityContentTest t3 =
                new ActivationIdentityContentTest();
        t3.twoRecordingsPublishOneActivationName();
        RuntimeObjectIdentityContentTest t4 =
                new RuntimeObjectIdentityContentTest();
        t4.runtimeObjectIdentityContentRules();
        LoopBodiesBelongToOneInvocationTest t5 =
                new LoopBodiesBelongToOneInvocationTest();
        try {
            t5.loopBodiesBelongToOneInvocationRules();
        } finally {
            t5.clear();
        }
        ExecutionContextIsNotProvenanceTest t6 =
                new ExecutionContextIsNotProvenanceTest();
        try {
            t6.executionContextIsNotProvenanceRules();
        } finally {
            t6.clearRegistry();
        }
        RequestScopeIsHonouredTest t7 =
                new RequestScopeIsHonouredTest();
        try {
            t7.requestScopeIsHonouredRules();
        } finally {
            t7.clearRegistry();
        }
    }

    private void aDifferentRequestDoesNotUnaddressTheOccurrence() {
        ConcolicTaskPlan.RuntimeTask task = task();

        task.noteRequestContext("matching root entered request "
                + "client#epoch0/record-ordered-deletes#1 instead of "
                + "nn0#epoch1/restart-namenode#1");

        assertTrue("a request note leaves the address answered",
                task.unansweredAddress().startsWith(
                        "0 compatible activation(s)"));
    }

    /** A candidate that really was not this address still says so. */
    private void anUnaddressedCandidateStillCounts() {
        ConcolicTaskPlan.RuntimeTask task = task();

        task.noteUnaddressedCandidate("matching root ran on another node");

        assertTrue(task.unansweredAddress().startsWith(
                "1 compatible activation(s)"));
        assertTrue(task.unansweredAddress().contains("another node"));
    }

    /** The planned occurrence still names node, epoch, region and ordinal. */
    private void theAddressIsNodeEpochRegionAndOrdinal() {
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
    private void anAbsentInheritedSourceIsNotAMismatch() {
        ConcolicTaskPlan.RuntimeTask task = task();

        assertEquals("", ConcolicTaskPlan.sourceMismatch(task, null,
                RuntimeTraceContext.current()));
    }

    /**
     * An activation nothing attributed to a node is still an occurrence --
     * of the unregistered source.
     *
     * <p>One attribution function, three arms: the activation's own stamp,
     * else the unique stamp among its frames, else the unregistered source.
     * The planner runs it and so addresses such an activation to
     * {@code workload/unregistered}; the replay runs the same function and
     * must answer the same, at close as at entry.  So it IS the occurrence
     * -- the next one of that source -- and it answers a task addressed
     * there.</p>
     *
     * <p>What it is not is the planned node's next k.  Answering "" for
     * every anchor was the planned-node fallback, removed at entry and
     * living on here: on lane11741d it let activations on IPC handler
     * threads, which the recording never attributes to dn0, take dn0's k,
     * so the five genuine activations on {@code main} were numbered
     * 1, 3, 5, 7 and the addressed activation 4 was consumed by an
     * activation that was nobody's.</p>
     */
    private void anUnattributedActivationIsTheUnregisteredSourcesOccurrence() {
        ConcolicTaskPlan.RuntimeTask task = task();
        String refusal = task.rootContextSelector.unconfirmed(
                Collections.<String>emptySet());

        assertTrue(refusal, refusal.contains("nothing attributed it to any"
                + " node"));
        assertTrue(refusal, refusal.contains(task.sourceKey));
    }

    /** A task addressed to the unregistered source is answered by one. */
    private void aTaskAddressedToTheUnregisteredSourceIsAnsweredByOne() {
        ConcolicTaskPlan.RuntimeTask task = unregisteredTask();

        assertEquals("", task.rootContextSelector.unconfirmed(
                Collections.<String>emptySet()));
    }

    /** An activation attributed to another node is refused, as before. */
    private void anActivationOnAnotherNodeIsRefused() {
        ConcolicTaskPlan.RuntimeTask task = task();

        String refusal = task.rootContextSelector.unconfirmed(
                Collections.singleton("hdfs-17899/source-dn#epoch0"));

        assertTrue(refusal, refusal.contains("occurrence ran on"));
        assertTrue(refusal, refusal.contains("source-dn"));
    }

    /**
     * Two activations under two request families are each the first of
     * their own.
     *
     * <p>Counting and matching use one scope, and the family is now in
     * both.  It was in neither: partitioning the count by the exchange while
     * matching ignored it handed out ordinal 1 in several buckets and any of
     * them satisfied a planned ordinal of 1 -- on hdfs-17960 that matched
     * the checkpoint region's planned occurrence to the process's first
     * saveNamespace.  Removing it from the count left the other defect: on
     * hdfs-17899 bug2 the two activations of {@code nn0 REGION.2392e4b7},
     * recorded under {@code target-dn/heartbeat} and {@code
     * sps/refresh-block-keys}, arrived in the other order and answered each
     * other's addresses.  Under the family each is the first of its own and
     * neither can take the other's.</p>
     */
    private void eachRequestFamilyCountsItsOwnActivations() {
        ConcolicTaskPlan.RuntimeTask task = task();
        String heartbeat = "hdfs-17899/target-dn#epoch0/heartbeat";
        String refresh = "hdfs-17899/sps#epoch0/refresh-block-keys";

        assertEquals("one region, one node, one family is one bucket",
                task.invocationCounterKey(task.sourceKey, heartbeat),
                task.invocationCounterKey(task.sourceKey, heartbeat));
        assertFalse("another family is another bucket",
                task.invocationCounterKey(task.sourceKey, heartbeat).equals(
                        task.invocationCounterKey(task.sourceKey, refresh)));
        assertFalse("the request key itself is not in the bucket",
                task.invocationCounterKey().contains("/request/"));

        // k=1 in each, and the two are different occurrences.
        Map<String, Integer> first = new java.util.LinkedHashMap<>();
        first.put(task.invocationCounterKey(task.sourceKey, heartbeat), 1);
        Map<String, Integer> second = new java.util.LinkedHashMap<>();
        second.put(task.invocationCounterKey(task.sourceKey, refresh), 1);
        OccurrenceAddress one = task.observedAddress(task.sourceKey,
                heartbeat, first);
        OccurrenceAddress other = task.observedAddress(task.sourceKey,
                refresh, second);

        assertEquals(1, one.ordinal());
        assertEquals(1, other.ordinal());
        assertFalse("two families, two occurrences", one.matches(other));
        assertTrue(one.difference(other),
                one.difference(other).contains("request family"));
    }

    /**
     * The bucket is the node, the region, the request family and the root,
     * and nothing else.
     */
    private void theBucketIsNodeRegionAndRoot() {
        ConcolicTaskPlan.RuntimeTask task = task();
        String bucket = task.invocationCounterKey();

        assertTrue(bucket.startsWith(task.sourceKey));
        assertTrue(bucket.contains(task.regionId));
        assertTrue(bucket.contains(task.rootMethod));
        assertEquals("node, region, family, root -- four parts", 4,
                bucket.split("\n", -1).length);
        // The family, not the request: the plan row this task is decoded
        // from names the request its recording had, and what partitions the
        // count is that request's (source, api) with no ordinal.
        assertFalse("the request key is not the bucket",
                bucket.contains("/request/"));
        assertEquals("an activation of the same region under another family"
                        + " is another bucket's", 2,
                new java.util.LinkedHashSet<>(java.util.Arrays.asList(
                        task.invocationCounterKey(task.sourceKey,
                                "hdfs-17899/dn0#epoch0/heartbeat"),
                        task.invocationCounterKey(task.sourceKey,
                                "hdfs-17899/balancer#epoch0/balance-block")))
                        .size());
    }

    /**
     * The planned k-th occurrence is the k-th activation, not the first.
     *
     * <p>An ordinal is only an address if the same activation answers to it
     * on both sides.  A plan that names activation 2 must not be satisfied
     * by activation 1 because 1 was the first of some other bucket.</p>
     */
    private void aPlannedSecondOccurrenceIsNotTheFirstActivation() {
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
    private void theWindowOpensWhenTheWorkloadStartsRecording() {
        CausynthTraceRecorder.setRecordingStartedForTests(false);
        RuntimeTraceContext.registerSource(new Object(),
                new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs/nn0", 0L));

        assertFalse("a named source is state, not the window",
                RuntimeTraceContext.recordingWindowOpen());

        CausynthTraceRecorder.startRecording();

        assertTrue("the workload opens the window by recording",
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
    private void aPreWindowActivationIsNeitherCountedNorOffered() {
        RuntimeTraceContext.resetForTests();
        ConcolicTaskPlan.RuntimeTask task = task();

        Map<String, Integer> admitted = plan(task)
                .addressLoopRootInvocation(task.rootMethod, task.rootMethod,
                        null, new Object[0], 1L);

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
    private void aFlipReplayCountsAndMatchesLikeTheSeed() {
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
     *
     * <p>Outside the window means before the workload started recording, not
     * before it named a source: a workload may register long before it
     * records, and hdfs-11741 restarts its cluster in between.</p>
     */
    private static Map<String, Integer> replayOnce() {
        RuntimeTraceContext.resetForTests();
        CausynthTraceRecorder.setRecordingStartedForTests(false);
        ConcolicTaskPlan.RuntimeTask task = task();
        ConcolicTaskPlan plan = plan(task);
        Object node = new Object();
        RuntimeTraceContext.registerSource(node,
                new SourceRef("NAMENODE", "nn", "hdfs-17899/nn0", 0L));

        assertTrue("the cluster start is outside the window",
                plan.addressLoopRootInvocation(task.rootMethod,
                        task.rootMethod, node, new Object[0], 11L)
                        .isEmpty());
        assertTrue("and it is not a candidate that failed to answer",
                task.unansweredAddress().startsWith(
                        "0 compatible activation(s)"));

        CausynthTraceRecorder.setRecordingStartedForTests(true);

        Map<String, Integer> admitted = plan.addressLoopRootInvocation(
                task.rootMethod, task.rootMethod, node, new Object[0], 12L);
        assertEquals("the first activation the recording saw is occurrence 1",
                Collections.singletonMap(task.taskId, 1), admitted);
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
    private void eachEpochAnswersItsOwnTasks() {
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
    private void anEpochNotYetReachedIsNotARefusal() {
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
    private void twoEpochsAreTwoCountingBuckets() {
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
    private void aReceiverRegisteredToAnotherNodeIsRefused() {
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
    private void aRegistrationThatNamesThePlannedSourceDecides() {
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
    private void noEvidenceAtAllIsNotARefusal() {
        assertEquals("", ConcolicTaskPlan.sourceMismatch(task(), null,
                RuntimeTraceContext.current()));
    }

    /** The circumstances are described, and describing is not vetoing. */
    private void theCircumstancesAreRecordedNotConsulted() {
        ConcolicTaskPlan.RuntimeTask task = task();

        assertEquals("the request is not compared by the address", "",
                ConcolicTaskPlan.sourceMismatch(task, null,
                        RuntimeTraceContext.current()));
        assertFalse("the bucket carries no circumstance",
                task.invocationCounterKey().contains("/request/"));
    }

    /** The transcript ends here; the helpers follow. */
    private static ConcolicTaskPlan.RuntimeTask task() {
        return new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(
                row("plans/hdfs-17899-bug3-loop-body-producer.json")));
    }

    /** The same plan row, addressed where an unattributed activation counts. */
    private static ConcolicTaskPlan.RuntimeTask unregisteredTask() {
        JsonObject encoded =
                row("plans/hdfs-17899-bug3-loop-body-producer.json");
        String unregistered = "workload/unregistered#epoch0";
        String regionId = encoded.get("regionId").getAsString();
        encoded.addProperty("sourceKey", unregistered);
        encoded.addProperty("occurrenceId",
                unregistered + "/region/" + regionId + "#1");
        JsonObject selector = encoded.getAsJsonObject("rootSelector");
        selector.addProperty("invocationOrdinal", 1);
        JsonObject anchor = selector.getAsJsonObject("causalAnchor");
        anchor.addProperty("sourceKey", unregistered);
        anchor.addProperty("kind", "UNREGISTERED_SOURCE");
        return new ConcolicTaskPlan.RuntimeTask(
                ExecutionTask.decode(encoded));
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

    /**
     * An occurrence is its address, and admission asks nothing else.
     *
     * <p>(node, epoch, region, k-th activation) is the whole identity. The
     * message an activation was reached by is provenance: the handoff row
     * states the producer that actually delivered, and a planned attach that
     * did not reproduce is reported at IMPORT. It is not a second identity that
     * may veto the first.</p>
     *
     * <p>It was one. Whenever the plan named an IN producer for a task,
     * admission replaced the address test entirely with "is the envelope on
     * this thread the one the plan named" -- so an activation that agreed on
     * node, epoch, region AND k was refused because a response envelope had
     * not been reproduced. On hdfs-11741 that is the balancer's REGION #3 and
     * #7, each with candidates listed at every other k and one candidate whose
     * stated difference was empty because its address matched; on hdfs-17897 it
     * is dn0's addKeys #1.</p>
     */
    static final class AddressIsTheOnlyAdmissionTest {
        private static final String REGION = "REGION.r";
        private static final String NODE = "hdfs-11741/balancer#epoch0";
        private static final String PORT = "XCH.1.resp.block-key-array";

        public void clearMessageState() {
            SymbolicMessageEnvelope.clear();
            RuntimeTraceContext.resetForTests();
        }

        /**
         * A task the plan gave an IN handoff answers its own address with no
         * envelope present at all.
         */
        public void addressIsTheOnlyAdmissionRules() throws Exception {
            anAddressedActivationIsAdmittedWithNoEnvelope();
            anUnplannedEnvelopeNeitherAdmitsNorRefuses();
            everyRefusalNamesWhatDiffered();
        }

        private void anAddressedActivationIsAdmittedWithNoEnvelope()
                throws Exception {
            ConcolicTaskPlan.RuntimeTask task = task(3);
            SymbolicMessageEnvelope.clear();

            assertTrue("the planned occurrence has an IN handoff",
                    task.communicationHandoff(PORT, false) != null);
            assertTrue("its own address answers it",
                    task.acceptsRootInvocation(address(3), false));
            assertFalse("another activation of it does not",
                    task.acceptsRootInvocation(address(2), false));
            assertFalse("nor does an unnamed address",
                    task.acceptsRootInvocation(address(0), false));
        }

        /**
         * An envelope naming another producer changes nothing either way.
         *
         * <p>The value that arrived is evidence the handoff row states. It
         * decides which v_H the attach mints, never which activation this is.</p>
         */
        private void anUnplannedEnvelopeNeitherAdmitsNorRefuses() throws Exception {
            ConcolicTaskPlan.RuntimeTask task = task(3);
            assertTrue(SymbolicMessageEnvelope.stage(PORT, 41L, "task-x",
                    "some-other-producer#9", singletonList("some-consumer#4")));
            SymbolicMessageEnvelope.installInbound(
                    SymbolicMessageEnvelope.takeOutbound());

            assertTrue("the address still answers",
                    task.acceptsRootInvocation(address(3), false));
            assertFalse("and still refuses every other k",
                    task.acceptsRootInvocation(address(4), false));
        }

        /** A refusal always states a difference; a match states none. */
        private void everyRefusalNamesWhatDiffered() {
            OccurrenceAddress planned = address(3);
            assertEquals("", planned.describe(address(3)));
            assertFalse("a refusal is never a hole in the sentence",
                    planned.difference(address(2)).trim().isEmpty());
            assertTrue(planned.difference(address(2)),
                    planned.difference(address(2)).contains("activation 2"));
            // describe() answers "" for a match, and difference() must still
            // say something a reader can act on.
            assertFalse(planned.difference(address(3)).trim().isEmpty());
        }

        private static OccurrenceAddress address(int ordinal) {
            return OccurrenceAddress.of(NODE, REGION, ordinal);
        }

        /** One planned occurrence with one selected IN communication handoff. */
        private static ConcolicTaskPlan.RuntimeTask task(int ordinal)
                throws Exception {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("taskId", "TASK.SEED.address");
            encoded.addProperty("goalId", "GOAL.1");
            encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
            encoded.addProperty("regionId", REGION);
            encoded.addProperty("relationKey", "REL.1");
            encoded.addProperty("sourceKey", NODE);
            encoded.addProperty("occurrenceId",
                    NODE + "/region/" + REGION + "#" + ordinal);
            encoded.addProperty("rootMethod", "<a.B: void run()>");
            encoded.addProperty("instrumentationSelector", "sel");
            JsonObject admission = new JsonObject();
            admission.addProperty("state", "EXECUTABLE");
            encoded.add("admission", admission);
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "GLOBAL_INVOCATION");
            selector.addProperty("invocationOrdinal", ordinal);
            selector.addProperty("method", "<a.B: void run()>");
            JsonObject anchor = new JsonObject();
            anchor.addProperty("sourceKey", NODE);
            anchor.addProperty("kind", "REGISTERED_SOURCE");
            selector.add("causalAnchor", anchor);
            encoded.add("rootSelector", selector);
            encoded.add("branches", new JsonArray());
            encoded.add("inputActions", new JsonArray());
            JsonObject loopBound = new JsonObject();
            loopBound.addProperty("schemaVersion", 1);
            encoded.add("loopBound", loopBound);
            JsonArray handoffs = new JsonArray();
            JsonObject handoff = new JsonObject();
            handoff.addProperty("portId", PORT);
            handoff.addProperty("handoffLeafPath", PORT);
            handoff.addProperty("side", "IN");
            handoff.addProperty("direction", "RESPONSE");
            handoff.addProperty("captureKind", "CALL_RETURN");
            handoff.addProperty("javaType", "int");
            handoff.addProperty("declaredCallee", "<a.P: int getKeyId()>");
            handoff.addProperty("definitionMethod", "<a.B: void run()>");
            handoff.addProperty("definitionUnitIndex", 2);
            handoffs.add(handoff);
            encoded.add("communicationHandoffs", handoffs);
            return new ConcolicTaskPlan.RuntimeTask(
                    ExecutionTask.decode(encoded));
        }
    }


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
    static final class EpochScopedActivationCountTest {
        private static final String NODE = "hdfs/nn0";
        private static final String REGION = "REGION.9492ec77";
        private static final String ROOT = "<a.Manager: void deleteSnapshot()>";

        public void clearRegistry() {
            RuntimeTraceContext.resetForTests();
        }

        /**
         * Twice before the restart, twice after: epoch 1's first is the third.
         */
        public void epochScopedActivationCountRules() throws Exception {
            theEpochOneAddressMatchesTheThirdActivation();
            theEpochOneSecondAddressMatchesTheFourthActivation();
            twoEpochsAreTwoBuckets();
            anUnattributedActivationCountsInTheUnregisteredSource();
            aRegisteredReceiverDecidesWhereTheActivationRan();
            anUnregisteredReceiverFallsBackToTheThreadsContext();
            anInheritedContradictionIsRecordedNotRefused();
            aRegionThatNeverExecutesTheSiteIsAdmittedByItsAddress();
            aRootLoopTaskWithoutKIsRefusedAtPlan();
        }

        private void theEpochOneAddressMatchesTheThirdActivation() {
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
        private void theEpochOneSecondAddressMatchesTheFourthActivation() {
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
        private void twoEpochsAreTwoBuckets() {
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
        private void anUnattributedActivationCountsInTheUnregisteredSource() {
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
        private void aRegisteredReceiverDecidesWhereTheActivationRan() {
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
        private void anUnregisteredReceiverFallsBackToTheThreadsContext() {
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
        private void anInheritedContradictionIsRecordedNotRefused() {
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
        private void aRegionThatNeverExecutesTheSiteIsAdmittedByItsAddress() {
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
        private void aRootLoopTaskWithoutKIsRefusedAtPlan() {
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
    static final class ActivationIsCountedWhereItRanTest {
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
        public void activationIsCountedWhereItRanRules() throws Exception {
            eachNodesFirstActivationAnswersOnlyThatNodesTask();
            anUnregisteredSharedReceiverIsNotOneNodesOccurrence();
            anUnattributedActivationTakesNoKFromThePlannedNode();
            anOrdinalRefusalNamesTheAttributedNode();
            theBucketIsTheAttributedNode();
        }

        private void eachNodesFirstActivationAnswersOnlyThatNodesTask() {
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
        private void anUnregisteredSharedReceiverIsNotOneNodesOccurrence() {
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
        private void anUnattributedActivationTakesNoKFromThePlannedNode() {
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
        private void anOrdinalRefusalNamesTheAttributedNode() {
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
        private void theBucketIsTheAttributedNode() {
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


    /**
     * A published activation name says which activation of which region on which
     * source this row plans.  Two independent recordings of one workload observe
     * that same activation, so they have to publish the same name for it.
     */
    static final class ActivationIdentityContentTest {
        private static final String OCCURRENCE =
                "hdfs-17899/target-dn#epoch0/region/REGION.53092d3e#1";
        private static final String METHOD = "<example.Keys: byte[] retrieve(int)>";
        private static final SourceRef SOURCE = new SourceRef(
                "HDFS_DATANODE", "DATANODE", "hdfs-17899/target-dn", 0L);

        /**
         * The same activation, aggregated out of two different recordings of one
         * workload, is published under one name.
         *
         * <p>The two roots below differ in every value a recording assigns and
         * agree on every value the workload decides: the recording JVM's thread
         * id, the recorder's global event counter behind {@code callId} and
         * {@code seq}, the trace-context lane and span tickets and the receiver's
         * object id all differ; the test, the source, the root method, the
         * receiver class and the causal request are the same.  That is exactly
         * the difference between two recordings of one obligation.</p>
         */
        public void twoRecordingsPublishOneActivationName() {
            RuntimeRegionPlanner.MethodEvent first = root(11L, 4L, 13703L,
                    452L, 458L, 313);
            RuntimeRegionPlanner.MethodEvent second = root(97L, 26L, 21847L,
                    456L, 462L, 300);

            assertNotEquals("the recorded correlation key addresses one frame of "
                            + "one recording and is expected to differ",
                    RuntimeRegionPlanner.recordedActivationKey(first),
                    RuntimeRegionPlanner.recordedActivationKey(second));

            String firstName = publishedName(first);
            String secondName = publishedName(second);
            assertEquals("two recordings of one activation must publish one name",
                    firstName, secondName);
        }

        private static String publishedName(
                RuntimeRegionPlanner.MethodEvent root) {
            return RuntimeRegionPlanner.activationId(OCCURRENCE,
                    selector(root, 1));
        }

        private static Map<String, Object> selector(
                RuntimeRegionPlanner.MethodEvent root, int invocationOrdinal) {
            return RuntimeRegionPlanner.rootSelector(root, SOURCE,
                    root.requestKey, root.requestApi, invocationOrdinal);
        }

        /** One recording's view of the same activation. */
        private static RuntimeRegionPlanner.MethodEvent root(
                long seq, long tid, long callId, long laneId, long spanId,
                int objectId) {
            return new RuntimeRegionPlanner.MethodEvent(seq,
                    "org.apache.hadoop.hdfs.TestBlockTokenBug3", "DataXceiver",
                    tid, METHOD, objectId,
                    "org.apache.hadoop.hdfs.security.token.block"
                            + ".BlockTokenSecretManager",
                    callId, callId - 1L, 7L, laneId, spanId, spanId - 1L, 0L,
                    SOURCE, true,
                    "hdfs-17899/source-dn#epoch0/request/replicate-block#1",
                    "replicate-block");
        }
    }


    /**
     * A published object id says which object a planned receiver anchor names.
     * Two independent recordings of one workload observe that same object, so
     * they have to publish the same id for it.
     *
     * <p>The recorder's own {@code identity()} counter cannot do that: it hands
     * out numbers in the order objects happen to be touched, so hdfs-17899's
     * {@code BlockTokenSecretManager.allKeys} receiver was object 313 in one
     * recording of bug3 and object 300 in the next.  The naming under test
     * replaces that counter with the address of the object's first observation
     * plus an ordinal within that address, which is the same shape the plan
     * already uses for activation-local site occurrences.</p>
     */
    static final class RuntimeObjectIdentityContentTest {
        private static final String SOURCE = "hdfs-17899/target-dn#epoch0";
        private static final String METHOD =
                "<example.Keys: byte[] retrieve(int)>";
        private static final String SITE = METHOD + "#u4";
        private static final String FIELD = "<example.Keys: java.util.Map all>";

        private static String receiverAddress() {
            return RuntimeObjectIdentity.address(SOURCE, "FIELD_READ", METHOD,
                    SITE, -1, FIELD, "", "fieldReceiverObjectId");
        }

        private static String valueAddress() {
            return RuntimeObjectIdentity.address(SOURCE, "FIELD_READ", METHOD,
                    SITE, -1, FIELD, "", "valueObjectId");
        }

        /**
         * One object, two recordings, one published id.
         *
         * <p>The two recordings below differ in exactly what a recording decides
         * -- how many objects were touched before this one, and therefore what
         * number the counter had reached -- and agree on what the workload
         * decides: the source, the event, the method, the static site, the field
         * and the slot.  That is the difference between two recordings of one
         * obligation.</p>
         */
        public void runtimeObjectIdentityContentRules() throws Exception {
            twoRecordingsPublishOneObjectName();
            twoObjectsAtOneAddressKeepTwoNames();
        }

        private void twoRecordingsPublishOneObjectName() {
            RuntimeObjectIdentity first = new RuntimeObjectIdentity();
            first.observe(313, receiverAddress());

            RuntimeObjectIdentity second = new RuntimeObjectIdentity();
            second.observe(300, receiverAddress());

            assertNotEquals("the recorded counters address one recording each "
                            + "and are expected to differ", 313, 300);
            assertEquals("two recordings of one object must publish one id",
                    first.nameOf(313), second.nameOf(300));
        }

        /**
         * The naming stays injective: two objects of one site keep two ids.
         *
         * <p>The planned receiver index and the shared-field flow grouping both
         * ask only whether two published ids are the same object, so collapsing
         * two receivers of one field onto one id would silently merge two
         * locations.  The ordinal within the address is what prevents that.</p>
         */
        private void twoObjectsAtOneAddressKeepTwoNames() {
            RuntimeObjectIdentity identity = new RuntimeObjectIdentity();
            identity.observe(313, receiverAddress());
            identity.observe(314, receiverAddress());

            assertNotEquals("two receivers of one field are two locations",
                    identity.nameOf(313), identity.nameOf(314));
            assertEquals(2, identity.size());
        }
    }


    /**
     * One occurrence's loop bodies are one enclosing invocation's.
     *
     * <p>An enclosing activation of a region on a node is the k-th activation in
     * the window, and its loop bodies are {@code #k#aN}. Bodies of a different
     * enclosing invocation -- another thread, another entry event, another
     * request -- belong to a different k by definition.</p>
     *
     * <p>Two things let one occurrence absorb another activation, and lane
     * 11741f shows both in one row: {@code REGION.2392e4b7…#5} published
     * {@code #a1..#a6} from an enclosing call on {@code IPC Server handler 8} and
     * {@code #a7,#a8} from another on {@code handler 2} -- eight bodies of a
     * four-element key array -- while the tasks addressed #1 and #4, the two
     * other balancer-driven invocations of the same region, were never answered.
     * First, admission at the loop root did not compare the address at all when
     * the task had a unique OUT anchor and the request matched: any invocation
     * under {@code balancer/balance-block#1} was every one of those addresses.
     * Second, nothing bound a task to the invocation it was admitted for.</p>
     */
    static final class LoopBodiesBelongToOneInvocationTest {
        private static final String NODE = "hdfs-17899/nn0";
        private static final String PLANNED_REQUEST_API = "heartbeat";
        private static final String PLANNED_REQUEST_SOURCE =
                "hdfs-17899/target-dn";

        public void clear() {
            RuntimeTraceContext.resetForTests();
            CausynthTraceRecorder.setRecordingStartedForTests(false);
        }

        /** Two enclosing invocations are occurrences #1 and #2, never one. */
        public void loopBodiesBelongToOneInvocationRules() throws Exception {
            twoEnclosingInvocationsAreTwoOccurrences();
            aTaskKeepsTheInvocationItWasAdmittedFor();
            anInvocationUnderThePlannedRequestIsNotEveryOccurrence();
        }

        private void twoEnclosingInvocationsAreTwoOccurrences() {
            ConcolicTaskPlan.RuntimeTask first = task(1);
            ConcolicTaskPlan.RuntimeTask second = task(2);
            ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                    Arrays.asList(first, second));
            Object node = openWindowOn(NODE);

            Map<String, Integer> firstEntry = plan.addressLoopRootInvocation(
                    first.rootMethod, first.rootMethod, node, new Object[0], 11L);
            Map<String, Integer> secondEntry = plan.addressLoopRootInvocation(
                    first.rootMethod, first.rootMethod, node, new Object[0], 12L);

            assertEquals("the first enclosing invocation is occurrence 1",
                    Collections.singletonMap(first.taskId, 1), firstEntry);
            assertEquals("the second is occurrence 2, and only that",
                    Collections.singletonMap(second.taskId, 2), secondEntry);
        }

        /**
         * A task keeps the one enclosing invocation it was admitted for.
         *
         * <p>Every hook of one physical entry asks again, so the same entry
         * event answers yes for as long as that invocation runs; a different
         * entry event never does, whatever else about it matches.</p>
         */
        private void aTaskKeepsTheInvocationItWasAdmittedFor() {
            ConcolicTaskPlan.RuntimeTask task = task(1);

            assertTrue("the invocation it was admitted for",
                    task.claimsEnclosingInvocation(11L));
            assertTrue("and every sibling hook of that same entry",
                    task.claimsEnclosingInvocation(11L));
            assertEquals(11L, task.enclosingInvocationEvent());
            assertTrue("a second enclosing invocation is not this occurrence",
                    !task.claimsEnclosingInvocation(12L));
            assertEquals("and it did not take it either", 11L,
                    task.enclosingInvocationEvent());
        }

        /**
         * The OUT anchor may defer a missing registration; it may not be the
         * address.
         *
         * <p>The deferral exists because a producer's receiver is commonly
         * unregistered at entry and its unique planner-authored OUT port
         * confirms the node before the activation publishes. At an enclosing
         * loop root it stood in for the whole address instead, so every
         * invocation under the planned request answered every k of that region.
         * It is gone from this path: the address decides, and the refusal names
         * the difference.</p>
         */
        private void anInvocationUnderThePlannedRequestIsNotEveryOccurrence() {
            ConcolicTaskPlan.RuntimeTask first = task(1);
            ConcolicTaskPlan.RuntimeTask second = task(2);
            ConcolicTaskPlan plan = new ConcolicTaskPlan(null,
                    Arrays.asList(first, second));
            CausynthTraceRecorder.setRecordingStartedForTests(true);
            Object caller = new Object();
            RuntimeTraceContext.registerSource(caller, new SourceRef(
                    "DATANODE", "dn", PLANNED_REQUEST_SOURCE, 0L));
            long request = RuntimeTraceContext.beginRequest(caller,
                    PLANNED_REQUEST_API);
            try {
                // The condition the deferral turns on, stated rather than
                // assumed: unique OUT anchor, no registered receiver, and the
                // exact planned request.
                assertTrue("this is the shape the deferral admitted",
                        ConcolicTaskPlan
                                .mayDeferMissingContextToOutgoingAnchor(first,
                                        null, RuntimeTraceContext.current()));

                Map<String, Integer> admitted =
                        plan.addressLoopRootInvocation(first.rootMethod,
                                first.rootMethod, null, new Object[0], 11L);

                assertTrue("an activation of another node is no occurrence of "
                                + "this one: " + admitted,
                        admitted.isEmpty());
                assertTrue(first.unansweredAddress(),
                        first.unansweredAddress().startsWith(
                                "1 compatible activation(s)"));
            } finally {
                RuntimeTraceContext.endRequest(request);
            }
        }

        /** Opens the recording window with {@code node} registered. */
        private static Object openWindowOn(String sourceKey) {
            RuntimeTraceContext.resetForTests();
            CausynthTraceRecorder.setRecordingStartedForTests(true);
            Object node = new Object();
            RuntimeTraceContext.registerSource(node,
                    new SourceRef("NAMENODE", "nn", sourceKey, 0L));
            return node;
        }

        /** The lane's own producer plan row, addressed at {@code ordinal}. */
        private static ConcolicTaskPlan.RuntimeTask task(int ordinal) {
            JsonObject encoded =
                    row("plans/hdfs-17899-bug3-loop-body-producer.json");
            String regionId = encoded.get("regionId").getAsString();
            encoded.addProperty("taskId", "TASK.SEED.occurrence" + ordinal);
            encoded.addProperty("occurrenceId", NODE + "#epoch0/region/"
                    + regionId + "#" + ordinal);
            encoded.getAsJsonObject("rootSelector")
                    .addProperty("invocationOrdinal", ordinal);
            return new ConcolicTaskPlan.RuntimeTask(
                    ExecutionTask.decode(encoded));
        }

        private static JsonObject row(String resource) {
            try (InputStream bytes = LoopBodiesBelongToOneInvocationTest.class
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


    /**
     * A value arriving over the wire does not say where the receiver ran.
     *
     * <p>An occurrence is addressed by (node, epoch, region, k-th activation),
     * and the node is where the activation ran. Execution context is set by
     * execution-scope events only: a node registering its instances, or an async
     * seed taken from a registered source. What a message carries is provenance,
     * and the propagated expression already states it.</p>
     *
     * <p>{@code enterInbound} used to fall back to the SENDER's source, parsed
     * out of the message header, when the local owner was unregistered and the
     * thread had no source yet. At record time a DataNode thread already carries
     * the DN, so the arm never fired; at replay the thread may be fresh, so it
     * did. On hdfs-17899 bug3 that is "matching root inherited
     * hdfs-17899/nn0#epoch0 instead of hdfs-17899/target-dn#epoch0", and the
     * ordinal inflation behind it: every node's activations of one region landing
     * in one counter because they all claimed one node.</p>
     */
    static final class ExecutionContextIsNotProvenanceTest {
        private static final String NN = "hdfs-17899/nn0";
        private static final String DN = "hdfs-17899/target-dn";

        public void clearRegistry() {
            RuntimeTraceContext.resetForTests();
        }

        /** A thread carrying the DataNode keeps it when the NameNode's value
         *  arrives on it. */
        public void executionContextIsNotProvenanceRules() throws Exception {
            anArrivingValueDoesNotRestampTheReceivingThread();
            anArrivalOnAnUnattributedThreadNamesNoNode();
            aRegisteredLocalOwnerStillNamesTheReceiver();
        }

        private void anArrivingValueDoesNotRestampTheReceivingThread() {
            RuntimeTraceContext.resetForTests();
            Object nameNode = new Object();
            RuntimeTraceContext.registerSource(nameNode,
                    new SourceRef("NAMENODE", "nn", NN, 0L));
            Object dataNode = new Object();
            RuntimeTraceContext.registerSource(dataNode,
                    new SourceRef("DATANODE", "dn", DN, 0L));

            // The NameNode sends; the header states its source, as provenance.
            long request = RuntimeTraceContext.beginRequest(nameNode, "heartbeat");
            String header = RuntimeTraceContext.outboundHeader(nameNode);
            RuntimeTraceContext.endRequest(request);
            assertNotNull(header);

            // The DataNode thread is executing as the DataNode.
            long dnRequest = RuntimeTraceContext.beginRequest(dataNode,
                    "block-report");
            assertEquals(DN + "#epoch0",
                    RuntimeTraceContext.currentSource().key());

            // The value arrives on that thread, through an owner the workload
            // never registered -- an IPC connection, not a node.
            long inbound = RuntimeTraceContext.enterInbound(header, "IPC",
                    "corr-1", "attempt-1", "REQUEST", new Object());

            assertEquals("the thread still runs as the DataNode",
                    DN + "#epoch0",
                    RuntimeTraceContext.currentSource().key());

            RuntimeTraceContext.exitInbound(inbound);
            RuntimeTraceContext.endRequest(dnRequest);
        }

        /** With nothing registered and no ambient source, the arrival names none. */
        private void anArrivalOnAnUnattributedThreadNamesNoNode() {
            RuntimeTraceContext.resetForTests();
            Object nameNode = new Object();
            RuntimeTraceContext.registerSource(nameNode,
                    new SourceRef("NAMENODE", "nn", NN, 0L));
            long request = RuntimeTraceContext.beginRequest(nameNode, "heartbeat");
            String header = RuntimeTraceContext.outboundHeader(nameNode);
            RuntimeTraceContext.endRequest(request);

            long inbound = RuntimeTraceContext.enterInbound(header, "IPC",
                    "corr-1", "attempt-1", "REQUEST", new Object());

            assertNull("provenance is not an execution scope",
                    RuntimeTraceContext.currentSource());

            RuntimeTraceContext.exitInbound(inbound);
        }

        /** A registered local owner still names the receiving side, as before. */
        private void aRegisteredLocalOwnerStillNamesTheReceiver() {
            RuntimeTraceContext.resetForTests();
            Object nameNode = new Object();
            RuntimeTraceContext.registerSource(nameNode,
                    new SourceRef("NAMENODE", "nn", NN, 0L));
            Object dataNode = new Object();
            RuntimeTraceContext.registerSource(dataNode,
                    new SourceRef("DATANODE", "dn", DN, 0L));
            long request = RuntimeTraceContext.beginRequest(nameNode, "heartbeat");
            String header = RuntimeTraceContext.outboundHeader(nameNode);
            RuntimeTraceContext.endRequest(request);

            long inbound = RuntimeTraceContext.enterInbound(header, "IPC",
                    "corr-1", "attempt-1", "REQUEST", dataNode);

            assertEquals(DN + "#epoch0",
                    RuntimeTraceContext.currentSource().key());

            RuntimeTraceContext.exitInbound(inbound);
        }
    }


    /**
     * A thread inside the workload's own request scope carries it.
     *
     * <p>The workload opens the scope itself --
     * {@code CausynthMessagePropagation.beginRequest(nnc, "refresh-block-keys")}
     * in bug2, {@code beginRequestIfRegistered(dn.getDatanodeId(), "heartbeat")}
     * in the DataNode -- and the same call runs in the recording and in the
     * replay. Everything the send then needs hangs off it: the outbound envelope
     * is active only when the thread carries a source, a request key and a
     * request api ({@code outboundHeader}), and the activation's attribution is
     * that same source ({@code activationSource}'s ambient arm). One scope, two
     * consumers, and this pins both against the one implementation.</p>
     */
    static final class RequestScopeIsHonouredTest {
        private static final String SPS = "hdfs-17899/sps";

        public void clearRegistry() {
            RuntimeTraceContext.resetForTests();
        }

        /** The envelope is active and the activation is that source's. */
        public void requestScopeIsHonouredRules() throws Exception {
            aThreadInsideARequestScopeCarriesItsSource();
            aRequestScopeIsInheritedByThreadsStartedInsideIt();
            workCarriesItsScopeToThePoolThreadThatWritesIt();
            arefusedEnvelopeNamesWhatWasMissing();
            aRefusalSeparatesTheCallFromTheThread();
            aThreadOlderThanTheScopeCarriesNothing();
        }

        private void aThreadInsideARequestScopeCarriesItsSource() {
            RuntimeTraceContext.resetForTests();
            Object nnc = new Object();
            RuntimeTraceContext.registerSource(nnc,
                    new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));

            long request = RuntimeTraceContext.beginRequest(nnc,
                    "refresh-block-keys");
            try {
                assertNotNull("the thread carries the source",
                        RuntimeTraceContext.currentSource());
                assertEquals(SPS + "#epoch0",
                        RuntimeTraceContext.currentSource().key());
                // What Client$Connection.sendRpcRequest asks for: an active
                // outbound envelope.  It refuses without source + request flow,
                // and that refusal is what leaves causynth.active() false and
                // the fault marker behind its short circuit unminted.
                String header = RuntimeTraceContext.outboundHeader(nnc);
                assertTrue(header, header.startsWith("1|"));
                assertEquals("source, request key and api, all present",
                        8, header.split("\\|", -1).length);
                // And the activation that runs here is that source's, by the
                // ambient arm of the one attribution function.
                assertEquals(SPS + "#epoch0",
                        RuntimeTraceContext.activationSource(null).key());
            } finally {
                RuntimeTraceContext.endRequest(request);
            }

            // Outside it again: no envelope, and nothing attributed.
            assertEquals("the unregistered source, as the planner counts it",
                    RuntimeTraceContext.UNREGISTERED_SOURCE.key(),
                    RuntimeTraceContext.activationSource(null).key());
        }

        /**
         * A thread started inside the scope inherits it; one started before it
         * does not.
         *
         * <p>{@code RuntimeTraceContext}'s state is an
         * {@link InheritableThreadLocal}, which is how work handed to a thread
         * the workload creates inside its own request keeps that request's
         * node.  It also means the moment a thread is created decides what it
         * carries, which is worth pinning: an executor thread created once, at
         * cluster start, carries nothing however many requests later run on
         * it.</p>
         */
        private void aRequestScopeIsInheritedByThreadsStartedInsideIt()
                throws Exception {
            RuntimeTraceContext.resetForTests();
            Object nnc = new Object();
            RuntimeTraceContext.registerSource(nnc,
                    new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));
            long request = RuntimeTraceContext.beginRequest(nnc,
                    "refresh-block-keys");
            try {
                final String[] inside = new String[1];
                Thread started = new Thread(() -> inside[0] =
                        RuntimeTraceContext.activationSource(null).key(),
                        "inside");
                started.start();
                started.join();
                assertEquals("a thread started inside the scope inherits it",
                        SPS + "#epoch0", inside[0]);
            } finally {
                RuntimeTraceContext.endRequest(request);
            }
        }

        /**
         * Work carries its own scope to the thread that performs it.
         *
         * <p>The point of the capture: Hadoop's {@code Client} builds a
         * {@code Call} on the caller's thread, inside the workload's request,
         * and writes it from a sender thread its connection pool created once,
         * before that request existed. The scope travels with the call, so the
         * send names the node and request the work belongs to however old the
         * thread is.</p>
         */
        private void workCarriesItsScopeToThePoolThreadThatWritesIt()
                throws Exception {
            RuntimeTraceContext.resetForTests();
            Object nnc = new Object();
            RuntimeTraceContext.registerSource(nnc,
                    new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));

            // A pool thread that existed before any request, as a connection's
            // sender threads do.
            final java.util.concurrent.CountDownLatch made =
                    new java.util.concurrent.CountDownLatch(1);
            final java.util.concurrent.CountDownLatch wrote =
                    new java.util.concurrent.CountDownLatch(1);
            final Object[] carried = new Object[1];
            final String[] header = new String[1];
            final String[] withoutScope = new String[1];
            final String[] filedUnder = new String[1];
            final String[] filedWithoutScope = new String[1];
            Thread sender = new Thread(() -> {
                try {
                    made.await();
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                    return;
                }
                try {
                    RuntimeTraceContext.outboundHeader(nnc);
                    withoutScope[0] = "ACTIVE";
                } catch (IllegalStateException noFlow) {
                    withoutScope[0] = "REFUSED";
                }
                header[0] = RuntimeTraceContext.outboundHeader(nnc, carried[0]);
                // The row the recorder writes for this send is attributed from
                // the same token, so the trace and the wire agree on the node.
                RuntimeTraceContext.View scoped =
                        RuntimeTraceContext.exchange(nnc, carried[0]);
                filedUnder[0] = (scoped.source == null ? ""
                        : scoped.source.key()) + " " + scoped.requestKey;
                RuntimeTraceContext.View unscoped =
                        RuntimeTraceContext.exchange(nnc, null);
                filedWithoutScope[0] = (unscoped.source == null ? ""
                        : unscoped.source.key()) + " " + unscoped.requestKey;
                wrote.countDown();
            }, "IPC Parameter Sending Thread #0");
            sender.start();

            long request = RuntimeTraceContext.beginRequest(nnc,
                    "refresh-block-keys");
            carried[0] = RuntimeTraceContext.captureScope();
            made.countDown();
            wrote.await();
            RuntimeTraceContext.endRequest(request);

            assertEquals("the pool thread's own state names no request",
                    "REFUSED", withoutScope[0]);
            assertTrue(header[0], header[0].startsWith("1|"));
            assertEquals("and the carried scope names all eight fields",
                    8, header[0].split("[|]", -1).length);
            assertTrue("the source is the work's, not the thread's",
                    header[0].contains(java.util.Base64.getUrlEncoder()
                            .withoutPadding().encodeToString(
                            SPS.getBytes("UTF-8"))));
            assertEquals("and the recorded row names the same node and request",
                    SPS + "#epoch0 " + SPS
                            + "#epoch0/request/refresh-block-keys#1",
                    filedUnder[0]);
            assertEquals("which the thread alone cannot name: no request at all",
                    SPS + "#epoch0 ", filedWithoutScope[0]);
        }

        /**
         * A refused outbound envelope names what the thread was missing.
         *
         * <p>bug2 guards its fault marker with {@code causynth.active()}, so an
         * envelope refused here means {@code Debug.makeSymbolicBoolean} is
         * never called and the region publishes
         * NO_SELECTED_INPUT_MATERIALIZED.  "It refused" is not actionable;
         * which of source, requestKey and requestApi was absent is.</p>
         */
        private void arefusedEnvelopeNamesWhatWasMissing() {
            RuntimeTraceContext.resetForTests();
            Object nnc = new Object();
            RuntimeTraceContext.registerSource(nnc,
                    new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));
            try {
                RuntimeTraceContext.outboundHeader(nnc);
                org.junit.Assert.fail("no request scope, no envelope");
            } catch (IllegalStateException refused) {
                String said = String.valueOf(refused.getMessage());
                assertTrue(said, said.contains("requestKey"));
                assertTrue(said, said.contains("requestApi"));
                // The owner named the source, so that half is not missing.
                assertTrue(said, !said.contains("no source"));
            }
        }

        /**
         * A refusal separates what the call carried from what the thread holds.
         *
         * <p>The carried scope IS the scope of the send; the thread's is only
         * what answers when nothing was carried.  One combined list cannot tell
         * "the work carried nothing" from "the work carried a node and no
         * request", and those have different owners -- the first is the carry,
         * the second is where the work was created.  On laneB2i the row said
         * only "this thread carries no source requestKey requestApi", which is
         * true of the thread and says nothing about the call.</p>
         */
        private void aRefusalSeparatesTheCallFromTheThread() throws Exception {
            RuntimeTraceContext.resetForTests();
            Object nnc = new Object();
            RuntimeTraceContext.registerSource(nnc,
                    new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));

            // Nothing carried at all.
            try {
                RuntimeTraceContext.outboundHeader(nnc, null);
                org.junit.Assert.fail("no scope, no envelope");
            } catch (IllegalStateException refused) {
                String said = String.valueOf(refused.getMessage());
                assertTrue(said, said.contains("the call carried no scope at all"));
                assertTrue(said, said.contains("thread "
                        + Thread.currentThread().getName()));
                assertTrue(said, said.contains("requestKey"));
            }

            // A scope captured where the node was known and no request was open:
            // it names the node and nothing else, and the send still refuses.
            Object partial;
            RuntimeTraceContext.enterRoot(nnc);
            partial = RuntimeTraceContext.captureScope();
            try {
                RuntimeTraceContext.outboundHeader(nnc, partial);
                org.junit.Assert.fail("a node is not a request");
            } catch (IllegalStateException refused) {
                String said = String.valueOf(refused.getMessage());
                assertTrue(said, said.contains("a partial scope holding only"));
                assertTrue(said, said.contains("source=" + SPS + "#epoch0"));
                assertTrue(said, !said.contains("requestKey="));
            }
        }

        /** A thread that existed before the scope carries nothing. */
        private void aThreadOlderThanTheScopeCarriesNothing() throws Exception {
            RuntimeTraceContext.resetForTests();
            Object nnc = new Object();
            RuntimeTraceContext.registerSource(nnc,
                    new SourceRef("EXTERNAL_APP", "SPS", SPS, 0L));

            final java.util.concurrent.CountDownLatch open =
                    new java.util.concurrent.CountDownLatch(1);
            final java.util.concurrent.CountDownLatch read =
                    new java.util.concurrent.CountDownLatch(1);
            final String[] seen = new String[1];
            Thread older = new Thread(() -> {
                try {
                    open.await();
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                    return;
                }
                seen[0] = RuntimeTraceContext.activationSource(null).key();
                read.countDown();
            }, "older");
            older.start();

            long request = RuntimeTraceContext.beginRequest(nnc,
                    "refresh-block-keys");
            open.countDown();
            read.await();
            RuntimeTraceContext.endRequest(request);

            assertEquals("the send runs on a thread the scope never reached",
                    RuntimeTraceContext.UNREGISTERED_SOURCE.key(), seen[0]);
        }
    }

}
