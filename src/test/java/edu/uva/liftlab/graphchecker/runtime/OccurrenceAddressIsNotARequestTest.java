package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.Test;

import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
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
     * Two candidates under two requests are each the first of their own.
     *
     * <p>The planner counts activations per request; replay has to count the
     * same population or the two ends disagree about which activation is the
     * k-th.  Keyed on the planned request -- a constant per task -- every
     * candidate fell in one bucket, so one arriving from another exchange
     * consumed the planned occurrence's ordinal and replay reported
     * invocation 2 where the plan said 1.</p>
     */
    @Test
    public void candidatesAreCountedInTheRequestTheyEntered() {
        ConcolicTaskPlan.RuntimeTask task = task();

        String here = task.invocationCounterKey(
                "hdfs-17960/client#epoch0/request/record-ordered-deletes#1",
                "record-ordered-deletes");
        String there = task.invocationCounterKey(
                "hdfs-17960/nn0#epoch1/request/restart-namenode#1",
                "restart-namenode");
        String alsoHere = task.invocationCounterKey(
                "hdfs-17960/client#epoch0/request/record-ordered-deletes#1",
                "record-ordered-deletes");

        assertTrue("two exchanges are two buckets", !here.equals(there));
        assertEquals("one exchange is one bucket", here, alsoHere);
    }

    /** The bucket is still the source, region and root of the occurrence. */
    @Test
    public void theBucketIsStillTheOccurrencesOwnScope() {
        ConcolicTaskPlan.RuntimeTask task = task();

        assertTrue(task.invocationCounterKey("", "")
                .startsWith(task.sourceKey));
    }

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
