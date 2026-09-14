package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.Test;

import java.util.LinkedHashMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * A map carrier is given a receiver identity the same way a scalar one is.
 *
 * <p>The plan's frozen receiver locators are indexed out of {@code
 * inputActions} ({@code ConcolicTaskPlan.indexPlannedReceiverObjectIds} reads
 * {@code fieldReceiverObjectId} off each planned action), so a location the
 * plan declares as a shared carrier and never reads as a symbolic input has
 * none. Every shape that goes through the receiver rule has a second answer
 * for that case -- the replay-stable access anchor -- and a map was excluded
 * from it, twice over: {@code bindPlannedReceiver} skipped the fallback for a
 * map, and {@code recordConsumerAccess} threw away the anchors it would have
 * been built from. A map was therefore the one shape that could end up with
 * no receiver at all, and {@code captureRecordedSharedStateRaw} then refuses
 * it -- correctly, since publishing with a receiver of 0 would drop it out of
 * every cross-session family, but the result is that no version of the map is
 * read out.</p>
 *
 * <p>On HDFS-17960 that location is {@code
 * DirectorySnapshottableFeature#snapshotsByNames}, the bug's own map and one
 * of the four the slice keeps.</p>
 */
public class MapCarrierReceiverIdentityTest {

    private static final String OWNER = "org.apache.hadoop.hdfs.server"
            + ".namenode.snapshot.DirectorySnapshottableFeature";
    private static final String FIELD = "snapshotsByNames";
    private static final String DESCRIPTOR = "Ljava/util/List;";
    private static final String SITE =
            "<" + OWNER + ": java.util.List getSnapshot(byte[])>#u7";

    /**
     * One object is one receiver, in every activation that touches it.
     *
     * <p>The name answers "which object is this".  A map read from two
     * activations of two occurrences is one object and must get one id; two
     * maps read at one site are two objects and must get two.  The VM states
     * its own identity for the object in the location key it answers the
     * capture with, and that is what is used.</p>
     *
     * <p>It used to be a hash of the access anchor with the planned
     * occurrence folded in, which got the second half right and the first
     * half exactly wrong: every worker of a replay group replays a different
     * occurrence, so one map was given four names and IMPORT stopped on six
     * SHARED_STATE_MAP_STATE_IDENTITY_AMBIGUOUS rows.</p>
     */
    @Test
    public void oneObjectIsOneReceiverAcrossActivations() throws Exception {
        long first = namedByVm(24L, "occ#1", SITE, 1);
        long second = namedByVm(24L, "occ#2", SITE, 1);
        long otherMap = namedByVm(25L, "occ#1", SITE, 1);

        assertEquals("one object, one receiver, two activations",
                first, second);
        assertNotEquals("two objects at one site are two receivers",
                first, otherMap);
        assertTrue("and it is not mistaken for an anchor hash",
                (first & 1L << 62) == 0L);
    }

    /** With no object to name, the anchor answers -- without an activation. */
    @Test
    public void theAnchorFallbackDoesNotNameAnActivation() throws Exception {
        long first = named("occ#1", SITE, 1);
        long other = named("occ#2", SITE, 1);
        long elsewhere = named("occ#1", SITE + "x", 1);

        assertEquals("the activation is not part of the name",
                first, other);
        assertNotEquals("two access sites are two receivers",
                first, elsewhere);
    }

    /** A frozen plan locator outranks the replay-side object identity. */
    @Test
    public void aFrozenLocatorIsNotOverwritten() throws Exception {
        SharedStateCapture.SharedCarrier carrier = mapCarrier();
        carrier.recordConsumerAccess(anchor(SITE, 1));
        carrier.bindPlannedReceiver(4242L);
        carrier.bindVmOwnerIdentity(24L);

        assertEquals(4242L, carrier.plannedReceiverObjectId());
    }

    // ---------- harness ----------

    private static long namedByVm(long vmOwnerRid, String occurrenceId,
                                  String site, int occurrence)
            throws Exception {
        SharedStateCapture.SharedCarrier carrier = mapCarrier();
        carrier.recordConsumerAccess(anchor(site, occurrence));
        carrier.bindPlannedReceiver(task(occurrenceId));
        carrier.bindVmOwnerIdentity(vmOwnerRid);
        return carrier.plannedReceiverObjectId();
    }

    private static long named(String occurrenceId, String site,
                              int occurrence) throws Exception {
        SharedStateCapture.SharedCarrier carrier = mapCarrier();
        carrier.recordConsumerAccess(anchor(site, occurrence));
        carrier.bindPlannedReceiver(task(occurrenceId));
        return carrier.plannedReceiverObjectId();
    }

    private static SharedStateCapture.SharedCarrier mapCarrier() {
        return SharedStateCapture.SharedCarrier.map(
                new LinkedHashMap<String, Object>(), OWNER, FIELD,
                DESCRIPTOR);
    }

    private static SharedStateCapture.ConsumerAccessAnchor anchor(
            String siteId, int occurrence) {
        return new SharedStateCapture.ConsumerAccessAnchor(siteId,
                occurrence);
    }

    /** A task that declares the map as a carrier and reads no input at all. */
    private static ConcolicTaskPlan.RuntimeTask task(String occurrenceId) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", "REGION.1");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "nn0#epoch1");
        encoded.addProperty("occurrenceId", occurrenceId);
        encoded.addProperty("rootMethod", "<a.B: void run()>");
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        JsonObject causal = new JsonObject();
        causal.addProperty("sourceKey", "nn0#epoch1");
        causal.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", causal);
        encoded.add("rootSelector", selector);
        encoded.add("branches", new JsonArray());
        // The point of the case: a declared carrier and no input action to
        // index a frozen receiver locator out of.
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        JsonObject carrier = new JsonObject();
        carrier.addProperty("declaringClass", OWNER);
        carrier.addProperty("fieldName", FIELD);
        carrier.addProperty("descriptor", DESCRIPTOR);
        carrier.addProperty("kind", "MAP_STATE");
        carrier.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        carrier.add("fieldPath", new JsonArray());
        JsonArray carriers = new JsonArray();
        carriers.add(carrier);
        encoded.add("sharedCarriers", carriers);
        return new ConcolicTaskPlan.RuntimeTask(
                ExecutionTask.decode(encoded));
    }
}
