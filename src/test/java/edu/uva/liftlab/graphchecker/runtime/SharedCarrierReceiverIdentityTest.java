package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.ConsumerAccessAnchor;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.SharedCarrier;
import org.junit.Test;

import java.util.Collection;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * What names the receiver of a per-instance shared field across two replay
 * sessions.
 *
 * <p>One declared field of a class with several live instances inside one
 * activation - a key object per key, read once per loop iteration - has no
 * single frozen receiver locator for the field alone.  The plan does name
 * each receiver, keyed by the exact static access site and the
 * activation-local occurrence of that site which read it; that pair is what
 * the runtime observes at each read and is stable across two replays of the
 * same planned occurrence.  These transcripts pin that every such receiver
 * gets its own non-zero identity, that the identity survives into a
 * cross-session location name, and that a carrier with neither a planned
 * locator nor an access anchor stays unnamed rather than being published
 * under a receiver of 0.</p>
 */
public class SharedCarrierReceiverIdentityTest {
    private static final String OWNER = "a.Key";
    private static final String FIELD = "expiry";
    private static final String DESCRIPTOR = "J";
    private static final String SIGNATURE =
            "<" + OWNER + ": long " + FIELD + ">";
    private static final String READ_SITE =
            "<a.Manager: void sweep()>#u12";
    private static final String OCCURRENCE =
            "hdfs/nn0#epoch0/region/REGION.1#2#a1";

    /** Both receivers reach a cross-session name, and they differ. */
    @Test
    public void bothReceiversCanonicaliseAcrossSessions() {
        ConcolicTaskPlan.RuntimeTask task = task();
        JsonObject summary = summary(
                version("INSTANCE_FIELD/7#24",
                        carrier(new Object(), READ_SITE, 1, task)),
                version("INSTANCE_FIELD/9#24",
                        carrier(new Object(), READ_SITE, 2, task)));

        Collection<String> unresolved =
                SharedStateEvidence.canonicalizeLocations(summary);

        assertEquals("[]", unresolved.toString());
        assertEquals("INSTANCE_FIELD/" + OCCURRENCE + "@receiver:101@"
                        + OWNER + "#" + FIELD + "#24",
                locationKey(summary, 0));
        assertEquals("INSTANCE_FIELD/" + OCCURRENCE + "@receiver:202@"
                        + OWNER + "#" + FIELD + "#24",
                locationKey(summary, 1));
    }

    /**
     * The same two receivers read in the other order still get the same two
     * names: the anchor, not the order of the reads, is the identity.
     */
    @Test
    public void identitiesDoNotDependOnReadOrder() {
        ConcolicTaskPlan.RuntimeTask replay = task();

        assertEquals(202L,
                carrier(new Object(), READ_SITE, 2, replay)
                        .plannedReceiverObjectId());
        assertEquals(101L,
                carrier(new Object(), READ_SITE, 1, replay)
                        .plannedReceiverObjectId());
    }

    /**
     * A carrier with no access anchor and no frozen locator is unnameable.
     *
     * <p>This is the row bug3 raised 14 times and bug2 more: a declared
     * carrier the region selects at entry reaches no field access, so it
     * records no anchor, and a location the plan never also reads as a
     * symbolic input has no frozen locator either.  With neither it binds 0,
     * the read-out refuses it, and the field is dropped while another field
     * on the same object -- one the plan did freeze a locator for -- is
     * captured.  The asymmetry is the plan's, not the field's.</p>
     */
    @Test
    public void aCarrierWithNoAnchorAndNoLocatorCannotBeNamed() {
        SharedCarrier carrier = SharedCarrier.field(new Object(),
                "a.Key", "unplannedField", "J");
        carrier.bindPlannedReceiver(task());

        assertEquals(0L, carrier.plannedReceiverObjectId());
    }

    /** One anchor is enough to name it, whatever the plan froze. */
    @Test
    public void anAnchorNamesACarrierThePlanFrozeNoLocatorFor() {
        SharedCarrier carrier = SharedCarrier.field(new Object(),
                "a.Key", "unplannedField", "J");
        carrier.recordConsumerAccess(
                new ConsumerAccessAnchor("<a.Manager: void sweep()>", 1));
        carrier.bindPlannedReceiver(task());

        assertTrue("an anchored carrier is nameable",
                carrier.plannedReceiverObjectId() > 0L);
    }

    /** Two activations of one region name the carrier differently. */
    @Test
    public void theRegionEntryAnchorSeparatesActivations() {
        SharedCarrier first = SharedCarrier.field(new Object(),
                "a.Key", "unplannedField", "J");
        first.recordConsumerAccess(
                new ConsumerAccessAnchor("<a.Manager: void sweep()>", 1));
        first.bindPlannedReceiver(task());
        SharedCarrier second = SharedCarrier.field(new Object(),
                "a.Key", "unplannedField", "J");
        second.recordConsumerAccess(
                new ConsumerAccessAnchor("<a.Manager: void sweep()>", 2));
        second.bindPlannedReceiver(task());

        assertTrue(first.plannedReceiverObjectId() > 0L);
        assertTrue(second.plannedReceiverObjectId() > 0L);
        assertTrue("two activations are two receivers",
                first.plannedReceiverObjectId()
                        != second.plannedReceiverObjectId());
    }

    /**
     * One map has one identity, however the activation reached it.
     *
     * <p>The region entry names a carrier nothing else can name.  It must
     * not compete with an access: a map reached by an access in one
     * activation and selected at entry in another would take an access name
     * once and an entry name the next time, and the two halves of one
     * location would never join.</p>
     */
    @Test
    public void anAccessOutranksTheRegionEntry() {
        SharedCarrier byAccessThenEntry = SharedCarrier.field(new Object(),
                "a.Key", "unplannedField", "J");
        byAccessThenEntry.recordConsumerAccess(
                new ConsumerAccessAnchor("<a.Key: long get()>", 1));
        byAccessThenEntry.recordEntryAnchor(
                new ConsumerAccessAnchor("<a.Manager: void sweep()>", 1));
        SharedCarrier byAccessOnly = SharedCarrier.field(new Object(),
                "a.Key", "unplannedField", "J");
        byAccessOnly.recordConsumerAccess(
                new ConsumerAccessAnchor("<a.Key: long get()>", 1));

        byAccessThenEntry.bindPlannedReceiver(task());
        byAccessOnly.bindPlannedReceiver(task());

        assertEquals("the entry must not rename an accessed location",
                byAccessOnly.plannedReceiverObjectId(),
                byAccessThenEntry.plannedReceiverObjectId());
    }

    /** With no access at all the entry still names it. */
    @Test
    public void theEntryNamesWhatNothingElseNames() {
        SharedCarrier carrier = SharedCarrier.field(new Object(),
                "a.Key", "unplannedField", "J");
        carrier.recordEntryAnchor(
                new ConsumerAccessAnchor("<a.Manager: void sweep()>", 1));
        carrier.bindPlannedReceiver(task());

        assertTrue(carrier.plannedReceiverObjectId() > 0L);
    }

    // ---------- plan and carrier harness ----------

    private static SharedCarrier carrier(Object owner, String site,
                                         int occurrence,
                                         ConcolicTaskPlan.RuntimeTask task) {
        SharedCarrier carrier = SharedCarrier.field(owner, OWNER, FIELD,
                DESCRIPTOR);
        carrier.recordConsumerAccess(
                new ConsumerAccessAnchor(site, occurrence));
        carrier.bindPlannedReceiver(task);
        return carrier;
    }

    /**
     * One activation that read {@code a.Key#expiry} on two instances at the
     * same site, the way a loop over a key collection does.
     */
    private static ConcolicTaskPlan.RuntimeTask task() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        encoded.addProperty("regionId", "REGION.1");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "nn0#epoch0");
        encoded.addProperty("occurrenceId", OCCURRENCE);
        encoded.addProperty("rootMethod", "<a.Manager: void sweep()>");
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "nn0#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        JsonArray inputActions = new JsonArray();
        inputActions.add(fieldAccess(101L, 1));
        inputActions.add(fieldAccess(202L, 2));
        encoded.add("inputActions", inputActions);
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        return new ConcolicTaskPlan.RuntimeTask(
                ExecutionTask.decode(encoded));
    }

    private static JsonObject fieldAccess(long receiverObjectId,
                                          int occurrence) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "sym.expiry." + occurrence);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature", SIGNATURE);
        action.addProperty("leafFieldSignature", SIGNATURE);
        action.addProperty("javaType", "long");
        action.addProperty("fieldReceiverObjectId", receiverObjectId);
        action.addProperty("siteId", READ_SITE);
        action.addProperty("staticAccessSiteId", READ_SITE);
        action.addProperty("accessorOccurrence", occurrence);
        action.addProperty("replayOccurrence", occurrence);
        JsonArray accessSites = new JsonArray();
        accessSites.add(READ_SITE);
        action.add("accessSites", accessSites);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add(FIELD);
        action.add("fieldPath", fieldPath);
        return action;
    }

    // ---------- published evidence harness ----------

    private static JsonObject summary(JsonObject... versions) {
        JsonObject summary = new JsonObject();
        summary.addProperty("occurrenceId", OCCURRENCE);
        JsonArray rows = new JsonArray();
        for (JsonObject version : versions) rows.add(version);
        JsonObject recorded = new JsonObject();
        recorded.add("versions", rows);
        summary.add(SharedStateEvidence.RECORDED_FIELD, recorded);
        return summary;
    }

    private static JsonObject version(String locationKey,
                                      SharedCarrier carrier) {
        JsonObject version = new JsonObject();
        version.addProperty("locationKey", locationKey);
        version.add("carrier", carrier.toJson());
        return version;
    }

    private static String locationKey(JsonObject summary, int index) {
        return summary.getAsJsonObject(SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(index).getAsJsonObject()
                .get("locationKey").getAsString();
    }
}
