package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The write log, read out by object.
 *
 * <p>A location is tracked because a symbolic value reached it, and the VM
 * files it under the identity of the object actually written.  So the runtime
 * names nothing: it publishes the envelope the VM hands back, keyed by the
 * location the VM states, which is the key the read nodes carry.</p>
 */
public class TrackedLocationWriteLogTest {

    /** The published record is the location, its versions, and no carrier. */
    @Test
    public void theRecordIsNamedByTheObjectAndCarriesNoCarrier() {
        JsonObject published = SharedStateCapture.reduceWriteLogForTest(
                SharedStateEvidence.versionsRecord("MAP_STATE/24#-3",
                        envelope("MAP_STATE", 24, -3,
                                new int[] {39, 41, 44}), null));

        assertEquals("MAP_STATE/24#-3",
                published.get("locationKey").getAsString());
        assertFalse("no carrier names this location any more",
                published.has("carrier"));
        JsonObject envelope = published.getAsJsonObject("envelope");
        assertTrue("the object identity is stated", envelope.has("location"));
        assertEquals("the session the clock belongs to is stated", 1,
                envelope.get("sessionId").getAsInt());
        JsonArray versions = envelope.getAsJsonArray("versions");
        assertEquals(3, versions.size());
        long previous = -1L;
        for (int index = 0; index < versions.size(); index++) {
            JsonObject version = versions.get(index).getAsJsonObject();
            assertEquals("version id, kind and expression, and no more", 3,
                    version.size());
            long clock = version.get("fieldVersionId").getAsLong();
            assertTrue("the clock increases with the writes",
                    clock > previous);
            previous = clock;
        }
    }

    /** A container whose base the VM stated is admitted. */
    @Test
    public void aContainerThatStatesItsBaseIsAdmitted() {
        assertEquals("", SharedStateEvidence.versionsFault(
                envelope("MAP_STATE", 24, -3, new int[] {39, 41})));
    }

    /**
     * A container whose base the VM could not state is refused, by name.
     *
     * <p>A container relation resolves as its base plus the mutation chain,
     * so a base nobody stated leaves every read of that container standing on
     * nothing.  The class travels in the fault because naming it is what gets
     * it walked.</p>
     */
    @Test
    public void aContainerWithNoStatedBaseIsRefused() {
        JsonObject envelope = envelope("MAP_STATE", 24, -3,
                new int[] {39, 41});
        JsonObject initial = envelope.getAsJsonArray("versions").get(0)
                .getAsJsonObject();
        JsonObject snapshot = new JsonObject();
        snapshot.addProperty("stated", false);
        snapshot.addProperty("unsupportedClass",
                "org.apache.hadoop.util.LightWeightGSet");
        initial.add("initialSnapshot", snapshot);

        String fault = SharedStateEvidence.versionsFault(envelope);

        assertTrue(fault, SharedStateEvidence.containerBaseUnstatedFault(
                fault));
        assertTrue(fault, fault.contains("LightWeightGSet"));
        assertEquals("SHARED_STATE_CONTAINER_BASE_UNSTATED",
                SharedStateEvidence.reason(
                        SharedStateEvidence.CONTAINER_BASE_UNSTATED));
    }

    /** An INITIAL with no snapshot member at all is refused the same way. */
    @Test
    public void aContainerWithNoSnapshotMemberIsRefused() {
        JsonObject envelope = envelope("MAP_STATE", 24, -3,
                new int[] {39, 41});
        envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                .remove("initialSnapshot");

        assertTrue(SharedStateEvidence.containerBaseUnstatedFault(
                SharedStateEvidence.versionsFault(envelope)));
    }

    /** A scalar has no container base and is not asked for one. */
    @Test
    public void aScalarIsNotAskedForAContainerBase() {
        JsonObject envelope = envelope("INSTANCE_FIELD", 9, 56,
                new int[] {39, 41});
        envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                .remove("initialSnapshot");

        assertEquals("", SharedStateEvidence.versionsFault(envelope));
    }

    // ---------- the envelope the VM emits per tracked location ----------

    private static JsonObject envelope(String kind, long ownerSymRid,
                                       int slot, int[] fieldVersionIds) {
        JsonObject location = new JsonObject();
        location.addProperty("locationKind", kind);
        location.addProperty("ownerSymRid", ownerSymRid);
        location.addProperty("slot", slot);
        JsonArray versions = new JsonArray();
        for (int index = 0; index < fieldVersionIds.length; index++) {
            JsonObject version = new JsonObject();
            version.addProperty("fieldVersionId", fieldVersionIds[index]);
            version.addProperty("versionKind", index == 0 ? "INITIAL"
                    : "MAP_STATE".equals(kind) ? "STATE_PUT" : "WRITE");
            version.addProperty("regionEnterEventId", 2);
            version.addProperty("writerContextId", 2);
            version.addProperty("regionId", "REGION.r");
            version.addProperty("taskId", "TASK.t");
            version.add("pathGuard", JsonNull.INSTANCE);
            if (index == 0) {
                JsonObject snapshot = new JsonObject();
                snapshot.addProperty("entries", 2);
                snapshot.addProperty("truncated", false);
                version.add("initialSnapshot", snapshot);
            }
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConstExpr");
            expression.addProperty("value", index);
            version.add("expression", expression);
            versions.add(version);
        }
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("kind", "SHARED_FIELD_VERSIONS");
        envelope.addProperty("sessionId", 1);
        envelope.addProperty("selected", true);
        envelope.addProperty("writerSetComplete", true);
        envelope.addProperty("serializationTruncated", false);
        envelope.addProperty("readLogTruncated", false);
        envelope.add("location", location);
        envelope.add("versions", versions);
        envelope.add("reads", new JsonArray());
        return envelope;
    }
}
