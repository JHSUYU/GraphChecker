package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.constant;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.read;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.siteOf;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.symbol;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.version;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.versionsEnvelope;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The recorded answer to "which write did this read take", what it refuses to
 * answer, and what it does to the trace's candidate writers.
 *
 * <p>The decisive property is the third state. An index that only said "yes"
 * or "no" would force a caller to treat "the session never watched this
 * location" as "the session says no", which is how an unwatched field ends up
 * looking like a proven one.</p>
 */
public class RecordedReadFromTest {

    private static final String FIELD = "example.State#value";
    private static final String WRITER_A = "REGION.writerA";
    private static final String WRITER_B = "REGION.writerB";
    private static final String WRITER_C = "REGION.writerC";
    private static final String READER = "REGION.reader";

    @Test
    public void anExactReadDecidesItsOwnReaderAndNoOther() {
        RecordedReadFrom index = index(store(
                SharedStateEvidence.RESOLUTION_EXACT, "SYNC_ORDERED", 11L));

        assertEquals(RecordedReadFrom.Decision.RECORDED_EXACT,
                index.decide(FIELD, siteOf(WRITER_A), siteOf(READER)));
        // The other tracked writer is not the one this read took.
        assertEquals(RecordedReadFrom.Decision.RECORDED_EXCLUDED,
                index.decide(FIELD, siteOf(WRITER_B), siteOf(READER)));
        // A reader with no recorded read of this location is not decided by
        // another reader's proof.
        assertEquals(RecordedReadFrom.Decision.NO_RECORDED_EVIDENCE,
                index.decide(FIELD, siteOf(WRITER_A), siteOf("REGION.other")));
        // A static region is not an address.  It resolves to the one
        // activation this run recorded for it, and to nothing otherwise.
        assertEquals(siteOf(WRITER_A), index.siteOfRegion(FIELD, WRITER_A));
        assertEquals("", index.siteOfRegion(FIELD, "REGION.never"));
        assertEquals(RecordedReadFrom.Decision.NO_RECORDED_EVIDENCE,
                index.decide(FIELD, WRITER_A, READER));

        RecordedReadFrom guardedIndex = index(store(
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L));

        assertEquals(RecordedReadFrom.Decision.RECORDED_GUARDED_CANDIDATE,
                guardedIndex.decide(FIELD, siteOf(WRITER_A), siteOf(READER)));
        assertEquals(RecordedReadFrom.Decision.RECORDED_GUARDED_CANDIDATE,
                guardedIndex.decide(FIELD, siteOf(WRITER_B), siteOf(READER)));
        assertEquals(RecordedReadFrom.Decision.RECORDED_EXCLUDED,
                guardedIndex.decide(FIELD, siteOf("REGION.neverWrote"),
                        siteOf(READER)));

        // Folded from the Phase 2 field acceptance: two writers of one
        // equal-valued location bind only by VM evidence, and the binding
        // follows the observed order without the reader's own relation
        // changing.  The two runs below start from byte-identical candidate
        // edges - all the trace can say is that either writer could have
        // reached the read - and end up bound to different writers.
        JsonArray firstRun = candidateEdges();
        index(store(SharedStateEvidence.RESOLUTION_EXACT, "SYNC_ORDERED",
                11L)).resolve(rows(firstRun));
        assertEquals(RecordedReadFrom.PROVENANCE_EXACT,
                provenance(firstRun, 0));
        assertEquals(RecordedReadFrom.PROVENANCE_EXCLUDED,
                provenance(firstRun, 1));

        JsonArray secondRun = candidateEdges();
        index(store(SharedStateEvidence.RESOLUTION_EXACT, "SYNC_ORDERED",
                12L)).resolve(rows(secondRun));
        assertEquals(RecordedReadFrom.PROVENANCE_EXCLUDED,
                provenance(secondRun, 0));
        assertEquals(RecordedReadFrom.PROVENANCE_EXACT,
                provenance(secondRun, 1));
        // Only the binding moved.  Everything the reader's local relation is
        // stated over - the ports, the field, the endpoints - is untouched,
        // which is what makes the summary reusable across the two orders.
        for (int edge = 0; edge < 2; edge++) {
            JsonObject before = firstRun.get(edge).getAsJsonObject();
            JsonObject after = secondRun.get(edge).getAsJsonObject();
            for (String member : new String[]{"edgeId", "fromRegion",
                    "toRegion", "fromOccurrenceId", "toOccurrenceId",
                    "toPort", RecordedReadFrom.EDGE_FIELD,
                    RecordedReadFrom.EDGE_SOURCE_KEY}) {
                assertEquals(member, before.get(member), after.get(member));
            }
        }

        // A writer the run observed but could not address - an unselected,
        // native or evicted one - is not a narrower choice.  It leaves the
        // read able to have taken a write no candidate stands for, so the
        // unknown arm survives and says so by name.
        JsonObject evicted = store(SharedStateEvidence.RESOLUTION_EXACT,
                "SYNC_ORDERED", 11L);
        evicted.getAsJsonArray("versions").get(1).getAsJsonObject()
                .remove(SharedStateEvidence.WRITER_OCCURRENCE_ID);
        RecordedReadFrom partial = index(evicted);
        assertFalse(partial.writerSetComplete(FIELD, siteOf(READER)));
        JsonArray evictedRun = candidateEdges();
        partial.resolve(rows(evictedRun));
        assertEquals(SharedStateEvidence.UNKNOWN_WRITER_SELECTOR,
                evictedRun.get(0).getAsJsonObject()
                        .get(RecordedReadFrom.EDGE_UNKNOWN_ARM).getAsString());

        // Unresolved candidates and retained unknown arms are two different
        // findings, and the coverage stream keeps them apart.
        JsonArray unresolved = candidateEdges();
        List<JsonObject> gaps = RecordedReadFrom.provenanceGaps(
                Arrays.asList(evictedRun.get(0).getAsJsonObject(),
                        unresolved.get(0).getAsJsonObject(),
                        unresolved.get(1).getAsJsonObject()));
        assertEquals(2, gaps.size());
        for (JsonObject gap : gaps) {
            assertTrue(SharedStateEvidence.isGap(gap));
        }
        assertEquals("SHARED_STATE_UNKNOWN_WRITER",
                gaps.get(0).get("reason").getAsString());
        assertEquals("SHARED_STATE_NOT_SELECTED",
                gaps.get(1).get("reason").getAsString());
        assertTrue(gaps.get(1).get("detail").getAsString()
                .contains("candidate writers stay unresolved"));
    }

    /**
     * README {@code STATE-1}: one declared field is a name, not a location.
     *
     * <p>Two objects of one class hold two stores under the same
     * {@code declaringClass#fieldName}. Folding them into one entry is how a
     * DataNode's read gets answered by a NameNode's write, so the index keeps
     * them apart by the VM's own location key: a writer of the other object
     * is excluded, and a reader that read both is decided by neither.</p>
     */
    @Test
    public void oneDeclaredFieldOnTwoObjectsIsTwoLocations() {
        JsonObject read = store(SharedStateEvidence.RESOLUTION_GUARDED,
                "AMBIGUOUS_WRITERS", 0L);
        JsonObject elsewhere = otherObjectStore(new JsonArray());
        RecordedReadFrom index = index(read, elsewhere);

        // The reader read one object.  Its own writers stay admissible.
        assertEquals(RecordedReadFrom.Decision.RECORDED_GUARDED_CANDIDATE,
                index.decide(FIELD, siteOf(WRITER_A), siteOf(READER)));
        // The other object's writer of the same declared field is not one of
        // them, however equal its value or its name.
        assertEquals(RecordedReadFrom.Decision.RECORDED_EXCLUDED,
                index.decide(FIELD, siteOf(WRITER_C), siteOf(READER)));

        // A reader that read both objects under one field name is addressed
        // by neither store, so nothing is decided and the trace's candidates
        // survive under their gap.
        JsonArray bothReads = new JsonArray();
        bothReads.add(read(31L, SharedStateEvidence.RESOLUTION_GUARDED,
                "AMBIGUOUS_WRITERS", 0L, 1));
        RecordedReadFrom ambiguous = index(read,
                otherObjectStore(bothReads));
        assertEquals(RecordedReadFrom.Decision.NO_RECORDED_EVIDENCE,
                ambiguous.decide(FIELD, siteOf(WRITER_A), siteOf(READER)));
        assertEquals("", ambiguous.locationKey(FIELD, siteOf(READER)));
        assertFalse(ambiguous.writerSetComplete(FIELD, siteOf(READER)));
    }

    @Test
    public void aPreselectedWriterEdgeIsNoLongerAdmitted() {
        // Wave 3 B: a read chooses among every recorded version of its
        // location, so nothing may hand it one edge in advance.  An envelope
        // that still names one is stating a narrowing this model dropped.
        JsonObject envelope = store(SharedStateEvidence.RESOLUTION_EXACT,
                "UNIQUE_VERSION", 11L);
        assertEquals("", SharedStateEvidence.versionsFault(envelope));
        JsonObject preselected = envelope.deepCopy();
        preselected.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty("selectedEdgeId", "RF.selected");
        assertTrue(SharedStateEvidence.versionsFault(preselected)
                .contains("names a preselected writer edge"));

        // Every candidate edge out of the recorded writer is now decided the
        // same way, by occurrence, whatever edge id it carries.
        RecordedReadFrom index = index(envelope);
        JsonArray candidates = new JsonArray();
        for (String edgeId : new String[]{"RF.earlier", "RF.selected",
                "RF.later"}) {
            JsonObject edge = candidateEdge(WRITER_A);
            edge.addProperty("edgeId", edgeId);
            candidates.add(edge);
        }
        assertEquals(3, index.resolve(rows(candidates)));
        for (int index0 = 0; index0 < 3; index0++) {
            assertEquals(RecordedReadFrom.PROVENANCE_EXACT,
                    provenance(candidates, index0));
        }
        assertEquals(RecordedReadFrom.Decision.RECORDED_EXACT,
                index.decide(FIELD, siteOf(WRITER_A), siteOf(READER)));
    }

    /** A second object holding the same declared field. */
    private static JsonObject otherObjectStore(JsonArray reads) {
        JsonArray versions = new JsonArray();
        versions.add(version(31L, WRITER_C, "TASK.c", constant(2),
                SharedStateEvidence.emptyConjunction()));
        return versionsEnvelope(9L, 24, versions, reads);
    }

    /** The two candidate edges trace refinement retains for this location. */
    private static JsonArray candidateEdges() {
        JsonArray edges = new JsonArray();
        edges.add(candidateEdge(WRITER_A));
        edges.add(candidateEdge(WRITER_B));
        return edges;
    }

    private static JsonObject candidateEdge(String writerRegion) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "RF." + writerRegion);
        edge.addProperty("fromRegion", writerRegion);
        edge.addProperty("toRegion", READER);
        edge.addProperty("fromOccurrenceId",
                RecordedSharedStateFixtures.occurrenceOf(writerRegion));
        edge.addProperty("toOccurrenceId",
                RecordedSharedStateFixtures.occurrenceOf(READER));
        edge.addProperty("toPort", READER + ".in.value");
        edge.addProperty(RecordedReadFrom.EDGE_FIELD, FIELD);
        edge.addProperty(RecordedReadFrom.EDGE_SOURCE_KEY,
                RecordedSharedStateFixtures.TEST_SOURCE);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE_GAP,
                "SHARED_STATE_NOT_SELECTED");
        return edge;
    }

    private static List<JsonObject> rows(JsonArray edges) {
        List<JsonObject> rows = new java.util.ArrayList<>();
        for (com.google.gson.JsonElement edge : edges) {
            rows.add(edge.getAsJsonObject());
        }
        return rows;
    }

    private static String provenance(JsonArray edges, int index) {
        return edges.get(index).getAsJsonObject()
                .get(RecordedReadFrom.EDGE_PROVENANCE).getAsString();
    }

    /** Two writer regions and one read of one location. */
    private static JsonObject store(String resolution, String reason,
                                    long chosen) {
        JsonArray versions = new JsonArray();
        versions.add(version(11L, WRITER_A, "TASK.a", symbol("A"),
                SharedStateEvidence.emptyConjunction()));
        versions.add(version(12L, WRITER_B, "TASK.b", constant(2),
                SharedStateEvidence.emptyConjunction()));
        JsonArray reads = new JsonArray();
        reads.add(read(21L, resolution, reason, chosen, 2));
        return versionsEnvelope(7L, 24, versions, reads);
    }

    private static JsonObject carrierRecord(JsonObject envelope) {
        JsonObject record = SharedStateEvidence.versionsRecord(
                SharedStateEvidence.locationKey(envelope), envelope,
                RecordedSharedStateFixtures.identity(READER, 1L));
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", "DECLARED_FIELD");
        carrier.addProperty("declaringClass", "example.State");
        carrier.addProperty("fieldName", "value");
        carrier.addProperty("descriptor", "I");
        carrier.addProperty("fieldKey", "example.State#value:I");
        record.add("carrier", carrier);
        return record;
    }

    private static RecordedReadFrom index(JsonObject... envelopes) {
        List<JsonObject> records = new java.util.ArrayList<>();
        for (JsonObject envelope : envelopes) {
            records.add(carrierRecord(envelope));
        }
        return RecordedReadFrom.index(Collections.singletonList(
                SharedStateEvidence.recorded(records, null)));
    }
}
