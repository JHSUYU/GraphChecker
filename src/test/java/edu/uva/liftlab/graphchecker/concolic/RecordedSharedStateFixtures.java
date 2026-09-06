package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;


/**
 * Builders for the VM envelopes the recorded shared-state layer admits.
 *
 * <p>Every builder produces the shape the custom JDK serializes, so a test
 * that mutates one field is testing this codebase's admission rule against
 * the VM's own wire format rather than against a convenient stand-in.</p>
 */
final class RecordedSharedStateFixtures {

    /** The one named test source every fixture activation belongs to. */
    static final String TEST_SOURCE = "test-node#epoch0";

    private RecordedSharedStateFixtures() {
    }

    /** The activation identity of one region in these fixtures. */
    static String occurrenceOf(String regionId) {
        return TEST_SOURCE + "/region/" + regionId + "#1";
    }


    /** One complete evidence identity, taken at snapshot {@code ordinal}. */
    static RecordedEvidenceIdentity identity(String regionId, long ordinal) {
        return RecordedEvidenceIdentity.of("", "workload#1",
                "TASK." + regionId, occurrenceOf(regionId), TEST_SOURCE,
                ordinal);
    }

    static JsonObject symbol(String name) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", name);
        return expression;
    }

    static JsonObject sum(JsonElement left, JsonElement right) {
        return binary(left, "+", right);
    }

    static JsonObject binary(JsonElement left, String operator,
                             JsonElement right) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        expression.addProperty("_op", operator);
        expression.add("_left", left);
        expression.add("_right", right);
        return expression;
    }

    /**
     * One writer's recorded path guard: the branch condition that writer took.
     *
     * <p>A guard is a predicate, not a value, and the composer lowers it as
     * one. The fixture therefore records a real comparison rather than a bare
     * symbol, so a test of the guard's lowering is a test against the shape a
     * path condition actually has.</p>
     */
    static JsonObject guard(String name) {
        return binary(symbol(name), ">", constant(0));
    }

    /** A recorded writer guard no execution can satisfy. */
    static JsonObject unsatisfiableGuard() {
        return binary(constant(1), "==", constant(2));
    }

    static JsonObject version(long fieldVersionId, String regionId,
                              String taskId, JsonElement value,
                              JsonElement pathGuard) {
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", fieldVersionId);
        version.addProperty("versionKind", "WRITE");
        version.addProperty("writerContextId", 100L + fieldVersionId);
        version.addProperty("writerJavaThreadId", 200L + fieldVersionId);
        version.addProperty("writerStep", fieldVersionId);
        version.addProperty("regionId", regionId);
        version.addProperty("taskId", taskId);
        version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                TEST_SOURCE);
        version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                occurrenceOf(regionId));
        version.addProperty("volatileWrite", false);
        version.addProperty("fingerprintKind", "PRIMITIVE");
        version.addProperty("fingerprint", 10L);
        version.add("expression", value);
        version.add("pathGuard", pathGuard);
        return version;
    }

    static JsonObject read(long readEventId, String resolution, String reason,
                           long chosenFieldVersionId, int candidateCount) {
        JsonObject read = new JsonObject();
        read.addProperty("readEventId", readEventId);
        read.addProperty("readerContextId", 900L);
        read.addProperty("readerJavaThreadId", 901L);
        read.addProperty("regionId", "REGION.reader");
        read.addProperty(SharedStateEvidence.READER_SOURCE_KEY, TEST_SOURCE);
        read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                occurrenceOf("REGION.reader"));
        read.addProperty("resolution", resolution);
        read.addProperty("reason", reason);
        read.addProperty("chosenFieldVersionId", chosenFieldVersionId);
        read.addProperty("candidateCount", candidateCount);
        read.addProperty("observedFingerprintKind", "PRIMITIVE");
        read.addProperty("observedFingerprint", 10L);
        return read;
    }

    static JsonObject versionsEnvelope(long owner, int slot,
                                       JsonArray versions, JsonArray reads) {
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", owner);
        location.addProperty("slot", slot);
        location.addProperty("locationKind", "INSTANCE_FIELD");
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("kind",
                SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
        envelope.addProperty("selected", true);
        envelope.add("location", location);
        envelope.addProperty("writerSetComplete", true);
        envelope.add("versions", versions);
        envelope.add("reads", reads);
        return envelope;
    }

    /** Two competing writers of one location, and one read of it. */
    static JsonObject twoWriterEnvelope(String resolution, String reason,
                                        long chosen) {
        JsonArray versions = new JsonArray();
        versions.add(version(11L, "REGION.writerA", "TASK.a",
                sum(symbol("A"), constant(1)), null));
        versions.add(version(12L, "REGION.writerB", "TASK.b",
                sum(symbol("B"), constant(2)), guard("G")));
        JsonArray reads = new JsonArray();
        reads.add(read(21L, resolution, reason, chosen, 2));
        return versionsEnvelope(7L, 24, versions, reads);
    }

    static JsonObject constant(long value) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConSymbolExp");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", String.valueOf(value));
        return expression;
    }

    static JsonObject candidate(String selector, long fieldVersionId,
                                JsonElement value, JsonElement pathGuard,
                                long readEventId, long... competitors) {
        JsonObject candidate = new JsonObject();
        candidate.addProperty("selector", selector);
        candidate.addProperty("unknown", false);
        candidate.addProperty("fieldVersionId", fieldVersionId);
        candidate.addProperty("writerContextId", 100L + fieldVersionId);
        candidate.addProperty("writerJavaThreadId", 200L + fieldVersionId);
        candidate.addProperty("regionId", "REGION.writer");
        candidate.addProperty("taskId", "TASK.writer");
        candidate.addProperty("volatileWrite", false);
        candidate.add("expression", value);
        candidate.add("pathGuard", pathGuard);
        JsonArray constraints = new JsonArray();
        JsonObject cut = new JsonObject();
        cut.addProperty("kind", "WRITE_BEFORE_READ");
        cut.addProperty("beforeEventId", fieldVersionId);
        cut.addProperty("afterEventId", readEventId);
        constraints.add(cut);
        for (long competitor : competitors) {
            JsonObject outside = new JsonObject();
            outside.addProperty("kind", "OTHER_WRITE_OUTSIDE_CUT");
            outside.addProperty("otherEventId", competitor);
            outside.addProperty("selectedEventId", fieldVersionId);
            outside.addProperty("readEventId", readEventId);
            constraints.add(outside);
        }
        candidate.add("orderConstraints", constraints);
        return candidate;
    }

    static JsonObject unknownCandidate(long readEventId, String symbolName) {
        JsonObject candidate = new JsonObject();
        candidate.addProperty("selector",
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        candidate.addProperty("unknown", true);
        candidate.addProperty("fieldVersionId", 0L);
        candidate.addProperty("writerContextId", 0L);
        candidate.addProperty("writerJavaThreadId", 0L);
        candidate.addProperty("regionId", "");
        candidate.addProperty("taskId", "");
        candidate.addProperty("volatileWrite", false);
        candidate.add("expression", symbol(symbolName));
        candidate.add("pathGuard", null);
        JsonArray constraints = new JsonArray();
        JsonObject cut = new JsonObject();
        cut.addProperty("kind", "UNKNOWN_WRITE_BEFORE_READ");
        cut.addProperty("readEventId", readEventId);
        constraints.add(cut);
        candidate.add("orderConstraints", constraints);
        return candidate;
    }

    /**
     * The guarded node the VM attaches to an undecided read: two competing
     * writers and the unconditional unknown-writer arm.
     */
    static JsonObject guardedRead(long readEventId, long owner, int slot) {
        JsonArray candidates = new JsonArray();
        candidates.add(candidate("rf1", 11L, sum(symbol("A"), constant(1)),
                null, readEventId, 12L));
        candidates.add(candidate("rf2", 12L, sum(symbol("B"), constant(2)),
                guard("G"), readEventId, 11L));
        candidates.add(unknownCandidate(readEventId,
                "M_I_unknownWriter_" + owner + "_" + slot + "_r"
                        + readEventId));
        return guardedRead(readEventId, owner, slot, candidates);
    }

    static JsonObject guardedRead(long readEventId, long owner, int slot,
                                  JsonArray candidates) {
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", owner);
        location.addProperty("slot", slot);
        location.addProperty("locationKind", "INSTANCE_FIELD");
        JsonArray selectors = new JsonArray();
        for (JsonElement element : candidates) {
            selectors.add(element.getAsJsonObject().get("selector")
                    .getAsString());
        }
        JsonObject node = new JsonObject();
        node.addProperty("_type", SharedStateEvidence.GUARDED_READ_TYPE);
        node.addProperty("_java_type", "I");
        node.addProperty("resolution",
                SharedStateEvidence.RESOLUTION_GUARDED);
        node.addProperty("reason", "AMBIGUOUS_WRITERS");
        node.addProperty("expressionAuthority",
                SharedStateEvidence.GUARDED_READ_AUTHORITY);
        node.addProperty("readEventId", readEventId);
        node.add("location", location);
        node.addProperty("writerSetComplete", true);
        node.add("exactlyOne", selectors);
        node.add("candidates", candidates);
        node.add("ite", selectionTerm(candidates, 0));
        return node;
    }

    private static JsonElement selectionTerm(JsonArray candidates,
                                             int index) {
        JsonObject candidate = candidates.get(index).getAsJsonObject();
        if (index + 1 == candidates.size()) {
            return candidate.get("expression");
        }
        JsonObject ite = new JsonObject();
        ite.addProperty("_type", "IteExpression");
        ite.addProperty("selector",
                candidate.get("selector").getAsString());
        ite.add("then", candidate.get("expression"));
        ite.add("else", selectionTerm(candidates, index + 1));
        return ite;
    }

    /**
     * The carrier join the runtime records on a versions read-out: the VM
     * addresses a location by its own identity, and only the call site that
     * selected it knows the declared Java field.
     */
    static JsonObject carrier(String field, String descriptor) {
        int separator = field.indexOf('#');
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", "DECLARED_FIELD");
        carrier.addProperty("declaringClass", field.substring(0, separator));
        carrier.addProperty("fieldName", field.substring(separator + 1));
        carrier.addProperty("descriptor", descriptor);
        carrier.addProperty("index", -1);
        carrier.addProperty("fieldKey", field + ":" + descriptor);
        return carrier;
    }

    /** One admitted versions record, joined to its declared field. */
    static JsonObject versionsRecord(JsonObject envelope, String field) {
        return versionsRecord(envelope, field, 1L);
    }

    /** The same record, read back at snapshot {@code ordinal}. */
    static JsonObject versionsRecord(JsonObject envelope, String field,
                                     long ordinal) {
        JsonObject record = SharedStateEvidence.versionsRecord(
                SharedStateEvidence.locationKey(envelope), envelope,
                identity("REGION.reader", ordinal));
        record.add("carrier", carrier(field, "I"));
        return record;
    }


    /** One {@code recordedSharedState} member of an execution. */
    static JsonObject recordedMember(JsonObject versionsEnvelope,
                                     JsonObject ledgerEnvelope,
                                     String field) {
        return SharedStateEvidence.recorded(
                java.util.Collections.singletonList(
                        versionsRecord(versionsEnvelope, field)),
                ledgerEnvelope == null ? null
                        : SharedStateEvidence.ledgerRecord(ledgerEnvelope,
                        identity("REGION.reader", 1L)));
    }

    static JsonObject event(long eventId, String eventKind, long contextId,
                            String regionId, long objectSymRid) {
        JsonObject event = event(eventId, eventKind, contextId, regionId);
        event.addProperty("objectSymRid", objectSymRid);
        return event;
    }

    static JsonObject event(long eventId, String eventKind, long contextId,
                            String regionId) {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", eventId);
        event.addProperty("eventKind", eventKind);
        event.addProperty("contextId", contextId);
        event.addProperty("javaThreadId", contextId + 500L);
        event.addProperty("step", eventId);
        event.addProperty("objectSymRid", 7L);
        event.addProperty("slot", 24);
        event.addProperty("regionId", regionId);
        event.addProperty("detail", "");
        return event;
    }

    static JsonObject edge(long before, long after, String edgeKind) {
        JsonObject edge = new JsonObject();
        edge.addProperty("beforeEventId", before);
        edge.addProperty("afterEventId", after);
        edge.addProperty("edgeKind", edgeKind);
        return edge;
    }

    static JsonObject ledgerEnvelope(JsonArray events, JsonArray order) {
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("kind",
                SharedStateEvidence.LEDGER_ENVELOPE_KIND);
        envelope.addProperty("open", true);
        envelope.addProperty("recording", true);
        envelope.addProperty("truncated", false);
        envelope.addProperty("domainSaturated", false);
        envelope.addProperty("partialOrder", true);
        envelope.addProperty("acyclic", true);
        envelope.add("events", events);
        envelope.add("order", order);
        return envelope;
    }

    /**
     * Two writes, one read, and an explicit synchronization edge between the
     * writes.
     */
    static JsonObject twoWriterLedger() {
        JsonArray events = new JsonArray();
        events.add(event(11L, "FIELD_WRITE", 101L, "REGION.writerA"));
        events.add(event(12L, "FIELD_WRITE", 102L, "REGION.writerB"));
        events.add(event(21L, "FIELD_READ", 103L, "REGION.reader"));
        JsonArray order = new JsonArray();
        order.add(edge(11L, 12L, "SYNCHRONIZATION"));
        return ledgerEnvelope(events, order);
    }



    // ----- composed goldens ----------------------------------------------
    //
    // The envelopes above describe what the VM records; these run them all
    // the way through the real composer, so a downstream artifact is checked
    // against a formula that was actually emitted rather than against a
    // hand-written stand-in of one.

    static final String TARGET_OCCURRENCE = "REGION.0@Test#call30";
    static final String PRODUCER_OCCURRENCE = "REGION.1@Test#call20";
    static final String COMPOSED_SOURCE_KEY = "TEST_DRIVER/test#epoch0";















}
