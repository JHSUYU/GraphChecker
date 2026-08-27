package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

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

    /** The cross-run address of one region's fixture activation. */
    static String siteOf(String regionId) {
        return RecordedEvidenceIdentity.siteKey(occurrenceOf(regionId));
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

    /** One summary row carrying an execution's recorded shared state. */
    static JsonObject recordedRow(JsonObject versionsEnvelope,
                                  JsonObject ledgerEnvelope, String field) {
        JsonObject row = new JsonObject();
        row.add(SharedStateEvidence.RECORDED_FIELD,
                recordedMember(versionsEnvelope, ledgerEnvelope, field));
        return row;
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

    /**
     * A recorded session whose single row carries a guarded read over the
     * two-writer ledger, with each candidate attributed to its writer region.
     */
    static RecordedSessionModel selectedReadCutModel() {
        JsonObject envelope = twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = guardedRead(21L, 7L, 24);
        // The recorded term's own writer regions, so the gate's cross-run key
        // names the regions the version store published from.
        JsonArray candidates = guarded.getAsJsonArray("candidates");
        candidates.get(0).getAsJsonObject()
                .addProperty("regionId", "REGION.writerA");
        candidates.get(1).getAsJsonObject()
                .addProperty("regionId", "REGION.writerB");
        SharedStateEvidence.normalizeGuards(guarded);
        envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                .add("expression", guarded);
        return RecordedSessionModel.of(
                java.util.Collections.singletonList(recordedRow(envelope,
                        twoWriterLedger(), "example.State#value")),
                null, "REGION.reader");
    }

    /** The read-cut payload a query carries, built from recorded evidence. */
    static JsonObject selectedReadCutQuery() {
        return selectedReadCutModel().queryPayload();
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

    /**
     * One undecided read of two competing writers, composed.
     *
     * <p>Its formula carries three read-from arms - two recorded writers and
     * the unconditional unknown one - the consumer port binding that hands the
     * target that value, and the two-writer ledger's own order.</p>
     */
    static ConcolicSmtComposer.Result composedGuardedGolden(Path directory)
            throws Exception {
        JsonObject edge = binding("EDGE.GUARDED", "REGION.1.out.0",
                "REGION.0.in.0");
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        edge.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        edge.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        JsonObject envelope = twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L);
        envelope.getAsJsonArray("reads").get(0).getAsJsonObject()
                .addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                        TARGET_OCCURRENCE);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = guardedRead(21L, 7L, 24);
        SharedStateEvidence.normalizeGuards(guarded);
        RelationSummary producer = withRecorded(
                producerSummary("GUARDED", edge), envelope,
                twoWriterLedger());
        return compose(directory, producer,
                binary(guarded, "==", constant(1)), edge);
    }

    /**
     * One proven read-from beside one candidate nothing decided, composed.
     *
     * <p>The VM named the writer, so the formula holds a direct equality and
     * the recorded {@code write &lt; read} order beside it. The second trace
     * edge into the same consumer port is resolved and never lowered: it stays
     * a candidate, which is the fifth evidence state the drawing has to be
     * able to show.</p>
     */
    static ConcolicSmtComposer.Result composedExactGolden(Path directory)
            throws Exception {
        JsonObject edge = binding("EDGE.EXACT", "REGION.1.out.0",
                "REGION.0.in.0");
        edge.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_EXACT);
        edge.addProperty("fieldVersionId", 11);
        edge.addProperty("readEventId", 21);
        edge.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        JsonObject competing = binding("EDGE.COMPETING", "REGION.1.out.1",
                "REGION.0.in.0");
        JsonObject envelope = twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_EXACT, "UNIQUE_VERSION", 11L);
        JsonObject read = envelope.getAsJsonArray("reads").get(0)
                .getAsJsonObject();
        read.addProperty("regionId", "REGION.0");
        read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                TARGET_OCCURRENCE);
        SharedStateEvidence.normalizeGuards(envelope);
        RelationSummary producer = withRecorded(withCompetingOutput(
                producerSummary("EXACT", edge, competing)), envelope,
                twoWriterLedger());
        return compose(directory, producer,
                binary(reference("REGION.0.in.0"), "==", constant(10)),
                Arrays.asList(edge, competing),
                Arrays.asList(region("REGION.0", true, false),
                        producerRegion()));
    }

    /** A second producer output, so the competing candidate is observable. */
    private static RelationSummary withCompetingOutput(
            RelationSummary summary) {
        JsonObject row = summary.toJson();
        OutputClosureContract second = OutputClosureCodec.singleton(
                "REL.REGION.1", "REGION.1",
                java.util.Collections.singletonList("REGION.1.out.1"),
                "REGION.1.out.1", "<Test: int competing>", "REGION_OUTPUT",
                "int", outputSlice("REGION.1.out.1",
                        "<Test: int competing>"));
        OutputClosureCodec.writeTo(row, OutputClosureCodec.merge(
                Arrays.asList(OutputClosureCodec.decode(row), second)));
        row.getAsJsonObject("regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject().getAsJsonObject("outputExpressions")
                .add("REGION.1.out.1", constant(20));
        return RelationSummary.decode(row);
    }

    private static JsonObject producerRegion() {
        JsonObject producer = region("REGION.1", false, true);
        producer.getAsJsonArray("outputs").add(port("REGION.1.out.1",
                "competing"));
        return producer;
    }

    private static RelationSummary withRecorded(RelationSummary summary,
                                                JsonObject envelope,
                                                JsonObject ledger) {
        JsonObject row = summary.toJson();
        row.add(SharedStateEvidence.RECORDED_FIELD,
                recordedMember(envelope, ledger, "example.State#value"));
        return RelationSummary.decode(row);
    }

    private static JsonObject outputSlice(String port, String cell) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        JsonArray inputs = new JsonArray();
        inputs.add("REGION.1.in.0");
        slice.add("inputPorts", inputs);
        for (String member : new String[]{"sites", "staticSites", "methods",
                "causalEdgeIds", "captureBindings", "captureBindingIssues"}) {
            slice.add(member, new JsonArray());
        }
        return slice;
    }

    /** The one upstream relation these goldens compose against. */
    private static RelationSummary producerSummary(String id,
                                                   JsonObject... edges) {
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL.REGION.1", "REGION.1",
                java.util.Collections.singletonList("REGION.1.out.0"),
                "REGION.1.out.0", "<Test: int output>", "REGION_OUTPUT",
                "int", outputSlice("REGION.1.out.0", "<Test: int output>"));
        JsonObject row = new JsonObject();
        row.addProperty("summaryId", "SUMMARY." + id);
        row.addProperty("sourceKey", COMPOSED_SOURCE_KEY);
        row.addProperty("occurrenceId", PRODUCER_OCCURRENCE);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(row);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray bindings = new JsonArray();
        for (JsonObject edge : edges) bindings.add(edge.deepCopy());
        row.add("edgeBindings", bindings);
        JsonObject path = new JsonObject();
        path.addProperty("caseId", "CASE." + id);
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        path.addProperty("sourceTaskId", "TASK." + id);
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", new JsonArray());
        path.add("guard", guard);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.1.out.0", constant(10));
        path.add("outputExpressions", outputs);
        JsonArray cases = new JsonArray();
        cases.add(path);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.add("cases", cases);
        row.add("regionRelation", relation);
        row.addProperty("relationallyComplete", true);
        return RelationSummary.decode(row);
    }

    private static ConcolicSmtComposer.Result compose(
            Path directory, RelationSummary producer,
            JsonObject targetPredicate, JsonObject firstHop)
            throws Exception {
        return compose(directory, producer, targetPredicate,
                Collections.singletonList(firstHop),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", false, true)));
    }

    private static ConcolicSmtComposer.Result compose(
            Path directory, RelationSummary producer,
            JsonObject targetPredicate, List<JsonObject> firstHops,
            List<JsonObject> regions) throws Exception {
        Files.createDirectories(directory);
        Path fatal = directory.resolve("fatal.jsonl");
        Path summaries = directory.resolve("summaries.jsonl");
        Path plan = directory.resolve("runtime_plan.jsonl");
        Path output = directory.resolve("candidate.smt2");
        Path manifest = directory.resolve("composed_smt_manifest.json");
        write(fatal, fatalQuery(targetPredicate, firstHops) + "\n");
        write(summaries, producer.toJson() + "\n");
        write(plan, RuntimePlanArtifact.encode(
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList(), regions));
        return ConcolicSmtComposer.compose(
                ConcolicSmtComposer.Arguments.parse(new String[]{
                        "--fatal-query", fatal.toString(),
                        "--summaries", summaries.toString(),
                        "--runtime-plan", plan.toString(),
                        "--output", output.toString(),
                        "--manifest", manifest.toString(),
                        "--fatal-region", "REGION.0",
                        "--occurrence-id", TARGET_OCCURRENCE}));
    }

    private static JsonObject fatalQuery(JsonObject targetPredicate,
                                         List<JsonObject> firstHops) {
        JsonObject fatal = new JsonObject();
        fatal.addProperty("schemaVersion",
                TargetReachPathQueryBuilder.SCHEMA_VERSION);
        fatal.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        fatal.addProperty("queryKey", "QUERY.RECORDED.SHARED.STATE");
        fatal.addProperty("regionId", "REGION.0");
        fatal.addProperty("occurrenceId", TARGET_OCCURRENCE);
        fatal.addProperty("targetSiteId", "<Test: void consume()>#u1");
        fatal.addProperty("targetOccurrence", 1);
        fatal.addProperty("requiredTakenOutcome", false);
        fatal.addProperty("constraintAuthority", "RECORDED_TARGET_PREFIX_V1");
        JsonArray constraints = new JsonArray();
        constraints.add(targetPredicate);
        JsonObject path = new JsonObject();
        path.add("constraints", constraints);
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        path.addProperty("desiredTakenOutcome", false);
        path.addProperty(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.SOURCE_TARGET_REACH_EVENT);
        path.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder.SOURCE_FATAL_BRANCH_AUTHORITY);
        JsonObject targetReach = new JsonObject();
        targetReach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        targetReach.addProperty("siteId", "<Test: void consume()>#u1");
        targetReach.addProperty("occurrence", 1);
        targetReach.addProperty("outcome", true);
        path.add(PathObservation.TargetReachEvent.FIELD, targetReach);
        JsonArray paths = new JsonArray();
        paths.add(path);
        fatal.add("paths", paths);
        fatal.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization", "IDENTITY");
        BranchWitness witness = BranchWitness.vmPc(
                "<Test: void consume()>#u1", "<Test: void consume()>", 1, 1,
                true, BranchPredicateAlgebra.complement(targetPredicate),
                0, metadata);
        path.add(TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS,
                witness.toJson());
        fatal.add("seedReplayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), witness).toJson());
        LoopBoundPolicy.cfgBackedges(8).writeTo(fatal);
        JsonArray selectedTargetBindings = new JsonArray();
        for (JsonObject firstHop : firstHops) {
            selectedTargetBindings.add(firstHop.deepCopy());
        }
        fatal.add("selectedTargetBindings", selectedTargetBindings);
        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", TARGET_OCCURRENCE);
        fatal.add("symbolicContext", context);
        return fatal;
    }

    private static JsonObject binding(String edgeId, String fromPort,
                                      String toPort) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromRegion", "REGION.1");
        binding.addProperty("toRegion", "REGION.0");
        binding.addProperty("fromOccurrenceId", PRODUCER_OCCURRENCE);
        binding.addProperty("toOccurrenceId", TARGET_OCCURRENCE);
        binding.addProperty("fromOutputPort", fromPort);
        binding.addProperty("toInputPort", toPort);
        binding.addProperty("evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        binding.addProperty("writerLaneId", "lane.writer");
        binding.addProperty("readerLaneId", "lane.reader");
        binding.addProperty("programOrderRequired", false);
        binding.addProperty("writerEventSeq", 20);
        binding.addProperty("readerEventSeq", 30);
        binding.addProperty("receiverObjectId", 7);
        return binding;
    }

    private static JsonObject region(String id, boolean hasInput,
                                     boolean hasOutput) {
        JsonObject region = new JsonObject();
        region.addProperty("regionId", id);
        JsonArray inputs = new JsonArray();
        if (hasInput) inputs.add(port(id + ".in.0", "input"));
        region.add("symbolicInputs", inputs);
        JsonArray outputs = new JsonArray();
        if (hasOutput) outputs.add(port(id + ".out.0", "output"));
        region.add("outputs", outputs);
        return region;
    }

    private static JsonObject port(String id, String role) {
        JsonObject port = new JsonObject();
        port.addProperty("portId", id);
        port.addProperty("cell", "<Test: int " + role + ">");
        port.addProperty("javaType", "int");
        return port;
    }

    private static JsonObject reference(String symbol) {
        JsonObject value = new JsonObject();
        value.addProperty("_type", "SymbolExpression");
        value.addProperty("_java_type", "I");
        value.addProperty("_exp", symbol);
        return value;
    }

    private static void write(Path path, String content) throws Exception {
        Files.write(path, content.getBytes(StandardCharsets.UTF_8));
    }
}
