package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/** Core receiver-boundary contracts: additive merging and stable lineage. */
public class SymbolicPropagationClosureTest {
    private static final String EPOCH = "epoch-1";

    @Test
    public void fanInMergesTwoPlusTwoWithoutCartesianCases() {
        List<JsonObject> rows = new ArrayList<>();
        for (int replay = 1; replay <= 2; replay++) {
            String scope = "replay-group:g" + replay;
            rows.add(summary("B", "B#a1", "TASK.B." + replay, scope,
                    symbol("M_B_" + replay)));
            rows.add(summary("C", "C#a1", "TASK.C." + replay, scope,
                    symbol("M_C_" + replay)));
            JsonObject b = boundary(VmExpressionIr.RPC_ATTACH,
                    100 + replay, symbol("M_B_" + replay));
            JsonObject c = boundary(VmExpressionIr.RPC_ATTACH,
                    200 + replay, symbol("M_C_" + replay));
            JsonObject a = summary("A", "A#a1", "TASK.A." + replay,
                    scope, binary(b, c));
            handoff(a, "FAMILY.B", "B.in", 100 + replay,
                    "TASK.B." + replay, "B#a1", b);
            handoff(a, "FAMILY.C", "C.in", 200 + replay,
                    "TASK.C." + replay, "C#a1", c);
            rows.add(a);
        }

        SymbolicPropagationClosure.Result result =
                rewrite(rows);

        assertTrue(result.complete());
        assertEquals(2, merge(result, "FAMILY.B")
                .getAsJsonArray("arms").size());
        assertEquals(2, merge(result, "FAMILY.C")
                .getAsJsonArray("arms").size());
        assertEquals(4, dependencySelectors(result).size());
        assertEquals(2, mergeIds(result.summaries()).size());
    }

    @Test
    public void guardedReadCarriesEveryWriterCase() {
        String scope = "replay-group:guarded-writer-cases";
        JsonObject positive = summary("W", "W#a1", "TASK.W.POS", scope,
                binary(symbol("M_INPUT"), constant(0)));
        JsonObject negative = summary("W", "W#a1", "TASK.W.NEG", scope,
                binary(symbol("M_INPUT"), constant(1)));
        JsonObject first = candidate("rf_positive", 691L,
                symbol("M_POSITIVE"), positive, 1);
        JsonObject second = candidate("rf_negative", 692L,
                symbol("M_NEGATIVE"), negative, 2);
        JsonObject read = guardedRead(701L, first, second);
        read.addProperty("writerSetComplete", false);
        JsonObject reader = summary("R", "R#a1", "TASK.R", scope,
                boundary(VmExpressionIr.FIELD_READ, 701L, read));
        addGuardedReadEvidence(reader, read, positive, negative);

        SymbolicPropagationClosure.Result result = rewrite(Arrays.asList(
                positive, negative, reader));

        assertFalse(result.complete());
        assertTrue(result.gaps().toString(), result.gaps().toString()
                .contains("READ_FROM_SNAPSHOT_INCOMPLETE"));
        JsonObject rewritten = firstExpressionOfType(result.summaries(),
                SharedStateEvidence.GUARDED_READ_TYPE);
        assertEquals(2, rewritten.getAsJsonArray("candidates").size());
        Set<String> families = new LinkedHashSet<>();
        for (JsonElement encoded : rewritten.getAsJsonArray("candidates")) {
            JsonObject arm = encoded.getAsJsonObject();
            families.add(optionalString(arm,
                    SymbolicPropagationClosure.WRITER_CASE_FAMILY));
            assertTrue(arm.has(SymbolicPropagationClosure.WRITER_CASE_OWNER));
            assertTrue(arm.has(
                    SymbolicPropagationClosure.WRITER_CASE_SELECTOR));
        }
        assertEquals(1, families.size());
        JsonObject dependency = dependency(result,
                families.iterator().next());
        assertEquals(SymbolicPropagationClosure.READ_FROM_DEPENDENCY_POLICY,
                optionalString(dependency, "selectionPolicy"));
        assertEquals(2, dependency.getAsJsonArray("arms").size());

    }

    @Test
    public void mapReadCandidateProjectsItsRecordedState() {
        String scope = "replay-group:map-projection";
        JsonObject state = containerRelation("STATE", symbol("M_MAP"));
        JsonObject query = containerRelation("READ", state);
        JsonObject writer = summary("W", "W#a1", "TASK.W", scope,
                state);
        JsonObject arm = candidate("rf_map", 693L, query, writer, 1);
        arm.addProperty("versionKind", "STATE_PUT");
        JsonObject read = guardedRead(702L, arm);
        JsonObject location = read.getAsJsonObject("location");
        location.addProperty("locationKind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        location.addProperty("slot", SharedStateEvidence.MAP_STATE_SLOT);
        JsonObject reader = summary("R", "R#a1", "TASK.R", scope,
                boundary(VmExpressionIr.FIELD_READ, 702L, read));
        addGuardedReadEvidence(reader, read, writer);
        JsonObject record = reader.getAsJsonObject(
                SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(0).getAsJsonObject();
        record.addProperty("locationKey", "MAP_STATE/17#-3");
        record.getAsJsonObject("carrier").addProperty("kind", "MAP_STATE");
        JsonObject recordedVersion = record.getAsJsonObject("envelope")
                .getAsJsonArray("versions").get(0).getAsJsonObject();
        recordedVersion.addProperty("versionKind", "STATE_PUT");
        recordedVersion.add("expression", state.deepCopy());

        SymbolicPropagationClosure.Result result = rewrite(Arrays.asList(
                writer, reader));

        assertTrue(result.gaps().toString(), result.complete());
        JsonObject rewritten = firstExpressionOfType(result.summaries(),
                SharedStateEvidence.GUARDED_READ_TYPE);
        assertEquals("READ", rewritten.getAsJsonArray("candidates").get(0)
                .getAsJsonObject().getAsJsonObject("expression")
                .get("operation").getAsString());
    }

    @Test
    public void missingProducerEvidenceFailsClosed() {
        JsonObject wrapped = boundary(VmExpressionIr.RPC_ATTACH, 701,
                symbol("M_missing"));
        JsonObject reader = summary("A", "A#a1", "TASK.A",
                "replay-group:missing", wrapped);
        handoff(reader, "FAMILY.MISSING", "A.in", 701,
                "TASK.NOT_PRESENT", "B#a1", wrapped);

        SymbolicPropagationClosure.Result result = rewrite(
                Arrays.asList(reader));

        assertFalse(result.complete());
        assertTrue(containsReason(result.gaps(),
                "CONSUMER_BOUNDARY_PRODUCER_CASE_MISSING"));
    }

    /**
     * Read evidence that cannot be addressed is reported, not dropped.
     *
     * <p>A recorded read with no read event id names no boundary, and a read
     * that names no reader occurrence is claimed by its unique carrier case
     * only while exactly one case carries the boundary.  Neither may end as
     * a silently unaddressed read that still publishes a complete closure.
     * </p>
     */
    @Test
    public void fieldReadWithUnaddressableEvidenceIsAGapNotASilentDrop() {
        String scope = "replay-group:unaddressable-read";
        JsonObject writer = summary("W", "W#a1", "TASK.W", scope,
                symbol("M_WRITER"));
        JsonObject read = guardedRead(701L,
                candidate("rf_only", 691L, symbol("M_WRITTEN"), writer, 1));
        JsonObject reader = summary("R", "R#a1", "TASK.R", scope,
                boundary(VmExpressionIr.FIELD_READ, 701L, read));
        addGuardedReadEvidence(reader, read, writer);
        observedRead(reader).remove("readEventId");

        SymbolicPropagationClosure.Result unaddressed = rewrite(
                Arrays.asList(writer, reader));

        assertFalse(unaddressed.gaps().toString(), unaddressed.complete());
        assertTrue(unaddressed.gaps().toString(), containsReason(
                unaddressed.gaps(), "CONSUMER_BOUNDARY_FAMILY_MISSING"));

        // The same read without a reader occurrence: one consuming case
        // joins it, and so do several - one physical read of a shared
        // location is exactly the value more than one case goes on to
        // consume, and that sharing is a link to expose rather than an
        // ambiguity to refuse.
        JsonObject soleWriter = summary("W", "W#a1", "TASK.W2", scope,
                symbol("M_WRITER"));
        JsonObject soleRead = guardedRead(711L,
                candidate("rf_only", 692L, symbol("M_WRITTEN"), soleWriter,
                        1));
        JsonObject soleReader = summary("R", "R#a2", "TASK.R2", scope,
                boundary(VmExpressionIr.FIELD_READ, 711L, soleRead));
        addGuardedReadEvidence(soleReader, soleRead, soleWriter);
        observedRead(soleReader).remove(
                SharedStateEvidence.READER_OCCURRENCE_ID);

        SymbolicPropagationClosure.Result claimed = rewrite(Arrays.asList(
                soleWriter, soleReader));
        assertTrue(claimed.gaps().toString(), claimed.complete());

        JsonObject secondCarrier = summary("R", "R#a3", "TASK.R3", scope,
                boundary(VmExpressionIr.FIELD_READ, 711L, soleRead));
        addGuardedReadEvidence(secondCarrier, soleRead, soleWriter);
        observedRead(secondCarrier).remove(
                SharedStateEvidence.READER_OCCURRENCE_ID);

        SymbolicPropagationClosure.Result shared = rewrite(Arrays.asList(
                soleWriter, soleReader, secondCarrier));

        // One read, one family.  A consumer-keyed address would have minted
        // one family per consuming case, and each consumer would then have
        // resolved the same physical read through a family of its own -
        // which is what left this boundary unjoined before.
        assertTrue(shared.gaps().toString(), shared.complete());
        assertFalse(shared.gaps().toString(), containsReason(shared.gaps(),
                "CONSUMER_BOUNDARY_FAMILY_MISSING"));
        assertFalse(shared.gaps().toString(), containsReason(shared.gaps(),
                "CONSUMER_BOUNDARY_EVENT_AMBIGUOUS"));
        assertFalse(shared.gaps().toString(), containsReason(shared.gaps(),
                "CONSUMER_BOUNDARY_OWNER_CASE_AMBIGUOUS"));
    }

    /** The single read the guarded-read evidence helper published. */
    private static JsonObject observedRead(JsonObject reader) {
        return reader.getAsJsonObject(SharedStateEvidence.RECORDED_FIELD)
                .getAsJsonArray("versions").get(0).getAsJsonObject()
                .getAsJsonObject("envelope").getAsJsonArray("reads")
                .get(0).getAsJsonObject();
    }

    private static JsonObject summary(String region, String occurrence,
                                      String task, String scope,
                                      JsonElement condition) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        row.addProperty("summaryId", "SUMMARY." + task);
        row.addProperty("relationKey", "REL." + region);
        row.addProperty("regionId", region);
        row.addProperty("sourceKey", "SOURCE." + region);
        row.addProperty("occurrenceId", occurrence);
        row.addProperty("plannedOccurrenceId",
                OccurrenceId.parse(occurrence).planned());
        row.addProperty("taskId", task);
        row.addProperty("sourceTaskId", task);
        row.addProperty("boundarySessionScope", scope);
        row.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, EPOCH);
        row.addProperty("pathSetClosed", true);
        JsonArray pc = new JsonArray();
        pc.add(condition.deepCopy());
        row.add("pathCondition", pc);
        boolean outcome = !task.endsWith(".2") && !task.endsWith(".NEG");
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.concrete(
                ExactConcreteBranchObservation.attested("SITE." + region,
                        "<fixture." + region + ": void run()>", 0, 1,
                        outcome),
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        row.add("branchMappings", mappings);
        row.addProperty(LocalCaseIdentity.FIELD,
                LocalCaseIdentity.compute(row));
        return row;
    }

    private static SymbolicPropagationClosure.Result rewrite(
            List<JsonObject> rows) {
        List<JsonObject> portable = new ArrayList<>();
        for (JsonObject row : rows) {
            row.remove(LocalCaseIdentity.FIELD);
            row.addProperty(LocalCaseIdentity.FIELD,
                    LocalCaseIdentity.compute(row));
            portable.add(SharedExpressionTable.compact(row));
        }
        return SymbolicPropagationClosure.rewriteSummaryRows(portable);
    }

    private static void handoff(JsonObject receiver, String family,
                                String port, long attachEvent,
                                String producerTask,
                                String producerOccurrence,
                                JsonObject wrapper) {
        JsonObject event = VmHandoffEvidence.event(port, attachEvent - 1,
                attachEvent, wrapper, producerTask, producerOccurrence);
        event = VmHandoffEvidence.withBoundaryFamily(event, family, EPOCH);
        event.addProperty("boundarySessionScope",
                receiver.get("boundarySessionScope").getAsString());
        JsonArray events = receiver.has(VmHandoffEvidence.FIELD)
                ? receiver.getAsJsonArray(VmHandoffEvidence.FIELD)
                : new JsonArray();
        events.add(event);
        receiver.add(VmHandoffEvidence.FIELD, events);
    }

    private static JsonObject candidate(String selector, long version,
                                        JsonElement expression,
                                        JsonObject writer, int ordinal) {
        String owner = LocalCaseIdentity.owner(writer);
        JsonObject result = new JsonObject();
        result.addProperty("selector", selector);
        result.addProperty("fieldVersionId", version);
        result.addProperty("versionKind", "WRITE");
        result.addProperty("writerContextId", ordinal);
        result.addProperty("regionEnterEventId", ordinal + 500L);
        result.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                optionalString(writer, "sourceKey"));
        result.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                optionalString(writer, "occurrenceId"));
        result.add("expression", expression.deepCopy());
        result.add("pathGuard", SharedStateEvidence.emptyConjunction());
        result.addProperty(SymbolicPropagationClosure.WRITER_CASE_OWNER,
                owner);
        result.addProperty(SymbolicPropagationClosure.WRITER_CASE_SELECTOR,
                LocalCaseIdentity.selector(owner));
        return result;
    }

    private static JsonObject guardedRead(long event,
                                          JsonObject... candidates) {
        JsonObject read = new JsonObject();
        read.addProperty("_type", SharedStateEvidence.GUARDED_READ_TYPE);
        read.addProperty("_java_type", "I");
        read.addProperty("readEventId", event);
        read.addProperty("expressionAuthority",
                SharedStateEvidence.GUARDED_READ_AUTHORITY);
        read.addProperty("writerSetComplete", true);
        JsonObject location = new JsonObject();
        location.addProperty("locationKind", "INSTANCE_FIELD");
        location.addProperty("ownerSymRid", 17L);
        location.addProperty("slot", 8);
        read.add("location", location);
        JsonArray arms = new JsonArray();
        JsonArray selectors = new JsonArray();
        for (JsonObject candidate : candidates) {
            arms.add(candidate);
            selectors.add(optionalString(candidate, "selector"));
        }
        read.add("candidates", arms);
        read.add("exactlyOne", selectors);
        return read;
    }

    private static void addGuardedReadEvidence(JsonObject reader,
                                               JsonObject read,
                                               JsonObject... writers) {
        JsonArray versions = new JsonArray();
        long enter = 500L;
        for (int index = 0; index < writers.length; index++) {
            JsonObject writer = writers[index];
            JsonObject candidate = read.getAsJsonArray("candidates")
                    .get(index).getAsJsonObject();
            JsonObject version = candidate.deepCopy();
            version.addProperty("versionKind", "WRITE");
            version.addProperty("writerContextId", index + 1L);
            version.addProperty("regionEnterEventId", enter + index);
            version.addProperty("taskId", optionalString(writer, "taskId"));
            version.addProperty("regionId", optionalString(writer, "regionId"));
            version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                    optionalString(writer, "sourceKey"));
            version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                    optionalString(writer, "occurrenceId"));
            version.add(SymbolicPropagationClosure.WRITER_ACTIVATION_CLOSURE,
                    activationClosure(writer));
            versions.add(version);
        }
        JsonObject observedRead = new JsonObject();
        observedRead.addProperty("readEventId",
                read.get("readEventId").getAsLong());
        observedRead.addProperty("readerContextId", 9L);
        observedRead.addProperty("regionEnterEventId", 509L);
        observedRead.addProperty("regionId", optionalString(reader, "regionId"));
        observedRead.addProperty("taskId", optionalString(reader, "taskId"));
        observedRead.addProperty(SharedStateEvidence.READER_SOURCE_KEY,
                optionalString(reader, "sourceKey"));
        observedRead.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                optionalString(reader, "occurrenceId"));
        observedRead.addProperty(SharedStateEvidence.CONSUMER_SITE_ID,
                "example.Reader#u11");
        observedRead.addProperty(
                SharedStateEvidence.CONSUMER_SITE_OCCURRENCE, 1);
        observedRead.addProperty("candidateCount",
                read.getAsJsonArray("candidates").size());
        JsonObject envelope = new JsonObject();
        envelope.addProperty("kind",
                SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
        envelope.addProperty("schemaVersion", SharedStateEvidence.SCHEMA_VERSION);
        envelope.addProperty("selected", true);
        envelope.add("location", read.get("location").deepCopy());
        envelope.addProperty("writerSetComplete",
                read.get("writerSetComplete").getAsBoolean());
        envelope.addProperty("serializationTruncated", false);
        JsonArray reads = new JsonArray();
        reads.add(observedRead);
        envelope.add("reads", reads);
        envelope.addProperty("readLogTruncated", false);
        envelope.add("versions", versions);

        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", "INSTANCE_FIELD");
        carrier.addProperty("declaringClass", "example.State");
        carrier.addProperty("fieldName", "value");
        carrier.addProperty("descriptor", "I");
        carrier.addProperty("receiverObjectId", 0L);
        JsonObject record = new JsonObject();
        record.addProperty("locationKey", "INSTANCE_FIELD/17#8");
        record.add("carrier", carrier);
        record.add("envelope", envelope);
        JsonArray records = new JsonArray();
        records.add(record);
        JsonObject state = new JsonObject();
        state.add("versions", records);
        reader.add(SharedStateEvidence.RECORDED_FIELD, state);
    }

    private static JsonObject activationClosure(JsonObject... cases) {
        JsonObject closure = new JsonObject();
        closure.addProperty("authority", SymbolicPropagationClosure
                .WRITER_ACTIVATION_CLOSURE_AUTHORITY);
        closure.addProperty("complete", true);
        JsonArray encoded = new JsonArray();
        for (JsonObject localCase : cases) {
            JsonObject address = new JsonObject();
            address.addProperty("taskId", optionalString(localCase, "taskId"));
            address.addProperty("regionId", optionalString(localCase, "regionId"));
            address.addProperty("occurrenceId",
                    optionalString(localCase, "occurrenceId"));
            encoded.add(address);
        }
        closure.add("cases", encoded);
        return closure;
    }

    private static JsonObject firstExpressionOfType(
            JsonElement value, String type) {
        if (value == null || value.isJsonNull()
                || value.isJsonPrimitive()) return new JsonObject();
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                JsonObject found = firstExpressionOfType(child, type);
                if (found.size() > 0) return found;
            }
            return new JsonObject();
        }
        JsonObject object = value.getAsJsonObject();
        if (type.equals(optionalString(object, "_type"))) return object;
        for (Map.Entry<String, JsonElement> field : object.entrySet()) {
            JsonObject found = firstExpressionOfType(field.getValue(), type);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    private static JsonObject firstExpressionOfType(
            List<JsonObject> rows, String type) {
        for (JsonObject row : rows) {
            JsonObject found = firstExpressionOfType(row, type);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    private static JsonObject boundary(String kind, long event,
                                       JsonElement payload) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", VmExpressionIr.CONSUMER_BOUNDARY_TYPE);
        result.addProperty(VmExpressionIr.BOUNDARY_KIND, kind);
        result.addProperty(VmExpressionIr.EVENT_ID, event);
        result.addProperty("_java_type", "I");
        result.add(VmExpressionIr.EXPRESSION, payload.deepCopy());
        return result;
    }

    private static JsonObject symbol(String name) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", name);
        return result;
    }

    private static JsonObject constant(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConSymbolExp");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "C_I_" + value);
        return result;
    }

    private static JsonObject containerRelation(String operation,
                                                JsonElement receiver) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", ContainerSmtCodec.EXPRESSION_TYPE);
        result.addProperty("_java_type", "L");
        result.addProperty("shape", "ASSOCIATIVE");
        result.addProperty("operation", operation);
        result.add("receiver", receiver.deepCopy());
        result.add("arguments", new JsonArray());
        return result;
    }

    private static JsonObject add(JsonElement left, JsonElement right) {
        JsonObject result = binary(left, right);
        result.addProperty("_op", "+");
        return result;
    }

    private static JsonObject binary(JsonElement left, JsonElement right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_java_type", "I");
        result.addProperty("_op", "==");
        result.add("_left", left.deepCopy());
        result.add("_right", right.deepCopy());
        return result;
    }

    private static Set<String> dependencySelectors(
            SymbolicPropagationClosure.Result result) {
        Set<String> selectors = new LinkedHashSet<>();
        for (JsonElement encoded : result.caseDependencies()) {
            for (JsonElement arm : encoded.getAsJsonObject()
                    .getAsJsonArray("arms")) {
                selectors.add(arm.getAsJsonObject().get("selector")
                        .getAsString());
            }
        }
        return selectors;
    }

    private static JsonObject dependency(
            SymbolicPropagationClosure.Result result, String family) {
        for (JsonElement encoded : result.caseDependencies()) {
            JsonObject row = encoded.getAsJsonObject();
            if (family.equals(optionalString(row, VmExpressionIr.FAMILY_KEY))) {
                return row;
            }
        }
        return new JsonObject();
    }

    private static JsonObject merge(
            SymbolicPropagationClosure.Result result, String family) {
        for (JsonObject summary : result.summaries()) {
            JsonObject found = firstMergeForFamily(summary, family);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    private static JsonObject firstMergeForFamily(JsonElement value,
                                                   String family) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return new JsonObject();
        }
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                JsonObject found = firstMergeForFamily(child, family);
                if (found.size() > 0) return found;
            }
            return new JsonObject();
        }
        JsonObject object = value.getAsJsonObject();
        if (SymbolicPropagationClosure.ITE_TYPE.equals(
                optionalString(object, "_type"))
                && family.equals(optionalString(object,
                VmExpressionIr.FAMILY_KEY))) {
            return object;
        }
        for (Map.Entry<String, JsonElement> field : object.entrySet()) {
            JsonObject found = firstMergeForFamily(field.getValue(), family);
            if (found.size() > 0) return found;
        }
        return new JsonObject();
    }

    /** Every family key an emitted case-merge node names. */
    private static void collectMergeFamilies(JsonElement value,
                                             Set<String> result) {
        if (value == null || value.isJsonNull()) return;
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                collectMergeFamilies(child, result);
            }
        } else if (value.isJsonObject()) {
            JsonObject object = value.getAsJsonObject();
            if (SymbolicPropagationClosure.ITE_TYPE.equals(
                    optionalString(object, "_type"))) {
                result.add(optionalString(object,
                        VmExpressionIr.FAMILY_KEY));
            }
            for (Map.Entry<String, JsonElement> field : object.entrySet()) {
                collectMergeFamilies(field.getValue(), result);
            }
        }
    }

    private static Set<String> mergeIds(List<JsonObject> summaries) {
        Set<String> result = new LinkedHashSet<>();
        for (JsonObject summary : summaries) collectMergeIds(summary, result);
        return result;
    }

    private static void collectMergeIds(JsonElement value,
                                        Set<String> result) {
        if (value == null || value.isJsonNull()) return;
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                collectMergeIds(child, result);
            }
        } else if (value.isJsonObject()) {
            JsonObject object = value.getAsJsonObject();
            if (SymbolicPropagationClosure.ITE_TYPE.equals(
                    optionalString(object, "_type"))) {
                result.add(optionalString(object, "mergeId"));
            }
            for (Map.Entry<String, JsonElement> field : object.entrySet()) {
                collectMergeIds(field.getValue(), result);
            }
        }
    }

    private static boolean containsType(JsonElement value, String type) {
        Set<String> ids = new LinkedHashSet<>();
        collectMergeIds(value, ids);
        return !ids.isEmpty()
                && SymbolicPropagationClosure.ITE_TYPE.equals(type);
    }

    private static boolean containsReason(JsonArray rows, String reason) {
        for (JsonElement encoded : rows) {
            JsonObject row = encoded.getAsJsonObject();
            if (reason.equals(optionalString(row, "reason"))) return true;
        }
        return false;
    }
}
