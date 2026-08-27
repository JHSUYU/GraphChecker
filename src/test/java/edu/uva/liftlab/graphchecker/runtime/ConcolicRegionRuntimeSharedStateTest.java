package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.RecordedEvidenceIdentity;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.concolic.SparseReadCutGate;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Stock-JDK behaviour of the recorded shared-state bridge, the admission of
 * the VM envelopes it reads back, and the installation boundary of a
 * solver-selected read cut.
 *
 * <p>An ordinary {@code java.lang.System} has none of the five natives, so
 * every call must answer with a named gap rather than a silent no-op. Envelope
 * decoding is exercised through its test seam, because the shape of a refusal
 * is the part a consumer depends on. Installing a read-cut gate means
 * observing, so that call returns a decision, never a wait.</p>
 */
public class ConcolicRegionRuntimeSharedStateTest {
    private static final String OWNER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime."
                    + "ConcolicRegionRuntimeSharedStateTest$Carrier";
    private static final String OCCURRENCE =
            "test-node#epoch0/region/REGION.r#1";
    /** The observer a record needs before anything may admit it. */
    private static final RecordedEvidenceIdentity IDENTITY =
            RecordedEvidenceIdentity.of("", "workload#0", "TASK.reader",
                    OCCURRENCE, "test-node#epoch0", 7L);

    /** Test-only owner; the evidence layer never inspects its type. */
    public static final class Carrier {
        public int value;
    }

    /** Test-only region receiver the declared owner path starts from. */
    public static final class Holder {
        public Carrier holder;
    }

    /** One declared carrier reached through {@code path} on the receiver. */
    private static JsonObject carrierDeclaration(String path) {
        JsonObject declaration = new JsonObject();
        declaration.addProperty("kind", "DECLARED_FIELD");
        declaration.addProperty("declaringClass", OWNER_CLASS);
        declaration.addProperty("fieldName", "value");
        declaration.addProperty("descriptor", "I");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add(path);
        fieldPath.add("value");
        declaration.add("fieldPath", fieldPath);
        return declaration;
    }

    /** The minimum executable task row, with or without declared carriers. */
    private static ExecutionTask executionTask(JsonArray carriers) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.reader");
        task.addProperty("goalId", "GOAL.reader");
        task.addProperty("sourceKey", "test-node#epoch0");
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "test-node/REGION.r");
        task.addProperty("regionId", "REGION.r");
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        if (carriers != null) {
            task.add(ExecutionTask.SHARED_CARRIERS, carriers);
        }
        return ExecutionTask.decode(task);
    }

    @Test
    public void sharedStateAndReadCutAnswerWithNamedFindingsOrNothing() {
        assertAbsent("selectSharedFieldCarrier", Object.class, String.class,
                String.class, String.class);
        assertAbsent("selectSharedElementCarrier", Object.class, int.class);
        assertAbsent("getSharedFieldVersions", Object.class, String.class,
                String.class, String.class);
        assertAbsent("getSharedElementVersions", Object.class, int.class);
        assertAbsent("getEventLedger");

        assertUnavailable(ConcolicRegionRuntime.selectSharedFieldCarrier(
                        new Carrier(), OWNER_CLASS, "value", "I"),
                SharedStateEvidence.STAGE_SELECT);
        assertUnavailable(ConcolicRegionRuntime.selectSharedElementCarrier(
                new int[]{1}, 0), SharedStateEvidence.STAGE_SELECT);
        assertUnavailable(ConcolicRegionRuntime.captureSharedFieldVersions(
                        new Carrier(), OWNER_CLASS, "value", "I"),
                SharedStateEvidence.STAGE_VERSIONS);
        assertUnavailable(ConcolicRegionRuntime.captureSharedElementVersions(
                new int[]{1}, 0), SharedStateEvidence.STAGE_VERSIONS);
        assertUnavailable(ConcolicRegionRuntime.captureSessionEventLedger(),
                SharedStateEvidence.STAGE_LEDGER);

        // Incomplete carrier addressing is missing metadata, not a guess.
        for (ConcolicRegionRuntime.SharedStateResult result
                : new ConcolicRegionRuntime.SharedStateResult[]{
                ConcolicRegionRuntime.selectSharedFieldCarrier(null,
                        OWNER_CLASS, "value", "I"),
                ConcolicRegionRuntime.selectSharedFieldCarrier(new Carrier(),
                        "", "value", "I"),
                ConcolicRegionRuntime.selectSharedFieldCarrier(new Carrier(),
                        OWNER_CLASS, " ", "I"),
                ConcolicRegionRuntime.selectSharedFieldCarrier(new Carrier(),
                        OWNER_CLASS, "value", null),
                ConcolicRegionRuntime.selectSharedElementCarrier(null, 0),
                ConcolicRegionRuntime.selectSharedElementCarrier(
                        new int[]{1}, -1),
                ConcolicRegionRuntime.captureSharedFieldVersions(null,
                        OWNER_CLASS, "value", "I"),
                ConcolicRegionRuntime.captureSharedElementVersions(null, 0)}) {
            assertFalse(result.ok());
            assertEquals(SharedStateEvidence.MISSING_METADATA,
                    result.status());
            assertEquals("SHARED_STATE_MISSING_METADATA", result.reason());
            assertTrue(SharedStateEvidence.isGap(result.gap()));
            assertEquals(0, result.record().size());
        }

        // An authoritative version store becomes recorded evidence.  The VM
        // addresses a location by its own identity; only this call site also
        // knows the declared Java field, so the join is recorded.
        ConcolicRegionRuntime.SharedStateResult versions =
                ConcolicRegionRuntime.decodeVersionsEnvelope(
                        versionsEnvelope().toString(),
                        ConcolicRegionRuntime.SharedCarrier.field(
                                new Carrier(), OWNER_CLASS, "value", "I"),
                        IDENTITY, null);
        assertTrue(versions.ok());
        assertEquals("INSTANCE_FIELD/7#24", versions.locationKey());
        assertEquals(0, versions.gap().size());
        assertTrue(SharedStateEvidence.isVersionsRecord(versions.record()));
        JsonObject carrier = versions.record().getAsJsonObject("carrier");
        assertEquals(OWNER_CLASS + "#value:I",
                carrier.get("fieldKey").getAsString());
        assertEquals("DECLARED_FIELD", carrier.get("kind").getAsString());

        // The stamp is what makes the record admissible at all: the same
        // envelope with no observer is refused rather than admitted with an
        // unknown provenance, and the ordinal - not the row count - is what a
        // consumer ranks two read-outs of one location by.
        JsonObject stamp = versions.record().getAsJsonObject(
                RecordedEvidenceIdentity.FIELD);
        assertEquals("", stamp.get("runId").getAsString());
        assertEquals("workload#0", stamp.get("sessionId").getAsString());
        assertEquals("TASK.reader", stamp.get("taskId").getAsString());
        assertEquals(OCCURRENCE, stamp.get("occurrenceId").getAsString());
        assertEquals(7L, stamp.get("snapshotOrdinal").getAsLong());
        assertFalse(SharedStateEvidence.isVersionsRecord(
                ConcolicRegionRuntime.decodeVersionsEnvelope(
                        versionsEnvelope().toString(), null, null,
                        null).record()));

        // Folded Phase 2 field acceptance: a task declares its carriers and
        // the runtime selects exactly those, at region entry, from the region
        // receiver.  Production runs recorded no field versions at all before
        // this, because nothing outside a test ever named a carrier.  The
        // declaration is carried verbatim - absence means none, and a path
        // that does not resolve is a named refusal rather than a search for a
        // plausible owner.
        assertEquals(0, executionTask(null).sharedCarriers().size());
        JsonArray declared = new JsonArray();
        declared.add(carrierDeclaration("holder"));
        declared.add(carrierDeclaration("absent"));
        assertEquals(declared,
                executionTask(declared).sharedCarriers());

        Holder holder = new Holder();
        holder.holder = new Carrier();
        ConcolicRegionRuntime.SharedCarrierRequest reachable =
                new ConcolicRegionRuntime.SharedCarrierRequest(
                        carrierDeclaration("holder"));
        assertEquals(holder.holder, reachable.resolveOwner(holder));
        assertEquals(ConcolicRegionRuntime.MissingValue.INSTANCE,
                new ConcolicRegionRuntime.SharedCarrierRequest(
                        carrierDeclaration("absent")).resolveOwner(holder));

        // A location the VM did not select is its own named finding, never an
        // empty writer set the consumer would read as "nobody wrote it".
        JsonObject unselected = versionsEnvelope();
        unselected.addProperty("selected", false);
        ConcolicRegionRuntime.SharedStateResult notSelected =
                ConcolicRegionRuntime.decodeVersionsEnvelope(
                        unselected.toString(), null, IDENTITY, null);
        assertFalse(notSelected.ok());
        assertEquals(SharedStateEvidence.NOT_SELECTED, notSelected.status());
        assertEquals("SHARED_STATE_NOT_SELECTED", notSelected.reason());
        assertTrue(SharedStateEvidence.isGap(notSelected.gap()));

        JsonObject noCompleteness = versionsEnvelope();
        noCompleteness.remove("writerSetComplete");
        JsonObject exactReadWithoutWriter = versionsEnvelope();
        exactReadWithoutWriter.getAsJsonArray("reads").get(0)
                .getAsJsonObject().addProperty("chosenFieldVersionId", 0L);
        for (JsonObject envelope : new JsonObject[]{noCompleteness,
                exactReadWithoutWriter}) {
            assertEquals(envelope.toString(),
                    SharedStateEvidence.MALFORMED_ENVELOPE,
                    ConcolicRegionRuntime.decodeVersionsEnvelope(
                            envelope.toString(), null, IDENTITY,
                            null).status());
        }
        for (String serialized : new String[]{"", "   ", "not json",
                "[1, 2]"}) {
            assertEquals(SharedStateEvidence.MALFORMED_ENVELOPE,
                    ConcolicRegionRuntime.decodeVersionsEnvelope(serialized,
                            null, IDENTITY, null).status());
            assertEquals(SharedStateEvidence.MALFORMED_ENVELOPE,
                    ConcolicRegionRuntime.decodeLedgerEnvelope(serialized,
                            IDENTITY).status());
        }

        ConcolicRegionRuntime.SharedStateResult ledger =
                ConcolicRegionRuntime.decodeLedgerEnvelope(
                        ledgerEnvelope().toString(), IDENTITY);
        assertTrue(ledger.ok());
        assertTrue(SharedStateEvidence.isLedgerRecord(ledger.record()));
        assertEquals(SharedStateEvidence.STAGE_LEDGER, ledger.stage());

        // A cyclic relation is not a partial order, so every order fact read
        // out of it would be unsound; noting it as a gap while still using
        // the edges is exactly the failure this refusal prevents.
        JsonObject cyclic = ledgerEnvelope();
        cyclic.addProperty("acyclic", false);
        ConcolicRegionRuntime.SharedStateResult refused =
                ConcolicRegionRuntime.decodeLedgerEnvelope(cyclic.toString(),
                        IDENTITY);
        assertFalse(refused.ok());
        assertEquals(SharedStateEvidence.MALFORMED_ENVELOPE,
                refused.status());
        assertTrue(refused.gap().get("detail").getAsString()
                .contains("cyclic"));

        // A gate that would write a program field or replace an RPC return
        // value is never installed, and a row this authority did not compile
        // is not a gate at all.
        JsonObject writesField = gate();
        writesField.addProperty("writesProgramField", true);
        ConcolicRegionRuntime.ReadCutGateResult violated =
                ConcolicRegionRuntime.installReadCutGate(writesField);
        assertFalse(violated.installed());
        assertEquals(SparseReadCutGate.INVARIANT_VIOLATED, violated.reason());
        assertEquals(0, violated.record().size());
        assertEquals(SparseReadCutGate.GAP_KIND,
                violated.gap().get("kind").getAsString());

        JsonObject replacesReturn = gate();
        replacesReturn.addProperty("replacesRpcReturnValue", true);
        assertEquals(SparseReadCutGate.INVARIANT_VIOLATED,
                ConcolicRegionRuntime.installReadCutGate(replacesReturn)
                        .reason());
        assertEquals(SparseReadCutGate.NOT_A_COMPILED_GATE,
                ConcolicRegionRuntime.installReadCutGate(null).reason());
        assertEquals(SparseReadCutGate.NOT_A_COMPILED_GATE,
                ConcolicRegionRuntime.installReadCutGate(new JsonObject())
                        .reason());
        JsonObject unkeyed = gate();
        unkeyed.addProperty("writerRegionId", "");
        assertEquals(SparseReadCutGate.NO_CROSS_RUN_READ_IDENTITY,
                ConcolicRegionRuntime.installReadCutGate(unkeyed).reason());

        // Nothing is running, so there is no activation to carry the
        // observation; the admissible offer is still named rather than
        // ignored, and it answers immediately rather than scheduling a wait.
        long started = System.nanoTime();
        ConcolicRegionRuntime.ReadCutGateResult admissible =
                ConcolicRegionRuntime.installReadCutGate(gate());
        long elapsedMillis = (System.nanoTime() - started) / 1_000_000L;
        assertFalse(admissible.installed());
        assertEquals(ConcolicRegionRuntime.READ_CUT_NO_ACTIVE_REGION,
                admissible.reason());
        assertEquals("example.State#value",
                admissible.gap().get("readFromField").getAsString());
        assertTrue("installation must not wait: " + elapsedMillis + "ms",
                elapsedMillis < 1_000L);
    }

    @Test
    public void nestedVmSerializerTruncationRefusesOnlyItsVersionStore() {
        JsonObject marker = new JsonObject();
        marker.addProperty("_type",
                SharedStateEvidence.TRUNCATED_EXPRESSION_TYPE);
        marker.addProperty("expressionAuthority",
                SharedStateEvidence.VM_SERIALIZATION_TRUNCATION_AUTHORITY);
        marker.addProperty("truncationKind", "UNIQUE_NODE_BOUND");
        marker.addProperty("expressionId", 73L);

        JsonObject deep = marker;
        for (int depth = 0; depth < 8_192; depth++) {
            JsonObject parent = new JsonObject();
            parent.add("child", deep);
            deep = parent;
        }
        assertTrue(SharedStateEvidence.containsVmSerializationTruncation(
                deep));

        JsonObject nested = new JsonObject();
        JsonArray operands = new JsonArray();
        JsonObject completeSibling = new JsonObject();
        completeSibling.addProperty("_type", "SymbolExpression");
        completeSibling.addProperty("_exp", "A");
        operands.add(completeSibling);
        operands.add(marker);
        nested.add("operands", operands);
        JsonObject envelope = versionsEnvelope();
        envelope.getAsJsonArray("versions").get(0).getAsJsonObject()
                .add("expression", nested);

        assertTrue(SharedStateEvidence.containsVmSerializationTruncation(
                nested));
        ConcolicRegionRuntime.SharedStateResult refused =
                ConcolicRegionRuntime.decodeVersionsEnvelope(
                        envelope.toString(), null, IDENTITY, null);
        assertFalse(refused.ok());
        assertEquals(SharedStateEvidence.EXPRESSION_SERIALIZATION_TRUNCATED,
                refused.status());
        assertEquals("VM_EXPRESSION_SERIALIZATION_TRUNCATED",
                refused.reason());
        assertEquals("INSTANCE_FIELD/7#24", refused.locationKey());
        assertEquals("VM_EXPRESSION_SERIALIZATION_TRUNCATED",
                refused.gap().get("reason").getAsString());
        assertTrue(refused.gap().get("detail").getAsString()
                .contains("version 11 value expression"));

        JsonObject truncatedGuard = versionsEnvelope();
        truncatedGuard.getAsJsonArray("versions").get(0).getAsJsonObject()
                .add("pathGuard", marker.deepCopy());
        ConcolicRegionRuntime.SharedStateResult guardRefused =
                ConcolicRegionRuntime.decodeVersionsEnvelope(
                        truncatedGuard.toString(), null, IDENTITY, null);
        assertEquals(SharedStateEvidence.EXPRESSION_SERIALIZATION_TRUNCATED,
                guardRefused.status());
        assertTrue(guardRefused.gap().get("detail").getAsString()
                .contains("version 11 path guard"));

        // The authority literal in program text is not the marker, and the
        // unrelated ledger remains independently admissible.
        JsonObject ordinary = versionsEnvelope();
        ordinary.getAsJsonArray("versions").get(0).getAsJsonObject()
                .getAsJsonObject("expression").addProperty("_exp",
                SharedStateEvidence.VM_SERIALIZATION_TRUNCATION_AUTHORITY);
        assertTrue(ConcolicRegionRuntime.decodeVersionsEnvelope(
                ordinary.toString(), null, IDENTITY, null).ok());
        assertTrue(ConcolicRegionRuntime.decodeLedgerEnvelope(
                ledgerEnvelope().toString(), IDENTITY).ok());
    }

    /** One compiled gate, in the shape the concolic layer emits it. */
    private static JsonObject gate() {
        JsonObject gate = new JsonObject();
        gate.addProperty("schemaVersion", SparseReadCutGate.SCHEMA_VERSION);
        gate.addProperty("kind", "SPARSE_READ_CUT_GATE");
        gate.addProperty("authority", SparseReadCutGate.AUTHORITY);
        gate.addProperty("gateId", "GATE.21.rf1");
        gate.addProperty("selector", "rf1");
        gate.addProperty("readEventId", 21L);
        gate.addProperty("locationKey", "INSTANCE_FIELD/7#24");
        gate.addProperty("fieldVersionId", 11L);
        gate.addProperty("readFromField", "example.State#value");
        gate.addProperty("writerRegionId", "REGION.writerA");
        gate.addProperty("readerRegionId", "REGION.reader");
        gate.addProperty("placement",
                SparseReadCutGate.BEFORE_SELECTED_ACCESS);
        gate.add("competingWrites", new JsonArray());
        gate.addProperty("observesOnly", true);
        gate.addProperty("writesProgramField", false);
        gate.addProperty("replacesRpcReturnValue", false);
        gate.addProperty("requiresObservedReadVersion", true);
        gate.addProperty("requiresObservedExchange", true);
        assertTrue(SparseReadCutGate.installable(gate));
        return gate;
    }

    private static JsonObject versionsEnvelope() {
        return new com.google.gson.JsonParser().parse(
                "{\"schemaVersion\":1,\"kind\":\"SHARED_FIELD_VERSIONS\","
                        + "\"selected\":true,\"location\":{"
                        + "\"ownerSymRid\":7,\"slot\":24,"
                        + "\"locationKind\":\"INSTANCE_FIELD\"},"
                        + "\"writerSetComplete\":true,\"versions\":["
                        + "{\"fieldVersionId\":11,\"versionKind\":\"WRITE\","
                        + "\"writerContextId\":101,"
                        + "\"writerJavaThreadId\":201,\"writerStep\":1,"
                        + "\"regionId\":\"REGION.a\",\"taskId\":\"TASK.a\","
                        + "\"volatileWrite\":false,"
                        + "\"fingerprintKind\":\"PRIMITIVE\","
                        + "\"fingerprint\":10,\"expression\":{\"_type\":"
                        + "\"SymbolExpression\",\"_java_type\":\"I\","
                        + "\"_exp\":\"A\"},\"pathGuard\":null}],"
                        + "\"reads\":[{\"readEventId\":21,"
                        + "\"readerContextId\":103,"
                        + "\"readerJavaThreadId\":203,"
                        + "\"regionId\":\"REGION.r\","
                        + "\"resolution\":\"EXACT\","
                        + "\"reason\":\"UNIQUE_VERSION\","
                        + "\"chosenFieldVersionId\":11,"
                        + "\"candidateCount\":1,"
                        + "\"observedFingerprintKind\":\"PRIMITIVE\","
                        + "\"observedFingerprint\":10}]}")
                .getAsJsonObject();
    }

    private static JsonObject ledgerEnvelope() {
        return new com.google.gson.JsonParser().parse(
                "{\"schemaVersion\":1,\"kind\":\"SESSION_EVENT_LEDGER\","
                        + "\"open\":true,\"recording\":true,"
                        + "\"truncated\":false,\"domainSaturated\":false,"
                        + "\"partialOrder\":true,\"acyclic\":true,"
                        + "\"events\":[{\"eventId\":11,"
                        + "\"eventKind\":\"FIELD_WRITE\",\"contextId\":101,"
                        + "\"javaThreadId\":201,\"step\":1,"
                        + "\"objectSymRid\":7,\"slot\":24,"
                        + "\"regionId\":\"REGION.a\",\"detail\":\"\"},"
                        + "{\"eventId\":21,\"eventKind\":\"FIELD_READ\","
                        + "\"contextId\":103,\"javaThreadId\":203,"
                        + "\"step\":1,\"objectSymRid\":7,\"slot\":24,"
                        + "\"regionId\":\"REGION.r\",\"detail\":\"READ\"}],"
                        + "\"order\":[{\"beforeEventId\":11,"
                        + "\"afterEventId\":21,"
                        + "\"edgeKind\":\"FIELD_READ_FROM\"}]}")
                .getAsJsonObject();
    }

    private static void assertAbsent(String name, Class<?>... parameters) {
        try {
            System.class.getMethod(name, parameters);
            throw new AssertionError(name
                    + " unexpectedly exists on this JDK; this test asserts "
                    + "the stock-JDK degradation path");
        } catch (NoSuchMethodException expected) {
            assertTrue(true);
        }
    }

    private static void assertUnavailable(
            ConcolicRegionRuntime.SharedStateResult result, String stage) {
        assertFalse(result.ok());
        assertEquals(stage, result.stage());
        assertEquals(SharedStateEvidence.API_UNAVAILABLE, result.status());
        assertEquals("SHARED_STATE_API_UNAVAILABLE", result.reason());
        assertEquals(0, result.record().size());
        assertEquals(0L, result.initialFieldVersionId());
        assertTrue(SharedStateEvidence.isGap(result.gap()));
        assertEquals(stage, result.gap().get("stage").getAsString());
    }
}
