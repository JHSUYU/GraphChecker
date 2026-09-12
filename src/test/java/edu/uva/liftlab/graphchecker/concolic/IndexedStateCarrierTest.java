package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * An indexed container carried whole: the classifier that selects it, the
 * version kinds it publishes, the replay chain that admits its reads, and the
 * SMT the composer lowers those reads to.
 */
public class IndexedStateCarrierTest {

    // ---------------------------------------------------------------- types

    @Test
    public void voidReturningIndexedMutatorsAreModeled() {
        // List.add(int,E) and List.clear() return nothing.  A signature
        // parser that rejected every void return dropped both, so a selected
        // list published no version for a positional insertion - which is
        // the only way a sorted snapshot list ever grows.
        assertTrue(JavaContainerTypes.modeledContainerMutator(
                "<java.util.List: void add(int,java.lang.Object)>"));
        assertTrue(JavaContainerTypes.modeledContainerMutator(
                "<java.util.ArrayList: void add(int,java.lang.Object)>"));
        assertTrue(JavaContainerTypes.modeledContainerMutator(
                "<java.util.List: void clear()>"));
        assertTrue(JavaContainerTypes.modeledContainerMutator(
                "<java.util.List: java.lang.Object remove(int)>"));
    }

    @Test
    public void aVoidReturnIsStillNotAResultBearingOperation() {
        // Admitting void into the parser must not make a void call look like
        // it produces a symbolic result.
        assertFalse(JavaContainerTypes.symbolicResultOperation(
                "<java.util.List: void add(int,java.lang.Object)>"));
        assertFalse(JavaContainerTypes.symbolicResultOperation(
                "<java.util.List: void clear()>"));
        assertFalse(JavaContainerTypes.symbolicResultReturn(
                "<java.util.List: void clear()>.return"));
        assertFalse(JavaContainerTypes.structuralCardinalityOperation(
                "<java.util.List: void clear()>"));
        assertFalse(JavaContainerTypes.associativePut(
                "<java.util.Map: void clear()>"));
        // A malformed signature is still refused.
        assertFalse(JavaContainerTypes.modeledContainerMutator(
                "java.util.List.clear"));
    }

    @Test
    public void indexedFieldsAreWholeStateCarriers() {
        assertEquals(JavaContainerTypes.Shape.INDEXED,
                JavaContainerTypes.wholeStateShape("java.util.List"));
        assertEquals(JavaContainerTypes.Shape.INDEXED,
                JavaContainerTypes.wholeStateShape("java.util.ArrayList"));
        assertEquals(JavaContainerTypes.Shape.INDEXED,
                JavaContainerTypes.wholeStateShape(
                        "java.util.List<example.Snapshot>"));
        assertEquals(JavaContainerTypes.Shape.ASSOCIATIVE,
                JavaContainerTypes.wholeStateShape("java.util.Map"));
        // An array already has its own element locations.
        assertEquals(JavaContainerTypes.Shape.NONE,
                JavaContainerTypes.wholeStateShape("java.util.List[]"));
        assertEquals(JavaContainerTypes.Shape.NONE,
                JavaContainerTypes.wholeStateShape("[Ljava/util/List;"));
        // A set is versioned whole by no carrier this build declares.
        assertEquals(JavaContainerTypes.Shape.NONE,
                JavaContainerTypes.wholeStateShape("java.util.HashSet"));
        assertEquals(JavaContainerTypes.Shape.NONE,
                JavaContainerTypes.wholeStateShape("example.Snapshot"));
        assertFalse(JavaContainerTypes.wholeStateCarrierType(""));
    }

    // -------------------------------------------------------- version kinds

    @Test
    public void indexedVersionKindsAreAdmitted() {
        // One unadmitted kind fails the whole envelope, so the location loses
        // every version it published and each read of it reaches the formula
        // with no read-from arm.
        assertEquals("", SharedStateEvidence.versionsFault(
                indexedEnvelope("INITIAL", "STATE_APPEND", "STATE_INSERT",
                        "STATE_WRITE", "STATE_REMOVE", "STATE_CLEAR")));
    }

    @Test
    public void anUnknownStateKindStillFailsTheEnvelope() {
        String fault = SharedStateEvidence.versionsFault(
                indexedEnvelope("INITIAL", "STATE_SPLICE"));
        assertTrue(fault, fault.contains("has no declared kind"));
    }

    @Test
    public void aPointerKindOnAWholeStateLocationIsRefused() {
        // A whole-state location publishes whole states.  A WRITE version on
        // it would be the pointer chain double-counting the same storage.
        String fault = SharedStateEvidence.versionsFault(
                indexedEnvelope("INITIAL", "WRITE"));
        assertTrue(fault, fault.contains(
                "that its location kind does not publish"));
    }

    @Test
    public void indexedStateRootsCarryContentAddressedIdentity() {
        assertTrue(SharedStateEvidence.isWholeStateRoot(
                relation("INDEXED", "STATE", null)));
        assertTrue(SharedStateEvidence.isWholeStateRoot(
                relation("ASSOCIATIVE", "STATE", null)));
        assertFalse(SharedStateEvidence.isWholeStateRoot(
                relation("INDEXED", "APPEND", null)));
        assertFalse(SharedStateEvidence.isWholeStateRoot(null));
    }

    // ------------------------------------------------------- replay admission

    @Test
    public void anIndexedMutationChainIsAnInitialObservation() {
        // The traversal of a selected list walks the state its mutations
        // produced.  Every one of those mutations has to be admitted, or the
        // first add ends the walk and the recorded read cannot be replayed.
        // Runtime carrier evidence rewrites a whole-state receiver to its
        // replay-stable content address, so that is the identity a replayed
        // traversal of a selected list actually carries.
        String port = "MAP_STATE.v1." + digest('d');
        JsonObject state = relation("INDEXED", "STATE", symbol(port));
        JsonObject appended = relation("INDEXED", "APPEND", state);
        JsonObject inserted = withArguments(
                relation("INDEXED", "INSERT", appended), integer(0),
                symbol("A_L_1"));
        JsonObject removed = withArguments(
                relation("INDEXED", "REMOVE", inserted), integer(1));
        JsonObject written = withArguments(
                relation("INDEXED", "WRITE", removed), integer(0),
                symbol("A_L_2"));
        JsonObject iterator = relation("INDEXED", "ITERATOR", written);
        JsonObject next = withArguments(
                relation("INDEXED", "NEXT", iterator), integer(0));

        InitialContainerObservation.Read observation =
                InitialContainerObservation.initialRead(next);
        assertNotNull(observation);
        assertEquals(port, observation.inputPort);
        assertEquals(Integer.valueOf(0), observation.index);
    }

    @Test
    public void anUnmodeledIndexedOperationIsNotAdmitted() {
        String port = "MAP_STATE.v1." + digest('e');
        JsonObject state = relation("INDEXED", "STATE", symbol(port));
        JsonObject spliced = relation("INDEXED", "SPLICE", state);
        JsonObject read = withArguments(
                relation("INDEXED", "READ", spliced), integer(0));
        assertNull(InitialContainerObservation.initialRead(read));
    }

    // ------------------------------------------------------- composer lowering

    @Test
    public void anIndexedCarrierChainLowersToClosedFormSize() {
        // The size of an indexed state is closed-form linear in the chain,
        // which is what lets an unrolled HAS_NEXT bound pin a traversal count
        // with no projection walk.
        JsonObject state = relation("INDEXED", "STATE",
                symbol("MAP_STATE.v1." + digest('a')));
        JsonObject appended = withArguments(
                relation("INDEXED", "APPEND", state), symbol("A_L_1"));
        JsonObject removed = withArguments(
                relation("INDEXED", "REMOVE", appended), integer(0));
        JsonObject hasNext = withArguments(
                relation("INDEXED", "HAS_NEXT", removed), integer(1));

        RecordingHost host = new RecordingHost();
        ContainerSmtCodec.Term term = ContainerSmtCodec.term(hasNext, host);
        assertNotNull(String.join(",", host.unsupported), term);
        assertTrue(host.unsupported.isEmpty());
        assertEquals(ContainerSmtCodec.Sort.BOOL, term.sort);
        assertTrue(term.text, term.text.contains("indexed_size"));
        assertTrue(term.text, term.text.contains("indexed_remove"));
        assertTrue(term.text, term.text.contains("indexed_append"));
    }

    @Test
    public void anIndexedSizeReadLowersWithADomainBound() {
        JsonObject state = relation("INDEXED", "STATE",
                symbol("MAP_STATE.v1." + digest('b')));
        JsonObject inserted = withArguments(
                relation("INDEXED", "INSERT", state), integer(0),
                symbol("A_L_1"));
        JsonObject size = relation("INDEXED", "SIZE", inserted);
        size.addProperty("_java_type", "I");

        RecordingHost host = new RecordingHost();
        ContainerSmtCodec.Term term = ContainerSmtCodec.term(size, host);
        assertNotNull(String.join(",", host.unsupported), term);
        assertTrue(host.unsupported.isEmpty());
        assertTrue(term.text, term.text.contains("indexed_size"));
        assertTrue(term.text, term.text.contains("indexed_insert"));
        assertTrue("a Java size is bounded to the int domain",
                host.required.toString().contains("2147483647"));
    }

    @Test
    public void anEvidencedCarrierReceiverSurvivesSelectOverStore() {
        // Select-over-store is exact in value but drops the published version
        // chain out of the formula, leaving the read constrained by no writer.
        JsonObject state = relation("INDEXED", "STATE",
                symbol("MAP_STATE.v1." + digest('c')));
        JsonObject written = withArguments(
                relation("INDEXED", "WRITE", state), integer(0),
                symbol("A_L_1"));
        assertTrue(ContainerSmtCodec.evidencedContainerIdentity(written));

        JsonObject guarded = new JsonObject();
        guarded.addProperty("_type", SharedStateEvidence.GUARDED_READ_TYPE);
        JsonObject overGuarded = withArguments(
                relation("INDEXED", "WRITE", guarded), integer(0),
                symbol("A_L_1"));
        assertTrue(ContainerSmtCodec.evidencedContainerIdentity(overGuarded));

        // A purely local state this encoder built itself is not evidenced.
        JsonObject local = relation("INDEXED", "STATE",
                symbol("A_L'java/util/ArrayList'_7"));
        assertFalse(ContainerSmtCodec.evidencedContainerIdentity(local));
        assertFalse(ContainerSmtCodec.evidencedContainerIdentity(null));
    }

    // --------------------------------------------------------------- helpers

    private static String digest(char fill) {
        StringBuilder text = new StringBuilder();
        for (int index = 0; index < 64; index++) text.append(fill);
        return text.toString();
    }

    private static JsonObject indexedEnvelope(String... versionKinds) {
        JsonObject location = new JsonObject();
        location.addProperty("locationKind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        location.addProperty("ownerSymRid", 41L);
        location.addProperty("slot", SharedStateEvidence.MAP_STATE_SLOT);

        JsonArray versions = new JsonArray();
        long id = 0L;
        for (String versionKind : versionKinds) {
            JsonObject version = new JsonObject();
            version.addProperty("fieldVersionId", ++id);
            version.addProperty("versionKind", versionKind);
            version.addProperty("regionEnterEventId", 286L);
            version.addProperty("regionId", "REGION.f0132fca");
            version.addProperty("taskId", "TASK.SEED.1");
            version.add("pathGuard", null);
            version.add("expression", relation("INDEXED", "STATE", null));
            versions.add(version);
        }

        JsonObject envelope = new JsonObject();
        envelope.addProperty("kind",
                SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
        envelope.addProperty("schemaVersion",
                SharedStateEvidence.SCHEMA_VERSION);
        envelope.addProperty("selected", true);
        envelope.add("location", location);
        envelope.addProperty("writerSetComplete", true);
        envelope.addProperty("serializationTruncated", false);
        envelope.addProperty("readLogTruncated", false);
        envelope.add("versions", versions);
        envelope.add("reads", new JsonArray());
        return envelope;
    }

    private static JsonObject relation(String shape, String operation,
                                       JsonObject receiver) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ContainerRelation");
        result.addProperty("_java_type", "L");
        result.addProperty("shape", shape);
        result.addProperty("operation", operation);
        if (receiver != null) result.add("receiver", receiver);
        result.add("arguments", new JsonArray());
        return result;
    }

    private static JsonObject withArguments(JsonObject relation,
                                            JsonObject... arguments) {
        JsonArray list = new JsonArray();
        for (JsonObject argument : arguments) list.add(argument);
        relation.add("arguments", list);
        return relation;
    }

    private static JsonObject symbol(String raw) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "Ljava/util/List;");
        result.addProperty("_exp", raw);
        return result;
    }

    private static JsonObject integer(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }

    /** A host that names every operand and records what it was asked for. */
    private static final class RecordingHost
            implements ContainerSmtCodec.Host {
        private final List<String> unsupported = new ArrayList<>();
        private final List<String> required = new ArrayList<>();

        @Override
        public ContainerSmtCodec.Term state(JsonElement identity,
                                            ContainerSmtCodec.Sort shape) {
            return new ContainerSmtCodec.Term("container__state", shape);
        }

        @Override
        public ContainerSmtCodec.Term operand(
                JsonElement expression, ContainerSmtCodec.Sort expected) {
            if (ContainerSmtCodec.handles(expression)) {
                return ContainerSmtCodec.term(
                        expression.getAsJsonObject(), this);
            }
            if (expected == ContainerSmtCodec.Sort.INT) {
                return new ContainerSmtCodec.Term(literal(expression),
                        ContainerSmtCodec.Sort.INT);
            }
            return new ContainerSmtCodec.Term("container__state", expected);
        }

        @Override
        public boolean preserveContainerIdentity(
                JsonElement expression, ContainerSmtCodec.Sort expected) {
            return ContainerSmtCodec.evidencedContainerIdentity(expression);
        }

        @Override
        public ContainerSmtCodec.Term box(JsonElement expression) {
            return new ContainerSmtCodec.Term("(VRef nullRef)",
                    ContainerSmtCodec.Sort.VALUE);
        }

        @Override
        public ContainerSmtCodec.Term unbox(ContainerSmtCodec.Term value,
                                            String javaType) {
            return value;
        }

        @Override
        public void require(String predicate) {
            required.add(predicate);
        }

        @Override
        public ContainerSmtCodec.Term field(ContainerSmtCodec.Term owner,
                                            String ownerClass,
                                            int fieldOffset,
                                            String javaType) {
            unsupported.add("field:" + ownerClass);
            return null;
        }

        @Override
        public void unsupported(String reason) {
            unsupported.add(reason);
        }

        private static String literal(JsonElement expression) {
            String raw = expression != null && expression.isJsonObject()
                    ? expression.getAsJsonObject().get("_exp").getAsString()
                    : "0";
            return raw.startsWith("Y_I_") ? raw.substring(4) : "0";
        }
    }
}
