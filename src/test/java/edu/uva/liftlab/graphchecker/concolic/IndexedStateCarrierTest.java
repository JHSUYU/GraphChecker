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

    // -------------------------------------------------------- version kinds

    // ------------------------------------------------------- replay admission

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
        // Size is linear in the chain, so the guard is arithmetic over the
        // one state at the bottom of it: append adds one, remove takes one
        // away.  No state in between is built, which is what keeps an
        // unrolled traversal from carrying a lambda-built element array per
        // iteration.
        assertTrue(term.text, term.text.contains(
                "(- (+ (indexed_size "));
        assertFalse("no element array is built for a traversal guard",
                term.text.contains("indexed_append")
                        || term.text.contains("indexed_remove"));
    }

    // ------------------------------------------------- boxed cell arithmetic

    @Test
    public void anIntElementReadLowersToIntegerArithmetic() {
        // The binarySearch midpoint shape: an int-element indexed read whose
        // value takes part in (low + high) >>> 1.  The read must reach the
        // formula as an Int, not as a tagged Value.
        JsonObject state = relation("INDEXED", "STATE",
                symbol("MAP_STATE.v1." + digest('f')));
        JsonObject read = withArguments(
                relation("INDEXED", "READ", state), integer(3));
        read.addProperty("_java_type", "I");

        RecordingHost host = new RecordingHost();
        ContainerSmtCodec.Term term = ContainerSmtCodec.term(read, host);
        assertNotNull(String.join(",", host.unsupported), term);
        assertTrue(host.unsupported.isEmpty());
        assertEquals(ContainerSmtCodec.Sort.INT, term.sort);
        assertTrue(term.text, term.text.contains("valueInt"));
        assertTrue(term.text, term.text.contains("indexed_read"));
        // The cell's own tag and its position are both required.
        String required = host.required.toString();
        assertTrue(required, required.contains("(_ is VInt)"));
        assertTrue(required, required.contains("indexed_size"));
    }

    @Test
    public void aThreeElementChainReadsByPositionWithoutItsArrays() {
        // append e0,e1,e2 then remove index 0: position 1 answers e2, and no
        // element array is built to say so.
        JsonObject chain = relation("INDEXED", "SNAPSHOT_BASE",
                relation("INDEXED", "STATE",
                        symbol("MAP_STATE.v1." + digest('a'))));
        for (int index = 0; index < 3; index++) {
            chain = withArguments(relation("INDEXED", "APPEND", chain),
                    symbol("e" + index));
        }
        chain = withArguments(relation("INDEXED", "REMOVE", chain),
                integer(0));
        JsonObject read = withArguments(
                relation("INDEXED", "READ", chain), integer(1));
        read.addProperty("_java_type", "L");

        RecordingHost host = new RecordingHost();
        ContainerSmtCodec.Term term = ContainerSmtCodec.term(read, host);
        assertNotNull(String.join(",", host.unsupported), term);
        assertTrue(host.unsupported.isEmpty());
        assertTrue(term.text, term.text.contains("(VRef e2)"));
        assertFalse("no element array is built to read one position",
                term.text.contains("indexed_append")
                        || term.text.contains("indexed_remove")
                        || term.text.contains("store")
                        || term.text.contains("lambda")
                        || term.text.contains("mkIndexedState"));
        // Membership is stated from the chain's closed-form size.
        assertTrue(host.required.toString(),
                host.required.toString().contains("(- (+ (+ (+ 0 1) 1) 1) 1)"));
    }

    // ------------------------------------------- container-valued read sort

    // -------------------------------------------- String literal identity

    // --------------------------------------------------------------- helpers

    private static JsonObject guardedRead(String javaType,
                                          JsonObject... arms) {
        JsonObject read = new JsonObject();
        read.addProperty("_type", SharedStateEvidence.GUARDED_READ_TYPE);
        read.addProperty("_java_type", javaType);
        JsonArray candidates = new JsonArray();
        int ordinal = 0;
        for (JsonObject arm : arms) {
            JsonObject candidate = new JsonObject();
            // Real evidence always carries the arm's selector; a projection
            // refuses an arm without one rather than guess its guard.
            candidate.addProperty("selector", "arm_" + ordinal++);
            candidate.add("expression", arm);
            candidates.add(candidate);
        }
        read.add("candidates", candidates);
        return read;
    }

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
            if (ContainerSmtCodec.handles(expression)) {
                ContainerSmtCodec.Term inner = ContainerSmtCodec.term(
                        expression.getAsJsonObject(), this);
                if (inner != null) return inner;
            }
            String raw = expression != null && expression.isJsonObject()
                    && expression.getAsJsonObject().has("_exp")
                    ? expression.getAsJsonObject().get("_exp").getAsString()
                    : "nullRef";
            return new ContainerSmtCodec.Term("(VRef " + raw + ")",
                    ContainerSmtCodec.Sort.VALUE);
        }

        @Override
        public ContainerSmtCodec.Term unbox(ContainerSmtCodec.Term value,
                                            String javaType) {
            return ContainerSmtCodec.unboxValue(value, javaType,
                    VmTermLowering.unboxedCellSort(
                            VmTermLowering.Sort.INT), this);
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
