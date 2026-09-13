package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec.Host;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec.Sort;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec.Term;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * A whole-state carrier whose INITIAL version carries its content.
 *
 * <p>The opaque INITIAL form lowers to one free container const, so
 * {@code assoc_has(S0, k)} is undecidable and the INITIAL arm of a read over
 * that location can answer "absent" for every key.  A concrete snapshot is a
 * mutation chain over an explicit empty base, and the codec's projection walk
 * has to terminate in that base rather than in a free const.</p>
 */
public class InitialContainerSnapshotTest {

    private static final int PRESENT_ONE = 276372523;
    private static final int PRESENT_TWO = 276372524;
    private static final int ABSENT = 999999999;


    /** PUT over SNAPSHOT_BASE + one member: a history on a recovered base. */
    private static JsonObject insertOverBase() {
        JsonObject base = relation("SNAPSHOT_BASE");
        base.add("receiver", stateRoot());
        base.add("arguments", new JsonArray());
        JsonObject held = relation("PUT");
        held.add("receiver", base);
        JsonArray heldArguments = new JsonArray();
        heldArguments.add(constant(PRESENT_ONE));
        heldArguments.add(reference(1));
        held.add("arguments", heldArguments);
        // The mutation the recorder watched, now standing on the stated base.
        JsonObject watched = relation("PUT");
        watched.add("receiver", held);
        JsonArray watchedArguments = new JsonArray();
        watchedArguments.add(constant(PRESENT_TWO));
        watchedArguments.add(reference(2));
        watched.add("arguments", watchedArguments);
        return watched;
    }

    /** An INDEXED empty base, the shape the HDFS-17960 list carrier has. */
    private static JsonObject indexedBase() {
        JsonObject base = relation("SNAPSHOT_BASE");
        base.addProperty("shape", "INDEXED");
        base.add("receiver", stateRoot());
        base.add("arguments", new JsonArray());
        return base;
    }

    /**
     * The observation walker reaches the state root through the chain.
     *
     * <p>A snapshotted carrier's reads stand on SNAPSHOT_BASE + one PUT per
     * entry rather than on the bare root. If the walk stops at the first PUT,
     * every read of a snapshotted container stops being an initial
     * observation and its recorded concrete value cannot be replayed - the
     * snapshot would cost the pipeline the replay it already had.</p>
     */
    @Test
    public void theWalkerReachesTheRootThroughATwoPutChain() {
        JsonObject overTheChain = read(rootedSnapshot(), constant(PRESENT_ONE));
        InitialContainerObservation.Read walked =
                InitialContainerObservation.initialRead(overTheChain);
        assertNotNull(walked);
        assertEquals("ASSOCIATIVE", walked.shape);
        assertEquals(MAP_STATE_SYMBOL, walked.stateSymbol);
        assertEquals(MAP_STATE_SYMBOL, walked.inputPort);
        assertNotNull(walked.selector);

        // The same read over the bare opaque root still answers, which is
        // what a truncated snapshot leaves behind.
        InitialContainerObservation.Read opaque =
                InitialContainerObservation.initialRead(
                        read(stateRoot(), constant(PRESENT_ONE)));
        assertNotNull(opaque);
        assertEquals(MAP_STATE_SYMBOL, opaque.stateSymbol);

        // A CLEAR over the chain is still the same initial state.
        JsonObject cleared = relation("CLEAR");
        cleared.add("receiver", rootedSnapshot());
        cleared.add("arguments", new JsonArray());
        assertNotNull(InitialContainerObservation.initialRead(
                read(cleared, constant(PRESENT_ONE))));
    }

    // ---- the recorded shapes -------------------------------------------

    /** The canonical whole-state identity the VM mints for a carrier. */
    private static final String MAP_STATE_SYMBOL = "MAP_STATE.v1."
            + "d88858a60a3a45e93323246272afba670de58ffdbfc904e049e22e9b"
            + "dbeeb4cb";

    private static JsonObject stateRoot() {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "L");
        identity.addProperty("_exp", MAP_STATE_SYMBOL);
        JsonObject root = relation("STATE");
        root.add("receiver", identity);
        root.add("arguments", new JsonArray());
        return root;
    }

    /** SNAPSHOT_BASE over the real state root, then the two PUTs. */
    private static JsonObject rootedSnapshot() {
        JsonObject base = relation("SNAPSHOT_BASE");
        base.add("receiver", stateRoot());
        base.add("arguments", new JsonArray());
        JsonObject state = base;
        int[] keys = {PRESENT_ONE, PRESENT_TWO};
        for (int index = 0; index < keys.length; index++) {
            JsonObject put = relation("PUT");
            put.add("receiver", state);
            JsonArray arguments = new JsonArray();
            arguments.add(constant(keys[index]));
            arguments.add(reference(index + 1));
            put.add("arguments", arguments);
            state = put;
        }
        return state;
    }

    private static JsonObject relation(String operation) {
        JsonObject relation = new JsonObject();
        relation.addProperty("_type", ContainerSmtCodec.EXPRESSION_TYPE);
        relation.addProperty("shape", "ASSOCIATIVE");
        relation.addProperty("operation", operation);
        relation.addProperty("_java_type", "L");
        return relation;
    }

    private static JsonObject emptyBase() {
        JsonObject base = relation("SNAPSHOT_BASE");
        base.add("arguments", new JsonArray());
        return base;
    }

    private static JsonObject constant(int value) {
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_java_type", "I");
        constant.addProperty("_exp", "Y_I_" + value);
        return constant;
    }

    private static JsonObject reference(int ordinal) {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "java/lang/Object");
        symbol.addProperty("_exp", "M_L'java/lang/Object'_" + ordinal);
        return symbol;
    }

    /** empty base, PUT k1 -> v1, PUT k2 -> v2. */
    private static JsonObject snapshot() {
        JsonObject state = emptyBase();
        int[] keys = {PRESENT_ONE, PRESENT_TWO};
        for (int index = 0; index < keys.length; index++) {
            JsonObject put = relation("PUT");
            put.add("receiver", state);
            JsonArray arguments = new JsonArray();
            arguments.add(constant(keys[index]));
            arguments.add(reference(index + 1));
            put.add("arguments", arguments);
            state = put;
        }
        return state;
    }

    private static JsonObject read(JsonObject state, JsonObject key) {
        JsonObject query = relation("READ");
        query.addProperty("_java_type", "L");
        query.add("receiver", state);
        JsonArray arguments = new JsonArray();
        arguments.add(key);
        query.add("arguments", arguments);
        return query;
    }

    // ---- a host that only has to lower leaves --------------------------

    private static final class Recorder implements Host {
        private final List<String> declarations = new ArrayList<>();
        private final List<String> refusals = new ArrayList<>();
        private int minted;

        @Override public Term state(JsonElement identity, Sort shape) {
            return declare("free_state_" + (++minted), shape);
        }

        @Override public Term operand(JsonElement expression, Sort expected) {
            Term value = leaf(expression);
            if (value == null) return null;
            if (expected == Sort.INT && value.sort == Sort.VALUE) {
                return new Term("(valueInt " + value.text + ")", Sort.INT);
            }
            return value;
        }

        @Override public Term box(JsonElement expression) {
            Term value = leaf(expression);
            if (value == null) return null;
            return value.sort == Sort.VALUE ? value
                    : new Term("(VInt " + value.text + ")", Sort.VALUE);
        }

        @Override public Term unbox(Term value, String javaType) {
            return value;
        }

        @Override public void require(String predicate) {
        }

        @Override public Term field(Term owner, String ownerClass,
                                    int fieldOffset, String javaType) {
            return declare("free_field_" + (++minted), Sort.VALUE);
        }

        @Override public void unsupported(String reason) {
            refusals.add(reason);
        }

        private Term leaf(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject node = expression.getAsJsonObject();
            String type = node.get("_type") == null ? ""
                    : node.get("_type").getAsString();
            String raw = node.get("_exp") == null ? ""
                    : node.get("_exp").getAsString();
            if ("ConstExpr".equals(type) && raw.startsWith("Y_I_")) {
                return new Term("(VInt " + raw.substring(4) + ")",
                        Sort.VALUE);
            }
            if ("SymbolExpression".equals(type)) {
                Term reference = declare("entry_" + raw.replaceAll(
                        "[^A-Za-z0-9_]", "_"), Sort.REF);
                return new Term("(VRef " + reference.text + ")", Sort.VALUE);
            }
            unsupported("leaf:" + type);
            return null;
        }

        private Term declare(String name, Sort sort) {
            String smt = sort == Sort.REF ? "Ref"
                    : sort == Sort.ASSOCIATIVE ? "AssocState"
                    : sort == Sort.INDEXED ? "IndexedState"
                    : sort == Sort.INT ? "Int" : "Value";
            String declaration = "(declare-const " + name + " " + smt + ")";
            if (!declarations.contains(declaration)) {
                declarations.add(declaration);
            }
            return new Term(name, sort);
        }
    }

    /** The same preamble the composer emits, plus this host's leaves. */
    private static StringBuilder preambleFor(Recorder host) {
        StringBuilder model = new StringBuilder("(set-logic ALL)\n");
        List<String> entries = new ArrayList<>();
        for (String line : VmTermLowering.preamble(false)) {
            model.append(line).append('\n');
        }
        for (String declaration : host.declarations) {
            model.append(declaration).append('\n');
            // The composer constrains every allocated reference non-null; a
            // snapshot entry that could be nullRef would make "present" and
            // "absent" indistinguishable for reasons the map never had.
            if (declaration.startsWith("(declare-const entry_")) {
                String name = declaration.split(" ")[1];
                model.append("(assert (not (= ").append(name)
                        .append(" nullRef)))\n");
                entries.add(name);
            }
        }
        // Two distinct allocated oops are distinct references, which is what
        // makes two snapshot entries two entries.
        if (entries.size() > 1) {
            model.append("(assert (distinct");
            for (String entry : entries) model.append(' ').append(entry);
            model.append("))\n");
        }
        return model;
    }

    private static String solve(String input) throws Exception {
        Process process = new ProcessBuilder("z3", "-in", "-smt2").start();
        try (java.io.OutputStream stream = process.getOutputStream()) {
            stream.write((input + "(check-sat)\n")
                    .getBytes(java.nio.charset.StandardCharsets.UTF_8));
        }
        java.io.ByteArrayOutputStream output =
                new java.io.ByteArrayOutputStream();
        try (java.io.InputStream stream = process.getInputStream()) {
            byte[] chunk = new byte[256];
            for (int count; (count = stream.read(chunk)) >= 0; ) {
                output.write(chunk, 0, count);
            }
        }
        process.waitFor();
        return new String(output.toByteArray(),
                java.nio.charset.StandardCharsets.UTF_8).trim();
    }

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "-version").start().waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}
