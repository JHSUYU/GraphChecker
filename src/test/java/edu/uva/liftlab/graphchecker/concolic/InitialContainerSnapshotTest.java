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

    /** A two-entry snapshot decides membership for present and absent keys. */
    @Test
    public void aConcreteInitialSnapshotDecidesMembership() {
        Recorder host = new Recorder();
        Term present = ContainerSmtCodec.term(
                read(snapshot(), constant(PRESENT_ONE)), host);
        assertNotNull(present);
        // No free container const survives: the walk ended at the empty base.
        assertTrue(present.text, !present.text.contains("free_state"));
        assertTrue(present.text, present.text.contains("276372523"));

        Term absent = ContainerSmtCodec.term(
                read(snapshot(), constant(ABSENT)), host);
        assertNotNull(absent);
        assertEquals("", host.refusals.toString().replace("[]", ""));
    }

    /** The same two arms, solved: present is non-null and absent is null. */
    @Test
    public void presentKeyIsNonNullAndAbsentKeyIsNull() throws Exception {
        org.junit.Assume.assumeTrue(z3Available());
        Recorder host = new Recorder();
        Term present = ContainerSmtCodec.term(
                read(snapshot(), constant(PRESENT_ONE)), host);
        Term second = ContainerSmtCodec.term(
                read(snapshot(), constant(PRESENT_TWO)), host);
        Term absent = ContainerSmtCodec.term(
                read(snapshot(), constant(ABSENT)), host);

        StringBuilder model = preambleFor(host);

        // A key the snapshot holds cannot read back as null ...
        assertEquals("unsat", solve(model + "(assert (= " + present.text
                + " (VRef nullRef)))\n"));
        assertEquals("unsat", solve(model + "(assert (= " + second.text
                + " (VRef nullRef)))\n"));
        // ... and a key it does not hold cannot read back as anything else.
        assertEquals("unsat", solve(model + "(assert (not (= " + absent.text
                + " (VRef nullRef))))\n"));
        // The two entries are distinct values, so the snapshot is not
        // collapsing every key onto one.
        assertEquals("unsat", solve(model + "(assert (= " + present.text
                + " " + second.text + "))\n"));
    }

    /** An empty snapshot holds nothing, rather than holding anything. */
    @Test
    public void anEmptySnapshotHoldsNothing() throws Exception {
        org.junit.Assume.assumeTrue(z3Available());
        Recorder host = new Recorder();
        Term absent = ContainerSmtCodec.term(
                read(emptyBase(), constant(PRESENT_ONE)), host);
        assertNotNull(absent);
        StringBuilder model = preambleFor(host);
        assertEquals("unsat", solve(model + "(assert (not (= " + absent.text
                + " (VRef nullRef))))\n"));
    }

    /** The truncated form keeps the opaque lowering and says so. */
    @Test
    public void truncationIsDeclaredRatherThanAssumed() {
        JsonObject complete = new JsonObject();
        JsonObject snapshot = new JsonObject();
        snapshot.addProperty("entries", 2);
        snapshot.addProperty("truncated", false);
        complete.add(SharedStateEvidence.INITIAL_SNAPSHOT_FIELD, snapshot);
        assertTrue(SharedStateEvidence.declaresInitialSnapshot(complete));
        assertTrue(!SharedStateEvidence.initialSnapshotTruncated(complete));
        assertEquals(2L,
                SharedStateEvidence.initialSnapshotEntries(complete));

        JsonObject truncated = new JsonObject();
        JsonObject partial = new JsonObject();
        partial.addProperty("entries", 64);
        partial.addProperty("truncated", true);
        truncated.add(SharedStateEvidence.INITIAL_SNAPSHOT_FIELD, partial);
        assertTrue(SharedStateEvidence.initialSnapshotTruncated(truncated));

        // An INITIAL that declares nothing is the old opaque form, and a
        // silent absence must read as truncated rather than as complete.
        JsonObject opaque = new JsonObject();
        assertTrue(!SharedStateEvidence.declaresInitialSnapshot(opaque));
        assertTrue(SharedStateEvidence.initialSnapshotTruncated(opaque));
        assertEquals(-1L, SharedStateEvidence.initialSnapshotEntries(opaque));
    }

    // ---- the recorded shapes -------------------------------------------

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
