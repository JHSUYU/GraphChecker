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

    /**
     * A container that held nothing is stated, not unknown.
     *
     * <p>HDFS-17960's fatal read stands on
     * {@code DirectorySnapshottableFeature#snapshotsByNames}, an
     * {@code ArrayList} the VM walked completely at selection and found
     * empty.  Its complete content is therefore the bare
     * {@code SNAPSHOT_BASE}, which already lowers to the exact empty list -
     * but the VM summarizes a snapshot by its member count, and the count of
     * an empty one is the same zero it reports for a container it never
     * stated.  Reading that summary alone called the most tightly pinned
     * carrier in the run "undetermined", so the value itself decides.</p>
     */
    @Test
    public void anEmptyStatedContentIsCompleteRatherThanTruncated() {
        JsonObject empty = new JsonObject();
        empty.add("expression", indexedBase());
        assertTrue(SharedStateEvidence.declaresInitialSnapshot(empty));
        assertTrue(!SharedStateEvidence.initialSnapshotTruncated(empty));
        assertEquals(0L, SharedStateEvidence.initialSnapshotEntries(empty));

        // The same reading counts a non-empty chain the VM summarized the
        // same way, so the two answers cannot disagree about one snapshot.
        JsonObject stated = new JsonObject();
        stated.add("expression", rootedSnapshot());
        assertTrue(!SharedStateEvidence.initialSnapshotTruncated(stated));
        assertEquals(2L, SharedStateEvidence.initialSnapshotEntries(stated));
    }

    /** Everything that does not stand on the base stays truncated. */
    @Test
    public void anUnstatedInitialContentStaysTruncated() {
        // The bare opaque root: nothing was ever stated about it.
        JsonObject bare = new JsonObject();
        bare.add("expression", stateRoot());
        assertTrue(!SharedStateEvidence.declaresInitialSnapshot(bare));
        assertTrue(SharedStateEvidence.initialSnapshotTruncated(bare));
        assertEquals(-1L, SharedStateEvidence.initialSnapshotEntries(bare));

        // A mutation history the recorder merely watched is not a statement
        // of what was in there before it started watching.
        JsonObject watched = new JsonObject();
        JsonObject append = relation("APPEND");
        append.add("receiver", stateRoot());
        JsonArray arguments = new JsonArray();
        arguments.add(constant(PRESENT_ONE));
        append.add("arguments", arguments);
        watched.add("expression", append);
        assertTrue(SharedStateEvidence.initialSnapshotTruncated(watched));

        // A version with no value at all cannot be read as complete.
        assertTrue(SharedStateEvidence.initialSnapshotTruncated(
                new JsonObject()));

        // And a declared refusal still wins over whatever the value shows:
        // the bound refused the content before any base was installed.
        JsonObject refused = new JsonObject();
        JsonObject partial = new JsonObject();
        partial.addProperty("entries", 64);
        partial.addProperty("truncated", true);
        refused.add(SharedStateEvidence.INITIAL_SNAPSHOT_FIELD, partial);
        refused.add("expression", rootedSnapshot());
        assertTrue(SharedStateEvidence.initialSnapshotTruncated(refused));
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
