package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec.Host;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec.Sort;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec.Term;
import org.junit.Assume;
import org.junit.Test;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertTrue;

/**
 * HDFS-11741 removal story: {@code allKeys.get(keyId)} over a map where keyId
 * was PUT and then conditionally removed by {@code removeExpiredKeys} under the
 * recorded symbolic branch {@code expiry &lt; now} (a {@code REMOVE_IF} op).
 * The codec lowers the read so that the guard is a free choice: z3 selects the
 * arm where the remove fired ({@code expiry &lt; now}) and the read is null --
 * the throw -- while forcing the guard false keeps the key present.  This is
 * the composer's consumption half of the conditional-remove contract; the VM
 * change that emits {@code REMOVE_IF} is tracked separately.
 */
public class ContainerSmtCodecRemoveIfTest {

    private static final int KEY_ID = 534995622;
    private static final long NOW = 1787738510917L;

    @Test
    public void flippingTheExpiryGuardMakesTheGetNull() throws Exception {
        // get( REMOVE_IF( PUT(STATE(base), keyId, present), keyId,
        //                 guard = (expiry < now) ),
        //      keyId )
        JsonObject present = ref("present_key");
        JsonObject put = assoc("PUT", state("base"),
                args(intConst(KEY_ID), present), null);
        JsonObject guard = binary("<", intSymbol("EXPIRY"), longConst(NOW));
        JsonObject removeIf = assoc("REMOVE_IF", put,
                args(intConst(KEY_ID)), guard);
        JsonObject get = assoc("READ", removeIf, args(intConst(KEY_ID)), null);

        TestHost host = new TestHost();
        Term read = ContainerSmtCodec.term(get, host);
        assertTrue("the get lowered", read != null);

        // The throw: read == null must be satisfiable, and it must force the
        // guard true (expiry < now) -- the removal fired.
        String sat = solve(host, read,
                "(assert (= " + read.text + " (VRef nullRef)))",
                "(check-sat)", "(get-value (sym_EXPIRY))");
        assertTrue("expiry < now must be a reachable throw: " + sat,
                sat.startsWith("sat"));

        // And it is genuinely conditional: forcing the guard false (the key is
        // NOT expired) makes the same read return the present value, not null.
        String noThrow = solve(host, read,
                // the recorded present value is a real, non-null BlockKey
                "(assert (not (= present_key nullRef)))",
                "(assert (not (< sym_EXPIRY " + NOW + ")))",
                "(assert (= " + read.text + " (VRef nullRef)))",
                "(check-sat)");
        assertTrue("with the key un-expired the get is not null: " + noThrow,
                noThrow.startsWith("unsat"));
    }

    // ------------------------------------------------------------------
    // A minimal Host: lowers exactly the expressions this fixture builds.
    // ------------------------------------------------------------------
    private static final class TestHost implements Host {
        private final List<String> decls = new ArrayList<>();
        private final List<String> requires = new ArrayList<>();
        private JsonObject lastReadFrom;

        @Override public Term state(JsonElement identity, Sort shape) {
            String name = "base_state";
            declare(name, "AssocState");
            return new Term(name, Sort.ASSOCIATIVE);
        }

        @Override public Term operand(JsonElement expression, Sort expected) {
            JsonObject o = expression.getAsJsonObject();
            String type = o.get("_type").getAsString();
            if ("ContainerRelation".equals(type)) {
                return ContainerSmtCodec.term(o, this);
            }
            if ("ReadFromExpression".equals(type)) {
                lastReadFrom = o.deepCopy();
                declare("base_state", "AssocState");
                return new Term("base_state", Sort.ASSOCIATIVE);
            }
            if ("BinaryExpression".equals(type)) {
                Term l = operand(o.get("_left"), Sort.INT);
                Term r = operand(o.get("_right"), Sort.INT);
                return new Term("(" + o.get("_op").getAsString() + " "
                        + l.text + " " + r.text + ")", Sort.BOOL);
            }
            if ("SymbolExpression".equals(type)) {
                String name = "sym_" + o.get("_exp").getAsString();
                declare(name, "Int");
                return new Term(name, Sort.INT);
            }
            if ("ConstExpr".equals(type)) {
                return new Term(payload(o), Sort.INT);
            }
            throw new IllegalStateException("unhandled operand " + type);
        }

        @Override public Term box(JsonElement expression) {
            JsonObject o = expression.getAsJsonObject();
            String type = o.get("_type").getAsString();
            if ("ConstExpr".equals(type)
                    && "I".equals(o.get("_java_type").getAsString())) {
                return new Term("(VInt " + payload(o) + ")", Sort.VALUE);
            }
            if ("ref".equals(type)) {
                String name = o.get("name").getAsString();
                declare(name, "Ref");
                return new Term("(VRef " + name + ")", Sort.VALUE);
            }
            throw new IllegalStateException("unhandled box " + type);
        }

        @Override public Term unbox(Term value, String javaType) {
            return value;
        }

        @Override public void require(String predicate) {
            requires.add(predicate);
        }

        @Override public Term field(Term owner, String ownerClass,
                                    int fieldOffset, String javaType) {
            throw new IllegalStateException("no field access in this fixture");
        }

        @Override public void unsupported(String reason) {
            throw new IllegalStateException("unsupported: " + reason);
        }

        private void declare(String name, String sort) {
            String decl = "(declare-const " + name + " " + sort + ")";
            if (!decls.contains(decl)) decls.add(decl);
        }
    }

    private String solve(TestHost host, Term read, String... tail)
            throws Exception {
        Path z3 = z3();
        Assume.assumeTrue("z3 is required", z3 != null);
        StringBuilder smt = new StringBuilder();
        smt.append("(declare-sort Ref 0)\n");
        smt.append(ContainerSmtCodec.valueDatatypeDeclaration()).append('\n');
        for (String line : ContainerSmtCodec.preamble()) {
            smt.append(line).append('\n');
        }
        smt.append("(declare-const nullRef Ref)\n");
        for (String decl : host.decls) smt.append(decl).append('\n');
        for (String pred : host.requires) {
            smt.append("(assert ").append(pred).append(")\n");
        }
        for (String line : tail) smt.append(line).append('\n');
        Path file = Files.createTempFile("removeif", ".smt2");
        Files.write(file, smt.toString().getBytes(StandardCharsets.UTF_8));
        Process p = new ProcessBuilder(z3.toString(), "-smt2",
                file.toString()).redirectErrorStream(true).start();
        StringBuilder out = new StringBuilder();
        try (BufferedReader r = new BufferedReader(new InputStreamReader(
                p.getInputStream(), StandardCharsets.UTF_8))) {
            String line;
            while ((line = r.readLine()) != null) {
                out.append(line).append('\n');
            }
        }
        p.waitFor();
        return out.toString().trim();
    }

    private static Path z3() {
        for (String candidate : new String[]{"/usr/local/bin/z3",
                "/usr/bin/z3"}) {
            Path path = Paths.get(candidate);
            if (Files.isExecutable(path)) return path;
        }
        return null;
    }

    // ---- expression builders ----
    private static JsonObject assoc(String op, JsonElement receiver,
                                    JsonArray arguments, JsonObject guard) {
        JsonObject o = new JsonObject();
        o.addProperty("_type", "ContainerRelation");
        o.addProperty("shape", "ASSOCIATIVE");
        o.addProperty("operation", op);
        o.addProperty("_java_type", "L");
        o.add("receiver", receiver);
        o.add("arguments", arguments);
        if (guard != null) o.add("guard", guard);
        return o;
    }

    private static JsonObject state(String symbol) {
        JsonObject id = new JsonObject();
        id.addProperty("_type", "SymbolExpression");
        id.addProperty("_java_type", "java/util/HashMap");
        id.addProperty("_exp", symbol);
        return assoc("STATE", id, new JsonArray(), null);
    }

    private static JsonArray args(JsonElement... items) {
        JsonArray a = new JsonArray();
        for (JsonElement item : items) a.add(item);
        return a;
    }

    private static JsonObject intConst(int v) {
        JsonObject o = new JsonObject();
        o.addProperty("_type", "ConstExpr");
        o.addProperty("_java_type", "I");
        o.addProperty("_exp", "Y_I_" + v);
        return o;
    }

    private static JsonObject longConst(long v) {
        JsonObject o = new JsonObject();
        o.addProperty("_type", "ConstExpr");
        o.addProperty("_java_type", "J");
        o.addProperty("_exp", "Y_J_" + v);
        return o;
    }

    private static JsonObject intSymbol(String name) {
        JsonObject o = new JsonObject();
        o.addProperty("_type", "SymbolExpression");
        o.addProperty("_java_type", "I");
        o.addProperty("_exp", name);
        return o;
    }

    private static JsonObject ref(String name) {
        JsonObject o = new JsonObject();
        o.addProperty("_type", "ref");
        o.addProperty("name", name);
        return o;
    }

    private static JsonObject binary(String op, JsonElement l, JsonElement r) {
        JsonObject o = new JsonObject();
        o.addProperty("_type", "BinaryExpression");
        o.addProperty("_op", op);
        o.add("_left", l);
        o.add("_right", r);
        return o;
    }

    private static String payload(JsonObject constant) {
        String raw = constant.get("_exp").getAsString();
        int first = raw.indexOf('_');
        int second = first < 0 ? -1 : raw.indexOf('_', first + 1);
        return second < 0 ? raw : raw.substring(second + 1);
    }
}
