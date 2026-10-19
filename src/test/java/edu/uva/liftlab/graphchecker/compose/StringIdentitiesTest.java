package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.smt.Z3;

import org.junit.Assume;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class StringIdentitiesTest {

    private static final JsonObject E = symbol("e", "I");
    private static final JsonObject L = symbol("l", "J");

    @Test
    public void anUnsignedRadixRenderingIsJavas() throws Exception {
        Assume.assumeTrue(z3Available());
        String hex = "unsupportedPrimitiveStringConversion:java/lang/Integer"
                + ".toHexString(I)Ljava/lang/String;";
        String longHex = "unsupportedPrimitiveStringConversion:java/lang/Long"
                + ".toHexString(J)Ljava/lang/String;";
        String binary = "unsupportedPrimitiveStringConversion:java/lang/"
                + "Integer.toBinaryString(I)Ljava/lang/String;";
        String octal = "unsupportedPrimitiveStringConversion:java/lang/Long"
                + ".toOctalString(J)Ljava/lang/String;";
        Object[][] rows = {
            {hex, E, 0L, Integer.toHexString(0)},
            {hex, E, 255L, Integer.toHexString(255)},
            {hex, E, -1L, Integer.toHexString(-1)},
            {hex, E, (long) Integer.MIN_VALUE,
                    Integer.toHexString(Integer.MIN_VALUE)},
            {longHex, L, -2L, Long.toHexString(-2L)},
            {binary, E, 5L, Integer.toBinaryString(5)},
            {octal, L, 4096L, Long.toOctalString(4096L)},
        };
        for (Object[] row : rows) {
            SmtLowering lowering = lowering();
            Term term = lowering.dispatch(string((String) row[0],
                    (JsonObject) row[1]), null, "test");
            assertEquals("[]", lowering.openRefusals().toString());
            String variable = ((JsonObject) row[1]).get("_exp").getAsString();
            StringBuilder query = new StringBuilder();
            for (SmtLowering.Declaration declaration : lowering.reachedBy(
                    Arrays.asList(term.text, term.precondition))) {
                query.append(declaration.render()).append('\n');
            }
            query.append("(assert (= ").append(variable).append(' ')
                    .append(smtInteger((Long) row[2]))
                    .append("))\n(assert (not (= ").append(term.text)
                    .append(" \"").append(row[3]).append("\")))\n");
            Z3.Answer answer = new Z3(Paths.get("z3"), 30000L, 2048).ask(
                    query.toString(), Collections.<String>emptyList(), false);
            assertTrue(row[0] + " of " + row[2] + ": " + answer.status(),
                    answer.unsat());
        }
    }

    private static String smtInteger(long value) {
        return value < 0 ? "(- " + (-value) + ")" : Long.toString(value);
    }

    private static boolean z3Available() {
        try {
            return new ProcessBuilder("z3", "-version").start().waitFor() == 0;
        } catch (IOException | InterruptedException unavailable) {
            return false;
        }
    }

    private static SmtLowering lowering() {
        Map<String, Sort> declared = new LinkedHashMap<String, Sort>();
        declared.put("e", Sort.INT);
        declared.put("l", Sort.INT);
        SmtLowering lowering = new SmtLowering(declared);
        lowering.begin("t", SmtLowering.NO_JOIN, ExpressionTable.empty());
        return lowering;
    }

    private static JsonObject symbol(String name, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", name);
        node.addProperty("_java_type", javaType);
        return node;
    }

    private static JsonObject string(String name, JsonObject... params) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "OpStrExpression");
        node.addProperty("_name", name);
        node.addProperty("_is_not", false);
        JsonArray list = new JsonArray();
        for (JsonObject param : params) list.add(param);
        node.add("_param_list", list);
        return node;
    }
}
