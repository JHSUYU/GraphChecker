package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.contract.ExpressionTable;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.IntegralWidth;

import org.junit.Test;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * WIRE-CODEC §6.2 and §6.1, one row per identity, through the one lowering:
 * what a recorded expression lowers to.  "=" expects the text exactly, "~"
 * a fragment of it, "!" a refusal naming the rest (the node lowers as it
 * did before the identities).
 */
public class StringIdentitiesTest {

    private static final JsonObject E = symbol("e", "I");
    private static final JsonObject F = symbol("f", "I");
    private static final JsonObject L = symbol("l", "J");
    private static final JsonObject B = symbol("b", "Z");
    private static final JsonObject S = symbol("s", "java/lang/String");
    private static final JsonObject T = symbol("t", "java/lang/String");

    @Test
    public void everyIdentityLowersExactly() {
        JsonObject saslName = string("concat", string("concat",
                string("toString", E), text(" ")), S, text(" "), T);
        Object[][] rows = {
            {"parseInt of an int's rendering is the int",
                call("java/lang/Integer", "parseInt", string("toString", E)),
                "=e", IntegralWidth.JAVA_INT},
            {"parseLong of an int's rendering widens it",
                call("java/lang/Long", "parseLong", string("toString", E)),
                "=e", IntegralWidth.JAVA_LONG},
            {"a parse node, radix 10, through valueOf, a boundary and an "
                    + "empty literal",
                method("java/lang/Long parseLong", string("concat", text(""),
                        boundary(string("valueOf", L))), integer(10L)),
                "=l", IntegralWidth.JAVA_LONG},
            {"parseInt of a long's rendering is the parse relation",
                call("java/lang/Integer", "parseInt", string("toString", L)),
                "~str.to_int", null},
            {"valueOf of a flag is its rendering",
                string("valueOf", B), "=(ite b \"true\" \"false\")", null},
            {"a primitive concat operand is appended as its rendering",
                string("concat", text("k="), E),
                "=(str.++ \"k=\" (java_int_to_string e))", null},
            {"parseBoolean: true, ignoring case, is the flag",
                string("equalsIgnoreCase", text("true"), string("toString",
                        B)), "=b", null},
            {"FALSE, ignoring case, is its negation",
                string("equalsIgnoreCase", string("toString", B),
                        text("FALSE")), "=(not b)", null},
            {"a literal no flag renders is never equal",
                string("equalsIgnoreCase", string("toString", B),
                        text("yes")), "=false", null},
            {"equals of a flag's rendering and \"true\" is the flag",
                string("equals", string("toString", B), text("true")), "=b",
                null},
            {"split element 0 of the SASL user name is the key id's "
                    + "rendering",
                split(saslName, " ", 0), "=(java_int_to_string e)", null},
            {"and parseInt of it is the key id",
                call("java/lang/Integer", "parseInt", split(saslName, " ", 0)),
                "=e", IntegralWidth.JAVA_INT},
            {"a split element between literals",
                split(string("concat", text("a,"), string("toString", E),
                        text(","), S), ",", 1), "=(java_int_to_string e)",
                null},
            {"a split element that is literal text",
                split(string("concat", text("a,"), S), ",", 0), "=\"a\"",
                null},
            // Past what a template states: found by position
            // (SmtLowering#splitElement), Java's own.
            {"an element after an opaque piece, by position",
                split(saslName, " ", 1), "~str.indexof", null},
            {"no element of a regex split",
                split(string("concat", string("toString", E), text("."), S),
                        ".", 0), "!java/lang/String.splitElement", null},
            {"an element at a delimiter a decimal may hold, by position",
                split(string("concat", string("toString", E), text("-x")),
                        "-", 0), "~str.indexof", null},
            {"equal skeletons compare piece-wise",
                string("equals", string("concat", text("id="),
                        string("toString", E), text(";"), S),
                        string("concat", text("id="), string("toString", F),
                                text(";"), T)),
                "=(and (= e f) (= s t))", null},
            {"a digit after a decimal compares as text",
                string("equals", string("concat", string("toString", E),
                        text("1")), string("concat", string("toString", F),
                        text("1"))), "~str.++", null},
            {"two skeletons compare as text",
                string("equals", string("concat", text("a"),
                        string("toString", E)), string("concat", text("b"),
                        string("toString", F))), "~str.++", null},
        };
        for (Object[] row : rows) {
            String name = (String) row[0];
            String expected = (String) row[2];
            SmtLowering lowering = lowering();
            Term term = lowering.dispatch((JsonObject) row[1], null, "test");
            String refusals = lowering.openRefusals().toString();
            if (expected.startsWith("!")) {
                assertTrue(name + ": " + refusals,
                        refusals.contains(expected.substring(1)));
                continue;
            }
            assertEquals(name + ": " + refusals, "[]", refusals);
            if (expected.startsWith("=")) {
                assertEquals(name, expected.substring(1), term.text);
            } else {
                assertTrue(name + ": " + term.text,
                        term.text.contains(expected.substring(1)));
            }
            if (row[3] != null) {
                assertEquals(name + ": width", row[3], term.integralWidth);
            }
        }
    }

    /**
     * A LONG TEXT IS A NAME ({@code SmtLowering#compact}): a substring writes
     * its receiver's text into its result, its length twice and its
     * definedness, so forty nested substrings held by value were ~4^40
     * (solr-adhoc-10 SL2: a parse of a handoff's string outgrew 24 GB).
     * Past the size, a text is a define-fun the query states once: the
     * chain's own text stays short, and what it reaches still ends at the
     * symbol it parses.
     */
    @Test(timeout = 30000)
    public void aSubstringChainNamesWhatItRepeats() {
        JsonObject chain = S;
        for (int level = 0; level < 40; level++) {
            chain = string("substring", chain, integer(1));
        }
        SmtLowering lowering = lowering();
        Term term = lowering.dispatch(chain, null, "test");
        assertEquals("[]", lowering.openRefusals().toString());
        assertTrue("the chain's text is short: " + term.text.length(),
                term.text.length() < 4 * SmtLowering.NAMED_TEXT_CHARS);
        assertTrue("and its definedness: " + term.precondition.length(),
                term.precondition.length() < 4 * SmtLowering.NAMED_TEXT_CHARS);
        StringBuilder stated = new StringBuilder();
        for (SmtLowering.Declaration declaration : lowering.reachedBy(
                Arrays.asList(term.text, term.precondition))) {
            stated.append(declaration.render()).append('\n');
        }
        assertTrue("its define-funs state the substrings down to s: "
                        + stated.length(), stated.toString().contains(
                "(str.substr s 1 ") && stated.length()
                < 100 * SmtLowering.NAMED_TEXT_CHARS);
    }

    /** §6.1: a recorded value is a literal of the sort it is read at. */
    @Test
    public void aLiteralIsOfItsSort() {
        Object[][] rows = {
            {"1", Sort.BOOL, "true"}, {"false", Sort.BOOL, "false"},
            {"2", Sort.BOOL, ""}, {"-7", Sort.INT, "(- 7)"},
            {"true", Sort.INT, ""}, {"\"a\\\"b\"", Sort.STRING, "\"a\"\"b\""},
            {"N", Sort.STRING, ""}, {"5", Sort.REF, ""},
            // A reference's one literal is null; a named object is a symbol.
            {"N", Sort.REF, "nullRef"}, {"M_L'a.B'_7", Sort.REF, ""},
        };
        for (Object[] row : rows) {
            assertEquals(row[0] + " as " + row[1], row[2],
                    VmTermLowering.smtLiteral((String) row[0], (Sort) row[1]));
        }
    }

    private static SmtLowering lowering() {
        Map<String, Sort> declared = new LinkedHashMap<String, Sort>();
        declared.put("e", Sort.INT);
        declared.put("f", Sort.INT);
        declared.put("l", Sort.INT);
        declared.put("b", Sort.BOOL);
        declared.put("s", Sort.STRING);
        declared.put("t", Sort.STRING);
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

    private static JsonObject text(String value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConStringSymbolExp");
        node.addProperty("_exp", "Y_L'String'_" + value);
        node.addProperty("_java_type", "java/lang/String");
        return node;
    }

    private static JsonObject integer(long value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_exp", "Y_I_" + value);
        node.addProperty("_java_type", "I");
        return node;
    }

    private static JsonObject string(String name, JsonObject... params) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "OpStrExpression");
        node.addProperty("_name", name);
        node.addProperty("_is_not", false);
        node.add("_param_list", list(params));
        return node;
    }

    /** A method-return symbol stating its call (VM f14). */
    private static JsonObject call(String holder, String name,
                                   JsonObject... arguments) {
        boolean parseInt = "parseInt".equals(name);
        JsonObject returned = symbol(parseInt ? "M_I_return1" : "M_J_return1",
                parseInt ? "I" : "J");
        JsonObject call = new JsonObject();
        call.addProperty("holder", holder);
        call.addProperty("name", name);
        call.add("arguments", list(arguments));
        returned.add("call", call);
        return returned;
    }

    private static JsonObject method(String name, JsonObject... params) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "MethodExpression");
        node.addProperty("_name", name);
        node.add("_param_list", list(params));
        node.add("_res_exp", symbol("M_J_return2", "J"));
        return node;
    }

    private static JsonObject split(JsonObject receiver, String regex,
                                    long index) {
        JsonObject node = method("java/lang/String splitElement", receiver,
                text(regex), integer(index));
        node.add("_res_exp", text("?"));
        return node;
    }

    private static JsonObject boundary(JsonObject expression) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConsumerBoundaryExpression");
        node.addProperty("_java_type", "Ljava/lang/String;");
        node.add("expression", expression);
        return node;
    }

    private static JsonArray list(JsonObject... nodes) {
        JsonArray list = new JsonArray();
        for (JsonObject node : nodes) list.add(node);
        return list;
    }
}
