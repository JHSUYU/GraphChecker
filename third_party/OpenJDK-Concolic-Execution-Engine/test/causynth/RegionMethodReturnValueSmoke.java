/**
 * The result of a call the VM does not model states the value it returned.
 *
 * <p>Integer.parseInt and Long.parseLong of a symbolic String mint a fresh
 * return symbol, tied to the String only by the MethodExpression recorded
 * beside it.  Nothing else declares that symbol, so the composer cut
 * SOLR-18406's SolrParams.getLong of a request parameter (M_J_return28) as
 * an undeclared free symbol.  The symbol now states what the call returned
 * as `concreteValue`, spelled as a read states it: the constant's node.  A
 * negative int and longs past 2^32 show the whole word is taken from the
 * result, not a slot beside it.</p>
 */
public final class RegionMethodReturnValueSmoke {
    public static void main(String[] args) {
        String negativeInt = new String("-42");
        String hexInt = new String("-1b");
        String wideLong = new String("6000000123");
        String negativeLong = new String("-5000000000");

        System.startConcolicRegion("REGION.method-return-value",
                "TASK.method-return-value");
        System.symbolize(negativeInt, "negative_int_text");
        System.symbolize(hexInt, "hex_int_text");
        System.symbolize(wideLong, "wide_long_text");
        System.symbolize(negativeLong, "negative_long_text");
        int parsedNegativeInt = Integer.parseInt(negativeInt);
        int parsedHexInt = Integer.parseInt(hexInt, 16);
        long parsedWideLong = Long.parseLong(wideLong);
        long parsedNegativeLong = Long.parseLong(negativeLong);
        String summary = System.finishConcolicRegion();

        require(parsedNegativeInt == -42 && parsedHexInt == -27
                        && parsedWideLong == 6000000123L
                        && parsedNegativeLong == -5000000000L,
                "the parses returned the wrong values");
        requireReturn(summary, "java/lang/Integer parseInt",
                "negative_int_text", "I", "Y_I_" + parsedNegativeInt);
        requireReturn(summary, "java/lang/Integer parseInt",
                "hex_int_text", "I", "Y_I_" + parsedHexInt);
        String wide = requireReturn(summary, "java/lang/Long parseLong",
                "wide_long_text", "J", "Y_J_" + parsedWideLong);
        requireReturn(summary, "java/lang/Long parseLong",
                "negative_long_text", "J", "Y_J_" + parsedNegativeLong);
        System.out.println("METHOD_RETURN " + wide);
        System.out.println("RegionMethodReturnValueSmoke OK");
    }

    /**
     * The return symbol of the `method` call on the String named `marker`,
     * checked to state `constant`; returns its definition and the constant's.
     */
    private static String requireReturn(String summary, String method,
                                        String marker, String javaType,
                                        String constant) {
        String call = methodObject(summary, method, marker);
        String symbol = resolve(summary,
                jsonObjectAt(call, valueAt(call, "_res_exp")));
        require(symbol.contains("\"_type\":\"SymbolExpression\"")
                        && symbol.contains("\"_java_type\":\"" + javaType
                                + "\"")
                        && symbol.contains("\"_exp\":\"M_" + javaType
                                + "_return"),
                "the call's result is not a return symbol: " + symbol);
        int stated = valueAt(symbol, "concreteValue");
        require(stated >= 0, "the return symbol states no value: " + symbol);
        String value = resolve(summary, jsonObjectAt(symbol, stated));
        require(value.contains("\"_type\":\"ConstExpr\"")
                        && value.contains("\"_exp\":\"" + constant + "\""),
                "the return symbol states " + value + ", not " + constant);
        return symbol + " -> " + value;
    }

    /** The MethodExpression of `method` whose arguments reach `marker`. */
    private static String methodObject(String json, String method,
                                       String marker) {
        String needle = "\"_name\":\"" + method + "\"";
        int offset = 0;
        while ((offset = json.indexOf(needle, offset)) >= 0) {
            String object = jsonObjectAt(json, json.lastIndexOf('{', offset));
            if (reaches(json, object, marker,
                    new java.util.HashSet<String>())) {
                return object;
            }
            offset += needle.length();
        }
        throw new AssertionError("missing " + method + " of " + marker
                + ": " + json);
    }

    private static boolean reaches(String artifact, String value,
                                   String marker,
                                   java.util.Set<String> visited) {
        if (value.contains(marker)) return true;
        String reference = "\"_type\":\"VmExpressionReference\"";
        int offset = 0;
        while ((offset = value.indexOf(reference, offset)) >= 0) {
            String object = jsonObjectAt(value, value.lastIndexOf('{', offset));
            if (visited.add(object)
                    && reaches(artifact, resolve(artifact, object), marker,
                            visited)) {
                return true;
            }
            offset += reference.length();
        }
        return false;
    }

    /** A reference's definition in the table, or the value itself. */
    private static String resolve(String artifact, String value) {
        if (!value.startsWith("{\"_type\":\"VmExpressionReference\"")) {
            return value;
        }
        String prefix = "\"_type\":\"VmExpressionDefinition\","
                + "\"sessionId\":" + scalar(value, "sessionId") + ","
                + "\"expressionId\":" + scalar(value, "expressionId") + ","
                + "\"expression\":";
        int at = artifact.indexOf(prefix);
        require(at >= 0, "missing definition of " + value);
        return jsonObjectAt(artifact, at + prefix.length());
    }

    /** Where the value of `key` starts in `object`, or -1. */
    private static int valueAt(String object, String key) {
        int at = object.indexOf("\"" + key + "\":");
        return at < 0 ? -1 : at + key.length() + 3;
    }

    private static String jsonObjectAt(String json, int start) {
        require(start >= 0 && json.charAt(start) == '{',
                "no object at " + start + ": " + json);
        int depth = 0;
        boolean inString = false;
        boolean escaped = false;
        for (int index = start; index < json.length(); index++) {
            char current = json.charAt(index);
            if (inString) {
                if (escaped) {
                    escaped = false;
                } else if (current == '\\') {
                    escaped = true;
                } else if (current == '"') {
                    inString = false;
                }
            } else if (current == '"') {
                inString = true;
            } else if (current == '{') {
                depth++;
            } else if (current == '}' && --depth == 0) {
                return json.substring(start, index + 1);
            }
        }
        throw new AssertionError("unterminated JSON object: "
                + json.substring(start));
    }

    private static String scalar(String object, String key) {
        int start = valueAt(object, key);
        int end = start;
        while (",}".indexOf(object.charAt(end)) < 0) end++;
        return object.substring(start, end);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
