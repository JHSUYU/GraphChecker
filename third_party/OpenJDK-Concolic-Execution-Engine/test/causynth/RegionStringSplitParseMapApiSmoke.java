import java.util.HashMap;
import java.util.Map;

/**
 * General regression for String.split element provenance followed by
 * Integer.parseInt, boxing, and a Map consumer.
 *
 * This test proves structural provenance, not the mathematical semantics of
 * regex splitting or integer parsing: a parse's result is a return symbol
 * stating its call, whose argument is the split element, and it keys the
 * map's PUT.
 */
public final class RegionStringSplitParseMapApiSmoke {
    public static void main(String[] args) {
        String decimalInput = new String("7004:decimal");
        String radixInput = new String("1b59,radix");
        Map<Integer, String> values = new HashMap<Integer, String>();

        System.startConcolicRegion("REGION.string-split-parse-map",
                "ACT.string-split-parse-map");
        String[] concreteParts = new String("11:concrete").split(":");
        require(concreteParts.length == 2
                && "concrete".equals(concreteParts[1]),
                "concrete split before symbolization");
        System.symbolize(decimalInput, "split_parse_decimal");
        System.symbolize(radixInput, "split_parse_radix");

        String[] decimalParts = decimalInput.split(":");
        int decimalKey = Integer.parseInt(decimalParts[0]);
        values.put(decimalKey, decimalParts[1]);

        String[] radixParts = radixInput.split(",", 3);
        int radixKey = Integer.parseInt(radixParts[0], 16);
        values.put(radixKey, radixParts[1]);

        String decimalValue = values.get(decimalKey);
        String radixValue = values.get(radixKey);
        String mapRelation = System.getSymbolicExpression(values);
        String readRelation = System.getSymbolicExpression(decimalValue);
        System.finishConcolicRegion();
        require("decimal".equals(decimalValue), "decimal lookup");
        require("radix".equals(radixValue), "radix lookup");
        String decimalParse = methodObjectContaining(mapRelation,
                "java/lang/Integer parseInt", "split_parse_decimal");
        require(decimalParse.contains(
                "\"_name\":\"java/lang/String splitElement\""),
                decimalParse);
        require(decimalParse.contains("split_parse_decimal"), decimalParse);
        require(decimalParse.contains("Y_L'String'_:"), decimalParse);
        require(decimalParse.contains("\"_exp\":\"Y_I_0\""),
                decimalParse);

        String radixParse = methodObjectContaining(mapRelation,
                "java/lang/Integer parseInt", "split_parse_radix");
        require(radixParse.contains(
                "\"_name\":\"java/lang/String splitElement\""),
                radixParse);
        require(radixParse.contains("split_parse_radix"), radixParse);
        require(radixParse.contains("Y_L'String'_,"), radixParse);
        require(radixParse.contains("\"_exp\":\"Y_I_3\""),
                radixParse);
        require(radixParse.contains("\"_exp\":\"Y_I_0\""),
                radixParse);
        require(radixParse.contains("\"_exp\":\"Y_I_16\""),
                radixParse);

        require(mapRelation.contains("\"operation\":\"PUT\""), mapRelation);
        require(readRelation.contains("\"operation\":\"READ\""),
                readRelation);
        System.out.println("CAUSYNTH_REGION_STRING_SPLIT_PARSE_MAP_API_SMOKE_OK");
    }

    /** The call a return symbol states, of `method`, reaching `marker`. */
    private static String methodObjectContaining(String json, String method,
                                                  String marker) {
        String[] callee = method.split(" ");
        String needle = "\"call\":{\"holder\":\"" + callee[0]
                + "\",\"name\":\"" + callee[1] + "\"";
        int offset = 0;
        while (offset < json.length()) {
            int name = json.indexOf(needle, offset);
            if (name < 0) break;
            int start = name + 7;
            if (start >= 0) {
                String object = jsonObjectAt(json, start);
                String reachable = reachableText(json, object);
                if (reachable.contains(marker)) return reachable;
            }
            offset = name + needle.length();
        }
        throw new AssertionError("missing method object " + method
                + " containing " + marker + ": " + json);
    }

    private static String jsonObjectAt(String json, int start) {
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
                continue;
            }
            if (current == '"') {
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

    /** Local node definitions reachable from one expression, each once. */
    private static String reachableText(String artifact, String root) {
        StringBuilder result = new StringBuilder();
        collectReachable(artifact, root, result,
                new java.util.HashSet<String>());
        return result.toString();
    }

    private static void collectReachable(
            String artifact, String value, StringBuilder result,
            java.util.Set<String> visited) {
        if (value == null) return;
        result.append(value);
        String marker = "\"_type\":\"VmExpressionReference\"";
        int offset = 0;
        while ((offset = value.indexOf(marker, offset)) >= 0) {
            int start = value.lastIndexOf('{', offset);
            String reference = jsonObjectAt(value, start);
            String session = scalar(reference, "sessionId");
            String expression = scalar(reference, "expressionId");
            String identity = session + "/" + expression;
            if (visited.add(identity)) {
                String definition = definitionOf(
                        artifact, session, expression);
                require(definition != null,
                        "missing VM expression definition " + identity);
                collectReachable(artifact, definition, result, visited);
            }
            offset = start + reference.length();
        }
    }

    private static String definitionOf(String artifact, String session,
                                       String expression) {
        String prefix = "\"_type\":\"VmExpressionDefinition\","
                + "\"sessionId\":" + session + ","
                + "\"expressionId\":" + expression + ","
                + "\"expression\":";
        int at = artifact.indexOf(prefix);
        if (at < 0) return null;
        int value = at + prefix.length();
        return jsonObjectAt(artifact, value);
    }

    private static String scalar(String object, String key) {
        String needle = "\"" + key + "\":";
        int start = object.indexOf(needle);
        if (start < 0) return null;
        start += needle.length();
        int end = start;
        while (end < object.length()
                && ",}".indexOf(object.charAt(end)) < 0) {
            end++;
        }
        return object.substring(start, end);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
