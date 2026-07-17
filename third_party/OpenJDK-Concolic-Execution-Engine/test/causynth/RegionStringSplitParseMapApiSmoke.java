import java.util.HashMap;
import java.util.Map;

/**
 * General regression for String.split element provenance followed by
 * Integer.parseInt, boxing, and a Map consumer.
 *
 * This test proves structural provenance, not the mathematical semantics of
 * regex splitting or integer parsing.  Until a downstream encoder supplies
 * validated split/parseInt semantics, it must treat these MethodExpressions
 * as unsupported for semantic solving (fail closed), not as a proven inverse.
 */
public final class RegionStringSplitParseMapApiSmoke {
    public static void main(String[] args) {
        String decimalInput = new String("7004:decimal");
        String radixInput = new String("1b59,radix");
        Map<Integer, String> values = new HashMap<Integer, String>();

        System.startConcolicRegion("REGION.string-split-parse-map",
                "ACT.string-split-parse-map");
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
        String summary = System.finishConcolicRegion();
        require("decimal".equals(decimalValue), "decimal lookup");
        require("radix".equals(radixValue), "radix lookup");
        String decimalParse = methodObjectContaining(summary,
                "java/lang/Integer parseInt", "split_parse_decimal");
        require(decimalParse.contains(
                "\"_name\":\"java/lang/String splitElement\""),
                decimalParse);
        require(decimalParse.contains("split_parse_decimal"), decimalParse);
        require(decimalParse.contains("Y_L'String'_:"), decimalParse);
        require(decimalParse.contains("\"_exp\":\"Y_I_0\""),
                decimalParse);

        String radixParse = methodObjectContaining(summary,
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

        require(summary.contains("java/util/HashMap put"), summary);
        require(summary.contains("java/util/HashMap get"), summary);
        require(!summary.contains("P_L'java/lang/Integer'_"), summary);
        System.out.println("CAUSYNTH_REGION_STRING_SPLIT_PARSE_MAP_API_SMOKE_OK");
    }

    private static String methodObjectContaining(String json, String method,
                                                  String marker) {
        String needle = "\"_name\":\"" + method + "\"";
        int offset = 0;
        while (offset < json.length()) {
            int name = json.indexOf(needle, offset);
            if (name < 0) break;
            int start = json.lastIndexOf('{', name);
            if (start >= 0) {
                String object = jsonObjectAt(json, start);
                if (object.contains(marker)) return object;
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

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
