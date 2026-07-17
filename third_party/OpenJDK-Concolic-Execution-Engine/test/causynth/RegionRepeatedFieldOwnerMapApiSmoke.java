import java.util.HashMap;
import java.util.Map;

/**
 * Verifies that one Java field declaration can be symbolized independently
 * on several concrete owners during one concolic region.  The runtime region
 * planner relies on this property when a static field-family input is refined
 * into occurrence-specific container-element bindings.
 */
public final class RegionRepeatedFieldOwnerMapApiSmoke {
    private static final class Key {
        private int keyId;

        private Key(int keyId) {
            this.keyId = keyId;
        }
    }

    public static void main(String[] args) {
        Key[] keys = new Key[] {
                new Key(11), new Key(12), new Key(13), new Key(14)
        };
        Map<Integer, Key> values = new HashMap<Integer, Key>();

        System.startConcolicRegion("REGION.repeated-field-owner-map",
                "ACT.repeated-field-owner-map");
        for (int index = 0; index < keys.length; index++) {
            String symbol = "container_key_index_" + index;
            System.symbolizeField(keys[index], "keyId", symbol);
            values.put(keys[index].keyId, keys[index]);
        }
        String summary = System.finishConcolicRegion();

        require(values.size() == 4, "concrete map size");
        for (int index = 0; index < keys.length; index++) {
            String symbol = "container_key_index_" + index;
            String put = methodObjectContaining(summary,
                    "java/util/HashMap put", symbol);
            require(put.contains(symbol), put);
        }
        System.out.println(
                "CAUSYNTH_REGION_REPEATED_FIELD_OWNER_MAP_API_SMOKE_OK");
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
