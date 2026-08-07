package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Alpha-renames one summary's canonical port tokens to the exact ports of a
 * single activation.
 *
 * <p>One region template activating twice is one summary instantiated at two
 * exact ports, so the rename is the same judgement wherever it is applied:
 * object members, string values and embedded tokens delimited by {@code _}
 * all move together.  Renaming in only one of those places would leave a
 * summary half-bound to the wrong activation.</p>
 */
final class PortAlphaRenaming {
    private PortAlphaRenaming() {
    }

    /**
     * Rewrites every canonical port token in {@code value}.
     *
     * @param collision message prefix used when two renamed members collide
     */
    static JsonElement remap(JsonElement value, Map<String, String> ports,
                             String collision) {
        if (value == null || value.isJsonNull()) return value;
        if (value.isJsonArray()) {
            JsonArray result = new JsonArray();
            for (JsonElement element : value.getAsJsonArray()) {
                result.add(remap(element, ports, collision));
            }
            return result;
        }
        if (value.isJsonObject()) {
            JsonObject result = new JsonObject();
            for (Map.Entry<String, JsonElement> entry
                    : value.getAsJsonObject().entrySet()) {
                String key = ports.getOrDefault(entry.getKey(),
                        entry.getKey());
                if (result.has(key)) {
                    throw new IllegalArgumentException(collision + key);
                }
                result.add(key, remap(entry.getValue(), ports, collision));
            }
            return result;
        }
        JsonPrimitive primitive = value.getAsJsonPrimitive();
        if (!primitive.isString()) return primitive.deepCopy();
        return new JsonPrimitive(remapPortTokens(
                primitive.getAsString(), ports));
    }

    private static String remapPortTokens(String value,
                                          Map<String, String> ports) {
        String exact = ports.get(value);
        if (exact != null) return exact;
        List<String> canonical = new ArrayList<>(ports.keySet());
        canonical.sort((left, right) -> Integer.compare(
                right.length(), left.length()));
        StringBuilder result = new StringBuilder();
        int cursor = 0;
        while (cursor < value.length()) {
            String match = "";
            for (String candidate : canonical) {
                if (!value.startsWith(candidate, cursor)) continue;
                int end = cursor + candidate.length();
                boolean leftBoundary = cursor == 0
                        || value.charAt(cursor - 1) == '_';
                boolean rightBoundary = end == value.length()
                        || value.charAt(end) == '_';
                if (leftBoundary && rightBoundary) {
                    match = candidate;
                    break;
                }
            }
            if (match.isEmpty()) {
                result.append(value.charAt(cursor++));
            } else {
                result.append(ports.get(match));
                cursor += match.length();
            }
        }
        return result.toString();
    }
}
