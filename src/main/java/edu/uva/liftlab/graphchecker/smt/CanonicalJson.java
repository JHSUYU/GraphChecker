package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonElement;
import com.google.gson.JsonPrimitive;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/** Deterministic JSON rendering used by immutable protocol identities. */
public final class CanonicalJson {
    private CanonicalJson() {
    }

    public static String render(JsonElement value) {
        if (value == null || value.isJsonNull()) return "null";
        if (value.isJsonPrimitive()) return value.toString();
        if (value.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement item : value.getAsJsonArray()) {
                if (!first) result.append(',');
                first = false;
                result.append(render(item));
            }
            return result.append(']').toString();
        }
        List<String> names = new ArrayList<>();
        for (java.util.Map.Entry<String, JsonElement> entry
                : value.getAsJsonObject().entrySet()) {
            names.add(entry.getKey());
        }
        Collections.sort(names);
        StringBuilder result = new StringBuilder("{");
        boolean first = true;
        for (String name : names) {
            if (!first) result.append(',');
            first = false;
            result.append(new JsonPrimitive(name).toString()).append(':')
                    .append(render(value.getAsJsonObject().get(name)));
        }
        return result.append('}').toString();
    }

    public static String sha256(JsonElement value) {
        return ArtifactIO.sha256(render(value));
    }
}
