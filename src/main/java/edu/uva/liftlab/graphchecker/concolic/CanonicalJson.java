package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/** Deterministic JSON rendering used by immutable protocol identities. */
public final class CanonicalJson {
    private CanonicalJson() {
    }

    public static JsonElement copy(JsonElement value) {
        if (value == null || value.isJsonNull()) return JsonNull.INSTANCE;
        if (value.isJsonPrimitive()) return value.deepCopy();
        if (value.isJsonArray()) {
            JsonArray result = new JsonArray();
            for (JsonElement item : value.getAsJsonArray()) {
                result.add(copy(item));
            }
            return result;
        }
        JsonObject result = new JsonObject();
        List<String> names = new ArrayList<>();
        for (java.util.Map.Entry<String, JsonElement> entry
                : value.getAsJsonObject().entrySet()) {
            names.add(entry.getKey());
        }
        Collections.sort(names);
        for (String name : names) {
            result.add(name, copy(value.getAsJsonObject().get(name)));
        }
        return result;
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
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(render(value).getBytes(
                    StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder(bytes.length * 2);
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-256 is unavailable",
                    impossible);
        }
    }
}
