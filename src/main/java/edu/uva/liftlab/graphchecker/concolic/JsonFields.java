package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/** Forgiving accessors for optional fields inside an already admitted row. */
public final class JsonFields {
    private JsonFields() {
    }

    public static JsonArray array(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    public static JsonObject object(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    public static String string(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException malformed) {
            return "";
        }
    }

    public static boolean bool(JsonObject object, String field,
                               boolean fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }

    public static int integer(JsonObject object, String field, int fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }

    public static long longInteger(JsonObject object, String field,
                                   long fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }

    public static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }

    static JsonObject requiredObject(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        if (value == null || !value.isJsonObject()) {
            throw new IllegalArgumentException(field + " must be an object");
        }
        return value.getAsJsonObject();
    }

    static String primitiveString(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                ? value.getAsString() : "";
    }

    static int primitiveInteger(JsonObject object, String field,
                                int fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || !value.isJsonPrimitive()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }

    static String textString(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isString()
                ? value.getAsString() : "";
    }

    static int exactInteger(JsonObject object, String field, int fallback) {
        JsonElement value = object == null ? null : object.get(field);
        try {
            return value == null || !value.isJsonPrimitive()
                    || !value.getAsJsonPrimitive().isNumber()
                    ? fallback : new java.math.BigDecimal(
                    value.getAsString()).intValueExact();
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }
}
