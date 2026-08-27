package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.LinkedHashMap;
import java.util.Map;

/** Forgiving accessors for optional fields inside an already admitted row. */
public final class JsonFields {
    /**
     * The one writer every artifact row is serialized through.
     *
     * <p>HTML escaping is off because a Soot signature starts with {@code <}:
     * escaping it to {@code \u003c} would change every recorded method name
     * and every artifact digest that pins one. Nulls are written because a
     * row member whose value is null is a stated absence a reader decodes,
     * not a member that was never there -- dropping it silently changes
     * {@code "requiredOutcome":null} into no requiredOutcome at all. A caller
     * that means "omit it" drops the pair itself; see
     * {@link #objectWithoutNulls}.</p>
     */
    public static final Gson WRITER = new GsonBuilder()
            .disableHtmlEscaping().serializeNulls().create();

    private JsonFields() {
    }

    /**
     * {@code {k:v, ...}} from alternating keys and values, dropping any pair
     * whose value is null before it reaches {@link #WRITER}: this caller
     * means "omit it", so no null ever reaches the writer that would have
     * written one.
     */
    public static String objectWithoutNulls(Object... fields) {
        Map<String, Object> row = new LinkedHashMap<>();
        for (int index = 0; fields != null
                && index + 1 < fields.length; index += 2) {
            if (fields[index + 1] != null) {
                row.put(String.valueOf(fields[index]), fields[index + 1]);
            }
        }
        return WRITER.toJson(row);
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

    public static JsonObject requiredObject(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        if (value == null || !value.isJsonObject()) {
            throw new IllegalArgumentException(field + " must be an object");
        }
        return value.getAsJsonObject();
    }

    public static JsonArray requiredArray(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        if (value == null || !value.isJsonArray()) {
            throw new IllegalArgumentException(field + " must be an array");
        }
        return value.getAsJsonArray();
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

    public static int exactInteger(JsonObject object, String field,
                            int fallback) {
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

    /** Trimmed string form of a primitive member, or "" when absent. */
    public static String text(JsonObject object, String field) {
        return primitiveString(object, field).trim();
    }

    /** {@code value} trimmed, or "" when null. */
    public static String trimmed(String value) {
        return value == null ? "" : value.trim();
    }

    /** {@code value}, or "" when null.  Unlike {@link #trimmed} it keeps
     * surrounding whitespace, so an identity read back off the wire is the
     * one that was written. */
    public static String nonNull(String value) {
        return value == null ? "" : value;
    }

    /** {@code value} trimmed; a null or blank one is rejected. */
    public static String required(String value, String label) {
        String result = trimmed(value);
        if (result.isEmpty()) {
            throw new IllegalArgumentException(label + " is required");
        }
        return result;
    }

    /** {@code value} untrimmed, rejected when null or blank. */
    public static String requireText(String value, String label) {
        required(value, label);
        return value;
    }
}
