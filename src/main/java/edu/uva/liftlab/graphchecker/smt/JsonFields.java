package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Accessors for OPTIONAL fields inside an already admitted row.  Absent or
 * null is a stated absence and yields the caller's fallback; a member of the
 * wrong kind is a row-invariant violation, refused by name and never read
 * as the fallback (it surfaces as {@code SESSION_INCOMPLETE} via
 * {@code contract.SessionReader.read}).
 */
public final class JsonFields {
    /**
     * The one writer every artifact row is serialized through.  HTML
     * escaping is off (Soot signatures start with {@code <}; escaping would
     * change digests).  Nulls are written: a null member is a stated absence;
     * to omit, use {@link #objectWithoutNulls}.
     */
    public static final Gson WRITER = new GsonBuilder()
            .disableHtmlEscaping().serializeNulls().create();

    private JsonFields() {
    }

    /** The one refusal every accessor raises: field, value, expected kind. */
    private static IllegalArgumentException malformed(
            String field, JsonElement value, String expected,
            RuntimeException cause) {
        return new IllegalArgumentException("row field " + field
                + " states " + value + ", which is not " + expected
                + ": a member a row states is the authority, so a value of"
                + " the wrong kind is a row-invariant violation and never"
                + " the field's absent value", cause);
    }

    /**
     * {@code {k:v, ...}} from alternating keys and values, omitting pairs
     * whose value is null.
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

    public static String optionalString(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        if (value == null || value.isJsonNull()) return "";
        try {
            return value.getAsString();
        } catch (RuntimeException notAString) {
            throw malformed(field, value, "a string", notAString);
        }
    }

    public static boolean optionalBool(JsonObject object, String field,
                                       boolean fallback) {
        JsonElement value = object == null ? null : object.get(field);
        if (value == null || value.isJsonNull()) return fallback;
        try {
            return value.getAsBoolean();
        } catch (RuntimeException notABoolean) {
            throw malformed(field, value, "a boolean", notABoolean);
        }
    }

    public static int optionalInteger(JsonObject object, String field, int fallback) {
        JsonElement value = object == null ? null : object.get(field);
        if (value == null || value.isJsonNull()) return fallback;
        try {
            return value.getAsInt();
        } catch (RuntimeException notAnInteger) {
            throw malformed(field, value, "an int", notAnInteger);
        }
    }

    public static long optionalLongInteger(JsonObject object, String field,
                                           long fallback) {
        JsonElement value = object == null ? null : object.get(field);
        if (value == null || value.isJsonNull()) return fallback;
        try {
            return value.getAsLong();
        } catch (RuntimeException notALong) {
            throw malformed(field, value, "a long", notALong);
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

    /** Copies one record shell while retaining its immutable nested values. */
    public static JsonObject shallowCopy(JsonObject source) {
        JsonObject result = new JsonObject();
        if (source != null) {
            for (Map.Entry<String, JsonElement> field : source.entrySet()) {
                result.add(field.getKey(), field.getValue());
            }
        }
        return result;
    }

    public static String primitiveString(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                ? value.getAsString() : "";
    }

    public static String textString(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isString()
                ? value.getAsString() : "";
    }

    public static int exactInteger(JsonObject object, String field,
                            int fallback) {
        JsonElement value = object == null ? null : object.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            return fallback;
        }
        try {
            return new java.math.BigDecimal(value.getAsString())
                    .intValueExact();
        } catch (RuntimeException notExactlyAnInteger) {
            throw malformed(field, value,
                    "an int the field holds exactly", notExactlyAnInteger);
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

    /** {@code value}, or "" when null; untrimmed, unlike {@link #trimmed}. */
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
