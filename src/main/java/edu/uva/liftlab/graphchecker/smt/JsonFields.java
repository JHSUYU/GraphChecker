package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Accessors for OPTIONAL fields inside an already admitted row.
 *
 * <p>Optional means "the row may state it or state nothing": an absent
 * member and an explicit null are a stated absence, and the caller's
 * fallback is what the contract says such a row means.  A member that IS
 * there but does not hold the kind of value the field is -- an object where
 * a string belongs, a string where a number belongs, a number too wide for
 * its field -- is neither of those.  The ROWS ARE THE AUTHORITY: such a
 * member is a row-invariant violation, so it is refused by name here and
 * never read as the fallback, which is how a malformed recording used to
 * reach the composer as a default it never wrote.  A refusal raised while a
 * session is being read lands as {@code SESSION_INCOMPLETE} (BLOCKING) with
 * the file and the reason ({@code contract.SessionReader.read}).</p>
 */
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
     * The one refusal every accessor here raises.
     *
     * <p>Named with the field, the value as written and what the field is,
     * because the reader that catches it can only say as much about the row
     * as this message does.</p>
     */
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
