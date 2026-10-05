package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonIOException;
import com.google.gson.JsonObject;
import com.google.gson.stream.JsonWriter;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
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
                + " states " + quoted(value) + ", which is not " + expected
                + ": a member a row states is the authority, so a value of"
                + " the wrong kind is a row-invariant violation and never"
                + " the field's absent value", cause);
    }

    /** The most characters of a value a refusal quotes. */
    private static final int QUOTED = 512;

    /**
     * A value as a refusal quotes it: its JSON, cut after {@link #QUOTED}
     * characters.  Never whole: a VM expression is a shared DAG, and a
     * FieldAccessExpression names its owner twice, so its rendering doubles
     * per level (2^depth nodes).
     */
    static String quoted(JsonElement value) {
        StringBuilder text = new StringBuilder();
        try {
            WRITER.toJson(value, new JsonWriter(new Writer() {
                @Override
                public void write(char[] chars, int offset, int length)
                        throws IOException {
                    int room = QUOTED - text.length();
                    text.append(chars, offset, Math.min(room, length));
                    if (length > room) throw new QuotedInFull();
                }

                @Override
                public void flush() {
                }

                @Override
                public void close() {
                }
            }));
        } catch (JsonIOException cut) {
            if (!(cut.getCause() instanceof QuotedInFull)) throw cut;
            text.append("...");
        }
        return text.toString();
    }

    /** Stops {@link #quoted} at its bound. */
    private static final class QuotedInFull extends IOException {
        private static final long serialVersionUID = 1L;
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

    /** The strings of an array member, in order; none when it is absent. */
    public static List<String> strings(JsonObject object, String field) {
        List<String> values = new ArrayList<String>();
        for (JsonElement element : array(object, field)) {
            values.add(element.getAsString());
        }
        return values;
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

    /**
     * A JVM setting: the system property {@code property}, else the
     * environment variable {@code environment} (what a launcher hands a JVM
     * it does not start with {@code -D}: a replay's, through the adapter),
     * trimmed; "" when neither names one.
     */
    public static String setting(String property, String environment) {
        return firstNonBlank(System.getProperty(property),
                System.getenv(environment));
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
