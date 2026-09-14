package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

/**
 * Reading a recorded VM expression node, and naming things by digest.
 *
 * <p>A recorded node is a {@code JsonObject} whose members the runtime may
 * or may not have written, so every accessor here answers a stated absence
 * rather than throwing: a composition refuses by naming what is missing,
 * never by a stack trace.</p>
 */
final class JsonText {
    private JsonText() {
    }

    /** The string this member holds, or "" when it holds none. */
    static String string(JsonObject object, String member) {
        if (object == null) return "";
        JsonElement value = object.get(member);
        if (value == null || value.isJsonNull()
                || !value.isJsonPrimitive()) {
            return "";
        }
        return value.getAsString();
    }

    /** The object this member holds, or an empty one. */
    static JsonObject object(JsonObject parent, String member) {
        if (parent == null) return new JsonObject();
        JsonElement value = parent.get(member);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    static int integer(JsonObject object, String member, int absent) {
        String value = string(object, member);
        if (value.isEmpty()) return absent;
        try {
            return Integer.parseInt(value.trim());
        } catch (NumberFormatException notAnInteger) {
            return absent;
        }
    }

    static long longInteger(JsonObject object, String member, long absent) {
        String value = string(object, member);
        if (value.isEmpty()) return absent;
        try {
            return Long.parseLong(value.trim());
        } catch (NumberFormatException notAnInteger) {
            return absent;
        }
    }

    /** The first of these that is not blank, or "". */
    static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value;
        }
        return "";
    }

    /** One decimal integer as SMT-LIB spells it, or "". */
    static String smtInteger(String value) {
        String text = value == null ? "" : value.trim();
        if (text.isEmpty()) return "";
        try {
            BigInteger integer = new BigInteger(text);
            return integer.signum() < 0
                    ? "(- " + integer.negate().toString() + ")"
                    : integer.toString();
        } catch (NumberFormatException notAnInteger) {
            return "";
        }
    }

    /** One recorded value as an SMT literal of that sort, or "". */
    static String smtLiteral(String value) {
        String text = value == null ? "" : value.trim();
        if ("true".equals(text) || "false".equals(text)) return text;
        return smtInteger(text);
    }

    /** Lowercase hex sha256, untruncated. */
    static String sha256(String text) {
        return digest(text, 0);
    }

    /** Lowercase hex sha256, truncated. */
    static String digest(String text, int length) {
        try {
            MessageDigest sha = MessageDigest.getInstance("SHA-256");
            byte[] bytes = sha.digest((text == null ? "" : text)
                    .getBytes(StandardCharsets.UTF_8));
            StringBuilder hex = new StringBuilder(bytes.length * 2);
            for (byte value : bytes) {
                hex.append(Character.forDigit((value >> 4) & 0xF, 16));
                hex.append(Character.forDigit(value & 0xF, 16));
            }
            String full = hex.toString();
            return length <= 0 || length >= full.length()
                    ? full : full.substring(0, length);
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    /** The same text, spelled the way an SMT symbol may be spelled. */
    static String smtName(String value) {
        String normalized = (value == null || value.trim().isEmpty()
                ? "anonymous" : value).replaceAll("[^A-Za-z0-9_]", "_");
        if (normalized.isEmpty()) normalized = "anonymous";
        if (Character.isDigit(normalized.charAt(0))) {
            normalized = "n_" + normalized;
        }
        return normalized;
    }
}
