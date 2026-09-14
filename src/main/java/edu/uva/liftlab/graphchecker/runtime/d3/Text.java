package edu.uva.liftlab.graphchecker.runtime.d3;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

/**
 * The two string facts this package needs of its own: a value that is never
 * null, and the contract's id function.
 *
 * <p>{@code d3.contract.Ids} is package-private there on purpose -- one
 * place computes an id inside the contract -- so the runtime states the same
 * function here rather than widening it.</p>
 */
final class Text {
    private Text() {
    }

    static String safe(String value) {
        return value == null ? "" : value.trim();
    }

    /** Lowercase hex sha256, truncated to 16 chars, as the contract does. */
    static String sha16(String value) {
        try {
            byte[] hash = MessageDigest.getInstance("SHA-256").digest(
                    safe(value).getBytes(StandardCharsets.UTF_8));
            StringBuilder hex = new StringBuilder(16);
            for (int i = 0; i < 8; i++) {
                hex.append(String.format("%02x", hash[i]));
            }
            return hex.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("sha-256 is required", impossible);
        }
    }
}
