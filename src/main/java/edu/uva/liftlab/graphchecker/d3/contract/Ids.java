package edu.uva.liftlab.graphchecker.d3.contract;

import java.io.UnsupportedEncodingException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

/**
 * The one hash every Design 3 identity is minted with.
 *
 * <p>CONTRACT-SPEC: "Ids are lowercase hex sha256 truncated to 16 chars unless
 * stated."  One spelling, in one place: an id computed two ways is two ids, and
 * the whole point of {@link Endpoint} and {@link Interaction} is that the
 * producer side and the consumer side of a join mint the same string.</p>
 */
final class Ids {
    /** The width of every id this contract mints. */
    static final int WIDTH = 16;

    private static final char[] HEX = "0123456789abcdef".toCharArray();

    private Ids() {
    }

    /** The lowercase sha256 of {@code value}, truncated to {@link #WIDTH}. */
    static String sha16(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hash = digest.digest(value.getBytes("UTF-8"));
            StringBuilder rendered = new StringBuilder(WIDTH);
            for (int octet = 0; rendered.length() < WIDTH; octet++) {
                rendered.append(HEX[(hash[octet] >> 4) & 0xF]);
                rendered.append(HEX[hash[octet] & 0xF]);
            }
            return rendered.toString();
        } catch (NoSuchAlgorithmException | UnsupportedEncodingException
                unsupported) {
            throw new IllegalStateException(unsupported);
        }
    }
}
