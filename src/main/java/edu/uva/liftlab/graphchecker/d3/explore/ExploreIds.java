package edu.uva.liftlab.graphchecker.d3.explore;

import java.io.UnsupportedEncodingException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

/**
 * The ids exploration mints for the things the contract does not name: a
 * path (one occurrence in one session), a task, an obligation.
 *
 * <p>Same spelling as the contract's own ids -- lowercase sha256 truncated to
 * 16 -- so a reader cannot tell from the shape which side minted one.  The
 * contract's {@code Ids} is package-private, deliberately: an id's INPUT is
 * what makes it an identity, and every input this stage hashes is stated at
 * its call site.</p>
 */
final class ExploreIds {
    private static final char[] HEX = "0123456789abcdef".toCharArray();

    private ExploreIds() {
    }

    static String sha16(String value) {
        try {
            byte[] hash = MessageDigest.getInstance("SHA-256")
                    .digest(value.getBytes("UTF-8"));
            StringBuilder rendered = new StringBuilder(16);
            for (int octet = 0; rendered.length() < 16; octet++) {
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
