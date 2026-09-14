package edu.uva.liftlab.graphchecker.d3.compose;

import java.util.HashMap;
import java.util.Map;

/**
 * Mints the SMT names that end in a truncated content digest.
 *
 * <p>Truncation is what makes these names readable -- a full sha256 makes
 * a query no human can scan -- and it is also the one way two different
 * identities can end up sharing a name, which an SMT query states as one
 * symbol and silently equates.  Every mint is recorded here against the
 * identity it was minted from, so a truncation collision is a loud
 * failure at composition time instead of a wrong answer at solve time.
 * The prefix is part of the name and so part of the record: two families
 * that hash the same identity under different prefixes are two names.</p>
 *
 * <p>One table belongs to one emitter, because the names it guards live
 * in one query.</p>
 */
public final class SmtSymbolTable {
    private final Map<String, String> minted = new HashMap<>();

    /** {@code prefix} followed by the first {@code length} digest digits. */
    public String mint(String prefix, String identity, int length) {
        return mintFromDigest(prefix, JsonText.sha256(identity),
                identity, length);
    }

    /** The same name, for a caller that already holds the full digest. */
    public String mintFromDigest(String prefix, String digest, String identity,
                          int length) {
        String name = prefix + digest.substring(0, length);
        String held = minted.putIfAbsent(name, identity);
        if (held != null && !held.equals(identity)) {
            throw new IllegalStateException(
                    "truncated SMT symbol collision: " + name + " names "
                            + held + " and " + identity);
        }
        return name;
    }
}
