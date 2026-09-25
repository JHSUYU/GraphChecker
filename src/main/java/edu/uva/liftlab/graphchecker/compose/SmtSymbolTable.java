package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.HashMap;
import java.util.Map;

/**
 * Mints SMT names ending in a truncated content digest, one table per query.
 * Truncation can make two identities share (and silently equate) one name,
 * so every mint is recorded against its identity to catch collisions.
 */
public final class SmtSymbolTable {
    private final Map<String, String> minted = new HashMap<>();
    /**
     * Names two identities would both be truncated to.  Recorded, not
     * thrown; the caller raises a BLOCKING gap.
     */
    private final Map<String, String> collisions =
            new java.util.LinkedHashMap<String, String>();

    /** {@code prefix} followed by the first {@code length} digest digits. */
    public String mint(String prefix, String identity, int length) {
        String name = prefix + ArtifactIO.digest(identity, length);
        String held = minted.putIfAbsent(name, identity);
        if (held != null && !held.equals(identity)) {
            collisions.put(name, held + " and " + identity);
        }
        return name;
    }

    /** The truncated names that would stand for two identities. */
    public Map<String, String> collisions() {
        return java.util.Collections.unmodifiableMap(collisions);
    }
}
