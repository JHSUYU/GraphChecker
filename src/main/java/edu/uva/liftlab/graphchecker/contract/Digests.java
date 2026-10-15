package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The digests ids are made of ({@link ArtifactIO#digest}'s spelling), each
 * computed once while it is held: an occurrence's and an endpoint's id, an
 * index's frame fold, a version's symbol, a mint's label.  A replay builds
 * the same id anew on row after row, and SHA-256 in the concolic
 * interpreter is no small cost on its serialized workload (18413's seed:
 * about 10 s).  Bounded: past {@link #HELD} inputs of one length it starts
 * over.
 */
public final class Digests {
    /** The most inputs each length holds before it starts over. */
    private static final int HELD = 1 << 14;

    /** Each digest by its length, then by its input. */
    private static final Map<Integer, Map<String, String>> HELD_BY_LENGTH =
            new ConcurrentHashMap<Integer, Map<String, String>>();

    private Digests() {
    }

    /** {@code ArtifactIO.digest(input, length)}, held. */
    public static String digest(String input, int length) {
        Map<String, String> held = HELD_BY_LENGTH.computeIfAbsent(length,
                any -> new ConcurrentHashMap<String, String>());
        String digested = held.get(input);
        if (digested == null) {
            digested = ArtifactIO.digest(input, length);
            if (held.size() >= HELD) held.clear();
            held.put(input, digested);
        }
        return digested;
    }

    /** {@code ArtifactIO.sha256(input)}, held. */
    public static String sha256(String input) {
        return digest(input, 0);
    }
}
