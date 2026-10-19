package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public final class Digests {
    private static final int HELD = 1 << 14;

    private static final Map<Integer, Map<String, String>> HELD_BY_LENGTH =
            new ConcurrentHashMap<Integer, Map<String, String>>();

    private Digests() {
    }

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

    public static String sha256(String input) {
        return digest(input, 0);
    }
}
