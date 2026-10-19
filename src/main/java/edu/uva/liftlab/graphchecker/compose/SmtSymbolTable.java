package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.util.HashMap;
import java.util.Map;

public final class SmtSymbolTable {
    private final Map<String, String> minted = new HashMap<>();
    private final Map<String, String> collisions =
            new java.util.LinkedHashMap<String, String>();

    public String mint(String prefix, String identity, int length) {
        String name = prefix + ArtifactIO.digest(identity, length);
        String held = minted.putIfAbsent(name, identity);
        if (held != null && !held.equals(identity)) {
            collisions.put(name, held + " and " + identity);
        }
        return name;
    }

    public void forget(String name) {
        minted.remove(name);
    }

    public Map<String, String> collisions() {
        return java.util.Collections.unmodifiableMap(collisions);
    }
}
