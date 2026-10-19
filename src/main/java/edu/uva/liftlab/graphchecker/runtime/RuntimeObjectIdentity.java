package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

final class RuntimeObjectIdentity {

    private static final int FLOOR = 1 << 20;

    private final Map<Integer, Integer> names = new LinkedHashMap<>();
    private final Map<String, Integer> ordinals = new LinkedHashMap<>();
    private final Set<Integer> used = new LinkedHashSet<>();

    void observe(int objectId, String address) {
        if (objectId <= 0 || names.containsKey(objectId)) {
            return;
        }
        int ordinal = ordinals.merge(address, 1, Integer::sum);
        names.put(objectId, mint(address + "\n#" + ordinal));
    }

    int nameOf(int objectId) {
        if (objectId <= 0) {
            return objectId;
        }
        Integer named = names.get(objectId);
        return named == null ? objectId : named;
    }


    private int mint(String address) {
        for (int attempt = 0; ; attempt++) {
            int candidate = fold(fnv1a(attempt == 0 ? address
                    : address + "\n@" + attempt));
            if (used.add(candidate)) {
                return candidate;
            }
        }
    }

    private static long fnv1a(String value) {
        long hash = 0xcbf29ce484222325L;
        for (int index = 0; index < value.length(); index++) {
            hash ^= value.charAt(index);
            hash *= 0x100000001b3L;
        }
        return hash;
    }

    private static int fold(long hash) {
        int mixed = (int) (hash ^ (hash >>> 32)) & Integer.MAX_VALUE;
        return mixed < FLOOR ? mixed + FLOOR : mixed;
    }

    static String address(String sourceKey, String eventKind, String method,
                          String siteId, int argumentIndex, String field,
                          String runtimeType, String slot) {
        return nonNull(sourceKey) + "\n" + nonNull(eventKind) + "\n"
                + nonNull(method) + "\n" + nonNull(siteId) + "\n"
                + argumentIndex + "\n" + nonNull(field) + "\n"
                + nonNull(runtimeType) + "\n" + nonNull(slot);
    }

}
