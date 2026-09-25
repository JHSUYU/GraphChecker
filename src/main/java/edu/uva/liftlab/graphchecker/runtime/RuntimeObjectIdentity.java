package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Content-addressed names for the objects one recording observed, so two
 * recordings of one obligation can be compared.
 *
 * <p>{@link CausynthTraceRecorder}'s {@code identity()} counter is exact in
 * one recording and meaningless across two.  Each object is renamed from its
 * <em>first observation</em> (source, event kind, method, site, slot, runtime
 * type) plus its ordinal among objects first seen at that address.  The
 * renaming is a bijection per recording, so same-object questions keep their
 * answers; genuinely different objects still get different names.</p>
 */
final class RuntimeObjectIdentity {

    /** Names sit above the recorder's counters, so an unrenamed id shows. */
    private static final int FLOOR = 1 << 20;

    private final Map<Integer, Integer> names = new LinkedHashMap<>();
    private final Map<String, Integer> ordinals = new LinkedHashMap<>();
    private final Set<Integer> used = new LinkedHashSet<>();

    /**
     * Records that {@code objectId} was first seen at {@code address}; call
     * for every object slot in recorded order (later sightings are ignored).
     */
    void observe(int objectId, String address) {
        if (objectId <= 0 || names.containsKey(objectId)) {
            return;
        }
        int ordinal = ordinals.merge(address, 1, Integer::sum);
        names.put(objectId, mint(address + "\n#" + ordinal));
    }

    /**
     * The name of one recorded object; 0 ("no object") and ids no event
     * introduced keep their recorded value.
     */
    int nameOf(int objectId) {
        if (objectId <= 0) {
            return objectId;
        }
        Integer named = names.get(objectId);
        return named == null ? objectId : named;
    }


    /**
     * One address's name, distinct from every name minted: a collision is
     * re-hashed with the attempt number (reproducible, since the recording
     * fixes the order).
     */
    private int mint(String address) {
        for (int attempt = 0; ; attempt++) {
            int candidate = fold(fnv1a(attempt == 0 ? address
                    : address + "\n@" + attempt));
            if (used.add(candidate)) {
                return candidate;
            }
        }
    }

    /** FNV-1a over UTF-16 units: identical in every JVM and session. */
    private static long fnv1a(String value) {
        long hash = 0xcbf29ce484222325L;
        for (int index = 0; index < value.length(); index++) {
            hash ^= value.charAt(index);
            hash *= 0x100000001b3L;
        }
        return hash;
    }

    /** A positive int name, above the recorder's own counter range. */
    private static int fold(long hash) {
        int mixed = (int) (hash ^ (hash >>> 32)) & Integer.MAX_VALUE;
        return mixed < FLOOR ? mixed + FLOOR : mixed;
    }

    /**
     * The content address of one observation.  {@code sourceKey} is the
     * logical node (after re-attribution); without it one site on two nodes
     * would share an address and depend on the interleaving.
     */
    static String address(String sourceKey, String eventKind, String method,
                          String siteId, int argumentIndex, String field,
                          String runtimeType, String slot) {
        return safe(sourceKey) + "\n" + safe(eventKind) + "\n"
                + safe(method) + "\n" + safe(siteId) + "\n"
                + argumentIndex + "\n" + safe(field) + "\n"
                + safe(runtimeType) + "\n" + safe(slot);
    }

}
