package edu.uva.liftlab.graphchecker.runtime;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Content-addressed names for the objects one recording observed.
 *
 * <p>{@link CausynthTraceRecorder} names each distinct object with its
 * {@code identity()} counter: a per-run sequence over an
 * {@code IdentityHashMap}.  That number is exact inside one recording and
 * meaningless across two.  The same planned field receiver of hdfs-17899's
 * {@code BlockTokenSecretManager.allKeys} was object 313 in one recording of
 * bug3 and object 300 in the next, which renamed the planned receiver anchor,
 * every {@code SF.} shared-field flow minted from it and every
 * {@code MEMBER.} associative member token, so two recordings of one
 * obligation could not be compared.
 *
 * <p>This renames every recorded object from the content of its <em>first
 * observation</em>: the source it ran on, the event kind that produced it, the
 * declaring method and static site, the argument or field slot, the runtime
 * type, and the slot the id was read out of.  One static site usually
 * allocates many objects, so the address alone is not injective; the ordinal
 * of the object among those first observed at that same address completes it.
 * That ordinal counts per address rather than per run, which is the spelling
 * the plan already uses for activation-local site occurrences and for accessor
 * return ports.
 *
 * <p>The renaming is a bijection on the ids one recording observed, so every
 * consumer that only asks whether two published ids name the same object
 * keeps its answer unchanged: the planned receiver index in
 * {@code ConcolicTaskPlan}, the shared-field flow grouping by receiver and
 * declared field in {@code RuntimeSelectedRegionFinalizer}, and the
 * associative member token.
 *
 * <p>Where two recordings genuinely observed <em>different</em> objects the
 * names still differ, because the objects do.  hdfs-17899 rolls a fresh
 * {@code BlockKey} on a wall-clock timer, so two recordings of bug3 reach the
 * target with a different number of keys created and a different
 * {@code serialNo} on each; the object naming reports that as the content
 * difference it is, on the same rows whose {@code primitiveValue} differs.
 */
final class RuntimeObjectIdentity {

    /**
     * Names never collide with the recorder's own small counter values, so a
     * published id that was never renamed is recognisable in a diff.
     */
    private static final int FLOOR = 1 << 20;

    private final Map<Integer, Integer> names = new LinkedHashMap<>();
    private final Map<String, Integer> ordinals = new LinkedHashMap<>();
    private final Set<Integer> used = new LinkedHashSet<>();

    /**
     * Records that {@code objectId} was first seen at {@code address}.
     *
     * <p>Must be called for every object slot of every event in recorded
     * order; later observations of an object already named are ignored, which
     * is what makes the first one the address.</p>
     */
    void observe(int objectId, String address) {
        if (objectId <= 0 || names.containsKey(objectId)) {
            return;
        }
        int ordinal = ordinals.merge(address, 1, Integer::sum);
        names.put(objectId, mint(address + "\n#" + ordinal));
    }

    /**
     * The content-addressed name of one recorded object.
     *
     * <p>0 stays 0: it is the recorder's statement that a slot held no
     * object, not an object.  An id no event ever introduced keeps its
     * recorded value rather than being silently renamed to something no
     * other row shares.</p>
     */
    int nameOf(int objectId) {
        if (objectId <= 0) {
            return objectId;
        }
        Integer named = names.get(objectId);
        return named == null ? objectId : named;
    }

    /** How many objects this recording named. */
    int size() {
        return names.size();
    }

    /**
     * One address's name, kept distinct from every name already minted.
     *
     * <p>A 31-bit name cannot be collision-free by construction, so a
     * collision is resolved by re-hashing the address with the number of
     * attempts already made.  The address set and the order it is offered in
     * are both fixed by the recording, so the resolution is reproducible.</p>
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
     * The content address of one observation.
     *
     * <p>{@code sourceKey} is the logical node the frame ran on, not a
     * transient trace id, and it is read after load-time source
     * re-attribution has settled.  Without it the same static site on two
     * cluster nodes would share one address and its objects would be told
     * apart only by an ordinal over an interleaving no run reproduces.</p>
     */
    static String address(String sourceKey, String eventKind, String method,
                          String siteId, int argumentIndex, String field,
                          String runtimeType, String slot) {
        return safe(sourceKey) + "\n" + safe(eventKind) + "\n"
                + safe(method) + "\n" + safe(siteId) + "\n"
                + argumentIndex + "\n" + safe(field) + "\n"
                + safe(runtimeType) + "\n" + safe(slot);
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }
}
