package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

/**
 * CONTRACT-SPEC §2.3: the ref a session's rows name an expression by, {@code
 * EXPR.} and the 16 hex of a 64-bit Merkle hash over the expression DAG.  A
 * node's hash folds its member names in sorted order, each scalar's text and
 * each child's hash, so equal expressions have equal refs in every session;
 * each node (by identity) is hashed once, however often it is shared.
 *
 * <p>No SHA-256 over a canonical rendering: the replay runs in the concolic
 * interpreter, where that cost 2.1 ms a node (SOLR-18406's publication spent
 * minutes in it).  Sixteen hex of the SHA-256 were 64 bits too; the
 * collision space is the same.</p>
 */
public final class ExpressionRefs {
    public static final String PREFIX = "EXPR.";
    private static final long SEED_OBJECT = 0x6f626a6563742e31L;
    private static final long SEED_ARRAY = 0x61727261792e3031L;
    private static final long TAG_STRING = 0x737472696e672e31L;
    private static final long TAG_NUMBER = 0x6e756d6265722e31L;
    private static final long TAG_TRUE = 0x747275652e2e2e31L;
    private static final long TAG_FALSE = 0x66616c73652e2e31L;
    private static final long TAG_NULL = 0x6e756c6c2e2e2e31L;

    private final Map<JsonElement, Long> hashes =
            new IdentityHashMap<JsonElement, Long>();

    /** The ref of one expression. */
    public synchronized String ref(JsonObject expression) {
        String hex = Long.toHexString(hash(expression));
        StringBuilder ref = new StringBuilder(PREFIX);
        for (int pad = hex.length(); pad < 16; pad++) ref.append('0');
        return ref.append(hex).toString();
    }

    /** Post-order and iterative: a chain nests thousands deep. */
    private long hash(JsonElement root) {
        Deque<JsonElement> pending = new ArrayDeque<JsonElement>();
        Deque<Boolean> expanded = new ArrayDeque<Boolean>();
        Map<JsonElement, Boolean> active =
                new IdentityHashMap<JsonElement, Boolean>();
        pending.push(root);
        expanded.push(Boolean.FALSE);
        while (!pending.isEmpty()) {
            JsonElement node = pending.pop();
            boolean children = expanded.pop();
            if (hashes.containsKey(node)) continue;
            if (!children) {
                if (active.put(node, Boolean.TRUE) != null) {
                    throw new IllegalArgumentException(
                            "cyclic expression graph");
                }
                pending.push(node);
                expanded.push(Boolean.TRUE);
                for (JsonElement child : members(node)) {
                    if (composite(child) && !hashes.containsKey(child)) {
                        pending.push(child);
                        expanded.push(Boolean.FALSE);
                    }
                }
                continue;
            }
            long hash;
            if (node.isJsonArray()) {
                hash = SEED_ARRAY;
                for (JsonElement element : node.getAsJsonArray()) {
                    hash = mix(hash, value(element));
                }
            } else {
                JsonObject object = node.getAsJsonObject();
                List<String> names = new ArrayList<String>(object.keySet());
                Collections.sort(names);
                hash = SEED_OBJECT;
                for (String name : names) {
                    hash = mix(mix(hash, text(name)), value(object.get(name)));
                }
            }
            hashes.put(node, hash);
            active.remove(node);
        }
        return hashes.get(root);
    }

    private static boolean composite(JsonElement value) {
        return value != null && (value.isJsonObject() || value.isJsonArray());
    }

    private static Iterable<JsonElement> members(JsonElement node) {
        return node.isJsonArray() ? node.getAsJsonArray()
                : node.getAsJsonObject().asMap().values();
    }

    /** A child's hash, already folded, or a scalar's. */
    private long value(JsonElement value) {
        if (composite(value)) return hashes.get(value);
        if (value == null || value.isJsonNull()) return TAG_NULL;
        JsonPrimitive scalar = value.getAsJsonPrimitive();
        if (scalar.isBoolean()) {
            return scalar.getAsBoolean() ? TAG_TRUE : TAG_FALSE;
        }
        return mix(scalar.isNumber() ? TAG_NUMBER : TAG_STRING,
                text(scalar.getAsString()));
    }

    /** FNV-1a over the UTF-16 units, finished by {@link #mix}. */
    private static long text(String value) {
        long hash = 0xcbf29ce484222325L;
        for (int index = 0; index < value.length(); index++) {
            hash ^= value.charAt(index);
            hash *= 0x100000001b3L;
        }
        return mix(hash, value.length());
    }

    /** Folds one value into a running hash (murmur3's 64-bit finalizer). */
    private static long mix(long hash, long value) {
        long mixed = hash * 0x9e3779b97f4a7c15L + value;
        mixed ^= mixed >>> 33;
        mixed *= 0xff51afd7ed558ccdL;
        mixed ^= mixed >>> 33;
        mixed *= 0xc4ceb9fe1a85ec53L;
        mixed ^= mixed >>> 33;
        return mixed;
    }
}
