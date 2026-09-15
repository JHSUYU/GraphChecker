package edu.uva.liftlab.graphchecker.d3.smt;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;

/** Deterministic JSON rendering used by immutable protocol identities. */
public final class CanonicalJson {
    private CanonicalJson() {
    }

    /**
     * Canonical copy of one immutable expression graph.
     *
     * <p>A propagated value is a shared DAG, not a tree: the decoder holds one
     * instance per content anchor and a node reached by several parents is
     * that one instance.  Copying it by plain recursion restates the whole
     * subtree once per <em>path</em> that reaches it, so a graph whose nodes
     * are shared k deep becomes a tree with k-fold more nodes than the graph
     * has.  That is what made one composed candidate's target-path complements
     * turn a 44k-node propagated graph into 42M {@code JsonObject}s.</p>
     *
     * <p>This walk copies one node per <em>node</em> instead, so the result is
     * a DAG with the source's sharing and exactly the same rendering.  Copies
     * are still fresh objects, and the memo is per call, so no result ever
     * aliases the source.  Gson primitives are immutable ({@code deepCopy}
     * returns {@code this}), so they are shared rather than re-wrapped.</p>
     */
    public static JsonElement copy(JsonElement value) {
        return copy(value, new IdentityHashMap<JsonElement, JsonElement>());
    }

    private static JsonElement copy(
            JsonElement value,
            IdentityHashMap<JsonElement, JsonElement> memo) {
        if (value == null || value.isJsonNull()) return JsonNull.INSTANCE;
        if (value.isJsonPrimitive()) return value;
        JsonElement held = memo.get(value);
        if (held != null) return held;
        JsonElement result;
        if (value.isJsonArray()) {
            JsonArray array = new JsonArray();
            for (JsonElement item : value.getAsJsonArray()) {
                array.add(copy(item, memo));
            }
            result = array;
        } else {
            JsonObject object = new JsonObject();
            List<String> names = new ArrayList<>();
            for (java.util.Map.Entry<String, JsonElement> entry
                    : value.getAsJsonObject().entrySet()) {
                names.add(entry.getKey());
            }
            Collections.sort(names);
            for (String name : names) {
                object.add(name, copy(value.getAsJsonObject().get(name),
                        memo));
            }
            result = object;
        }
        // Recorded only once the node is built, so a cyclic input still fails
        // the way an unmemoized walk failed it instead of being accepted.
        memo.put(value, result);
        return result;
    }

    public static String render(JsonElement value) {
        if (value == null || value.isJsonNull()) return "null";
        if (value.isJsonPrimitive()) return value.toString();
        if (value.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement item : value.getAsJsonArray()) {
                if (!first) result.append(',');
                first = false;
                result.append(render(item));
            }
            return result.append(']').toString();
        }
        List<String> names = new ArrayList<>();
        for (java.util.Map.Entry<String, JsonElement> entry
                : value.getAsJsonObject().entrySet()) {
            names.add(entry.getKey());
        }
        Collections.sort(names);
        StringBuilder result = new StringBuilder("{");
        boolean first = true;
        for (String name : names) {
            if (!first) result.append(',');
            first = false;
            result.append(new JsonPrimitive(name).toString()).append(':')
                    .append(render(value.getAsJsonObject().get(name)));
        }
        return result.append('}').toString();
    }

    public static String sha256(JsonElement value) {
        return ArtifactIO.sha256(render(value));
    }

    public static String sha256(String value) {
        return ArtifactIO.sha256(value);
    }
}
