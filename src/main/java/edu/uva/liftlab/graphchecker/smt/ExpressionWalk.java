package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;

public final class ExpressionWalk implements Iterator<JsonObject> {
    private final Deque<Iterator<JsonElement>> pending =
            new ArrayDeque<Iterator<JsonElement>>();
    private final Set<JsonElement> walked;
    private JsonObject expanding;
    private JsonObject upcoming;

    private ExpressionWalk(JsonElement root, Set<JsonElement> walked) {
        this.walked = walked;
        pending.push(Collections.singletonList(root).iterator());
    }

    public static ExpressionWalk of(JsonElement root) {
        return of(root, identitySet());
    }

    public static ExpressionWalk of(JsonElement root,
                                    Set<JsonElement> walked) {
        return new ExpressionWalk(root, walked);
    }

    public static Set<JsonElement> identitySet() {
        return Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
    }

    public void prune() {
        expanding = null;
    }

    @Override
    public boolean hasNext() {
        if (upcoming != null) return true;
        if (expanding != null) {
            pending.push(expanding.asMap().values().iterator());
            expanding = null;
        }
        while (!pending.isEmpty()) {
            Iterator<JsonElement> members = pending.peek();
            if (!members.hasNext()) {
                pending.pop();
                continue;
            }
            JsonElement node = members.next();
            if (node == null || node.isJsonNull() || node.isJsonPrimitive()
                    || !walked.add(node)) {
                continue;
            }
            if (node.isJsonArray()) {
                pending.push(node.getAsJsonArray().iterator());
                continue;
            }
            upcoming = node.getAsJsonObject();
            return true;
        }
        return false;
    }

    @Override
    public JsonObject next() {
        if (!hasNext()) throw new NoSuchElementException();
        expanding = upcoming;
        upcoming = null;
        return expanding;
    }
}
