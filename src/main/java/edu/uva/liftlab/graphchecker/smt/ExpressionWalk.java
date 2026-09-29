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

/**
 * THE WALK of a recorded VM expression: each object node once, by identity,
 * in the order a recursive walk first reaches it (members and items in
 * order), on an explicit stack.
 *
 * <p>The decoder shares nodes, so walked as a tree an expression costs its
 * paths, not its nodes (a chain whose nodes name the one below twice has
 * 2^depth); recursing, a walk overflows the stack on a chain thousands deep;
 * capped at a depth, it dropped what lay below (Arms.symbolsIn at 512,
 * Corpus's reads at 64).  Skipping a node already walked answers what
 * walking it again would: its members are walked before anything that was
 * pending when it was reached.</p>
 */
public final class ExpressionWalk implements Iterator<JsonObject> {
    private final Deque<Iterator<JsonElement>> pending =
            new ArrayDeque<Iterator<JsonElement>>();
    private final Set<JsonElement> walked;
    /** The node {@link #next} returned last, its members not yet pending. */
    private JsonObject expanding;
    private JsonObject upcoming;

    private ExpressionWalk(JsonElement root, Set<JsonElement> walked) {
        this.walked = walked;
        pending.push(Collections.singletonList(root).iterator());
    }

    /** Every object node of {@code root}. */
    public static ExpressionWalk of(JsonElement root) {
        return of(root, identitySet());
    }

    /**
     * The nodes of {@code root} not in {@code walked} yet; a caller walking
     * many expressions of one table passes one set, since they share
     * subtrees.
     */
    public static ExpressionWalk of(JsonElement root,
                                    Set<JsonElement> walked) {
        return new ExpressionWalk(root, walked);
    }

    public static Set<JsonElement> identitySet() {
        return Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
    }

    /** Leaves the members of the node {@link #next} returned last unwalked. */
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
