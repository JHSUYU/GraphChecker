package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;
import com.google.gson.internal.LazilyParsedNumber;

import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.AbstractSet;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * CONTRACT-SPEC §2.3: the session's expressions, ref to the VM's expression
 * object unchanged.  Rows carry refs into this shared DAG, never inlined
 * trees; the file holds it as a DAG too ({@link SessionExpressionLog}).
 *
 * <p>HELD COMPACT, MATERIALIZED ON DEMAND.  The table holds the DAG as its
 * log states it, each node once: one byte string of varint-tagged values
 * over the session's strings (each held once, from the read's pool), a node
 * naming each child by its index.  A node a reader asks for -- by its ref,
 * or as a child of one it holds -- is built then as the Gson object the log
 * line parses to (its members in order, a number by its spelling), and
 * stays THE object of that node while anything holds it: the table keeps
 * it weakly, a node holds its children, and so every walk and memo that
 * goes by node identity ({@code smt.ExpressionWalk}, {@code
 * compose.SmtLowering}'s memo) sees one object per node.  Once nothing
 * holds it, it is released, and a later ask builds it again -- an object
 * no one can compare with the one before, which nobody holds.  As Gson
 * trees, solr-adhoc-39 PV7's 208 sessions' tables held 3.2 GB of the
 * planner's heap (a map per node; 40.9 M map entries); on disk 1.6 GB.</p>
 */
public final class ExpressionTable extends Value {
    /** Value tags: a varint's low three bits; the rest its payload. */
    private static final int OBJECT = 0;
    private static final int ARRAY = 1;
    private static final int STRING = 2;
    private static final int NUMBER = 3;
    private static final int TRUE = 4;
    private static final int FALSE = 5;
    private static final int NULL = 6;
    private static final int NODE = 7;

    private static final ExpressionTable EMPTY = new Builder().build();

    /** Every string the nodes name: member names, strings, number
     *  spellings. */
    private final String[] strings;
    /** The nodes, one encoded object each. */
    private final byte[] code;
    /** node index -> where it starts in {@link #code}. */
    private final int[] offsets;
    /** The refs, in the order the log stated them, and each one's node. */
    private final String[] refs;
    private final int[] refNodes;
    /** Open addressing over {@link #refs}: a ref's index + 1, 0 none. */
    private final int[] slots;
    /** node index -> the object built for it, while anything holds it. */
    private Live[] live;
    /** The objects the collector let go of: their slots are emptied as
     *  the next node is asked for (SGF8-adhoc-05 round 5's 342 tables held
     *  5.2 M cleared references, 167 MB, beside 13 live objects). */
    private final ReferenceQueue<JsonObject> released =
            new ReferenceQueue<JsonObject>();

    /** One built object, weakly, with its node's index. */
    private static final class Live extends WeakReference<JsonObject> {
        final int index;

        Live(JsonObject made, int index, ReferenceQueue<JsonObject> queue) {
            super(made, queue);
            this.index = index;
        }
    }

    private ExpressionTable(String[] strings, byte[] code, int[] offsets,
                            String[] refs, int[] refNodes) {
        this.strings = strings;
        this.code = code;
        this.offsets = offsets;
        this.refs = refs;
        this.refNodes = refNodes;
        this.slots = new int[Integer.highestOneBit(
                Math.max(1, refs.length) * 2 + 1) * 2];
        for (int at = 0; at < refs.length; at++) {
            int slot = slot(refs[at]);
            while (slots[slot] != 0) slot = (slot + 1) & (slots.length - 1);
            slots[slot] = at + 1;
        }
    }

    /** The empty table: a session that propagated nothing. */
    public static ExpressionTable empty() {
        return EMPTY;
    }

    /** The expression behind one reference, or {@code null}. */
    public JsonObject expression(String ref) {
        if (ref == null) return null;
        int at = indexOf(ref);
        return at < 0 ? null : node(refNodes[at]);
    }

    /** The refs, in the order the log stated them. */
    public Set<String> refs() {
        return new AbstractSet<String>() {
            @Override
            public boolean contains(Object ref) {
                return ref instanceof String && indexOf((String) ref) >= 0;
            }

            @Override
            public int size() {
                return refs.length;
            }

            @Override
            public Iterator<String> iterator() {
                return Collections.unmodifiableList(Arrays.asList(refs))
                        .iterator();
            }
        };
    }

    /** Every ref's expression, built: a whole-table reader's view (IMPORT's
     *  gate, a log written again). */
    public Map<String, JsonObject> expressions() {
        Map<String, JsonObject> all = new LinkedHashMap<String, JsonObject>();
        for (int at = 0; at < refs.length; at++) {
            all.put(refs[at], node(refNodes[at]));
        }
        return Collections.unmodifiableMap(all);
    }

    @Override
    Object[] parts() {
        return new Object[] {expressions()};
    }

    @Override
    public String toString() {
        return "ExpressionTable{" + refs.length + " expressions}";
    }

    private int slot(String ref) {
        return (ref.hashCode() * 0x9E3779B9) >>> 1 & (slots.length - 1);
    }

    private int indexOf(String ref) {
        for (int slot = slot(ref); slots[slot] != 0;
             slot = (slot + 1) & (slots.length - 1)) {
            if (refs[slots[slot] - 1].equals(ref)) return slots[slot] - 1;
        }
        return -1;
    }

    /**
     * The object of one node: the one built while anything still holds it,
     * else built now -- its children likewise, each object registered as it
     * is made and filled from a work list (a chain nests thousands deep).
     * One table's nodes are built under its lock: a node is never built
     * twice at once.
     */
    private synchronized JsonObject node(int index) {
        for (Live gone = (Live) released.poll(); gone != null;
             gone = (Live) released.poll()) {
            if (live[gone.index] == gone) live[gone.index] = null;
        }
        JsonObject held = held(index);
        if (held != null) return held;
        Deque<Integer> pending = new ArrayDeque<Integer>();
        Deque<JsonObject> unfilled = new ArrayDeque<JsonObject>();
        JsonObject built = register(index);
        pending.push(index);
        unfilled.push(built);
        while (!pending.isEmpty()) {
            int node = pending.pop();
            JsonObject into = unfilled.pop();
            Cursor cursor = new Cursor(offsets[node]);
            int tagged = cursor.next();
            if ((tagged & 7) != OBJECT) {
                throw new IllegalStateException("expression node " + node
                        + " is no object");
            }
            fill(into, tagged >>> 3, cursor, pending, unfilled);
        }
        return built;
    }

    private JsonObject held(int index) {
        Live reference = live == null ? null : live[index];
        return reference == null ? null : reference.get();
    }

    private JsonObject register(int index) {
        if (live == null) live = new Live[offsets.length];
        JsonObject made = new JsonObject();
        live[index] = new Live(made, index, released);
        return made;
    }

    private void fill(JsonObject into, int members, Cursor cursor,
                      Deque<Integer> pending, Deque<JsonObject> unfilled) {
        for (int member = 0; member < members; member++) {
            String name = strings[cursor.next()];
            into.add(name, value(cursor, pending, unfilled));
        }
    }

    private JsonElement value(Cursor cursor, Deque<Integer> pending,
                              Deque<JsonObject> unfilled) {
        int tagged = cursor.next();
        int payload = tagged >>> 3;
        switch (tagged & 7) {
            case OBJECT: {
                JsonObject inline = new JsonObject();
                fill(inline, payload, cursor, pending, unfilled);
                return inline;
            }
            case ARRAY: {
                JsonArray array = new JsonArray(payload);
                for (int element = 0; element < payload; element++) {
                    array.add(value(cursor, pending, unfilled));
                }
                return array;
            }
            case STRING:
                return new JsonPrimitive(strings[payload]);
            case NUMBER:
                return new JsonPrimitive(
                        new LazilyParsedNumber(strings[payload]));
            case TRUE:
                return new JsonPrimitive(Boolean.TRUE);
            case FALSE:
                return new JsonPrimitive(Boolean.FALSE);
            case NULL:
                return JsonNull.INSTANCE;
            default: {
                JsonObject child = held(payload);
                if (child == null) {
                    child = register(payload);
                    pending.push(payload);
                    unfilled.push(child);
                }
                return child;
            }
        }
    }

    /** Reads the varints of {@link #code} from one offset on. */
    private final class Cursor {
        private int at;

        private Cursor(int at) {
            this.at = at;
        }

        private int next() {
            int value = 0;
            int shift = 0;
            while (true) {
                if (at >= code.length) {
                    throw new NoSuchElementException(
                            "expression code ends inside a value");
                }
                byte read = code[at++];
                value |= (read & 0x7F) << shift;
                if ((read & 0x80) == 0) return value;
                shift += 7;
            }
        }
    }

    /**
     * A table as its log states it, line by line ({@link
     * SessionExpressionLog#take}): each node once, children first, a child
     * named by its log number; each ref naming one.  A ref stated again
     * names its last node, where it was first stated.
     */
    static final class Builder {
        /** log node number -> node index. */
        private final Map<Long, Integer> numbered = new HashMap<Long, Integer>();
        private final Map<String, Integer> stringIndex =
                new HashMap<String, Integer>();
        private final List<String> strings = new ArrayList<String>();
        private byte[] code = new byte[256];
        private int length;
        private int[] offsets = new int[16];
        private int nodes;
        private final Map<String, Integer> refs =
                new LinkedHashMap<String, Integer>();

        /** One node line: {@code number}'s expression, each child an object
         *  naming an earlier node by its number ({@code isChild}). */
        void node(long number, JsonObject expression) {
            if (numbered.containsKey(number)) {
                throw new IllegalArgumentException(
                        "malformed session expression node " + number);
            }
            if (nodes == offsets.length) {
                offsets = Arrays.copyOf(offsets, nodes * 2);
            }
            offsets[nodes] = length;
            object(expression);
            numbered.put(number, nodes++);
        }

        /** One ref line: {@code ref} names node {@code number}. */
        void ref(String ref, long number) {
            refs.put(ref, index(number));
        }

        ExpressionTable build() {
            String[] names = new String[refs.size()];
            int[] nodesOf = new int[refs.size()];
            int at = 0;
            for (Map.Entry<String, Integer> ref : refs.entrySet()) {
                names[at] = ref.getKey();
                nodesOf[at++] = ref.getValue();
            }
            return new ExpressionTable(strings.toArray(new String[0]),
                    Arrays.copyOf(code, length), Arrays.copyOf(offsets, nodes),
                    names, nodesOf);
        }

        private int index(long number) {
            Integer index = numbered.get(number);
            if (index == null) {
                throw new IllegalArgumentException("session expression node "
                        + number + " is named before it is defined");
            }
            return index;
        }

        private void object(JsonObject object) {
            Set<Map.Entry<String, JsonElement>> members = object.entrySet();
            tagged(OBJECT, members.size());
            for (Map.Entry<String, JsonElement> member : members) {
                varint(string(member.getKey()));
                value(member.getValue());
            }
        }

        private void value(JsonElement value) {
            if (value == null || value.isJsonNull()) {
                tagged(NULL, 0);
            } else if (value.isJsonObject()) {
                JsonObject object = value.getAsJsonObject();
                Long child = SessionExpressionLog.childNumber(object);
                if (child != null) {
                    tagged(NODE, index(child));
                } else {
                    object(object);
                }
            } else if (value.isJsonArray()) {
                JsonArray array = value.getAsJsonArray();
                tagged(ARRAY, array.size());
                for (JsonElement element : array) value(element);
            } else {
                JsonPrimitive primitive = value.getAsJsonPrimitive();
                if (primitive.isBoolean()) {
                    tagged(primitive.getAsBoolean() ? TRUE : FALSE, 0);
                } else if (primitive.isNumber()) {
                    tagged(NUMBER, string(primitive.getAsString()));
                } else {
                    tagged(STRING, string(primitive.getAsString()));
                }
            }
        }

        private int string(String value) {
            Integer index = stringIndex.get(value);
            if (index == null) {
                index = strings.size();
                strings.add(value);
                stringIndex.put(value, index);
            }
            return index;
        }

        private void tagged(int tag, int payload) {
            varint(payload << 3 | tag);
        }

        private void varint(int value) {
            if (length + 5 > code.length) {
                code = Arrays.copyOf(code, code.length * 2);
            }
            int rest = value;
            while ((rest & ~0x7F) != 0) {
                code[length++] = (byte) (rest & 0x7F | 0x80);
                rest >>>= 7;
            }
            code[length++] = (byte) rest;
        }
    }
}
