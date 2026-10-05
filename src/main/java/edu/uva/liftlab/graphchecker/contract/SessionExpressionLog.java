package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.primitiveString;

/**
 * CONTRACT-SPEC §2.3: a session's {@code expressions.jsonl}, the DAG its rows'
 * refs name, appended as the replay files it: a header line, then each
 * expression node once (children first, a child named by its session-local
 * node number), and one line per ref naming its node.
 *
 * <p>Append-only, so a killed replay keeps every line it flushed and nothing
 * is ever written twice.  The table was one JSON object rewritten whole
 * every 30 s, content-addressed by SHA-256 in the concolic interpreter; the
 * rewrites and the hashing were most of a large replay's publication.</p>
 */
public final class SessionExpressionLog {
    public static final String KIND = "SESSION_EXPRESSION_LOG";
    public static final int SCHEMA_VERSION = 1;
    /** An expression's child, named by its node number. */
    static final String NODE_TYPE = "SessionExpressionNode";
    private static final String NODE = "node";
    private static final String REF = "ref";
    private static final String EXPRESSION = "expression";

    private SessionExpressionLog() {
    }

    /** The first line of every log. */
    public static JsonObject header() {
        JsonObject header = new JsonObject();
        header.addProperty("kind", KIND);
        header.addProperty("schemaVersion", SCHEMA_VERSION);
        return header;
    }

    /** An expression node: an object that names its {@code _type}. */
    static boolean expression(JsonElement value) {
        if (value == null || !value.isJsonObject()) return false;
        JsonElement type = value.getAsJsonObject().get("_type");
        return type != null && type.isJsonPrimitive()
                && !type.getAsString().isEmpty()
                && !NODE_TYPE.equals(type.getAsString());
    }

    /** Numbers the nodes one session's log has written, by identity. */
    public static final class Writer {
        private final Map<JsonElement, Long> numbers =
                new IdentityHashMap<JsonElement, Long>();

        /**
         * The lines that file one ref: each node of {@code expression} not
         * yet written, children first, then the ref's own line.  Iterative:
         * a chain nests thousands deep.
         */
        public List<JsonObject> lines(String ref, JsonObject expression) {
            List<JsonObject> lines = new ArrayList<JsonObject>();
            Deque<JsonObject> pending = new ArrayDeque<JsonObject>();
            Deque<Boolean> expanded = new ArrayDeque<Boolean>();
            Map<JsonElement, Boolean> active =
                    new IdentityHashMap<JsonElement, Boolean>();
            pending.push(expression);
            expanded.push(Boolean.FALSE);
            while (!pending.isEmpty()) {
                JsonObject node = pending.pop();
                boolean children = expanded.pop();
                if (numbers.containsKey(node)) continue;
                if (!children) {
                    if (active.put(node, Boolean.TRUE) != null) {
                        throw new IllegalArgumentException(
                                "cyclic expression graph at " + ref);
                    }
                    pending.push(node);
                    expanded.push(Boolean.TRUE);
                    for (JsonObject child : children(node)) {
                        if (!numbers.containsKey(child)) {
                            pending.push(child);
                            expanded.push(Boolean.FALSE);
                        }
                    }
                    continue;
                }
                long number = numbers.size() + 1L;
                JsonObject line = new JsonObject();
                line.addProperty(NODE, number);
                line.add(EXPRESSION, numbered(node));
                lines.add(line);
                numbers.put(node, number);
                active.remove(node);
            }
            JsonObject line = new JsonObject();
            line.addProperty(REF, ref);
            line.addProperty(NODE, numbers.get(expression));
            lines.add(line);
            return lines;
        }

        /** The node's own members, each child node by its number. */
        private JsonObject numbered(JsonObject node) {
            JsonObject copy = new JsonObject();
            for (Map.Entry<String, JsonElement> member : node.entrySet()) {
                copy.add(member.getKey(), inline(member.getValue()));
            }
            return copy;
        }

        private JsonElement inline(JsonElement value) {
            if (expression(value)) {
                JsonObject child = new JsonObject();
                child.addProperty("_type", NODE_TYPE);
                child.addProperty(NODE, numbers.get(value));
                return child;
            }
            if (value != null && value.isJsonArray()) {
                JsonArray copy = new JsonArray();
                for (JsonElement element : value.getAsJsonArray()) {
                    copy.add(inline(element));
                }
                return copy;
            }
            if (value != null && value.isJsonObject()) {
                return numbered(value.getAsJsonObject());
            }
            return value;
        }
    }

    /** The expression nodes one node holds, through its own arrays and
     *  plain objects. */
    private static List<JsonObject> children(JsonObject node) {
        List<JsonObject> found = new ArrayList<JsonObject>();
        Deque<JsonElement> inline = new ArrayDeque<JsonElement>(
                node.asMap().values());
        while (!inline.isEmpty()) {
            JsonElement value = inline.pop();
            if (expression(value)) {
                found.add(value.getAsJsonObject());
            } else if (value != null && value.isJsonArray()) {
                for (JsonElement element : value.getAsJsonArray()) {
                    inline.push(element);
                }
            } else if (value != null && value.isJsonObject()) {
                inline.addAll(value.getAsJsonObject().asMap().values());
            }
        }
        return found;
    }

    /**
     * The table one log states.  A session opens its log with the header
     * ({@code SessionPublisher}), so a missing or headless file was never
     * published, and is refused: read as the empty table, every row's ref
     * came out UNSTATED_VALUE and hid the missing file (hdfs-17960's
     * offline compose).  Its strings come from {@code pool}.
     */
    static ExpressionTable read(Path file, RowPool pool) throws IOException {
        if (file == null || !Files.isRegularFile(file)) {
            throw new IllegalArgumentException(
                    "the session published no expression log: no " + file);
        }
        Map<Long, JsonObject> nodes = new LinkedHashMap<Long, JsonObject>();
        Map<String, JsonObject> refs = new LinkedHashMap<String, JsonObject>();
        try (BufferedReader in = Files.newBufferedReader(file,
                StandardCharsets.UTF_8)) {
            String line;
            boolean headed = false;
            while ((line = in.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonObject row = RowCodec.fromLine(line, pool);
                if (!headed) {
                    if (!KIND.equals(primitiveString(row, "kind")) || !row.has(
                            "schemaVersion") || row.get("schemaVersion")
                            .getAsInt() != SCHEMA_VERSION) {
                        throw new IllegalArgumentException(
                                "unsupported session expression log header");
                    }
                    headed = true;
                } else if (row.has(REF)) {
                    refs.put(primitiveString(row, REF), node(nodes, row));
                } else {
                    long number = row.get(NODE).getAsLong();
                    JsonElement expression = row.get(EXPRESSION);
                    if (expression == null || !expression.isJsonObject()
                            || nodes.containsKey(number)) {
                        throw new IllegalArgumentException(
                                "malformed session expression node " + number);
                    }
                    nodes.put(number, resolved(nodes,
                            expression.getAsJsonObject()));
                }
            }
            if (!headed) {
                throw new IllegalArgumentException(
                        "the session expression log " + file
                                + " states no header");
            }
        }
        return ExpressionTable.of(refs);
    }

    /** One line's node, each child by the node an earlier line defined. */
    private static JsonObject resolved(Map<Long, JsonObject> nodes,
                                       JsonObject node) {
        Deque<JsonElement> inline = new ArrayDeque<JsonElement>();
        inline.push(node);
        while (!inline.isEmpty()) {
            JsonElement value = inline.pop();
            if (value.isJsonArray()) {
                JsonArray array = value.getAsJsonArray();
                for (int index = 0; index < array.size(); index++) {
                    JsonElement element = array.get(index);
                    if (numbered(element)) {
                        array.set(index, node(nodes, element.getAsJsonObject()));
                    } else if (!element.isJsonPrimitive()) {
                        inline.push(element);
                    }
                }
            } else if (value.isJsonObject()) {
                for (Map.Entry<String, JsonElement> member
                        : value.getAsJsonObject().entrySet()) {
                    JsonElement element = member.getValue();
                    if (numbered(element)) {
                        member.setValue(node(nodes,
                                element.getAsJsonObject()));
                    } else if (!element.isJsonPrimitive()
                            && !element.isJsonNull()) {
                        inline.push(element);
                    }
                }
            }
        }
        return node;
    }

    private static boolean numbered(JsonElement value) {
        return value != null && value.isJsonObject() && NODE_TYPE.equals(
                primitiveString(value.getAsJsonObject(), "_type"));
    }

    private static JsonObject node(Map<Long, JsonObject> nodes,
                                   JsonObject naming) {
        long number = naming.get(NODE).getAsLong();
        JsonObject node = nodes.get(number);
        if (node == null) {
            throw new IllegalArgumentException(
                    "session expression node " + number
                            + " is named before it is defined");
        }
        return node;
    }
}
