package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.primitiveString;

public final class SessionExpressionLog {
    public static final String KIND = "SESSION_EXPRESSION_LOG";
    public static final int SCHEMA_VERSION = 1;
    static final String NODE_TYPE = "SessionExpressionNode";
    private static final String NODE = "node";
    private static final String REF = "ref";
    private static final String EXPRESSION = "expression";

    private SessionExpressionLog() {
    }

    public static JsonObject header() {
        JsonObject header = new JsonObject();
        header.addProperty("kind", KIND);
        header.addProperty("schemaVersion", SCHEMA_VERSION);
        return header;
    }

    static boolean expression(JsonElement value) {
        if (value == null || !value.isJsonObject()) return false;
        JsonElement type = value.getAsJsonObject().get("_type");
        return type != null && type.isJsonPrimitive()
                && !type.getAsString().isEmpty()
                && !NODE_TYPE.equals(type.getAsString());
    }

    public static final class Writer {
        private final Map<JsonElement, Long> numbers =
                new IdentityHashMap<JsonElement, Long>();

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

    static ExpressionTable read(Path file, RowPool pool) throws IOException {
        if (file == null || !Files.isRegularFile(file)) {
            throw new IllegalArgumentException(
                    "the session published no expression log: no " + file);
        }
        ExpressionTable.Builder table = new ExpressionTable.Builder();
        try (BufferedReader in = ArtifactIO.lines(file)) {
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
                } else {
                    take(table, row);
                }
            }
            if (!headed) {
                throw new IllegalArgumentException(
                        "the session expression log " + file
                                + " states no header");
            }
        }
        return table.build();
    }

    static void take(ExpressionTable.Builder table, JsonObject row) {
        if (row.has(REF)) {
            table.ref(primitiveString(row, REF), row.get(NODE).getAsLong());
            return;
        }
        long number = row.get(NODE).getAsLong();
        JsonElement expression = row.get(EXPRESSION);
        if (expression == null || !expression.isJsonObject()) {
            throw new IllegalArgumentException(
                    "malformed session expression node " + number);
        }
        table.node(number, expression.getAsJsonObject());
    }

    static Long childNumber(JsonObject value) {
        return NODE_TYPE.equals(primitiveString(value, "_type"))
                ? Long.valueOf(value.get(NODE).getAsLong()) : null;
    }
}
