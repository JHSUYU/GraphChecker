package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.trimmed;

/**
 * Canonical parser for Soot field declarations and structured field paths.
 * Deliberately a value parser, not another admission layer: static analysis
 * proves the access site, and Scheduler and Runtime consume that proof
 * through this same representation.
 */
public final class FieldPathSpec {
    private static final Pattern DECLARED_FIELD = Pattern.compile(
            "<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>");
    private FieldPathSpec() {
    }

    public static DeclaredField declaredField(String cell) {
        String value = trimmed(cell);
        Matcher matcher = DECLARED_FIELD.matcher(value);
        return matcher.matches()
                ? new DeclaredField(matcher.group(1), matcher.group(2),
                matcher.group(3))
                : null;
    }

    public static List<String> path(String cell) {
        List<String> result = new ArrayList<>();
        DeclaredField declared = declaredField(cell);
        if (declared != null) result.add(declared.name());
        return Collections.unmodifiableList(result);
    }

    /**
     * The dotted label one field path spells, or empty when the path is
     * empty or any segment is blank.
     *
     * <p>Fail-closed on a blank segment: such a path names no field, and a
     * label built from it - {@code symbol.a..b} - would match an engine
     * symbol no materialization site ever wrote.  Runtime and Solver build
     * the same label here so their two answers cannot drift.</p>
     */
    public static String join(List<String> path) {
        if (path == null || path.isEmpty()) return "";
        StringBuilder result = new StringBuilder();
        for (String segment : path) {
            String value = trimmed(segment);
            if (value.isEmpty()) return "";
            if (result.length() > 0) result.append('.');
            result.append(value);
        }
        return result.toString();
    }

    public static List<String> stringArray(JsonObject object,
                                           String member) {
        JsonElement value = object == null ? null : object.get(member);
        if (value == null || !value.isJsonArray()) {
            return Collections.emptyList();
        }
        List<String> result = new ArrayList<>();
        for (JsonElement element : value.getAsJsonArray()) {
            if (!element.isJsonPrimitive()) return Collections.emptyList();
            String text = trimmed(element.getAsString());
            if (text.isEmpty()) return Collections.emptyList();
            result.add(text);
        }
        return Collections.unmodifiableList(result);
    }

    public static List<List<String>> paths(JsonObject object,
                                           String member) {
        JsonElement value = object == null ? null : object.get(member);
        if (value == null || !value.isJsonArray()) {
            return Collections.emptyList();
        }
        List<List<String>> result = new ArrayList<>();
        for (JsonElement element : value.getAsJsonArray()) {
            if (!element.isJsonArray()) return Collections.emptyList();
            JsonObject row = new JsonObject();
            row.add("path", element);
            List<String> path = stringArray(row, "path");
            if (path.isEmpty()) return Collections.emptyList();
            result.add(path);
        }
        return Collections.unmodifiableList(result);
    }

    public static boolean hasNonEmptyPaths(JsonObject object,
                                           String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonArray()
                && value.getAsJsonArray().size() > 0
                && paths(object, member).size()
                == value.getAsJsonArray().size();
    }

    public static final class DeclaredField {
        private final String owner;
        private final String type;
        private final String name;

        private DeclaredField(String owner, String type, String name) {
            this.owner = trimmed(owner);
            this.type = trimmed(type);
            this.name = trimmed(name);
        }

        public String owner() { return owner; }

        public String type() { return type; }

        public String name() { return name; }

        public String signature() {
            return "<" + owner + ": " + type + " " + name + ">";
        }
    }
}
