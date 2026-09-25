package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

/** Soot field declaration and field-path parser; a value parser, not an
 *  admission layer. */
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

    /** Dotted label of a field path; "" when empty or any segment is blank. A
     *  blank segment names no field ({@code a..b} would match no written
     *  symbol); Runtime and Solver share this so their labels cannot drift. */
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
        return strings(object == null ? null : object.get(member));
    }

    /** Non-blank trimmed strings of an array; empty when any entry is not. */
    private static List<String> strings(JsonElement value) {
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
            List<String> path = strings(element);
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
