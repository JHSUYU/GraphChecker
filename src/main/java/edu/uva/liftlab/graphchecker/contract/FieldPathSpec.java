package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.text;
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

    public static String leafOwner(String cell) {
        DeclaredField declared = declaredField(cell);
        if (declared == null) return "";
        return declared.owner();
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

    /** The unique complete declaration for an exact direct path, returned as
     *  the original immutable-by-convention wire value. */
    public static JsonObject exactLeafDeclaration(
            JsonObject action, List<String> expectedPath,
            String requiredAuthority) {
        if (action == null || expectedPath == null
                || expectedPath.size() < 2
                || !trimmed(requiredAuthority).equals(text(action,
                "fieldPathAuthority"))) {
            return null;
        }
        JsonElement encoded = action.get("fieldPathLeafDeclarations");
        if (encoded == null || !encoded.isJsonArray()) return null;
        JsonObject selected = null;
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) continue;
            JsonObject declaration = element.getAsJsonObject();
            if (!expectedPath.equals(stringArray(declaration,
                    "fieldPath"))) {
                continue;
            }
            DeclaredField leaf = declaredField(text(declaration,
                    "fieldSignature"));
            if (leaf == null
                    || !leaf.name().equals(expectedPath.get(
                    expectedPath.size() - 1))) {
                continue;
            }
            if (selected != null) return null;
            selected = declaration;
        }
        return selected;
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
