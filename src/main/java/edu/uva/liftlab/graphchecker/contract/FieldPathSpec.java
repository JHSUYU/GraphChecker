package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Canonical parser for Soot field declarations and projected field paths.
 *
 * <p>This is deliberately a value parser, not another admission layer.
 * Static analysis proves the access site; Scheduler and Runtime consume that
 * proof through the same declaration/path representation.</p>
 */
public final class FieldPathSpec {
    private static final Pattern DECLARED_FIELD = Pattern.compile(
            "<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>");
    private static final Pattern PROJECTION = Pattern.compile(
            "#field:([^#]+)");

    private FieldPathSpec() {
    }

    /** Parses only the canonical field declaration before any projections. */
    public static DeclaredField declaredField(String cell) {
        String value = trim(cell);
        int projection = value.indexOf("#field:");
        String base = projection < 0 ? value
                : value.substring(0, projection);
        Matcher matcher = DECLARED_FIELD.matcher(base);
        return matcher.matches()
                ? new DeclaredField(matcher.group(1), matcher.group(2),
                matcher.group(3))
                : null;
    }

    /** Returns the declared root field followed by every projected segment. */
    public static List<String> path(String cell) {
        List<String> result = new ArrayList<>();
        DeclaredField declared = declaredField(cell);
        if (declared != null) result.add(declared.name());
        Matcher matcher = PROJECTION.matcher(trim(cell));
        while (matcher.find()) {
            String segment = trim(matcher.group(1));
            if (!segment.isEmpty()) result.add(segment);
        }
        return Collections.unmodifiableList(result);
    }

    public static String accessOwner(String cell) {
        DeclaredField declared = declaredField(cell);
        return declared == null ? "" : declared.owner();
    }

    public static String leafOwner(String cell) {
        DeclaredField declared = declaredField(cell);
        if (declared == null) return "";
        return trim(cell).contains("#field:")
                ? declared.type() : declared.owner();
    }

    public static String leafName(String cell) {
        List<String> path = path(cell);
        return path.isEmpty() ? "" : path.get(path.size() - 1);
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
            String text = trim(element.getAsString());
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

    /**
     * Returns the unique complete declaration for an exact direct path.
     * The returned row is the original immutable-by-convention wire value.
     */
    public static JsonObject exactLeafDeclaration(
            JsonObject action, List<String> expectedPath,
            String requiredAuthority) {
        if (action == null || expectedPath == null
                || expectedPath.size() < 2
                || !trim(requiredAuthority).equals(text(action,
                "fieldPathAuthority"))) {
            return null;
        }
        JsonElement encoded = action.get("fieldPathLeafDeclarations");
        if (encoded == null || !encoded.isJsonArray()) return null;
        JsonObject selected = null;
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) continue;
            JsonObject declaration = element.getAsJsonObject();
            if (!booleanValue(declaration, "complete")
                    || !expectedPath.equals(stringArray(declaration,
                    "fieldPath"))) {
                continue;
            }
            DeclaredField leaf = declaredField(text(declaration,
                    "fieldSignature"));
            if (leaf == null
                    || !leaf.owner().equals(text(declaration,
                    "declaredFieldOwnerClass"))
                    || !leaf.type().equals(text(declaration,
                    "declaredFieldType"))
                    || !leaf.name().equals(expectedPath.get(
                    expectedPath.size() - 1))) {
                continue;
            }
            if (selected != null) return null;
            selected = declaration;
        }
        return selected;
    }

    private static String text(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonPrimitive()
                ? trim(value.getAsString()) : "";
    }

    private static boolean booleanValue(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonPrimitive()
                && value.getAsBoolean();
    }

    private static String trim(String value) {
        return value == null ? "" : value.trim();
    }

    public static final class DeclaredField {
        private final String owner;
        private final String type;
        private final String name;

        private DeclaredField(String owner, String type, String name) {
            this.owner = trim(owner);
            this.type = trim(type);
            this.name = trim(name);
        }

        public String owner() {
            return owner;
        }

        public String type() {
            return type;
        }

        public String name() {
            return name;
        }

        public String signature() {
            return "<" + owner + ": " + type + " " + name + ">";
        }
    }
}
