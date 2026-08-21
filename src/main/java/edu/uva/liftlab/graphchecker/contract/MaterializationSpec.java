package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;

/**
 * Static field-input materialization selected by exact analysis sites.
 *
 * <p>The static artifact stores this value once under {@code materialization}.
 * Runtime planning projects it into an execution action after concrete object
 * identity has been selected.</p>
 */
public final class MaterializationSpec {
    public enum Kind {
        NONE, ACCESSOR_RETURN
    }

    private final Kind kind;
    private final String javaType;
    private final String rootField;
    private final String leafField;
    private final List<String> path;
    private final String method;
    private final int unitIndex;
    private final String declaredCallee;
    private final String implementationMethod;

    private MaterializationSpec(
            Kind kind, String javaType, String rootField, String leafField,
            List<String> path, String method, int unitIndex,
            String declaredCallee,
            String implementationMethod) {
        this.kind = kind == null ? Kind.NONE : kind;
        this.javaType = trim(javaType);
        this.rootField = trim(rootField);
        this.leafField = trim(leafField);
        this.path = immutable(path);
        this.method = trim(method);
        this.unitIndex = unitIndex;
        this.declaredCallee = trim(declaredCallee);
        this.implementationMethod = trim(implementationMethod);
        if (this.kind == Kind.ACCESSOR_RETURN) {
            validateAccessorReturn();
        }
    }

    private static MaterializationSpec none() {
        return new MaterializationSpec(Kind.NONE, "", "", "",
                Collections.<String>emptyList(), "", -1, "", "");
    }

    /**
     * Region artifacts keep accessor identity in the port's canonical flat
     * fields, and that is the only representation any producer writes.
     */
    public static MaterializationSpec decode(JsonObject port) {
        if (!"ACCESSOR_RETURN".equals(text(port, "sourceKind"))) {
            return none();
        }
        String field = text(port, "declaredFieldSignature");
        if (field.isEmpty()) field = text(port, "cell");
        String method = text(port, "callerMethod");
        int unitIndex = integer(port, "unitIndex", -1);
        String declaredCallee = text(port, "declaredCallee");
        String implementation = text(port,
                "accessorImplementationMethod");
        List<String> path = FieldPathSpec.stringArray(port, "fieldPath");
        String javaType = text(port, "javaType");
        if (field.isEmpty() || method.isEmpty() || unitIndex < 0
                || declaredCallee.isEmpty() || implementation.isEmpty()
                || path.isEmpty() || javaType.isEmpty()) {
            return none();
        }
        return new MaterializationSpec(Kind.ACCESSOR_RETURN, javaType,
                field, field, path, method, unitIndex, declaredCallee,
                implementation);
    }

    /** Java type of the value bound to the logical input port. */
    public static String logicalJavaType(JsonObject port) {
        MaterializationSpec materialization = decode(port);
        return materialization.javaType.isEmpty()
                ? text(port, "javaType") : materialization.javaType;
    }

    public Kind kind() {
        return kind;
    }

    public String leafField() {
        return leafField;
    }

    public List<String> path() {
        return path;
    }

    public String method() {
        return method;
    }

    public String siteId() {
        return method.isEmpty() || unitIndex < 0 ? ""
                : method + "#u" + unitIndex;
    }

    public String declaredCallee() {
        return declaredCallee;
    }

    public String implementationMethod() {
        return implementationMethod;
    }

    /** Flat execution-action projection consumed by the custom-JDK bridge. */
    public Map<String, Object> actionFields() {
        Map<String, Object> result = new LinkedHashMap<>();
        if (kind == Kind.NONE) return result;
        result.put("bindingMode", "FIELD_ACCESS");
        result.put("javaType", javaType);
        result.put("accessFieldSignature", rootField);
        result.put("leafFieldSignature", leafField);
        result.put("fieldPath", new ArrayList<>(path));
        result.put("accessorCallerMethod", method);
        result.put("accessorCallUnitIndex", unitIndex);
        result.put("accessorDeclaredCallee", declaredCallee);
        result.put("accessorImplementationMethod", implementationMethod);
        return result;
    }

    private void validateAccessorReturn() {
        FieldPathSpec.DeclaredField root =
                FieldPathSpec.declaredField(rootField);
        FieldPathSpec.DeclaredField leaf =
                FieldPathSpec.declaredField(leafField);
        if (root == null || leaf == null || path.isEmpty()
                || !root.name().equals(path.get(0))
                || !leaf.name().equals(path.get(path.size() - 1))
                || !leaf.type().equals(javaType)
                || method.isEmpty() || unitIndex < 0
                || declaredCallee.isEmpty()
                || implementationMethod.isEmpty()) {
            throw new IllegalArgumentException(
                    "ACCESSOR_RETURN requires an exact root-to-leaf path "
                            + "and call site");
        }
        if (rootField.equals(leafField)) {
            if (path.size() != 1) {
                throw new IllegalArgumentException(
                        "direct accessor materialization requires one field");
            }
            return;
        }
        String rootDescriptor = javaTypeDescriptor(root.type());
        if (path.size() < 2 || !rootDescriptor.startsWith("L")
                || !rootDescriptor.endsWith(";")) {
            throw new IllegalArgumentException(
                    "nested accessor materialization requires a reference "
                            + "root and complete field path");
        }
    }

    private static List<String> immutable(List<String> values) {
        return Collections.unmodifiableList(new ArrayList<>(
                values == null ? Collections.<String>emptyList() : values));
    }

    private static String text(JsonObject json, String member) {
        JsonElement value = json == null ? null : json.get(member);
        return value != null && value.isJsonPrimitive()
                ? trim(value.getAsString()) : "";
    }

    private static int integer(JsonObject json, String member, int fallback) {
        JsonElement value = json == null ? null : json.get(member);
        try {
            return value != null && value.isJsonPrimitive()
                    ? value.getAsInt() : fallback;
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String trim(String value) {
        return value == null ? "" : value.trim();
    }
}
