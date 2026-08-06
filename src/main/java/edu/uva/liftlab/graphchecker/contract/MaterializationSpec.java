package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

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
        NONE, FIELD_READ, ACCESSOR_RETURN
    }

    private final Kind kind;
    private final String javaType;
    private final String rootField;
    private final String leafField;
    private final List<String> path;
    private final List<String> proofEdgeIds;
    private final List<String> accessSites;
    private final String method;
    private final int unitIndex;
    private final String declaredCallee;
    private final String implementationMethod;

    private MaterializationSpec(
            Kind kind, String javaType, String rootField, String leafField,
            List<String> path, List<String> proofEdgeIds,
            Collection<String> accessSites, String method, int unitIndex,
            String declaredCallee,
            String implementationMethod) {
        this.kind = kind == null ? Kind.NONE : kind;
        this.javaType = trim(javaType);
        this.rootField = trim(rootField);
        this.leafField = trim(leafField);
        this.path = immutable(path);
        this.proofEdgeIds = immutable(proofEdgeIds);
        this.accessSites = immutableSites(accessSites);
        this.method = trim(method);
        this.unitIndex = unitIndex;
        this.declaredCallee = trim(declaredCallee);
        this.implementationMethod = trim(implementationMethod);
        if (this.kind == Kind.FIELD_READ && this.accessSites.isEmpty()) {
            throw new IllegalArgumentException(
                    "FIELD_READ materialization requires accessSites");
        }
        if (this.kind == Kind.ACCESSOR_RETURN) {
            validateAccessorReturn();
        }
    }

    public static MaterializationSpec none() {
        return new MaterializationSpec(Kind.NONE, "", "", "",
                Collections.<String>emptyList(),
                Collections.<String>emptyList(),
                Collections.<String>emptyList(), "", -1, "", "");
    }

    public static MaterializationSpec fieldRead(
            String javaType, String rootField, String leafField,
            List<String> path, List<String> proofEdgeIds,
            Collection<String> accessSites) {
        return new MaterializationSpec(Kind.FIELD_READ, javaType,
                rootField, leafField, path, proofEdgeIds, accessSites,
                "", -1, "", "");
    }

    public static MaterializationSpec accessorReturn(
            String javaType, String field, List<String> path,
            String callerMethod, int unitIndex,
            String declaredCallee, String implementationMethod) {
        return accessorReturn(javaType, field, field, path, callerMethod,
                unitIndex, declaredCallee, implementationMethod);
    }

    /**
     * Materializes one demanded leaf below the object returned by an exact
     * accessor call.  The root and leaf declarations stay separate so a
     * transported reference is never mistaken for the symbolic value.
     */
    public static MaterializationSpec accessorReturn(
            String javaType, String rootField, String leafField,
            List<String> path, String callerMethod, int unitIndex,
            String declaredCallee, String implementationMethod) {
        return new MaterializationSpec(Kind.ACCESSOR_RETURN, javaType,
                rootField, leafField, path,
                Collections.<String>emptyList(),
                Collections.<String>emptyList(), callerMethod, unitIndex,
                declaredCallee,
                implementationMethod);
    }

    public static MaterializationSpec decode(JsonObject port) {
        JsonElement encoded = port == null ? null
                : port.get("materialization");
        if (encoded == null) return none();
        if (!encoded.isJsonObject()) {
            throw new IllegalArgumentException(
                    "materialization must be an object");
        }
        JsonObject json = encoded.getAsJsonObject();
        Kind kind;
        try {
            kind = Kind.valueOf(text(json, "kind"));
        } catch (IllegalArgumentException ignored) {
            throw new IllegalArgumentException(
                    "unsupported materialization kind");
        }
        return new MaterializationSpec(kind, text(json, "javaType"),
                text(json, "rootField"), text(json, "leafField"),
                FieldPathSpec.stringArray(json, "path"),
                FieldPathSpec.stringArray(json, "proofEdgeIds"),
                FieldPathSpec.stringArray(json, "accessSites"),
                text(json, "method"), integer(json, "unitIndex", -1),
                text(json, "declaredCallee"),
                text(json, "implementationMethod"));
    }

    /** Java type of the value bound to the logical input port. */
    public static String logicalJavaType(JsonObject port) {
        MaterializationSpec materialization = decode(port);
        return materialization.javaType.isEmpty()
                ? text(port, "javaType") : materialization.javaType;
    }

    public static boolean repeatedPrimitiveAccessorReturn(String cell) {
        return JavaPrimitiveBoxing.unboxReturn(cell);
    }

    public Kind kind() {
        return kind;
    }

    public String rootField() {
        return rootField;
    }

    public String leafField() {
        return leafField;
    }

    public List<String> path() {
        return path;
    }

    public List<String> accessSites() {
        return accessSites;
    }

    public boolean matchesAccessSite(String actualMethod,
                                     int actualUnitIndex) {
        return kind == Kind.FIELD_READ
                && accessSites.contains(trim(actualMethod)
                + "#u" + actualUnitIndex);
    }

    public String method() {
        return method;
    }

    public String siteId() {
        return method.isEmpty() || unitIndex < 0 ? ""
                : method + "#u" + unitIndex;
    }

    public int unitIndex() {
        return unitIndex;
    }

    public String declaredCallee() {
        return declaredCallee;
    }

    public String implementationMethod() {
        return implementationMethod;
    }

    public boolean directFieldPath() {
        return kind == Kind.FIELD_READ && path.size() > 1
                && !proofEdgeIds.isEmpty();
    }

    public Map<String, Object> toMap() {
        Map<String, Object> result = new LinkedHashMap<>();
        if (kind == Kind.NONE) return result;
        result.put("kind", kind.name());
        result.put("javaType", javaType);
        result.put("rootField", rootField);
        result.put("leafField", leafField);
        result.put("path", new ArrayList<>(path));
        if (!proofEdgeIds.isEmpty()) {
            result.put("proofEdgeIds", new ArrayList<>(proofEdgeIds));
        }
        if (kind == Kind.FIELD_READ) {
            result.put("accessSites", new ArrayList<>(accessSites));
        } else {
            result.put("method", method);
            result.put("unitIndex", unitIndex);
            result.put("declaredCallee", declaredCallee);
            result.put("implementationMethod", implementationMethod);
        }
        return result;
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
        if (kind == Kind.FIELD_READ) {
            result.put("accessSites", new ArrayList<>(accessSites));
            if (directFieldPath()) {
                result.put("fieldPathAuthority",
                        "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
            }
        } else {
            result.put("accessorCallerMethod", method);
            result.put("accessorCallUnitIndex", unitIndex);
            result.put("accessorDeclaredCallee", declaredCallee);
            result.put("accessorImplementationMethod",
                    implementationMethod);
        }
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

    private static List<String> immutableSites(Collection<String> values) {
        TreeSet<String> sorted = new TreeSet<>();
        if (values != null) {
            for (String value : values) {
                String site = trim(value);
                if (!site.isEmpty()) {
                    sorted.add(site);
                }
            }
        }
        return Collections.unmodifiableList(new ArrayList<>(sorted));
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
