package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Static field-input materialization selected by one exact analysis site.
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
    private final String method;
    private final String siteId;
    private final int unitIndex;
    private final String declaredCallee;
    private final String implementationMethod;

    private MaterializationSpec(
            Kind kind, String javaType, String rootField, String leafField,
            List<String> path, List<String> proofEdgeIds, String method,
            String siteId, int unitIndex, String declaredCallee,
            String implementationMethod) {
        this.kind = kind == null ? Kind.NONE : kind;
        this.javaType = trim(javaType);
        this.rootField = trim(rootField);
        this.leafField = trim(leafField);
        this.path = immutable(path);
        this.proofEdgeIds = immutable(proofEdgeIds);
        this.method = trim(method);
        this.siteId = trim(siteId);
        this.unitIndex = unitIndex;
        this.declaredCallee = trim(declaredCallee);
        this.implementationMethod = trim(implementationMethod);
    }

    public static MaterializationSpec none() {
        return new MaterializationSpec(Kind.NONE, "", "", "",
                Collections.<String>emptyList(),
                Collections.<String>emptyList(), "", "", -1, "", "");
    }

    public static MaterializationSpec fieldRead(
            String javaType, String rootField, String leafField,
            List<String> path, List<String> proofEdgeIds, String method,
            String siteId, int unitIndex) {
        return new MaterializationSpec(Kind.FIELD_READ, javaType,
                rootField, leafField, path, proofEdgeIds, method, siteId,
                unitIndex, "", "");
    }

    public static MaterializationSpec accessorReturn(
            String javaType, String field, List<String> path,
            String callerMethod, String siteId, int unitIndex,
            String declaredCallee, String implementationMethod) {
        return new MaterializationSpec(Kind.ACCESSOR_RETURN, javaType,
                field, field, path, Collections.<String>emptyList(),
                callerMethod, siteId, unitIndex, declaredCallee,
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
                text(json, "method"), text(json, "siteId"),
                integer(json, "unitIndex", -1),
                text(json, "declaredCallee"),
                text(json, "implementationMethod"));
    }

    public Kind kind() {
        return kind;
    }

    public String javaType() {
        return javaType;
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

    public String method() {
        return method;
    }

    public String siteId() {
        return siteId;
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
        result.put("method", method);
        result.put("siteId", siteId);
        result.put("unitIndex", unitIndex);
        if (kind == Kind.ACCESSOR_RETURN) {
            result.put("declaredCallee", declaredCallee);
            result.put("implementationMethod", implementationMethod);
        }
        return result;
    }

    /** Flat execution-action projection consumed by the custom-JDK bridge. */
    public Map<String, Object> actionFields() {
        Map<String, Object> result = new LinkedHashMap<>();
        if (kind == Kind.NONE) return result;
        FieldPathSpec.DeclaredField root =
                FieldPathSpec.declaredField(rootField);
        FieldPathSpec.DeclaredField leaf =
                FieldPathSpec.declaredField(leafField);
        result.put("bindingMode", "FIELD_ACCESS");
        result.put("javaType", javaType);
        result.put("accessFieldSignature", rootField);
        result.put("leafFieldSignature", leafField);
        result.put("fieldPath", new ArrayList<>(path));
        if (root != null) {
            result.put("accessOwnerClass", root.owner());
            result.put("accessFieldType", root.type());
            result.put("accessField", root.name());
        }
        if (leaf != null) {
            result.put("leafOwnerClass", leaf.owner());
            result.put("leafField", leaf.name());
        }
        if (kind == Kind.FIELD_READ) {
            result.put("accessMethod", method);
            result.put("accessSiteId", siteId);
            result.put("accessUnitIndex", unitIndex);
            result.put("accessSiteAuthority",
                    "STATIC_UNIQUE_EXACT_DECLARED_FIELD_READ_SITE_V1");
            if (directFieldPath()) {
                result.put("fieldPathAuthority",
                        "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
            }
        } else {
            result.put("accessorCallerMethod", method);
            result.put("accessorCallSiteId", siteId);
            result.put("accessorCallUnitIndex", unitIndex);
            result.put("accessorDeclaredCallee", declaredCallee);
            result.put("accessorImplementationMethod",
                    implementationMethod);
            result.put("accessorCallSiteAuthority",
                    "STATIC_UNIQUE_EXACT_DECLARED_FIELD_ACCESSOR_CALLSITE_V1");
            result.put("accessorImplementationAuthority",
                    "SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY");
        }
        return result;
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
