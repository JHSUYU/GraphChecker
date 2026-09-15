package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.text;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.trimmed;

/**
 * Static field-input materialization selected by exact analysis sites; runtime
 * planning projects it into an execution action once concrete object identity
 * has been selected.
 */
public final class MaterializationSpec {
    public enum Kind {
        NONE, ACCESSOR_RETURN
    }

    private final Kind kind;
    private final String javaType;
    private final String rootField;
    private final List<String> path;
    private final String method;
    private final int unitIndex;
    private final String declaredCallee;
    private final String implementationMethod;

    private MaterializationSpec(
            Kind kind, String javaType, String rootField,
            List<String> path, String method, int unitIndex,
            String declaredCallee,
            String implementationMethod) {
        this.kind = kind == null ? Kind.NONE : kind;
        this.javaType = trimmed(javaType);
        this.rootField = trimmed(rootField);
        this.path = immutable(path);
        this.method = trimmed(method);
        this.unitIndex = unitIndex;
        this.declaredCallee = trimmed(declaredCallee);
        this.implementationMethod = trimmed(implementationMethod);
        if (this.kind == Kind.ACCESSOR_RETURN) {
            validateAccessorReturn();
        }
    }

    private static MaterializationSpec none() {
        return new MaterializationSpec(Kind.NONE, "", "",
                Collections.<String>emptyList(), "", -1, "", "");
    }

    /** Region artifacts keep accessor identity in the port's canonical flat
     *  fields, the only representation any producer writes. */
    public static MaterializationSpec decode(JsonObject port) {
        if (!"ACCESSOR_RETURN".equals(text(port, "sourceKind"))) {
            return none();
        }
        String field = text(port, "declaredFieldSignature");
        String method = text(port, "callerMethod");
        int unitIndex = optionalInteger(port, "unitIndex", -1);
        String declaredCallee = text(port, "declaredCallee");
        String implementation = text(port,
                "accessorImplementationMethod");
        List<String> path = FieldPathSpec.stringArray(port, "fieldPath");
        String javaType = text(port, "javaType");
        if (field.isEmpty() || method.isEmpty() || unitIndex < 0
                || declaredCallee.isEmpty() || implementation.isEmpty()
                || path.isEmpty() || javaType.isEmpty()) {
            throw new IllegalArgumentException(
                    "ACCESSOR_RETURN requires its complete canonical fields");
        }
        return new MaterializationSpec(Kind.ACCESSOR_RETURN, javaType,
                field, path, method, unitIndex, declaredCallee,
                implementation);
    }

    /** Flat execution-action projection consumed by the custom-JDK bridge. */
    public Map<String, Object> actionFields() {
        Map<String, Object> result = new LinkedHashMap<>();
        if (kind == Kind.NONE) return result;
        result.put("bindingMode", "FIELD_ACCESS");
        result.put("javaType", javaType);
        result.put("accessFieldSignature", rootField);
        result.put("leafFieldSignature", rootField);
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
        // One field: the port names the accessed declaration once, so root
        // and leaf were always the same field and the path is its own name.
        if (root == null || path.size() != 1
                || !root.name().equals(path.get(0))
                || !root.type().equals(javaType)
                || method.isEmpty() || unitIndex < 0
                || declaredCallee.isEmpty()
                || implementationMethod.isEmpty()) {
            throw new IllegalArgumentException(
                    "ACCESSOR_RETURN requires an exact root-to-leaf path "
                            + "and call site");
        }
    }

    private static List<String> immutable(List<String> values) {
        return Collections.unmodifiableList(new ArrayList<>(
                values == null ? Collections.<String>emptyList() : values));
    }
}
