package edu.uva.liftlab.graphchecker.d3.contract;

import com.google.gson.JsonObject;

import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * CONTRACT-SPEC 2: the session's {@code expressions.json}.
 *
 * <p>{@code ref -> expression JSON}: the VM's expression objects,
 * unchanged.  Rows carry references, not
 * trees: the VM propagates values as a shared DAG and a row that inlined its
 * expression would restate its whole upstream history at every handoff.</p>
 */
public final class ExpressionTable {
    private final Map<String, JsonObject> expressions;

    private ExpressionTable(Map<String, JsonObject> expressions) {
        this.expressions = expressions;
    }

    public static ExpressionTable of(Map<String, JsonObject> expressions) {
        return new ExpressionTable(Fields.copy(expressions));
    }

    /** The empty table: a session that propagated nothing. */
    public static ExpressionTable empty() {
        return new ExpressionTable(Fields.<String, JsonObject>copy(null));
    }

    /** Reads the file's object form: one member per reference. */
    public static ExpressionTable fromJson(JsonObject json) {
        if (json == null) return empty();
        java.util.Map<String, JsonObject> expressions =
                new java.util.LinkedHashMap<>();
        for (Map.Entry<String, com.google.gson.JsonElement> member
                : json.entrySet()) {
            if (!member.getValue().isJsonObject()) {
                throw new IllegalArgumentException(
                        "expression " + member.getKey() + " is not an object");
            }
            expressions.put(member.getKey(),
                    member.getValue().getAsJsonObject());
        }
        return of(expressions);
    }

    /** The expression behind one reference, or {@code null}. */
    public JsonObject expression(String ref) {
        return ref == null ? null : expressions.get(ref);
    }

    public Set<String> refs() {
        return expressions.keySet();
    }

    public Map<String, JsonObject> expressions() {
        return expressions;
    }

    public boolean isEmpty() {
        return expressions.isEmpty();
    }

    public JsonObject toJson() {
        JsonObject json = new JsonObject();
        for (Map.Entry<String, JsonObject> entry : expressions.entrySet()) {
            json.add(entry.getKey(), entry.getValue());
        }
        return json;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ExpressionTable)) return false;
        return expressions.equals(((ExpressionTable) value).expressions);
    }

    @Override
    public int hashCode() {
        return Objects.hash(expressions);
    }

    @Override
    public String toString() {
        return "ExpressionTable{" + expressions.size() + " expressions}";
    }
}
