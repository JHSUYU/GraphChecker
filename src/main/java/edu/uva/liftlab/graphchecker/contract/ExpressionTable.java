package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * CONTRACT-SPEC 2: the session's {@code expressions.json}, ref to the VM's
 * expression object unchanged.  Rows carry refs into this shared DAG, never
 * inlined trees.
 */
public final class ExpressionTable extends Value {
    private final Map<String, JsonObject> expressions;

    private ExpressionTable(Map<String, JsonObject> expressions) {
        this.expressions = expressions;
    }

    public static ExpressionTable of(Map<String, JsonObject> expressions) {
        return new ExpressionTable(Fields.copy(expressions));
    }

    /** The empty table: a session that propagated nothing. */
    public static ExpressionTable empty() {
        return new ExpressionTable(Collections.<String, JsonObject>emptyMap());
    }

    /** Reads the file's object form: one member per reference. */
    public static ExpressionTable fromJson(JsonObject json) {
        Map<String, JsonObject> expressions = new LinkedHashMap<>();
        for (Map.Entry<String, JsonElement> member : json.entrySet()) {
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

    public JsonObject toJson() {
        JsonObject json = new JsonObject();
        for (Map.Entry<String, JsonObject> entry : expressions.entrySet()) {
            json.add(entry.getKey(), entry.getValue());
        }
        return json;
    }

    @Override
    Object[] parts() {
        return new Object[] {expressions};
    }

    @Override
    public String toString() {
        return "ExpressionTable{" + expressions.size() + " expressions}";
    }
}
