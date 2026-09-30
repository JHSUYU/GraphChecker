package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

/**
 * CONTRACT-SPEC §2.3: the session's expressions, ref to the VM's expression
 * object unchanged.  Rows carry refs into this shared DAG, never inlined
 * trees; the file holds it as a DAG too ({@link SessionExpressionLog}).
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

    @Override
    Object[] parts() {
        return new Object[] {expressions};
    }

    @Override
    public String toString() {
        return "ExpressionTable{" + expressions.size() + " expressions}";
    }
}
