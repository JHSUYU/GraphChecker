package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

public class SolverPathContextTest {
    @Test
    public void positionedArrayRelationRoundTripsByContent() {
        JsonObject relation = arrayLoad(1);
        JsonArray path = new JsonArray();
        path.add(relation);
        path.add(binaryPredicate());

        SolverPathContext context = SolverPathContext.fromPath(path,
                Collections.<Integer>emptySet(), 1);
        SolverPathContext decoded = SolverPathContext.fromJson(
                context.toJson());

        assertEquals(1, decoded.size());
        assertEquals(relation, decoded.expressions().get(0));
        assertFalse(decoded.toJson().has("contextId"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void unwitnessedBooleanPredicateIsNotReclassifiedAsContext() {
        JsonArray path = new JsonArray();
        path.add(binaryPredicate());
        path.add(binaryPredicate());
        SolverPathContext.fromPath(path,
                Collections.<Integer>emptySet(), 1);
    }

    private static JsonObject arrayLoad(int indexValue) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "_array_expr");
        result.addProperty("_arr_str", "AL_1");
        result.addProperty("_is_load", true);
        JsonObject index = new JsonObject();
        index.addProperty("_type", "ConstExpr");
        index.addProperty("_java_type", "I");
        index.addProperty("_exp", "Y_I_" + indexValue);
        result.add("_index_exp", index);
        JsonObject value = new JsonObject();
        value.addProperty("_type", "SymbolExpression");
        value.addProperty("_java_type", "Lexample/State;");
        value.addProperty("_exp", "EL_1-0-1");
        result.add("_value_exp", value);
        return result;
    }

    private static JsonObject binaryPredicate() {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_op", "==");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "Z");
        left.addProperty("_exp", "M_Z_field_REGION.1.in.0_example/Leaf");
        result.add("_left", left);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "Z");
        right.addProperty("_exp", "Y_Z_0");
        result.add("_right", right);
        return result;
    }
}
