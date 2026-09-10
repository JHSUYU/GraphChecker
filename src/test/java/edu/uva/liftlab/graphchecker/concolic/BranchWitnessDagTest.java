package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertSame;

/** Branch witnesses keep expression DAG sharing without weakening public copies. */
public class BranchWitnessDagTest {

    @Test
    public void immutableCaptureUsesCowAndKeepsDecoderIdentities() {
        JsonObject predicate = doublingPredicate(40);
        predicate.add("unused", JsonNull.INSTANCE);
        JsonElement child = predicate.get("_left");
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization",
                BranchWitness.IDENTITY_NORMALIZATION);

        BranchWitness witness = BranchWitness.vmPcImmutable("SITE", "method",
                3, 1, true, predicate, 7, metadata);
        JsonObject view = witness.sourceSatisfiedPredicateView()
                .getAsJsonObject();
        assertNotSame(predicate, view);
        assertSame(child, view.get("_left"));
        assertSame(view.get("_left"), view.get("_right"));
        assertSame(view, witness.toImmutableJsonView().get(
                "sourceSatisfiedPredicate"));
    }

    private static JsonObject doublingPredicate(int depth) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", "x");
        for (int index = 0; index < depth; index++) {
            JsonObject parent = new JsonObject();
            parent.addProperty("_type", "BinaryExpression");
            parent.add("_left", expression);
            parent.addProperty("_op", "==");
            parent.add("_right", expression);
            expression = parent;
        }
        return expression;
    }
}
