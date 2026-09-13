package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ConcolicConstraintSolverMaterializationTest {
    @Test
    public void materializesOccurrenceScopedBoundedScalarAction()
            throws Exception {
        Assume.assumeTrue(z3Available());

        String input = "REGION.timer.in.now";
        String raw = "M_J_field_" + input
                + ".occ.deadbeef_java/lang/Long";
        JsonObject target = binary(symbol(raw), ">", constant(10));
        JsonObject event = new JsonObject();
        event.addProperty("eventId", 1L);
        event.addProperty("contextId", 1L);
        BranchWitness source = BranchWitness.vmPcImmutable("TEST#u1",
                "<test.Timer: void run()>", 1, 1, false,
                BranchPredicateAlgebra.complement(target), 0, event);

        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 3);
        query.addProperty("kind", "REGION_PATH_FLIP");
        query.addProperty("queryKey", CanonicalJson.sha256("timer-query"));
        query.addProperty("regionId", "REGION.timer");
        query.addProperty("sourceActivationOccurrenceId",
                "test/node#epoch0/region/REGION.timer#1#a1");
        query.add("replayContract",
                BranchReplayContract.atSource(source).toJson());
        JsonObject context = new JsonObject();
        context.addProperty("schemaVersion", SolverPathContext.SCHEMA_VERSION);
        context.addProperty("kind", SolverPathContext.KIND);
        context.addProperty("authority", SolverPathContext.AUTHORITY);
        context.add("constraints", new JsonArray());
        query.add("solverPathContext", context);
        query.add("consumerAnchorCaseDependencies", new JsonArray());

        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("symbolicDemand", "BOUNDED_STATE_FRONTIER");
        action.addProperty("symbol", input);
        action.addProperty("javaType", "long");
        action.addProperty("observed", true);
        action.addProperty("primitiveValue", "0");
        JsonArray actions = new JsonArray();
        actions.add(action);
        JsonObject activation = new JsonObject();
        activation.add("inputActions", actions);

        ConcolicConstraintSolver.Result result =
                ConcolicConstraintSolver.solve(query,
                        Collections.singletonList(activation), activation,
                        Paths.get("z3"), 10_000L);

        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        assertEquals(input, result.modelAssignments.get(0).getAsJsonObject()
                .get("inputSymbol").getAsString());
    }

    private static JsonObject query(BranchWitness source) {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 3);
        query.addProperty("kind", "REGION_PATH_FLIP");
        query.addProperty("queryKey", CanonicalJson.sha256("map-query"));
        query.addProperty("regionId", "REGION.map");
        query.addProperty("sourceActivationOccurrenceId",
                "test/node#epoch0/region/REGION.map#1#a1");
        query.add("replayContract",
                BranchReplayContract.atSource(source).toJson());
        JsonObject context = new JsonObject();
        context.addProperty("schemaVersion", SolverPathContext.SCHEMA_VERSION);
        context.addProperty("kind", SolverPathContext.KIND);
        context.addProperty("authority", SolverPathContext.AUTHORITY);
        context.add("constraints", new JsonArray());
        query.add("solverPathContext", context);
        query.add("consumerAnchorCaseDependencies", new JsonArray());
        return query;
    }

    private static JsonObject symbol(String raw) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "J");
        result.addProperty("_exp", raw);
        return result;
    }

    private static JsonObject constant(long value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "J");
        result.addProperty("_exp", "Y_J_" + value);
        return result;
    }

    private static JsonObject nullReference() {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "");
        result.addProperty("_exp", "N");
        return result;
    }

    private static JsonObject binary(JsonObject left, String operator,
                                     JsonObject right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}
