package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.nio.file.Paths;
import java.util.Collections;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Sort;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Term;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/**
 * The composer and the path-flip solver lower one recorded VM expression
 * through one implementation.  These cover the arms where they used to
 * disagree, stated on the solver because that is the side whose refusals
 * the unification removed.
 */
public class VmLoweringCoreTest {

    /** Both lowerings are the shared core, not two copies of it. */
    @Test
    public void bothLowerersAreTheSharedCore() throws Exception {
        assertSame(VmLoweringCore.class, Class.forName(
                "edu.uva.liftlab.graphchecker.concolic"
                        + ".ConcolicSmtComposer$Emitter").getSuperclass());
        assertSame(VmLoweringCore.class, Class.forName(
                "edu.uva.liftlab.graphchecker.concolic"
                        + ".ConcolicConstraintSolver$Encoder")
                .getSuperclass());
    }

    /**
     * Java integral division is exact in SMT (truncating toward zero, then
     * wrapped), so the flip solver models it instead of refusing it.
     */
    @Test
    public void flipSolverModelsIntegralDivision() throws Exception {
        JsonObject quotient = binary(symbol(INPUT, "J"), "/",
                constant("J", "2"));
        ConcolicConstraintSolver.Result result = lower(
                binary(quotient, ">", constant("J", "3")));

        assertNoRefusal(result);
        assertTrue(result.smtLib, result.smtLib.contains("java_idiv_a"));
    }

    /**
     * A zero divisor throws rather than producing a value, so the query
     * states the divisor non-zero instead of leaving it to the solver.
     */
    @Test
    public void flipSolverStatesTheDivisorIsNonZero() throws Exception {
        JsonObject quotient = binary(constant("J", "3"), "/",
                symbol(INPUT, "J"));
        ConcolicConstraintSolver.Result result = lower(
                binary(quotient, ">", constant("J", "0")));

        assertNoRefusal(result);
        assertTrue(result.smtLib, result.smtLib.contains(
                "(assert (not (= " + solverSymbol(result) + " 0)))"));
    }

    /**
     * A String literal is interned, so {@code lit == x} holds exactly when
     * x is that interned object; over a recorded expression that is content
     * equality.  The flip solver now uses the composer's model of it.
     */
    @Test
    public void flipSolverDecidesStringIdentityAgainstALiteral()
            throws Exception {
        ConcolicConstraintSolver.Result result = lower(binary(
                symbol(INPUT, "Ljava/lang/String;"), "==",
                stringLiteral("supergroup")));

        assertNoRefusal(result);
        assertTrue(result.smtLib, result.smtLib.contains("\"supergroup\""));
    }

    // ------------------------------------------------------------------
    // Pure predicates of the shared core.
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------

    private static final String INPUT =
            "M_J_field_REGION.lowering.in.value.occ.deadbeef_java/lang/Long";
    private static final String OTHER_INPUT =
            "M_J_field_REGION.lowering.in.other.occ.deadbeef_java/lang/Long";

    /** Lowers one predicate through the flip solver's encoder. */
    private static ConcolicConstraintSolver.Result lower(JsonObject predicate)
            throws Exception {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", 1L);
        event.addProperty("contextId", 1L);
        BranchWitness source = BranchWitness.vmPcImmutable("TEST#u1",
                "<test.Lowering: void run()>", 1, 1, false,
                BranchPredicateAlgebra.complement(predicate), 0, event);

        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 3);
        query.addProperty("kind", "REGION_PATH_FLIP");
        query.addProperty("queryKey", CanonicalJson.sha256("lowering-query"));
        query.addProperty("regionId", "REGION.lowering");
        query.addProperty("sourceActivationOccurrenceId",
                "test/node#epoch0/region/REGION.lowering#1#a1");
        query.add("replayContract",
                BranchReplayContract.atSource(source).toJson());
        JsonObject context = new JsonObject();
        context.addProperty("schemaVersion", SolverPathContext.SCHEMA_VERSION);
        context.addProperty("kind", SolverPathContext.KIND);
        context.addProperty("authority", SolverPathContext.AUTHORITY);
        context.add("constraints", new JsonArray());
        query.add("solverPathContext", context);
        query.add("consumerAnchorCaseDependencies", new JsonArray());

        JsonObject activation = new JsonObject();
        activation.add("inputActions", new JsonArray());
        return ConcolicConstraintSolver.solve(query,
                Collections.singletonList(activation), activation,
                Paths.get("z3"), 10_000L);
    }

    /** The SMT name the one declared input symbol was given. */
    private static String solverSymbol(
            ConcolicConstraintSolver.Result result) {
        for (String line : result.smtLib.split("\\R")) {
            if (line.startsWith("(declare-const sym__")) {
                return line.substring("(declare-const ".length(),
                        line.indexOf(' ', "(declare-const ".length()));
            }
        }
        throw new AssertionError("no input symbol declared:\n"
                + result.smtLib);
    }

    private static void assertNoRefusal(
            ConcolicConstraintSolver.Result result) {
        assertEquals(result.record.toString(), 0,
                result.record.getAsJsonArray("unsupported").size());
    }

    private static void assertRefused(ConcolicConstraintSolver.Result result,
                                      String reason) {
        String recorded = result.record.getAsJsonArray("unsupported")
                .toString();
        assertTrue(recorded, recorded.contains(reason));
    }

    private static JsonObject symbol(String raw, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", raw);
        return result;
    }

    private static JsonObject constant(String javaType, String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", "Y_" + javaType + "_" + value);
        return result;
    }

    private static JsonObject stringLiteral(String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConStringSymbolExp");
        result.addProperty("_java_type", "Ljava/lang/String;");
        result.addProperty("_exp", "Y_S_" + value);
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
}
