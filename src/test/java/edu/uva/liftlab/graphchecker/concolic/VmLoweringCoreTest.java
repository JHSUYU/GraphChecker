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

    /** Java integral remainder keeps the same definedness it always had. */
    @Test
    public void flipSolverStillModelsIntegralRemainder() throws Exception {
        JsonObject remainder = binary(symbol(INPUT, "J"), "%",
                constant("J", "7"));
        ConcolicConstraintSolver.Result result = lower(
                binary(remainder, ">", constant("J", "0")));

        assertNoRefusal(result);
        assertTrue(result.smtLib, result.smtLib.contains("java_irem_a"));
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

    /** Two unknown String objects are still reference identity, refused. */
    @Test
    public void flipSolverStillRefusesStringIdentityWithoutALiteral()
            throws Exception {
        ConcolicConstraintSolver.Result result = lower(binary(
                symbol(INPUT, "Ljava/lang/String;"), "==",
                symbol(OTHER_INPUT, "Ljava/lang/String;")));

        assertRefused(result, "JAVA_STRING_REFERENCE_IDENTITY");
    }

    /** One expression equals itself whatever it denotes. */
    @Test
    public void identicalOperandsDecideEqualityWithoutTheSolver()
            throws Exception {
        ConcolicConstraintSolver.Result result = lower(binary(
                symbol(INPUT, "J"), "==", symbol(INPUT, "J")));

        assertNoRefusal(result);
        assertFalse(result.smtLib, result.smtLib.contains(
                "(= " + solverSymbol(result) + " "
                        + solverSymbol(result) + ")"));
    }

    /**
     * A recorded int that is neither 0 nor 1 is not a Java boolean.  Both
     * lowerings now refuse it rather than reading it as "true".
     */
    @Test
    public void aMalformedBooleanLiteralIsRefused() throws Exception {
        ConcolicConstraintSolver.Result result = lower(constant("Z", "7"));

        assertRefused(result, "INVALID_JAVA_BOOLEAN_LITERAL");
    }

    /** A well-formed one still folds to the SMT literal. */
    @Test
    public void aBooleanLiteralFolds() throws Exception {
        ConcolicConstraintSolver.Result result = lower(binary(
                constant("Z", "1"), "&&",
                binary(symbol(INPUT, "J"), ">", constant("J", "0"))));

        assertNoRefusal(result);
        assertTrue(result.smtLib, result.smtLib.contains("(and true "));
    }

    // ------------------------------------------------------------------
    // Pure predicates of the shared core.
    // ------------------------------------------------------------------

    /**
     * A split delimiter must be one ordinary literal character.  Only the
     * round trip through Java's decimal int rendering additionally excludes
     * the characters that occur inside that rendering.
     */
    @Test
    public void oneDelimiterRuleServesBothRoundTrips() {
        assertEquals("", VmLoweringCore.delimiterGap(",", false));
        assertEquals("", VmLoweringCore.delimiterGap(",", true));
        assertEquals("REGEX_NOT_SAFE_SINGLE_LITERAL",
                VmLoweringCore.delimiterGap(".", false));
        assertEquals("REGEX_NOT_SAFE_SINGLE_LITERAL",
                VmLoweringCore.delimiterGap("ab", true));
        assertEquals("REGEX_NOT_SAFE_SINGLE_LITERAL",
                VmLoweringCore.delimiterGap(null, true));
        // A digit or a minus sign is an ordinary literal for a String
        // split, and destroys a decimal prefix.
        assertEquals("", VmLoweringCore.delimiterGap("7", false));
        assertEquals("DELIMITER_OCCURS_IN_JAVA_INT_TEXT",
                VmLoweringCore.delimiterGap("7", true));
        assertEquals("DELIMITER_OCCURS_IN_JAVA_INT_TEXT",
                VmLoweringCore.delimiterGap("-", true));
    }

    /** Java binary numeric promotion, over integral operands only. */
    @Test
    public void integralPromotionNeedsTwoKnownIntegralWidths() {
        Term intValue = Term.of("1", Sort.INT, IntegralWidth.JAVA_INT);
        Term longValue = Term.of("2", Sort.INT, IntegralWidth.JAVA_LONG);
        Term unknown = Term.of("3", Sort.INT);
        Term string = Term.of("\"x\"", Sort.STRING);

        assertEquals(IntegralWidth.JAVA_INT,
                VmLoweringCore.promotedIntegralWidth(intValue, intValue));
        assertEquals(IntegralWidth.JAVA_LONG,
                VmLoweringCore.promotedIntegralWidth(intValue, longValue));
        assertEquals(IntegralWidth.NONE,
                VmLoweringCore.promotedIntegralWidth(intValue, unknown));
        assertEquals(IntegralWidth.NONE,
                VmLoweringCore.promotedIntegralWidth(intValue, string));
    }

    /** An unstated String nullness is the solver's fail-closed trigger. */
    @Test
    public void knownNonNullStringsNeedNoGuard() {
        assertEquals("true", VmLoweringCore.stringNonNull(
                Term.nonNullString("\"x\"", "true")));
        assertEquals("(not s_null)", VmLoweringCore.stringNonNull(
                Term.nullableString("s", "s_null", "s")));
        assertEquals("false", VmLoweringCore.stringNonNull(
                Term.of("1", Sort.INT)));
    }

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
