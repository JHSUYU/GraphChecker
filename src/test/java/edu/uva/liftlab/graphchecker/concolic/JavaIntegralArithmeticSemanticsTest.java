package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec.Host;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec.Sort;
import edu.uva.liftlab.graphchecker.concolic.ContainerSmtCodec.Term;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics
        .IntegralWidth;
import org.junit.Assume;
import org.junit.Test;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Java's integral {@code /} and {@code %} against the JVM that defines them.
 *
 * <p>Every case is decided twice: once by running the operator in this JVM,
 * and once by asking z3 what the emitted SMT term denotes.  A lowering that
 * merely "looks right" -- SMT-LIB's {@code div}/{@code mod} are Euclidean
 * where Java truncates toward zero -- fails here on the first negative
 * dividend, which is the whole point: a witness produced by the wrong integer
 * semantics corresponds to no real execution.</p>
 */
public class JavaIntegralArithmeticSemanticsTest {

    /** JLS 15.17.2: the quotient is truncated toward zero. */
    @Test
    public void intDivisionTruncatesTowardZeroLikeThisJvm()
            throws Exception {
        List<String> obligations = new ArrayList<>();
        for (int[] pair : intPairs()) {
            obligations.add(equality(
                    JavaPrimitiveSmtSemantics.integralDivision(
                            literal(pair[0]), literal(pair[1]),
                            IntegralWidth.JAVA_INT),
                    literal(pair[0] / pair[1])));
        }
        assertEveryObligationHolds(obligations);
    }

    /** JLS 15.17.3: the remainder takes the sign of the dividend. */
    @Test
    public void intRemainderTakesTheDividendSignLikeThisJvm()
            throws Exception {
        List<String> obligations = new ArrayList<>();
        for (int[] pair : intPairs()) {
            obligations.add(equality(
                    JavaPrimitiveSmtSemantics.integralRemainder(
                            literal(pair[0]), literal(pair[1]),
                            IntegralWidth.JAVA_INT),
                    literal(pair[0] % pair[1])));
        }
        assertEveryObligationHolds(obligations);
    }

    @Test
    public void longDivisionAndRemainderMatchThisJvm() throws Exception {
        List<String> obligations = new ArrayList<>();
        for (long[] pair : longPairs()) {
            obligations.add(equality(
                    JavaPrimitiveSmtSemantics.integralDivision(
                            literal(pair[0]), literal(pair[1]),
                            IntegralWidth.JAVA_LONG),
                    literal(pair[0] / pair[1])));
            obligations.add(equality(
                    JavaPrimitiveSmtSemantics.integralRemainder(
                            literal(pair[0]), literal(pair[1]),
                            IntegralWidth.JAVA_LONG),
                    literal(pair[0] % pair[1])));
        }
        assertEveryObligationHolds(obligations);
    }

    /**
     * The one integral division that overflows: the width's wrap is what
     * turns the mathematical {@code 2^(n-1)} back into {@code MIN_VALUE},
     * so this case needs no rule of its own -- but it must be pinned.
     */
    @Test
    public void minValueOverMinusOneWrapsBackToMinValue() throws Exception {
        assertEquals(Integer.MIN_VALUE, Integer.MIN_VALUE / -1);
        assertEquals(0, Integer.MIN_VALUE % -1);
        assertEquals(Long.MIN_VALUE, Long.MIN_VALUE / -1L);
        assertEquals(0L, Long.MIN_VALUE % -1L);
        assertEveryObligationHolds(java.util.Arrays.asList(
                equality(JavaPrimitiveSmtSemantics.integralDivision(
                        literal(Integer.MIN_VALUE), "(- 1)",
                        IntegralWidth.JAVA_INT),
                        literal(Integer.MIN_VALUE)),
                equality(JavaPrimitiveSmtSemantics.integralRemainder(
                        literal(Integer.MIN_VALUE), "(- 1)",
                        IntegralWidth.JAVA_INT), "0"),
                equality(JavaPrimitiveSmtSemantics.integralDivision(
                        literal(Long.MIN_VALUE), "(- 1)",
                        IntegralWidth.JAVA_LONG),
                        literal(Long.MIN_VALUE)),
                equality(JavaPrimitiveSmtSemantics.integralRemainder(
                        literal(Long.MIN_VALUE), "(- 1)",
                        IntegralWidth.JAVA_LONG), "0")));
    }

    /**
     * Java throws on a zero divisor where SMT-LIB leaves the result
     * uninterpreted, so the divisor is stated non-zero rather than left as
     * free slack the solver may satisfy the formula with.
     */
    @Test
    public void aZeroDivisorIsStatedRatherThanLeftToTheSolver() {
        assertEquals("false",
                JavaPrimitiveSmtSemantics.integralDivisorDefined("0"));
        assertEquals("false",
                JavaPrimitiveSmtSemantics.integralDivisorDefined("(- 0)"));
        assertEquals("true",
                JavaPrimitiveSmtSemantics.integralDivisorDefined("3"));
        assertEquals("true",
                JavaPrimitiveSmtSemantics.integralDivisorDefined("(- 1)"));
        assertEquals("(not (= divisor 0))",
                JavaPrimitiveSmtSemantics.integralDivisorDefined("divisor"));
        assertEquals("(not (= (java_int_wrap (+ a b)) 0))",
                JavaPrimitiveSmtSemantics.integralDivisorDefined(
                        "(java_int_wrap (+ a b))"));
    }

    /**
     * A container size is a Java {@code int} ({@code array.length},
     * {@code Collection.size()}), which is what lets it be an operand of
     * Java binary numeric promotion at all -- and is never outside that
     * domain, which is what makes the promoted width's wrap meaningful.
     */
    @Test
    public void containerSizeIsAJavaIntPinnedToItsDomain() {
        SizeHost host = new SizeHost();
        Term size = ContainerSmtCodec.term(indexedSize(), host);

        assertTrue("the size lowered", size != null);
        assertEquals(Sort.INT, size.sort);
        assertEquals(IntegralWidth.JAVA_INT, size.integralWidth);
        assertEquals(1, host.requires.size());
        assertEquals("(and (<= 0 (indexed_size base_state))"
                        + " (<= (indexed_size base_state) 2147483647))",
                host.requires.get(0));
    }

    // ------------------------------------------------------------------

    private static int[][] intPairs() {
        List<int[]> pairs = new ArrayList<>();
        int[] interesting = {0, 1, -1, 2, -2, 3, -3, 7, -7, 5, -5, 31,
                Integer.MAX_VALUE, Integer.MIN_VALUE};
        for (int left : interesting) {
            for (int right : interesting) {
                if (right != 0) pairs.add(new int[]{left, right});
            }
        }
        Random random = new Random(20260827L);
        for (int index = 0; index < 200; index++) {
            int right = random.nextInt();
            if (right == 0) right = 1;
            pairs.add(new int[]{random.nextInt(), right});
        }
        return pairs.toArray(new int[0][]);
    }

    private static long[][] longPairs() {
        List<long[]> pairs = new ArrayList<>();
        long[] interesting = {0L, 1L, -1L, 2L, -2L, 3L, -3L, 4L, -4L,
                1787784003829L, -1787784003829L,
                Long.MAX_VALUE, Long.MIN_VALUE};
        for (long left : interesting) {
            for (long right : interesting) {
                if (right != 0L) pairs.add(new long[]{left, right});
            }
        }
        Random random = new Random(915L);
        for (int index = 0; index < 200; index++) {
            long right = random.nextLong();
            if (right == 0L) right = 1L;
            pairs.add(new long[]{random.nextLong(), right});
        }
        return pairs.toArray(new long[0][]);
    }

    private static String literal(long value) {
        // Math.abs(Long.MIN_VALUE) is still negative, and this table is
        // mostly about that value.
        return value < 0
                ? "(- " + java.math.BigInteger.valueOf(value).negate() + ")"
                : String.valueOf(value);
    }

    private static String equality(String term, String expected) {
        return "(= " + term + " " + expected + ")";
    }

    /**
     * Refutes the negation: if any one obligation could fail, z3 says sat and
     * names the case.
     */
    private void assertEveryObligationHolds(List<String> obligations)
            throws Exception {
        Path z3 = z3();
        Assume.assumeTrue("z3 is required", z3 != null);
        StringBuilder smt = new StringBuilder("(set-logic ALL)\n");
        smt.append(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION)
                .append('\n');
        smt.append(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION)
                .append('\n');
        smt.append("(assert (not (and");
        for (String obligation : obligations) {
            smt.append(' ').append(obligation);
        }
        smt.append(")))\n(check-sat)\n");
        assertEquals(obligations.size() + " Java integral obligation(s)"
                        + " must all hold", "unsat", run(z3, smt.toString()));
    }

    private static String run(Path z3, String smt) throws Exception {
        Path file = Files.createTempFile("javaintegral", ".smt2");
        Files.write(file, smt.getBytes(StandardCharsets.UTF_8));
        Process process = new ProcessBuilder(z3.toString(), "-smt2",
                file.toString()).redirectErrorStream(true).start();
        StringBuilder out = new StringBuilder();
        try (BufferedReader reader = new BufferedReader(
                new InputStreamReader(process.getInputStream(),
                        StandardCharsets.UTF_8))) {
            String line;
            while ((line = reader.readLine()) != null) {
                out.append(line).append('\n');
            }
        }
        process.waitFor();
        Files.deleteIfExists(file);
        return out.toString().trim();
    }

    private static Path z3() {
        for (String candidate : new String[]{"/usr/local/bin/z3",
                "/usr/bin/z3"}) {
            Path path = Paths.get(candidate);
            if (Files.isExecutable(path)) return path;
        }
        return null;
    }

    private static JsonObject indexedSize() {
        JsonObject identity = new JsonObject();
        identity.addProperty("_type", "SymbolExpression");
        identity.addProperty("_java_type", "byte[]");
        identity.addProperty("_exp", "AL_1-0");
        JsonObject state = new JsonObject();
        state.addProperty("_type", "ContainerRelation");
        state.addProperty("shape", "INDEXED");
        state.addProperty("operation", "STATE");
        state.addProperty("_java_type", "L");
        state.add("receiver", identity);
        state.add("arguments", new JsonArray());
        JsonObject size = new JsonObject();
        size.addProperty("_type", "ContainerRelation");
        size.addProperty("shape", "INDEXED");
        size.addProperty("operation", "SIZE");
        size.addProperty("_java_type", "I");
        size.add("receiver", state);
        size.add("arguments", new JsonArray());
        return size;
    }

    /** Lowers exactly the one expression {@link #indexedSize()} builds. */
    private static final class SizeHost implements Host {
        private final List<String> requires = new ArrayList<>();

        @Override public Term state(JsonElement identity, Sort shape) {
            return new Term("base_state", Sort.INDEXED);
        }

        @Override public Term operand(JsonElement expression, Sort expected) {
            return ContainerSmtCodec.term(expression.getAsJsonObject(), this);
        }

        @Override public Term box(JsonElement expression) {
            throw new IllegalStateException("no boxing in this fixture");
        }

        @Override public Term unbox(Term value, String javaType) {
            return value;
        }

        @Override public void require(String predicate) {
            requires.add(predicate);
        }

        @Override public Term field(Term owner, String ownerClass,
                                    int fieldOffset, String javaType) {
            throw new IllegalStateException("no field access here");
        }

        @Override public void unsupported(String reason) {
            throw new IllegalStateException("unsupported: " + reason);
        }
    }
}
