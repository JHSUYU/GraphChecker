package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
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

                // ------------------------------------------------------------------

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
