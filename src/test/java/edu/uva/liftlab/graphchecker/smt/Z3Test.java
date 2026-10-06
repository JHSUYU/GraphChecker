package edu.uva.liftlab.graphchecker.smt;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class Z3Test {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    /** A z3 carries its own hard timeout, whole seconds ten past its budget. */
    @Test
    public void aZ3StopsItselfTenSecondsPastItsBudget() {
        long[][] table = {
                // budget ms, -T seconds
                {1L, 11L},
                {1_000L, 11L},
                {1_500L, 12L},
                {20_000L, 30L},
                {1_800_000L, 1_810L},
        };
        for (long[] row : table) {
            assertEquals("budget " + row[0] + " ms", "-T:" + row[1],
                    Z3.hardTimeout(row[0]));
        }
    }

    /**
     * An unsat answer's core is known only where its own run said unsat: a
     * core run that timed out or answered unknown names no core, which is
     * not the empty one (an UNSAT that may rest on an excluded model would
     * read as resting on none).  {what the core run does, known, core}.
     */
    @Test
    public void aCoreIsKnownOnlyWhereItsRunSaidUnsat() throws IOException {
        Object[][] rows = {
                {"printf 'unsat\\n(refused_claim__0 valuation__m)\\n'", true,
                        Arrays.asList("refused_claim__0", "valuation__m")},
                {"exec sleep 60", false, Collections.<String>emptyList()},
                {"echo unknown", false, Collections.<String>emptyList()},
        };
        for (Object[] row : rows) {
            Path script = folder.newFile("z3-core-" + row[1] + "-"
                    + Math.abs(row[0].hashCode())).toPath();
            Files.write(script, Arrays.asList("#!/bin/bash",
                    "input=$(cat)",
                    "case \"$input\" in",
                    "  *get-unsat-core*) " + row[0] + " ;;",
                    "  *) echo unsat ;;",
                    "esac"), StandardCharsets.UTF_8);
            assertTrue(script.toFile().setExecutable(true));
            Z3.Answer answer = new Z3(script, 1000L).ask(
                    "(declare-const m Bool)\n(assert m)\n",
                    Collections.<String>emptyList(), true);
            assertTrue(row[0] + ": " + answer, answer.unsat());
            assertEquals(row[0] + ": " + answer, row[1], answer.coreKnown());
            assertEquals(row[0] + ": " + answer, row[2], answer.core());
            assertEquals("a disjunction of it knows its core as it does",
                    row[1], Z3.Answer.unsatOfAll(Arrays.asList(answer,
                            answer)).coreKnown());
        }
    }

    /**
     * A z3 whose every run reads the arithmetic engine its query states and
     * acts as the query's {@code ; on<engine> <act>} comment says: answer
     * {@code sat} (its model naming the engine), {@code unknown}, answer
     * {@code sat} only after half a second ({@code late}), or never
     * ({@code hang}).
     */
    private Path fakeZ3() throws IOException {
        Path script = folder.newFile("z3").toPath();
        Files.write(script, Arrays.asList(
                "#!/bin/bash",
                "input=$(cat)",
                "engine=$(printf '%s' \"$input\" | sed -n"
                        + " 's/.*(set-option :smt.arith.solver \\([0-9]*\\)).*/\\1/p'"
                        + " | head -1)",
                "act=$(printf '%s' \"$input\" | sed -n"
                        + " \"s/.*; on$engine \\([a-z]*\\).*/\\1/p\" | head -1)",
                "case $act in",
                "  hang) exec sleep 60 ;;",
                "  late) sleep 0.5; printf 'sat\\n((x %s))\\n' \"$engine\" ;;",
                "  sat) printf 'sat\\n((x %s))\\n' \"$engine\" ;;",
                "  *) echo unknown ;;",
                "esac"), StandardCharsets.UTF_8);
        assertTrue(script.toFile().setExecutable(true));
        return script;
    }

    /**
     * A z3 starts only under the host's memory ceiling, the percentage the
     * campaign states (the owner's 70 when none is); one that is no
     * percentage is refused, never read as the default.  {stated, ceiling or
     * null for refused}.
     */
    @Test
    public void theMemoryCeilingIsAPercentageOrRefused() {
        Object[][] rows = {{null, 70}, {"70", 70}, {" 100 ", 100}, {"1", 1},
                {"0", null}, {"101", null}, {"seventy", null}, {"", null}};
        for (Object[] row : rows) {
            Integer ceiling;
            try {
                ceiling = Z3.ceilingPercent((String) row[0]);
            } catch (IllegalStateException refused) {
                ceiling = null;
            }
            assertEquals(Arrays.toString(row), row[1], ceiling);
        }
    }

    /**
     * EVERY RUN RACES THE TWO ARITHMETIC ENGINES and answers with the first
     * that decides, the preferred one (2) whenever it decides within its
     * grace of the other: an undecided pair stays undecided, and a pair that
     * never answers times out at the budget.  {engine 2, engine 6, status,
     * the engine whose model answered}.
     */
    @Test
    public void aRunIsTheFirstEngineThatDecides() throws IOException {
        Z3 solver = new Z3(fakeZ3(), 3000L);
        String[][] rows = {
                {"sat", "sat", "sat", "2"},
                {"late", "sat", "sat", "2"},
                {"hang", "sat", "sat", "6"},
                {"unknown", "sat", "sat", "6"},
                {"sat", "hang", "sat", "2"},
                {"unknown", "unknown", "unknown", null},
                {"hang", "hang", "timeout", null}};
        for (String[] row : rows) {
            long started = System.nanoTime();
            Z3.Answer answer = solver.ask("; on2 " + row[0] + "\n; on6 "
                    + row[1] + "\n", Collections.singletonList("x"), false);
            long seconds = (System.nanoTime() - started) / 1_000_000_000L;
            String what = Arrays.toString(row) + ": " + answer;
            assertEquals(what, row[2], answer.status());
            assertEquals(what, row[3], answer.values().get("x"));
            assertTrue(what + " took " + seconds + " s", seconds < 10L);
        }
    }

    /**
     * A QUERY'S OWN ARITHMETIC OPTION IS REPLACED AS IT STREAMS to an
     * engine, however the writes split it; text that only resembles one
     * passes unchanged.  {query, what engine 6 reads}.
     */
    @Test
    public void anEngineReadsItsOwnOptionWhereverTheQueryStatesOne()
            throws IOException {
        String[][] rows = {
                {"(set-option :smt.arith.solver 2)\n(assert x)",
                        "(set-option :smt.arith.solver 6)\n(assert x)"},
                {"((set-option :smt.arith.solver 12)(",
                        "((set-option :smt.arith.solver 6)("},
                {"(set-option :smt.arith.solver )", "(set-option :smt.arith.solver )"},
                {"(set-option :smt.arith.solver 2x)", "(set-option :smt.arith.solver 2x)"},
                {"(set-option :smt.arith.random_seed 2)",
                        "(set-option :smt.arith.random_seed 2)"},
                {"(set-option :smt.arith.solver 2", "(set-option :smt.arith.solver 2"}};
        for (String[] row : rows) {
            for (int chunk : new int[] {1, 7, row[0].length()}) {
                StringWriter read = new StringWriter();
                try (Z3.EngineWriter engine = new Z3.EngineWriter(read, 6)) {
                    for (int at = 0; at < row[0].length(); at += chunk) {
                        engine.write(row[0].substring(at,
                                Math.min(row[0].length(), at + chunk)));
                    }
                }
                assertEquals(row[0] + " in " + chunk + "s", row[1],
                        read.toString());
            }
        }
    }
}
