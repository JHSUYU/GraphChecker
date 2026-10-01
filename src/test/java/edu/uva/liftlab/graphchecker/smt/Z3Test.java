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
