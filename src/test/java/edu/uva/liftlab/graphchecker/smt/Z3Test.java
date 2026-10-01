package edu.uva.liftlab.graphchecker.smt;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
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
}
