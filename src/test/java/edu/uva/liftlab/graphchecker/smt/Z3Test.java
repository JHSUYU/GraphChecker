package edu.uva.liftlab.graphchecker.smt;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class Z3Test {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    /**
     * An unsat answer's core is known only where its own run said unsat: a
     * core run that timed out or answered unknown names no core, which is
     * not the empty one (an UNSAT that may rest on an excluded model would
     * read as resting on none).  {what the core run does, known, core}.
     */
    @Test
    public void aCoreIsKnownOnlyWhereItsRunSaidUnsat() throws IOException {
        Object[][] rows = {
                {"printf 'unsat\\n(refuted_claim__0 valuation__m)\\n'", true,
                        Arrays.asList("refuted_claim__0", "valuation__m")},
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
            Z3.Answer answer = new Z3(script, 1000L, 8192).ask(
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
     * EVERY z3 STARTS UNDER ITS SLOT'S CAP: z3's own memory_max_size, the
     * slot less what z3's accounting misses.  A lone ask's engines take half
     * the room each, a caller of many asks at once a slot of the room shared
     * that many ways, a path ask a slot of its own size, never past half the
     * room nor below the least slot; a room that holds no run is refused.
     * {room, how the solver is held (lone, shared:k, slotted:mb), the cap}.
     */
    @Test
    public void aZ3StartsUnderItsSlotsCap() {
        Object[][] rows = {
                {8192, "lone", 4032},
                {8192, "shared:4", 960},
                {8192, "slotted:1024", 960},
                {1152, "lone", 512},
                {1152, "slotted:1024", 512},
                {4096, "lone", 1984},
                {512, "slotted:16", 64},
                {255, "lone", null},
        };
        for (Object[] row : rows) {
            Integer cap;
            try {
                Z3 solver = new Z3(Paths.get("z3"), 1000L, (Integer) row[0]);
                String[] how = ((String) row[1]).split(":");
                if (how[0].equals("shared")) {
                    solver = solver.shared(Integer.parseInt(how[1]));
                } else if (how[0].equals("slotted")) {
                    solver = solver.slotted(Integer.parseInt(how[1]));
                }
                cap = solver.capMb();
                assertTrue(Arrays.toString(row), Z3.command(Paths.get("z3"),
                        cap + Z3.MISSED_MB, 20_000L).contains(
                        "memory_max_size=" + cap));
            } catch (IllegalArgumentException refused) {
                cap = null;
            }
            assertEquals(Arrays.toString(row), row[2], cap);
        }
    }

    /**
     * A z3 AT ITS CAP IS UNDECIDED BY NAME, as a timeout is: never a verdict,
     * no error of the query (an error voids a composition's claim), its
     * reason the cap it hit; the other engine's verdict still answers.
     * {engine 2, engine 6, status}.
     */
    @Test
    public void aZ3AtItsCapIsUndecidedByName() throws IOException {
        Path script = folder.newFile("z3-memout").toPath();
        Files.write(script, Arrays.asList(
                "#!/bin/bash",
                "input=$(cat)",
                "engine=$(printf '%s' \"$input\" | sed -n"
                        + " 's/.*(set-option :smt.arith.solver \\([0-9]*\\)).*/\\1/p'"
                        + " | head -1)",
                "act=$(printf '%s' \"$input\" | sed -n"
                        + " \"s/.*; on$engine \\([a-z]*\\).*/\\1/p\" | head -1)",
                "case $act in",
                "  oom) echo '(error \"out of memory\")'; exit 101 ;;",
                "  *) echo sat ;;",
                "esac"), StandardCharsets.UTF_8);
        assertTrue(script.toFile().setExecutable(true));
        String[][] rows = {{"oom", "oom", "memout"}, {"oom", "sat", "sat"}};
        for (String[] row : rows) {
            Z3 solver = new Z3(script, 3000L, 1152);
            Z3.Answer answer = solver.ask("; on2 " + row[0] + "\n; on6 "
                    + row[1] + "\n", Collections.<String>emptyList(), true);
            String what = Arrays.toString(row) + ": " + answer;
            assertEquals(what, row[2], answer.status());
            assertEquals(what, row[2].equals("memout"), answer.memOut());
            assertTrue(what, answer.memOut() != answer.decided());
            assertTrue(what + " " + solver.errors(), solver.errors().isEmpty());
            assertTrue(what + " " + answer.reason(), !answer.memOut()
                    || answer.reason().contains("512 MB"));
        }
    }

    /**
     * TWO ENGINES THAT DECIDE ONE RUN DIFFERENTLY ARE AN ERROR, NEVER A
     * VERDICT: engine 6 says unsat at once, engine 2 sat after 0.3 s; the
     * verdict's run takes engine 6's unsat, its core's run, within the
     * preferred engine's grace, has both.  The ask is undecided and the
     * disagreement named among the solver's errors.
     */
    @Test
    public void twoEnginesThatDifferAreAnErrorNeverAVerdict()
            throws IOException {
        Path script = folder.newFile("z3-split").toPath();
        Files.write(script, Arrays.asList("#!/bin/bash",
                "input=$(cat)",
                "case $input in",
                "  *'smt.arith.solver 2)'*) sleep 0.3; echo sat ;;",
                "  *get-unsat-core*) echo unsat; echo '(c)' ;;",
                "  *) echo unsat ;;",
                "esac"), StandardCharsets.UTF_8);
        assertTrue(script.toFile().setExecutable(true));
        Z3 solver = new Z3(script, 3000L, 8192);
        Z3.Answer answer = solver.ask("(assert true)\n",
                Collections.<String>emptyList(), true);
        assertTrue(answer.toString(), !answer.decided()
                && answer.status().startsWith(Z3.DISAGREE));
        assertTrue(solver.errors().toString(),
                solver.errors().toString().contains("engines disagree"));
    }
}
