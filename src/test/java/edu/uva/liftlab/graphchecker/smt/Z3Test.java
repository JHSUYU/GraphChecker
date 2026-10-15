package edu.uva.liftlab.graphchecker.smt;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.io.StringWriter;
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
     * A CAP AFTER THE VERDICT ANSWERS ONLY WITH ITS PAYLOAD: a core run
     * whose z3 printed unsat and then stopped at its cap names no core (the
     * core is unknown, not empty), and a model run's z3 that printed sat and
     * then stopped at its cap loses the race to the other engine's model.
     * {what each engine's core or model run prints after its verdict, the
     * core known, x's value}.
     */
    @Test
    public void aCapAfterTheVerdictAnswersOnlyWithItsPayload()
            throws IOException {
        Path script = folder.newFile("z3-cap-after").toPath();
        Files.write(script, Arrays.asList(
                "#!/bin/bash",
                "input=$(cat)",
                "engine=$(printf '%s' \"$input\" | sed -n"
                        + " 's/.*(set-option :smt.arith.solver \\([0-9]*\\)).*/\\1/p'"
                        + " | head -1)",
                "verdict=$(printf '%s' \"$input\" | sed -n"
                        + " 's/.*; verdict \\([a-z]*\\).*/\\1/p' | head -1)",
                "case $input in",
                "  *get-unsat-core*) echo unsat;"
                        + " echo '(error \"out of memory\")' ;;",
                "  *get-value*) echo sat; if [ $engine = 2 ];"
                        + " then echo '(error \"out of memory\")';"
                        + " else echo '((x 6))'; fi ;;",
                "  *) echo $verdict ;;",
                "esac"), StandardCharsets.UTF_8);
        assertTrue(script.toFile().setExecutable(true));
        Z3 solver = new Z3(script, 3000L, 8192);
        Z3.Answer unsat = solver.ask("; verdict unsat\n",
                Collections.<String>emptyList(), true);
        assertTrue(unsat.toString(), unsat.unsat());
        assertTrue("a core cut by the cap is unknown: " + unsat,
                !unsat.coreKnown() && unsat.core().isEmpty());
        Z3.Answer sat = solver.ask("; verdict sat\n",
                Collections.singletonList("x"), false);
        assertEquals("the other engine's model answers: " + sat, "6",
                sat.values().get("x"));
        assertTrue(solver.errors().toString(), solver.errors().isEmpty());
    }

    /**
     * A SHARED SLOT'S CAP ON ITS MODEL OR ITS CORE ASKS THAT RUN AGAIN
     * ALONE: the verdict fits a path ask's 448 MB cap, its model (or core)
     * run does not; that run asked again alone, at the room's lone 1984 MB
     * cap, the ask answers with its model (its core).  {what the fixture
     * caps at 448 MB, the verdict, the model's x or the core}.
     */
    @Test
    public void aSharedSlotsCapOnItsPayloadAsksThatRunAgainAlone()
            throws IOException {
        String[][] rows = {{"get-value", "sat", "6"},
                {"get-unsat-core", "unsat", "[c]"}};
        for (String[] row : rows) {
            Path script = folder.newFile("z3-payload-" + row[0]).toPath();
            Files.write(script, Arrays.asList(
                    "#!/bin/bash",
                    "input=$(cat)",
                    "case \"$input\" in",
                    "  *" + row[0] + "*) case \" $* \" in",
                    "      *' memory_max_size=448 '*) echo " + row[1] + ";"
                            + " echo '(error \"out of memory\")' ;;",
                    "      *) echo " + row[1] + "; echo '((x 6))' | sed"
                            + " 's/((x 6))/" + (row[1].equals("sat")
                            ? "((x 6))" : "(c)") + "/' ;;",
                    "    esac ;;",
                    "  *) echo " + row[1] + " ;;",
                    "esac"), StandardCharsets.UTF_8);
            assertTrue(script.toFile().setExecutable(true));
            Z3.Answer answer = new Z3(script, 3000L, 4096).slotted(512).ask(
                    "(assert true)\n", row[1].equals("sat")
                            ? Collections.singletonList("x")
                            : Collections.<String>emptyList(),
                    row[1].equals("unsat"));
            String what = Arrays.toString(row) + ": " + answer;
            assertEquals(what, row[1], answer.status());
            assertEquals(what, row[2], row[1].equals("sat")
                    ? answer.values().get("x") : answer.core().toString());
        }
    }

    /**
     * A CORE AT ITS CAP LEAVES THE VERDICT UNSAT, ITS CORE UNKNOWN: the
     * verdict is unsat at a path ask's 448 MB cap, its core run is not
     * there nor alone at the room's 1984 MB cap -- where the verdict would
     * not fit either.  The verdict is never asked again for a core: unsat,
     * the core unknown, never undecided for want of one; the runs a
     * check-sat, the core run, the core run alone.
     */
    @Test
    public void aCoreAtItsCapLeavesTheVerdictUnsatItsCoreUnknown()
            throws IOException {
        Path log = folder.newFile("core-cap.log").toPath();
        Path script = folder.newFile("z3-core-cap").toPath();
        Files.write(script, Arrays.asList(
                "#!/bin/bash",
                "input=$(cat)",
                "cap=$(printf '%s' \" $* \" | sed -n"
                        + " 's/.* memory_max_size=\\([0-9]*\\) .*/\\1/p')",
                "case \"$input\" in",
                "  *get-unsat-core*) echo \"core $cap\" >> " + log + ";"
                        + " echo unsat; echo '(error \"out of memory\")' ;;",
                "  *) echo \"verdict $cap\" >> " + log + ";"
                        + " if [ \"$cap\" = 1984 ]; then"
                        + " echo '(error \"out of memory\")'; exit 101;"
                        + " fi; echo unsat ;;",
                "esac"), StandardCharsets.UTF_8);
        assertTrue(script.toFile().setExecutable(true));
        Z3.Answer answer = new Z3(script, 3000L, 4096).slotted(512).ask(
                "(assert true)\n", Collections.<String>emptyList(), true);
        assertTrue(answer.toString(), answer.unsat());
        assertTrue("its core unknown: " + answer, !answer.coreKnown());
        java.util.Set<String> runs = new java.util.TreeSet<String>(
                Files.readAllLines(log));
        assertEquals("the verdict at its slot, the core there and alone",
                new java.util.TreeSet<String>(Arrays.asList("verdict 448",
                        "core 448", "core 1984")), runs);
    }

    /**
     * THE ROOM SERVES RUNS IN THE ORDER THEY ASKED: a lone run waiting for
     * the whole room is not passed by a smaller one that would fit, and a
     * waiter that stops waiting (interrupted) does not hold the ones behind
     * it.
     */
    @Test
    public void theRoomServesRunsInTheOrderTheyAsked() throws Exception {
        Z3.Room room = new Z3.Room(4096);
        assertTrue(room.take(2048));
        java.util.List<String> order = java.util.Collections.synchronizedList(
                new java.util.ArrayList<String>());
        Thread lone = new Thread(() -> {
            if (room.take(4096)) order.add("lone");
        });
        lone.start();
        while (lone.getState() != Thread.State.WAITING) Thread.sleep(5L);
        Thread small = new Thread(() -> {
            if (room.take(1024)) order.add("small");
        });
        small.start();
        while (small.getState() != Thread.State.WAITING) Thread.sleep(5L);
        Thread.sleep(100L);
        assertTrue("the small run passed the lone one: " + order,
                order.isEmpty());
        room.give(2048);
        lone.join(5000L);
        assertEquals("[lone]", order.toString());
        room.give(4096);
        small.join(5000L);
        assertEquals("[lone, small]", order.toString());
        room.give(1024);

        // A waiter interrupted while it waits stalls no one behind it.
        assertTrue(room.take(4096));
        Thread quitter = new Thread(() -> room.take(1024));
        quitter.start();
        while (quitter.getState() != Thread.State.WAITING) Thread.sleep(5L);
        Thread behind = new Thread(() -> {
            if (room.take(1024)) order.add("behind");
        });
        behind.start();
        while (behind.getState() != Thread.State.WAITING) Thread.sleep(5L);
        quitter.interrupt();
        quitter.join(5000L);
        room.give(4096);
        behind.join(5000L);
        assertEquals("[lone, small, behind]", order.toString());
        assertEquals(1024, room.held());
    }

    /**
     * THE RUNS OF A ROOM HOLD NO MORE THAN IT: asks put at once run as many
     * as their slots fit, the rest waiting -- a room of 4096 MB at slots of
     * 1024 runs two asks (four z3s) at a time -- and every slot is given
     * back.
     */
    @Test
    public void theRunsOfARoomHoldNoMoreThanIt() throws Exception {
        Path script = folder.newFile("z3-slow").toPath();
        Files.write(script, Arrays.asList("#!/bin/bash", "cat >/dev/null",
                "sleep 0.4", "echo sat"), StandardCharsets.UTF_8);
        assertTrue(script.toFile().setExecutable(true));
        Z3 solver = new Z3(script, 5000L, 4096).slotted(1024);
        java.util.concurrent.ExecutorService pool =
                java.util.concurrent.Executors.newFixedThreadPool(6);
        java.util.List<java.util.concurrent.Future<Z3.Answer>> asked =
                new java.util.ArrayList<java.util.concurrent.Future<Z3.Answer>>();
        for (int at = 0; at < 6; at++) {
            asked.add(pool.submit(() -> solver.ask("(assert true)\n",
                    Collections.<String>emptyList(), false)));
        }
        int most = 0;
        while (!asked.stream().allMatch(java.util.concurrent.Future::isDone)) {
            most = Math.max(most, solver.roomHeldMb());
            Thread.sleep(5L);
        }
        for (java.util.concurrent.Future<Z3.Answer> each : asked) {
            assertTrue(each.get().sat());
        }
        pool.shutdown();
        assertEquals("two runs of two 1 GB slots at once, never more", 4096,
                most);
        assertEquals("every slot given back", 0, solver.roomHeldMb());
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
        Z3 solver = new Z3(fakeZ3(), 3000L, 8192);
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
     * A VERDICT ALONE IS THE FIRST ENGINE'S THAT DECIDES: asked no model
     * and no core, the preferred engine gets no grace -- the verdict is the
     * same whichever engine gives it -- so engine 6's sat answers at once
     * where engine 2 never answers (within the grace, a second, before).
     */
    @Test
    public void aVerdictAloneIsTheFirstEngineThatDecides() throws IOException {
        Z3 solver = new Z3(fakeZ3(), 3000L, 8192);
        long started = System.nanoTime();
        Z3.Answer answer = solver.ask("; on2 hang\n; on6 sat\n",
                Collections.<String>emptyList(), false);
        long millis = (System.nanoTime() - started) / 1_000_000L;
        assertEquals("sat", answer.status());
        assertTrue("took " + millis + " ms", millis < 800L);
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
