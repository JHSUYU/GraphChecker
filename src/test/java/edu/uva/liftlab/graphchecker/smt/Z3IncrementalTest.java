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
import java.util.List;
import java.util.TreeSet;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class Z3IncrementalTest {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    private static final String SHARED = "(declare-const x Int)\n"
            + "(declare-const y Int)\n"
            + "(assert (! (>= x 0) :named shared_nonneg))\n";

    /**
     * A SCOPE ANSWERS AS ITS QUESTION ASKED ALONE, and leaves nothing to the
     * next: asked in order of one set of scoped z3s, each question's
     * verdict, model and core are those of the shared part and its scope
     * asked of a z3 of its own -- an assertion, a name or a declaration of
     * one scope is gone in the next, so a symbol two scopes declare with
     * two sorts is two symbols.  {scope, the symbols asked, core wanted,
     * status, values, core}.
     */
    @Test
    public void aScopeAnswersAsItsQuestionAskedAlone() throws IOException {
        Object[][] rows = {
                {"(assert (= x 1))", "x", false, "sat", "{x=1}", null},
                {"(assert (= x 2))\n(assert (= y (+ x 1)))", "x y", false,
                        "sat", "{x=2, y=3}", null},
                {"(assert (! (= x 7) :named seven))", "", true, "sat", "{}",
                        null},
                {"(assert (! (< x 0) :named negative))", "", true, "unsat",
                        "{}", "[negative, shared_nonneg]"},
                {"(assert (! (= y 2) :named two))\n"
                        + "(assert (! (= y 5) :named five))", "", true,
                        "unsat", "{}", "[five, two]"},
                {"(declare-const t Int)\n(assert (= t (+ x 3)))\n"
                        + "(assert (= x 0))", "t", false, "sat", "{t=3}",
                        null},
                {"(declare-const t Bool)\n(assert t)", "t", false, "sat",
                        "{t=true}", null},
        };
        Z3 solver = new Z3(z3(), 30000L, 4096);
        // In a room of its own: one-shot asks in the scopes' room would
        // take it from them between questions, their z3s started afresh.
        Z3 one = new Z3(z3(), 30000L, 4096);
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write(SHARED), 1)) {
            for (Object[] row : rows) {
                String scope = (String) row[0];
                List<String> symbols = ((String) row[1]).isEmpty()
                        ? Collections.<String>emptyList()
                        : Arrays.asList(((String) row[1]).split(" "));
                boolean core = (Boolean) row[2];
                Z3.Answer scoped = scopes.ask(output -> output.write(scope),
                        symbols, core, 0L);
                Z3.Answer alone = one.ask(SHARED + scope + "\n", symbols,
                        core);
                String what = Arrays.toString(row) + ": " + scoped;
                assertEquals(what, row[3], scoped.status());
                assertEquals(what, alone.status(), scoped.status());
                assertEquals(what, row[4], scoped.values().toString());
                assertEquals(what, alone.values(), scoped.values());
                if (row[5] != null) {
                    assertTrue(what, scoped.coreKnown());
                    assertEquals(what, row[5],
                            new TreeSet<String>(scoped.core()).toString());
                    assertEquals(what, new TreeSet<String>(alone.core()),
                            new TreeSet<String>(scoped.core()));
                }
            }
        }
        assertTrue(solver.errors().toString(), solver.errors().isEmpty());
    }

    /**
     * A z3 THAT ENDS MID-QUESTION ANSWERS IT NOTHING, and the questions
     * after it are asked of a fresh one: the fixture z3 runs out of memory
     * where a scope says so -- on its check, its model or its core -- as
     * both engines do.  A memout is undecided, a sat whose model was cut
     * too; an unsat whose core was cut stands, its core unknown.  A z3
     * that ran out of memory after answering others asks the question
     * again of a fresh one, once ({@code agedoom}: only a z3 that answered
     * before runs out).
     * {scope, symbols, core wanted, status, values, core known}.
     */
    @Test
    public void aZ3ThatEndsMidQuestionAnswersItNothing() throws IOException {
        Object[][] rows = {
                {"; unsat", "", false, "unsat", "{}", false},
                {"; agedoom", "", false, "unsat", "{}", false},
                {"; oom", "", false, "memout", "{}", false},
                {"; sat", "x", false, "sat", "{x=1}", false},
                {"; sat ; modelcut", "x", false, "memout", "{}", false},
                {"; unsat ; corecut", "", true, "unsat", "{}", false},
                {"; unsat", "", true, "unsat", "{}", true},
                {"; sat", "", false, "sat", "{}", false},
        };
        Z3 solver = new Z3(fake(), 3000L, 4096);
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"), 1)) {
            for (Object[] row : rows) {
                String scope = (String) row[0];
                List<String> symbols = ((String) row[1]).isEmpty()
                        ? Collections.<String>emptyList()
                        : Collections.singletonList((String) row[1]);
                Z3.Answer answer = scopes.ask(output -> output.write(
                        scope + "\n"), symbols, (Boolean) row[2], 0L);
                String what = Arrays.toString(row) + ": " + answer;
                assertEquals(what, row[3], answer.status());
                assertEquals(what, row[4], answer.values().toString());
                assertEquals(what, row[5], answer.coreKnown());
            }
        }
        assertTrue(solver.errors().toString(), solver.errors().isEmpty());
    }

    /**
     * THE CHECK AN ENGINE LOST IS CANCELLED, ITS z3 KEPT: engine 2 refutes
     * the slow scope in a second, engine 6 would search it for a minute and
     * is sent SIGINT, answers {@code unknown} and reads on; the next
     * question, which engine 6 alone decides, it decides at once, in its
     * first z3.  A verdict asked alone -- no model, no core -- is the first
     * engine's that decides, the preferred one given no grace: engine 6's
     * sat at once, engine 2's check of a minute cancelled, its z3 kept.
     */
    @Test
    public void theCheckAnEngineLostIsCancelledItsZ3Kept() throws IOException {
        Path log = folder.newFile("starts.log").toPath();
        Z3 solver = new Z3(fake(log), 30000L, 4096);
        long started = System.nanoTime();
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"), 1)) {
            assertEquals("unsat", scopes.ask(output -> output.write(
                    "; slow\n"), null, false, 0L).status());
            assertEquals("sat", scopes.ask(output -> output.write(
                    "; only6\n"), null, false, 0L).status());
            long asked = System.nanoTime();
            assertEquals("sat", scopes.ask(output -> output.write(
                    "; late2\n"), null, false, 0L).status());
            long millis = (System.nanoTime() - asked) / 1_000_000L;
            assertTrue("a verdict alone took " + millis + " ms",
                    millis < 800L);
            assertEquals("sat", scopes.ask(output -> output.write(
                    "; sat\n"), null, false, 0L).status());
        }
        long seconds = (System.nanoTime() - started) / 1_000_000_000L;
        assertTrue("took " + seconds + " s", seconds < 10L);
        assertEquals("one z3 per engine, never started again",
                Arrays.asList("start", "start"), Files.readAllLines(log));
    }

    /**
     * A SIGNAL THAT LANDS LATE IS NO ANSWER: engine 2 refutes a scope in
     * half a second, engine 6, deaf to the SIGINT that cancels its check,
     * answers after 1.5 s, and the signal lands later -- on its next check,
     * unknown and "canceled", or between checks, ending it as z3 ends.
     * Either next question is asked once more, and engine 6, which alone
     * decides it, does; it is started again only where the signal ended
     * it.
     */
    @Test
    public void aSignalThatLandsLateIsNoAnswer() throws IOException {
        Path log = folder.newFile("stray.log").toPath();
        Z3 solver = new Z3(fake(log), 30000L, 4096);
        String[][] rows = {{"; deaf", "unsat"}, {"; only6", "sat"},
                {"; deafdie", "unsat"}, {"; only6", "sat"}};
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"), 1)) {
            for (String[] row : rows) {
                assertEquals(Arrays.toString(row), row[1], scopes.ask(
                        output -> output.write(row[0] + "\n"), null, false,
                        0L).status());
            }
        }
        assertEquals("two z3s, engine 6's started again once",
                3, Files.readAllLines(log).size());
        assertTrue(solver.errors().toString(), solver.errors().isEmpty());
    }

    /**
     * TWO DECIDED ANSWERS THAT DIFFER ARE AN ERROR, NEVER A VERDICT: engine
     * 6 says unsat at once and engine 2, within its grace, sat with its
     * model.  The question is undecided and named among the solver's
     * errors, which refuse a claim over it by name.
     */
    @Test
    public void twoAnswersThatDifferAreAnErrorNeverAVerdict()
            throws IOException {
        Z3 solver = new Z3(fake(), 30000L, 4096);
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"), 1)) {
            Z3.Answer engines = scopes.ask(output -> output.write(
                    "; split\n"), Collections.singletonList("x"), false, 0L);
            assertTrue(engines.toString(), !engines.decided()
                    && engines.status().startsWith(Z3.DISAGREE));
        }
        assertEquals(solver.errors().toString(), 1, solver.errors().size());
    }

    /**
     * A SHARED PART THAT TAKES LONG TO READ IS NO QUESTION'S SILENCE: the
     * fixture reads it in 12 s, past a 1 s question's budget and margin
     * counted from the question's send; counted from the read's end, the
     * question is answered, its z3 never ended.
     */
    @Test
    public void aSharedPartThatTakesLongToReadIsNoSilence()
            throws IOException {
        Path log = folder.newFile("slowread.log").toPath();
        Z3 solver = new Z3(fake(log), 30000L, 4096);
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n; slowread\n"), 1)) {
            assertEquals("sat", scopes.ask(output -> output.write(
                    "; sat\n"), null, false, 1000L).status());
        }
        assertEquals("one z3 per engine", 2, Files.readAllLines(log).size());
    }

    /**
     * THE PLAIN PAIRS ARE AS MANY AS THE ROOMS HOLD: on each other host one
     * a 2048 MB, placed first, then here as many as the room holds beside
     * the tracking one, at 1024 MB a z3 -- at most as many in all as its
     * asker puts questions at once -- a room here that holds no two pairs
     * running one.  {room here, rooms on other hosts, questions at once,
     * the pairs each room holds}.  Three of them ask three questions of a
     * second each at once.
     */
    @Test
    public void thePlainPairsAreAsManyAsTheRoomsHold() throws IOException {
        Object[][] rows = {{2048, "", 8, "1 here"}, {3072, "", 8, "1 here"},
                {4096, "", 8, "1 here"}, {6144, "", 8, "2 here"},
                {8192, "", 3, "3 here"}, {18432, "", 8, "8 here"},
                {30000, "", 8, "8 here"},
                {16384, "a=8192 b=4096", 64, "4 on a, 2 on b, 7 here"},
                {16384, "a=8192 b=4096", 5, "4 on a, 1 on b"},
                {2048, "a=3072 b=1024", 64, "1 on a, 1 here"}};
        for (Object[] row : rows) {
            List<Z3.Room> hosts = new java.util.ArrayList<Z3.Room>();
            for (String room : ((String) row[1]).isEmpty() ? new String[0]
                    : ((String) row[1]).split(" ")) {
                String[] parts = room.split("=");
                hosts.add(new Z3.Room(parts[0], Integer.parseInt(parts[1]),
                        Z3.ssh(parts[0])));
            }
            Z3 solver = new Z3(z3(), 3000L, (Integer) row[0], hosts,
                    folder.getRoot().toPath());
            try (Z3Incremental scopes = new Z3Incremental(solver,
                    output -> output.write(""), (Integer) row[2])) {
                List<Z3.Room> placed = Z3Incremental.placed(solver,
                        (Integer) row[2]);
                assertEquals(Arrays.toString(row), row[3],
                        Z3Incremental.where(placed));
                assertEquals(Arrays.toString(row), placed.size(),
                        scopes.plainPairs());
            }
        }
        Path log = folder.newFile("pairs.log").toPath();
        Z3 solver = new Z3(fake(log), 30000L, 8192);
        java.util.concurrent.ExecutorService askers =
                java.util.concurrent.Executors.newFixedThreadPool(3);
        long started = System.nanoTime();
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"), 3)) {
            List<java.util.concurrent.Future<Z3.Answer>> asked =
                    new java.util.ArrayList<java.util.concurrent.Future<
                            Z3.Answer>>();
            for (int at = 0; at < 3; at++) {
                asked.add(askers.submit(() -> scopes.ask(output ->
                        output.write("; nap\n"), null, false, 0L)));
            }
            for (java.util.concurrent.Future<Z3.Answer> each : asked) {
                assertEquals("unsat", each.get().status());
            }
        } catch (InterruptedException | java.util.concurrent
                .ExecutionException failed) {
            throw new AssertionError(failed);
        } finally {
            askers.shutdownNow();
        }
        long seconds = (System.nanoTime() - started) / 1_000_000_000L;
        assertTrue("three naps took " + seconds + " s", seconds < 3L);
        assertEquals("three pairs, two z3s each", 6,
                Files.readAllLines(log).size());
    }

    /**
     * A QUESTION THAT WANTS A CORE IS ASKED WHOLE, TRACKING: its verdict,
     * model and core of one check of the tracking pair, no plain pair asked
     * first -- the room never moves between them for it.
     */
    @Test
    public void aQuestionThatWantsACoreIsAskedWholeTracking()
            throws IOException {
        Path log = folder.newFile("whole.log").toPath();
        Z3 solver = new Z3(fake(log), 30000L, 4096);
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"), 1)) {
            Z3.Answer unsat = scopes.ask(output -> output.write("; unsat\n"),
                    null, true, 0L);
            assertTrue(unsat.toString(), unsat.unsat() && unsat.coreKnown()
                    && unsat.core().equals(Collections.singletonList("c")));
            Z3.Answer sat = scopes.ask(output -> output.write("; sat\n"),
                    Collections.singletonList("x"), true, 0L);
            assertEquals("sat {x=1}", sat.status() + " " + sat.values());
        }
        List<String> checks = Files.readAllLines(
                log.resolveSibling(log.getFileName() + ".checks"));
        assertTrue(checks.toString(), !checks.isEmpty()
                && !checks.contains("plain"));
    }

    /**
     * A PAIR ON ANOTHER HOST ASKS AS ONE HERE, over ssh (a stand-in that
     * runs the command here): its z3s read their head and the shared part
     * from the file written for them, so each knows its engine; the check
     * engine 6 lost is cancelled by a SIGINT sent to the pid its shell
     * printed, its z3 kept, and the next question, which engine 6 alone
     * decides, it decides at once.  Closed, its z3s are gone and so are
     * their files.  A host that refuses ssh ({@code gone}) asks no more,
     * and what its pair took the pair on the other host answers.
     */
    @Test
    public void aPairOnAnotherHostAsksAsOneHere() throws Exception {
        Path log = folder.newFile("remote.log").toPath();
        Path visible = folder.newFolder("visible").toPath();
        Path ssh = ScopedFixture.ssh(folder.getRoot().toPath());
        Path fake = fake(log);
        Z3 solver = new Z3(fake, 30000L, 4096, Arrays.asList(
                new Z3.Room("far", 2048, Arrays.asList(ssh.toString(),
                        "far"))), visible);
        long started = System.nanoTime();
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"), 1)) {
            assertEquals("1 on far", Z3Incremental.where(
                    Z3Incremental.placed(solver, 1)));
            assertEquals("unsat", scopes.ask(output -> output.write(
                    "; slow\n"), null, false, 0L).status());
            assertEquals("sat", scopes.ask(output -> output.write(
                    "; only6\n"), null, false, 0L).status());
            assertEquals("sat {x=1}", scopes.ask(output -> output.write(
                    "; sat\n"), Collections.singletonList("x"), false, 0L)
                    .toString());
            assertEquals(2, visible.toFile().list().length);
        }
        long seconds = (System.nanoTime() - started) / 1_000_000_000L;
        assertTrue("took " + seconds + " s", seconds < 10L);
        assertEquals("one z3 per engine, never started again",
                Arrays.asList("start", "start"), Files.readAllLines(log));
        assertEquals(0, visible.toFile().list().length);
        for (String pid : Files.readAllLines(log.resolveSibling(
                log.getFileName() + ".pids"))) {
            // Killed, it may wait a moment to be reaped.
            long until = System.nanoTime() + 3_000_000_000L;
            while (Files.exists(Paths.get("/proc", pid))
                    && System.nanoTime() - until < 0L) {
                Thread.sleep(50L);
            }
            assertTrue("z3 " + pid + " outlived its close",
                    !Files.exists(Paths.get("/proc", pid)));
        }

        Z3 halfGone = new Z3(fake, 30000L, 2048, Arrays.asList(
                new Z3.Room("gone", 2048, Arrays.asList(ssh.toString(),
                        "gone")),
                new Z3.Room("far", 2048, Arrays.asList(ssh.toString(),
                        "far"))), visible);
        java.util.concurrent.ExecutorService askers =
                java.util.concurrent.Executors.newFixedThreadPool(4);
        try (Z3Incremental scopes = new Z3Incremental(halfGone,
                output -> output.write("(declare-const x Int)\n"), 2)) {
            List<java.util.concurrent.Future<Z3.Answer>> asked =
                    new java.util.ArrayList<java.util.concurrent.Future<
                            Z3.Answer>>();
            for (int at = 0; at < 4; at++) {
                asked.add(askers.submit(() -> scopes.ask(output ->
                        output.write("; sat\n"), null, false, 0L)));
            }
            for (java.util.concurrent.Future<Z3.Answer> each : asked) {
                assertEquals("sat", each.get().status());
            }
        } finally {
            askers.shutdownNow();
        }
    }

    /**
     * A HOST WHOSE sshd REFUSES THE FIRST CONNECTIONS (MaxStartups under a
     * burst: SGF8-adhoc-39, 15 of 102 pairs) is asked again: a z3 that
     * ended before its shell printed its pid is started again, at most
     * {@link Z3Incremental#SSH_ATTEMPTS} times, and its pair answers.
     */
    @Test
    public void aHostThatRefusesItsFirstConnectionsIsAskedAgain()
            throws Exception {
        Path visible = folder.newFolder("busy-visible").toPath();
        Path ssh = ScopedFixture.ssh(folder.newFolder("busy").toPath());
        Z3 solver = new Z3(fake(), 30000L, 2048, Arrays.asList(
                new Z3.Room("busy", 2048, Arrays.asList(ssh.toString(),
                        "busy"))), visible);
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"), 1)) {
            assertEquals("sat", scopes.ask(output -> output.write(
                    "; sat\n"), null, false, 0L).status());
        }
        assertTrue(Integer.parseInt(Files.readAllLines(
                ssh.resolveSibling("ssh.busy")).get(0).trim()) > 2);
    }

    private Path fake() throws IOException {
        return fake(folder.newFile("unused.log").toPath());
    }

    /**
     * A z3 answering scopes as their {@code ; <word>} comments say, and a
     * SIGINT as z3 4.14.1 does: inside a check it ends the check, unknown,
     * "interrupted from keyboard"; anywhere else it ends z3.  It searches
     * running, as z3 does, so a SIGINT is sent to it there.  A shared
     * part saying {@code slowread} takes 12 s to read.  {@code oom} runs out of
     * memory on the check, {@code agedoom} on a z3 that answered a check
     * before, {@code modelcut} on its model, {@code corecut} on its core;
     * {@code slow} searches a minute under engine 6 unless cancelled, a
     * second under engine 2, then unsat; {@code late2} searches a minute
     * under engine 2 unless cancelled, under engine 6 0.3 s, then sat;
     * {@code only6} is sat under engine 6, unknown under 2; {@code deaf}
     * and {@code deafdie} search 1.5 s under engine 6 deaf to SIGINT, then
     * unsat (0.5 s under 2), and the signal lands later: on the next check,
     * cancelling it, or (deafdie) on the next scope, ending z3;
     * {@code split} is unsat under 6 at once, sat under 2 after 0.2 s;
     * {@code nap} unsat after a second; else {@code sat} ({@code ((x 1))})
     * or unsat (core {@code (c)}), engine 6 searching 0.3 s first.  Each
     * start logged, and each check, tracking or plain, beside it
     * ({@code .checks}), and its pid ({@code .pids}).
     */
    private Path fake(Path log) throws IOException {
        Path script = folder.newFile("z3-scoped.py").toPath();
        Files.write(script, Arrays.asList("#!/usr/bin/env python3",
                "import os, signal, sys, time",
                "class Cancelled(Exception): pass",
                "solving = False; deaf = None; stray = None",
                "def cancel(signum, frame):",
                "    global stray",
                "    if deaf: stray = deaf; return",
                "    if solving: raise Cancelled()",
                "    os._exit(1)",
                "signal.signal(signal.SIGINT, cancel)",
                "with open('" + log + "', 'a') as starts: starts.write("
                        + "'start\\n')",
                "with open('" + log + ".pids', 'a') as pids: pids.write("
                        + "str(os.getpid()) + '\\n')",
                "engine = '2'; tracking = False; answered = 0",
                "text = ''; scope = ''; verdict = ''; reason = ''",
                "def say(line):",
                "    sys.stdout.write(line + '\\n'); sys.stdout.flush()",
                "def oom():",
                "    say('(error \"out of memory\")'); sys.exit(101)",
                "def busy(seconds):",
                "    end = time.time() + seconds",
                "    while time.time() < end: pass",
                "def search(seconds):",
                "    global solving, reason",
                "    solving = True",
                "    try:",
                "        busy(seconds); return True",
                "    except Cancelled:",
                "        reason = 'interrupted from keyboard'; return False",
                "    finally: solving = False",
                "while True:",
                "    line = sys.stdin.readline()",
                "    if not line: break",
                "    said = line.strip()",
                "    if said.startswith('(set-option :smt.arith.solver '):",
                "        engine = said.split(' ')[-1].rstrip(')')",
                "    if said == '(set-option :produce-unsat-cores true)':",
                "        tracking = True",
                "    if said == '(push 1)':",
                "        scope = ''",
                "        if stray == 'die': os._exit(1)",
                "    if not said.startswith('(echo \"'):",
                "        text += line; scope += line; continue",
                "    if '(check-sat)' in text:",
                "        reason = 'incomplete'",
                "        if '; oom' in scope: oom()",
                "        if '; agedoom' in scope and answered > 0: oom()",
                "        answered += 1",
                "        with open('" + log + ".checks', 'a') as checks:",
                "            checks.write(('tracking' if tracking else 'plain')"
                        + " + '\\n')",
                "        if stray == 'cancel':",
                "            stray = None; verdict = 'unknown'",
                "            reason = 'interrupted from keyboard'",
                "        elif ('; slow' in scope and engine == '6')"
                        + " or ('; late2' in scope and engine == '2'):",
                "            verdict = 'sat' if search(60) else 'unknown'",
                "        elif '; deaf' in scope and engine == '6':",
                "            deaf = 'die' if '; deafdie' in scope else 'cancel'",
                "            busy(1.5); deaf = None; verdict = 'unsat'",
                "        elif '; deaf' in scope:",
                "            time.sleep(0.5); verdict = 'unsat'",
                "        elif '; slow' in scope:",
                "            time.sleep(1); verdict = 'unsat'",
                "        elif '; late2' in scope:",
                "            verdict = 'sat' if search(0.3) else 'unknown'",
                "        elif '; only6' in scope:",
                "            verdict = 'sat' if engine == '6' else 'unknown'",
                "        elif '; nap' in scope:",
                "            time.sleep(1); verdict = 'unsat'",
                "        elif '; split' in scope:",
                "            if engine == '2': time.sleep(0.2)",
                "            verdict = 'sat' if engine == '2' else 'unsat'",
                "        elif engine == '6' and not search(0.3):",
                "            verdict = 'unknown'",
                "        else:",
                "            verdict = 'sat' if '; sat' in scope else 'unsat'",
                "        say(verdict)",
                "    elif '(get-value' in text:",
                "        if '; modelcut' in scope: oom()",
                "        say('((x 1))')",
                "    elif '(get-unsat-core)' in text:",
                "        if '; corecut' in scope: oom()",
                "        say('(c)')",
                "    elif '; slowread' in text:",
                "        time.sleep(12)",
                "    elif '(get-info' in text:",
                "        say('(:reason-unknown \"' + reason + '\")')",
                "    say(said[len('(echo \"'):-2])",
                "    text = ''"), StandardCharsets.UTF_8);
        assertTrue(script.toFile().setExecutable(true));
        return script;
    }

    private static Path z3() {
        Path z3 = Paths.get("/usr/local/bin/z3");
        return Files.isExecutable(z3) ? z3 : Paths.get("z3");
    }
}
