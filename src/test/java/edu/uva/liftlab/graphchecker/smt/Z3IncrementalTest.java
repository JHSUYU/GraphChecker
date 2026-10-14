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
                output -> output.write(SHARED))) {
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
     * too; an unsat whose core was cut stands, its core unknown.
     * {scope, symbols, core wanted, status, values, core known}.
     */
    @Test
    public void aZ3ThatEndsMidQuestionAnswersItNothing() throws IOException {
        Object[][] rows = {
                {"; unsat", "", false, "unsat", "{}", false},
                {"; oom", "", false, "memout", "{}", false},
                {"; sat", "x", false, "sat", "{x=1}", false},
                {"; sat ; modelcut", "x", false, "memout", "{}", false},
                {"; unsat ; corecut", "", true, "unsat", "{}", false},
                {"; unsat", "", true, "unsat", "{}", true},
                {"; sat", "", false, "sat", "{}", false},
        };
        Z3 solver = new Z3(fake(), 3000L, 4096);
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"))) {
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
                output -> output.write("(declare-const x Int)\n"))) {
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

    private Path fake() throws IOException {
        return fake(folder.newFile("unused.log").toPath());
    }

    /**
     * A z3 answering scopes as their {@code ; <word>} comments say:
     * {@code oom} runs out of memory on the check, {@code modelcut} on its
     * model, {@code corecut} on its core; {@code slow} searches a minute
     * under engine 6 unless SIGINT cancels it, a second under engine 2,
     * then unsat; {@code late2} searches a minute under engine 2 unless
     * SIGINT cancels it, and is sat at once under engine 6; {@code only6}
     * is sat under engine 6, unknown under 2;
     * else {@code sat} ({@code ((x 1))}) or unsat (core {@code (c)}).  Each
     * start logged.
     */
    private Path fake(Path log) throws IOException {
        Path script = folder.newFile("z3-scoped.py").toPath();
        Files.write(script, Arrays.asList("#!/usr/bin/env python3",
                "import signal, sys, time",
                "class Cancelled(Exception): pass",
                "solving = False; pending = False",
                "def cancel(signum, frame):",
                "    global pending",
                "    if solving: raise Cancelled()",
                "    pending = True",
                "signal.signal(signal.SIGINT, cancel)",
                "with open('" + log + "', 'a') as starts: starts.write("
                        + "'start\\n')",
                "engine = '2'; text = ''; scope = ''; verdict = ''",
                "def say(line):",
                "    sys.stdout.write(line + '\\n'); sys.stdout.flush()",
                "def oom():",
                "    say('(error \"out of memory\")'); sys.exit(101)",
                "while True:",
                "    line = sys.stdin.readline()",
                "    if not line: break",
                "    said = line.strip()",
                "    if said.startswith('(set-option :smt.arith.solver '):",
                "        engine = said.split(' ')[-1].rstrip(')')",
                "    if said == '(push 1)': scope = ''",
                "    if not said.startswith('(echo \"'):",
                "        text += line; scope += line; continue",
                "    if '(check-sat)' in text:",
                "        if '; oom' in scope: oom()",
                "        if ('; slow' in scope and engine == '6')"
                        + " or ('; late2' in scope and engine == '2'):",
                "            solving = True",
                "            try:",
                "                if pending: raise Cancelled()",
                "                time.sleep(60); verdict = 'sat'",
                "            except Cancelled: verdict = 'unknown'",
                "            finally: solving = False",
                "        elif '; slow' in scope:",
                "            time.sleep(1); verdict = 'unsat'",
                "        elif '; only6' in scope or '; late2' in scope:",
                "            verdict = 'sat' if engine == '6' else 'unknown'",
                "        else:",
                "            verdict = 'sat' if '; sat' in scope else 'unsat'",
                "        pending = False",
                "        say(verdict)",
                "    elif '(get-value' in text:",
                "        if '; modelcut' in scope: oom()",
                "        say('((x 1))')",
                "    elif '(get-unsat-core)' in text:",
                "        if '; corecut' in scope: oom()",
                "        say('(c)')",
                "    elif '(get-info' in text:",
                "        say('(:reason-unknown \"' + ('canceled' if verdict"
                        + " == 'unknown' else 'incomplete') + '\")')",
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
