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
import java.util.ArrayList;
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

    @Test(timeout = 120000L)
    public void eightPairsOnOneHostStartInWavesAndAllAnswer()
            throws Exception {
        Path visible = folder.newFolder("waves-visible").toPath();
        Path ssh = ScopedFixture.ssh(folder.newFolder("waves").toPath());
        Z3 solver = new Z3(fake(), 30000L, 2048, Arrays.asList(
                new Z3.Room("far", 8 * 2 * Z3Incremental.PAIR_SLOT_MB,
                        Arrays.asList(ssh.toString(), "far"))), visible);
        java.util.concurrent.ExecutorService askers =
                java.util.concurrent.Executors.newFixedThreadPool(16);
        try (Z3Incremental scopes = new Z3Incremental(solver,
                output -> output.write("(declare-const x Int)\n"), 8)) {
            List<java.util.concurrent.Future<Z3.Answer>> asked =
                    new ArrayList<java.util.concurrent.Future<Z3.Answer>>();
            for (int at = 0; at < 16; at++) {
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

    private Path fake() throws IOException {
        return fake(folder.newFile("unused.log").toPath());
    }

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
