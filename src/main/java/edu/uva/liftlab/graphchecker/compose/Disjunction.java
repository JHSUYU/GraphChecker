package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Z3;
import edu.uva.liftlab.graphchecker.smt.Z3Incremental;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Function;

final class Disjunction implements AutoCloseable {

    static final long WHOLE_BUDGET_MS = 60000L;

    static final long OWN_RUN_BUDGET_MS = 600000L;

    static final int PROJECTED_SHARE = 4;

    static final long SELF_CHECK_BUDGET_MS = 60000L;

    static final int LEAST_PATH_ASKS = 8;

    private static final class Refutation {
        final Set<String> under;
        final Z3.Answer answer;
        final boolean coreComplete;

        Refutation(Set<String> under, Z3.Answer answer,
                   boolean coreComplete) {
            this.under = under;
            this.answer = answer;
            this.coreComplete = coreComplete;
        }
    }

    private final Composer.Composition composition;
    private final Z3 solver;
    private final Z3Incremental scopes;
    private final ExecutorService pool;
    private final Map<String, List<Refutation>> refuted;
    private final Map<String, List<Set<String>>> ownRefuted;
    private final Map<String, Z3.Answer> selfChecked;
    private final AtomicBoolean pathByPath;

    Disjunction(Composer.Composition composition, Z3 solver) {
        this(composition, solver, Math.max(LEAST_PATH_ASKS,
                Z3Incremental.placeable(solver)));
    }

    private Disjunction(Composer.Composition composition, Z3 solver,
                        int pathAsks) {
        this(composition, solver, new Z3Incremental(solver,
                        composition.sharedQuery(), pathAsks),
                Executors.newFixedThreadPool(pathAsks),
                new ConcurrentHashMap<String, List<Refutation>>(),
                new ConcurrentHashMap<String, List<Set<String>>>(),
                new ConcurrentHashMap<String, Z3.Answer>(),
                new AtomicBoolean());
    }

    private Disjunction(Composer.Composition composition, Z3 solver,
                        Z3Incremental scopes, ExecutorService pool,
                        Map<String, List<Refutation>> refuted,
                        Map<String, List<Set<String>>> ownRefuted,
                        Map<String, Z3.Answer> selfChecked,
                        AtomicBoolean pathByPath) {
        this.composition = composition;
        this.solver = solver;
        this.scopes = scopes;
        this.pool = pool;
        this.refuted = refuted;
        this.ownRefuted = ownRefuted;
        this.selfChecked = selfChecked;
        this.pathByPath = pathByPath;
    }

    Disjunction asking(int asksAtOnce) {
        return new Disjunction(composition, solver.shared(asksAtOnce), scopes,
                pool, refuted, ownRefuted, selfChecked, pathByPath);
    }

    List<Z3.Answer> selfCheck(long capMillis) {
        List<String> none = Collections.emptyList();
        List<Z3.Answer> answers = alone(
                selector -> composition.scopeQuery(selector, none),
                composition.assertsRefutations(), capMillis <= 0L ? scopes
                        : scopes.until(System.nanoTime() + TimeUnit
                        .MILLISECONDS.toNanos(capMillis)));
        for (int at = 0; at < answers.size(); at++) {
            String selector = composition.disjuncts().get(at).selector();
            selfChecked.put(selector, answers.get(at));
            if (answers.get(at).unsat()) {
                remember(selector, new HashSet<String>(), answers.get(at),
                        answers.get(at).coreKnown());
            }
        }
        return answers;
    }

    boolean refutedBySelfCheck(String selector) {
        Z3.Answer answer = selfChecked.get(selector);
        if (answer == null || !answer.unsat() || !answer.coreKnown()) {
            return false;
        }
        for (String label : answer.core()) {
            if (Composer.excludesAModel(label)) return true;
        }
        return false;
    }

    List<Z3.Answer> withoutFatalArms() {
        return alone(composition::scopeWithoutFatalArm, false, scopes);
    }

    private List<Z3.Answer> alone(
            Function<String, ArtifactIO.Body> question, boolean wantCore,
            Z3Incremental by) {
        List<String> none = Collections.emptyList();
        List<Future<Z3.Answer>> pending = new ArrayList<Future<Z3.Answer>>();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            String selector = disjunct.selector();
            pending.add(pool.submit(() -> by.ask(
                    question.apply(selector), none, wantCore,
                    SELF_CHECK_BUDGET_MS)));
        }
        List<Z3.Answer> answers = new ArrayList<Z3.Answer>();
        for (Future<Z3.Answer> each : pending) answers.add(get(each));
        return answers;
    }

    Z3.Answer ask(List<String> assertions, List<String> selectors,
                  List<String> asked, boolean wantCore) {
        Set<String> under = new HashSet<String>(assertions);
        List<Z3.Answer> known = new ArrayList<Z3.Answer>();
        boolean open = false;
        for (String selector : selectors) {
            Z3.Answer refutation = refutation(selector, under, wantCore);
            known.add(refutation);
            open |= refutation == null;
        }
        if (open && !pathByPath.get()) {
            Z3.Answer whole = solver.ask(
                    composition.query(assertions), asked, wantCore,
                    WHOLE_BUDGET_MS);
            if (whole.decided()) return whole;
            if (whole.timedOut() || whole.memOut()) pathByPath.set(true);
        }
        Z3.Answer ownRun = ownRuns(selectors, known, assertions, asked);
        if (ownRun != null) return ownRun;
        List<Future<Z3.Answer>> pending = new ArrayList<Future<Z3.Answer>>();
        for (int at = 0; at < selectors.size(); at++) {
            String selector = selectors.get(at);
            pending.add(known.get(at) != null ? null : pool.submit(
                    () -> pathAnswer(selector, assertions, asked, wantCore,
                            0L)));
        }
        try {
            List<Z3.Answer> refutations = new ArrayList<Z3.Answer>();
            Z3.Answer undecided = null;
            for (int at = 0; at < selectors.size(); at++) {
                Z3.Answer answer = known.get(at);
                if (answer == null) answer = get(pending.get(at));
                if (answer.sat()) return answer;
                if (answer.unsat()) {
                    refutations.add(answer);
                } else if (undecided == null) {
                    undecided = answer;
                }
            }
            return undecided != null ? undecided
                    : Z3.Answer.unsatOfAll(refutations);
        } finally {
            for (Future<Z3.Answer> each : pending) {
                if (each != null) each.cancel(true);
            }
        }
    }

    private Z3.Answer ownRuns(List<String> selectors, List<Z3.Answer> known,
                              List<String> assertions, List<String> asked) {
        List<Future<Z3.Answer>> pending = new ArrayList<Future<Z3.Answer>>();
        for (int at = 0; at < selectors.size(); at++) {
            String selector = selectors.get(at);
            pending.add(known.get(at) != null ? null : pool.submit(
                    () -> ownRun(selector, assertions, asked,
                            solver.timeoutMillis())));
        }
        try {
            for (Future<Z3.Answer> each : pending) {
                if (each == null) continue;
                Z3.Answer answer = get(each);
                if (answer != null && answer.sat()) return answer;
            }
            return null;
        } finally {
            for (Future<Z3.Answer> each : pending) {
                if (each != null) each.cancel(true);
            }
        }
    }

    Z3.Answer askPath(String selector, List<String> assertions,
                      List<String> asked, boolean wantCore) {
        return askPath(selector, assertions, asked, wantCore, 0L);
    }

    Z3.Answer askPath(String selector, List<String> assertions,
                      List<String> asked, boolean wantCore,
                      long budgetMillis) {
        Set<String> under = new HashSet<String>(assertions);
        Z3.Answer known = refutation(selector, under, wantCore);
        if (known != null) return known;
        return pathAsk(selector, assertions, asked, wantCore, budgetMillis);
    }

    Z3.Answer whole(List<String> assertions, List<String> asked,
                    boolean wantCore, long budgetMillis) {
        Z3.Answer answer = solver.ask(composition.query(assertions), asked,
                wantCore, budgetMillis);
        if (answer.timedOut() || answer.memOut()) pathByPath.set(true);
        return answer;
    }

    Z3.Answer askOwnRun(String selector, List<String> assertions,
                        List<String> asked, long budgetMillis) {
        long budget = Math.max(1L, Math.min(budgetMillis,
                solver.timeoutMillis()));
        if (composition.ownRun(selector).isEmpty()) {
            return askPath(selector, assertions, asked, false, budget);
        }
        Z3.Answer own = ownRun(selector, assertions, asked, budget);
        return own != null ? own : Z3.Answer.decided("unsat",
                Collections.<String, String>emptyMap());
    }

    private Z3.Answer pathAsk(String selector, List<String> assertions,
                              List<String> asked, boolean wantCore,
                              long budgetMillis) {
        long budget = budgetMillis > 0L
                ? Math.min(budgetMillis, solver.timeoutMillis())
                : solver.timeoutMillis();
        long deadline = System.currentTimeMillis() + budget;
        Z3.Answer own = ownRun(selector, assertions, asked, budget);
        if (own != null && own.sat()) return own;
        return pathAnswer(selector, assertions, asked, wantCore,
                Math.max(1L, deadline - System.currentTimeMillis()));
    }

    private Z3.Answer pathAnswer(String selector, List<String> assertions,
                                 List<String> asked, boolean wantCore,
                                 long budgetMillis) {
        long budget = budgetMillis > 0L
                ? Math.min(budgetMillis, solver.timeoutMillis())
                : solver.timeoutMillis();
        List<String> fewer = projected(selector, assertions);
        if (fewer.size() < assertions.size()) {
            Z3.Answer first = scopes.ask(composition.scopeQuery(selector,
                    fewer), Collections.<String>emptyList(), wantCore,
                    Math.max(1L, budget / PROJECTED_SHARE));
            if (first.unsat()) {
                remember(selector, new HashSet<String>(fewer), first,
                        wantCore && first.coreKnown());
                return first;
            }
        }
        Z3.Answer answer = scopes.ask(composition.scopeQuery(selector,
                assertions), asked, wantCore, budget);
        if (answer.unsat()) {
            remember(selector, new HashSet<String>(assertions), answer,
                    wantCore && answer.coreKnown());
        }
        return answer;
    }

    private List<String> projected(String selector, List<String> assertions) {
        Set<String> roots = composition.rootsOf(selector);
        List<String> kept = new ArrayList<String>();
        for (String assertion : assertions) {
            String root = Composer.pinnedRoot(assertion);
            if (root == null || roots.contains(root)) kept.add(assertion);
        }
        return kept;
    }

    private Z3.Answer ownRun(String selector, List<String> assertions,
                             List<String> asked, long budget) {
        List<String> own = composition.ownRun(selector);
        if (own.isEmpty()) return null;
        Set<String> under = new HashSet<String>(assertions);
        for (Set<String> refutedUnder : ownRefuted.getOrDefault(selector,
                Collections.<Set<String>>emptyList())) {
            if (under.containsAll(refutedUnder)) return null;
        }
        long runBudget = Math.min(OWN_RUN_BUDGET_MS, budget);
        List<String> fewer = projected(selector, assertions);
        if (fewer.size() < assertions.size()) {
            List<String> held = new ArrayList<String>(fewer);
            held.addAll(own);
            Z3.Answer first = scopes.ask(composition.scopeQuery(selector,
                    held), Collections.<String>emptyList(), false,
                    Math.max(1L, runBudget / PROJECTED_SHARE));
            if (first.unsat()) {
                ownRefuted(selector, new HashSet<String>(fewer));
                return first;
            }
        }
        List<String> held = new ArrayList<String>(assertions);
        held.addAll(own);
        Z3.Answer answer = scopes.ask(composition.scopeQuery(selector,
                held), asked, false, runBudget);
        if (answer.unsat()) ownRefuted(selector, under);
        return answer;
    }

    private void ownRefuted(String selector, Set<String> under) {
        ownRefuted.computeIfAbsent(selector,
                key -> new CopyOnWriteArrayList<Set<String>>()).add(under);
    }

    private Z3.Answer refutation(String selector, Set<String> under,
                                 boolean wantCore) {
        List<Refutation> found = refuted.get(selector);
        if (found == null) return null;
        boolean bare = !composition.assertsRefutations();
        for (Refutation each : found) {
            if ((!wantCore || each.coreComplete
                    || (bare && each.under.isEmpty()))
                    && under.containsAll(each.under)) {
                return each.answer;
            }
        }
        return null;
    }

    private void remember(String selector, Set<String> under,
                          Z3.Answer answer, boolean coreComplete) {
        refuted.computeIfAbsent(selector,
                key -> new CopyOnWriteArrayList<Refutation>())
                .add(new Refutation(under, answer, coreComplete));
    }

    private static Z3.Answer get(Future<Z3.Answer> pending) {
        try {
            return pending.get();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException("interrupted while solving",
                    interrupted);
        } catch (ExecutionException failed) {
            Throwable cause = failed.getCause();
            if (cause instanceof RuntimeException) {
                throw (RuntimeException) cause;
            }
            throw new IllegalStateException(cause);
        }
    }

    @Override
    public void close() {
        pool.shutdownNow();
        scopes.close();
    }
}
