package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Z3;

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
import java.util.function.Function;

/**
 * How one composition's disjunction is asked ({@link ClaimPolicy}): "one of
 * these paths" under some assertions, which already say one of them holds.
 *
 * <ul>
 *   <li><b>Whole first, while that decides.</b>  Asked whole, within
 *       {@link #WHOLE_BUDGET_MS}, z3 decides in seconds where it decides at
 *       all, one parse for every path.  Once a whole ask of the composition
 *       ran past that budget, every later one is asked path by path: they
 *       are the same disjunction under more pins (hdfs-11741 i1, 157 paths:
 *       24 of its 31 whole asks ran their 60 s out, 21 of them in a row,
 *       each followed by every path asked anyway).</li>
 *   <li><b>Path by path, in parallel.</b>  The body asserts exactly one path
 *       selector, so the disjunction is sat iff some path is and unsat iff
 *       every one is (its core the union of theirs).  The paths are asked
 *       {@link #PATH_ASKS} at a time, in their order, and the answer is the
 *       one the paths give in order: the first sat path's (every path
 *       before it refuted or undecided, the asks after it stopped), else
 *       undecided if any path was, else unsat.  Whole, z3 can spend any
 *       budget searching every path's conjunction at once where a case
 *       split settles each path in a second (hdfs-11741 r3).  A path is
 *       asked by {@code Composition#pathQuery}: the shared commands and its
 *       own.</li>
 *   <li><b>A refuted path stays refuted.</b>  Assertions only add
 *       constraints: a path unsat under some assertions is unsat under every
 *       set that contains them, so it is not asked again there; its
 *       refutation answers for it, core and all.  A path unsat with no
 *       assertion at all ({@link #selfCheck}, asked with its core) refutes
 *       itself under every valuation; its core names no pin, only what the
 *       body asserts by name (a refuted claim).  A refutation asked without
 *       a core answers only asks that want none.  hdfs-11741 i1: 155 of 157
 *       paths refute themselves, so every pinned re-ask of the witness
 *       (as it happened, clocks pinned, the least clocks, the margins)
 *       asks two paths, not 157.</li>
 * </ul>
 *
 * <p>Selectors are never asserted together: two contradict the partition.
 * The asks of one composition share one pool; {@link #close} stops it and
 * every z3 still running for it.</p>
 */
final class Disjunction implements AutoCloseable {

    /** Budget of a disjunction's verdict asked whole (its model and core
     *  runs keep the solver's). */
    static final long WHOLE_BUDGET_MS = 60000L;

    /** Budget of a path's ask in its own run ({@link #pathAsk}), at most
     *  the solver's. */
    static final long OWN_RUN_BUDGET_MS = 600000L;

    /** Budget of a path's self-refutation run: decides a path, scans them
     *  all. */
    static final long SELF_CHECK_BUDGET_MS = 60000L;

    /**
     * How many path asks run at once: sixteen z3 processes, two per ask (one
     * per arithmetic engine, {@code Z3#run}), on a 48-core host, each
     * started only while the host has memory to spare ({@code Z3}).
     */
    static final int PATH_ASKS = 8;

    /** One path found unsat under these assertions. */
    private static final class Refutation {
        final Set<String> under;
        final Z3.Answer answer;
        /** Whether its core is known: only a real core names what it rests
         *  on (the body's named assertions too, an excluded model's). */
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
    private final ExecutorService pool;
    private final Map<String, List<Refutation>> refuted =
            new ConcurrentHashMap<String, List<Refutation>>();
    /** Each path's self-check answer, by selector ({@link #selfCheck}). */
    private final Map<String, Z3.Answer> selfChecked =
            new ConcurrentHashMap<String, Z3.Answer>();
    /** Set once a whole ask ran past its budget. */
    private volatile boolean pathByPath;

    Disjunction(Composer.Composition composition, Z3 solver) {
        this.composition = composition;
        this.solver = solver;
        this.pool = Executors.newFixedThreadPool(PATH_ASKS);
    }

    /**
     * Every path alone with no assertion, within
     * {@link #SELF_CHECK_BUDGET_MS}, asked with its core: an unsat one
     * contradicts itself -- or a refuted claim the formula asserts excludes
     * it, which its core names -- and is remembered as refuted under every
     * set of assertions, its core reused by every answer that rests on it
     * ({@link #refutation}).  The answers, in the disjuncts' order.
     */
    List<Z3.Answer> selfCheck() {
        List<String> none = Collections.emptyList();
        List<Z3.Answer> answers = alone(
                selector -> composition.pathQuery(selector, none), true);
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

    /** Whether this path's own self-check ({@link #selfCheck}) is unsat
     *  with a core naming a model the formula excludes: one CONFIRM refuted
     *  or gave no verdict on excludes it, no contradiction of its run. */
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

    /**
     * Every path alone with its fatal arm left out
     * ({@code Composition#withoutFatalArm}), within
     * {@link #SELF_CHECK_BUDGET_MS}: what its own run satisfied, so unsat
     * is a contradiction the composition built.  In the disjuncts' order.
     */
    List<Z3.Answer> withoutFatalArms() {
        return alone(composition::withoutFatalArm, false);
    }

    /** One question per path, asked {@link #PATH_ASKS} at a time with no
     *  assertion, a core where {@code wantCore}, read back in the
     *  disjuncts' order. */
    private List<Z3.Answer> alone(
            Function<String, ArtifactIO.Body> question, boolean wantCore) {
        List<String> none = Collections.emptyList();
        List<Future<Z3.Answer>> pending = new ArrayList<Future<Z3.Answer>>();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            String selector = disjunct.selector();
            pending.add(pool.submit(() -> solver.ask(question.apply(selector),
                    none, wantCore, SELF_CHECK_BUDGET_MS)));
        }
        List<Z3.Answer> answers = new ArrayList<Z3.Answer>();
        for (Future<Z3.Answer> each : pending) answers.add(get(each));
        return answers;
    }

    /**
     * "One of {@code selectors}" under {@code assertions}, asking for the
     * values of {@code asked} on sat and for a core on unsat when
     * {@code wantCore}: whole while that decides, else path by path.
     */
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
        // With every path refuted already there is nothing to ask.
        if (open && !pathByPath) {
            Z3.Answer whole = solver.ask(composition.query(assertions),
                    asked, wantCore, WHOLE_BUDGET_MS);
            if (whole.decided()) return whole;
            if (whole.timedOut()) pathByPath = true;
        }
        // Every open path's own run first, all of them: a sat one answers
        // before any path is asked free (hdfs-11741 L1: a path its own run
        // refutes ran its free ask out for 30 minutes ahead of the next
        // path's own run, sat in 100 s).
        Z3.Answer ownRun = ownRuns(selectors, known, assertions, asked);
        if (ownRun != null) return ownRun;
        List<Future<Z3.Answer>> pending = new ArrayList<Future<Z3.Answer>>();
        for (int at = 0; at < selectors.size(); at++) {
            String selector = selectors.get(at);
            pending.add(known.get(at) != null ? null : pool.submit(
                    () -> solver.ask(composition.pathQuery(selector,
                            assertions), asked, wantCore)));
        }
        try {
            List<Z3.Answer> refutations = new ArrayList<Z3.Answer>();
            Z3.Answer undecided = null;
            for (int at = 0; at < selectors.size(); at++) {
                Z3.Answer answer = known.get(at);
                if (answer == null) {
                    answer = get(pending.get(at));
                    if (answer.unsat()) {
                        remember(selectors.get(at), under, answer,
                                wantCore && answer.coreKnown());
                    }
                }
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
            // The asks after a sat path answer nothing: stopped, their z3s
            // with them (Z3#run kills its processes when interrupted).
            for (Future<Z3.Answer> each : pending) {
                if (each != null) each.cancel(true);
            }
        }
    }

    /**
     * The first open path, in order, its own run answers sat for
     * ({@link #ownRun}), its asks after it stopped; null when none does.
     */
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

    /** One path alone under {@code assertions}, with the solver's budget,
     *  answered by its refutation where it has one. */
    Z3.Answer askPath(String selector, List<String> assertions,
                      List<String> asked, boolean wantCore) {
        return askPath(selector, assertions, asked, wantCore, 0L);
    }

    /** The same within {@code budgetMillis} ({@code <= 0}: the solver's). */
    Z3.Answer askPath(String selector, List<String> assertions,
                      List<String> asked, boolean wantCore,
                      long budgetMillis) {
        Set<String> under = new HashSet<String>(assertions);
        Z3.Answer known = refutation(selector, under, wantCore);
        if (known != null) return known;
        Z3.Answer answer = pathAsk(selector, assertions, asked, wantCore,
                budgetMillis);
        if (answer.unsat()) {
            remember(selector, under, answer, wantCore && answer.coreKnown());
        }
        return answer;
    }

    /**
     * One path under {@code assertions}, in its own run first: with the arm
     * of each message its session sent it and each state read's observed
     * writer ({@code Composition#ownRun}), a model is a model of the
     * question, and z3 finds one where the question asked free runs its
     * budget out (hdfs-11741 L1: two fatal-observing paths sat in about 100
     * s so, undecided after 30 minutes free).  Asked free only where its own
     * run is refuted or undecided within {@link #OWN_RUN_BUDGET_MS}.
     */
    private Z3.Answer pathAsk(String selector, List<String> assertions,
                              List<String> asked, boolean wantCore,
                              long budgetMillis) {
        long budget = budgetMillis > 0L
                ? Math.min(budgetMillis, solver.timeoutMillis())
                : solver.timeoutMillis();
        long deadline = System.currentTimeMillis() + budget;
        Z3.Answer own = ownRun(selector, assertions, asked, budget);
        if (own != null && own.sat()) return own;
        return solver.ask(composition.pathQuery(selector, assertions),
                asked, wantCore, Math.max(1L,
                        deadline - System.currentTimeMillis()));
    }

    /** The path asked in its own run ({@code Composition#ownRun}) within
     *  {@link #OWN_RUN_BUDGET_MS} and {@code budget}; null where it has
     *  none. */
    private Z3.Answer ownRun(String selector, List<String> assertions,
                             List<String> asked, long budget) {
        List<String> own = composition.ownRun(selector);
        if (own.isEmpty()) return null;
        List<String> held = new ArrayList<String>(assertions);
        held.addAll(own);
        return solver.ask(composition.pathQuery(selector, held), asked,
                false, Math.min(OWN_RUN_BUDGET_MS, budget));
    }

    /** The answer of a refutation of {@code selector} under a subset of
     *  {@code under}, one with a complete core when one is wanted, or
     *  null. */
    private Z3.Answer refutation(String selector, Set<String> under,
                                 boolean wantCore) {
        List<Refutation> found = refuted.get(selector);
        if (found == null) return null;
        for (Refutation each : found) {
            if ((!wantCore || each.coreComplete)
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
    }
}
