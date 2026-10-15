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
 *       one scope ({@code Composition#scopeQuery}) of a long-lived z3 that
 *       read what every path shares once ({@code Composition#sharedQuery},
 *       {@link Z3Incremental}): SGF6-bugs-snapshot-no-active 0001's paths
 *       share 65 of their 69 MB, read again by every path's own z3 before
 *       (4 of a path's 5.5-8 s).</li>
 *   <li><b>A refuted path stays refuted.</b>  Assertions only add
 *       constraints: a path unsat under some assertions is unsat under every
 *       set that contains them, so it is not asked again there; its
 *       refutation answers for it, core and all.  A path unsat with no
 *       assertion at all ({@link #selfCheck}) refutes itself under every
 *       valuation; its core names no pin, so where the body asserts no
 *       refuted claim it names nothing a core is read for, and the
 *       self-check asks none.  Any other refutation asked without a core
 *       answers only asks that want none.  hdfs-11741 i1: 155 of 157 paths
 *       refute themselves, so every pinned re-ask of the witness (as it
 *       happened, clocks pinned, the least clocks, the margins) asks two
 *       paths, not 157.</li>
 *   <li><b>A path is asked under the pins it names first.</b>  A
 *       valuation pins every declared root; a path's question names few
 *       of them ({@code Composition#rootsOf}).  Asked under the pins of
 *       those alone -- a subset of the valuation's assertions -- an unsat
 *       there is the path's refutation under every valuation agreeing on
 *       them, so each path is asked once per distinct projection, not once
 *       per valuation (SGF6-bugs-snapshot-no-active 0001: 141 paths, 128
 *       valuations); that first try takes at most a quarter of the path's
 *       budget ({@link #PROJECTED_SHARE}).  Sat or undecided there, the
 *       whole valuation decides, within the whole budget: an unsat is only
 *       ever read off a subset of the assertions asked, and a memout or
 *       timeout is never one.  A path's own run is asked so too, its
 *       refutations remembered apart.</li>
 * </ul>
 *
 * <p>Selectors are never asserted together: two contradict the partition.
 * The asks of one composition share one pool and one set of scoped z3s;
 * {@link #close} stops them and every z3 still running for it.</p>
 */
final class Disjunction implements AutoCloseable {

    /** Budget of a disjunction's verdict asked whole (its model and core
     *  runs keep the solver's). */
    static final long WHOLE_BUDGET_MS = 60000L;

    /** Budget of a path's ask in its own run ({@link #pathAsk}), at most
     *  the solver's. */
    static final long OWN_RUN_BUDGET_MS = 600000L;

    /**
     * A path's question under the pins its question names
     * ({@link #projected}) takes at most this share of the path's budget,
     * one in this many; the question under every pin keeps the whole
     * budget of its own.  Its projected roots follow only the commands
     * every path shares that name two or more of them, so the projection
     * can leave out a pin it needs and be sat or undecided where the
     * whole question is unsat: it is a first try, never the path's budget.
     */
    static final int PROJECTED_SHARE = 4;

    /** Budget of a path's self-refutation run: decides a path, scans them
     *  all. */
    static final long SELF_CHECK_BUDGET_MS = 60000L;

    /**
     * How many path questions are put to the scoped z3s at once
     * ({@link Z3Incremental}), which ask them in order, one at a time: the
     * ones after a sat path are stopped before they are asked.
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
    /** The solver of whole asks. */
    private final Z3 solver;
    /** Every path's question, a scope over what the paths share. */
    private final Z3Incremental scopes;
    private final ExecutorService pool;
    private final Map<String, List<Refutation>> refuted;
    /** The pin sets each path's own run ({@code Composition#ownRun}) was
     *  found unsat under, by selector: such a run is not asked again under
     *  any set containing one. */
    private final Map<String, List<Set<String>>> ownRefuted;
    /** Each path's self-check answer, by selector ({@link #selfCheck}). */
    private final Map<String, Z3.Answer> selfChecked;
    /** Set once a whole ask ran past its budget or its memory cap. */
    private final AtomicBoolean pathByPath;

    Disjunction(Composer.Composition composition, Z3 solver) {
        this(composition, solver, new Z3Incremental(solver,
                        composition.sharedQuery()),
                Executors.newFixedThreadPool(PATH_ASKS),
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

    /**
     * This disjunction as {@code asksAtOnce} callers ask it together
     * ({@code ClaimPolicy}'s valuations): its refutations, its scoped z3s,
     * its pool and whether it asks path by path shared, each whole ask's
     * z3s in a slot of the composer's z3 room shared that many ways
     * ({@code Z3#shared}).  Its owner closes them.
     */
    Disjunction asking(int asksAtOnce) {
        return new Disjunction(composition, solver.shared(asksAtOnce), scopes,
                pool, refuted, ownRefuted, selfChecked, pathByPath);
    }

    /**
     * Every path alone with no assertion, within
     * {@link #SELF_CHECK_BUDGET_MS}: an unsat one contradicts itself -- or a
     * refuted claim the formula asserts excludes it, which its core names,
     * so it is asked with its core where the formula asserts one -- and is
     * remembered as refuted under every set of assertions, answering every
     * ask that rests on it ({@link #refutation}).  Its core names no pin
     * (it was asked under none), so where no refuted claim is asserted it
     * names nothing a core is read for and is not asked for
     * (SGF6-bugs-snapshot-no-active 0001: 141 paths' core runs, 26 of 48 at
     * their cap, held the decide for hours).  Within {@code capMillis} in
     * all ({@code <= 0}: none): past it no path is asked and the one
     * running ends, each undecided -- never a refutation, the path left in
     * the disjunction ({@code ClaimPolicy#SELF_CHECK_SHARE}).  The
     * answers, in the disjuncts' order.
     */
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
     * ({@code Composition#scopeWithoutFatalArm}), within
     * {@link #SELF_CHECK_BUDGET_MS}: what its own run satisfied, so unsat
     * is a contradiction the composition built.  In the disjuncts' order.
     */
    List<Z3.Answer> withoutFatalArms() {
        return alone(composition::scopeWithoutFatalArm, false, scopes);
    }

    /** One question per path, asked {@link #PATH_ASKS} at a time of
     *  {@code by} with no assertion, a core where {@code wantCore}, read
     *  back in the disjuncts' order. */
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
        if (open && !pathByPath.get()) {
            // At its own slot: at its cap, every path is a smaller question
            // than the whole asked alone (Z3#ask).
            Z3.Answer whole = solver.ask(
                    composition.query(assertions), asked, wantCore,
                    WHOLE_BUDGET_MS);
            if (whole.decided()) return whole;
            // Past its budget, or at its memory cap: every path is a
            // smaller question.
            if (whole.timedOut() || whole.memOut()) pathByPath.set(true);
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
            // The asks after a sat path answer nothing: stopped, each check
            // still running cancelled (Z3Incremental).
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
        return pathAsk(selector, assertions, asked, wantCore, budgetMillis);
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
        return pathAnswer(selector, assertions, asked, wantCore,
                Math.max(1L, deadline - System.currentTimeMillis()));
    }

    /**
     * One path asked free under {@code assertions} within
     * {@code budgetMillis} ({@code <= 0}: the solver's): first under the
     * pins of the roots its question names ({@link #projected}), within its
     * {@link #PROJECTED_SHARE}, whose unsat refutes it under every valuation
     * agreeing on them; sat or undecided there, under them all, within the
     * whole budget.  Its unsat is remembered under what it was asked
     * under.
     */
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

    /**
     * {@code assertions} without the valuation pins of roots the path's
     * question does not name ({@code Composition#rootsOf}): a subset, so
     * its unsat is theirs.
     */
    private List<String> projected(String selector, List<String> assertions) {
        Set<String> roots = composition.rootsOf(selector);
        List<String> kept = new ArrayList<String>();
        for (String assertion : assertions) {
            String root = Composer.pinnedRoot(assertion);
            if (root == null || roots.contains(root)) kept.add(assertion);
        }
        return kept;
    }

    /**
     * The path asked in its own run ({@code Composition#ownRun}) within
     * {@link #OWN_RUN_BUDGET_MS} and {@code budget}; null where it has none,
     * or where it was found unsat under a subset of these pins already.
     * First under the pins its question names ({@link #projected}), within
     * its {@link #PROJECTED_SHARE}: unsat there is remembered for every
     * valuation agreeing on them; sat or undecided there, it is asked under
     * them all, within the whole budget.
     */
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

    /** The answer of a refutation of {@code selector} under a subset of
     *  {@code under}, one with a complete core when one is wanted -- or one
     *  asked under no assertion where the body asserts no refuted claim:
     *  its core names nothing a core is read for ({@link #selfCheck}) --
     *  or null. */
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
