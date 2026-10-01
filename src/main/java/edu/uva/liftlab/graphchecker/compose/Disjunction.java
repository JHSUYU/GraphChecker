package edu.uva.liftlab.graphchecker.compose;

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

/**
 * How one composition's disjunction is asked ({@link ClaimPolicy}): "one of
 * these paths" under some assertions, which already say one of them holds.
 *
 * <ul>
 *   <li><b>Whole first, while that decides.</b>  Asked whole, within
 *       {@link #WHOLE_BUDGET_MS}, z3 decides in seconds where it decides at
 *       all, one parse for every path.  Once a whole ask of the composition
 *       ran past that budget, every later one is asked path by path: they
 *       are the same disjunction under more pins (hdfs-11741 i1: 157 paths,
 *       and every whole ask after the first ran its 60 s out or near it,
 *       about two dozen of them in a row).</li>
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
 *       assertion at all ({@link #selfCheck}) refutes itself under every
 *       valuation, and its core names no pin.  A refutation asked without a
 *       core answers only asks that want none.  hdfs-11741 i1: 155 of 157
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
        /** Whether its core names every pin it rests on: it was asked for
         *  one, or under no pin at all. */
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
    /** Set once a whole ask ran past its budget. */
    private volatile boolean pathByPath;

    Disjunction(Composer.Composition composition, Z3 solver) {
        this.composition = composition;
        this.solver = solver;
        this.pool = Executors.newFixedThreadPool(PATH_ASKS);
    }

    /**
     * Every path alone with no assertion, within
     * {@link #SELF_CHECK_BUDGET_MS}: an unsat one contradicts itself, and is
     * remembered as refuted under every set of assertions.  The answers, in
     * the disjuncts' order.
     */
    List<Z3.Answer> selfCheck() {
        List<String> none = Collections.emptyList();
        List<Future<Z3.Answer>> pending = new ArrayList<Future<Z3.Answer>>();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            String selector = disjunct.selector();
            pending.add(pool.submit(() -> solver.ask(
                    composition.pathQuery(selector, none), none, false,
                    SELF_CHECK_BUDGET_MS)));
        }
        List<Z3.Answer> answers = new ArrayList<Z3.Answer>();
        for (int at = 0; at < pending.size(); at++) {
            Z3.Answer answer = get(pending.get(at));
            answers.add(answer);
            if (answer.unsat()) {
                remember(composition.disjuncts().get(at).selector(),
                        new HashSet<String>(), answer, true);
            }
        }
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
                        remember(selectors.get(at), under, answer, wantCore);
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

    /** One path alone under {@code assertions}, with the solver's budget,
     *  answered by its refutation where it has one. */
    Z3.Answer askPath(String selector, List<String> assertions,
                      List<String> asked, boolean wantCore) {
        Set<String> under = new HashSet<String>(assertions);
        Z3.Answer known = refutation(selector, under, wantCore);
        if (known != null) return known;
        Z3.Answer answer = solver.ask(composition.pathQuery(selector,
                assertions), asked, wantCore);
        if (answer.unsat()) remember(selector, under, answer, wantCore);
        return answer;
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
                .add(new Refutation(under, answer,
                        coreComplete || under.isEmpty()));
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
