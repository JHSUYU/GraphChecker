package edu.uva.liftlab.graphchecker.d3.explore;

import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.Obligation;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.Task;
import edu.uva.liftlab.graphchecker.d3.contract.Verdict;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.function.Predicate;

/**
 * The obligations of one task: one per decision of one admitted path.
 *
 * <p>An obligation is the path <em>as its replay ran it</em> -- every prefix
 * decision in the arm it took -- with exactly one decision negated.  Nothing
 * else is asked for: not the fatal predicate (that is the composition's
 * question), not another region's path (that region is its own task).  The
 * model of that query says what the replay must be handed to take the other
 * arm: a value per root at its mint, and a value per handoff at its attach.
 * A query the solver refuses is closed here and never issued, so a wave costs
 * a replay only for a flip that some world of the corpus supports.</p>
 */
public final class ObligationFactory {
    /** How many obligations one task may open in one wave. */
    public static final int DEFAULT_MAX_PER_TASK = 256;
    /** What one obligation's query may cost. */
    public static final long DEFAULT_TIMEOUT_MILLIS = 20_000L;
    /** How many queries of one task are solved at a time. */
    public static final int DEFAULT_SOLVER_THREADS = 4;

    private final Corpus corpus;
    private final Path z3;
    private final long timeoutMillis;
    private final int maxPerTask;
    private final int threads;

    public ObligationFactory(Corpus corpus, Path z3, long timeoutMillis,
                             int maxPerTask, int threads) {
        this.corpus = corpus;
        this.z3 = z3 == null ? Paths.get("z3") : z3;
        this.timeoutMillis = timeoutMillis <= 0
                ? DEFAULT_TIMEOUT_MILLIS : timeoutMillis;
        this.maxPerTask = maxPerTask <= 0 ? DEFAULT_MAX_PER_TASK : maxPerTask;
        this.threads = threads <= 0 ? DEFAULT_SOLVER_THREADS : threads;
    }

    public ObligationFactory(Corpus corpus, Path z3, long timeoutMillis,
                             int maxPerTask) {
        this(corpus, z3, timeoutMillis, maxPerTask, DEFAULT_SOLVER_THREADS);
    }

    public ObligationFactory(Corpus corpus, Path z3) {
        this(corpus, z3, DEFAULT_TIMEOUT_MILLIS, DEFAULT_MAX_PER_TASK);
    }

    /** One flip, solved: issued to the runtime, closed here, or refused. */
    public static final class Outcome {
        public final String obligationId;
        public final String taskId;
        /** Null unless the query is satisfiable and the flip can be run. */
        public final Obligation obligation;
        /** Null when the obligation is issued; the verdict otherwise. */
        public final ObligationResult result;
        public final String smt2;
        public final List<GapRow> gaps;

        private Outcome(String obligationId, String taskId,
                        Obligation obligation, ObligationResult result,
                        String smt2, List<GapRow> gaps) {
            this.obligationId = obligationId;
            this.taskId = taskId;
            this.obligation = obligation;
            this.result = result;
            this.smt2 = smt2;
            this.gaps = Collections.unmodifiableList(gaps);
        }

        public boolean issued() {
            return obligation != null;
        }
    }

    /** One obligation's id: the task, the path and the decision it flips. */
    public static String obligationId(String taskId, String pathId,
                                      DecisionRow decision) {
        return ExploreIds.sha16(taskId + "|" + pathId + "|"
                + decision.siteId() + "|" + decision.ordinal() + "|"
                + !decision.outcome());
    }

    /**
     * Every obligation this task's paths offer.
     *
     * <p>A path is one recorded run of the FOCUSED occurrence.  The task's
     * factor replays with it -- the writers and readers of one location on
     * one node are one symbolic unit -- but the decisions that are flipped
     * are the focused occurrence's, because an obligation names a site and an
     * ordinal and nothing that would say in which co-occurrence they are.</p>
     */
    public List<Outcome> obligations(Task task) {
        return obligations(task, new Predicate<String>() {
            @Override public boolean test(String obligationId) {
                return false;
            }
        });
    }

    /**
     * @param asked a query already asked in an earlier wave, which is never
     *              solved again: the answer would be the same one, and a
     *              solve is what an obligation costs before any replay runs
     */
    public List<Outcome> obligations(final Task task,
                                     Predicate<String> asked) {
        final List<Corpus.RecordedPath> paths =
                new ArrayList<Corpus.RecordedPath>();
        final List<Integer> indexes = new ArrayList<Integer>();
        for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
            for (int index = 0; index < path.decisions.size()
                    && paths.size() < maxPerTask; index++) {
                DecisionRow decision = path.decisions.get(index);
                if (!FlipQuery.flippable(corpus, path.sessionId, decision)) {
                    continue;
                }
                if (asked.test(obligationId(task.taskId(), path.pathId,
                        decision))) {
                    continue;
                }
                paths.add(path);
                indexes.add(index);
            }
        }
        return solveAll(task, paths, indexes);
    }

    /**
     * Solves one task's candidate flips, several at a time.
     *
     * <p>A solve is what an obligation costs before any replay runs, and the
     * queries of one wave are independent -- each is one path with one
     * decision negated, over a corpus nobody writes to while the wave is
     * planned.  The order of the answers is the order of the candidates, so
     * a wave's file is the same however many threads produced it.</p>
     */
    private List<Outcome> solveAll(final Task task,
                                   final List<Corpus.RecordedPath> paths,
                                   final List<Integer> indexes) {
        List<Outcome> outcomes = new ArrayList<Outcome>();
        if (paths.isEmpty()) return outcomes;
        if (threads <= 1 || paths.size() == 1) {
            for (int candidate = 0; candidate < paths.size(); candidate++) {
                Corpus.RecordedPath path = paths.get(candidate);
                int index = indexes.get(candidate);
                outcomes.add(solve(task, path, index,
                        path.decisions.get(index)));
            }
            return outcomes;
        }
        ExecutorService workers = Executors.newFixedThreadPool(
                Math.min(threads, paths.size()));
        try {
            List<Future<Outcome>> pending = new ArrayList<Future<Outcome>>();
            for (int candidate = 0; candidate < paths.size(); candidate++) {
                final Corpus.RecordedPath path = paths.get(candidate);
                final int index = indexes.get(candidate);
                pending.add(workers.submit(new Callable<Outcome>() {
                    @Override public Outcome call() {
                        return solve(task, path, index,
                                path.decisions.get(index));
                    }
                }));
            }
            for (Future<Outcome> future : pending) {
                try {
                    outcomes.add(future.get());
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                    break;
                } catch (ExecutionException failed) {
                    throw new IllegalStateException(
                            "solving an obligation of task " + task.taskId()
                                    + " failed", failed.getCause());
                }
            }
        } finally {
            workers.shutdownNow();
        }
        return outcomes;
    }

    private Outcome solve(Task task, Corpus.RecordedPath path, int index,
                          DecisionRow decision) {
        String id = obligationId(task.taskId(), path.pathId, decision);
        FlipQuery.Built built = FlipQuery.build(corpus, task, path, index);
        List<GapRow> gaps = new ArrayList<GapRow>(built.gaps);
        if (!built.ok()) {
            return new Outcome(id, task.taskId(), null, null, "", gaps);
        }
        Z3Solver.Answer answer;
        try {
            answer = Z3Solver.solve(z3, built.smt2, timeoutMillis);
        } catch (IOException | InterruptedException failed) {
            if (failed instanceof InterruptedException) {
                Thread.currentThread().interrupt();
            }
            gaps.add(GapRow.of(path.sessionId, GapKind.ADMISSION_GAP,
                    GapClass.DIAGNOSTIC, id,
                    "the solver could not be run: " + failed));
            return new Outcome(id, task.taskId(), null, null, built.smt2,
                    gaps);
        }
        if (answer.timedOut) {
            gaps.add(GapRow.of(path.sessionId, GapKind.ADMISSION_GAP,
                    GapClass.DIAGNOSTIC, id,
                    "SOLVER_TIMEOUT after " + timeoutMillis + "ms: the flip "
                            + "is an unexplored sibling, not a closed one"));
            return new Outcome(id, task.taskId(), null, null, built.smt2,
                    gaps);
        }
        if (!answer.sat) {
            return new Outcome(id, task.taskId(), null,
                    ObligationResult.of(id, Verdict.UNSAT, "",
                            "no world of this corpus takes the other arm at "
                                    + decision.siteId() + "#"
                                    + decision.ordinal()),
                    built.smt2, gaps);
        }
        Map<String, String> roots = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> variable
                : built.rootVariables.entrySet()) {
            String value = answer.model.get(variable.getKey());
            if (value != null) roots.put(variable.getValue(), value);
        }
        Map<String, String> answers = new LinkedHashMap<String, String>();
        List<String> unproducible = new ArrayList<String>();
        for (FlipQuery.Control control : built.controls) {
            String value = answer.model.get(control.variable);
            if (value != null) answers.put(control.attachEndpointId, value);
            if (control.unproducible) {
                unproducible.add(control.attachEndpointId);
            }
        }
        Obligation obligation = Obligation.of(id, task.taskId(), path.pathId,
                decision.siteId(), decision.ordinal(), !decision.outcome(),
                roots, answers, unproducible);
        return new Outcome(id, task.taskId(), obligation, null, built.smt2,
                gaps);
    }
}
