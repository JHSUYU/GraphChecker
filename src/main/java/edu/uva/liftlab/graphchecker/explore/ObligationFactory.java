package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Z3;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The obligations of one task, and the solving of one of them.
 *
 * <p>An obligation is the path <em>as its replay ran it</em> -- every prefix
 * decision in the arm it took -- with exactly one decision negated.  Nothing
 * else is asked for: not the fatal predicate (that is the composition's
 * question), not another region's path (that region is its own task).</p>
 *
 * <p>Planning and solving are separate on purpose, and the campaign runs them
 * in separate processes: one JVM plans a wave ({@link ExploreMain}) and one
 * worker per obligation solves and replays it
 * ({@link ObligationSolverMain}).  A solve is what an obligation costs before
 * any replay runs, and a wave's queries are independent -- each is one path
 * with one decision negated over a corpus nobody writes to while the wave is
 * open.</p>
 */
public final class ObligationFactory {
    /** How many recorded paths of one task a wave proposes flips from. */
    public static final int DEFAULT_MAX_PATHS_PER_TASK = 32;
    /** How many flips one path may offer in one wave. */
    public static final int DEFAULT_MAX_FLIPS_PER_PATH = 32;

    private ObligationFactory() {
    }

    /** What a wave may propose per task. */
    public static final class Bounds {
        public final int maxPathsPerTask;
        public final int maxFlipsPerPath;

        public Bounds(int maxPathsPerTask, int maxFlipsPerPath) {
            this.maxPathsPerTask = maxPathsPerTask <= 0
                    ? DEFAULT_MAX_PATHS_PER_TASK : maxPathsPerTask;
            this.maxFlipsPerPath = maxFlipsPerPath <= 0
                    ? DEFAULT_MAX_FLIPS_PER_PATH : maxFlipsPerPath;
        }

        public static Bounds defaults() {
            return new Bounds(DEFAULT_MAX_PATHS_PER_TASK,
                    DEFAULT_MAX_FLIPS_PER_PATH);
        }
    }

    /** One flip a wave proposes: the path, the decision, and its identity. */
    public static final class Candidate {
        public final String obligationId;
        public final Task task;
        public final Corpus.RecordedPath path;
        public final int index;
        public final DecisionRow decision;

        private Candidate(Task task, Corpus.RecordedPath path, int index) {
            this.task = task;
            this.path = path;
            this.index = index;
            this.decision = path.decisions.get(index);
            this.obligationId = obligationId(task.taskId(),
                    decision.siteId(), decision.ordinal(),
                    !decision.outcome());
        }

        /**
         * The row a wave publishes: what to flip, with no model yet.
         *
         * <p>The assignments are the solver's answer, not the planner's; a
         * wave says which flips are worth a query, and the worker that solves
         * one writes the values its replay is to apply.</p>
         */
        public Obligation proposal() {
            return Obligation.of(obligationId, task.taskId(), path.pathId,
                    decision.siteId(), decision.ordinal(),
                    !decision.outcome(),
                    Collections.<String, String>emptyMap(),
                    Collections.<String, String>emptyMap(),
                    Collections.<String>emptyList());
        }
    }

    /** One obligation solved: the query, the verdict, and what to apply. */
    public static final class Outcome {
        public final String obligationId;
        public final String taskId;
        /** Null unless the query is satisfiable and the flip can be run. */
        public final Obligation obligation;
        public final ObligationResult result;
        public final String smt2;
        /**
         * root id -> the skew the model asks of that clock, as a decimal.
         *
         * <p>{@code model - recordedValue}: a clock is the one root every
         * execution reads differently, so the counterfactual an obligation
         * states about one is how far off the reading is, and the replay
         * adds it to the instant it reads for itself.</p>
         */
        public final Map<String, String> clockDeltas;
        public final List<GapRow> gaps;

        private Outcome(String obligationId, String taskId,
                        Obligation obligation, ObligationResult result,
                        String smt2, Map<String, String> clockDeltas,
                        List<GapRow> gaps) {
            this.obligationId = obligationId;
            this.taskId = taskId;
            this.obligation = obligation;
            this.result = result;
            this.smt2 = smt2;
            this.clockDeltas = Collections.unmodifiableMap(clockDeltas);
            this.gaps = Collections.unmodifiableList(gaps);
        }

        public boolean issued() {
            return obligation != null;
        }

        public Verdict verdict() {
            return result.verdict();
        }
    }

    /** No clock was moved, which is every outcome but a satisfied one. */
    private static final Map<String, String> NO_SKEW =
            Collections.<String, String>emptyMap();

    /** {@code model - recorded} as a decimal, or "" if either is not one. */
    private static String skew(String model, String recorded) {
        if (model == null || recorded == null) return "";
        try {
            return new java.math.BigInteger(model.trim())
                    .subtract(new java.math.BigInteger(recorded.trim()))
                    .toString();
        } catch (NumberFormatException notAnInstant) {
            return "";
        }
    }

    /**
     * One obligation's id: the PLANNED OCCURRENCE and the arm it asks for.
     *
     * <p>The task is the occurrence ({@link ClosurePlanner#taskId}), so this
     * key is a fact about the occurrence and not about a session.  The
     * {@code pathId} was in here, and every session mints its own
     * ({@link Corpus#pathId}), so one arm had as many ids as there were
     * sessions that ran the occurrence -- 30 owed arms of the 11741 corpus
     * came back as 706 obligations on wave 1 because the answers to them
     * were filed under the seed's path.  The obligation ROW still carries a
     * {@code pathId}: the prefix a flip is cut from is what the query is
     * built over, and the composition reads it.  Only the IDENTITY drops the
     * session (see {@link Frontier}).</p>
     */
    public static String obligationId(String taskId, String siteId,
                                      int ordinal, boolean flippedOutcome) {
        return ArtifactIO.digest(taskId + "|" + siteId + "|" + ordinal + "|"
                + flippedOutcome, 16);
    }

    /**
     * The flips one task offers, naming every candidate the corpus has
     * already answered.
     *
     * <p>CLOSURE-V2 SS3: a candidate is a symbolic decision of a closure
     * member AT A SITE THE CLOSURE DEMANDED IT FOR -- the target's guards for
     * the anchor, a writer's or a producer's own guards for a writer or a
     * producer.  E7's rule was every symbolic decision of every instrumented
     * occurrence, which spent a wave on branches no value the target read
     * rests on: on the P2f' three-session corpus that was 45 candidates where
     * the closure demands two.  The guard set comes from the wave's closure
     * plan, which took it from the epoch's static map, so "why is this
     * occurrence a task" and "which of its branches may be flipped" are one
     * answer.</p>
     *
     * @param flipSites the site ids this task's demand names; a task with
     *                  none offers no flip, and null is the same as none
     * @param owed the ONE ledger of what is still owed ({@link Frontier}):
     *             an arm some session recorded, or some wave answered, is
     *             settled and is never proposed again
     * @param gaps where a settled candidate is recorded, so a reader can see
     *             that the wave shrank because the corpus grew
     */
    public static List<Candidate> candidates(Corpus corpus, Task task,
                                             Set<String> flipSites,
                                             Bounds bounds, Frontier owed,
                                             List<GapRow> gaps) {
        List<Candidate> candidates = new ArrayList<Candidate>();
        Set<String> offered = new LinkedHashSet<String>();
        int paths = 0;
        for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
            if (paths++ >= bounds.maxPathsPerTask) break;
            int flips = 0;
            for (int index = 0; index < path.decisions.size()
                    && flips < bounds.maxFlipsPerPath; index++) {
                DecisionRow decision = path.decisions.get(index);
                if (!FlipQuery.flippable(corpus, path.sessionId, decision)) {
                    continue;
                }
                if (flipSites == null
                        || !flipSites.contains(decision.siteId())) {
                    continue;
                }
                Candidate candidate = new Candidate(task, path, index);
                // A second path of the same occurrence offering the same arm
                // is the same obligation, not another one: one witness of an
                // owed fact is enough, and it costs neither a gap row nor a
                // flip of the budget.  The first path in corpus order is the
                // prefix the query is built over.
                if (!offered.add(candidate.obligationId)) continue;
                String reason = owed.settled(candidate.obligationId);
                if (!reason.isEmpty()) {
                    gaps.add(GapRow.of(path.sessionId,
                            GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                            decision.siteId() + "#" + decision.ordinal()
                                    + " -> " + !decision.outcome(), reason));
                    continue;
                }
                candidates.add(candidate);
                flips++;
            }
        }
        return candidates;
    }

    /**
     * Why this model is the recording's own valuation, or {@code ""}.
     *
     * <p>Every root the model assigns carries the value that session's
     * {@code RootMintRow} recorded, and no handoff is answered: nothing about
     * the world this obligation asks for differs from the one already on
     * disk.  A model that assigns NO root is not this case -- a clock-driven
     * flip states its skew elsewhere -- so the test is over the roots the
     * query actually bound.</p>
     */
    private static String recordedValuation(Corpus corpus, Candidate candidate,
                                            Map<String, String> roots,
                                            Map<String, String> answers) {
        if (roots.isEmpty() || !answers.isEmpty()) return "";
        List<String> same = new ArrayList<String>();
        for (Map.Entry<String, String> assignment : roots.entrySet()) {
            String reading = corpus.rootValue(candidate.path.sessionId,
                    assignment.getKey());
            if (reading.isEmpty()
                    || !reading.equals(assignment.getValue())) {
                return "";
            }
            same.add(assignment.getKey() + "=" + reading);
        }
        return "the model is the recording's own valuation ("
                + String.join(", ", same) + ") and answers no handoff, so "
                + "the replay it asks for is the seed replay: this is not an "
                + "arm the seed lacks. Either the flipped decision's recorded "
                + "polarity disagrees with the root value the same session "
                + "minted -- DecisionRow.outcome must say whether the "
                + "published term HELD (CONTRACT-SPEC SS2) -- or the query "
                + "binds a root the flip does not depend on";
    }

    /**
     * Finds the flip one published obligation names.
     *
     * <p>The worker that solves an obligation is handed the row and the
     * sessions, and nothing else: a task is its focused occurrence's id and a
     * path is a session and an occurrence, so both are recoverable from the
     * corpus rather than carried in a second file that could disagree.</p>
     */
    public static Candidate locate(Corpus corpus, Obligation obligation) {
        Task task = ClosurePlanner.taskOf(corpus, obligation.taskId());
        if (task == null) return null;
        for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
            if (!path.pathId.equals(obligation.pathId())) continue;
            for (int index = 0; index < path.decisions.size(); index++) {
                DecisionRow decision = path.decisions.get(index);
                if (decision.siteId().equals(obligation.siteId())
                        && decision.ordinal() == obligation.ordinal()) {
                    return new Candidate(task, path, index);
                }
            }
        }
        return null;
    }

    /** Solves one candidate: its query, its verdict and its model. */
    public static Outcome solve(Corpus corpus, Candidate candidate, Path z3,
                                long timeoutMillis) {
        String id = candidate.obligationId;
        DecisionRow decision = candidate.decision;
        FlipQuery.Built built = FlipQuery.build(corpus, candidate.task,
                candidate.path, candidate.index);
        List<GapRow> gaps = new ArrayList<GapRow>(built.gaps);
        if (!built.ok()) {
            return new Outcome(id, candidate.task.taskId(), null,
                    ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                            "the query was refused: " + built.refusal),
                    "", NO_SKEW, gaps);
        }
        long budget = timeoutMillis <= 0 ? Z3.DEFAULT_TIMEOUT_MILLIS
                : timeoutMillis;
        Z3 solver = new Z3(z3, budget);
        Z3.Answer answer = solver.ask(built.smt2, built.modelSymbols, false);
        // The query as it was ASKED, for the artifact: the body plus the
        // question the one driver puts to z3.
        String query = Z3.modelQuery(built.smt2, built.modelSymbols);
        if (answer.timedOut()) {
            gaps.add(GapRow.of(candidate.path.sessionId,
                    GapKind.SOLVER_TIMEOUT, GapClass.DIAGNOSTIC, id,
                    "no verdict in " + budget + "ms: the flip is an "
                            + "unexplored sibling, not a closed one"));
            return new Outcome(id, candidate.task.taskId(), null,
                    ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                            "SOLVER_TIMEOUT after " + budget + "ms"),
                    query, NO_SKEW, gaps);
        }
        // An answer that is neither sat nor unsat is not a verdict about the
        // corpus: an "(error ...)" says z3 could not READ the query and an
        // "unknown" says it did not decide, so reading either as UNSAT would
        // publish "no world of this corpus takes the other arm" on the
        // solver's authority.  Refused by name, the way the composer refuses
        // the same two answers.
        if (!answer.decided()) {
            return new Outcome(id, candidate.task.taskId(), null,
                    ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                            "the solver did not decide this flip: "
                                    + answer.status()
                                    + (answer.reason().isEmpty() ? ""
                                    : " " + answer.reason())
                                    + (solver.errors().isEmpty() ? ""
                                    : " " + solver.errors())),
                    query, NO_SKEW, gaps);
        }
        if (!answer.sat()) {
            return new Outcome(id, candidate.task.taskId(), null,
                    ObligationResult.of(id, Verdict.UNSAT, "",
                            "no world of this corpus takes the other arm at "
                                    + decision.siteId() + "#"
                                    + decision.ordinal()),
                    query, NO_SKEW, gaps);
        }
        Map<String, String> roots = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> variable
                : built.rootVariables.entrySet()) {
            String value = answer.values().get(variable.getKey());
            if (value != null) roots.put(variable.getValue(), value);
        }
        // A clock's model is an instant of the window the RECORDING read in,
        // so what the replay is owed is the difference: it reads its own
        // instant and moves it by this much.
        Map<String, String> clockDeltas = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> variable
                : built.clockVariables.entrySet()) {
            String rootId = variable.getValue();
            String delta = skew(answer.values().get(variable.getKey()),
                    corpus.rootValue(candidate.path.sessionId, rootId));
            if (delta.isEmpty()) {
                gaps.add(GapRow.of(candidate.path.sessionId,
                        GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, rootId,
                        "the model moves this clock but the reading it is "
                                + "relative to is not an integer, so the "
                                + "replay is owed no skew and reads its own "
                                + "instant"));
                continue;
            }
            clockDeltas.put(rootId, delta);
        }
        Map<String, String> answers = new LinkedHashMap<String, String>();
        List<String> unproducible = new ArrayList<String>();
        for (FlipQuery.Control control : built.controls) {
            String value = answer.values().get(control.variable);
            if (value != null) answers.put(control.attachEndpointId, value);
            if (control.unproducible) {
                unproducible.add(control.attachEndpointId);
            }
        }
        Obligation solved = Obligation.of(id, candidate.task.taskId(),
                candidate.path.pathId, decision.siteId(), decision.ordinal(),
                !decision.outcome(), roots, answers, unproducible);
        // Exploration exists to collect an arm the seed does NOT have
        // (HANDOVER SS1.5).  A model that hands every root back the value the
        // recording minted, and answers no handoff, asks for the seed replay
        // under another name: whatever it satisfies, it is not a world the
        // corpus lacks, and a replay spent on it would record the rows it
        // already has.  Refused by name rather than run.
        String recorded = recordedValuation(corpus, candidate, roots, answers);
        if (!recorded.isEmpty()) {
            gaps.add(GapRow.of(candidate.path.sessionId,
                    GapKind.ADMISSION_GAP, GapClass.BLOCKING, id, recorded));
            return new Outcome(id, candidate.task.taskId(), null,
                    ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                            recorded), query, NO_SKEW, gaps);
        }
        return new Outcome(id, candidate.task.taskId(), solved,
                ObligationResult.of(id, Verdict.SAT_MODEL_READY, "",
                        "the flip at " + decision.siteId() + "#"
                                + decision.ordinal() + " is reachable under "
                                + roots.size() + " root value(s) and "
                                + answers.size() + " answered handoff(s)"),
                query, clockDeltas, gaps);
    }
}
