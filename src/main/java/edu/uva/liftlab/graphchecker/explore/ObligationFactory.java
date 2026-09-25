package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.Z3;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;

import java.math.BigInteger;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The obligations of one task, and the solving of one of them.
 *
 * <p>An obligation is the path as its replay ran it with exactly one decision
 * negated; never the fatal predicate (the composition's question) nor another
 * region's path (its own task). Planning ({@link ExploreMain}) and solving
 * ({@link ObligationSolverMain}, one worker per obligation) run in separate
 * processes: a wave's queries are independent.</p>
 */
public final class ObligationFactory {
    /** How many recorded paths of one task a wave proposes flips from. */
    public static final int DEFAULT_MAX_PATHS_PER_TASK = 32;
    /** How many flips one path may offer in one wave. */
    public static final int DEFAULT_MAX_FLIPS_PER_PATH = 32;
    /** The most flips a cut path's world may already hold: the nesting bound.
     *  Each wave nests one more flip, so without it the search grows per world;
     *  the deepest known witness chain is two flips. */
    public static final int DEFAULT_MAX_WORLD_DEPTH = 3;

    private ObligationFactory() {
    }

    /** What a wave may propose per task. */
    public static final class Bounds {
        public final int maxPathsPerTask;
        public final int maxFlipsPerPath;
        /** Most flips a cut path's world may hold; 0 cuts from the seed only.
         */
        public final int maxWorldDepth;

        /** A negative {@code maxWorldDepth} is the default. */
        public Bounds(int maxPathsPerTask, int maxFlipsPerPath,
                      int maxWorldDepth) {
            this.maxPathsPerTask = maxPathsPerTask <= 0
                    ? DEFAULT_MAX_PATHS_PER_TASK : maxPathsPerTask;
            this.maxFlipsPerPath = maxFlipsPerPath <= 0
                    ? DEFAULT_MAX_FLIPS_PER_PATH : maxFlipsPerPath;
            this.maxWorldDepth = maxWorldDepth < 0
                    ? DEFAULT_MAX_WORLD_DEPTH : maxWorldDepth;
        }

        public static Bounds defaults() {
            return new Bounds(DEFAULT_MAX_PATHS_PER_TASK,
                    DEFAULT_MAX_FLIPS_PER_PATH, DEFAULT_MAX_WORLD_DEPTH);
        }
    }

    /** One flip a wave proposes: the path, the decision, and its identity. */
    public static final class Candidate {
        public final String obligationId;
        public final Task task;
        public final Corpus.RecordedPath path;
        public final int index;
        public final DecisionRow decision;

        private Candidate(Corpus corpus, Task task,
                          Corpus.RecordedPath path, int index) {
            this.task = task;
            this.path = path;
            this.index = index;
            this.decision = path.decisions.get(index);
            this.obligationId = obligationId(task.taskId(),
                    decision.siteId(), decision.ordinal(),
                    !decision.outcome(),
                    prefixDigest(path.decisions, index),
                    worldKey(corpus, task, path.sessionId));
        }

        /** The row a wave publishes: what to flip, no model yet (the solver
         *  writes values). */
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
        /** Null unless the query is satisfiable and the flip can be run. */
        public final Obligation obligation;
        public final ObligationResult result;
        public final String smt2;
        /** root id -> clock skew ({@code model - recorded}) as a decimal: every
         *  run reads a clock differently, so the replay adds this to its own
         *  reading. */
        public final Map<String, String> clockDeltas;
        /** root id -> the rendered occurrence the recording mints it at, for
         *  every assigned root. Focused beside the flipped path: a replay
         *  plants only at a FOCUSED mint ({@code
         *  ConcolicRegionRuntime#focusedRootValue}), so an unfocused mint reads
         *  the recorded value. */
        public final Map<String, String> rootMints;
        /** Inherited flips (the parent's own, then its inherited ones), each
         *  with its ORIGINAL obligation id; the replay is held to all ({@code
         *  runtime/FocusedReplay}). */
        public final List<Corpus.Flip> inheritedFlips;
        public final List<GapRow> gaps;

        private Outcome(Obligation obligation, ObligationResult result,
                        String smt2, Map<String, String> clockDeltas,
                        Map<String, String> rootMints,
                        List<Corpus.Flip> inheritedFlips,
                        List<GapRow> gaps) {
            this.obligation = obligation;
            this.result = result;
            this.smt2 = smt2;
            this.clockDeltas = Collections.unmodifiableMap(clockDeltas);
            this.rootMints = Collections.unmodifiableMap(rootMints);
            this.inheritedFlips =
                    Collections.unmodifiableList(inheritedFlips);
            this.gaps = Collections.unmodifiableList(gaps);
        }

        public boolean issued() {
            return obligation != null;
        }
    }

    /** Every outcome but a satisfied one: no obligation to run, nothing to
     *  apply. */
    private static Outcome refused(Candidate candidate, Verdict verdict,
                                   String detail, String query,
                                   List<GapRow> gaps) {
        return new Outcome(null, ObligationResult.of(candidate.obligationId,
                verdict, "", detail), query,
                Collections.<String, String>emptyMap(),
                Collections.<String, String>emptyMap(),
                Collections.<Corpus.Flip>emptyList(), gaps);
    }

    /** {@code model - recorded} as a decimal, or "" if either is not one. */
    private static String skew(String model, String recorded) {
        if (model == null || recorded == null) return "";
        try {
            return new BigInteger(model.trim())
                    .subtract(new BigInteger(recorded.trim()))
                    .toString();
        } catch (NumberFormatException notAnInstant) {
            return "";
        }
    }

    /** One PATH PREFIX digest: decisions {@code [0, uptoExclusive)} as {@code
     *  siteId#ordinal=outcome} joined by {@code /}. Concrete decisions count
     *  (they are path shape); the empty prefix digests the empty string. */
    public static String prefixDigest(List<DecisionRow> decisions,
                                      int uptoExclusive) {
        StringBuilder text = new StringBuilder();
        int bound = decisions == null ? 0
                : Math.min(uptoExclusive, decisions.size());
        for (int index = 0; index < bound; index++) {
            DecisionRow decision = decisions.get(index);
            if (text.length() > 0) text.append('/');
            text.append(decision.siteId()).append('#')
                    .append(decision.ordinal()).append('=')
                    .append(decision.outcome());
        }
        return ArtifactIO.digest(text.toString(), 16);
    }

    /** One WHOLE WORLD digest: all its flips, sorted, so order is irrelevant;
     *  the seed's is {@code ""}. Labels slot and graph rows; arm keys use
     *  {@link #worldKey} instead. */
    public static String worldDigest(Corpus.World world) {
        if (world == null || world.flips.isEmpty()) return "";
        List<String> held = new ArrayList<String>();
        for (Corpus.Flip flip : world.flips) {
            held.add(flip.focusedOccurrenceId + "|" + flip.siteId + "|"
                    + flip.ordinal + "|" + flip.outcome);
        }
        Collections.sort(held);
        return ArtifactIO.digest(String.join("/", held), 16);
    }

    /** THE WORLD PART OF AN ARM'S KEY: what the world delivered to the task
     *  ({@link Corpus#inputShape}), never which flips did it (keying by cause
     *  asks one question once per upstream flip combination). Shared by {@link
     *  Candidate} and {@link Frontier}, which must agree. */
    public static String worldKey(Corpus corpus, Task task,
                                  String sessionId) {
        return corpus.inputShape(sessionId, task.focused(), task.factor());
    }

    /**
     * One obligation's id: planned occurrence ({@link ClosurePlanner#taskId}),
     * {@link #prefixDigest}, {@link #worldKey} and the arm.
     *
     * <p>Never the session: a {@code pathId} in the key gives one arm as many
     * ids as sessions (the row still carries it; the query is built over it).
     * The prefix lets flip chains deepen; the delivered structure keeps a known
     * path under new inputs owed (hdfs-11741: the same expiry compare over four
     * keys instead of five), never the same path under the same inputs.</p>
     */
    public static String obligationId(String taskId, String siteId,
                                      int ordinal, boolean flippedOutcome,
                                      String prefixDigest,
                                      String worldKey) {
        return ArtifactIO.digest(taskId + "|" + siteId + "|" + ordinal + "|"
                + flippedOutcome + "|" + prefixDigest + "|" + worldKey, 16);
    }

    /**
     * The flips one task offers, recording every already-settled candidate.
     *
     * <p>CLOSURE-V2 SS3: only decisions at sites the closure demanded for this
     * member (target guards for the anchor, own guards for a writer/producer).
     * Cut only from ADMITTED sessions' paths: a child inherits the parent's
     * world (R5, R6), and a NOT_ADMITTED replay ran no world. Such sessions
     * still attest arms ({@link Frontier}).</p>
     *
     * @param flipSites site ids this task's demand names; null = none
     * @param owed      the one ledger of owed arms ({@link Frontier})
     * @param gaps      receives settled candidates, so a shrinking wave is
     * explained
     */
    public static List<Candidate> candidates(Corpus corpus, Task task,
                                             Set<String> flipSites,
                                             Bounds bounds, Frontier owed,
                                             List<GapRow> gaps) {
        List<Candidate> candidates = new ArrayList<Candidate>();
        Set<String> offered = new LinkedHashSet<String>();
        int paths = 0;
        int unread = 0;
        int tooDeep = 0;
        for (Corpus.RecordedPath path : smallestWorldFirst(corpus,
                corpus.pathsOf(task.focused()))) {
            // Only admitted sessions are cut from (see above).
            if (!corpus.session(path.sessionId).admitted()) continue;
            // The nesting bound; counted into a gap below.
            if (corpus.world(path.sessionId).flips.size()
                    > bounds.maxWorldDepth) {
                tooDeep++;
                continue;
            }
            // A bound that drops work says so (gap below). Smallest-world-first
            // means the cap keeps the paths closest to the recording.
            if (paths >= bounds.maxPathsPerTask) {
                unread++;
                continue;
            }
            paths++;
            int flips = 0;
            int unflipped = 0;
            // Fault flips first (DESIGN4 SS1.4): cheap, and they grow the
            // graph.
            for (int index : faultFirst(corpus, path)) {
                if (flips >= bounds.maxFlipsPerPath) {
                    unflipped++;
                    continue;
                }
                DecisionRow decision = path.decisions.get(index);
                if (!FlipQuery.flippable(decision)) {
                    continue;
                }
                if (flipSites == null
                        || !flipSites.contains(decision.siteId())) {
                    continue;
                }
                Candidate candidate =
                        new Candidate(corpus, task, path, index);
                // The same arm from another path is the same obligation; the
                // first path (smallest world, fewest inherited constraints) is
                // its prefix.
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
            if (unflipped > 0) {
                gaps.add(GapRow.of(path.sessionId,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        task.taskId() + " max-flips-per-path="
                                + bounds.maxFlipsPerPath,
                        "this path offered more flippable decisions than one "
                                + "wave takes from it: " + unflipped
                                + " decision(s) after the "
                                + bounds.maxFlipsPerPath
                                + " this wave cut, left unasked"));
            }
        }
        if (tooDeep > 0) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    task.taskId() + " max-world-depth="
                            + bounds.maxWorldDepth,
                    tooDeep + " cuttable path(s) of this task stand in a "
                            + "world of more than " + bounds.maxWorldDepth
                            + " flip(s), and no wave nests deeper: none of "
                            + "them was cut from"));
        }
        if (unread > 0) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    task.taskId() + " max-paths-per-region="
                            + bounds.maxPathsPerTask,
                    "this task has " + (paths + unread) + " cuttable "
                            + "recorded path(s) and this wave planned from "
                            + paths + ": " + unread + " path(s), the "
                            + "ones carrying the largest worlds, were not "
                            + "read at all"));
        }
        return candidates;
    }

    /** The decision indexes of one path, its fault decisions first. */
    private static List<Integer> faultFirst(Corpus corpus,
                                            Corpus.RecordedPath path) {
        List<Integer> faults = new ArrayList<Integer>();
        List<Integer> others = new ArrayList<Integer>();
        for (int index = 0; index < path.decisions.size(); index++) {
            (corpus.fault(path.sessionId, path.decisions.get(index))
                    ? faults : others).add(index);
        }
        faults.addAll(others);
        return faults;
    }

    /** Paths of one occurrence, SMALLEST WORLD FIRST (stable). A candidate
     *  inherits its path's whole world, so the representative of an arm is the
     *  path with the fewest flips: same question, fewest constraints. The seed
     *  is first. */
    private static List<Corpus.RecordedPath> smallestWorldFirst(
            final Corpus corpus, List<Corpus.RecordedPath> paths) {
        List<Corpus.RecordedPath> ordered =
                new ArrayList<Corpus.RecordedPath>(paths);
        ordered.sort(Comparator.comparingInt(
                path -> corpus.world(path.sessionId).flips.size()));
        return ordered;
    }

    /** Why this model is the recording's own valuation, or "": every assigned
     *  root equals its recorded mint value and no handoff is answered. A moved
     *  clock is a counterfactual of its own and is checked FIRST (a pinned root
     *  beside moved clocks is not the seed replay). */
    private static String recordedValuation(Corpus corpus, Candidate candidate,
                                            Map<String, String> roots,
                                            Map<String, String> answers,
                                            Map<String, String> clockDeltas) {
        if (movesAClock(clockDeltas)) return "";
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

    /** Whether any clock skew is non-zero; a non-integer delta counts as no
     *  movement. */
    private static boolean movesAClock(Map<String, String> clockDeltas) {
        if (clockDeltas == null) return false;
        for (String delta : clockDeltas.values()) {
            if (delta == null || delta.trim().isEmpty()) continue;
            try {
                if (new BigInteger(delta.trim()).signum() != 0) {
                    return true;
                }
            } catch (NumberFormatException notAnInstant) {
                continue;
            }
        }
        return false;
    }

    /** Finds the flip one published obligation names, from the corpus alone. */
    public static Candidate locate(Corpus corpus, Obligation obligation) {
        Task task = ClosurePlanner.taskOf(corpus, obligation.taskId());
        if (task == null) return null;
        for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
            if (!path.pathId.equals(obligation.pathId())) continue;
            for (int index = 0; index < path.decisions.size(); index++) {
                DecisionRow decision = path.decisions.get(index);
                if (decision.siteId().equals(obligation.siteId())
                        && decision.ordinal() == obligation.ordinal()) {
                    return new Candidate(corpus, task, path, index);
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
            return refused(candidate, Verdict.NOT_ADMITTED,
                    "the query was refused: " + built.refusal, "", gaps);
        }
        long budget = timeoutMillis <= 0 ? Z3.DEFAULT_TIMEOUT_MILLIS
                : timeoutMillis;
        Z3 solver = new Z3(z3, budget);
        Z3.Answer answer = solver.ask(built.smt2, built.modelSymbols, false);
        // The query as asked (body plus the driver's question), for the
        // artifact.
        String query = Z3.modelQuery(built.smt2, built.modelSymbols);
        if (answer.timedOut()) {
            gaps.add(GapRow.of(candidate.path.sessionId,
                    GapKind.SOLVER_TIMEOUT, GapClass.DIAGNOSTIC, id,
                    "no verdict in " + budget + "ms: the flip is an "
                            + "unexplored sibling, not a closed one"));
            return refused(candidate, Verdict.NOT_ADMITTED,
                    "SOLVER_TIMEOUT after " + budget + "ms", query, gaps);
        }
        // Neither sat nor unsat (error/unknown) is no verdict: refused by name,
        // never read as UNSAT.
        if (!answer.decided()) {
            return refused(candidate, Verdict.NOT_ADMITTED,
                    "the solver did not decide this flip: " + answer.status()
                            + (answer.reason().isEmpty() ? ""
                            : " " + answer.reason())
                            + (solver.errors().isEmpty() ? ""
                            : " " + solver.errors()), query, gaps);
        }
        if (!answer.sat()) {
            return refused(candidate, Verdict.UNSAT,
                    "no world of this corpus takes the other arm at "
                            + decision.siteId() + "#" + decision.ordinal(),
                    query, gaps);
        }
        Map<String, String> roots = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> variable
                : built.rootVariables.entrySet()) {
            String value = answer.values().get(variable.getKey());
            if (value != null) roots.put(variable.getValue(), value);
        }
        // A clock's model is an instant of the recording's window; the replay
        // is owed the difference.
        Map<String, String> clockDeltas = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> variable
                : built.clockVariables.entrySet()) {
            String rootId = variable.getValue();
            String recorded = corpus.rootValue(candidate.path.sessionId,
                    rootId);
            String delta = skew(answer.values().get(variable.getKey()),
                    recorded);
            if (delta.isEmpty()) {
                gaps.add(GapRow.of(candidate.path.sessionId,
                        GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, rootId,
                        "the model moves this clock but the reading it is "
                                + "relative to is not an integer, so the "
                                + "replay is owed no skew and reads its own "
                                + "instant"));
                continue;
            }
            // Fail closed: a skew or instant outside a Java long can never be
            // applied (clockDomain's ceiling should make this unreachable).
            BigInteger skewed = new BigInteger(delta);
            BigInteger instant =
                    skewed.add(new BigInteger(recorded.trim()));
            if (!JavaPrimitiveSmtSemantics.fitsJavaLong(skewed)
                    || !JavaPrimitiveSmtSemantics.fitsJavaLong(instant)) {
                gaps.add(GapRow.of(candidate.path.sessionId,
                        GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, rootId,
                        "the model asks clock root " + rootId + " for "
                                + "instant " + instant + ", a skew of "
                                + skewed + " on the " + recorded.trim()
                                + " this replay read, and a clock is a "
                                + "millisecond count in a Java long: no "
                                + "replay could apply it"));
                return refused(candidate, Verdict.NOT_ADMITTED,
                        "clock root " + rootId + " is owed a skew of "
                                + skewed + ", which is not a Java long, so "
                                + "the obligation states a world no replay "
                                + "can run", query, gaps);
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
        // A model equal to the recording's valuation asks for the seed replay
        // (HANDOVER SS1.5: exploration collects arms the seed lacks): refused.
        // DIAGNOSTIC under EXPLORATION, never BLOCKING in the recording's
        // ledger. Asked of the model's own skews/roots/answers, before
        // inheriting the parent's world (merged values would fake a
        // counterfactual).
        String recorded = recordedValuation(corpus, candidate, roots, answers,
                clockDeltas);
        if (!recorded.isEmpty()) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, id,
                    recorded));
            return refused(candidate, Verdict.NOT_ADMITTED, recorded, query,
                    gaps);
        }
        // The world this flip extends ({@link Corpus.World}): the parent's
        // values are the floor, the model overlays them (model wins), and the
        // parent's flips travel whole (enforced by FocusedReplay, asserted by
        // FlipQuery).
        Corpus.World inherited = corpus.world(candidate.path.sessionId);
        roots = overlay(inherited.rootAssignments, roots);
        clockDeltas = overlay(inherited.clockDeltas, clockDeltas);
        answers = overlay(inherited.answers, answers);
        Obligation solved = Obligation.of(id, candidate.task.taskId(),
                candidate.path.pathId, decision.siteId(), decision.ordinal(),
                !decision.outcome(), roots, answers, unproducible);
        // The focused set: each assigned root's mint occurrence, as the
        // RECORDING states it (the run every address is written about). A root
        // the recording mints nowhere cannot be planted: refused by name.
        Map<String, String> mints = new LinkedHashMap<String, String>();
        Set<String> assigned = new LinkedHashSet<String>(roots.keySet());
        assigned.addAll(clockDeltas.keySet());
        List<String> unmintable = new ArrayList<String>();
        for (String rootId : assigned) {
            RootMintRow mint = corpus.rootOf(corpus.seedSessionId(), rootId);
            if (mint == null) {
                unmintable.add(rootId);
                gaps.add(GapRow.of(candidate.path.sessionId,
                        GapKind.ASSIGNMENT_UNMINTABLE, GapClass.DIAGNOSTIC,
                        id, rootId));
                continue;
            }
            mints.put(rootId, mint.occurrence().render());
        }
        if (!unmintable.isEmpty()) {
            return refused(candidate, Verdict.NOT_ADMITTED,
                    "ASSIGNMENT_UNMINTABLE: the model assigns "
                            + String.join(", ", unmintable)
                            + ", which the recording "
                            + corpus.seedSessionId()
                            + " mints nowhere, so no occurrence of a "
                            + "replay can be focused to plant it", query,
                    gaps);
        }
        return new Outcome(solved, ObligationResult.of(id,
                Verdict.SAT_MODEL_READY, "", "the flip at "
                        + decision.siteId() + "#" + decision.ordinal()
                        + " is reachable under " + roots.size()
                        + " root value(s) and " + answers.size()
                        + " answered handoff(s), planted at " + mints.size()
                        + " mint(s)"),
                query, clockDeltas, mints, inherited.flips, gaps);
    }

    /** {@code base} with {@code over} laid on top: {@code over} wins. */
    private static Map<String, String> overlay(Map<String, String> base,
                                               Map<String, String> over) {
        Map<String, String> merged = new LinkedHashMap<String, String>(base);
        merged.putAll(over);
        return merged;
    }
}
