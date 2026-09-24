package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.Z3;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.ReadsFrom;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;

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
    /**
     * How many flips the world of a path a wave cuts from may already hold.
     *
     * <p>THE NESTING BOUND, the net the search's own accounting allows: the
     * regions, their identities, the loop ordinals and the symbolized roots
     * are finite by construction, but a world is a set of flips and each
     * wave nests one more -- hdfs-11741 asked 30, 260 and 337 obligations in
     * its first three waves over 44 distinct arms, one arm up to 55 times
     * over the worlds that reach it.  Its witness chain is two flips deep (a
     * dn1 drop cut from a world holding nn0's rotation drop), and every
     * other case's exploration closes by itself before a fourth flip: their
     * waves cut from worlds of at most three.  So three.</p>
     */
    public static final int DEFAULT_MAX_WORLD_DEPTH = 3;

    private ObligationFactory() {
    }

    /** What a wave may propose per task. */
    public static final class Bounds {
        public final int maxPathsPerTask;
        public final int maxFlipsPerPath;
        /**
         * The most flips a cut path's world may hold; 0 cuts from the seed
         * alone ({@link #DEFAULT_MAX_WORLD_DEPTH}).
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
        /**
         * root id -> the OCCURRENCE the recording mints that root at,
         * rendered, for every root this model assigns.
         *
         * <p>THE FOCUSED SET is the flipped path's occurrence, its factor
         * members and these: a replay plants an assignment AT THE MINT
         * ({@code ConcolicRegionRuntime#focusedRootValue}, which asks only
         * on a focused occurrence), so a mint that runs unfocused reads the
         * recording's value under an obligation asking for another one.
         * 31 of the 80 focus rows the 11741 campaign #2 wrote assign {@code
         * HDFS.BLOCK_KEY.SERIAL_NO} while their focused set is entirely on
         * {@code hdfs-11741/balancer#epoch0} or a DataNode, and the mint is
         * nn0's {@code REGION.aaa1cfd7} ({@code updateKeys}): every one of
         * them ran the recorded 182907, and the composer refusing "the mint
         * states 182907 and the obligation assigns 182910" was the second
         * statement of that, not the first.</p>
         */
        public final Map<String, String> rootMints;
        /**
         * The flips this replay inherits: the parent's own and its
         * inherited ones, in that order.
         *
         * <p>The world a cut path ran in is not a fact the child can drop
         * ({@link Corpus.World}).  The replay is held to every one of them
         * ({@code runtime/FocusedReplay}), and the chain carries each
         * flip's ORIGINAL obligation id so a report can name which
         * obligation first asked for it.</p>
         */
        public final List<Corpus.Flip> inheritedFlips;
        /**
         * The versions this world chose ({@link #versions}): the replay
         * holds each read to its writer, and a choice it cannot realize
         * is unreachable.
         */
        public final List<ReadsFrom> versions;
        public final List<GapRow> gaps;

        private Outcome(String obligationId, String taskId,
                        Obligation obligation, ObligationResult result,
                        String smt2, Map<String, String> clockDeltas,
                        Map<String, String> rootMints,
                        List<Corpus.Flip> inheritedFlips,
                        List<ReadsFrom> versions, List<GapRow> gaps) {
            this.obligationId = obligationId;
            this.taskId = taskId;
            this.obligation = obligation;
            this.result = result;
            this.smt2 = smt2;
            this.clockDeltas = Collections.unmodifiableMap(clockDeltas);
            this.rootMints = Collections.unmodifiableMap(rootMints);
            this.inheritedFlips =
                    Collections.unmodifiableList(inheritedFlips);
            this.versions = Collections.unmodifiableList(versions);
            this.gaps = Collections.unmodifiableList(gaps);
        }

        /**
         * An outcome that issues no obligation: nothing is planted, no clock
         * is moved, no world is extended and no version is chosen.
         */
        static Outcome refused(String obligationId, String taskId,
                               ObligationResult result, String smt2,
                               List<GapRow> gaps) {
            return new Outcome(obligationId, taskId, null, result, smt2,
                    Collections.<String, String>emptyMap(),
                    Collections.<String, String>emptyMap(),
                    Collections.<Corpus.Flip>emptyList(),
                    Collections.<ReadsFrom>emptyList(), gaps);
        }

        public boolean issued() {
            return obligation != null;
        }

        public Verdict verdict() {
            return result.verdict();
        }
    }

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
     * One PATH PREFIX, as an obligation's identity spells it.
     *
     * <p>The decisions {@code [0, uptoExclusive)} of the path, in list
     * order, each written {@code siteId#ordinal=outcome} and joined by
     * {@code /}.  A CONCRETE decision -- one the recording published with no
     * term -- is in it: it is part of the path's SHAPE, and two runs of one
     * occurrence that differ only in a concrete branch are two local paths,
     * not one.  An empty prefix digests the empty string, so the first
     * decision of every path has one id whichever path it was cut from.</p>
     */
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

    /**
     * One WHOLE WORLD, digested: every flip the session was held to.
     *
     * <p>The flips -- its own and every one it inherited -- each written
     * {@code focusedOccurrenceId|siteId|ordinal|outcome} and sorted, so
     * the same set of flips digests the same however a focus row happened
     * to order them.  The SEED's world is empty and digests to {@code ""}.
     * This is the SPELLING of a world, which the slot table and the wave
     * graph label rows with; an arm is keyed by what the world delivered to
     * it ({@link #worldKey}).</p>
     */
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

    /**
     * THE WORLD PART OF ONE ARM'S KEY: what the session's world delivered
     * to the task ({@link Corpus#inputShape}), never which flips did it.
     *
     * <p>A world that changed nothing the task received digests as the seed
     * does, and two worlds that delivered it the same structure are one
     * world here: the question an arm asks is about the task's own inputs,
     * and the replay that answers it inherits the world of the path it is
     * cut from anyway ({@link #smallestWorldFirst}).  It used to be the
     * world's flips on the task's upstream set, over the corpus's causal
     * graph -- a key by CAUSE, which asked one question once per
     * combination of upstream flips that delivered the same structure.</p>
     *
     * <p>The ONE answer for both readers of it: the candidate a wave cuts
     * ({@link Candidate}) and the ledger of what is owed
     * ({@link Frontier}), which have to agree or an arm is proposed under
     * a key the recording settled under another.</p>
     */
    public static String worldKey(Corpus corpus, Task task,
                                  String sessionId) {
        if (corpus == null || task == null) return "";
        return corpus.inputShape(sessionId, task.focused(), task.factor());
    }

    /**
     * One obligation's id: the PLANNED OCCURRENCE, the PREFIX it is cut
     * under, the WORLD it is cut in, and the arm it asks for.
     *
     * <p>The task is the occurrence ({@link ClosurePlanner#taskId}), so this
     * key is a fact about the occurrence and not about a session.  The
     * {@code pathId} was in here, and every session mints its own
     * ({@link Corpus#pathId}), so one arm had as many ids as there were
     * sessions that ran the occurrence -- 30 owed arms of the 11741 corpus
     * came back as 706 obligations on wave 1 because the answers to them
     * were filed under the seed's path.  The obligation ROW still carries a
     * {@code pathId}: the prefix a flip is cut from is what the query is
     * built over, and the composition reads it.  The IDENTITY drops the
     * session and keeps the prefix ({@link #prefixDigest}).</p>
     *
     * <p>THE PREFIX IS PART OF THE KEY, and it is what lets a chain of
     * flips deepen.  An arm recorded under one prefix of an occurrence says
     * nothing about the same arm under another: an unexplored local path of
     * a known region is still work, and a wave that finds no NEW EDGE is
     * not the end of the exploration.</p>
     *
     * <p>SO IS WHAT THE WORLD DELIVERED TO THE TASK ({@link #worldKey}): an
     * unexplored local path of a known region is still work, and so is a
     * known local path under inputs of another structure -- never the same
     * path under the same inputs.  HDFS-11741 is the case.  dn1's expiry
     * scan runs over the DataNode's own old map before the put loop, so its
     * local prefix is letter for letter the same in the seed, in the session
     * that flipped dn1 alone, and in the session where nn0's second rotation
     * dropped the key; keyed by the prefix alone the first of those settles
     * the arm for every world, and the witness's second flip -- that same
     * compare, over the map addKeys filled with four keys instead of five --
     * is never proposed.  Keyed by every world's flips it would be proposed
     * once per world instead, and keyed by the flips that reach the task,
     * once per combination of them that delivered the same four keys.</p>
     */
    public static String obligationId(String taskId, String siteId,
                                      int ordinal, boolean flippedOutcome,
                                      String prefixDigest,
                                      String worldKey) {
        return ArtifactIO.digest(taskId + "|" + siteId + "|" + ordinal + "|"
                + flippedOutcome + "|"
                + (prefixDigest == null ? "" : prefixDigest) + "|"
                + (worldKey == null ? "" : worldKey), 16);
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
     * <p>WHICH PATHS A WAVE MAY CUT FROM: the SEED's, and the paths of a
     * FOCUSED session every {@code ObligationResult} of whose own {@code
     * obligations.jsonl} states {@link Verdict#ADMITTED}.  A candidate cut
     * from a path INHERITS that session's world -- its root assignments,
     * its clock skews, its answers and the flips it enforced (R5, R6) -- and
     * a world is only a world if the replay that ran it was admitted: a
     * NOT_ADMITTED session's path is a prefix its own replay did not
     * reproduce, so a child of it would be asked to extend a world nothing
     * ran.  Such a session's rows still ATTEST the arms they hold
     * ({@link Frontier} spans every session of the epoch); they are only
     * not cut from.  No gap row: a wave that does not cut from a refused
     * replay is the rule working, not a question the corpus could not
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
        int unread = 0;
        int cappedPaths = 0;
        int tooDeep = 0;
        for (Corpus.RecordedPath path : smallestWorldFirst(corpus,
                corpus.pathsOf(task.focused()))) {
            // Only an ADMITTED session's path is cut from: a NOT_ADMITTED
            // replay's path is a prefix its own run did not reproduce, and
            // a child of it would extend a world nothing ran.  Its rows
            // still attest the arms they hold ({@link Frontier}).
            if (!corpus.session(path.sessionId).admitted()) continue;
            // THE NESTING BOUND ({@link #DEFAULT_MAX_WORLD_DEPTH}): a world
            // already this deep is not cut from, and the gap below says how
            // many paths that left unread.
            if (corpus.world(path.sessionId).flips.size()
                    > bounds.maxWorldDepth) {
                tooDeep++;
                continue;
            }
            // A BOUND THAT DROPS WORK SAYS SO.  This used to be a bare
            // `break`: of hdfs-11741 campaign #6's 137 cuttable paths at one
            // task, 32 were planned and 105 were discarded in silence -- no
            // log line, no gap row, nothing a reader of the manifest could
            // tell apart from "the corpus offered 32".  Two (task, arm)
            // pairs of that run went missing this way and it took an
            // offline re-plan with the bound lifted to find out why.
            // The paths are ordered smallest-world-first, so what a cap
            // keeps is the closest to the recording and not an arbitrary
            // prefix -- which is worth stating too, because it is the
            // reason the cap is survivable at all.
            if (paths >= bounds.maxPathsPerTask) {
                unread++;
                continue;
            }
            paths++;
            cappedPaths++;
            int flips = 0;
            int unflipped = 0;
            // FAULT FLIPS FIRST (DESIGN4 SS1.4): the query is cheap and the
            // world a fault opens is the one that grows the graph, so the
            // budget and the wave's order both take them before the rest.
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
                // A second path of the same occurrence offering the same arm
                // is the same obligation, not another one: one witness of an
                // owed fact is enough, and it costs neither a gap row nor a
                // flip of the budget.  The first path of the SMALLEST world
                // that offers it is the prefix the query is built over
                // ({@link #smallestWorldFirst}): the replay inherits the
                // world of the path it is cut from, and a flip that is not
                // part of this arm's key is a constraint it does not need.
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
                    "this task has " + (cappedPaths + unread) + " cuttable "
                            + "recorded path(s) and this wave planned from "
                            + cappedPaths + ": " + unread + " path(s), the "
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

    /**
     * The paths of one occurrence, SMALLEST WORLD FIRST.
     *
     * <p>Two paths that offer the same arm offer the same obligation, and
     * the first one in this order is the prefix the query is built over.
     * A candidate INHERITS the world of the path it is cut from -- every
     * flip of it, though the arm's key names only what the world delivered
     * to the task ({@link #worldKey}) -- and the replay is held to all of
     * them, so the
     * representative is the path whose world holds the fewest: the same
     * question, asked with the fewest constraints on the run that answers
     * it.  Corpus order decides between worlds of one size, as it did
     * before, and the seed's world is empty and therefore first.</p>
     */
    private static List<Corpus.RecordedPath> smallestWorldFirst(
            final Corpus corpus, List<Corpus.RecordedPath> paths) {
        List<Corpus.RecordedPath> ordered =
                new ArrayList<Corpus.RecordedPath>(paths);
        // Stable: paths of equally sized worlds keep the corpus's own order.
        Collections.sort(ordered, new Comparator<Corpus.RecordedPath>() {
            @Override
            public int compare(Corpus.RecordedPath left,
                               Corpus.RecordedPath right) {
                return corpus.world(left.sessionId).flips.size()
                        - corpus.world(right.sessionId).flips.size();
            }
        });
        return ordered;
    }

    /**
     * Why this model is the recording's own valuation, or {@code ""}.
     *
     * <p>Every root the model assigns carries the value that session's
     * {@code RootMintRow} recorded, and no handoff is answered: nothing about
     * the world this obligation asks for differs from the one already on
     * disk.  A model that assigns NO root is not this case -- a clock-driven
     * flip states its skew elsewhere -- so the test is over the roots the
     * query actually bound.  AND A CLOCK SKEW IS A COUNTERFACTUAL OF ITS
     * OWN: a model that moves any clock asks for a world no execution of
     * this recording ran, whatever the other roots say, so the skew is
     * asked FIRST and a moved clock answers the question before the root
     * comparison is reached.  nn0's second-rotation {@code
     * removeExpiredKeys#u15} flips were refused as "the seed replay under
     * another name" while the same model moved two CLOCK variables, only
     * because the query also reached a pinned integral root
     * ({@code HDFS.BLOCK_KEY.SERIAL_NO}) and kept it where the recording
     * minted it -- which is what a pinned root DOES.</p>
     */
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

    /**
     * Whether this model asks any clock to read somewhere else.
     *
     * <p>A skew is {@code model - recorded} as a decimal ({@link #skew}),
     * so the one that states "this clock stays where it was" is zero.  A
     * delta that is not an integer is not one this map carries -- the gap
     * for it is raised where it is computed -- and is read here as no
     * movement rather than as a movement of unknown size.</p>
     */
    private static boolean movesAClock(Map<String, String> clockDeltas) {
        if (clockDeltas == null) return false;
        for (String delta : clockDeltas.values()) {
            if (delta == null || delta.trim().isEmpty()) continue;
            try {
                if (new java.math.BigInteger(delta.trim()).signum() != 0) {
                    return true;
                }
            } catch (NumberFormatException notAnInstant) {
                continue;
            }
        }
        return false;
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
            return Outcome.refused(id, candidate.task.taskId(),
                    ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                            "the query was refused: " + built.refusal), "", gaps);
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
            return Outcome.refused(id, candidate.task.taskId(),
                    ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                            "SOLVER_TIMEOUT after " + budget + "ms"), query, gaps);
        }
        // An answer that is neither sat nor unsat is not a verdict about the
        // corpus: an "(error ...)" says z3 could not READ the query and an
        // "unknown" says it did not decide, so reading either as UNSAT would
        // publish "no world of this corpus takes the other arm" on the
        // solver's authority.  Refused by name, the way the composer refuses
        // the same two answers.
        if (!answer.decided()) {
            return Outcome.refused(id, candidate.task.taskId(),
                    ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                            "the solver did not decide this flip: "
                                    + answer.status()
                                    + (answer.reason().isEmpty() ? ""
                                    : " " + answer.reason())
                                    + (solver.errors().isEmpty() ? ""
                                    : " " + solver.errors())), query, gaps);
        }
        if (!answer.sat()) {
            return Outcome.refused(id, candidate.task.taskId(),
                    ObligationResult.of(id, Verdict.UNSAT, "",
                            "no world of this corpus takes the other arm at "
                                    + decision.siteId() + "#"
                                    + decision.ordinal()), query, gaps);
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
            // FAIL CLOSED: NEVER WRITE A SKEW THE REPLAY CANNOT APPLY.
            // A CLOCK cell is a millisecond count in a Java long
            // (JavaPrimitiveSmtSemantics.clockDomain), so both the skew the
            // focus row carries and the instant the mint plants have to be
            // one.  With the ceiling on the query's clock variables this is
            // unreachable -- it is the door held to the next declaration
            // that forgets it, and to the answer hdfs-11741 campaign #2 got
            // when the ceiling was missing: an instant past 2^63, a
            // negative difference printed as the unsigned
            // 18446742283726387588, a skew FocusedReplay.clockSkew could
            // not parse, and a mint that planted nothing.
            java.math.BigInteger skewed = new java.math.BigInteger(delta);
            java.math.BigInteger instant =
                    skewed.add(new java.math.BigInteger(recorded.trim()));
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
                return Outcome.refused(id, candidate.task.taskId(),
                        ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                                "clock root " + rootId + " is owed a skew of "
                                        + skewed + ", which is not a Java "
                                        + "long, so the obligation states a "
                                        + "world no replay can run"), query, gaps);
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
        // Exploration exists to collect an arm the seed does NOT have
        // (HANDOVER SS1.5).  A model that hands every root back the value the
        // recording minted, and answers no handoff, asks for the seed replay
        // under another name: whatever it satisfies, it is not a world the
        // corpus lacks, and a replay spent on it would record the rows it
        // already has.  Refused by name rather than run.
        //
        // THE WAVE'S GAP, DIAGNOSTIC.  It says "the flipped decision does
        // not depend on the declared roots on this prefix", which is a
        // fact about the question this wave asked and about no execution:
        // the verdict row already refuses the obligation, so nothing is
        // admitted on it either way.  It used to be raised BLOCKING under
        // candidate.path.sessionId -- the SEED's id for every wave-0 flip
        // -- so 5 rows of hdfs-11741 campaign #4 landed in the recording's
        // own ledger saying the recording had a blocking defect, and
        // run_engine.sh campaign_write_gaps exited 3 on them.  A session's
        // gaps are the session's own.
        //
        // Asked of the MODEL's OWN SKEWS first: a moved clock is a world of
        // its own, so a clock-driven flip is never this refusal however its
        // pinned roots came back.
        //
        // Asked of the MODEL's OWN roots and answers, before the world this
        // path was cut from is merged in: "did the solver ask for anything
        // the parent's replay did not already run" is a question about this
        // query's answer, and merged values would make a child of a skewed
        // replay look like a counterfactual it is not.
        String recorded = recordedValuation(corpus, candidate, roots, answers,
                clockDeltas);
        if (!recorded.isEmpty()) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, id,
                    recorded));
            return Outcome.refused(id, candidate.task.taskId(),
                    ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                            recorded), query, gaps);
        }
        // THE WORLD THIS FLIP EXTENDS.  The path was cut from a session that
        // ran in a world of its own ({@link Corpus.World}), and the replay
        // of this obligation has to run in that world too, plus whatever
        // this model asks on top: the path only exists there.  So the
        // parent's assignments, skews and answers are the floor and the
        // model overlays them -- the model wins on a key both state, because
        // that key is exactly what this obligation moves further -- and the
        // parent's FLIPS travel whole, to be enforced by the replay
        // ({@code runtime/FocusedReplay}) and asserted by the query
        // ({@link FlipQuery}).  The seed's world is empty, so a wave-0 flip
        // merges nothing.
        Corpus.World inherited = corpus.world(candidate.path.sessionId);
        roots = overlay(inherited.rootAssignments, roots);
        clockDeltas = overlay(inherited.clockDeltas, clockDeltas);
        answers = overlay(inherited.answers, answers);
        Obligation solved = Obligation.of(id, candidate.task.taskId(),
                candidate.path.pathId, decision.siteId(), decision.ordinal(),
                !decision.outcome(), roots, answers, unproducible);
        // THE FOCUSED SET.  A replay plants an assignment at the MINT of
        // the root and nowhere else, so the obligation states WHERE every
        // root it assigns is minted and the focus row lists those
        // occurrences beside the flipped path's own.  The RECORDING is what
        // states where: it is the one run of the whole workload the case's
        // declarations and every planned address are written about, and
        // exploration already resolves the anchor against it alone
        // ({@link ExploreMain}).  The window a root may move in is the
        // flipped path's own business ({@link FlipQuery}) and stays there --
        // that is a counterfactual about one execution, while an address is
        // a fact about the workload's shape.
        //
        // A root the recording minted nowhere names no occurrence any
        // replay could be focused on, so the obligation is refused by name
        // here rather than spending a replay that would read the
        // recording's value and owe an ASSIGNMENT_UNPLANTED for it.
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
            return Outcome.refused(id, candidate.task.taskId(),
                    ObligationResult.of(id, Verdict.NOT_ADMITTED, "",
                            "ASSIGNMENT_UNMINTABLE: the model assigns "
                                    + String.join(", ", unmintable)
                                    + ", which the recording "
                                    + corpus.seedSessionId()
                                    + " mints nowhere, so no occurrence of a "
                                    + "replay can be focused to plant it"), query, gaps);
        }
        return new Outcome(id, candidate.task.taskId(), solved,
                ObligationResult.of(id, Verdict.SAT_MODEL_READY, "",
                        "the flip at " + decision.siteId() + "#"
                                + decision.ordinal() + " is reachable under "
                                + roots.size() + " root value(s) and "
                                + answers.size() + " answered handoff(s), "
                                + "planted at " + mints.size() + " mint(s)"),
                query, clockDeltas, mints, inherited.flips,
                versions(corpus, built.stateChoices, answer.values()), gaps);
    }

    /**
     * THE VERSIONS THIS WORLD CHOSE: for every read the query bound, the
     * write the model makes it observe -- where the model had writers to
     * choose among, or where the writer ran on another thread than the
     * reader.  Everywhere else program order already decides which write a
     * read observes, and a replay that runs the same path observes it
     * again.  A replay holds a read at the hook the weave put before it and
     * waits for its writer at the writer's own ({@code contract.AccessSites}),
     * so a read is held only where both sites carry one: a placeholder's
     * mint, a site the log did not state or an access in a method the weave
     * does not reach is not one a replay could hold.
     */
    static List<ReadsFrom> versions(Corpus corpus,
                                    List<FlipQuery.StateChoice> choices,
                                    Map<String, String> model) {
        List<ReadsFrom> versions = new ArrayList<ReadsFrom>();
        for (FlipQuery.StateChoice choice : choices) {
            Arms.Arm chosen = choice.chosen(model);
            if (chosen == null) continue;
            Endpoint writer = chosen.interaction().producer();
            for (ReadRow reader : choice.readers) {
                if (held(corpus, reader, writer, choice.alternatives())) {
                    versions.add(ReadsFrom.of(reader.endpoint(), writer));
                }
            }
        }
        return versions;
    }

    /** Whether a replay holds this read to this writer (see #versions). */
    static boolean held(Corpus corpus, ReadRow reader, Endpoint writer,
                        int alternatives) {
        if (reader.mintVersion() != ReadRow.UNKNOWN_VERSION) return false;
        if (!corpus.accessSites().holds(reader.endpoint().site())
                || !corpus.accessSites().holds(writer.site())) {
            return false;
        }
        return alternatives > 1 || !corpus.arms().sameThread(
                reader.sessionId(), reader.endpoint().occurrence(),
                writer.occurrence());
    }

    /** {@code base} with {@code over} laid on top: {@code over} wins. */
    private static Map<String, String> overlay(Map<String, String> base,
                                               Map<String, String> over) {
        Map<String, String> merged = new LinkedHashMap<String, String>(base);
        merged.putAll(over);
        return merged;
    }
}
