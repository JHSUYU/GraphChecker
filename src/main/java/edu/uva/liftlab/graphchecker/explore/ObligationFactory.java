package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonPrimitive;

import edu.uva.liftlab.graphchecker.compose.Independence;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.Z3;

import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;

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
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * The obligations of one task, and the solving of one of them.
 *
 * <p>An obligation is the path as its replay ran it with exactly one decision
 * negated; never the fatal predicate (the composition's question) nor another
 * region's path (its own task). Planning ({@link ExploreMain}) and solving
 * ({@link ObligationSolverMain}, one worker per obligation) run in separate
 * processes: a round's queries are independent.</p>
 */
public final class ObligationFactory {
    /** How many recorded paths of one task a round proposes flips from. */
    public static final int DEFAULT_MAX_PATHS_PER_TASK = 32;
    /** How many flips one path may offer in one round. */
    public static final int DEFAULT_MAX_FLIPS_PER_PATH = 32;
    /** The most flips a cut path's world may already hold: the nesting bound.
     *  Each wave (a generation of worlds, PIPELINE §7.9) nests one more flip,
     *  so without it the search grows per world;
     *  the deepest known witness chain is two flips. */
    public static final int DEFAULT_MAX_WORLD_DEPTH = 3;

    private ObligationFactory() {
    }

    /** What a round may propose per task. */
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

    /** One flip a round proposes: the path, the decision, and its identity. */
    public static final class Candidate {
        public final String obligationId;
        public final Task task;
        public final Corpus.RecordedPath path;
        public final int index;
        public final DecisionRow decision;

        private Candidate(Corpus corpus, Task task,
                          Corpus.RecordedPath path, int index) {
            this(task, path, index, obligationId(task.taskId(),
                    path.decisions.get(index).siteId(),
                    path.decisions.get(index).ordinal(),
                    !path.decisions.get(index).outcome(),
                    dependence(corpus, task, path, index)));
        }

        private Candidate(Task task, Corpus.RecordedPath path, int index,
                          String obligationId) {
            this.task = task;
            this.path = path;
            this.index = index;
            this.decision = path.decisions.get(index);
            this.obligationId = obligationId;
        }

        /** The row a round publishes: what to flip, no model yet (the solver
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
        /** Reader -> writer, the world's pairings (the model's moved writer
         *  choices over the parent's), each as a confirmation names it. */
        public final Map<String, String> pairings;
        /** The rows that hold the replay to them ({@code
         *  runtime.Confirmation}) and the occurrences their order moves,
         *  where the schedule prefix ends ({@link ConfirmMain#holding}). */
        public final ConfirmMain.Holding holding;
        public final List<GapRow> gaps;
        /** The question asked ({@link #question}). */
        public final String question;
        /** Whether this verdict settles it: a solver's own decided one;
         *  never a timeout, an undecided solver, or a reused answer (the
         *  obligation it reused settles it). */
        public final boolean settles;

        private Outcome(Obligation obligation, ObligationResult result,
                        String smt2, Map<String, String> clockDeltas,
                        Map<String, String> rootMints,
                        List<Corpus.Flip> inheritedFlips,
                        Map<String, String> pairings,
                        ConfirmMain.Holding holding,
                        List<GapRow> gaps, String question,
                        boolean settles) {
            this.obligation = obligation;
            this.result = result;
            this.smt2 = smt2;
            this.question = question;
            this.settles = settles;
            this.clockDeltas = Collections.unmodifiableMap(clockDeltas);
            this.rootMints = Collections.unmodifiableMap(rootMints);
            this.inheritedFlips =
                    Collections.unmodifiableList(inheritedFlips);
            this.pairings = Collections.unmodifiableMap(pairings);
            this.holding = holding;
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
                                   List<GapRow> gaps, String question) {
        return refused(candidate, verdict, detail, query, gaps, question,
                true);
    }

    private static Outcome refused(Candidate candidate, Verdict verdict,
                                   String detail, String query,
                                   List<GapRow> gaps, String question,
                                   boolean settles) {
        return new Outcome(null, ObligationResult.of(candidate.obligationId,
                verdict, "", detail), query,
                Collections.<String, String>emptyMap(),
                Collections.<String, String>emptyMap(),
                Collections.<Corpus.Flip>emptyList(),
                Collections.<String, String>emptyMap(), null, gaps, question,
                settles);
    }

    /** {@code model - recorded} as a decimal, or "" if either is not one. */
    static String skew(String model, String recorded) {
        if (model == null || recorded == null) return "";
        try {
            return new BigInteger(model.trim())
                    .subtract(new BigInteger(recorded.trim()))
                    .toString();
        } catch (NumberFormatException notAnInstant) {
            return "";
        }
    }

    /** One WHOLE WORLD digest: all its flips, sorted, so order is irrelevant;
     *  the seed's is {@code ""}. Labels slot and graph rows; arm keys use
     *  {@link #dependence} instead. */
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
     * WHAT ONE FLIPPED GUARD DEPENDS ON, digested: the part of an arm's key
     * besides the arm itself. Shared by {@link Candidate} and {@link
     * Frontier}, which must agree.
     *
     * <ul>
     *   <li><b>Its path condition</b>: the conjuncts {@link FlipQuery}
     *       asserts with it (the path's earlier decisions and the inherited
     *       flips' prefixes) that share a variable with the guard, directly or
     *       through one another ({@link Independence#ofGuard}), each as its
     *       occurrence and {@code siteId#ordinal=outcome}. Any other conjunct
     *       holds at its recorded values whatever the flip's model is, so two
     *       paths differing only there ask the same question.</li>
     *   <li><b>Its world</b>: what the world delivered to the task and to
     *       the factor members that feed it ({@link Corpus#inputShape}), the
     *       writes counted at the locations the guard reads.</li>
     * </ul>
     *
     * <p>Never the session, and never the decision being flipped as an
     * inherited flip: a flip cut back from the world that took it would
     * otherwise be owed again. Trap: the world stays even where the guard
     * names none of it (hdfs-11741's witness, see {@link
     * Corpus#inputShape}).</p>
     */
    public static String dependence(Corpus corpus, Task task,
                                    Corpus.RecordedPath path, int index) {
        DecisionRow flipped = path.decisions.get(index);
        List<DecisionRow> conditions =
                new ArrayList<DecisionRow>(path.decisions.subList(0, index));
        List<ReadRow> reads = new ArrayList<ReadRow>(
                corpus.readsOn(path.sessionId, task.focused()));
        for (Corpus.Flip inherited : corpus.world(path.sessionId).flips) {
            OccurrenceAddress at =
                    corpus.occurrence(inherited.focusedOccurrenceId);
            if (at == null) continue;
            List<DecisionRow> decisions =
                    corpus.decisionsOf(path.sessionId, at);
            long through = -1L;
            for (DecisionRow decision : decisions) {
                if (decision.siteId().equals(inherited.siteId)
                        && decision.ordinal() == inherited.ordinal) {
                    through = decision.seq();
                }
            }
            for (DecisionRow decision : decisions) {
                if (decision.seq() <= through
                        && decision.seq() != flipped.seq()) {
                    conditions.add(decision);
                }
            }
            if (!at.equals(task.focused())) {
                reads.addAll(corpus.readsOn(path.sessionId, at));
            }
        }
        List<DecisionRow> predicates = new ArrayList<DecisionRow>();
        for (DecisionRow condition : conditions) {
            if (Arms.predicate(condition.term())) predicates.add(condition);
        }
        Independence rests = Independence.ofGuard(corpus, path.sessionId,
                flipped.term(), predicates, reads);
        Set<String> kept = new TreeSet<String>();
        for (DecisionRow condition : predicates) {
            if (!rests.keeps(condition)) continue;
            kept.add(condition.occurrence().id() + "|" + condition.siteId()
                    + "#" + condition.ordinal() + "=" + condition.outcome());
        }
        return ArtifactIO.digest(String.join("/", kept) + "\n"
                + corpus.inputShape(path.sessionId, task.focused(),
                corpus.feeders(task.focused(), task.factor()),
                rests.locations()), 16);
    }

    /** The flip a question is about, digested: task, path, site, ordinal
     *  and the outcome asked for -- the first half of its {@link
     *  #question}, and what holds an arm in flight from being proposed again
     *  ({@code Frontier#inFlight}): an id drifts, a flip does not. */
    public static String flip(Candidate candidate) {
        return flip(candidate.task.taskId(), candidate.path.pathId,
                candidate.decision.siteId(), candidate.decision.ordinal(),
                !candidate.decision.outcome());
    }

    /** {@link #flip(Candidate)} of an obligation row's fields. */
    static String flip(String taskId, String pathId, String siteId,
                       int ordinal, boolean flippedOutcome) {
        return ArtifactIO.digest(taskId + "|" + pathId + "|" + siteId + "#"
                + ordinal + " -> " + flippedOutcome, 16);
    }

    /**
     * THE QUESTION one flip asks, as {@code <flip>:<content>}: the flip
     * ({@link #flip}), then a digest of everything its answer rests on --
     * the query as its solver is asked it (or the refusal that leaves
     * none), and all its replay is given: the world it plants (its path's,
     * inherited whole), the focused occurrence, the factor (a set) and the
     * seed session (the focus row, whose factor grows as sessions land and
     * no query reads), and {@code given} (the declared occurrence and the plan
     * generation its class tree is woven from, which GROW moves); the
     * schedule cut is the path's session cut at the focus and factor.  An
     * obligation's id drifts as sessions land; its question does not while
     * all of this reads the same (SOLR-18413 r5: 185 questions asked 717
     * times; 118 of the 166 re-asked with byte-identical queries).  Its
     * solver reuses the answer of one a worker settled ({@code
     * ObligationDir#answered}).
     */
    static String question(Candidate candidate, Corpus.World world,
                           FlipQuery.Built built, String given) {
        StringBuilder text = new StringBuilder();
        text.append(built.ok()
                        ? Z3.modelQuery(built.smt2, built.modelSymbols)
                        : "refused: " + built.refusal).append('\n')
                .append(new TreeMap<String, String>(world.rootAssignments))
                .append(new TreeMap<String, String>(world.clockDeltas))
                .append(new TreeMap<String, String>(world.answers))
                .append(new TreeMap<String, String>(world.pairings));
        for (Corpus.Flip flip : world.flips) {
            // Never the id it was first asked under: ids drift.
            text.append('\n').append(flip.focusedOccurrenceId).append('|')
                    .append(flip.siteId).append('#').append(flip.ordinal)
                    .append(" -> ").append(flip.outcome);
        }
        text.append("\nfocused ").append(candidate.task.focused().id())
                .append("\nseed ").append(candidate.task.seedSessionId());
        // A set: the order the corpus lists it in moves as sessions land.
        Set<String> factor = new TreeSet<String>();
        for (OccurrenceAddress member : candidate.task.factor()) {
            factor.add(member.id());
        }
        for (String member : factor) text.append("\nfactor ").append(member);
        text.append('\n').append(given);
        return flip(candidate) + ":" + ArtifactIO.digest(text.toString(), 16);
    }

    /**
     * One obligation's id: planned occurrence ({@link ClosurePlanner#taskId}),
     * the arm, and what its guard depends on ({@link #dependence}).
     *
     * <p>Never the session: a {@code pathId} in the key gives one arm as many
     * ids as sessions (the row still carries it; the query is built over it).
     * The dependence lets flip chains deepen and keeps a known path under new
     * inputs owed (hdfs-11741: the same expiry compare over four keys instead
     * of five), never the same question twice.</p>
     */
    public static String obligationId(String taskId, String siteId,
                                      int ordinal, boolean flippedOutcome,
                                      String dependence) {
        return ArtifactIO.digest(taskId + "|" + siteId + "|" + ordinal + "|"
                + flippedOutcome + "|" + dependence, 16);
    }

    /**
     * The flips one task offers, recording every already-settled candidate.
     *
     * <p>PIPELINE §7.4: only decisions at sites the closure demanded for this
     * member (target guards for the anchor, own guards for a writer/producer).
     * Cut only from the paths of sessions that may parent ({@link
     * Branches#parents}): a child inherits the parent's world (PIPELINE
     * §7.5), a NOT_ADMITTED replay ran no world, and one whose branch
     * stopped ran none the question is asked in. Such sessions still attest
     * arms ({@link Frontier}).  Every path is keyed; {@code
     * maxPathsPerTask} bounds the paths that offer an owed arm no round has
     * in flight, so it defers new work only, to the next round.</p>
     *
     * @param flipSites site ids this task's demand names; null = none
     * @param branches  which sessions a path may be cut from
     * @param owed      the one ledger of owed arms ({@link Frontier})
     * @param gaps      receives settled candidates, so a shrinking round is
     * explained
     */
    public static List<Candidate> candidates(Corpus corpus, Task task,
                                             Set<String> flipSites,
                                             Bounds bounds, Branches branches,
                                             Frontier owed,
                                             List<GapRow> gaps) {
        List<Candidate> candidates = new ArrayList<Candidate>();
        Set<String> offered = new LinkedHashSet<String>();
        int paths = 0;
        int unread = 0;
        int tooDeep = 0;
        for (Corpus.RecordedPath path : smallestWorldFirst(corpus,
                corpus.pathsOf(task.focused()))) {
            // Only a parent's paths are cut (see above).
            if (!branches.parents(path.sessionId)) continue;
            // The nesting bound; counted into a gap below.
            if (corpus.world(path.sessionId).flips.size()
                    > bounds.maxWorldDepth) {
                tooDeep++;
                continue;
            }
            // Its owed arms: each arm once (the same arm from another path is
            // the same obligation; the first path -- smallest world, fewest
            // inherited constraints -- is its prefix), fault flips first
            // (PIPELINE §7.4: cheap, and they grow the graph), at most
            // maxFlipsPerPath of them.
            List<Candidate> owedHere = new ArrayList<Candidate>();
            List<Candidate> flying = new ArrayList<Candidate>();
            int unflipped = 0;
            for (int index : faultFirst(corpus, path)) {
                DecisionRow decision = path.decisions.get(index);
                if (!FlipQuery.flippable(decision)) {
                    continue;
                }
                if (flipSites == null
                        || !FlipQuery.asks(flipSites, decision)) {
                    continue;
                }
                Candidate candidate =
                        new Candidate(corpus, task, path, index);
                if (offered.contains(candidate.obligationId)) continue;
                String reason = owed.settled(candidate.obligationId);
                if (!reason.isEmpty()) {
                    offered.add(candidate.obligationId);
                    gaps.add(GapRow.of(path.sessionId,
                            GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                            decision.siteId() + "#" + decision.ordinal()
                                    + " -> " + !decision.outcome(), reason));
                    continue;
                }
                // Queued or running: owed, but not this round's to ask
                // (Frontier#open holds it), so it holds no path slot.
                if (owed.flying(candidate)) {
                    flying.add(candidate);
                    continue;
                }
                if (owedHere.size() >= bounds.maxFlipsPerPath) {
                    unflipped++;
                    continue;
                }
                owedHere.add(candidate);
            }
            for (Candidate candidate : flying) {
                offered.add(candidate.obligationId);
                candidates.add(candidate);
            }
            // The path bound counts new work, never repetition: a path whose
            // arms are all settled, in flight or offered by a path before it
            // is no path to cut from (hdfs-adhoc-08 HG8F: of 15995 paths past
            // the bound, 15670 offered nothing owed).  Smallest-world-first
            // means the bound keeps the paths closest to the recording.  It
            // DEFERS, never drops: every round reads the task's paths again,
            // and once the paths before them are answered or in flight, the
            // ones it left are the first that count (gap below).
            if (owedHere.isEmpty()) continue;
            if (paths >= bounds.maxPathsPerTask) {
                unread++;
                continue;
            }
            paths++;
            for (Candidate candidate : owedHere) {
                offered.add(candidate.obligationId);
                candidates.add(candidate);
            }
            if (unflipped > 0) {
                gaps.add(GapRow.of(path.sessionId,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        task.taskId() + " max-flips-per-path="
                                + bounds.maxFlipsPerPath,
                        "this path offered more owed arms than one round "
                                + "takes from it: " + unflipped
                                + " after the " + bounds.maxFlipsPerPath
                                + " this round cut, left unasked"));
            }
        }
        if (tooDeep > 0) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    task.taskId() + " max-world-depth="
                            + bounds.maxWorldDepth,
                    tooDeep + " cuttable path(s) of this task stand in a "
                            + "world of more than " + bounds.maxWorldDepth
                            + " flip(s), and no round nests deeper: none of "
                            + "them was cut from"));
        }
        if (unread > 0) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    task.taskId() + " max-paths-per-region="
                            + bounds.maxPathsPerTask,
                    "this task has " + (paths + unread) + " recorded "
                            + "path(s) that offer an owed arm and this round "
                            + "planned from " + paths + ": " + unread
                            + " path(s), the ones carrying the largest "
                            + "worlds, wait for a later round"));
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

    /** What one model plants, or why no replay can plant it. */
    private static final class Planted {
        final Map<String, String> roots = new LinkedHashMap<String, String>();
        final Map<String, String> clockDeltas =
                new LinkedHashMap<String, String>();
        final Map<String, String> answers =
                new LinkedHashMap<String, String>();
        /** Reader -> writer: the writer choices the model moved off the
         *  recording ({@link ConfirmMain#writer}). */
        final Map<String, String> pairings =
                new LinkedHashMap<String, String>();
        final List<String> unproducible = new ArrayList<String>();
        /** Why no replay can run it, or "". */
        String refusal = "";
    }

    /** The roots, clock skews, answers and pairings one model assigns. */
    private static Planted planted(Corpus corpus, Candidate candidate,
                                   FlipQuery.Built built,
                                   Map<String, String> values,
                                   List<GapRow> gaps) {
        Planted planted = new Planted();
        for (Map.Entry<String, String> variable
                : built.rootVariables.entrySet()) {
            String value = values.get(variable.getKey());
            if (value != null) planted.roots.put(variable.getValue(), value);
        }
        // A clock's model is an instant of the recording's window; the replay
        // is owed the difference from the host's reading there (a skew, as
        // the replay plants it: RootMintRow#hostReading).
        for (Map.Entry<String, String> variable
                : built.clockVariables.entrySet()) {
            String rootId = variable.getValue();
            RootMintRow read = corpus.rootOf(candidate.path.sessionId,
                    rootId);
            String recorded = read == null ? "" : read.hostReading();
            String delta = skew(values.get(variable.getKey()), recorded);
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
                planted.refusal = "clock root " + rootId + " is owed a skew "
                        + "of " + skewed + ", which is not a Java long, so "
                        + "the obligation states a world no replay can run";
                return planted;
            }
            planted.clockDeltas.put(rootId, delta);
        }
        for (FlipQuery.Control control : built.controls) {
            String value = values.get(control.variable);
            if (value != null) {
                String answered = answer(control.sort, value);
                if (answered == null) {
                    planted.refusal = "the model's value " + value + " of "
                            + "the String handoff " + control.attachEndpointId
                            + " is no string literal, so no replay can be "
                            + "answered with it";
                    return planted;
                }
                planted.answers.put(control.attachEndpointId, answered);
            }
            if (control.unproducible) {
                planted.unproducible.add(control.attachEndpointId);
            }
        }
        // A writer the model chose that is not the recording's pairing (the
        // writer its reads observed, or the run's own choice) is a pairing
        // the replay is held to, the location's
        // INITIAL among them; a read another session made is no event of
        // the world this replay runs.
        for (FlipQuery.WriterChoice choice : built.choices) {
            String chosen = "";
            for (String selector : choice.writes.keySet()) {
                if ("true".equals(values.get(selector))) chosen = selector;
            }
            if (chosen.isEmpty() || chosen.equals(choice.recorded)) continue;
            WriteRow write = choice.writes.get(chosen);
            for (ReadRow read : choice.reads) {
                if (write == null || !read.sessionId().equals(
                        candidate.path.sessionId)) {
                    planted.refusal = "PAIRING_UNPLANTABLE: the model takes "
                            + "the other arm with read " + read.endpoint()
                            + " of session " + read.sessionId() + " paired "
                            + "to " + (write == null ? "an arm stating no "
                            + "write" : "writer " + ConfirmMain.writer(write))
                            + ", and the replay runs the world of "
                            + candidate.path.sessionId;
                    return planted;
                }
                planted.pairings.put(Confirmation.id(read.endpoint()),
                        ConfirmMain.writer(write));
            }
        }
        return planted;
    }

    /**
     * Why this model plants nothing its path's own session did not already
     * run, or "": no clock moved, no handoff answered, no writer choice
     * moved off the recording, and every assigned root at the value that
     * session ran it at (none assigned included) -- its mint's, or, where it
     * read the root and minted none, its stated reading ({@link
     * Corpus#rootValue}).  The replay it asks for then runs the world that
     * session ran -- its path's world, inherited whole -- and a replay sets
     * nothing else: a container's state ({@code st__*}) follows its writer's
     * and a term the lowering refused ({@code unsupported__*}) is the run's,
     * never planted.  A moved clock is a counterfactual of its own and is
     * checked FIRST (a pinned root beside moved clocks is not that replay).
     * Asked of the model's own skews, roots, answers and pairings, before
     * the parent's world is laid under them.
     */
    private static String plantsNothing(Corpus corpus, Candidate candidate,
                                        FlipQuery.Built built,
                                        Map<String, String> values,
                                        Planted planted) {
        if (movesAClock(planted.clockDeltas) || !planted.answers.isEmpty()
                || !planted.pairings.isEmpty()) {
            return "";
        }
        List<String> same = new ArrayList<String>();
        for (Map.Entry<String, String> assignment
                : planted.roots.entrySet()) {
            String reading = corpus.rootValue(candidate.path.sessionId,
                    assignment.getKey());
            if (reading.isEmpty()
                    || !reading.equals(assignment.getValue())) {
                return "";
            }
            same.add(assignment.getKey() + "=" + reading);
        }
        if (!same.isEmpty()) {
            return "the model is the valuation " + candidate.path.sessionId
                    + " ran (" + String.join(", ", same) + ", each its mint's"
                    + " or, where it minted none, the reading it states) and"
                    + " answers no handoff, so the replay it asks for runs"
                    + " that session's world again: this is not an arm the"
                    + " corpus lacks. Either the flipped decision's recorded"
                    + " polarity disagrees with the root value the same"
                    + " session ran -- DecisionRow.outcome must say whether"
                    + " the published term HELD (CONTRACT-SPEC §2.2) -- or"
                    + " the query binds a root the flip does not depend on";
        }
        Set<String> plantable = new LinkedHashSet<String>();
        plantable.addAll(built.rootVariables.keySet());
        plantable.addAll(built.clockVariables.keySet());
        for (FlipQuery.Control control : built.controls) {
            plantable.add(control.variable);
        }
        List<String> run = new ArrayList<String>();
        for (String symbol : built.modelSymbols) {
            if (!plantable.contains(symbol) && values.containsKey(symbol)) {
                run.add(symbol);
            }
        }
        return "EMPTY_WORLD: the model assigns no root, moves no clock, "
                + "answers no handoff and moves no writer choice, so the "
                + "replay it asks for would run the world of "
                + candidate.path.sessionId + " again, where "
                + candidate.decision.siteId() + "#"
                + candidate.decision.ordinal() + " took "
                + candidate.decision.outcome() + "; the " + run.size()
                + " symbol(s) it sets are ones no replay plants"
                + (run.isEmpty() ? "" : " (" + String.join(", ",
                run.subList(0, Math.min(8, run.size())))
                + (run.size() > 8 ? ", ..." : "") + ")");
    }

    /**
     * The query with every writer choice held to the recording's pairing
     * ({@link FlipQuery.WriterChoice#recorded}: the writer its reads
     * observed, or the run's own choice where that is no one writer's
     * arm); a container
     * state follows its writer's.  A term the lowering refused ({@code
     * unsupported__*}) has no recorded value and stays free.  "" when the
     * query has no writer choice to hold.
     */
    private static String heldToRecording(FlipQuery.Built built) {
        StringBuilder held = new StringBuilder();
        for (FlipQuery.WriterChoice choice : built.choices) {
            if (built.modelSymbols.contains(choice.recorded)) {
                held.append("(assert ").append(choice.recorded)
                        .append(")\n");
            }
        }
        return held.length() == 0 ? "" : built.smt2 + held;
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

    /** Finds the flip one published obligation names, from the corpus alone,
     *  under the id its ROUND gave it.  Never recomputed: a solver reads the
     *  corpus as it stands, where sessions landed since the round grow a
     *  task's factor and so its dependence -- a second id for one
     *  obligation, whose answer the ledger then never meets (hdfs-17967
     *  pathA v82: 24 of 169 workers). */
    public static Candidate locate(Corpus corpus, Obligation obligation) {
        Task task = ClosurePlanner.taskOf(corpus, obligation.taskId());
        if (task == null) return null;
        for (Corpus.RecordedPath path : corpus.pathsOf(task.focused())) {
            if (!path.pathId.equals(obligation.pathId())) continue;
            for (int index = 0; index < path.decisions.size(); index++) {
                DecisionRow decision = path.decisions.get(index);
                if (decision.siteId().equals(obligation.siteId())
                        && decision.ordinal() == obligation.ordinal()) {
                    return new Candidate(task, path, index,
                            obligation.obligationId());
                }
            }
        }
        return null;
    }

    /**
     * Solves one candidate: its query, its verdict and its model; or reuses
     * the answer of the same question a worker settled.
     *
     * @param given    what the replay is given besides the corpus, as
     *                 {@link #question} keys it
     * @param answered the questions this iteration's workers settled
     */
    public static Outcome solve(Corpus corpus, Candidate candidate, Path z3,
                                long timeoutMillis, String given,
                                Map<String, ObligationDir.Answer> answered) {
        String id = candidate.obligationId;
        DecisionRow decision = candidate.decision;
        FlipQuery.Built built = FlipQuery.build(corpus, candidate.task,
                candidate.path, candidate.index);
        Corpus.World inherited = corpus.world(candidate.path.sessionId);
        String question = question(candidate, inherited, built, given);
        List<GapRow> gaps = new ArrayList<GapRow>(built.gaps);
        ObligationDir.Answer earlier = answered.get(question);
        if (earlier != null) {
            String detail = "question " + question + " was settled "
                    + earlier.result.verdict() + " by obligation "
                    + earlier.obligationId
                    + (earlier.result.sessionId().isEmpty() ? ""
                    : " (session " + earlier.result.sessionId() + ")")
                    + ", which asked the same flip and query of the same "
                    + "world, focus, factor, seed session, declared "
                    + "occurrence and plan generation: "
                    + earlier.result.detail();
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, id, detail));
            // Settled by that obligation, never by this one: were it taken
            // back, a reuse of a reuse would stand on nothing.
            return refused(candidate, earlier.result.verdict(), detail, "",
                    gaps, question, false);
        }
        if (!built.ok()) {
            return refused(candidate, Verdict.NOT_ADMITTED,
                    "the query was refused: " + built.refusal, "", gaps,
                    question);
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
                    "SOLVER_TIMEOUT after " + budget + "ms", query, gaps,
                    question, false);
        }
        // Neither sat nor unsat (error/unknown) is no verdict: refused by name,
        // never read as UNSAT.
        if (!answer.decided()) {
            return refused(candidate, Verdict.NOT_ADMITTED,
                    "the solver did not decide this flip: " + answer.status()
                            + (answer.reason().isEmpty() ? ""
                            : " " + answer.reason())
                            + (solver.errors().isEmpty() ? ""
                            : " " + solver.errors()), query, gaps,
                    question, false);
        }
        if (!answer.sat()) {
            return refused(candidate, Verdict.UNSAT,
                    "no world of this corpus takes the other arm at "
                            + decision.siteId() + "#" + decision.ordinal(),
                    query, gaps, question);
        }
        Planted planted = planted(corpus, candidate, built, answer.values(),
                gaps);
        if (!planted.refusal.isEmpty()) {
            return refused(candidate, Verdict.NOT_ADMITTED, planted.refusal,
                    query, gaps, question);
        }
        // A pairing is planted only where the recorded ones take no flip:
        // a model that moves a writer choice is asked again with every
        // choice held to the writer the recording's reads observed, and one
        // that then plants something is the one run -- a root moved under
        // the run's own pairings, which no order has to realize.
        if (!planted.pairings.isEmpty()) {
            String held = heldToRecording(built);
            Z3.Answer again = held.isEmpty() ? null
                    : solver.ask(held, built.modelSymbols, false);
            if (again != null && again.decided() && again.sat()) {
                Planted recorded = planted(corpus, candidate, built,
                        again.values(), gaps);
                if (recorded.refusal.isEmpty() && plantsNothing(corpus,
                        candidate, built, again.values(), recorded)
                        .isEmpty()) {
                    planted = recorded;
                    query = Z3.modelQuery(held, built.modelSymbols);
                }
            }
        }
        // A model that plants nothing its path's session did not run asks
        // for that session's replay again (PIPELINE §7: exploration collects
        // arms the corpus lacks).  DIAGNOSTIC under EXPLORATION, never
        // BLOCKING in the recording's ledger.
        String nothing = plantsNothing(corpus, candidate, built,
                answer.values(), planted);
        if (!nothing.isEmpty()) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, id,
                    nothing));
            return refused(candidate, Verdict.NOT_ADMITTED, nothing, query,
                    gaps, question);
        }
        // The world this flip extends ({@link Corpus.World}): the parent's
        // values are the floor, the model overlays them (model wins), and the
        // parent's flips travel whole (enforced by FocusedReplay, asserted by
        // FlipQuery).
        Map<String, String> roots =
                overlay(inherited.rootAssignments, planted.roots);
        Map<String, String> clockDeltas =
                overlay(inherited.clockDeltas, planted.clockDeltas);
        Map<String, String> answers =
                overlay(inherited.answers, planted.answers);
        Map<String, String> pairings =
                overlay(inherited.pairings, planted.pairings);
        // The world's pairings held as CONFIRM holds a model's, over the
        // session the path was cut from (ConfirmMain#holding).
        ConfirmMain.Holding holding;
        try {
            holding = ConfirmMain.holding(
                    corpus.session(candidate.path.sessionId), pairings);
        } catch (ConfirmMain.Refused unheld) {
            return refused(candidate, Verdict.NOT_ADMITTED,
                    unheld.getMessage(), query, gaps, question);
        }
        Obligation solved = Obligation.of(id, candidate.task.taskId(),
                candidate.path.pathId, decision.siteId(), decision.ordinal(),
                !decision.outcome(), roots, answers, planted.unproducible);
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
                    gaps, question);
        }
        return new Outcome(solved, ObligationResult.of(id,
                Verdict.SAT_MODEL_READY, "", "the flip at "
                        + decision.siteId() + "#" + decision.ordinal()
                        + " is reachable under " + roots.size()
                        + " root value(s), " + answers.size()
                        + " answered handoff(s) and " + pairings.size()
                        + " planted pairing(s), planted at " + mints.size()
                        + " mint(s)"),
                query, clockDeltas, mints, inherited.flips, pairings,
                holding, gaps, question, false);
    }

    /**
     * A model's value of one control as a replay is answered with it: a
     * String's as its JSON string literal, which the replay plants verbatim, the way a read row spells
     * a String; any other sort's as the model prints it.  Null when a
     * String's value is no string literal.
     */
    static String answer(String sort, String value) {
        if (!VmTermLowering.Sort.STRING.smt.equals(sort)) return value;
        String text = Z3.javaString(value);
        return text == null ? null : new JsonPrimitive(text).toString();
    }

    /** {@code base} with {@code over} laid on top: {@code over} wins. */
    private static Map<String, String> overlay(Map<String, String> base,
                                               Map<String, String> over) {
        Map<String, String> merged = new LinkedHashMap<String, String>(base);
        merged.putAll(over);
        return merged;
    }
}
