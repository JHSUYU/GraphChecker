package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonPrimitive;

import edu.uva.liftlab.graphchecker.compose.Independence;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
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
import edu.uva.liftlab.graphchecker.contract.Parallel;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

public final class ObligationFactory {
    static final int MAX_REFUTED_WORLDS = 8;
    static final String REFUTED_BOUND = "OPEN_ARM_MAX_REFUTED_WORLDS";

    public static final int DEFAULT_MAX_PATHS_PER_TASK = 32;
    public static final int DEFAULT_MAX_FLIPS_PER_PATH = 32;
    public static final int DEFAULT_MAX_WORLD_DEPTH = 3;

    private ObligationFactory() {
    }

    public static final class Bounds {
        public final int maxPathsPerTask;
        public final int maxFlipsPerPath;
        public final int maxWorldDepth;

        public Bounds(int maxPathsPerTask, int maxFlipsPerPath,
                      int maxWorldDepth) {
            this.maxPathsPerTask = maxPathsPerTask <= 0
                    ? DEFAULT_MAX_PATHS_PER_TASK : maxPathsPerTask;
            this.maxFlipsPerPath = maxFlipsPerPath <= 0
                    ? DEFAULT_MAX_FLIPS_PER_PATH : maxFlipsPerPath;
            this.maxWorldDepth = maxWorldDepth < 0
                    ? DEFAULT_MAX_WORLD_DEPTH : maxWorldDepth;
        }
    }

    public static final class Candidate {
        public final String obligationId;
        public final Task task;
        public final Corpus.RecordedPath path;
        public final int index;
        public final DecisionRow decision;
        public final boolean forced;
        public final ReadRow pairedRead;
        public final long pairedVersion;

        private Candidate(Corpus corpus, Task task,
                          Corpus.RecordedPath path, int index,
                          boolean forced) {
            this(task, path, index, obligationId(task.taskId(),
                    path.decisions.get(index).siteId(),
                    path.decisions.get(index).ordinal(),
                    path.decisions.get(index).outcome() == forced,
                    dependence(corpus, task, path, index)
                            + (forced ? "|forced" : "")), forced);
        }

        private Candidate(Task task, Corpus.RecordedPath path, int index,
                          String obligationId, boolean forced) {
            this.task = task;
            this.path = path;
            this.index = index;
            this.decision = path.decisions.get(index);
            this.obligationId = obligationId;
            this.forced = forced;
            this.pairedRead = null;
            this.pairedVersion = -1L;
        }

        Candidate(Task task, Corpus.RecordedPath path, ReadRow read,
                  long version, String obligationId) {
            this.task = task;
            this.path = path;
            this.index = -1;
            this.decision = null;
            this.obligationId = obligationId;
            this.forced = false;
            this.pairedRead = read;
            this.pairedVersion = version;
        }

        public boolean pairing() {
            return pairedRead != null;
        }

        public String siteId() {
            return pairing() ? PairingFlip.site(pairedRead)
                    : decision.siteId();
        }

        public int ordinal() {
            return pairing() ? PairingFlip.ordinal(pairedVersion)
                    : decision.ordinal();
        }

        public boolean flippedOutcome() {
            return pairing() || decision.outcome() == forced;
        }

        public Obligation proposal() {
            return Obligation.of(obligationId, task.taskId(), path.pathId,
                    siteId(), ordinal(),
                    flippedOutcome(),
                    Collections.<String, String>emptyMap(),
                    Collections.<String, String>emptyMap(),
                    Collections.<String>emptyList());
        }
    }

    public static final class Outcome {
        public final Obligation obligation;
        public final ObligationResult result;
        public final String smt2;
        public final Map<String, String> clockDeltas;
        public final Map<String, String> rootMints;
        public final List<Corpus.Flip> inheritedFlips;
        public final Map<String, String> pairings;
        public final ConfirmMain.Holding holding;
        public final List<GapRow> gaps;
        public final String question;
        public final boolean settles;
        public final boolean openArm;
        final HardAsk owed;

        Outcome(Obligation obligation, ObligationResult result,
                        String smt2, Map<String, String> clockDeltas,
                        Map<String, String> rootMints,
                        List<Corpus.Flip> inheritedFlips,
                        Map<String, String> pairings,
                        ConfirmMain.Holding holding,
                        List<GapRow> gaps, String question,
                        boolean settles, boolean openArm, HardAsk owed) {
            this.owed = owed;
            this.obligation = obligation;
            this.openArm = openArm;
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

    private static Outcome refused(Candidate candidate, Verdict verdict,
                                   String detail, String query,
                                   List<GapRow> gaps, String question) {
        return refused(candidate, verdict, detail, query, gaps, question,
                true);
    }

    static Outcome refused(Candidate candidate, Verdict verdict,
                           String detail, String query,
                           List<GapRow> gaps, String question,
                           boolean settles) {
        return refused(candidate.obligationId, verdict, detail, query, gaps,
                question, settles, null);
    }

    private static Outcome refused(String obligationId, Verdict verdict,
                                   String detail, String query,
                                   List<GapRow> gaps, String question,
                                   boolean settles, HardAsk owed) {
        return new Outcome(null, ObligationResult.of(obligationId,
                verdict, "", detail), query,
                Collections.<String, String>emptyMap(),
                Collections.<String, String>emptyMap(),
                Collections.<Corpus.Flip>emptyList(),
                Collections.<String, String>emptyMap(), null, gaps, question,
                settles, false, owed);
    }

    static final String HARD_MODEL_STALE = "HARD_MODEL_STALE";

    static Outcome settled(HardAsk ask, Z3.Answer answer, long budget,
                           Z3 solver, String query) {
        List<GapRow> gaps = new ArrayList<GapRow>(ask.gaps);
        if (answer.timedOut()) {
            gaps.add(GapRow.of(ask.gapSession, GapKind.SOLVER_TIMEOUT,
                    GapClass.DIAGNOSTIC, ask.obligationId,
                    "no verdict in " + budget + "ms: the flip is an "
                            + "unexplored sibling, not a closed one"));
            return refused(ask.obligationId, Verdict.NOT_ADMITTED,
                    "SOLVER_TIMEOUT after " + budget + "ms", query, gaps,
                    ask.question, false, ask);
        }
        if (answer.memOut()) {
            gaps.add(GapRow.of(ask.gapSession, GapKind.SOLVER_MEMOUT,
                    GapClass.DIAGNOSTIC, ask.obligationId,
                    answer.reason() + ": the flip is an unexplored sibling,"
                            + " not a closed one"));
            return refused(ask.obligationId, Verdict.NOT_ADMITTED,
                    "SOLVER_MEMOUT at " + solver.capMb() + " MB", query, gaps,
                    ask.question, false, ask);
        }
        if (!answer.decided()) {
            return refused(ask.obligationId, Verdict.NOT_ADMITTED,
                    "the solver did not decide this flip: " + answer.status()
                            + (answer.reason().isEmpty() ? ""
                            : " " + answer.reason())
                            + (solver.errors().isEmpty() ? ""
                            : " " + solver.errors()), query, gaps,
                    ask.question, false, null);
        }
        if (!answer.sat()) {
            return refused(ask.obligationId, Verdict.UNSAT, ask.unsatDetail,
                    query, gaps, ask.question, true, null);
        }
        return null;
    }

    static String instant(String reading, String skew) {
        if (reading == null || skew == null) return "";
        try {
            return new BigInteger(reading.trim())
                    .add(new BigInteger(skew.trim())).toString();
        } catch (NumberFormatException notAnInstant) {
            return "";
        }
    }

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

    static String worldText(Corpus.World world) {
        StringBuilder text = new StringBuilder()
                .append(new TreeMap<String, String>(world.rootAssignments))
                .append(new TreeMap<String, String>(world.clockDeltas))
                .append(new TreeMap<String, String>(world.answers))
                .append(new TreeMap<String, String>(world.pairings));
        for (Corpus.Flip flip : world.flips) {
            text.append('\n').append(flip.focusedOccurrenceId).append('|')
                    .append(flip.siteId).append('#').append(flip.ordinal)
                    .append(" -> ").append(flip.outcome);
        }
        return text.toString();
    }

    static String wholeWorldDigest(Corpus.World world) {
        return ArtifactIO.digest(worldText(world), 16);
    }

    public static String dependence(Corpus corpus, Task task,
                                    Corpus.RecordedPath path, int index) {
        return corpus.dependence(task, path.pathId + "#" + index,
                () -> keyed(corpus, task, path, index));
    }

    static final class Keyed {
        final Task task;
        final Corpus.RecordedPath path;
        final int index;

        Keyed(Task task, Corpus.RecordedPath path, int index) {
            this.task = task;
            this.path = path;
            this.index = index;
        }
    }

    static List<String> dependences(Corpus corpus, List<Keyed> arms) {
        corpus.configurationLiterals();
        Map<String, Keyed> last = new HashMap<String, Keyed>();
        for (Keyed arm : arms) last.put(arm.path.sessionId, arm);
        try {
            return Parallel.grouped(arms, arm -> arm.path.sessionId, arm -> {
                String keyed = dependence(corpus, arm.task, arm.path,
                        arm.index);
                if (last.get(arm.path.sessionId) == arm) {
                    corpus.keysDone(arm.path.sessionId);
                }
                return keyed;
            });
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
    }

    private static String keyed(Corpus corpus, Task task,
                                Corpus.RecordedPath path, int index) {
        DecisionRow flipped = path.decisions.get(index);
        List<DecisionRow> predicates = new ArrayList<DecisionRow>();
        for (DecisionRow condition : path.decisions.subList(0, index)) {
            if (Arms.predicate(condition.term())) predicates.add(condition);
        }
        Independence rests = Independence.ofGuard(corpus, path.sessionId,
                flipped.term(), predicates,
                corpus.readsOn(path.sessionId, task.focused()));
        Map<String, Set<String>> kept = new TreeMap<String, Set<String>>();
        List<String> stated = new ArrayList<String>();
        stated.add(flipped.term());
        Set<String> domains = new TreeSet<String>();
        domains(corpus, path.sessionId, flipped.term(), domains);
        for (DecisionRow condition : predicates) {
            if (!rests.keeps(condition)) continue;
            kept.computeIfAbsent(condition.occurrence().id() + "|"
                    + condition.siteId() + "=" + condition.outcome(),
                    key -> new HashSet<String>()).add(corpus.decisionShape(
                    path.sessionId, condition.term()));
            stated.add(condition.term());
            domains(corpus, path.sessionId, condition.term(), domains);
        }
        StringBuilder text = new StringBuilder();
        for (Map.Entry<String, Set<String>> decided : kept.entrySet()) {
            text.append(decided.getKey()).append('x')
                    .append(decided.getValue().size()).append('/');
        }
        Set<String> held = new TreeSet<String>();
        for (ReadRow read : corpus.readsOn(path.sessionId, task.focused())) {
            String location = SmtLowering.locationKey(read.location());
            if (rests.locations().contains(location)
                    && ClosurePlanner.unrecorded(corpus, path.sessionId,
                    location, read.observedVersion())) {
                held.add(read.endpoint().site());
            }
        }
        return ArtifactIO.digest(text + "\n"
                + corpus.inputShape(path.sessionId, task.focused(),
                corpus.feeders(task), rests.locations(), stated)
                + (domains.isEmpty() ? "" : "\n" + domains)
                + (held.isEmpty() ? "" : "\nheld " + held), 16);
    }

    private static void domains(Corpus corpus, String sessionId, String term,
                                Set<String> into) {
        for (String symbol : corpus.termSymbols(sessionId, term)) {
            RootMintRow root = corpus.rootBySymbol(sessionId, symbol);
            if (root == null || root.kind() != RootKind.INTEGRAL
                    || root.category() != RootCategory.CONFIG) {
                continue;
            }
            RootDomain domain = corpus.domainOf(root);
            into.add(symbol + "[" + domain.min() + "," + domain.max() + "]");
        }
    }

    public static String flip(Candidate candidate) {
        return flip(candidate.task.taskId(), candidate.path.pathId,
                candidate.siteId(), candidate.ordinal(),
                candidate.flippedOutcome());
    }

    static String flip(String taskId, String pathId, String siteId,
                       int ordinal, boolean flippedOutcome) {
        return ArtifactIO.digest(taskId + "|" + pathId + "|" + siteId + "#"
                + ordinal + " -> " + flippedOutcome, 16);
    }

    static String question(Candidate candidate, Corpus.World world,
                           String solverKey, String given) {
        StringBuilder text = new StringBuilder();
        text.append(solverKey).append('\n').append(worldText(world));
        text.append("\nfocused ").append(candidate.task.focused().id())
                .append("\nseed ").append(candidate.task.seedSessionId());
        Set<String> factor = new TreeSet<String>();
        for (OccurrenceAddress member : candidate.task.factor()) {
            factor.add(member.id());
        }
        for (String member : factor) text.append("\nfactor ").append(member);
        text.append('\n').append(given);
        return flip(candidate) + ":" + ArtifactIO.digest(text.toString(), 16);
    }

    public static String obligationId(String taskId, String siteId,
                                      int ordinal, boolean flippedOutcome,
                                      String dependence) {
        return ArtifactIO.digest(taskId + "|" + siteId + "|" + ordinal + "|"
                + flippedOutcome + "|" + dependence, 16);
    }

    public static List<Candidate> candidates(Corpus corpus, List<Task> tasks,
                                             Map<String, Set<String>> flipSites,
                                             Bounds bounds, Branches branches,
                                             Frontier owed,
                                             List<GapRow> gaps, ZkKeys keys) {
        List<List<Corpus.RecordedPath>> cut =
                new ArrayList<List<Corpus.RecordedPath>>();
        List<Integer> tooDeep = new ArrayList<Integer>();
        List<Keyed> offering = new ArrayList<Keyed>();
        Map<String, Corpus.Flip> unstated =
                new LinkedHashMap<String, Corpus.Flip>();
        for (Task task : tasks) {
            List<Corpus.RecordedPath> paths =
                    new ArrayList<Corpus.RecordedPath>();
            int deep = 0;
            for (Corpus.RecordedPath path : smallestWorldFirst(corpus,
                    corpus.pathsOf(task.focused()))) {
                if (!branches.parents(path.sessionId)) continue;
                if (corpus.world(path.sessionId).flips.size()
                        > bounds.maxWorldDepth) {
                    deep++;
                    continue;
                }
                if (!unstated.containsKey(path.sessionId)) {
                    Corpus.Flip withheld =
                            corpus.unstatedFlip(path.sessionId);
                    if (withheld != null) {
                        unstated.put(path.sessionId, withheld);
                    }
                }
                paths.add(path);
                offering.add(new Keyed(task, path, OFFERED));
            }
            cut.add(paths);
            tooDeep.add(deep);
        }
        for (Map.Entry<String, Corpus.Flip> withheld : unstated.entrySet()) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    withheld.getKey(), "WORLD_UNSTATED: the world this "
                            + "replay ran holds the flip "
                            + withheld.getValue().render() + ", and it "
                            + "states no decision of that occurrence: its "
                            + "activation published no row (its root was "
                            + "still running when the run ended), so no flip "
                            + "query cut from it can assert the flip it "
                            + "inherits: none is cut from it, and its "
                            + "pairing flips, which assert no prefix, still "
                            + "are"));
        }
        List<Offered> offers;
        try {
            offers = Parallel.grouped(offering, path -> path.path.sessionId,
                    path -> offered(corpus, path.task,
                            flipSites.get(path.task.taskId()), path.path,
                            keys, !unstated.containsKey(path.path.sessionId)));
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        }
        List<Candidate> candidates = new ArrayList<Candidate>();
        int from = 0;
        for (int task = 0; task < tasks.size(); task++) {
            int to = from + cut.get(task).size();
            candidates.addAll(candidates(tasks.get(task), cut.get(task),
                    offers.subList(from, to), tooDeep.get(task), bounds,
                    owed, gaps));
            from = to;
        }
        return candidates;
    }

    private static final int OFFERED = -1;

    private static final class Offered {
        final List<Candidate> asked = new ArrayList<Candidate>();
        final List<GapRow> gaps = new ArrayList<GapRow>();
        int offChain;
    }

    private static Offered offered(Corpus corpus, Task task,
                                   Set<String> flipSites,
                                   Corpus.RecordedPath path, ZkKeys keys,
                                   boolean flips) {
        Offered offered = new Offered();
        if (flips) {
            for (int index : faultFirst(corpus, path)) {
                DecisionRow decision = path.decisions.get(index);
                if (!FlipQuery.flippable(decision)) {
                    continue;
                }
                if (!keys.flippable(corpus, path.sessionId, decision)) {
                    offered.offChain++;
                    continue;
                }
                if (flipSites == null
                        || !FlipQuery.asks(flipSites, decision)) {
                    continue;
                }
                offered.asked.add(new Candidate(corpus, task, path, index,
                        false));
            }
        }
        offered.asked.addAll(PairingFlip.candidates(corpus, task, path,
                offered.gaps));
        return offered;
    }

    private static List<Candidate> candidates(Task task,
                                              List<Corpus.RecordedPath> paths,
                                              List<Offered> offers,
                                              int tooDeep, Bounds bounds,
                                              Frontier owed,
                                              List<GapRow> gaps) {
        List<Candidate> candidates = new ArrayList<Candidate>();
        int offChain = 0;
        Set<String> offered = new LinkedHashSet<String>();
        int cut = 0;
        int unread = 0;
        for (int at = 0; at < paths.size(); at++) {
            Corpus.RecordedPath path = paths.get(at);
            Offered of = offers.get(at);
            offChain += of.offChain;
            gaps.addAll(of.gaps);
            List<Candidate> owedHere = new ArrayList<Candidate>();
            List<Candidate> flying = new ArrayList<Candidate>();
            int unflipped = 0;
            for (Candidate candidate : of.asked) {
                if (offered.contains(candidate.obligationId)) continue;
                String reason = owed.settled(candidate);
                if (!reason.isEmpty()) {
                    offered.add(candidate.obligationId);
                    gaps.add(GapRow.of(path.sessionId,
                            GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                            candidate.siteId() + "#" + candidate.ordinal()
                                    + " -> " + candidate.flippedOutcome(),
                            reason));
                    continue;
                }
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
            if (owedHere.isEmpty()) continue;
            if (cut >= bounds.maxPathsPerTask) {
                unread++;
                continue;
            }
            cut++;
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
                    "this task has " + (cut + unread) + " recorded "
                            + "path(s) that offer an owed arm and this round "
                            + "planned from " + cut + ": " + unread
                            + " path(s), the ones carrying the largest "
                            + "worlds, wait for a later round"));
        }
        if (offChain > 0) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    task.taskId() + " zk-keys", offChain + " decision(s) of"
                            + " this task's paths decide on store values off"
                            + " the ZooKeeper causal chain alone ("
                            + ZkChain.FILE + "): no flip"));
        }
        return candidates;
    }

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

    private static List<Corpus.RecordedPath> smallestWorldFirst(
            final Corpus corpus, List<Corpus.RecordedPath> paths) {
        List<Corpus.RecordedPath> ordered =
                new ArrayList<Corpus.RecordedPath>(paths);
        ordered.sort(Comparator.comparingInt(
                path -> corpus.world(path.sessionId).flips.size()));
        return ordered;
    }

    private static final class Planted {
        final Map<String, String> roots = new LinkedHashMap<String, String>();
        final Map<String, String> clockDeltas =
                new LinkedHashMap<String, String>();
        final Map<String, String> answers =
                new LinkedHashMap<String, String>();
        final Map<String, String> pairings =
                new LinkedHashMap<String, String>();
        final List<String> unproducible = new ArrayList<String>();
        String refusal = "";
    }

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
                            + "write" : "writer " + Confirmation.writer(write))
                            + ", and the replay runs the world of "
                            + candidate.path.sessionId;
                    return planted;
                }
                planted.pairings.put(Confirmation.id(read.endpoint()),
                        Confirmation.writer(write));
            }
        }
        return planted;
    }

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

    private static String heldToRecording(FlipQuery.Built built,
                                          String pins) {
        StringBuilder held = new StringBuilder();
        for (FlipQuery.WriterChoice choice : built.choices) {
            if (built.modelSymbols.contains(choice.recorded)) {
                held.append("(assert ").append(choice.recorded)
                        .append(")\n");
            }
        }
        return held.length() == 0 ? "" : built.smt2 + pins + held;
    }

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

    public static Candidate locate(Corpus corpus, Obligation obligation) {
        Task task = ClosurePlanner.taskOf(corpus, obligation.taskId());
        if (task == null) return null;
        List<Corpus.RecordedPath> paths = new ArrayList<Corpus.RecordedPath>(
                corpus.pathsOf(task.focused()));
        List<Corpus.RecordedPath> forced =
                corpus.forcedPaths(task.focused());
        paths.addAll(forced);
        for (Corpus.RecordedPath path : paths) {
            if (!path.pathId.equals(obligation.pathId())) continue;
            if (Obligation.pairing(obligation.siteId())) {
                return PairingFlip.locate(corpus, task, path, obligation);
            }
            for (int index = 0; index < path.decisions.size(); index++) {
                DecisionRow decision = path.decisions.get(index);
                if (decision.siteId().equals(obligation.siteId())
                        && decision.ordinal() == obligation.ordinal()) {
                    return new Candidate(task, path, index,
                            obligation.obligationId(), forced.contains(path));
                }
            }
        }
        return null;
    }

    public static List<Candidate> forced(Corpus corpus, Task task) {
        List<Candidate> candidates = new ArrayList<Candidate>();
        for (Corpus.RecordedPath path
                : corpus.forcedPaths(task.focused())) {
            for (int index = 0; index < path.decisions.size(); index++) {
                DecisionRow decision = path.decisions.get(index);
                if (decision.isForced()
                        && decision.concreteOutcome() != decision.outcome()) {
                    candidates.add(new Candidate(corpus, task, path, index,
                            true));
                    break;
                }
            }
        }
        return candidates;
    }

    public static Outcome solve(Corpus corpus, Candidate candidate,
                                Z3 solver, Solved solved, String given,
                                Map<String, ObligationDir.Answer> answered,
                                HardAsk.Model decided) throws IOException {
        if (candidate.pairing()) {
            return PairingFlip.solve(corpus, candidate, given, answered);
        }
        String id = candidate.obligationId;
        DecisionRow decision = candidate.decision;
        FlipQuery.Built built = candidate.forced
                ? FlipQuery.buildForced(corpus, candidate.task,
                candidate.path, candidate.index)
                : FlipQuery.build(corpus, candidate.task, candidate.path,
                candidate.index);
        boolean openArm = !candidate.forced && corpus.openArmFlip(
                candidate.task.focused(), decision.siteId(),
                decision.ordinal(), !decision.outcome());
        List<Corpus.Refuted> refuted = openArm
                ? corpus.refutedWorlds(flip(candidate))
                : Collections.<Corpus.Refuted>emptyList();
        if (built.ok() && !refuted.isEmpty()) {
            built = built.excluding(excluded(corpus, candidate, built,
                    refuted));
        }
        Corpus.World inherited = corpus.world(candidate.path.sessionId);
        String query = built.ok()
                ? Z3.modelQuery(built.smt2, built.modelSymbols) : "";
        String querySha256 = ArtifactIO.sha256(query);
        String question = question(candidate, inherited, built.ok()
                ? "query " + querySha256 : "refused: " + built.refusal, given);
        List<GapRow> gaps = new ArrayList<GapRow>(built.gaps);
        int distinct = Corpus.distinctWorlds(refuted);
        if (distinct >= MAX_REFUTED_WORLDS) {
            return refused(candidate, Verdict.NOT_ADMITTED, REFUTED_BOUND
                    + ": " + distinct + " distinct world(s) its replays"
                    + " refuted, and the flip is not asked again past "
                    + MAX_REFUTED_WORLDS, "", gaps, question, false);
        }
        ObligationDir.Answer earlier = answered.get(question);
        if (earlier != null && earlier.result.refutation() == null
                && !earlier.result.worldUnrefuted()) {
            String detail = (earlier.result.armRefusal() != null
                    ? ObligationResult.ARM_REFUSED + ": " : "")
                    + "question " + question + " was settled "
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
            return refused(candidate, earlier.result.verdict(), detail, "",
                    gaps, question, false);
        }
        if (built.notFlippable()) {
            return refused(candidate, Verdict.UNSAT, built.refusal
                    + ": no root, clock, handoff control or movable read"
                    + " reaches the flipped predicate, and it rests on no"
                    + " held fact: the recording's arm is the only one, so"
                    + " no world of this corpus takes the other on this path",
                    "", gaps, question);
        }
        if (!built.ok()) {
            return refused(candidate, Verdict.NOT_ADMITTED,
                    (built.armRefused ? ObligationResult.ARM_REFUSED + ": "
                            : "") + "the query was refused: "
                            + built.refusal, "", gaps, question);
        }
        long budget = solver.timeoutMillis();
        List<String> rests = new ArrayList<String>();
        for (Corpus.Refuted world : refuted) rests.add(world.digest);
        Solved.Key key = Solved.Key.of(query);
        HardAsk ask = new HardAsk(id, candidate.path.sessionId, question,
                (candidate.forced ? "no world of this corpus takes the"
                        + " forced way to the throw from "
                        : "no world of this corpus takes the other arm"
                        + " at ")
                        + decision.siteId() + "#" + decision.ordinal()
                        + (rests.isEmpty() ? "" : " but the "
                        + rests.size() + " world(s) its replays refuted "
                        + "(WORLD_REFUTED), on which this rests: "
                        + String.join(", ", rests)),
                gaps, built.modelSymbols, querySha256,
                key.of(built.modelSymbols), solved.dir());
        FlipQuery.Built asked = built;
        Z3.Answer answer;
        if (decided == null) {
            answer = solved.answer(key, asked.modelSymbols,
                    () -> solver.ask(asked.smt2, asked.modelSymbols, false));
        } else if (decided.querySha256.equals(ask.querySha256)) {
            answer = Z3.Answer.decided("sat", decided.values);
        } else {
            return refused(candidate, Verdict.NOT_ADMITTED, HARD_MODEL_STALE
                    + ": the hard lane decided query " + decided.querySha256
                    + ", and this corpus builds " + ask.querySha256, query,
                    gaps, question, false);
        }
        Outcome settled = settled(ask, answer, budget, solver, query);
        if (settled != null) return settled;
        Z3 asker = decided == null ? solver
                : solver.alone(decided.budgetMillis, decided.roomMb);
        NearestWorld nearest = NearestWorld.of(text -> solved.answer(
                Z3.modelQuery(text, asked.modelSymbols), asked.modelSymbols,
                () -> asker.ask(text, asked.modelSymbols, false)),
                built.smt2, built.modelSymbols, built.recorded,
                built.flipVariables, answer, decided == null);
        answer = nearest.answer;
        if (!nearest.pins.isEmpty()) {
            query = Z3.modelQuery(built.smt2 + nearest.pins,
                    built.modelSymbols);
        }
        Planted planted = planted(corpus, candidate, built, answer.values(),
                gaps);
        if (!planted.refusal.isEmpty()) {
            return refused(candidate, Verdict.NOT_ADMITTED, planted.refusal,
                    query, gaps, question);
        }
        if (!planted.pairings.isEmpty()) {
            String held = heldToRecording(built, nearest.pins);
            String heldQuery = Z3.modelQuery(held, built.modelSymbols);
            Z3.Answer again = held.isEmpty() ? null
                    : solved.answer(heldQuery, asked.modelSymbols,
                    () -> asker.ask(held, asked.modelSymbols, false));
            if (again != null && again.decided() && again.sat()) {
                Planted recorded = planted(corpus, candidate, built,
                        again.values(), gaps);
                if (recorded.refusal.isEmpty() && plantsNothing(corpus,
                        candidate, built, again.values(), recorded)
                        .isEmpty()) {
                    planted = recorded;
                    query = heldQuery;
                }
            }
        }
        String nothing = plantsNothing(corpus, candidate, built,
                answer.values(), planted);
        if (!nothing.isEmpty()) {
            gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, id,
                    nothing));
            return refused(candidate, Verdict.NOT_ADMITTED, nothing, query,
                    gaps, question);
        }
        Map<String, String> roots =
                overlay(inherited.rootAssignments, planted.roots);
        Map<String, String> clockDeltas =
                overlay(inherited.clockDeltas, planted.clockDeltas);
        Map<String, String> answers =
                overlay(inherited.answers, planted.answers);
        Map<String, String> pairings =
                overlay(inherited.pairings, planted.pairings);
        if (!refuted.isEmpty()) {
            List<Corpus.Flip> flips = new ArrayList<Corpus.Flip>();
            flips.add(new Corpus.Flip(candidate.task.focused().id(),
                    decision.siteId(), decision.ordinal(),
                    candidate.flippedOutcome(), id));
            flips.addAll(inherited.flips);
            String digest = wholeWorldDigest(new Corpus.World(roots,
                    clockDeltas, answers, pairings, flips));
            for (Corpus.Refuted world : refuted) {
                if (world.digest.equals(digest)) {
                    return refused(candidate, Verdict.NOT_ADMITTED,
                            "the model's world " + digest + " is one a"
                                    + " replay of this flip refuted"
                                    + " (obligation " + world.obligationId
                                    + "): never run again", query, gaps,
                            question, false);
                }
            }
        }
        ConfirmMain.Holding holding;
        try {
            holding = ConfirmMain.holding(
                    corpus.session(candidate.path.sessionId), pairings);
        } catch (ConfirmMain.Refused unheld) {
            return refused(candidate, Verdict.NOT_ADMITTED,
                    unheld.getMessage(), query, gaps, question);
        }
        Obligation issued = Obligation.of(id, candidate.task.taskId(),
                candidate.path.pathId, decision.siteId(), decision.ordinal(),
                candidate.flippedOutcome(), roots, answers,
                planted.unproducible);
        Map<String, String> mints = new LinkedHashMap<String, String>();
        Set<String> assigned = new LinkedHashSet<String>(roots.keySet());
        assigned.addAll(clockDeltas.keySet());
        List<String> unmintable = new ArrayList<String>();
        for (String rootId : assigned) {
            RootMintRow mint = corpus.mintOf(candidate.path.sessionId,
                    rootId);
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
                            + ", which neither the recording "
                            + corpus.seedSessionId() + " nor the path's "
                            + "session " + candidate.path.sessionId
                            + " mints, so no occurrence of a "
                            + "replay can be focused to plant it", query,
                    gaps, question);
        }
        return new Outcome(issued, ObligationResult.of(id,
                Verdict.SAT_MODEL_READY, "", "the flip at "
                        + decision.siteId() + "#" + decision.ordinal()
                        + " is reachable under " + roots.size()
                        + " root value(s), " + answers.size()
                        + " answered handoff(s) and " + pairings.size()
                        + " planted pairing(s), planted at " + mints.size()
                        + " mint(s)"),
                query, clockDeltas, mints, inherited.flips, pairings,
                holding, gaps, question, false, openArm, null);
    }

    private static List<String> excluded(Corpus corpus, Candidate candidate,
                                         FlipQuery.Built built,
                                         List<Corpus.Refuted> refuted) {
        String session = candidate.path.sessionId;
        List<String> assertions = new ArrayList<String>();
        for (Corpus.Refuted world : refuted) {
            List<String> chosen = new ArrayList<String>();
            List<String> unstated = new ArrayList<String>();
            for (FlipQuery.WriterChoice choice : built.choices) {
                String selector = choice.recorded;
                for (ReadRow read : choice.reads) {
                    String writer = world.world.pairings.get(
                            Confirmation.id(read.endpoint()));
                    if (writer == null) continue;
                    for (Map.Entry<String, WriteRow> write
                            : choice.writes.entrySet()) {
                        if (write.getValue() != null && Confirmation.writer(
                                write.getValue()).equals(writer)) {
                            selector = write.getKey();
                        }
                    }
                }
                if (selector.isEmpty()
                        || !built.modelSymbols.contains(selector)) {
                    unstated.add("writer choice " + choice.key);
                } else {
                    chosen.add(selector);
                }
            }
            for (Map.Entry<String, String> variable
                    : built.rootVariables.entrySet()) {
                String value = world.world.rootAssignments.get(
                        variable.getValue());
                if (value == null) {
                    value = corpus.rootValue(session, variable.getValue());
                }
                equal(chosen, unstated, variable.getKey(), value,
                        built.sorts.get(variable.getKey()));
            }
            for (Map.Entry<String, String> variable
                    : built.clockVariables.entrySet()) {
                RootMintRow read = corpus.rootOf(session,
                        variable.getValue());
                String delta = world.world.clockDeltas.get(
                        variable.getValue());
                equal(chosen, unstated, variable.getKey(), read == null ? ""
                        : delta == null ? read.hostReading().trim()
                        : instant(read.hostReading(), delta),
                        built.sorts.get(variable.getKey()));
            }
            for (FlipQuery.Control control : built.controls) {
                equal(chosen, unstated, control.variable,
                        world.world.answers.get(control.attachEndpointId),
                        control.sort);
            }
            String named = "; refuted world " + world.digest
                    + " (obligation " + world.obligationId + ", session "
                    + world.sessionId + ")";
            assertions.add(!unstated.isEmpty() || chosen.isEmpty()
                    ? named + ": this query cannot state "
                    + (unstated.isEmpty() ? "any of its choices"
                    : String.join(", ", unstated))
                    + ", so only its digest is refused"
                    : named + "\n(assert (not (and "
                    + String.join(" ", chosen) + ")))");
        }
        return assertions;
    }

    private static void equal(List<String> chosen, List<String> unstated,
                              String variable, String value, String sort) {
        String literal = value == null || value.isEmpty() ? ""
                : SmtText.literal(value, sort);
        if (literal.isEmpty()) {
            unstated.add(variable);
        } else {
            chosen.add("(= " + variable + " " + literal + ")");
        }
    }

    static String answer(String sort, String value) {
        if (!VmTermLowering.Sort.STRING.smt.equals(sort)) return value;
        String text = Z3.javaString(value);
        return text == null ? null : new JsonPrimitive(text).toString();
    }

    static Map<String, String> overlay(Map<String, String> base,
                                               Map<String, String> over) {
        Map<String, String> merged = new LinkedHashMap<String, String>(base);
        merged.putAll(over);
        return merged;
    }
}
