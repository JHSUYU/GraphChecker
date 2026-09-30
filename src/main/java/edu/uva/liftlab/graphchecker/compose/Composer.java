package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.explore.Corpus;
import edu.uva.liftlab.graphchecker.explore.SlotTable;
import edu.uva.liftlab.graphchecker.contract.Family;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.PathEntry;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtLiteral;
import static edu.uva.liftlab.graphchecker.compose.VmTermLowering.smtName;
import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.integralLiteral;

/**
 * One composed query per anchor, factorized per path.  A MERGE, not a
 * reconstruction: every value was propagated inside some replay; nothing
 * here finds writers, links arms by request family, or picks versions.  It
 * ALIGNs the anchor across sessions, MERGEs one disjunct per admitted path,
 * LOWERs through {@link SmtLowering} and GATEs (fail closed).
 *
 * <p>The shape, for anchor A:</p>
 * <pre>
 *   exactly-one(selector_p)                       over admitted paths p
 *   selector_p =&gt; pi_p /\ phi_p /\ reads_p /\ joins_p /\ valuation_p
 *   selector_p =&gt; family(I)   for every interaction I that p's chain reaches
 *   root domains, clock floors, identity axioms
 * </pre>
 *
 * <p>Deliberately NOT global: a path's arrivals, clock readings and
 * valuation are per session (R-PIN); a family sits under its session's
 * selector, so an arm-less family kills only its disjunct; an arm is
 * guarded by its replay's valuation of only the roots its expression
 * depends on (R-GUARD).</p>
 */
public final class Composer {

    /** One valuation of the declared roots: one question for the solver. */
    public static final class Valuation {
        private final int ordinal;
        private final Map<String, String> assignment;
        private final Map<String, String> moved;
        private final List<String> assertions;

        private Valuation(int ordinal, Map<String, String> assignment,
                          Map<String, String> moved,
                          List<String> assertions) {
            this.ordinal = ordinal;
            this.assignment = Collections.unmodifiableMap(assignment);
            this.moved = Collections.unmodifiableMap(moved);
            this.assertions = Collections.unmodifiableList(assertions);
        }

        public int ordinal() {
            return ordinal;
        }

        /** Root id -> the value this valuation gives it. */
        public Map<String, String> assignment() {
            return assignment;
        }

        /** Root id -> its value, for the roots this valuation moved. */
        public Map<String, String> moved() {
            return moved;
        }

        /** The pins, as named assertions the solver conjoins. */
        public List<String> assertions() {
            return assertions;
        }

        @Override
        public String toString() {
            return "valuation " + ordinal
                    + (moved.isEmpty() ? " (recorded)" : " " + moved);
        }
    }

    /** One admitted path, as the composition states it. */
    public static final class Disjunct {
        private final Corpus.RecordedPath path;
        private final String selector;
        private final boolean fatalObserved;
        private final Set<String> interactionIds;

        private Disjunct(Corpus.RecordedPath path, String selector,
                         boolean fatalObserved, Set<String> interactionIds) {
            this.path = path;
            this.selector = selector;
            this.fatalObserved = fatalObserved;
            this.interactionIds = Collections.unmodifiableSet(interactionIds);
        }

        public Corpus.RecordedPath path() {
            return path;
        }

        public String selector() {
            return selector;
        }

        public boolean fatalObserved() {
            return fatalObserved;
        }

        /** Every interaction this path's chain reaches. */
        public Set<String> interactionIds() {
            return interactionIds;
        }
    }

    /** What one composition is, before the solver is asked. */
    public static final class Composition {
        private final OccurrenceAddress anchor;
        private final String body;
        private final List<Disjunct> disjuncts;
        private final List<PathEntry> paths;
        private final List<Family> families;
        private final List<RootDomain> roots;
        private final List<Valuation> valuations;
        private final List<GapRow> gaps;
        private final List<String> clockCells;
        private final Map<String, Long> clockReadings;
        private final Map<String, Long> clockNanos;
        private final Map<String, Set<String>> unattestedRoots;
        private final Map<String, List<String>> observedReads;
        private final Map<String, List<String>> observedArrivals;
        private final Map<String, List<String>> heldArrivals;
        private final Map<String, ComposedFamilies.ArmChoice> armChoices;
        private final String seedSessionId;

        /** The composer's state once every path is composed. */
        private Composition(Composer composed, String body,
                            List<Disjunct> disjuncts, List<PathEntry> paths,
                            List<Valuation> valuations,
                            List<String> clockCells,
                            Map<String, Long> clockReadings,
                            Map<String, Long> clockNanos) {
            this.anchor = composed.anchor;
            this.body = body;
            this.disjuncts = Collections.unmodifiableList(disjuncts);
            this.paths = Collections.unmodifiableList(paths);
            this.families = Collections.unmodifiableList(
                    new ArrayList<Family>(composed.families.values()));
            this.roots = Collections.unmodifiableList(
                    new ArrayList<RootDomain>(composed.roots.values()));
            this.valuations = Collections.unmodifiableList(valuations);
            this.gaps = Collections.unmodifiableList(composed.gaps);
            this.clockCells = Collections.unmodifiableList(clockCells);
            this.clockReadings =
                    Collections.unmodifiableMap(clockReadings);
            this.clockNanos = Collections.unmodifiableMap(clockNanos);
            this.unattestedRoots =
                    Collections.unmodifiableMap(composed.unattestedRoots);
            this.observedReads =
                    Collections.unmodifiableMap(composed.observedReads);
            this.observedArrivals =
                    Collections.unmodifiableMap(composed.observedArrivals);
            this.heldArrivals =
                    Collections.unmodifiableMap(composed.heldArrivals);
            this.armChoices = composed.composedFamilies.armChoices();
            this.seedSessionId = composed.seed();
        }

        public OccurrenceAddress anchor() {
            return anchor;
        }

        /** Declarations and assertions; no {@code check-sat}. */
        public String body() {
            return body;
        }

        /**
         * One question's text: the body (rendered once) plus these
         * assertions.  Legal spelling is reapplied because pins name raw
         * symbols such as {@code CLOCK/...#...}, and a bare {@code #} is a
         * bit-vector literal to z3; the pass is idempotent.
         */
        public String query(List<String> assertions) {
            StringBuilder text = new StringBuilder(body);
            if (assertions != null) {
                for (String assertion : assertions) {
                    if (assertion == null || assertion.isEmpty()) continue;
                    text.append(assertion).append('\n');
                }
            }
            return SmtNames.legalSymbols(text.toString());
        }

        public List<Disjunct> disjuncts() {
            return disjuncts;
        }

        public List<PathEntry> paths() {
            return paths;
        }

        public List<Family> families() {
            return families;
        }

        public List<RootDomain> roots() {
            return roots;
        }

        public List<Valuation> valuations() {
            return valuations;
        }

        public List<GapRow> gaps() {
            return gaps;
        }

        /** Every clock cell the formula declares. */
        public List<String> clockCells() {
            return clockCells;
        }

        /** Clock cell -> one instant some session read it at. */
        public Map<String, Long> clockReadings() {
            return clockReadings;
        }

        /** Clock cell -> its clock's tick in nanoseconds
         *  ({@code RootMintRow#clockNanos}). */
        public Map<String, Long> clockNanos() {
            return clockNanos;
        }

        /** Interaction -> the declared roots its unattested arms mention. */
        public Map<String, Set<String>> unattestedRoots() {
            return unattestedRoots;
        }

        /**
         * Path id -> the interleaving that path's anchor reads actually
         * took: each STATE family's arm the run took
         * ({@link ComposedFamilies#stateFamilies}).
         */
        public List<String> observedReads(String pathId) {
            return asserted(observedReads.get(pathId));
        }

        /**
         * Path id -> the values that path's ANCHOR's attaches actually
         * received: the wire slots a MESSAGE_PAIRING_FLIPPED witness replaces.
         */
        public List<String> observedArrivals(String pathId) {
            return asserted(observedArrivals.get(pathId));
        }

        /**
         * Every path held, under its selector, to the pairing its own run
         * had (observed reads and received arrivals).  Part of "the run as
         * it happened": without it a healthy path can reach the fatal arm at
         * the recorded valuation through a delivery its run never took.
         */
        public List<String> recordedPairings() {
            List<String> held = new ArrayList<String>();
            for (Disjunct disjunct : disjuncts) {
                List<String> terms = new ArrayList<String>();
                List<String> reads = observedReads.get(disjunct.path().pathId);
                List<String> arrivals =
                        heldArrivals.get(disjunct.path().pathId);
                if (reads != null) terms.addAll(reads);
                if (arrivals != null) terms.addAll(arrivals);
                if (terms.isEmpty()) continue;
                held.add("(assert (=> " + disjunct.selector() + " "
                        + VmTermLowering.and(terms) + "))");
            }
            return held;
        }

        private static List<String> asserted(List<String> terms) {
            List<String> asserted = new ArrayList<String>();
            if (terms == null) return asserted;
            for (String term : terms) asserted.add("(assert " + term + ")");
            return asserted;
        }

        public String seedSessionId() {
            return seedSessionId;
        }

        /**
         * Every family ARM selector, so a claim can say which delivery of a
         * slot the witness model used.
         */
        public List<String> armSelectors() {
            return new ArrayList<String>(armChoices.keySet());
        }

        /** The delivery one arm selector stands for, or null. */
        public ComposedFamilies.ArmChoice arm(String selector) {
            return armChoices.get(selector);
        }

        /** Every selector, for reading which disjunct a model selected. */
        public List<String> selectors() {
            return Composer.selectors(disjuncts);
        }

        /** The disjunct one selector names, or null. */
        public Disjunct bySelector(String selector) {
            for (Disjunct disjunct : disjuncts) {
                if (disjunct.selector().equals(selector)) return disjunct;
            }
            return null;
        }
    }

    private final Corpus corpus;
    private final OccurrenceAddress anchor;
    private final Map<String, RootDomain> declaredDomains;
    private final int maxValuations;
    private final SmtLowering lowering;
    private final List<GapRow> gaps = new ArrayList<GapRow>();
    private final Map<String, Family> families =
            new LinkedHashMap<String, Family>();
    /** Root id -> the domain the case and the recording give it. */
    private final Map<String, RootDomain> roots =
            new LinkedHashMap<String, RootDomain>();
    /** The one family-arm rule, shared with the flip solver. */
    private final Arms arms;
    /**
     * Interaction -> the declared roots an UNATTESTED arm of it mentions.
     * Such an arm has no producer path condition, so a witness may not move
     * a root inside it (R-I5).
     */
    private final Map<String, Set<String>> unattestedRoots =
            new LinkedHashMap<String, Set<String>>();
    /** Path id -> the family arms its anchor reads took. */
    private final Map<String, List<String>> observedReads =
            new LinkedHashMap<String, List<String>>();
    /**
     * Path id -> what every attach a family binds received, anchor and
     * upstream ({@link Composition#recordedPairings}).  Not what a mechanism
     * is named by: upstream arrivals are consequences of roots and clocks.
     */
    private final Map<String, List<String>> heldArrivals =
            new LinkedHashMap<String, List<String>>();
    /** Path id -> what the anchor's attaches received. */
    private final Map<String, List<String>> observedArrivals =
            new LinkedHashMap<String, List<String>>();
    /** This epoch's skeleton: which interactions have a slot (R-I6). */
    private SlotTable slots;
    /** Sessions whose pairing replaces a slot's: their arms are not ours. */
    private final Set<String> replacing = new LinkedHashSet<String>();
    /** What refused the first path that reached the anchor, or "". */
    private String firstRefusal = "";
    /** How the alternatives of one slot read in SMT. */
    private final ComposedFamilies composedFamilies;

    private Composer(Corpus corpus, OccurrenceAddress anchor,
                     Map<String, RootDomain> declaredDomains,
                     int maxValuations) {
        this.corpus = corpus;
        this.anchor = anchor;
        this.declaredDomains = declaredDomains == null
                ? Collections.<String, RootDomain>emptyMap()
                : declaredDomains;
        this.maxValuations = maxValuations <= 0 ? 64 : maxValuations;
        this.lowering = new SmtLowering(corpus.declaredSymbols());
        this.arms = new Arms(corpus);
        this.composedFamilies = new ComposedFamilies(this, corpus, arms,
                lowering, families, unattestedRoots, replacing, gaps);
    }

    /** This epoch's skeleton, for the relocated family bodies. */
    SlotTable slots() {
        return slots;
    }

    /** Composes the declared occurrence; a missing one is a claim, not a
     *  crash. */
    public static Composition compose(Corpus corpus,
                                      OccurrenceAddress anchor,
                                      Map<String, RootDomain> declaredDomains,
                                      int maxValuations) {
        return new Composer(corpus, anchor, declaredDomains, maxValuations)
                .run();
    }

    private Composition run() {
        // One symbol for two roots makes paths unsat; refuse it.
        for (Map.Entry<String, Set<String>> collision
                : corpus.collidingRootSymbols().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                    collision.getKey(), "one solver name for "
                            + collision.getValue().size() + " roots: "
                            + collision.getValue());
        }

        // A session read short would hide missing decisions.
        for (SessionReader session : corpus.sessions()) {
            if (session.incomplete().isEmpty()) continue;
            gap(GapKind.SESSION_INCOMPLETE, GapClass.BLOCKING,
                    session.sessionId(), "this session could not be read "
                            + "whole: " + session.incomplete());
        }

        // A verdict is the session's own row; the wave's aggregate copy is
        // checked against it, and a disagreement is BLOCKING.
        for (SessionReader session : corpus.sessions()) {
            for (ObligationResult settled : session.obligations()) {
                ObligationResult wave =
                        corpus.waveVerdict(settled.obligationId());
                if (wave == null || wave.verdict() == settled.verdict()) {
                    continue;
                }
                gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                        settled.obligationId(), "the replay that ran this "
                                + "obligation states " + settled.verdict()
                                + " in session " + session.sessionId()
                                + " and the wave's own file states "
                                + wave.verdict() + ", so what it settled is "
                                + "stated twice and differently");
            }
        }

        // Exactly one session must STATE role SEED (manifest.json); never
        // infer it from "focused nothing".
        List<String> seeds = corpus.seedSessionIds();
        if (seeds.size() != 1 && !corpus.sessions().isEmpty()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, seeds.toString(),
                    seeds.isEmpty()
                            ? "no session of this corpus states role SEED, "
                            + "so none of them is the recording"
                            : seeds.size() + " sessions of this corpus state "
                            + "role SEED, so which one is the recording has "
                            + "no answer");
        }

        // The skeleton first: a replacing session's rows must not reach a
        // family.
        try {
            slots = SlotTable.read(corpus.iteration());
        } catch (java.io.IOException | RuntimeException unreadable) {
            // Unreadable skeleton: named, and composition fails closed.
            slots = null;
            gap(GapKind.TOPOLOGY_DIVERGENCE, GapClass.BLOCKING,
                    SlotTable.FILE, "this epoch's slot table could not be "
                            + "read: " + unreadable);
        }
        if (slots != null) {
            for (SlotTable.Replacement replacement
                    : slots.replacements(corpus)) {
                // FAIL CLOSED ON THE ARMS, OPEN ON THE CLAIM: its arms never
                // reach a family, but only an ADMITTED replay's replacement
                // blocks ({@link SessionReader#admitted}).
                replacing.add(replacement.sessionId);
                gaps.add(GapRow.of(replacement.sessionId,
                        GapKind.TOPOLOGY_DIVERGENCE, replacement.cls(),
                        replacement.consumerEndpointId,
                        replacement.detail()));
            }
        }

        List<Disjunct> disjuncts = new ArrayList<Disjunct>();
        List<PathEntry> entries = new ArrayList<PathEntry>();
        List<Corpus.RecordedPath> admitted = admit();
        int ordinal = 0;
        for (Corpus.RecordedPath path : admitted) {
            Disjunct disjunct = compose(path, ordinal);
            if (disjunct != null) {
                disjuncts.add(disjunct);
                entries.add(PathEntry.of(path.pathId, path.sessionId,
                        disjunct.selector(), disjunct.fatalObserved()));
                ordinal++;
            }
        }
        if (disjuncts.isEmpty()) {
            // Say which absence: nothing reached, or all were refused.
            gap(GapKind.ADMISSION_GAP, GapClass.BLOCKING, anchor.render(),
                    admitted.isEmpty()
                            ? "no session of this corpus published a path "
                            + "that reached the declared occurrence"
                            : admitted.size() + " paths reached the anchor "
                            + "and all were refused: " + (firstRefusal
                            .isEmpty() ? "no refusal was named"
                            : firstRefusal));
        } else {
            List<String> selectors = selectors(disjuncts);
            lowering.assertNamed("target_path_partition",
                    Arms.exactlyOne(selectors));
            // OR over selectors = OR_p (pi_p and phi_p), since each path
            // asserts selector => its conjunction.
            lowering.assertNamed("fatal_target",
                    VmTermLowering.or(selectors));
        }

        composedFamilies.outsideTheClosure(disjuncts);

        List<String> clockCells = new ArrayList<String>();
        Map<String, Long> clockReadings = new LinkedHashMap<String, Long>();
        Map<String, Long> clockNanos = new LinkedHashMap<String, Long>();
        clocks(clockCells, clockReadings, clockNanos);
        domains();
        lowering.assertIdentitiesDistinct();
        // Corpus inconsistencies (one name, two sorts; one truncated name,
        // two identities) are BLOCKING gaps, not exceptions.
        for (Map.Entry<String, String> conflict
                : lowering.sortConflicts().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                    conflict.getKey(), "this corpus states one solver name "
                            + "at two sorts: " + conflict.getValue());
        }
        for (Map.Entry<String, String> collision
                : lowering.nameCollisions().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                    collision.getKey(), "one solver name for two "
                            + "identities of this corpus: "
                            + collision.getValue());
        }
        for (Map.Entry<String, String> cut : lowering.cuts().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, cut.getKey(),
                    cut.getValue().isEmpty()
                            ? "the propagation did not carry this value"
                            : cut.getValue());
        }
        for (Map.Entry<String, String> pinned
                : lowering.pinnedLeaves().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    "UndeclaredSymbolPinned:" + pinned.getKey(), "no row of "
                            + "this corpus declares this symbol and its node "
                            + "states it returned " + pinned.getValue()
                            + ": it is that value, and what it was computed "
                            + "from is not in the formula");
        }

        // Valuations before the body: the body declares what pins reach.
        List<Valuation> valuations = valuations();
        List<String> pins = new ArrayList<String>();
        for (Valuation valuation : valuations) {
            pins.addAll(valuation.assertions());
        }
        return new Composition(this, lowering.body(pins), disjuncts, entries,
                valuations, clockCells, clockReadings, clockNanos);
    }

    // ------------------------------------------------------------------
    // Admission.
    // ------------------------------------------------------------------

    /**
     * Every session's path that reached the anchor.  The declared occurrence
     * is always the anchor; a session without a target row is an admission
     * gap, never a reason to elect another occurrence.
     */
    private List<Corpus.RecordedPath> admit() {
        List<Corpus.RecordedPath> admitted =
                new ArrayList<Corpus.RecordedPath>();
        List<TargetRow> targets = corpus.targetsOn(anchor);
        if (targets.isEmpty()) {
            gap(GapKind.DECLARATION_MISSING, GapClass.BLOCKING,
                    anchor.render(), "no session of this corpus published a "
                            + "target row for the declared occurrence");
            return admitted;
        }
        for (TargetRow target : targets) {
            Corpus.RecordedPath path = corpus.path(target.sessionId(),
                    anchor);
            if (!target.reachedAnchor()) {
                gap(GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        target.sessionId(), "this session ran the occurrence "
                                + "and did not reach the anchor");
                continue;
            }
            if (path == null) {
                gap(GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        target.sessionId(), "this session reached the anchor "
                                + "and published no path at the occurrence");
                continue;
            }
            if (!settled(target.sessionId())) continue;
            admitted.add(path);
        }
        return admitted;
    }

    /**
     * Whether this session's OWN rows admit the obligation it ran (the
     * replay owns the verdict).  A refused obligation's path is the
     * recording again under a valuation the run did not take, so it is no
     * disjunct.  A SEED admits itself; an obligation the manifest names and
     * no row settles is BLOCKING.
     */
    private boolean settled(String session) {
        SessionReader reader = corpus.session(session);
        if (reader == null || reader.seed()) return true;
        Set<String> stated = new LinkedHashSet<String>();
        // {@link SessionReader#admitted} decides; this only names refusals.
        boolean admitted = reader.admitted();
        for (ObligationResult result : reader.obligations()) {
            stated.add(result.obligationId());
            if (result.verdict() == Verdict.ADMITTED) continue;
            gap(GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC, session,
                    "this replay states " + result.verdict() + " for the "
                            + "obligation it ran (" + result.obligationId()
                            + "): " + result.detail());
        }
        List<String> asked = reader.manifest() == null
                ? Collections.<String>emptyList()
                : reader.manifest().obligationIds();
        for (String obligation : asked) {
            if (stated.contains(obligation)) continue;
            admitted = false;
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, obligation,
                    "session " + session + " states it ran this obligation "
                            + "and publishes no verdict for it, so what it "
                            + "settled is not in this corpus");
        }
        return admitted;
    }

    // ------------------------------------------------------------------
    // One path.
    // ------------------------------------------------------------------

    private Disjunct compose(Corpus.RecordedPath path, int ordinal) {
        String session = path.sessionId;
        TargetRow target = corpus.target(session, anchor);
        if (target == null) return null;
        String selector = "path_selector__" + ordinal + "__"
                + ArtifactIO.digest(path.pathId, 10);
        lowering.declare(selector, Sort.BOOL);
        SmtLowering.SessionJoin rows = corpus.join(session);
        lowering.begin(session, rows, corpus.expressions(session));

        List<String> terms = new ArrayList<String>();
        List<GapRow> refusals = new ArrayList<GapRow>();
        List<ReadRow> joined = new ArrayList<ReadRow>();
        List<String> observed = new ArrayList<String>();
        Map<String, String> joins = new LinkedHashMap<String, String>();

        // (0a) THE CLOSURE (P3): the occurrences of this session the joins
        //      reach, and the seq each prefix runs to.  Row-level, before
        //      any lowering.
        Map<String, Long> reached = closure(session, anchor, target.seq(),
                null);
        // (0a') What phi rests on (constraint independence): conditions and
        //       reads sharing no variable with phi or a root stay out.
        List<DecisionRow> conditions = before(path.decisions, target.seq());
        conditions.addAll(reachedConditions(session, reached));
        Independence relevant = independence(session,
                Collections.singletonList(target.phiTerm()), reached,
                conditions);

        // (0b) Reads whose value the row states outright, bound BEFORE any
        //      lowering so every leaf naming them resolves, not just later
        //      ones.
        Set<String> answered = new LinkedHashSet<String>();
        statedReads(session, reached.keySet(), relevant, rows, refusals,
                joins, answered);

        // (1) The valuation this replay ran under, for every VARIED root
        //     (a root may be written and never branched on).  Declared roots
        //     this session did NOT mint are answered in (1b), once the
        //     path's terms are whole.
        Map<String, Set<String>> unminted =
                new LinkedHashMap<String, Set<String>>();
        terms.addAll(valuationOf(session, refusals, unminted));

        // (2) Each anchor handoff: the obligation's answer if any, else
        //     nothing (its family binds it; collected in `bound`).  Never a
        //     recorded literal.
        Set<String> interactionIds = new LinkedHashSet<String>();
        Set<String> handoffs = new LinkedHashSet<String>();
        List<AttachRow> bound = new ArrayList<AttachRow>();
        terms.addAll(handoffReads(session, interactionIds, handoffs,
                refusals, bound));

        // (3) State joins, read := observed write's expression, kept by
        //     symbol: a read with family alternatives must not also be
        //     asserted here.
        stateJoins(session, reached.keySet(), relevant, rows, refusals,
                joined, joins, answered);

        // (4) pi_p: decisions STRICTLY BEFORE the target's seq.  The anchor
        //     decision shares the target's seq; including it would
        //     contradict phi on every healthy path.
        terms.addAll(prefix(path.decisions, target.seq(), "decision ",
                relevant, refusals));

        // (4b) P3: the prefix of every OTHER occurrence the joins reach,
        //      strictly before the write that reached it: a joined value
        //      without its producer's decisions has no reason (and clock
        //      readings live only there).  Per session, already under this
        //      path's valuation; a handoff producer's prefix is stated inside
        //      its family ({@link #prefix}).
        terms.addAll(closureConditions(session, reached, relevant,
                refusals));

        // (5) phi_p is the FATAL arm as published; never re-derive its
        //     polarity.  No predicate is a concrete branch (invariant 9):
        //     the arm this run took is the whole of phi_p, and a healthy one
        //     is no path to the fatal arm in any world.
        String subject = "phi of " + anchor.render();
        if (target.phiTerm() == null || target.phiTerm().isEmpty()) {
            if (target.observedFatal()) {
                terms.add("true");
            } else {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, subject, "the anchor decided "
                                + "concretely on its healthy arm, so no root "
                                + "of this path reaches the fatal one"));
            }
        } else {
            String phi = lowering.statedTerm(target.phiTerm(),
                    "phi:" + subject);
            if (!phi.isEmpty() && !unknown(phi, refusals, subject)) {
                terms.add(phi);
            }
        }

        // (5b) Every OTHER handoff the conjunction reaches (via joins, pi,
        //      phi), by the same rules as (2).
        List<String> reaching = new ArrayList<String>(terms);
        reaching.addAll(joins.values());
        terms.addAll(reachedHandoffs(session, reaching, interactionIds,
                handoffs, refusals, bound));

        // Read BEFORE end() forgets them: any refusal drops the whole path
        // (it would otherwise rest on a free constant).
        List<String> refused = new ArrayList<String>(
                lowering.openRefusals());
        terms.addAll(lowering.end());

        // (1b) Refuse the path only if its own terms name a declared root
        //      this session never minted ({@link #unstatedRoots}).
        unstatedRoots(session, unminted, terms, joins, refusals);
        for (String refusal : refused) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, refusal,
                    "this path rests on a value the recording does not "
                            + "state, so it is not in the disjunction"));
        }
        if (!refusals.isEmpty()) {
            refused(refusals);
            return null;
        }

        // (6) Families: one selector per (producer occurrence, session) for
        //     every interaction reached, under this path's selector.  If no
        //     single session could make all deliveries the path took (R3c),
        //     the path is dropped.
        List<String> familyTerms = new ArrayList<String>();
        List<GapRow> unproducible = new ArrayList<GapRow>();
        if (!composedFamilies.closeFamilies(ordinal, selector, session,
                interactionIds, bound, familyTerms, unproducible)) {
            refused(unproducible);
            return null;
        }
        // (7) And the STATE families: which writer the read may have seen.
        //     A read a family gives alternatives to takes its value there.
        Set<String> chosen = composedFamilies.stateFamilies(path,
                ordinal, selector, joined, joins, interactionIds,
                familyTerms, observed);
        // (8) And the state joins this conjunction ASKS ABOUT.
        terms.addAll(statedJoins(joins, chosen, terms, familyTerms));

        lowering.assertNamed("path_fatal__" + ordinal,
                "(=> " + selector + " " + VmTermLowering.and(terms) + ")");
        observedReads.put(path.pathId, observed);
        observedArrivals.put(path.pathId,
                arrivals(corpus.attachesOn(session, anchor)));
        heldArrivals.put(path.pathId, arrivals(bound));
        return new Disjunct(path, selector, target.observedFatal(),
                interactionIds);
    }

    private static List<String> selectors(List<Disjunct> disjuncts) {
        List<String> selectors = new ArrayList<String>();
        for (Disjunct disjunct : disjuncts) selectors.add(disjunct.selector());
        return selectors;
    }

    /** Files one path's refusals; the first names an empty disjunction. */
    private void refused(List<GapRow> rows) {
        gaps.addAll(rows);
        if (firstRefusal.isEmpty() && !rows.isEmpty()) {
            GapRow first = rows.get(0);
            firstRefusal = first.kind() + " " + first.subject() + ": "
                    + first.detail();
        }
    }

    /**
     * The state joins THIS CONJUNCTION ASKS ABOUT, to a fixed point seeded
     * by the path's terms and its family terms.  An unreached join
     * constrains nothing but drags its theory (e.g. {@code assoc_put}) into
     * the query, which can cost z3 its whole budget.  Same rule as
     * {@link SmtLowering#body}, applied to assertions.
     */
    List<String> statedJoins(Map<String, String> joins,
                                     Set<String> chosen, List<String> terms,
                                     List<String> familyTerms) {
        Map<String, String> pending = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> join : joins.entrySet()) {
            // A family-chosen read takes its value from the family.
            if (chosen.contains(join.getKey())) continue;
            pending.put(join.getKey(), join.getValue());
        }
        Set<String> asked = new LinkedHashSet<String>();
        List<String> reaching = new ArrayList<String>(terms);
        reaching.addAll(familyTerms);
        while (!reaching.isEmpty()) {
            Set<String> reached = lowering.reachedSymbols(reaching);
            reaching = new ArrayList<String>();
            for (String symbol : reached) {
                String join = pending.remove(symbol);
                if (join == null) continue;
                asked.add(symbol);
                reaching.add(join);
            }
        }
        // In row order, so runs compare stably.
        List<String> stated = new ArrayList<String>();
        for (Map.Entry<String, String> join : joins.entrySet()) {
            if (asked.contains(join.getKey())) stated.add(join.getValue());
        }
        return stated;
    }

    /**
     * What this replay ran every varied root at: {@link Corpus#rootValue}
     * (the mint's reading, or the obligation's assignment where the replay
     * PLANTED it; a flip mint states no recorded value).
     */
    private List<String> valuationOf(String session,
                                     List<GapRow> refusals,
                                     Map<String, Set<String>> unminted) {
        List<String> valuation = new ArrayList<String>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow any = corpus.anyRoot(entry.getKey());
            RootMintRow row = corpus.root(entry.getKey(), session);
            if (any == null || any.kind() == RootKind.CLOCK) continue;
            if (row == null) {
                // Not minted here: never pin another session's reading.
                // Collect its symbols; {@link #unstatedRoots} refuses only
                // if this path's own terms name one.  Do not ask
                // `lowering.declared`: the query spans earlier paths.
                if (any.declared()) {
                    Set<String> symbols = new LinkedHashSet<String>();
                    for (RootMintRow mint : entry.getValue()) {
                        if (mint != null && !mint.symbol().isEmpty()) {
                            symbols.add(mint.symbol());
                        }
                    }
                    if (!symbols.isEmpty()) {
                        unminted.put(any.rootId(), symbols);
                    }
                }
                continue;
            }
            String ran = corpus.rootValue(session, row.rootId());
            // Minted but no value stated: the disjunct would decide
            // nothing.  Not gated on the symbol being declared (circular:
            // only this pin declares a marker).
            if (ran.isEmpty() && row.declared()) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, any.rootId(),
                        "this replay minted a declared root and states no "
                                + "value it ran it at: its mint states none "
                                + "and no obligation it ran under assigns "
                                + "it"));
                continue;
            }
            // Mint and obligation disagree: refuse.
            String read = corpus.rootReading(session, row.rootId());
            if (!read.isEmpty() && !read.equals(ran)) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, any.rootId(),
                        "this session's mint states \"" + read + "\" and the "
                                + "obligation it ran under assigns \"" + ran
                                + "\", so what this replay ran the root at "
                                + "is stated twice and differently"));
                continue;
            }
            if (!corpus.varied(row.rootId())) continue;
            lowering.declareStated(row.symbol(),
                    row.kind() == RootKind.MARKER ? Sort.BOOL : Sort.INT);
            // A declared domain is a window around THIS replay's reading;
            // pinning the exact value would answer the question in advance.
            String window = windowOf(row);
            if (!window.isEmpty()) {
                valuation.add(window);
                continue;
            }
            String literal = smtLiteral(ran);
            if (literal.isEmpty()) continue;
            valuation.add("(= " + row.symbol() + " " + literal + ")");
        }
        return valuation;
    }

    /**
     * Refuses the path for each declared root it did not mint whose symbol
     * its OWN terms (and joins) name; otherwise that quantity would be free.
     * Roots it never names are not refused.
     *
     * <p>"Names" uses both {@link SmtLowering#reachedSymbols} (leaves, through
     * container bodies) and {@link SmtNames#names} (symbols written into
     * published text), whole tokens only.</p>
     */
    private void unstatedRoots(String session,
                               Map<String, Set<String>> unminted,
                               List<String> terms,
                               Map<String, String> joins,
                               List<GapRow> refusals) {
        if (unminted.isEmpty()) return;
        List<String> texts = new ArrayList<String>(terms);
        texts.addAll(joins.values());
        Set<String> named = lowering.reachedSymbols(texts);
        for (String text : texts) named.addAll(SmtNames.names(text));
        for (Map.Entry<String, Set<String>> root : unminted.entrySet()) {
            for (String symbol : root.getValue()) {
                if (!named.contains(symbol)) continue;
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, root.getKey(),
                        "this path's own terms name this declared root ("
                                + symbol + ") and this session minted no "
                                + "value for it, so what the path rests on "
                                + "is stated by no row of the execution it "
                                + "is about"));
                break;
            }
        }
    }

    /** One declared root's window around THIS session's reading, or "". */
    private String windowOf(RootMintRow row) {
        if (!row.declared() || row.kind() == RootKind.MARKER) return "";
        RootDomain domain = domainOf(row);
        String min = domain.min();
        String max = domain.max();
        if (min == null || max == null || integralLiteral(min).isEmpty()
                || integralLiteral(max).isEmpty()) {
            return "";
        }
        return window(row.symbol(), min, max);
    }

    /** {@code min <= symbol <= max}: a declared domain as one predicate. */
    private static String window(String symbol, String min, String max) {
        return "(and (>= " + symbol + " " + integralLiteral(min) + ") (<= "
                + symbol + " " + integralLiteral(max) + "))";
    }

    /**
     * What this path read at each of the anchor's handoffs, in order:
     * <ol>
     *   <li>an obligation answered the mint: that value;</li>
     *   <li>an ATTESTED producer delivered it: nothing is conjoined; the
     *       attach joins its FAMILY only (CLOSURE-V2) and takes just its
     *       sort from the delivery ({@link #attestedArrival});</li>
     *   <li>otherwise refused by name.</li>
     * </ol>
     */
    private List<String> handoffReads(String session,
                                      Set<String> interactionIds,
                                      Set<String> handoffs,
                                      List<GapRow> refusals,
                                      List<AttachRow> bound) {
        List<String> reads = new ArrayList<String>();
        for (AttachRow attach : corpus.attachesOn(session, anchor)) {
            handoffRead(session, attach, reads, interactionIds, handoffs,
                    refusals, bound);
        }
        return reads;
    }

    /**
     * Every OTHER handoff this path's conjunction reaches (e.g. a delivered
     * value a joined write put into a container), by the same rules, to a
     * fixed point as in {@link Arms#wireArms}.  Unbound, each would be a free
     * constant.
     */
    private List<String> reachedHandoffs(String session, List<String> terms,
                                         Set<String> interactionIds,
                                         Set<String> handoffs,
                                         List<GapRow> refusals,
                                         List<AttachRow> bound) {
        List<String> reads = new ArrayList<String>();
        List<String> pending = new ArrayList<String>(terms);
        while (!pending.isEmpty()) {
            Set<String> reached = lowering.reachedSymbols(pending);
            pending = new ArrayList<String>();
            for (String name : reached) {
                if (handoffs.contains(name)) continue;
                AttachRow attach = corpus.attach(session, name);
                if (attach == null) continue;
                List<String> stated = new ArrayList<String>();
                handoffRead(session, attach, stated, interactionIds,
                        handoffs, refusals, bound);
                reads.addAll(stated);
                pending.addAll(stated);
            }
        }
        return reads;
    }

    /**
     * One attach, by the three rules, stated once per symbol
     * ({@code handoffs} holds the symbols already bound).
     */
    private void handoffRead(String session, AttachRow attach,
                             List<String> reads, Set<String> interactionIds,
                             Set<String> handoffs, List<GapRow> refusals,
                             List<AttachRow> bound) {
        if (!handoffs.add(attach.symbol())) return;
        Interaction interaction = attach.interaction();
        if (interaction != null) {
            interactionIds.add(interaction.id());
        } else {
            // No known source, so no family: named, and refused below.
            composedFamilies.unpaired(session, attach);
        }
        if (attach.answered()) {
            String literal = smtLiteral(attach.answeredValue());
            if (literal.isEmpty()) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, attach.symbol(),
                        "an answered attach whose value is not a "
                                + "literal: " + attach.answeredValue()));
                return;
            }
            String read = bind(attach.symbol(), literal, attach, refusals);
            if (!read.isEmpty()) reads.add(read);
            return;
        }
        if (attestedArrival(attach)) {
            bound.add(attach);
            return;
        }
        // Never pin the received literal: the question is whether the
        // producer could have delivered another value.  Refuse by name.
        refusals.add(GapRow.of(session, GapKind.UNATTESTED_ARM,
                GapClass.DIAGNOSTIC, attach.symbol(),
                "no session of this corpus states the rows of the producer "
                        + "occurrence this delivery came from, so what was "
                        + "delivered is stated and why is not: this path "
                        + "would have to pin the read to the literal it "
                        + "received"));
    }

    /**
     * One handoff read, at the sort the MINT declared, never the one the
     * value's spelling suggests ("0" fits many sorts).
     */
    private String bind(String symbol, String literal, AttachRow attach,
                        List<GapRow> refusals) {
        Sort sort = scalarSort(attach.javaType(), attach.sessionId(),
                symbol, refusals);
        if (sort == null) return "";
        lowering.declareStated(symbol, sort);
        return "(= " + symbol + " " + literal + ")";
    }

    /**
     * The scalar sort one JVM descriptor denotes, or a named refusal; never
     * a fallback to {@code Ref}, which would leave the value unconstrained.
     */
    private Sort scalarSort(String javaType, String session, String subject,
                            List<GapRow> refusals) {
        Sort sort = JavaSmtSorts.sortOfJava(javaType);
        if (sort.scalar()) return sort;
        refusals.add(GapRow.of(session == null || session.isEmpty()
                        ? COMPOSITION : session, GapKind.UNSTATED_VALUE,
                GapClass.DIAGNOSTIC, subject,
                "the row states the Java type as \""
                        + (javaType == null ? "" : javaType)
                        + "\", which names no scalar this lowering can "
                        + "place"));
        return null;
    }

    /**
     * Whether an ATTESTED arm delivers this arrival; if so, declares the
     * symbol at the arm's sort. States NOTHING about the value: the
     * family ({@link ComposedFamilies#closeFamilies}) binds it, and pinning
     * the recorded delivery here too made paths self-contradictory.
     *
     * <p>Declared HERE, during the path's lowering, or leaves naming it in
     * phi or a join are cut as free.  Attested is the PRODUCER's property
     * ({@link Arms#attestedExports}), from any session that ran it, lowered
     * in that session's scope; never ask the consumer's session.</p>
     */
    private boolean attestedArrival(AttachRow attach) {
        Endpoint producer = attach.producer();
        if (producer == null) return false;
        for (ExportRow export : arms.attestedExports(producer)) {
            Term delivered = composedFamilies.lower(export.sessionId(),
                    export.expressionRef(), "paired-arm");
            if (delivered == null) continue;
            lowering.declareStated(attach.symbol(), delivered.sort);
            return true;
        }
        return false;
    }

    /**
     * Every row of this session that states a value a symbol of this path
     * may be: every MINT ROW of the session wherever published (a mint is
     * identified by its version, see {@link SmtLowering#mintedReadSymbol};
     * a sibling activation may publish it under its own address), then the
     * reads of the reached occurrences.
     */
    private List<ReadRow> statedRows(String session,
                                     Set<String> occurrences) {
        List<ReadRow> rows = new ArrayList<ReadRow>();
        Set<String> stated = new LinkedHashSet<String>();
        SessionReader reader = corpus.session(session);
        // Mint rows first: other reads resolve to the symbols they state.
        if (reader != null) {
            for (ReadRow read : reader.reads()) {
                if (read.mintVersion() >= 0L && read.symbol() != null
                        && !read.symbol().isEmpty()
                        && stated.add(read.symbol())) {
                    rows.add(read);
                }
            }
        }
        // Then the anchor, then reached occurrences in closure order (P3);
        // a symbol is stated by the first row met.
        for (String occurrenceId : occurrences) {
            OccurrenceAddress at = corpus.occurrence(occurrenceId);
            if (at == null) continue;
            for (ReadRow read : corpus.readsOn(session, at)) {
                if (read.symbol() == null || stated.add(read.symbol())) {
                    rows.add(read);
                }
            }
        }
        return rows;
    }

    /**
     * The occurrences this path's joins reach, and each one's cutoff seq:
     * P3, a row-level fixed point over ONE session's log.
     *
     * <p>The start keeps its cutoff (the target observation; widening it
     * would include the anchor decision phi negates).  Any other occurrence
     * is reached at the seq of the write a read joined to, widened by later
     * writes; its reads before the cutoff are joined in turn.</p>
     *
     * <p>P3c: EARLIER VERSIONS of a reached write's location are reached
     * too, since a state is the result of every earlier mutation (e.g. what
     * a map lacks was removed earlier under a clock comparison).  Each
     * (location, version) is handled once.</p>
     */
    Map<String, Long> closure(String session, OccurrenceAddress start,
                              long cutoff, List<WriteRow> seeds) {
        Map<String, Long> reached = new LinkedHashMap<String, Long>();
        reached.put(start.id(), cutoff);
        List<String> pending = new ArrayList<String>();
        pending.add(start.id());
        List<WriteRow> versions = new ArrayList<WriteRow>();
        Set<String> handled = new LinkedHashSet<String>();
        if (seeds != null) {
            for (WriteRow seed : seeds) {
                reach(seed, start, reached, pending, versions, handled);
            }
        }
        while (!pending.isEmpty() || !versions.isEmpty()) {
            while (!pending.isEmpty()) {
                String at = pending.remove(0);
                OccurrenceAddress occurrence = corpus.occurrence(at);
                if (occurrence == null) continue;
                boolean whole = anchor.id().equals(at);
                long cut = reached.get(at);
                for (ReadRow read : corpus.readsOn(session, occurrence)) {
                    if (!whole && read.seq() >= cut) continue;
                    if (read.observedVersion() < 0L) continue;
                    WriteRow write = corpus.writeOf(session,
                            SmtLowering.locationKey(read.location()),
                            read.observedVersion());
                    if (write == null) continue;
                    reach(write, start, reached, pending, versions,
                            handled);
                }
            }
            if (versions.isEmpty()) continue;
            WriteRow write = versions.remove(0);
            String key = SmtLowering.locationKey(write.location());
            for (WriteRow under : corpus.writesOf(session, key)) {
                if (under.version() >= write.version()) continue;
                reach(under, start, reached, pending, versions, handled);
            }
        }
        return reached;
    }

    /**
     * One write this path rests on (joined or an earlier version): its
     * writer is reached and its location's earlier versions queued.
     */
    private void reach(WriteRow write, OccurrenceAddress start,
                       Map<String, Long> reached,
                       List<String> pending, List<WriteRow> versions,
                       Set<String> handled) {
        String writer = write.endpoint().occurrence().id();
        // Never the anchor or the start: their cutoff is fixed.
        if (anchor.id().equals(writer) || start.id().equals(writer)) return;
        if (handled.add(SmtLowering.locationKey(write.location()) + "#"
                + write.version())) {
            versions.add(write);
        }
        Long held = reached.get(writer);
        if (held != null && held.longValue() >= write.seq()) return;
        reached.put(writer, write.seq());
        pending.add(writer);
    }

    /**
     * The decision prefix of every reached occurrence but the anchor's,
     * by the same rule as the anchor's pi; undeclared names are refused.
     */
    List<String> closureConditions(String session,
                                   Map<String, Long> reached,
                                   Independence relevant,
                                   List<GapRow> refusals) {
        List<String> conditions = new ArrayList<String>();
        for (Map.Entry<String, Long> entry : reached.entrySet()) {
            if (anchor.id().equals(entry.getKey())) continue;
            OccurrenceAddress at = corpus.occurrence(entry.getKey());
            if (at == null) continue;
            conditions.addAll(prefix(corpus.decisionsOf(session, at),
                    entry.getValue().longValue(), "join-pi ", relevant,
                    refusals));
        }
        return conditions;
    }

    /** The decisions of every reached occurrence but the anchor, each
     *  before its cutoff: what {@link #closureConditions} may state. */
    List<DecisionRow> reachedConditions(String session,
                                        Map<String, Long> reached) {
        List<DecisionRow> conditions = new ArrayList<DecisionRow>();
        for (Map.Entry<String, Long> entry : reached.entrySet()) {
            if (anchor.id().equals(entry.getKey())) continue;
            OccurrenceAddress at = corpus.occurrence(entry.getKey());
            if (at == null) continue;
            conditions.addAll(before(corpus.decisionsOf(session, at),
                    entry.getValue().longValue()));
        }
        return conditions;
    }

    /** The decisions strictly before {@code seq}. */
    private static List<DecisionRow> before(List<DecisionRow> decisions,
                                            long seq) {
        List<DecisionRow> earlier = new ArrayList<DecisionRow>();
        for (DecisionRow decision : decisions) {
            if (decision.seq() < seq) earlier.add(decision);
        }
        return earlier;
    }

    /** What {@code seeds} rest on among these conditions and the reads of
     *  the reached occurrences ({@link Independence}). */
    Independence independence(String session, List<String> seeds,
                              Map<String, Long> reached,
                              List<DecisionRow> conditions) {
        return Independence.of(corpus, session, seeds, conditions,
                statedRows(session, reached.keySet()));
    }

    /**
     * The decisions strictly before {@code before}, polarity applied by
     * {@link Arms#pathCondition} (the rule {@link Arms#wireArms} uses too),
     * lowered in the open scope; a term naming an undeclared symbol is
     * refused by name.
     */
    private List<String> prefix(List<DecisionRow> decisions, long before,
                                String kind, Independence relevant,
                                List<GapRow> refusals) {
        List<String> conditions = new ArrayList<String>();
        for (DecisionRow decision : decisions) {
            if (decision.seq() >= before) continue;
            if (!relevant.keeps(decision)) continue;
            String subject = kind + decision.siteId() + "#"
                    + decision.ordinal();
            String conjunct = lowering.statedTerm(Arms.conjunct(decision),
                    "pi:" + subject);
            if (!Arms.predicate(conjunct)) continue;
            if (unknown(conjunct, refusals, subject)) continue;
            conditions.add(conjunct);
        }
        return conditions;
    }

    /**
     * Read := the value the ROW states, bound before any lowering: the PIN
     * half of {@link #stateJoins}, hoisted so every leaf naming the symbol
     * resolves.  Only for reads neither the write log nor a mint covers
     * (a root's version is its mint's, whatever the run read); rows stating
     * no value are left to the join half.  {@code answered} keeps one
     * refusal per row across both halves.
     */
    void statedReads(String session, Set<String> occurrences,
                     Independence relevant, SmtLowering.SessionJoin join,
                     List<GapRow> refusals, Map<String, String> joins,
                     Set<String> answered) {
        for (ReadRow read : statedRows(session, occurrences)) {
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            if (!relevant.keeps(read)) continue;
            if (joins.containsKey(read.symbol())) continue;
            if (joinable(session, read)) continue;
            if (!"".equals(SmtLowering.mintedReadSymbol(join,
                    read.observedVersion()))) {
                continue;
            }
            pin(session, read, refusals, joins, answered);
        }
    }

    /**
     * Read := the value its own row states, via
     * {@link SmtLowering#statedValue}.  Answers whether the row states a
     * value at all; an unplaceable one is refused by name.
     */
    private boolean pin(String session, ReadRow read,
                        List<GapRow> refusals, Map<String, String> joins,
                        Set<String> answered) {
        String text = read.concreteValue() == null ? ""
                : read.concreteValue().trim();
        if (text.isEmpty()) return false;
        answered.add(read.symbol());
        Term value = lowering.statedValue(text, read.javaType());
        if (value == null) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, read.symbol(),
                    "the row states the value \"" + text + "\" at Java "
                            + "type \"" + (read.javaType() == null ? ""
                            : read.javaType()) + "\", which this lowering "
                            + "places nowhere"));
            return true;
        }
        lowering.pin(read.symbol(), value.sort);
        joins.put(read.symbol(), "(= " + read.symbol() + " " + value.text
                + ")");
        return true;
    }

    /** Whether this session's write log covers the version this read saw. */
    private boolean joinable(String session, ReadRow read) {
        return read.observedVersion() >= 0L
                && corpus.writeOf(session,
                SmtLowering.locationKey(read.location()),
                read.observedVersion()) != null;
    }

    /**
     * Read := THE ONE BINDING RULE ({@link SmtLowering}'s guarded read too):
     * JOIN, the expression of the write version it observed, if it lowers
     * with no refusal; else its MINT; else PIN; else REFUSE.  No "latest
     * write", no choice between writers.  A join that refused is an attempt:
     * dropped when the mint or the pin binds the read, stated beside the
     * read's own refusal when nothing does.
     */
    void stateJoins(String session, Set<String> occurrences,
                    Independence relevant, SmtLowering.SessionJoin join,
                    List<GapRow> refusals, List<ReadRow> joined,
                    Map<String, String> joins, Set<String> answered) {
        for (ReadRow read : statedRows(session, occurrences)) {
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            if (!relevant.keeps(read)) continue;
            // Family alternatives are the anchor's only.
            boolean atAnchor = anchor.id().equals(
                    read.endpoint().occurrence().id());
            String key = SmtLowering.locationKey(read.location());
            WriteRow write = read.observedVersion() < 0L ? null
                    : corpus.writeOf(session, key,
                            read.observedVersion());
            SmtLowering.Attempt<Term> attempt = null;
            if (write != null) {
                JsonObject expression = corpus.session(session).expressions()
                        .expression(write.expressionRef());
                // A cited ref missing from its own table: BLOCKING.
                if (expression == null) {
                    refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                            GapClass.BLOCKING, write.expressionRef(),
                            "a write row of " + key + "@"
                                    + read.observedVersion() + " cites an "
                                    + "expression its session's table does "
                                    + "not hold, so the chain this read "
                                    + "joins to is not in this corpus"));
                    continue;
                }
                attempt = lowering.attempt(expression, null,
                        "state-join:" + key + "@" + read.observedVersion());
                if (attempt.lowered()) {
                    Term value = attempt.value();
                    lowering.declareStated(read.symbol(), value.sort);
                    joins.put(read.symbol(), "(= " + read.symbol() + " "
                            + value.text + ")");
                    if (atAnchor) joined.add(read);
                    continue;
                }
            }
            if (!mintOrPin(session, read, key, write, atAnchor, join,
                    refusals, joined, joins, answered) && attempt != null) {
                lowering.commit(attempt);
            }
        }
    }

    /**
     * The rest of the rule for a read no write joins: its MINT, else PIN,
     * else REFUSE by name.  Answers whether the read is bound.
     */
    private boolean mintOrPin(String session, ReadRow read, String key,
                              WriteRow write, boolean atAnchor,
                              SmtLowering.SessionJoin join,
                              List<GapRow> refusals, List<ReadRow> joined,
                              Map<String, String> joins,
                              Set<String> answered) {
        if (joins.containsKey(read.symbol())) {
            // Pinned at step 0 to what its row states: a version no row
            // wrote, its writer outside every region.  At the anchor a
            // STATE family may still offer the concurrent writers beside
            // what it returned; a mint's version is a root's.
            if (atAnchor && write == null && read.observedVersion() >= 0L
                    && "".equals(SmtLowering.mintedReadSymbol(join,
                    read.observedVersion()))) {
                joined.add(read);
            }
            return true;
        }
        // What the MINT that created this version gave it, keyed by
        // `mintVersion` alone (CONTRACT v2.4), before the value the read
        // returned: a root's version moves with the root.
        String minted = SmtLowering.mintedReadSymbol(join,
                read.observedVersion());
        if (minted == null) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, key + "@" + read.observedVersion(),
                    "two placeholder rows of this session state mint "
                            + "version " + read.observedVersion()
                            + " under different symbols: "
                            + join.mintedReadSymbols(
                            read.observedVersion())));
            return false;
        }
        // This row states the version; bound at step 0.
        if (minted.equals(read.symbol())) return true;
        if (!minted.isEmpty()) {
            Sort sort = lowering.declarations().get(minted);
            // A DECLARED ROOT IS BOUND BY ITS DOMAIN, NOT BY A VALUE.  An
            // ordinary read needs a stated value; a clock mint deliberately
            // states none (pinning it could never show a skew), and
            // {@link #clocks} states its domain.
            RootMintRow root = corpus.rootBySymbol(session, minted);
            if (sort == null && root != null) {
                sort = corpus.declaredSymbols().get(minted);
            }
            if (sort == null || (!lowering.stated(minted) && root == null)) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, minted,
                        "the read row that states this version's symbol "
                                + "states no value for it, and no root of "
                                + "this session mints it, so nothing binds "
                                + "it"));
                return false;
            }
            if (root != null && !lowering.stated(minted)) {
                // So the root's domain lands on the joined symbol.
                lowering.declareStated(minted, sort);
            }
            lowering.declareStated(read.symbol(), sort);
            joins.put(read.symbol(), "(= " + read.symbol() + " " + minted
                    + ")");
            return true;
        }
        // The row's own value (non-joinable rows were asked at step 0, and
        // one it could not place is refused there).
        if (answered.contains(read.symbol())
                || pin(session, read, refusals, joins, answered)) {
            return joins.containsKey(read.symbol());
        }
        refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                GapClass.DIAGNOSTIC, key + "@" + read.observedVersion(),
                (write == null ? "no write of this location at this "
                        + "version in this session"
                        : "the write of this version did not lower (its "
                        + "refusal is stated beside this)")
                        + ", and the recording states no value the read "
                        + "returned"));
        return false;
    }

    /**
     * What this session received at these attaches, one term per symbol.
     * Kept beside the path, not in it: an arrival is a consequence of its
     * producer's roots (R-READ), so pinning it would pin them.
     */
    private List<String> arrivals(List<AttachRow> attaches) {
        List<String> stated = new ArrayList<String>();
        Set<String> seen = new LinkedHashSet<String>();
        for (AttachRow attach : attaches) {
            if (!seen.add(attach.symbol())) continue;
            String literal = smtLiteral(JsonFields.firstNonBlank(
                    attach.answeredValue(), attach.arrival()));
            if (literal.isEmpty()) continue;
            stated.add("(= " + attach.symbol() + " " + literal + ")");
        }
        return stated;
    }

    // ------------------------------------------------------------------
    // Roots, clocks and the enumeration.
    // ------------------------------------------------------------------

    /** Every root the corpus minted, with what the case says it may be. */
    private void domains() {
        int ordinal = 0;
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = seedRow(entry.getValue());
            // A CLOCK's domain is {@link #clocks}'s to state.
            if (row.kind() == RootKind.CLOCK) continue;
            RootDomain domain = domainOf(row);
            roots.put(row.rootId(), domain);
            if (!lowering.declared(row.symbol())) continue;
            // A declared marker is free: nothing to assert.
            if (row.kind() == RootKind.MARKER && row.declared()) continue;
            // A root sessions recorded differently has no corpus-wide
            // window; each path carries its own ({@link #valuationOf}).
            if (corpus.varied(row.rootId())) {
                gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        row.rootId(), "sessions of this corpus recorded "
                                + "this root at different values, so its "
                                + "domain is stated per path and not once");
                continue;
            }
            String min = domain.min();
            String max = domain.max();
            if (min != null && max != null && !min.isEmpty()
                    && !max.isEmpty()) {
                lowering.assertNamed("root_domain__" + ordinal++,
                        window(row.symbol(), min, max));
                continue;
            }
            // No domain: pin to the recording, unless the symbol is also a
            // read (a region input published twice; the join decides).
            if (placeholder(row)) {
                gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        row.rootId(), "placeholder published as root: this "
                                + "symbol is also a read of session "
                                + row.sessionId() + ", so the read states "
                                + "what it is and the mint pins nothing");
                continue;
            }
            String literal = smtLiteral(row.recordedValue());
            if (literal.isEmpty()) continue;
            lowering.assertNamed("root_domain__" + ordinal++,
                    "(= " + row.symbol() + " " + literal + ")");
        }
    }

    /**
     * Whether a mint is a declared region INPUT also published as a root.
     * The read wins (it joins to its writer) and the mint pins nothing.
     */
    private boolean placeholder(RootMintRow row) {
        if (row.declared()) return false;
        RootDomain domain = domainOf(row);
        if (!domain.pinned()) return false;
        for (RootMintRow mint : corpus.roots().get(row.rootId())) {
            if (corpus.read(mint.sessionId(), mint.symbol()) != null) {
                return true;
            }
        }
        return false;
    }

    /**
     * Every declared CLOCK cell the formula names: its domain, its recorded
     * reading, and its place in its node's order.
     *
     * <p>A cell is one per (root, occurrence); its reading is the SEED's.
     * Domain ({@link JavaPrimitiveSmtSemantics#clockDomain}): floor = the
     * reading, ceiling = reading + window, unless {@code root-domains.jsonl}
     * declares bounds (the only way to ask for a backward move).  A cell
     * the seed did not read is domained but has no reading.  EVERY cell is
     * domained, or it is left free.</p>
     *
     * <p>ONE ORDER PER CLOCK OF A NODE: a seed cell is no earlier than the
     * last cell before it (by seq) that read the same clock.  A node reads
     * more than one -- the wall clock and a monotonic one (hdfs-11741's
     * Balancer: {@code Time.now()} for its keys, {@code monotonicNow()}
     * for its SASL user) -- and ordering those against each other made
     * every path false.  One run is far shorter than a clock window, so
     * two readings of one clock share a tick and lie within one window;
     * any other two are two clocks.</p>
     */
    private void clocks(List<String> cells, Map<String, Long> readings,
                        Map<String, Long> ticks) {
        String seed = seed();
        Map<NodeId, List<RootMintRow>> byNode =
                new LinkedHashMap<NodeId, List<RootMintRow>>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = seedRow(entry.getValue());
            if (row.kind() != RootKind.CLOCK
                    || !lowering.declared(row.symbol())) {
                continue;
            }
            long reading;
            try {
                reading = Long.parseLong(row.recordedValue().trim());
            } catch (NumberFormatException notAnInstant) {
                gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        row.rootId(), "the mint of this clock cell states "
                                + "no instant (" + row.recordedValue()
                                + "), so it has no domain and no reading");
                continue;
            }
            String instant = Long.toString(reading);
            cells.add(row.symbol());
            ticks.put(row.symbol(), row.clockNanos());
            RootDomain domain = domainOf(row);
            String floor = domain.min() == null ? instant
                    : integralLiteral(domain.min());
            String ceiling = domain.max() == null
                    ? JavaPrimitiveSmtSemantics.clockSkewCeiling(instant,
                            row.clockNanos())
                    : integralLiteral(domain.max());
            roots.put(row.rootId(), RootDomain.of(row.rootId(),
                    RootKind.CLOCK, row.recordedValue(), floor, ceiling));
            lowering.assertNamed("clock_domain__"
                            + ArtifactIO.digest(row.symbol(), 10),
                    JavaPrimitiveSmtSemantics.clockDomain(row.symbol(),
                            floor, ceiling));
            if (!row.sessionId().equals(seed)) {
                gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        row.rootId(), "this cell reaches the composition "
                                + "and the recording states no reading of "
                                + "it, so no claim can say whether a "
                                + "witness moved it away from what the run "
                                + "read");
                continue;
            }
            readings.put(row.symbol(), reading);
            byNode.computeIfAbsent(row.occurrence().node(),
                    node -> new ArrayList<RootMintRow>()).add(row);
        }
        for (List<RootMintRow> mints : byNode.values()) {
            mints.sort(Comparator.comparingLong(RootMintRow::seq));
            for (int index = 1; index < mints.size(); index++) {
                String later = mints.get(index).symbol();
                long reading = readings.get(later);
                long tick = ticks.get(later);
                long window = JavaPrimitiveSmtSemantics.clockTicks(
                        JavaPrimitiveSmtSemantics.CLOCK_SKEW_WINDOW_NANOS,
                        tick);
                for (int before = index - 1; before >= 0; before--) {
                    String earlier = mints.get(before).symbol();
                    if (ticks.get(earlier) != tick
                            || Math.abs(readings.get(earlier) - reading)
                            > window) {
                        continue;
                    }
                    lowering.assertNamed("clock_order__" + ArtifactIO.digest(
                                    earlier + "|" + later, 10),
                            "(<= " + earlier + " " + later + ")");
                    break;
                }
            }
        }
    }

    /**
     * The session that recorded the run, or null when that has no answer
     * (the corpus's {@code ""} would silently read as "not the seed").
     */
    private String seed() {
        String stated = corpus.seedSessionId();
        return stated == null || stated.isEmpty() ? null : stated;
    }

    private RootMintRow seedRow(List<RootMintRow> rows) {
        String seed = seed();
        if (seed != null) {
            for (RootMintRow row : rows) {
                if (row.sessionId().equals(seed)) return row;
            }
        }
        return rows.get(0);
    }

    /** The case's declaration where there is one, the mint's otherwise. */
    private RootDomain domainOf(RootMintRow row) {
        return RootDomain.resolved(row, declaredDomains);
    }

    /**
     * One question per declared root; ordinal 0 is the run as it happened,
     * then single moves by distance, then pairs.  A declared MARKER flips;
     * an INTEGRAL without a domain is pinned, not enumerated; CLOCKs are not
     * enumerated.  Every skipped root is named: the claim's polarity gate
     * reads which valuations were asked.
     */
    private List<Valuation> valuations() {
        List<String> declared = new ArrayList<String>();
        Map<String, List<String>> alternatives =
                new LinkedHashMap<String, List<String>>();
        for (Map.Entry<String, RootDomain> entry : roots.entrySet()) {
            RootDomain domain = entry.getValue();
            if (domain.kind() == RootKind.CLOCK) continue;
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null || !row.declared()) continue;
            if (!lowering.declared(row.symbol())) {
                // Unnamed by any path: moving it decides nothing, and the pin
                // would name an undeclared constant (a z3 error).
                gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        entry.getKey(), "the case declares this root and no "
                                + "admitted path's formula names it, so no "
                                + "valuation of it was asked");
                continue;
            }
            List<String> values = alternativesOf(domain);
            if (values.isEmpty()) {
                if (domain.kind() == RootKind.MARKER) {
                    gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            entry.getKey(), "a declared marker is free in "
                                    + "{recorded, flipped} by its kind, and "
                                    + "this mint states \""
                                    + domain.recordedValue()
                                    + "\", which is neither polarity, so "
                                    + "there is no flip to ask");
                }
                continue;
            }
            declared.add(entry.getKey());
            alternatives.put(entry.getKey(), values);
        }
        List<Valuation> valuations = new ArrayList<Valuation>();
        Map<String, String> recorded = new LinkedHashMap<String, String>();
        for (String rootId : declared) {
            recorded.put(rootId, roots.get(rootId).recordedValue());
        }
        valuations.add(valuation(0, recorded,
                Collections.<String, String>emptyMap()));
        List<Map<String, String>> moves = new ArrayList<Map<String, String>>();
        for (String rootId : declared) {
            for (String value : alternatives.get(rootId)) {
                Map<String, String> move = new LinkedHashMap<String, String>();
                move.put(rootId, value);
                moves.add(move);
            }
        }
        moves.sort(Comparator.comparingLong(this::distance));
        List<Map<String, String>> pairs =
                new ArrayList<Map<String, String>>();
        for (int first = 0; first < moves.size(); first++) {
            for (int second = first + 1; second < moves.size(); second++) {
                Map<String, String> left = moves.get(first);
                Map<String, String> right = moves.get(second);
                String leftRoot = left.keySet().iterator().next();
                String rightRoot = right.keySet().iterator().next();
                if (leftRoot.equals(rightRoot)) continue;
                Map<String, String> pair =
                        new LinkedHashMap<String, String>(left);
                pair.putAll(right);
                pairs.add(pair);
            }
        }
        moves.addAll(pairs);
        int ordinal = 1;
        for (Map<String, String> move : moves) {
            if (valuations.size() >= maxValuations) break;
            Map<String, String> assignment =
                    new LinkedHashMap<String, String>(recorded);
            assignment.putAll(move);
            valuations.add(valuation(ordinal++, assignment, move));
        }
        return valuations;
    }

    /**
     * How far one move is from the recording: |delta| for numeric domains,
     * 1 per moved root otherwise (e.g. a boolean config).
     */
    private long distance(Map<String, String> move) {
        long total = 0L;
        for (Map.Entry<String, String> entry : move.entrySet()) {
            RootDomain domain = roots.get(entry.getKey());
            if (domain == null) continue;
            String moved = entry.getValue().trim();
            String recorded = domain.recordedValue().trim();
            if (integralLiteral(moved).isEmpty()
                    || integralLiteral(recorded).isEmpty()) {
                total += 1L;
                continue;
            }
            total += new BigInteger(moved)
                    .subtract(new BigInteger(recorded)).abs().longValue();
        }
        return total;
    }

    private Valuation valuation(int ordinal, Map<String, String> assignment,
                                Map<String, String> moved) {
        List<String> assertions = new ArrayList<String>();
        for (Map.Entry<String, String> entry : assignment.entrySet()) {
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null) continue;
            String literal = smtLiteral(entry.getValue());
            if (literal.isEmpty()) continue;
            assertions.add("(assert (! (= " + row.symbol() + " " + literal
                    + ") :named valuation__" + smtName(row.symbol())
                    + "))");
        }
        return new Valuation(ordinal, assignment, moved, assertions);
    }

    /** What else one declared root may be, ordered by how far it is. */
    private List<String> alternativesOf(RootDomain domain) {
        List<String> values = new ArrayList<String>();
        String recorded = domain.recordedValue() == null ? ""
                : domain.recordedValue().trim();
        if (domain.kind() == RootKind.MARKER) {
            if ("true".equals(recorded)) values.add("false");
            else if ("false".equals(recorded)) values.add("true");
            return values;
        }
        if (domain.pinned()) return values;
        String min = domain.min();
        String max = domain.max();
        if (min == null || max == null || integralLiteral(min).isEmpty()
                || integralLiteral(max).isEmpty()) {
            return values;
        }
        BigInteger low = new BigInteger(min.trim());
        BigInteger high = new BigInteger(max.trim());
        BigInteger centre = integralLiteral(recorded).isEmpty()
                ? low : new BigInteger(recorded);
        List<BigInteger> candidates = new ArrayList<BigInteger>();
        for (BigInteger value = low; value.compareTo(high) <= 0;
             value = value.add(BigInteger.ONE)) {
            if (value.equals(centre)) continue;
            candidates.add(value);
            if (candidates.size() >= maxValuations) break;
        }
        candidates.sort(Comparator.comparing(
                value -> value.subtract(centre).abs()));
        for (BigInteger value : candidates) values.add(value.toString());
        return values;
    }

    // ------------------------------------------------------------------
    // Reading a published SMT term.
    // ------------------------------------------------------------------

    /**
     * Whether a published term names something nothing declares; if so the
     * path is refused by the missing names (a free constant would answer a
     * question the execution never asked).
     */
    private boolean unknown(String term, List<GapRow> refusals,
                            String subject) {
        List<String> free = new ArrayList<String>();
        // let-bound names are not free.
        Set<String> bound = SmtNames.letBound(term);
        for (String token : SmtNames.names(term)) {
            if (SmtNames.BUILTIN.contains(token)) continue;
            if (bound.contains(token)) continue;
            if (lowering.defined(token)) continue;
            // A recorded symbol may appear only as text.
            if (lowering.declareStated(token)) continue;
            free.add(token);
        }
        if (free.isEmpty()) return false;
        refusals.add(GapRow.of(COMPOSITION, GapKind.UNSTATED_VALUE,
                GapClass.DIAGNOSTIC, subject,
                "this term names symbols nothing declares: " + free));
        return true;
    }

    /** The session-id field of a gap the COMPOSITION raised. */
    static final String COMPOSITION = "composition";

    void gap(GapKind kind, GapClass cls, String subject,
                     String detail) {
        gaps.add(GapRow.of(COMPOSITION, kind, cls,
                subject == null || subject.trim().isEmpty()
                        ? anchor.render() : subject, detail));
    }
}
