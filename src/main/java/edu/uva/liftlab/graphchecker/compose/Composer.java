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
 * One composed query per anchor, factorized per path.
 *
 * <p>The composition is a merge and not a reconstruction.  Every value in
 * it was propagated symbolically inside some replay and published as that
 * replay's own expression; nothing here finds a writer through a graph,
 * links an arm to a producer by a request family, or picks a version for a
 * read.  What this class does is ALIGN (the anchor's occurrence across
 * sessions), MERGE (one disjunct per admitted path), LOWER (through the one
 * {@link SmtLowering}) and GATE (fail closed on what the recording does not
 * state).</p>
 *
 * <p>The shape, for anchor A:</p>
 * <pre>
 *   exactly-one(selector_p)                       over admitted paths p
 *   selector_p =&gt; pi_p /\ phi_p /\ reads_p /\ joins_p /\ valuation_p
 *   selector_p =&gt; family(I)   for every interaction I that p's chain reaches
 *   root domains, clock floors, identity axioms
 * </pre>
 *
 * <p>Three things are deliberately NOT global.  A path's own arrivals, its
 * clock readings and its replay's valuation are per-session facts, and one
 * session's value asserted for all of them closed every other path (the
 * measured R-PIN defect).  A family binds a symbol one session minted, so
 * it is conjoined under that session's selector: a family with no available
 * arm then kills its own disjunct instead of the whole formula, which is
 * what a globally asserted family did at every flipped-marker valuation.
 * And an arm is guarded by the delivering replay's valuation of ONLY the
 * roots its own delivered expression depends on (R-GUARD).</p>
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
        private final Map<String, Set<String>> unattestedRoots;
        private final Map<String, List<String>> observedReads;
        private final Map<String, List<String>> observedArrivals;
        private final Map<String, ComposedFamilies.ArmChoice> armChoices;
        private final String seedSessionId;

        private Composition(OccurrenceAddress anchor, String body,
                            List<Disjunct> disjuncts, List<PathEntry> paths,
                            List<Family> families, List<RootDomain> roots,
                            List<Valuation> valuations, List<GapRow> gaps,
                            List<String> clockCells,
                            Map<String, Long> clockReadings,
                            Map<String, Set<String>> unattestedRoots,
                            Map<String, List<String>> observedReads,
                            Map<String, List<String>> observedArrivals,
                            Map<String, ComposedFamilies.ArmChoice> armChoices,
                            String seedSessionId) {
            this.anchor = anchor;
            this.body = body;
            this.disjuncts = Collections.unmodifiableList(disjuncts);
            this.paths = Collections.unmodifiableList(paths);
            this.families = Collections.unmodifiableList(families);
            this.roots = Collections.unmodifiableList(roots);
            this.valuations = Collections.unmodifiableList(valuations);
            this.gaps = Collections.unmodifiableList(gaps);
            this.clockCells = Collections.unmodifiableList(clockCells);
            this.clockReadings =
                    Collections.unmodifiableMap(clockReadings);
            this.unattestedRoots =
                    Collections.unmodifiableMap(unattestedRoots);
            this.observedReads =
                    Collections.unmodifiableMap(observedReads);
            this.observedArrivals =
                    Collections.unmodifiableMap(observedArrivals);
            this.armChoices = Collections.unmodifiableMap(armChoices);
            this.seedSessionId = seedSessionId;
        }

        public OccurrenceAddress anchor() {
            return anchor;
        }

        /** Declarations and assertions; no {@code check-sat}. */
        public String body() {
            return body;
        }

        /**
         * One question's text: this body with those assertions conjoined.
         *
         * <p>The body is the program and the extra assertions are the
         * question, so the body is rendered once and every valuation, probe
         * and pairing test appends only its own lines: re-rendering per
         * question would put a copy of one formula in the solver for each.
         * Legal spelling is applied here because a pin names recorded
         * symbols -- a clock cell is spelled {@code CLOCK/...#...} -- and
         * {@code #} opens a bit-vector literal, so a pin written bare makes
         * z3 answer the whole query "invalid bit-vector literal" instead of
         * a verdict.  {@link SmtLowering#legalSymbols} is idempotent, so a
         * body that already passed through it is the text it was.</p>
         */
        public String query(List<String> assertions) {
            StringBuilder text = new StringBuilder(body);
            if (assertions != null) {
                for (String assertion : assertions) {
                    if (assertion == null || assertion.isEmpty()) continue;
                    text.append(assertion).append('\n');
                }
            }
            return SmtLowering.legalSymbols(text.toString());
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

        /** Interaction -> the declared roots its unattested arms mention. */
        public Map<String, Set<String>> unattestedRoots() {
            return unattestedRoots;
        }

        /** Path id -> the interleaving that path's reads actually took. */
        public List<String> observedReads(String pathId) {
            List<String> observed = observedReads.get(pathId);
            return observed == null ? Collections.<String>emptyList()
                    : observed;
        }

        /** Path id -> the values that path's attaches actually received. */
        public List<String> observedArrivals(String pathId) {
            List<String> observed = observedArrivals.get(pathId);
            return observed == null ? Collections.<String>emptyList()
                    : observed;
        }

        public String seedSessionId() {
            return seedSessionId;
        }

        /**
         * Every family ARM selector, for reading which delivery a model
         * rested on.
         *
         * <p>A family is a case split (one selector per arm), so a sat
         * model answers WHICH arm it took -- and a claim that names a
         * mechanism over a slot has to be able to say which delivery of
         * that slot the witness used, not merely that the slot had
         * alternatives.</p>
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
            List<String> selectors = new ArrayList<String>();
            for (Disjunct disjunct : disjuncts) {
                selectors.add(disjunct.selector());
            }
            return selectors;
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
     *
     * <p>An arm from a replay that ran the producer concretely states what
     * was delivered and nothing about what else could have been: there is
     * no producer path condition behind it.  So a witness may state it, and
     * may not move a root that occurs inside it (R-I5).</p>
     */
    private final Map<String, Set<String>> unattestedRoots =
            new LinkedHashMap<String, Set<String>>();
    /** Path id -> what its reads observed, as named assertions. */
    private final Map<String, List<String>> observedReads =
            new LinkedHashMap<String, List<String>>();
    /** Path id -> the arrivals its attaches actually received. */
    private final Map<String, List<String>> observedArrivals =
            new LinkedHashMap<String, List<String>>();
    /** Attaches already named as unpaired; one row per attach, not per path. */
    private final Set<String> unpairedNamed = new LinkedHashSet<String>();
    /** This epoch's skeleton: which interactions have a slot (R-I6). */
    private SlotTable slots;
    /** Sessions whose pairing replaces a slot's: their arms are not ours. */
    private final Set<String> replacing = new LinkedHashSet<String>();
    /** Interactions already remarked on, so one row says it once. */
    private final Set<String> slotNamed = new LinkedHashSet<String>();
    /** What refused the first path that reached the anchor, or "". */
    private String firstRefusal = "";
    /** Locations already named as aliasing, so one row says it once. */
    private final Set<String> aliasingNamed = new LinkedHashSet<String>();
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
        this.composedFamilies = new ComposedFamilies(this, corpus, anchor,
                arms, lowering, families, unattestedRoots, replacing,
                slotNamed, unpairedNamed, aliasingNamed, gaps);
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
        // A root symbol naming two roots makes one term carry two
        // quantities, and every path that read them both is then
        // unsatisfiable at its own valuation.  It is the runtime's to fix,
        // and the composition refuses rather than composing the collision.
        for (Map.Entry<String, Set<String>> collision
                : corpus.collidingRootSymbols().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                    collision.getKey(), "one solver name for "
                            + collision.getValue().size() + " roots: "
                            + collision.getValue());
        }

        // A session this stage could not read whole states less than it
        // ran, and a short kind reads downstream as "this run had none": the
        // paths composed over it would be missing decisions nobody can see
        // are missing.  IMPORT names it too; the claim refuses on it.
        for (edu.uva.liftlab.graphchecker.contract.SessionReader session
                : corpus.sessions()) {
            if (session.incomplete().isEmpty()) continue;
            gap(GapKind.SESSION_INCOMPLETE, GapClass.BLOCKING,
                    session.sessionId(), "this session could not be read "
                            + "whole: " + session.incomplete());
        }

        // A VERDICT IS THE SESSION'S OWN ROW, and the wave's aggregate copy
        // of it is checked against that row rather than believed.  The
        // campaign shell stamped ADMITTED onto the aggregate after every
        // replay that merely finished, so on hdfs-11741 campaign #3 six of
        // eleven obligations were aggregated ADMITTED while their own
        // sessions said NOT_ADMITTED, and the composition took all eleven
        // as paths.  A corpus that states one verdict twice and differently
        // says nothing about that obligation at all.
        for (edu.uva.liftlab.graphchecker.contract.SessionReader session
                : corpus.sessions()) {
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

        // Which recording a claim is about has to have one answer, and the
        // sessions STATE it (manifest.json, role: SEED | FOCUSED).  It used
        // to be inferred -- "the session that focused nothing" -- and the
        // 11741 campaign #2 corpus has nine of those: the seed, seven
        // replays the kill cut before their focused occurrence activated,
        // and one NOT_ADMITTED focused replay whose occurrence never ran.
        // RECORDED_FAILURE_EXPLAINED and MESSAGE_PAIRING_FLIPPED would each
        // have picked whichever came first.
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

        // The skeleton, and what contradicts it.  Asked before any path is
        // composed, because a replacing session's rows must not reach a
        // family: the two pairings cannot both be this epoch's.
        try {
            slots = SlotTable.read(corpus.iteration());
        } catch (java.io.IOException | RuntimeException unreadable) {
            // The strict codec REFUSES a row it cannot read, and a refusal
            // that reached a caller as a stack trace told the reader
            // nothing: a skeleton this stage cannot state is named, and the
            // composition closes fail-closed over it.
            slots = null;
            gap(GapKind.TOPOLOGY_DIVERGENCE, GapClass.BLOCKING,
                    SlotTable.FILE, "this epoch's slot table could not be "
                            + "read: " + unreadable);
        }
        if (slots != null) {
            for (SlotTable.Replacement replacement
                    : slots.replacements(corpus)) {
                // FAIL CLOSED ON THE ARMS, OPEN ON THE CLAIM.  The session
                // goes into `replacing` either way -- two pairings of one
                // consumer cannot both be this epoch's, so neither set of
                // arms may reach a family -- and only an ADMITTED replay's
                // replacement STOPS the composition ({@link
                // SessionReader#admitted}).  One that did not run the world
                // it was asked for states no topology, so its row is a
                // DIAGNOSTIC and the claim is still made.
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
            // Two different absences, and the row says which.  "Nothing
            // reached the anchor" and "everything that reached it was
            // refused" send a reader to opposite ends of the pipeline, and
            // the second one was reported as the first.
            gap(GapKind.ADMISSION_GAP, GapClass.BLOCKING, anchor.render(),
                    admitted.isEmpty()
                            ? "no session of this corpus published a path "
                            + "that reached the declared occurrence"
                            : admitted.size() + " paths reached the anchor "
                            + "and all were refused: " + (firstRefusal
                            .isEmpty() ? "no refusal was named"
                            : firstRefusal));
        } else {
            List<String> selectors = new ArrayList<String>();
            for (Disjunct disjunct : disjuncts) {
                selectors.add(disjunct.selector());
            }
            lowering.assertNamed("target_path_partition",
                    Arms.exactlyOne(selectors));
            // The disjunction is over the SELECTORS: each path already
            // asserts "selector => (pi and phi)", so asserting that some
            // selector holds says exactly OR_p (pi_p and phi_p), without
            // writing every path's formula into the artifact twice.
            lowering.assertNamed("fatal_target",
                    VmTermLowering.or(selectors));
        }

        composedFamilies.outsideTheClosure(disjuncts);

        List<String> clockCells = new ArrayList<String>();
        Map<String, Long> clockReadings = new LinkedHashMap<String, Long>();
        clocks(clockCells, clockReadings);
        domains();
        lowering.assertIdentitiesDistinct();
        // What the corpus states inconsistently, named and BLOCKING: one
        // solver name at two sorts, and one truncated name for two
        // identities.  Both make the query say something no execution
        // said, so the composition closes fail-closed rather than
        // answering over them -- and rather than throwing, which told a
        // reader nothing at all.
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
        for (String cut : lowering.cuts()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, cut,
                    lowering.unsupportedDetail().containsKey(cut)
                            ? lowering.unsupportedDetail().get(cut)
                            : "the propagation did not carry this value");
        }

        // The valuations first, then the body: a pin names a declared root
        // the body's own assertions need not mention, and the body declares
        // only what a text it will be asked with reaches.
        List<Valuation> valuations = valuations();
        List<String> pins = new ArrayList<String>();
        for (Valuation valuation : valuations) {
            pins.addAll(valuation.assertions());
        }
        return new Composition(anchor, lowering.body(pins), disjuncts, entries,
                new ArrayList<Family>(families.values()),
                new ArrayList<RootDomain>(roots.values()), valuations,
                gaps, clockCells, clockReadings, unattestedRoots,
                observedReads, observedArrivals,
                composedFamilies.armChoices(), seed());
    }

    // ------------------------------------------------------------------
    // Admission.
    // ------------------------------------------------------------------

    /**
     * Every session's path that reached the anchor.
     *
     * <p>The declared occurrence is the anchor, always.  A session that
     * published no target row for it did not reach it, and that is an
     * admission gap about that session -- never a reason to elect a
     * different occurrence.</p>
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
     * Whether this session's OWN rows admit the obligation it ran.
     *
     * <p>The session's manifest names the obligations it was handed and its
     * {@code obligations.jsonl} states what each of them settled; the
     * replay owns that verdict, because whether the focused prefix
     * reproduced and the flipped decision was taken is a fact of the run.
     * A replay that refused its obligation collected no arm the seed lacks,
     * so its path is not a disjunct of this composition: it is the
     * recording again, under a valuation the wave asked for and the run did
     * not take.</p>
     *
     * <p>A SEED session is asked nothing and admits itself.  An obligation
     * the manifest names and the rows do not settle is BLOCKING: the
     * session ran it and cannot say what happened, which is not the same as
     * a refusal.</p>
     */
    private boolean settled(String session) {
        SessionReader reader = corpus.session(session);
        if (reader == null || reader.seed()) return true;
        Set<String> stated = new LinkedHashSet<String>();
        // ONE PREDICATE, ONE PLACE ({@link SessionReader#admitted}): this
        // stage names each refusal below, and does not keep a second
        // opinion about what "admitted" means.
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
        // The rows of this path's session: a reader and the placeholder
        // that answers it are matched by the MINT VERSION, which is
        // session-unique, so the view needs no narrower scope.
        SmtLowering.SessionJoin rows =
                SmtLowering.joinOf(corpus.session(session));
        lowering.begin(session, rows, corpus.expressions(session));

        List<String> terms = new ArrayList<String>();
        List<GapRow> refusals = new ArrayList<GapRow>();
        List<ReadRow> joined = new ArrayList<ReadRow>();
        List<String> observed = new ArrayList<String>();
        Map<String, String> joins = new LinkedHashMap<String, String>();

        // (0a) THE CLOSURE (P3).  Which occurrences of THIS session this
        //      path's joins reach, and the seq each one's prefix is a
        //      reason up to.  A row-level fixed point, computed before
        //      anything is lowered, because it is a fact about the join
        //      graph and not about SMT.
        Map<String, Long> reached = closure(session, anchor, target.seq(),
                null);

        // (0b) Every read of the reached occurrences whose value the ROW
        //     states outright, bound BEFORE any expression of this path is
        //     lowered.  A read symbol is a declared symbol of its session,
        //     so a leaf naming it -- in phi, in a decision's term, in an
        //     arm, or inside the write expression another read joined to
        //     -- must be this path's binding for it wherever it appears.
        //     Declared as each row was met instead, it resolved only for
        //     the leaves that happened to come after its own row.
        Set<String> answered = new LinkedHashSet<String>();
        statedReads(session, reached.keySet(), refusals, joins, answered);

        // (1) The valuation this replay ran under, for every VARIED root.
        //     A replay's assignments are not all visible as decisions -- a
        //     root can be written and never branched on -- and the
        //     execution still happened under that value.  A root every
        //     session read the same way is pinned by its own domain and is
        //     not repeated here.
        //
        //     A declared root this session did NOT mint is collected here
        //     and answered in (1b), once this path's own terms are what
        //     they will be: whether the path states anything about such a
        //     root is a fact about its terms, and none of them is lowered
        //     yet.
        Map<String, Set<String>> unminted =
                new LinkedHashMap<String, Set<String>>();
        terms.addAll(valuationOf(session, refusals, unminted));

        // (2) What this path read at each handoff of the anchor: the
        //     obligation's answer where one answered the mint, and
        //     otherwise NOTHING -- the arrival is bound by its family
        //     alone, and the attach is collected for it (`bound`).  Never
        //     a literal, this session's or any other's.
        Set<String> interactionIds = new LinkedHashSet<String>();
        Set<String> handoffs = new LinkedHashSet<String>();
        List<AttachRow> bound = new ArrayList<AttachRow>();
        terms.addAll(handoffReads(session, interactionIds, handoffs,
                refusals, bound));

        // (3) The state joins: read := the expression of the write version
        //     it observed, within this session.  Kept by symbol, because a
        //     read with ALTERNATIVES takes its value from the family and
        //     not from a conjunct of the path -- asserting both would make
        //     the family redundant and the alternatives unreachable.
        stateJoins(session, reached.keySet(), rows, refusals, joined,
                observed, joins, answered);

        // (4) pi_p: THE PREFIX STRICTLY BEFORE THE TARGET OBSERVATION,
        //     through the one routine that applies each decision's
        //     polarity -- a published term is the site's PREDICATE, and
        //     which arm this run took is the row's outcome.
        //
        //     `before` is the target row's own seq, and that is what makes
        //     the conjunction a question rather than a contradiction: the
        //     anchor's decision and the target row share a seq in every
        //     session, so a pi taken over ALL of the occurrence's
        //     decisions carries the anchor's own RECORDED polarity while
        //     phi below asserts its complement.  Every path whose session
        //     did not observe the fatal arm was then unsat before any root
        //     was considered -- all 7 paths of hdfs-11741 campaign #4 and
        //     all 11 of #3, with z3's core `path_fatal__* + fatal_target`
        //     and no valuation assertion in it, and 17960's own third
        //     path, the one with fatalObserved=false.  The composer could
        //     only ever witness from a replay that had already failed.
        //     `Arms.wireArms` applies exactly this rule at an export
        //     (`Arms.arm`, `pathCondition(decisions, deliveredAt)`): what
        //     a run had decided BY THE TIME of the event, never after it.
        List<String> pi = Arms.pathCondition(path.decisions, target.seq());
        List<DecisionRow> inPi = new ArrayList<DecisionRow>();
        for (DecisionRow decision : path.decisions) {
            if (decision.seq() < target.seq()) inPi.add(decision);
        }
        for (int index = 0; index < pi.size(); index++) {
            DecisionRow decision = inPi.get(index);
            String subject = "decision " + decision.siteId() + "#"
                    + decision.ordinal();
            // The published term names the session's EXPRESSIONS by
            // reference; the one lowering resolves them, and what is left
            // has to be a name something declares.
            String conjunct = lowering.statedTerm(pi.get(index),
                    "pi:" + subject);
            if (!Arms.predicate(conjunct)) continue;
            if (unknown(conjunct, refusals, subject)) continue;
            terms.add(conjunct);
        }

        // (4b) P3: AND THE PREFIX OF EVERY OTHER OCCURRENCE THIS PATH'S
        //      JOINS REACH, each strictly before the write that reached
        //      it.  A read bound to the expression of a write version is
        //      bound to a value that occurrence PRODUCED, and what it
        //      produced it produced under the decisions it had taken by
        //      then: without them the join states the value and not the
        //      reason for it, and every conjunct that carries a clock
        //      reading is in one of these prefixes and in no other place.
        //      On hdfs-11741 the anchor's allKeys read joins to a write by
        //      dn1 REGION.ba3902cd -- the refresh that reads the DN clock,
        //      10 to 13 decisions in every session -- and pi_p named none
        //      of them, so Composer.clocks() found 0 cells and CLOCK_SKEW
        //      was unreachable in every manifest published so far.
        //
        //      Per session, never global: these are the reached
        //      occurrence's decisions AS THIS SESSION RECORDED THEM, so
        //      they are already under this path's own valuation (step 1)
        //      and need no second guard.  A handoff arm's producer is the
        //      other half of the same rule and states its prefix in its
        //      own session's scope inside the family ({@link #prefix}).
        terms.addAll(closureConditions(session, reached, refusals));

        // (5) phi_p is the FATAL arm as published; the composer never
        //     re-derives the polarity.  Re-deriving it negated a term that
        //     was already the complement, and every healthy-observed path
        //     was handed its own observation back.
        String subject = "phi of " + anchor.render();
        if (target.phiTerm() != null && !target.phiTerm().isEmpty()) {
            String phi = lowering.statedTerm(target.phiTerm(),
                    "phi:" + subject);
            if (!phi.isEmpty() && !unknown(phi, refusals, subject)) {
                terms.add(phi);
            }
        }

        // (5b) Every OTHER handoff this conjunction reaches, by the same
        //      three rules: the state joins are what carry them, so this is
        //      asked once the joins, pi and phi are lowered and the text is
        //      what it will be.
        List<String> reaching = new ArrayList<String>(terms);
        reaching.addAll(joins.values());
        terms.addAll(reachedHandoffs(session, reaching, interactionIds,
                handoffs, refusals, bound));

        // BEFORE end(), which closes the conjunction and forgets them: a
        // refusal raised while this path was lowered is the reason the
        // path is not in the disjunction, and a path that kept the rest of
        // its conjunction would rest on the free constant the refusal
        // left behind.
        List<String> refused = new ArrayList<String>(
                lowering.openRefusals());
        terms.addAll(lowering.end());

        // (1b) THE OTHER HALF OF (1), asked here because here is where
        //      this path's own terms are whole: a declared root this
        //      session minted no value for, whose SYMBOL this path's own
        //      terms name.  Such a path rests on a quantity it states
        //      nothing about, and the only value the corpus could give it
        //      is another execution's reading -- so it is refused.  A root
        //      NO term of this path names is simply not stated by this
        //      path, and refusing it was a refusal for something the path
        //      never asked about (see {@link #valuationOf}).
        unstatedRoots(session, unminted, terms, joins, refusals);
        for (String refusal : refused) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, refusal,
                    "this path rests on a value the recording does not "
                            + "state, so it is not in the disjunction"));
        }
        if (!refusals.isEmpty()) {
            gaps.addAll(refusals);
            if (firstRefusal.isEmpty()) {
                firstRefusal = refusals.get(0).subject();
            }
            return null;
        }

        // (6) One selector per (producer occurrence, session) for every
        //     interaction this path's chain reaches, under this path's
        //     selector.  A producer for which NO session of this corpus
        //     could have made every delivery this path took from it (R3c)
        //     leaves the path out of the disjunction: a witness that mixed
        //     two runs' deliveries of one occurrence would rest on an
        //     export no execution produced.
        List<String> familyTerms = new ArrayList<String>();
        List<GapRow> unproducible = new ArrayList<GapRow>();
        if (!composedFamilies.closeFamilies(ordinal, selector,
                interactionIds, bound, familyTerms, unproducible)) {
            gaps.addAll(unproducible);
            if (firstRefusal.isEmpty() && !unproducible.isEmpty()) {
                firstRefusal = unproducible.get(0).subject();
            }
            return null;
        }
        // (7) And the STATE families: which writer the read may have seen.
        //     A read a family gives alternatives to takes its value there.
        Set<String> chosen = composedFamilies.stateFamilies(path,
                ordinal, selector, joined, interactionIds, familyTerms);
        // (8) And the state joins this conjunction ASKS ABOUT.
        terms.addAll(statedJoins(joins, chosen, terms, familyTerms));

        lowering.assertNamed("path_fatal__" + ordinal,
                "(=> " + selector + " " + VmTermLowering.and(terms) + ")");
        observedReads.put(path.pathId, observed);
        observedArrivals.put(path.pathId, arrivals(session));
        return new Disjunct(path, selector, target.observedFatal(),
                interactionIds);
    }

    /**
     * The state joins THIS CONJUNCTION ASKS ABOUT, to a fixed point.
     *
     * <p>A join is {@code read := the expression of the write version it
     * observed}.  Where no other term of the path names that read symbol,
     * the equation binds a variable the question never asks: it is
     * satisfiable for every value of everything it mentions, so it
     * constrains nothing -- and it drags the whole theory its right-hand
     * side is written in into the query.  The same reachability rule the
     * preamble is already emitted under ({@link SmtLowering#body}), one
     * level up, applied to the assertions instead of the declarations.</p>
     *
     * <p>MEASURED on hdfs-11741 campaign #4.  Seven paths each carried
     * {@code (= |MAP_STATE/321#-3@v1337| (assoc_put ...))} -- the DataNode's
     * {@code allKeys} map as an {@code AssocState}, joined to the refresh
     * that put the last key in.  The anchor's own lookup does not read that
     * variable: it reads the container DAG, an eight-deep {@code ite} over
     * key equality, and {@code MAP_STATE/321} is named by nothing else in
     * the file.  With every arrival pinned to a literal the equation was
     * cheap; with the arrivals bound by their families instead (item 1) the
     * keys became symbolic and z3 spent the whole 1800 s budget on the
     * array-and-lambda theory {@code assoc_put} and {@code assoc_remove}
     * are written in -- all four valuations UNDECIDED.  Dropping that one
     * unreached join and nothing else: valuation 0 decided in 0.16 s.</p>
     *
     * <p>To a fixed point, and seeded by the FAMILIES as well as the path's
     * own terms: one join's right-hand side names another join's symbol,
     * and a family arm names symbols the path's own conjunction need
     * not.</p>
     */
    List<String> statedJoins(Map<String, String> joins,
                                     Set<String> chosen, List<String> terms,
                                     List<String> familyTerms) {
        Map<String, String> pending = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> join : joins.entrySet()) {
            // A read a family gives alternatives to takes its value there;
            // asserting both would make the family redundant and its
            // alternatives unreachable.
            if (chosen.contains(join.getKey())) continue;
            pending.put(join.getKey(), join.getValue());
        }
        Set<String> asked = new LinkedHashSet<String>();
        List<String> reaching = new ArrayList<String>(terms);
        reaching.addAll(familyTerms);
        while (!reaching.isEmpty()) {
            Set<String> reached = new LinkedHashSet<String>();
            for (String text : reaching) {
                lowering.reachedSymbols(text, reached,
                        new LinkedHashSet<String>());
            }
            reaching = new ArrayList<String>();
            for (String symbol : reached) {
                String join = pending.remove(symbol);
                if (join == null) continue;
                asked.add(symbol);
                reaching.add(join);
            }
        }
        // In the ROWS' own order, not the order the fixed point met them:
        // the conjunction a reader compares between two runs is the one the
        // recording is read in.
        List<String> stated = new ArrayList<String>();
        for (Map.Entry<String, String> join : joins.entrySet()) {
            if (asked.contains(join.getKey())) stated.add(join.getValue());
        }
        return stated;
    }

    /**
     * What this replay ran every varied root at.
     *
     * <p>The value is {@link Corpus#rootValue}, the ONE notion: the mint's
     * reading where the replay read the root, the obligation's assignment
     * where the replay PLANTED it.  Reading the mint alone left a flip
     * replay's own valuation stated nowhere -- its mint states no
     * recordedValue by rule, because a counterfactual is not a recording --
     * so no path's formula named the marker, no valuation of it was asked,
     * and 17960 published a finding at the recorded valuation with no root
     * moved.</p>
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
                // A root the case declares and THIS replay did not mint:
                // the path states nothing about it, and pinning it to some
                // other session's reading would state a fact about an
                // execution that never read it.  Whether that silence is a
                // REFUSAL is a question about this path's own terms, and it
                // is asked once they are whole ({@link #unstatedRoots}):
                // the symbols of every mint of the root are collected here
                // and looked for there.
                //
                // It used to be asked of `lowering.declared(any.symbol())`,
                // which is "this QUERY names the symbol" -- and the query
                // is every path composed before this one, over a registry
                // seeded with every symbol EVERY session of the corpus
                // declared ({@link Corpus#declaredSymbols}).  So a root one
                // session minted refused every other session's path,
                // whether or not its terms had ever heard of it: on the
                // hdfs-11741 campaign #4 corpus the three hook-minted
                // BLOCK_KEY.EXPIRY_DATE roots -- minted only by the twelve
                // focused replays of nn0's KEY_MANAGER_TICK, and by neither
                // the seed nor any other replay -- filed 288 of the
                // composition's 290 BLOCKING UNSTATED_VALUE rows, 96 per
                // root, and every path of the corpus was refused.
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
            // Neither half states it, and this replay DID mint the root:
            // the path would be satisfiable at every valuation of it, which
            // is a disjunct that decides nothing and reads as one that
            // does.  Not gated on the symbol being declared already -- that
            // gate is circular, because the only thing that declares a
            // marker's symbol is the pin this refusal replaces: on the
            // 05f4bf265 17960 corpus the two flip sessions state no value,
            // nothing named the marker, and the composition published
            // MESSAGE_PAIRING_FLIPPED at the recorded valuation instead.
            if (ran.isEmpty() && row.declared()) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, any.rootId(),
                        "this replay minted a declared root and states no "
                                + "value it ran it at: its mint states none "
                                + "and no obligation it ran under assigns "
                                + "it"));
                continue;
            }
            // Both halves state it and they disagree: one replay ran the
            // root at one value, so a corpus that names two is not a
            // recording this path can carry.
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
            // A DECLARED domain is relative to what THIS replay read, and
            // what each replay read is its own fact: the NameNode's serial
            // advances between sessions, so one session's window is not
            // another's.  The path carries its own window; pinning it to
            // the value it happened to read would answer the case's own
            // question before the solver is asked.
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
     * The declared roots this path NAMES and its session never minted.
     *
     * <p>The other half of {@link #valuationOf}, and the whole of the rule
     * a path is refused by: a path states a valuation for every varied root
     * IT minted, and it is refused for a root it did not mint exactly when
     * its OWN terms name that root's symbol.  A term of this path naming a
     * symbol no row of this session states leaves the quantity free -- or,
     * worse, joined to a pin some other session's path wrote -- and a free
     * constant is how a model answers a question the execution never asked.
     * A root no term of this path names is not a quantity this path is
     * about at all, and its silence about it says nothing that needs
     * refusing.</p>
     *
     * <p>"Names" is asked of the text this path will be asserted with --
     * pi, phi, the handoff reads, the closure prefixes, the side conditions
     * and the state joins this session published -- through the one walk
     * that follows a named container subterm into its body
     * ({@link SmtLowering#reachedSymbols}), and, beside it, the one
     * tokenizer ({@link SmtLowering#names}), because a ROOT symbol reaches
     * a term in two ways: lowered from a recorded leaf, which
     * {@code reachedSymbols} reports, and written into a published term as
     * text, which it reads as a name the lowering itself minted.  Whole
     * tokens either way; a substring of a longer name is a different
     * name.</p>
     */
    private void unstatedRoots(String session,
                               Map<String, Set<String>> unminted,
                               List<String> terms,
                               Map<String, String> joins,
                               List<GapRow> refusals) {
        if (unminted.isEmpty()) return;
        List<String> texts = new ArrayList<String>(terms);
        texts.addAll(joins.values());
        Set<String> named = new LinkedHashSet<String>();
        for (String text : texts) {
            if (text == null || text.isEmpty()) continue;
            lowering.reachedSymbols(text, named,
                    new LinkedHashSet<String>());
            named.addAll(SmtLowering.names(text));
        }
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
        return "(and (>= " + row.symbol() + " " + integralLiteral(min)
                + ") (<= " + row.symbol() + " " + integralLiteral(max)
                + "))";
    }

    /**
     * What this path read at each of the anchor's handoffs.
     *
     * <p>Three rules, in order, and all three are this path's OWN fact:</p>
     * <ol>
     *   <li>an obligation answered the mint: that value;</li>
     *   <li>otherwise, where the recording states which producer endpoint
     *       delivered it and that producer's arm is ATTESTED: NOTHING is
     *       conjoined here at all.  The attach joins its handoff's FAMILY
     *       and nothing else (CLOSURE-V2) -- the arm this session's run
     *       recorded is one of that family's arms and is selected by the
     *       family's guard, not asserted as a fact.  What the path takes
     *       from the delivery is the SORT its variable is declared at
     *       ({@link #attestedArrival});</li>
     *   <li>otherwise the read is REFUSED BY NAME and the path leaves the
     *       disjunction.  MEASURED UNREACHABLE on both frozen corpora:
     *       hdfs-17960 campaign #8 states no attach row at all, and every
     *       one of hdfs-11741 campaign #4's 616 attach rows names a
     *       producer endpoint the seed exported at, so {@code
     *       attestedExports} is non-empty for all of them.</li>
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
     * Every OTHER handoff this path's own conjunction reaches.
     *
     * <p>The same three rules, on the set the formula actually names.  A
     * handoff variable is not the anchor's business alone: the anchor's
     * read of a container joins to the write that PUT a delivered value
     * into it, so what the anchor read is itself a delivery, one occurrence
     * further back, and its variable stands in this path's formula.  Bound
     * by nothing it is a free constant -- on hdfs-11741 campaign #3 dn1's
     * {@code addKeys} arrival {@code M_I_field_HOFF.29a470e4...} is
     * declared twelve times inside the {@code allKeys} dag and stated by no
     * assertion at all -- and a free constant is how a model answers a
     * question the execution never asked.</p>
     *
     * <p>To a fixed point, because an arm's own expression names the
     * handoffs its producer was itself handed: the same closure {@link
     * Arms#wireArms} takes over a family, taken here over the path.</p>
     */
    private List<String> reachedHandoffs(String session, List<String> terms,
                                         Set<String> interactionIds,
                                         Set<String> handoffs,
                                         List<GapRow> refusals,
                                         List<AttachRow> bound) {
        List<String> reads = new ArrayList<String>();
        List<String> pending = new ArrayList<String>(terms);
        while (!pending.isEmpty()) {
            Set<String> reached = new LinkedHashSet<String>();
            for (String text : pending) {
                lowering.reachedSymbols(text, reached,
                        new LinkedHashSet<String>());
            }
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
     * One attach, by the three rules, stated once per symbol.
     *
     * <p>{@code handoffs} is the set of symbols this path has already
     * bound: one attach row per symbol reaches the formula, whichever
     * occurrence of the path named it first, and a symbol stated twice is
     * two assertions about one variable.</p>
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
            // The wire delivered something and the recording cannot say
            // from where, so there is no interaction to build a family on
            // -- and a variable no family constrains is the one thing a
            // witness must not rest on unremarked.  The read below refuses
            // it by name for exactly that reason.
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
        // AND NOTHING ELSE.  There used to be a third rule here -- bind
        // the read to the literal this session happened to receive -- and
        // an arrival is not a statement about why the delivery was that
        // value: it is the value, pinned, on a path whose whole question
        // is whether the producer could have delivered another one.  A
        // read no attested arm delivers is refused BY NAME, so the path
        // leaves the disjunction and the reason is in the ledger, which is
        // the fail-closed answer; a path that kept the rest of its
        // conjunction would rest on a pin the rows do not state for it.
        //
        // MEASURED unreachable on both frozen corpora before deleting it:
        // hdfs-17960 campaign #8 states no attach row at all, and all 616
        // of hdfs-11741 campaign #4's attach rows name a producer endpoint
        // the seed exported at, so attestedExports is non-empty for every
        // one of them (0 answered, 0 without a producer).
        refusals.add(GapRow.of(session, GapKind.UNATTESTED_ARM,
                GapClass.DIAGNOSTIC, attach.symbol(),
                "no session of this corpus states the rows of the producer "
                        + "occurrence this delivery came from, so what was "
                        + "delivered is stated and why is not: this path "
                        + "would have to pin the read to the literal it "
                        + "received"));
    }

    /**
     * One handoff read, at the sort the MINT declared.
     *
     * <p>Never at the sort the value's spelling suggests: "0" is an int, a
     * long, a char and a false all at once, and a variable whose sort came
     * from one reading of it is a variable two paths can declare twice.</p>
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
     * The scalar sort one JVM descriptor denotes, or a named refusal.
     *
     * <p>A descriptor this lowering cannot place falls through to a
     * reference, and a reference is not a wrong answer -- it is a DIFFERENT
     * question: a numeric value declared {@code Ref} is compared with
     * nothing the rest of the formula says, and the solver answers freely.
     * A handoff variable and a read symbol are scalars by construction, so
     * anything else is refused by the name of the spelling that caused
     * it.</p>
     */
    private Sort scalarSort(String javaType, String session, String subject,
                            List<GapRow> refusals) {
        Sort sort = JavaSmtSorts.sortOfJava(javaType);
        if (sort == Sort.BOOL || sort == Sort.INT || sort == Sort.FLOAT32
                || sort == Sort.FLOAT64 || sort == Sort.STRING) {
            return sort;
        }
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
     * Whether an ATTESTED arm delivers this arrival, and at what sort.
     *
     * <p>It states NOTHING about the value.  The arrival is bound by the
     * handoff's FAMILY and by nothing else ({@link
     * ComposedFamilies#closeFamilies}): the arm this session's own run
     * recorded is one of that family's arms and is selected by the family's
     * guard, not asserted as a fact of every path.  This used to return the
     * first attested delivery as a conjunct of the path -- so every one of
     * hdfs-11741 campaign #4's seven paths carried the SEED's delivery
     * {@code (= HOFF.836a0f0e... 182905)} and {@code (= HOFF.2fb7f999...
     * 182905)}, which put the key the token names back into the array the
     * anchor looks it up in and made all seven unsatisfiable with every
     * root free (PATH_SELF_CONTRADICTORY, the measured blocker).  The
     * family already said the same thing as a disjunction over thirteen
     * arms, so what the pin added was exactly the contradiction.</p>
     *
     * <p>What is still asked here is what only a delivery can answer: that
     * SOME attested arm exists at all -- a read no attested arm delivers is
     * refused by name below -- and the SORT the variable is declared at.
     * The arm's own sort, never the arrival's spelling: the arrival says
     * what the value looked like, the delivery says what it is, and one
     * variable has one sort.  The declaration has to happen HERE, while the
     * path is being lowered, because a leaf naming this symbol in phi or in
     * a join is cut as a free symbol otherwise, and the families are
     * emitted once the path's own conjunction is closed.</p>
     *
     * <p>ATTESTED IS THE PRODUCER'S PROPERTY, and {@link
     * Arms#attestedExports} is the one rule for it: any session of the
     * corpus that ran the producer occurrence symbolically can say under
     * what the delivery happened, and the pairing then uses THAT session's
     * export at this same endpoint -- lowered in its own session's scope,
     * because the identities inside it are that execution's.  Asking
     * whether the CONSUMER's session attests the producer asks a question
     * about the wrong run: on hdfs-11741 campaign #3 nn0's export
     * occurrence was nobody's focus, so all eleven focused paths fell back
     * to the arrival literal 182905/182907 and nn0's symbols reached no
     * dn1 formula at all.</p>
     */
    private boolean attestedArrival(AttachRow attach) {
        Endpoint producer = attach.producer();
        if (producer == null) return false;
        for (ExportRow export : arms.attestedExports(producer)) {
            Term delivered = composedFamilies.lower(export.sessionId(),
                    export, "paired-arm");
            if (delivered == null) continue;
            lowering.declareStated(attach.symbol(), delivered.sort);
            return true;
        }
        return false;
    }

    /**
     * Read := the expression of the write version it observed.
     *
     * <p>JOIN, then PIN to what the recording says the read returned, then
     * REFUSE by name.  There is no "latest write" and no choice between
     * writers: the version the read observed is a recorded fact of one
     * session's own counter.</p>
     */
    /**
     * Every row of this session that states a value a symbol of this path
     * may be.
     *
     * <p>The anchor's own reads, and every MINT ROW this session published,
     * wherever it published it.  A mint's identity in a session is the
     * version it installed -- the key {@link
     * SmtLowering#mintedReadSymbol} resolves by, and the key the runtime
     * publishes one row per (location, version) by -- and the occurrence the
     * row was published AT is not part of it.  The two disagree whenever a
     * sibling activation publishes first: the anchor region's two
     * FSImageSaver activations race on one {@code AtomicInteger}, the one
     * that mints installs the VM symbol (labelled with its own planned
     * occurrence) and the one that CLOSES first wins the session-wide
     * per-(location, version) claim and publishes the row, under its own
     * address and the other's symbol.  On hdfs-17960 session
     * e03c7d5b... that is mint v177 -- the ANCHOR's own declared input --
     * published at {@code saveFSImageInAllDirs#u36@1}, so a loop over the
     * anchor's rows alone bound nothing for it, the leaf naming it was cut
     * {@code UndeclaredFreeSymbol}, and the whole flip path left the
     * disjunction (2 paths where the corpus has 3).</p>
     */
    private List<ReadRow> statedRows(String session,
                                     Set<String> occurrences) {
        List<ReadRow> rows = new ArrayList<ReadRow>();
        Set<String> stated = new LinkedHashSet<String>();
        SessionReader reader = corpus.session(session);
        // THE MINT ROWS FIRST, wherever they were published: every other
        // read of a version a mint installed resolves to the symbol one of
        // these rows states, so a row bound after them would be asked about
        // a symbol nothing had stated yet.
        if (reader != null) {
            for (ReadRow read : reader.reads()) {
                if (read.mintVersion() >= 0L && read.symbol() != null
                        && !read.symbol().isEmpty()
                        && stated.add(read.symbol())) {
                    rows.add(read);
                }
            }
        }
        // THE ANCHOR FIRST, then the occurrences its joins reach, in the
        // order the closure met them (P3): a symbol two occurrences read
        // is stated once, by the row of whichever of them this path
        // reached first, and the anchor is always first.
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
     * The occurrences this path's joins reach, and each one's cutoff seq.
     *
     * <p>P3, as a row-level fixed point over ONE session's own log.  The
     * anchor is reached at {@code target.seq()} -- P1's bound, and nothing
     * widens it, because the anchor's own decision at that seq is the one
     * phi asserts the complement of.  Every other occurrence is reached
     * because a read this path binds joined to a WRITE of it, and the
     * cutoff is that write's seq: what the writer had decided by the time
     * it produced the value.  A second read joining to a LATER write of the
     * same occurrence widens the cutoff to that write's seq and the
     * occurrence is walked again, so the prefix the path carries is the one
     * that covers every delivery it rests on.</p>
     *
     * <p>The reached occurrence's own reads are then joined too, which is
     * what makes this a closure rather than one step: dn1's refresh read
     * the value nn0 exported, and nn0's export is a reason the refresh
     * wrote what it wrote.  A read of a reached occurrence counts only
     * where it happened BEFORE that occurrence's cutoff; the anchor's reads
     * are all of them, because they are its declared inputs and the target
     * row is one of them.</p>
     *
     * <p>P3c, the second edge: the EARLIER VERSIONS of a reached write's own
     * location are reached with it.  The state of an object at version v is
     * the result of every earlier mutation of that object in that run, so
     * each earlier writer's prefix is a reason the value is what it is --
     * not only the prefix of whichever occurrence made the last change.
     * 11741's anchor joined the version its DataNode's put loop produced,
     * and what the map LACKS at that version is what another occurrence
     * removed from it earlier, under a comparison against the clock it read;
     * no row of the session joins the two, so without this the composed
     * query stated "the map lacks the key" as a bare fact of the recording
     * and declared no cell of that clock.  An earlier write is reached
     * exactly as a joined one is -- its writer at that write's seq, widening
     * as ever -- and its own earlier versions are covered by construction,
     * being earlier still; each (location, version) is handled once.</p>
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
     * One write this path rests on: its writer is reached, its state swept.
     *
     * <p>The same rule whether the write was joined by a read row or is an
     * earlier version of a location already reached, because it is the same
     * fact either way -- the value this path rests on came out of that
     * write.  The ANCHOR is never reached and no write of its own is swept:
     * its cutoff is the target observation, and a write of its own is not a
     * reason to widen it.</p>
     */
    private void reach(WriteRow write, OccurrenceAddress start,
                       Map<String, Long> reached,
                       List<String> pending, List<WriteRow> versions,
                       Set<String> handled) {
        String writer = write.endpoint().occurrence().id();
        // NEVER THE ANCHOR, and never the occurrence this closure starts
        // from: the start's cutoff is the event the closure is about -- the
        // target observation, or the export an arm delivered -- and a write
        // of its own is not a reason to widen it past that.
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
     * The decision prefix of every reached occurrence but the anchor's.
     *
     * <p>Through the same one routine the anchor's prefix goes through, so
     * a decision means the same thing wherever it stands: the published
     * term is the site's PREDICATE and the row's outcome says which arm the
     * run took.  A conjunct that names something nothing declares is
     * refused by name, exactly as in the anchor's own prefix -- a path that
     * kept the rest of its conjunction would rest on the free constant the
     * refusal left behind.</p>
     */
    List<String> closureConditions(String session,
                                           Map<String, Long> reached,
                                           List<GapRow> refusals) {
        List<String> conditions = new ArrayList<String>();
        for (Map.Entry<String, Long> entry : reached.entrySet()) {
            if (anchor.id().equals(entry.getKey())) continue;
            OccurrenceAddress at = corpus.occurrence(entry.getKey());
            if (at == null) continue;
            long before = entry.getValue().longValue();
            List<DecisionRow> decisions = corpus.decisionsOf(session, at);
            List<DecisionRow> inPi = new ArrayList<DecisionRow>();
            for (DecisionRow decision : decisions) {
                if (decision.seq() < before) inPi.add(decision);
            }
            List<String> pi = Arms.pathCondition(decisions, before);
            for (int index = 0; index < pi.size(); index++) {
                DecisionRow decision = inPi.get(index);
                String subject = "join-pi " + decision.siteId() + "#"
                        + decision.ordinal();
                String conjunct = lowering.statedTerm(pi.get(index),
                        "pi:" + subject);
                if (!Arms.predicate(conjunct)) continue;
                if (unknown(conjunct, refusals, subject)) continue;
                conditions.add(conjunct);
            }
        }
        return conditions;
    }

    /**
     * Read := the value the ROW states it returned, before any lowering.
     *
     * <p>The PIN half of {@link #stateJoins}, hoisted: it needs no
     * expression, so it can bind every symbol the rows state outright
     * before the first leaf of this path is lowered.  That is what makes a
     * read symbol a DECLARED symbol of its session rather than one that
     * happened to be declared in time -- a leaf of it inside another
     * read's joined write expression was cut as free because that read's
     * row came first (the 17960 anchor's AtomicInteger placeholder, 18
     * rows, reached through write v172's expression).</p>
     *
     * <p>Only the reads the JOIN half does not own: a read the write log
     * covers takes its value from the write's expression, which is the
     * chain, and is bound there.  A read whose row states NO value is left
     * to the JOIN half, which asks the version's own row for it and names
     * the refusal if nothing states that either; a row whose stated value
     * this lowering places nowhere is named here.  Either way one refusal
     * per row: {@code answered} is what the two halves say it by.</p>
     */
    void statedReads(String session, Set<String> occurrences,
                             List<GapRow> refusals,
                             Map<String, String> joins,
                             Set<String> answered) {
        for (ReadRow read : statedRows(session, occurrences)) {
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            if (joins.containsKey(read.symbol())) continue;
            if (joinable(session, read)) continue;
            pin(session, read, refusals, joins, answered);
        }
    }

    /**
     * Read := the value its own row states, through the one lowering.
     *
     * <p>Answers whether the row states a value this places: a scalar is
     * its literal, and a REFERENCE is the identity the VM spelled -- the
     * same {@code identity__} name every other leaf of that object gets,
     * or null for {@code "N"} -- because a row and a
     * {@code FieldAccess concreteValue} state a recorded reference the
     * same way and there is one place that reads that spelling.  A row
     * whose stated value this places nowhere is named by the caller, never
     * skipped in silence.</p>
     */
    private boolean pin(String session, ReadRow read,
                        List<GapRow> refusals, Map<String, String> joins,
                        Set<String> answered) {
        String text = read.concreteValue() == null ? ""
                : read.concreteValue().trim();
        if (text.isEmpty()) return false;
        answered.add(read.symbol());
        Term value = lowering.statedValue(text, read.javaType(),
                "read-pin:" + read.symbol());
        if (value == null) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, read.symbol(),
                    "the row states the value \"" + text + "\" at Java "
                            + "type \"" + (read.javaType() == null ? ""
                            : read.javaType()) + "\", which this lowering "
                            + "places nowhere"));
            return true;
        }
        lowering.declareStated(read.symbol(), value.sort);
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

    void stateJoins(String session, Set<String> occurrences,
                            SmtLowering.SessionJoin join,
                            List<GapRow> refusals,
                            List<ReadRow> joined, List<String> observed,
                            Map<String, String> joins,
                            Set<String> answered) {
        /** Name -> the one statement this path makes under it. */
        Map<String, String> statedOnce = new LinkedHashMap<String, String>();
        for (ReadRow read : statedRows(session, occurrences)) {
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            // WHAT this row states is session-wide; WHICH reads of the
            // anchor a family may offer another writer to, and what the
            // anchor's own reads returned, are the anchor's.
            boolean atAnchor = anchor.id().equals(
                    read.endpoint().occurrence().id());
            String key = SmtLowering.locationKey(read.location());
            WriteRow write = read.observedVersion() < 0L ? null
                    : corpus.writeOf(session, key,
                            read.observedVersion());
            if (write != null) {
                JsonObject expression = corpus.session(session).expressions()
                        .expression(write.expressionRef());
                // A row that cites a ref its own session's table does not
                // hold is an inconsistency the CORPUS states, and the join
                // is the chain: composed over the sort an absent
                // expression refuses at, it declared this read's symbol as
                // a reference while another session's row declared the
                // same symbol Int -- which is how the first three-session
                // 17960 corpus (two sessions with an empty table and 28
                // cited refs each) came out of the composer as a stack
                // trace instead of a claim.
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
                // And a join whose lowering REFUSED is not a join: the
                // term it hands back is the free constant the refusal left
                // behind, and binding a read row's symbol to it declares
                // that symbol at the refusal's sort.
                int refusedBefore = lowering.openRefusals().size();
                Term value = lowering.term(expression, null,
                        "state-join:" + key + "@" + read.observedVersion());
                if (value != null
                        && lowering.openRefusals().size() == refusedBefore) {
                    lowering.declareStated(read.symbol(), value.sort);
                    joins.put(read.symbol(), "(= " + read.symbol() + " "
                            + value.text + ")");
                    if (atAnchor) joined.add(read);
                    String literal = atAnchor ? smtLiteral(
                            read.concreteValue()) : "";
                    if (!literal.isEmpty()) {
                        // What the read RETURNED, kept beside the join: the
                        // join is the chain and moves with the roots, this
                        // is the interleaving the run actually took, and the
                        // claim policy asks for it when it needs to know
                        // whether a witness rests on another writer.
                        //
                        // ONE statement per symbol, as the arrivals are:
                        // the name is the symbol's, and an occurrence
                        // publishes one row per read of its declared input
                        // -- two activations of the anchor, two rows, one
                        // symbol.  Asserted twice the query has two
                        // assertions of one :named, which z3 answers with
                        // `named expression already defined` -- an (error
                        // …), so no verdict at all, and it appeared only in
                        // the WITNESS query, which runs only once a
                        // valuation is sat.
                        String name = "observed_read__"
                                + ArtifactIO.digest(read.symbol(), 10);
                        String statement = "(assert (! (= " + read.symbol()
                                + " " + literal + ") :named " + name + "))";
                        String held = statedOnce.put(name, statement);
                        if (held == null) {
                            observed.add(statement);
                        } else if (!held.equals(statement)) {
                            refusals.add(GapRow.of(session,
                                    GapKind.UNSTATED_VALUE,
                                    GapClass.BLOCKING, read.symbol(),
                                    "two read rows of this occurrence state "
                                            + "different values for one "
                                            + "symbol: " + held + " and "
                                            + statement));
                        }
                    }
                    continue;
                }
            }
            if (joins.containsKey(read.symbol())) continue;
            // The row's own stated value.  Every row that is not joinable
            // was already asked this at step 0; a joinable one whose write
            // expression lowered to nothing is asked here.
            if (!answered.contains(read.symbol())
                    && pin(session, read, refusals, joins, answered)) {
                continue;
            }
            if (answered.contains(read.symbol())) continue;
            // What the MINT at the version this read observed gave it: no
            // write made that version, and a placeholder row of this
            // session states it under `mintVersion` (CONTRACT v2.4).  That
            // is the VM's primitive at a declared region input, keyed by
            // the version it created and by nothing else -- unique by
            // construction, where (occurrence, location) could not choose
            // between two ports of one occurrence.
            String minted = SmtLowering.mintedReadSymbol(join,
                    read.observedVersion());
            if (minted == null) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, key + "@"
                                + read.observedVersion(),
                        "two placeholder rows of this session state mint "
                                + "version " + read.observedVersion()
                                + " under different symbols: "
                                + join.mintedReadSymbols(
                                read.observedVersion())));
                continue;
            }
            if (minted.equals(read.symbol())) {
                // This row IS the one that states the version: its own
                // pin bound it at step 0, and there is nothing to add.
                continue;
            }
            if (!minted.isEmpty()) {
                Sort sort = lowering.declarations().get(minted);
                if (!lowering.stated(minted) || sort == null) {
                    refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                            GapClass.DIAGNOSTIC, minted,
                            "the read row that states this version's "
                                    + "symbol states no value for it, so "
                                    + "nothing binds it"));
                    continue;
                }
                lowering.declareStated(read.symbol(), sort);
                joins.put(read.symbol(), "(= " + read.symbol() + " "
                        + minted + ")");
                continue;
            }
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, key + "@" + read.observedVersion(),
                    "no write of this location at this version in this "
                            + "session, and the recording states no value "
                            + "the read returned"));
        }
    }

    /**
     * What this session received at each attach, as the pairing it took.
     *
     * <p>Kept beside the path rather than inside it: where a read binds to
     * the paired producer's expression (R-READ) the arrival is a
     * CONSEQUENCE of that producer's roots, so pinning it would pin them --
     * but it is still the pairing the run had, and that is the question
     * MESSAGE_PAIRING_FLIPPED asks.</p>
     */
    private List<String> arrivals(String session) {
        List<String> stated = new ArrayList<String>();
        Set<String> seen = new LinkedHashSet<String>();
        for (AttachRow attach : corpus.attachesOn(session, anchor)) {
            if (!seen.add(attach.symbol())) continue;
            String literal = smtLiteral(JsonFields.firstNonBlank(
                    attach.answeredValue(), attach.arrival()));
            if (literal.isEmpty()) continue;
            stated.add("(assert (! (= " + attach.symbol() + " " + literal
                    + ") :named observed_arrival__"
                    + ArtifactIO.digest(attach.symbol(), 10) + "))");
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
            RootDomain domain = domainOf(row);
            roots.put(row.rootId(), domain);
            if (!lowering.declared(row.symbol())) continue;
            if (row.kind() == RootKind.CLOCK) continue;
            if (row.kind() == RootKind.MARKER) {
                // A declared marker is free in {recorded, flipped}, which
                // for a Boolean is every value it has: nothing to assert.
                if (row.declared()) continue;
            }
            // FIRST: is "the" recorded value one thing at all?  A root two
            // sessions recorded differently has no corpus-wide reading, so
            // it has no corpus-wide window either: a declared domain is
            // RELATIVE to a reading, and resolving it against the seed's
            // would exclude another session from its own legal window and
            // close that session's disjunct for a reason nothing states.
            // Each path carries its own (valuationOf); nothing is asserted
            // here.
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
                        "(and (>= " + row.symbol() + " "
                                + integralLiteral(min) + ") (<= "
                                + row.symbol() + " "
                                + integralLiteral(max) + "))");
                continue;
            }
            // A root with no domain is pinned to what the recording read
            // -- UNLESS the same symbol is also a READ of its own session,
            // in which case the mint is a region INPUT published twice and
            // the read's join is the truth about it.  Pinning it here
            // would fix a value the join is free to move, and the two
            // statements about one symbol would close the path.
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
     * Whether a mint is a declared region INPUT wearing a root's clothes.
     *
     * <p>A region's declared inputs are published as symbols the region
     * READS; publishing the same symbol as a RootMintRow as well states it
     * twice, and the two statements are not the same -- a root is pinned
     * to its recording, a read joins to whatever wrote it.  Where both
     * rows exist the read is the truth and the mint pins nothing; the row
     * is named so the double publication is visible rather than
     * arbitrated in silence.</p>
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
     * A clock has no domain, only a floor.
     *
     * <p>A millisecond count since the epoch is not negative; that is the
     * one thing that makes a value a time at all, and without it a free
     * cell comes back at the 64-bit floor and every witness resting on one
     * is refused as an absurd clock.  It is not a window: two cells may sit
     * any distance apart and in any order.  What the execution fixes is
     * stated by its own decisions, which carry their readings.</p>
     *
     * <p>A CELL is the name the FORMULA names, and that is the clock root's
     * symbol as the session that read it published it -- one cell per
     * (root, session), because every execution reads a clock fresh.  A
     * decision row keys its readings by the clock's ROOT ID, which is a
     * name of the case and not of any query: asked whether the lowering
     * declared that, the answer was no for all 13 cells of hdfs-11741, so
     * {@code clockCells()} came back empty, {@code clockNecessary} answered
     * "no clocks" without a solver run, and CLOCK_SKEW was unreachable in
     * every one of the 52+ manifests published so far.  A reading whose
     * root no mint row of that session states is named, not skipped.</p>
     */
    private void clocks(List<String> cells, Map<String, Long> readings) {
        String seed = seed();
        Set<String> stated = new LinkedHashSet<String>();
        for (Map.Entry<String, Map<String, Long>> cell
                : corpus.clockCells().entrySet()) {
            int unminted = 0;
            int unnamed = 0;
            // ONE STATEMENT PER CELL, not one per (root, session).  The
            // mint's symbol is a name of the (root, occurrence) and is the
            // SAME in every session that read that root -- 11741's 13
            // roots are 13 symbols read by 7 to 13 sessions each -- so a
            // floor per session states one :named assertion eleven times,
            // which z3 answers with `named expression already defined`, an
            // (error ...) and no verdict at all for the whole query.
            String symbol = "";
            for (Map.Entry<String, Long> reading
                    : cell.getValue().entrySet()) {
                RootMintRow row = corpus.rootOf(reading.getKey(),
                        cell.getKey());
                if (row == null) {
                    unminted++;
                    continue;
                }
                if (!lowering.declared(row.symbol())) {
                    unnamed++;
                    continue;
                }
                symbol = row.symbol();
            }
            if (!symbol.isEmpty() && stated.add(symbol)) {
                cells.add(symbol);
                // THE RECORDING'S reading, by the same rule {@link #seedRow}
                // resolves a root several sessions minted: every session
                // read this cell at its own instant and they are all
                // different, so there is no corpus-wide "the reading", and
                // the one a claim about the recording rests on is the
                // seed's.  A cell the recording itself did not read is
                // named and left with no reading, so `clockNecessary` pins
                // nothing for it rather than pinning some other execution's
                // instant.
                Long recorded = seed == null ? null
                        : cell.getValue().get(seed);
                if (recorded == null) {
                    gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                            cell.getKey(), "this cell reaches the "
                                    + "composition and the recording states "
                                    + "no reading of it, so no claim can say "
                                    + "whether a witness moved it away from "
                                    + "what the run read");
                } else {
                    readings.put(symbol, recorded);
                }
                // A CLOCK CELL IS A MILLISECOND COUNT IN A JAVA long:
                // floor AND ceiling, spelled in the one place the rule
                // lives ({@link JavaPrimitiveSmtSemantics#clockDomain}).
                // Renamed with the fact it states -- no reader outside
                // this line named clock_floor__.
                lowering.assertNamed("clock_domain__"
                                + ArtifactIO.digest(symbol, 10),
                        JavaPrimitiveSmtSemantics.clockDomain(symbol));
            }
            if (unminted == 0 && unnamed == 0) continue;
            // The same fact #valuations names for a declared root no
            // formula mentions, and for the same reason: which questions
            // were ASKED is what a claim's polarity is about, and a clock
            // nothing names is a clock no claim can be made about.  One
            // row per CELL, with the counts: on hdfs-11741 it is all 13
            // cells, and the reason is pi_p and not attestation -- the
            // occurrences that read a clock are the WRITERS the anchor's
            // state joins reach (dn1 REGION.ba3902cd, 10 to 13 decisions
            // in every session), and pi_p carried the anchor occurrence's
            // own decisions alone, so no clock-bearing conjunct was ever
            // in any path.
            gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    cell.getKey(), cell.getValue().size()
                            + " sessions' decisions read this clock and no "
                            + "cell of it reaches the composition: "
                            + unminted + " state no mint row for it and "
                            + unnamed + " state a symbol no admitted "
                            + "path's formula names, so no clock claim can "
                            + "be asked about it");
        }
    }

    /**
     * The session that recorded the run, or null when that has no answer.
     *
     * <p>One spelling for "no answer", and it is the contract's: the corpus
     * answers {@code ""} to a caller that asks for a name to print, and
     * every claim that turns on WHICH session is the recording asks this,
     * because {@code ""} equals no session id and would silently read as
     * "not the seed" instead of "the corpus does not say".</p>
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
     * One question per declared root, ordinal 0 being the run as it
     * happened.
     *
     * <p>Assignment-major: the recorded valuation first, then single moves
     * ordered by the distance moved (one rotation before three), then
     * pairs.  What a root may be is its KIND and the case's declaration: a
     * declared MARKER is free in {recorded, flipped} by kind and needs no
     * declared domain, an INTEGRAL without one is pinned to what the
     * recording read and is not enumerated, and a CLOCK has its Java-long
     * domain and no
     * window.  Every root this skips is named, because which valuations
     * were asked is what the claim's polarity gate is about.</p>
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
                // No admitted path's formula names this root, so moving it
                // would produce the same query twice and decide nothing --
                // and the pin would name a constant the query never
                // declares, which z3 answers with an error instead of a
                // verdict.  Named rather than skipped in silence: on the
                // 17960 seed this is the whole reason one valuation was
                // asked, and reading it took a dig through the corpus.
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
        Collections.sort(moves, new Comparator<Map<String, String>>() {
            @Override
            public int compare(Map<String, String> left,
                               Map<String, String> right) {
                return Long.compare(distance(left), distance(right));
            }
        });
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
     * How far one move is from the recording, for the ordering.
     *
     * <p>A root whose domain is NUMERIC has a distance, and the ordering
     * asks the nearest counterfactual first.  A root whose domain is not --
     * 17960's own {@code HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED} is
     * {@code true}/{@code false} -- has no metric at all: a move either is
     * the recorded value or is not, so it counts one.  That is stated here
     * as the rule it is, rather than as a {@code NumberFormatException}
     * caught around the numeric case, because "this domain is not numeric"
     * and "this row is malformed" are two different facts and an exception
     * handler answered both with the same number.</p>
     */
    private long distance(Map<String, String> move) {
        long total = 0L;
        for (Map.Entry<String, String> entry : move.entrySet()) {
            RootDomain domain = roots.get(entry.getKey());
            if (domain == null) continue;
            String moved = entry.getValue().trim();
            String recorded = domain.recordedValue().trim();
            if (!integral(moved) || !integral(recorded)) {
                total += 1L;
                continue;
            }
            total += new BigInteger(moved)
                    .subtract(new BigInteger(recorded)).abs().longValue();
        }
        return total;
    }

    /** Whether one domain value is an integer this ordering can subtract. */
    private static boolean integral(String value) {
        if (value.isEmpty()) return false;
        int start = value.charAt(0) == '-' || value.charAt(0) == '+' ? 1 : 0;
        if (start >= value.length()) return false;
        for (int index = start; index < value.length(); index++) {
            if (!Character.isDigit(value.charAt(index))) return false;
        }
        return true;
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
        final BigInteger origin = centre;
        Collections.sort(candidates, new Comparator<BigInteger>() {
            @Override
            public int compare(BigInteger left, BigInteger right) {
                return left.subtract(origin).abs()
                        .compareTo(right.subtract(origin).abs());
            }
        });
        for (BigInteger value : candidates) values.add(value.toString());
        return values;
    }

    // ------------------------------------------------------------------
    // Reading a published SMT term.
    // ------------------------------------------------------------------

    /**
     * Whether a published term names something nothing declares.
     *
     * <p>A term the runtime writes is written over the symbols the runtime
     * declared.  One that names anything else would either fail to parse or
     * put a free constant in the formula, and a free constant is how a
     * model answers a question the execution never asked -- so the path
     * that carries it is refused, by the name of what is missing.</p>
     */
    boolean unknown(String term, List<GapRow> refusals,
                            String subject) {
        List<String> free = new ArrayList<String>();
        for (String token : SmtLowering.names(term)) {
            if (SmtLowering.BUILTIN.contains(token)) continue;
            if (lowering.defined(token)) continue;
            // The one registry says whether the recording states it, and
            // at what sort: a published term can name a recorded symbol
            // as text, without a leaf of it ever being lowered.
            if (lowering.declareStated(token)) continue;
            free.add(token);
        }
        if (free.isEmpty()) return false;
        if (refusals != null) {
            refusals.add(GapRow.of(COMPOSITION, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, subject,
                    "this term names symbols nothing declares: " + free));
        }
        return true;
    }

    /**
     * A gap the COMPOSITION raised, as against one a session published.
     *
     * <p>Every row carries a session id, and a composition is not a
     * session, so the rows it raises say so in that field rather than
     * borrowing some session's name for a fact that is not about it.</p>
     */
    static final String COMPOSITION = "composition";

    void gap(GapKind kind, GapClass cls, String subject,
                     String detail) {
        gaps.add(GapRow.of(COMPOSITION, kind, cls,
                subject == null || subject.trim().isEmpty()
                        ? anchor.render() : subject, detail));
    }
}
