package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.d3.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.d3.contract.Arm;
import edu.uva.liftlab.graphchecker.d3.contract.AttachRow;
import edu.uva.liftlab.graphchecker.d3.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.d3.contract.Endpoint;
import edu.uva.liftlab.graphchecker.d3.contract.ExportRow;
import edu.uva.liftlab.graphchecker.d3.contract.Family;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;
import edu.uva.liftlab.graphchecker.d3.contract.Interaction;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.PathEntry;
import edu.uva.liftlab.graphchecker.d3.contract.ReadRow;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RootDomain;
import edu.uva.liftlab.graphchecker.d3.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.d3.contract.TargetRow;
import edu.uva.liftlab.graphchecker.d3.contract.WriteRow;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
        private final CorpusIndex.PathRecord path;
        private final String selector;
        private final boolean fatalObserved;
        private final Set<String> interactionIds;

        private Disjunct(CorpusIndex.PathRecord path, String selector,
                         boolean fatalObserved, Set<String> interactionIds) {
            this.path = path;
            this.selector = selector;
            this.fatalObserved = fatalObserved;
            this.interactionIds = Collections.unmodifiableSet(interactionIds);
        }

        public CorpusIndex.PathRecord path() {
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
        private final String seedSessionId;

        private Composition(OccurrenceAddress anchor, String body,
                            List<Disjunct> disjuncts, List<PathEntry> paths,
                            List<Family> families, List<RootDomain> roots,
                            List<Valuation> valuations, List<GapRow> gaps,
                            List<String> clockCells,
                            Map<String, Long> clockReadings,
                            Map<String, Set<String>> unattestedRoots,
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
            this.seedSessionId = seedSessionId;
        }

        public OccurrenceAddress anchor() {
            return anchor;
        }

        /** Declarations and assertions; no {@code check-sat}. */
        public String body() {
            return body;
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

        public String seedSessionId() {
            return seedSessionId;
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

    private final CorpusIndex corpus;
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
    /** Attaches already named as unpaired; one row per attach, not per path. */
    private final Set<String> unpairedNamed = new LinkedHashSet<String>();

    private Composer(CorpusIndex corpus, OccurrenceAddress anchor,
                     Map<String, RootDomain> declaredDomains,
                     int maxValuations) {
        this.corpus = corpus;
        this.anchor = anchor;
        this.declaredDomains = declaredDomains == null
                ? Collections.<String, RootDomain>emptyMap()
                : declaredDomains;
        this.maxValuations = maxValuations <= 0 ? 64 : maxValuations;
        this.lowering = new SmtLowering(corpus.declaredSymbols());
    }

    /** Composes the declared occurrence; a missing one is a claim, not a
     *  crash. */
    public static Composition compose(CorpusIndex corpus,
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

        // Which recording a claim is about has to have one answer.  Two
        // sessions that focused nothing are two recordings, and
        // RECORDED_FAILURE_EXPLAINED and MESSAGE_PAIRING_FLIPPED would each
        // pick whichever came first.
        List<String> seeds = new ArrayList<String>();
        for (SessionReader session : corpus.sessions()) {
            if (!session.explored()) seeds.add(session.sessionId());
        }
        if (seeds.size() > 1) {
            gap(GapKind.UNSTATED_VALUE, GapClass.BLOCKING, seeds.toString(),
                    "more than one session of this corpus focused nothing, "
                            + "so which one is the recording has no answer");
        }

        List<Disjunct> disjuncts = new ArrayList<Disjunct>();
        List<PathEntry> entries = new ArrayList<PathEntry>();
        List<CorpusIndex.PathRecord> admitted = admit();
        int ordinal = 0;
        for (CorpusIndex.PathRecord path : admitted) {
            Disjunct disjunct = compose(path, ordinal);
            if (disjunct != null) {
                disjuncts.add(disjunct);
                entries.add(PathEntry.of(path.pathId(), path.sessionId(),
                        disjunct.selector(), disjunct.fatalObserved()));
                ordinal++;
            }
        }
        if (disjuncts.isEmpty()) {
            gap(GapKind.ADMISSION_GAP, GapClass.BLOCKING, anchor.render(),
                    "no session of this corpus published a path that "
                            + "reached the declared occurrence");
        } else {
            List<String> selectors = new ArrayList<String>();
            for (Disjunct disjunct : disjuncts) {
                selectors.add(disjunct.selector());
            }
            lowering.assertNamed("target_path_partition",
                    exactlyOne(selectors));
            // The disjunction is over the SELECTORS: each path already
            // asserts "selector => (pi and phi)", so asserting that some
            // selector holds says exactly OR_p (pi_p and phi_p), without
            // writing every path's formula into the artifact twice.
            lowering.assertNamed("fatal_target",
                    VmTermLowering.or(selectors));
        }

        List<String> clockCells = new ArrayList<String>();
        Map<String, Long> clockReadings = new LinkedHashMap<String, Long>();
        clocks(clockCells, clockReadings);
        domains();
        lowering.assertIdentitiesDistinct();
        for (String cut : lowering.cuts()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, cut,
                    lowering.unsupportedDetail().containsKey(cut)
                            ? lowering.unsupportedDetail().get(cut)
                            : "the propagation did not carry this value");
        }

        return new Composition(anchor, lowering.body(), disjuncts, entries,
                new ArrayList<Family>(families.values()),
                new ArrayList<RootDomain>(roots.values()), valuations(),
                gaps, clockCells, clockReadings, unattestedRoots,
                corpus.seedSessionId());
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
    private List<CorpusIndex.PathRecord> admit() {
        List<CorpusIndex.PathRecord> admitted =
                new ArrayList<CorpusIndex.PathRecord>();
        List<TargetRow> targets = corpus.targetsAt(anchor);
        if (targets.isEmpty()) {
            gap(GapKind.DECLARATION_MISSING, GapClass.BLOCKING,
                    anchor.render(), "no session of this corpus published a "
                            + "target row for the declared occurrence");
            return admitted;
        }
        for (TargetRow target : targets) {
            CorpusIndex.PathRecord path = corpus.path(target.sessionId(),
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
            admitted.add(path);
        }
        return admitted;
    }

    // ------------------------------------------------------------------
    // One path.
    // ------------------------------------------------------------------

    private Disjunct compose(CorpusIndex.PathRecord path, int ordinal) {
        String session = path.sessionId();
        TargetRow target = corpus.target(session, anchor);
        if (target == null) return null;
        String selector = "path_selector__" + ordinal + "__"
                + JsonText.digest(path.pathId(), 10);
        lowering.declare(selector, Sort.BOOL);
        lowering.begin(session, corpus.joinOf(session));

        List<String> terms = new ArrayList<String>();
        List<GapRow> refusals = new ArrayList<GapRow>();

        // (1) The valuation this replay ran under, for every VARIED root.
        //     A replay's assignments are not all visible as decisions -- a
        //     root can be written and never branched on -- and the
        //     execution still happened under that value.  A root every
        //     session read the same way is pinned by its own domain and is
        //     not repeated here.
        terms.addAll(valuationOf(session, refusals));

        // (2) What this path read at each handoff of the anchor: answered,
        //     else the paired arm where it carries a movable root, else
        //     this session's own arrival.  Never a corpus-wide arrival.
        Set<String> interactionIds = new LinkedHashSet<String>();
        terms.addAll(handoffReads(session, interactionIds, refusals));

        // (3) The state joins: read := the expression of the write version
        //     it observed, within this session.
        terms.addAll(stateJoins(session, refusals));

        // (4) pi_p, as the runtime published it.
        for (DecisionRow decision : path.decisions()) {
            String term = decision.term();
            if (unknown(term, refusals, "decision " + decision.siteId()
                    + "#" + decision.ordinal())) {
                continue;
            }
            terms.add(term);
        }

        // (5) phi_p is the FATAL arm as published; the composer never
        //     re-derives the polarity.  Re-deriving it negated a term that
        //     was already the complement, and every healthy-observed path
        //     was handed its own observation back.
        String phi = target.phiTerm();
        if (!unknown(phi, refusals, "phi of " + anchor.render())) {
            terms.add(phi);
        }

        terms.addAll(lowering.end());
        for (String refusal : lowering.openRefusals()) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, refusal,
                    "this path rests on a value the recording does not "
                            + "state, so it is not in the disjunction"));
        }
        if (!refusals.isEmpty()) {
            gaps.addAll(refusals);
            return null;
        }

        lowering.assertNamed("path_fatal__" + ordinal,
                "(=> " + selector + " " + VmTermLowering.and(terms) + ")");

        // (6) The families of every interaction this path's chain reaches,
        //     each under this path's selector.
        closeFamilies(path, ordinal, selector, interactionIds);
        return new Disjunct(path, selector, target.observedFatal(),
                interactionIds);
    }

    /** What this replay ran every varied root at. */
    private List<String> valuationOf(String session,
                                     List<GapRow> refusals) {
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
                // execution that never read it.
                if (any.declared() && lowering.declared(any.symbol())) {
                    refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                            GapClass.BLOCKING, any.rootId(),
                            "this session minted no value for a declared "
                                    + "root the composition constrains"));
                }
                continue;
            }
            if (!corpus.varied(row.rootId())) continue;
            lowering.declare(row.symbol(),
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
            String literal = JsonText.smtLiteral(row.recordedValue());
            if (literal.isEmpty()) continue;
            valuation.add("(= " + row.symbol() + " " + literal + ")");
        }
        return valuation;
    }

    /** One declared root's window around THIS session's reading, or "". */
    private String windowOf(RootMintRow row) {
        if (!row.declared() || row.kind() == RootKind.MARKER) return "";
        RootDomain domain = domainOf(row);
        String min = domain.min();
        String max = domain.max();
        if (min == null || max == null || JsonText.smtInteger(min).isEmpty()
                || JsonText.smtInteger(max).isEmpty()) {
            return "";
        }
        return "(and (>= " + row.symbol() + " " + JsonText.smtInteger(min)
                + ") (<= " + row.symbol() + " " + JsonText.smtInteger(max)
                + "))";
    }

    /**
     * What this path read at each of the anchor's handoffs.
     *
     * <p>Three rules, in order, and all three are this path's OWN fact:</p>
     * <ol>
     *   <li>an obligation answered the mint: that value;</li>
     *   <li>otherwise, where the recording states which producer endpoint
     *       delivered it, that producer's arm is attested, and its
     *       expression mentions a root the case may move: the arm's
     *       expression.  The consumer's literal is a CONSEQUENCE of that
     *       root's recorded value, and pinning it would pin the root on
     *       every such path (R-READ);</li>
     *   <li>otherwise the arrival this session recorded.</li>
     * </ol>
     */
    private List<String> handoffReads(String session,
                                      Set<String> interactionIds,
                                      List<GapRow> refusals) {
        List<String> reads = new ArrayList<String>();
        Set<String> stated = new LinkedHashSet<String>();
        for (AttachRow attach : corpus.attachesRead(session, anchor)) {
            if (!stated.add(attach.symbol())) continue;
            Interaction interaction = attach.interaction();
            if (interaction != null) {
                interactionIds.add(interaction.id());
            } else {
                // The wire delivered something and the recording cannot say
                // from where.  The arrival is still this path's own fact,
                // stated below, but there is no interaction to build a
                // family on -- and a variable no family constrains is the
                // one thing a witness must not rest on unremarked.
                unpaired(session, attach);
            }
            if (attach.answered()) {
                String literal = JsonText.smtLiteral(attach.answeredValue());
                if (literal.isEmpty()) {
                    refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                            GapClass.DIAGNOSTIC, attach.symbol(),
                            "an answered attach whose value is not a "
                                    + "literal: " + attach.answeredValue()));
                    continue;
                }
                String read = bind(attach.symbol(), literal, attach,
                        refusals);
                if (!read.isEmpty()) reads.add(read);
                continue;
            }
            String paired = pairedArm(session, attach);
            if (!paired.isEmpty()) {
                reads.add("(= " + attach.symbol() + " " + paired + ")");
                continue;
            }
            String arrival = JsonText.smtLiteral(attach.arrival());
            if (arrival.isEmpty()) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, attach.symbol(),
                        "this session recorded no arrival at this attach "
                                + "and no producer arm delivers it"));
                continue;
            }
            String read = bind(attach.symbol(), arrival, attach, refusals);
            if (!read.isEmpty()) reads.add(read);
        }
        return reads;
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
        lowering.declare(symbol, sort);
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
     * The paired producer's delivered expression, when it may carry a move.
     *
     * <p>Only where the arm is ATTESTED (the producer occurrence has
     * decisions in this session, so the composition can say under what the
     * delivery happened) and its expression mentions a root the case
     * declared a domain for.  Where the arm carries no movable root, the
     * literal the consumer read states a fact the root cannot explain, and
     * the literal is kept.</p>
     */
    private String pairedArm(String session, AttachRow attach) {
        Endpoint producer = attach.producer();
        if (producer == null) return "";
        if (!corpus.attested(session, producer.occurrence())) return "";
        for (ExportRow export : corpus.exportsOf(producer)) {
            if (!export.sessionId().equals(session)) continue;
            Term delivered = lower(session, export, "paired-arm");
            if (delivered == null) continue;
            if (!movableRoot(delivered.text)) continue;
            // The arm's own sort declares the variable: the arrival's
            // spelling says what it looked like, the delivery says what it
            // is, and one variable has one sort.
            lowering.declare(attach.symbol(), delivered.sort);
            return delivered.text;
        }
        return "";
    }

    /**
     * Read := the expression of the write version it observed.
     *
     * <p>JOIN, then PIN to what the recording says the read returned, then
     * REFUSE by name.  There is no "latest write" and no choice between
     * writers: the version the read observed is a recorded fact of one
     * session's own counter.</p>
     */
    private List<String> stateJoins(String session, List<GapRow> refusals) {
        List<String> joins = new ArrayList<String>();
        for (ReadRow read : corpus.readsAt(session, anchor)) {
            if (read.symbol() == null || read.symbol().isEmpty()) continue;
            String key = SmtLowering.locationKey(read.location());
            WriteRow write = read.observedVersion() < 0L ? null
                    : corpus.write(session, key, read.observedVersion());
            if (write != null) {
                JsonObject expression = corpus.session(session).expressions()
                        .expression(write.expressionRef());
                Term value = lowering.term(expression, null,
                        "state-join:" + key + "@" + read.observedVersion());
                if (value != null) {
                    lowering.declare(read.symbol(), value.sort);
                    joins.add("(= " + read.symbol() + " " + value.text + ")");
                    continue;
                }
            }
            String literal = JsonText.smtLiteral(read.concreteValue());
            if (!literal.isEmpty()) {
                Sort sort = scalarSort(read.javaType(), session,
                        read.symbol(), refusals);
                if (sort == null) continue;
                lowering.declare(read.symbol(), sort);
                joins.add("(= " + read.symbol() + " " + literal + ")");
                continue;
            }
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, key + "@" + read.observedVersion(),
                    "no write of this location at this version in this "
                            + "session, and the recording states no value "
                            + "the read returned"));
        }
        return joins;
    }

    // ------------------------------------------------------------------
    // Families.
    // ------------------------------------------------------------------

    /**
     * Every delivery the corpus recorded at one interaction, and at every
     * interaction reached through one.
     *
     * <p>A family is keyed by the INTERACTION -- both endpoints -- so a
     * producer on the same port at another occurrence, another node or
     * another attempt contributes nothing to it.  An arm's expression may
     * itself mention a handoff variable, because a producer forwards what
     * it was handed; those families are closed transitively, which is what
     * makes a multi-hop transfer one formula instead of a free constant.</p>
     */
    private void closeFamilies(CorpusIndex.PathRecord path, int ordinal,
                               String selector, Set<String> reached) {
        List<String> queue = new ArrayList<String>();
        for (AttachRow attach : corpus.attachesRead(path.sessionId(),
                anchor)) {
            Interaction interaction = attach.interaction();
            if (interaction == null) continue;
            queue.add(attach.symbol() + " " + interaction.id());
        }
        Set<String> closed = new LinkedHashSet<String>();
        while (!queue.isEmpty()) {
            String item = queue.remove(0);
            if (!closed.add(item)) continue;
            int split = item.indexOf(' ');
            String symbol = item.substring(0, split);
            String interactionId = item.substring(split + 1);
            Interaction interaction = corpus.interaction(interactionId);
            if (interaction == null) continue;
            reached.add(interactionId);
            List<String> arms = new ArrayList<String>();
            List<Arm> rows = new ArrayList<Arm>();
            for (AttachRow paired : corpus.attachesOf(interaction)) {
                String producerSession = paired.sessionId();
                for (ExportRow export
                        : corpus.exportsOf(interaction.producer())) {
                    if (!export.sessionId().equals(producerSession)) continue;
                    Term delivered = lower(producerSession, export,
                            "arm:" + interactionId);
                    if (delivered == null) continue;
                    String text = delivered.text;
                    lowering.declare(symbol, delivered.sort);
                    boolean attested = corpus.attested(producerSession,
                            interaction.producer().occurrence());
                    List<String> conjuncts = new ArrayList<String>();
                    CorpusIndex.PathRecord producerPath = corpus.path(
                            producerSession,
                            interaction.producer().occurrence());
                    if (attested && producerPath != null) {
                        conjuncts.addAll(prefix(producerPath, export));
                    }
                    Set<String> guardRoots = new LinkedHashSet<String>();
                    conjuncts.addAll(guard(producerSession, text,
                            guardRoots));
                    conjuncts.add("(= " + symbol + " " + text + ")");
                    arms.add(VmTermLowering.and(conjuncts));
                    rows.add(Arm.of(producerPath == null ? producerSession
                                    : producerPath.pathId(),
                            attested && producerPath != null
                                    ? producerPath.pathId() : "",
                            export.expressionRef(), guardRoots, attested));
                    if (!attested) {
                        Set<String> held = unattestedRoots.get(interactionId);
                        if (held == null) {
                            held = new LinkedHashSet<String>();
                            unattestedRoots.put(interactionId, held);
                        }
                        held.addAll(declaredRootsIn(text));
                        gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                                interactionId, "the producer ran concretely "
                                        + "in session " + producerSession
                                        + ": the arm states what was "
                                        + "delivered, and no witness may "
                                        + "move a root inside it");
                    }
                    // Nested: what this arm delivers may itself be a value
                    // its own replay was handed.
                    for (String nested : handoffSymbolsIn(text)) {
                        if (nested.equals(symbol)) continue;
                        AttachRow source = corpus.attachOfSymbol(nested,
                                producerSession);
                        if (source == null || source.interaction() == null) {
                            continue;
                        }
                        queue.add(nested + " "
                                + source.interaction().id());
                    }
                }
            }
            if (arms.isEmpty()) {
                gap(GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                        interactionId, "no session of this corpus published "
                                + "what was delivered at this interaction");
                continue;
            }
            families.put(interactionId, Family.of(interactionId, rows));
            lowering.assertNamed("handoff_family__" + ordinal + "__"
                            + JsonText.digest(interactionId, 12),
                    "(=> " + selector + " " + VmTermLowering.or(arms) + ")");
        }
    }

    /**
     * The producer path condition an arm is guarded by.
     *
     * <p>What the delivering replay had decided BY THE TIME it exported.  A
     * decision it took afterwards is not a reason the delivery happened, and
     * guarding the arm with it would make the arm unavailable wherever the
     * rest of that replay went another way.  The cut is the session's own
     * monotonic event order: {@code decision.seq() < export.seq()}.</p>
     */
    private List<String> prefix(CorpusIndex.PathRecord producerPath,
                                ExportRow export) {
        List<String> conjuncts = new ArrayList<String>();
        for (DecisionRow decision : producerPath.decisions()) {
            if (decision.seq() >= export.seq()) continue;
            if (unknown(decision.term(), null, "")) continue;
            conjuncts.add(decision.term());
        }
        return conjuncts;
    }

    /**
     * An attach whose producer the recording does not name.
     *
     * <p>Two different absences, and the row says which.  A producer
     * endpoint that exists but could not be addressed in full is
     * LINEAGE_LOST -- the interaction is there and the naming failed.  An
     * attach with no producer at all is an UNSTATED_VALUE: the recording
     * does not say the delivery happened, only that a value arrived.</p>
     */
    private void unpaired(String session, AttachRow attach) {
        if (!unpairedNamed.add(session + "|" + attach.endpoint().id())) {
            return;
        }
        Endpoint producer = attach.producer();
        boolean degraded = producer != null
                && producer.occurrence() != null
                && producer.occurrence().lineageLost();
        gaps.add(GapRow.of(session,
                producer == null && !degraded ? GapKind.UNSTATED_VALUE
                        : GapKind.LINEAGE_LOST,
                GapClass.DIAGNOSTIC, attach.endpoint().toString(),
                "this attach names no producer endpoint, so the value it "
                        + "received joins no interaction and has no family; "
                        + "the arrival this session recorded is all the "
                        + "composition states about it"));
    }

    /**
     * The delivering replay's valuation of ONLY the roots this arm's own
     * expression depends on.
     *
     * <p>A root the delivery does not mention rules out nothing about it
     * and only makes the family false at valuations no delivering replay
     * ran under -- four of bug3's nine families were individually
     * unsatisfiable at a flipped marker for exactly that reason.</p>
     */
    private List<String> guard(String session, String armText,
                               Set<String> guardRoots) {
        List<String> guards = new ArrayList<String>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = corpus.root(entry.getKey(), session);
            if (row == null || row.kind() == RootKind.CLOCK) continue;
            if (!corpus.varied(row.rootId())) continue;
            if (!mentions(armText, row.symbol())) continue;
            String literal = JsonText.smtLiteral(row.recordedValue());
            if (literal.isEmpty()) continue;
            guardRoots.add(row.rootId());
            guards.add("(= " + row.symbol() + " " + literal + ")");
        }
        return guards;
    }

    /**
     * One export's expression, lowered in its own session's scope.
     *
     * <p>Its own session: the identities inside it are that execution's
     * objects, and the reads inside it join to that execution's write log.
     * An arm lowered in the consumer's scope would state one replay's
     * history of another replay's objects.</p>
     */
    private Term lower(String session, ExportRow export, String origin) {
        SessionReader reader = corpus.session(session);
        if (reader == null) return null;
        JsonObject expression = reader.expressions()
                .expression(export.expressionRef());
        if (expression == null) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    export.expressionRef(), "the session's expression table "
                            + "holds no expression under this ref");
            return null;
        }
        lowering.begin(session, corpus.joinOf(session));
        Term value = lowering.term(expression, null, origin);
        List<String> refused = new ArrayList<String>(
                lowering.openRefusals());
        lowering.end();
        if (value == null || !refused.isEmpty()) {
            for (String refusal : refused) {
                gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, refusal,
                        "an arm of this corpus rests on a value the "
                                + "recording does not state");
            }
            return null;
        }
        return value;
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
                                + JsonText.smtInteger(min) + ") (<= "
                                + row.symbol() + " "
                                + JsonText.smtInteger(max) + "))");
                continue;
            }
            String literal = JsonText.smtLiteral(row.recordedValue());
            if (literal.isEmpty()) continue;
            lowering.assertNamed("root_domain__" + ordinal++,
                    "(= " + row.symbol() + " " + literal + ")");
        }
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
     */
    private void clocks(List<String> cells, Map<String, Long> readings) {
        for (Map.Entry<String, Map<String, Long>> cell
                : corpus.clockCells().entrySet()) {
            if (!lowering.declared(cell.getKey())) continue;
            cells.add(cell.getKey());
            for (Map.Entry<String, Long> reading
                    : cell.getValue().entrySet()) {
                readings.put(cell.getKey(), reading.getValue());
                break;
            }
            lowering.assertNamed("clock_floor__"
                            + JsonText.digest(cell.getKey(), 10),
                    "(>= " + cell.getKey() + " 0)");
        }
    }

    private RootMintRow seedRow(List<RootMintRow> rows) {
        String seed = corpus.seedSessionId();
        if (seed != null) {
            for (RootMintRow row : rows) {
                if (row.sessionId().equals(seed)) return row;
            }
        }
        return rows.get(0);
    }

    /** The case's declaration where there is one, the mint's otherwise. */
    private RootDomain domainOf(RootMintRow row) {
        RootDomain declared = declaredDomains.get(row.rootId());
        if (declared == null) declared = declaredDomains.get(row.symbol());
        String min = declared == null ? row.domainMin() : declared.min();
        String max = declared == null ? row.domainMax() : declared.max();
        return RootDomain.of(row.rootId(), row.kind(), row.recordedValue(),
                resolve(min, row.recordedValue()),
                resolve(max, row.recordedValue()));
    }

    /**
     * One bound, absolute.
     *
     * <p>Two spellings, one notion: an absolute bound is the value itself,
     * and a bound written {@code +k} or {@code -k} is that many steps from
     * what the recording read -- the only way a case can state the domain
     * of a counter whose zero nobody chose.</p>
     */
    private static String resolve(String bound, String recorded) {
        String stated = bound == null ? "" : bound.trim();
        if (stated.isEmpty()) return null;
        if (!stated.startsWith("+") && !stated.startsWith("-")) {
            return JsonText.smtInteger(stated).isEmpty() ? null : stated;
        }
        String offset = stated.startsWith("+") ? stated.substring(1) : stated;
        if (JsonText.smtInteger(offset).isEmpty()
                || JsonText.smtInteger(recorded).isEmpty()) {
            return null;
        }
        return new BigInteger(recorded.trim())
                .add(new BigInteger(offset.trim())).toString();
    }

    /**
     * One question per declared root, ordinal 0 being the run as it
     * happened.
     *
     * <p>Assignment-major: the recorded valuation first, then single moves
     * ordered by the distance moved (one rotation before three), then
     * pairs.  A root the case declared no domain for is not enumerated --
     * the composition pinned it to what the recording read.</p>
     */
    private List<Valuation> valuations() {
        List<String> declared = new ArrayList<String>();
        Map<String, List<String>> alternatives =
                new LinkedHashMap<String, List<String>>();
        for (Map.Entry<String, RootDomain> entry : roots.entrySet()) {
            RootDomain domain = entry.getValue();
            if (domain.kind() == RootKind.CLOCK) continue;
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null || !row.declared()
                    || !lowering.declared(row.symbol())) {
                continue;
            }
            List<String> values = alternativesOf(domain);
            if (values.isEmpty()) continue;
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

    /** How far one move is from the recording, for the ordering. */
    private long distance(Map<String, String> move) {
        long total = 0L;
        for (Map.Entry<String, String> entry : move.entrySet()) {
            RootDomain domain = roots.get(entry.getKey());
            if (domain == null) continue;
            try {
                total += new BigInteger(entry.getValue().trim())
                        .subtract(new BigInteger(
                                domain.recordedValue().trim())).abs()
                        .longValue();
            } catch (NumberFormatException notAnInteger) {
                total += 1L;
            }
        }
        return total;
    }

    private Valuation valuation(int ordinal, Map<String, String> assignment,
                                Map<String, String> moved) {
        List<String> assertions = new ArrayList<String>();
        for (Map.Entry<String, String> entry : assignment.entrySet()) {
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null) continue;
            String literal = JsonText.smtLiteral(entry.getValue());
            if (literal.isEmpty()) continue;
            assertions.add("(assert (! (= " + row.symbol() + " " + literal
                    + ") :named valuation__" + JsonText.smtName(row.symbol())
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
        if (min == null || max == null || JsonText.smtInteger(min).isEmpty()
                || JsonText.smtInteger(max).isEmpty()) {
            return values;
        }
        BigInteger low = new BigInteger(min.trim());
        BigInteger high = new BigInteger(max.trim());
        BigInteger centre = JsonText.smtInteger(recorded).isEmpty()
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

    /** Whether one symbol occurs in a term as a symbol, not a substring. */
    private static boolean mentions(String term, String symbol) {
        return SmtLowering.mentions(term, symbol);
    }

    /** The declared roots one lowered expression mentions. */
    private Set<String> declaredRootsIn(String term) {
        Set<String> found = new LinkedHashSet<String>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null || !row.declared()) continue;
            if (mentions(term, row.symbol())) found.add(row.rootId());
        }
        return found;
    }

    /** Whether any root the case may move occurs in this term. */
    private boolean movableRoot(String term) {
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = corpus.anyRoot(entry.getKey());
            if (row == null || !row.declared()) continue;
            RootDomain domain = domainOf(row);
            if (domain.pinned() && row.kind() != RootKind.MARKER) continue;
            if (mentions(term, row.symbol())) return true;
        }
        return false;
    }

    /** The handoff variables one lowered expression mentions. */
    private List<String> handoffSymbolsIn(String term) {
        List<String> found = new ArrayList<String>();
        for (String symbol : corpus.handoffSymbols()) {
            if (mentions(term, symbol)) found.add(symbol);
        }
        return found;
    }

    /**
     * Whether a published term names something nothing declares.
     *
     * <p>A term the runtime writes is written over the symbols the runtime
     * declared.  One that names anything else would either fail to parse or
     * put a free constant in the formula, and a free constant is how a
     * model answers a question the execution never asked -- so the path
     * that carries it is refused, by the name of what is missing.</p>
     */
    private boolean unknown(String term, List<GapRow> refusals,
                            String subject) {
        List<String> free = new ArrayList<String>();
        for (String token : tokens(term)) {
            if (BUILTIN.contains(token)) continue;
            if (lowering.declared(token)) continue;
            if (corpus.declaredSymbols().containsKey(token)) {
                lowering.declare(token,
                        corpus.declaredSymbols().get(token));
                continue;
            }
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

    /** Every symbol-shaped token of one SMT term. */
    static List<String> tokens(String term) {
        List<String> tokens = new ArrayList<String>();
        if (term == null) return tokens;
        StringBuilder token = new StringBuilder();
        boolean quoted = false;
        for (int index = 0; index < term.length(); index++) {
            char value = term.charAt(index);
            if (value == '"') {
                quoted = !quoted;
                continue;
            }
            if (quoted) continue;
            if (Character.isLetterOrDigit(value) || value == '_'
                    || value == '.' || value == '$' || value == '\''
                    || value == '-' && token.length() > 0) {
                token.append(value);
                continue;
            }
            take(tokens, token);
        }
        take(tokens, token);
        return tokens;
    }

    private static void take(List<String> tokens, StringBuilder token) {
        if (token.length() == 0) return;
        String value = token.toString();
        token.setLength(0);
        if (value.isEmpty()) return;
        char first = value.charAt(0);
        if (Character.isDigit(first) || first == '-' || first == '.') return;
        tokens.add(value);
    }

    private static final Set<String> BUILTIN = new LinkedHashSet<String>(
            Arrays.asList("and", "or", "not", "xor", "ite", "let", "forall",
                    "exists", "distinct", "true", "false", "div", "mod",
                    "abs", "rem", "select", "store", "as", "const", "lambda",
                    "is", "bvadd", "bvsub", "bvmul", "bvand", "bvor",
                    "bvxor", "bvnot", "bvshl", "bvlshr", "bvashr", "bvsdiv",
                    "bvudiv", "bvsrem", "bvurem", "bvule", "bvult", "bvsle",
                    "bvslt", "bvuge", "bvugt", "bvsge", "bvsgt", "concat",
                    "extract", "zero_extend", "sign_extend", "Int", "Bool",
                    "Real", "String", "Ref", "Value", "AssocState",
                    "IndexedState", "FloatingPoint", "RoundingMode",
                    "roundNearestTiesToEven", "RNE", "RTZ", "RTP", "RTN",
                    "RNA", "nullRef", "java_int_wrap", "java_long_wrap",
                    "java_int_to_string", "indexed_state_of",
                    "assoc_state_of", "indexed_read", "indexed_write",
                    "indexed_append", "indexed_insert", "indexed_remove",
                    "indexed_contains", "indexed_size", "indexed_elements",
                    "assoc_has", "assoc_read", "assoc_key_at",
                    "assoc_value_at", "assoc_put", "assoc_remove",
                    "assoc_size", "assoc_present", "assoc_values",
                    "assoc_order", "assoc_position", "VByte", "VChar",
                    "VShort", "VInt", "VLong", "VFloat", "VDouble", "VBool",
                    "VRef", "VString", "valueByte", "valueChar", "valueShort",
                    "valueInt", "valueLong", "valueFloat", "valueDouble",
                    "valueBool", "valueRef", "valueString", "str", "fp",
                    "to_real", "to_int", "divisible"));

    private static String exactlyOne(List<String> selectors) {
        if (selectors.size() == 1) return selectors.get(0);
        StringBuilder sum = new StringBuilder("(= (+");
        for (String selector : selectors) {
            sum.append(" (ite ").append(selector).append(" 1 0)");
        }
        return sum.append(") 1)").toString();
    }

    /**
     * A gap the COMPOSITION raised, as against one a session published.
     *
     * <p>Every row carries a session id, and a composition is not a
     * session, so the rows it raises say so in that field rather than
     * borrowing some session's name for a fact that is not about it.</p>
     */
    static final String COMPOSITION = "composition";

    private void gap(GapKind kind, GapClass cls, String subject,
                     String detail) {
        gaps.add(GapRow.of(COMPOSITION, kind, cls,
                subject == null || subject.trim().isEmpty()
                        ? anchor.render() : subject, detail));
    }
}
