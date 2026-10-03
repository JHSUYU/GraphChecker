package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Term;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Clock;
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
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.PathEntry;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootDomain;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
 * valuation are per session (CONTRACT-SPEC §5); a family sits under its
 * session's
 * selector, so an arm-less family kills only its disjunct; an arm is
 * guarded by its replay's valuation of only the roots its expression
 * depends on (CONTRACT-SPEC §4).</p>
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
        /** The name of its {@code (=> selector (and pi ... phi ...))}. */
        private final String fatal;
        /** That implication with phi, the fatal arm, left out: what the
         *  path's own run satisfied ({@link Composition#withoutFatalArm}). */
        private final String withoutFatalArm;
        private final boolean fatalObserved;
        private final Set<String> interactionIds;
        private final Set<String> restsOn;

        private Disjunct(Corpus.RecordedPath path, String selector,
                         String fatal, String withoutFatalArm,
                         boolean fatalObserved, Set<String> interactionIds,
                         Set<String> restsOn) {
            this.path = path;
            this.selector = selector;
            this.fatal = fatal;
            this.withoutFatalArm = withoutFatalArm;
            this.fatalObserved = fatalObserved;
            this.interactionIds = Collections.unmodifiableSet(interactionIds);
            this.restsOn = Collections.unmodifiableSet(restsOn);
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

        /** The tracked locations its fatal predicate rests on. */
        public Set<String> restsOn() {
            return restsOn;
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
        private final Map<String, String> clockBefore;
        private final Map<String, Set<String>> unattestedRoots;
        private final Map<String, List<String>> observedReads;
        private final Map<String, List<String>> observedArrivals;
        private final Map<String, List<String>> heldArrivals;
        private final Map<String, ComposedFamilies.ArmChoice> armChoices;
        private final Map<String, List<String>> ownArms;
        private final String seedSessionId;
        /** Where each top-level command of the body ends, and the path
         *  selector it is guarded by (null: every path's); #pathQuery. */
        private final int[] commandEnds;
        private final String[] commandGuards;

        /** The composer's state once every path is composed. */
        private Composition(Composer composed, String body,
                            List<Disjunct> disjuncts, List<PathEntry> paths,
                            List<Valuation> valuations,
                            List<String> clockCells,
                            Map<String, Long> clockReadings,
                            Map<String, Long> clockNanos,
                            Map<String, String> clockBefore) {
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
            this.clockBefore = Collections.unmodifiableMap(clockBefore);
            this.unattestedRoots =
                    Collections.unmodifiableMap(composed.unattestedRoots);
            this.observedReads =
                    Collections.unmodifiableMap(composed.observedReads);
            this.observedArrivals =
                    Collections.unmodifiableMap(composed.observedArrivals);
            this.heldArrivals =
                    Collections.unmodifiableMap(composed.heldArrivals);
            this.armChoices = composed.composedFamilies.armChoices();
            this.ownArms = composed.composedFamilies.ownArms();
            this.seedSessionId = composed.seed();
            List<Integer> ends = new ArrayList<Integer>();
            List<String> guards = new ArrayList<String>();
            commands(body, new LinkedHashSet<String>(
                    Composer.selectors(disjuncts)), ends, guards);
            this.commandEnds = new int[ends.size()];
            for (int index = 0; index < ends.size(); index++) {
                this.commandEnds[index] = ends.get(index);
            }
            this.commandGuards = guards.toArray(new String[0]);
        }

        public OccurrenceAddress anchor() {
            return anchor;
        }

        /** Declarations and assertions; no {@code check-sat}. */
        public String body() {
            return body;
        }

        /**
         * One question: the body plus these assertions, written out to its
         * reader, never copied (a body runs past 200 MB and is asked on
         * many threads at once, {@link Disjunction}).  The body is
         * spelled legally once ({@link SmtLowering#body}); the assertions
         * are spelled here, since pins name raw symbols such as
         * {@code CLOCK/...#...} and a bare {@code #} is a bit-vector literal
         * to z3.  Spelling is token-local, so each assertion spelled alone
         * spells the text.
         */
        public ArtifactIO.Body query(List<String> assertions) {
            List<String> legal = legal(assertions);
            return output -> {
                output.write(body);
                for (String assertion : legal) output.write(assertion);
            };
        }

        /**
         * One path's question: the body without the commands another path's
         * selector guards, this path's selector asserted, plus these
         * assertions.  The partition forces every other selector false, so
         * each command dropped held vacuously: the answer is
         * {@link #query}'s with the selector asserted, but z3 reads what
         * every path shares and this path's own text, not every path's.
         */
        public ArtifactIO.Body pathQuery(String selector,
                                         List<String> assertions) {
            List<String> legal = legal(assertions);
            legal.add(0, "\n(assert " + selector + ")\n");
            return output -> {
                int start = 0;
                for (int index = 0; index < commandEnds.length; index++) {
                    if (kept(index, selector)) {
                        output.write(body, start, commandEnds[index] - start);
                    }
                    start = commandEnds[index];
                }
                for (String assertion : legal) output.write(assertion);
            };
        }

        /**
         * One path's question with its fatal arm left out ({@link
         * #pathQuery}, its {@code path_fatal__} command replaced by the
         * same implication without phi): what its own run satisfied, every
         * root free.  Unsat, the composition contradicts the run itself
         * (ClaimPolicy's self-check).
         */
        public ArtifactIO.Body withoutFatalArm(String selector) {
            Disjunct disjunct = bySelector(selector);
            String own = "\n(assert " + SmtNames.legalSymbols(
                    disjunct.withoutFatalArm) + ")\n";
            String named = ":named " + disjunct.fatal + "))";
            return output -> {
                int start = 0;
                for (int index = 0; index < commandEnds.length; index++) {
                    int end = commandEnds[index];
                    if (!kept(index, selector)) {
                        start = end;
                        continue;
                    }
                    if (selector.equals(commandGuards[index])
                            && body.startsWith(named, end - named.length())) {
                        output.write(own);
                    } else {
                        output.write(body, start, end - start);
                    }
                    start = end;
                }
                output.write("\n(assert " + selector + ")\n");
            };
        }

        private boolean kept(int command, String selector) {
            String guard = commandGuards[command];
            return guard == null || guard.equals(selector);
        }

        /** Each assertion spelled legally, one per line. */
        private static List<String> legal(List<String> assertions) {
            List<String> legal = new ArrayList<String>();
            if (assertions == null) return legal;
            for (String assertion : assertions) {
                if (assertion == null || assertion.isEmpty()) continue;
                legal.add(SmtNames.legalSymbols(assertion) + "\n");
            }
            return legal;
        }

        /**
         * The body's top-level commands: where each ends (the first one's
         * text starts at 0, each next at the previous end), and the selector
         * among these that guards it, {@code (assert (=> selector ...))}
         * named or not, else null.  Bar-quoted symbols, string literals and
         * comments are skipped whole, so a parenthesis inside one is none.
         */
        private static void commands(String body, Set<String> selectors,
                                     List<Integer> ends, List<String> guards) {
            int start = 0;
            int depth = 0;
            int index = 0;
            while (index < body.length()) {
                char at = body.charAt(index);
                if (at == '|') {
                    int close = body.indexOf('|', index + 1);
                    index = close < 0 ? body.length() : close + 1;
                    continue;
                }
                if (at == '"') {
                    int close = index + 1;
                    while (close < body.length()) {
                        if (body.charAt(close) == '"') {
                            // "" is an escaped quote inside the literal.
                            if (close + 1 < body.length()
                                    && body.charAt(close + 1) == '"') {
                                close += 2;
                                continue;
                            }
                            break;
                        }
                        close++;
                    }
                    index = close + 1;
                    continue;
                }
                if (at == ';') {
                    int close = body.indexOf('\n', index);
                    index = close < 0 ? body.length() : close;
                    continue;
                }
                if (at == '(') depth++;
                if (at == ')' && --depth == 0) {
                    int from = start;
                    while (Character.isWhitespace(body.charAt(from))) from++;
                    ends.add(index + 1);
                    guards.add(guard(body.substring(from,
                            Math.min(index + 1, from + GUARD_PREFIX)),
                            selectors));
                    start = index + 1;
                }
                index++;
            }
            if (start < body.length()) {
                ends.add(body.length());
                guards.add(null);
            }
        }

        /** How much of a command's head names its guard: the assert and
         *  implication heads and a selector, whose names are short. */
        private static final int GUARD_PREFIX = 256;

        /** The selector this command's head is guarded by, or null. */
        private static String guard(String command, Set<String> selectors) {
            String rest = command.startsWith("(assert (! (=> ")
                    ? command.substring("(assert (! (=> ".length())
                    : command.startsWith("(assert (=> ")
                    ? command.substring("(assert (=> ".length()) : null;
            if (rest == null) return null;
            int end = rest.indexOf(' ');
            String token = end < 0 ? rest : rest.substring(0, end);
            return selectors.contains(token) ? token : null;
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

        /** Every clock cell the formula declares, in the recording's seq
         *  order, each with a reading ({@link #clockReadings}). */
        public List<String> clockCells() {
            return clockCells;
        }

        /** Clock cell -> its instant on the recording's timeline: the
         *  seed's reading, or where a session that read it places it
         *  ({@code Composer#clocks}). */
        public Map<String, Long> clockReadings() {
            return clockReadings;
        }

        /** Clock cell -> its clock's tick in nanoseconds
         *  ({@code RootMintRow#clockNanos}). */
        public Map<String, Long> clockNanos() {
            return clockNanos;
        }

        /** Clock cell -> the cell before it on its node's clock, where its
         *  order names one ({@code clock_order__}). */
        public Map<String, String> clockBefore() {
            return clockBefore;
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
        /**
         * The path's own run: the arm its own session is of each message the
         * path received, and the writer arm each state read observed --
         * selectors, never the values the run's handoffs carried, which are
         * on its own clock ({@code SmtLowering#clockBases}).
         */
        public List<String> ownRun(String selector) {
            List<String> own = new ArrayList<String>();
            Disjunct disjunct = bySelector(selector);
            if (disjunct == null) return own;
            List<String> arms = ownArms.get(selector);
            if (arms != null) own.addAll(arms);
            List<String> reads = observedReads.get(disjunct.path().pathId);
            if (reads != null) own.addAll(reads);
            return asserted(own);
        }

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

        /**
         * Every nested selector a state arm's stores are chosen among
         * ({@link ComposedFamilies.ArmChoice#states}), so a claim can say
         * which state of the delivered object the witness's queries saw.
         */
        public List<String> stateSelectors() {
            Set<String> selectors = new LinkedHashSet<String>();
            for (ComposedFamilies.ArmChoice arm : armChoices.values()) {
                for (SmtLowering.StateChoice state : arm.states()) {
                    selectors.add(state.selector);
                }
            }
            return new ArrayList<String>(selectors);
        }

        /**
         * Every codec hole's symbol an arm binds
         * ({@link ComposedFamilies.ArmChoice#holes}), so a claim can state
         * the model's valuation of each for CONFIRM.
         */
        public List<String> holeSymbols() {
            Set<String> symbols = new LinkedHashSet<String>();
            for (ComposedFamilies.ArmChoice arm : armChoices.values()) {
                for (ComposedFamilies.BoundHole hole : arm.holes().values()) {
                    symbols.add(hole.symbol);
                }
            }
            return new ArrayList<String>(symbols);
        }

        /**
         * The causal cone of one path's fatal, as acceptance reads it off
         * the formula ({@code experiments/accept/cone.py}): every name its
         * {@code path_fatal__} names, closed over the message families
         * asserted under its selector that name one of them.
         */
        public Set<String> cone(String selector) {
            Set<String> cone = new LinkedHashSet<String>();
            List<Set<String>> families = new ArrayList<Set<String>>();
            int start = 0;
            for (int index = 0; index < commandEnds.length; index++) {
                int end = commandEnds[index];
                if (selector.equals(commandGuards[index])) {
                    String command = body.substring(start, end);
                    if (command.contains(":named path_fatal__")) {
                        SmtNames.symbols(command, cone);
                    } else if (command.contains(":named message_family__")) {
                        families.add(SmtNames.symbols(command,
                                new LinkedHashSet<String>()));
                    }
                }
                start = end;
            }
            boolean grew = true;
            while (grew) {
                grew = false;
                for (Set<String> family : families) {
                    if (!Collections.disjoint(family, cone)
                            && !cone.containsAll(family)) {
                        cone.addAll(family);
                        grew = true;
                    }
                }
            }
            return cone;
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
    /** The epoch's static facts: where a reference write's construction
     *  guard is ({@link #constructionGuards}). */
    private final StaticScopeMap scope;
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
     * a root inside it (IDENTITY §4).
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
    /** This epoch's skeleton: which interactions have a slot (PIPELINE
     *  §7.1). */
    private SlotTable slots;
    /** Sessions whose pairing replaces a slot's: their arms are not ours. */
    private final Set<String> replacing = new LinkedHashSet<String>();
    /** What refused the first path that reached the anchor, or "". */
    private String firstRefusal = "";
    /** How the alternatives of one slot read in SMT. */
    private final ComposedFamilies composedFamilies;

    private Composer(Corpus corpus, OccurrenceAddress anchor,
                     Map<String, RootDomain> declaredDomains,
                     int maxValuations, StaticScopeMap scope) {
        this.corpus = corpus;
        this.anchor = anchor;
        this.scope = scope;
        this.declaredDomains = declaredDomains == null
                ? Collections.<String, RootDomain>emptyMap()
                : declaredDomains;
        this.maxValuations = maxValuations <= 0 ? 64 : maxValuations;
        this.lowering = new SmtLowering(corpus.declaredSymbols());
        lowering.clockBases(clockBases());
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
                                      int maxValuations,
                                      StaticScopeMap scope) {
        return new Composer(corpus, anchor, declaredDomains, maxValuations,
                scope).run();
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
                        disjunct.selector(), disjunct.fatalObserved(),
                        disjunct.restsOn()));
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
        Map<String, String> clockBefore = new LinkedHashMap<String, String>();
        clocks(clockCells, clockReadings, clockNanos, clockBefore);
        domains();
        refutations(disjuncts);
        lowering.assertIdentitiesDistinct();
        // A manifest that predates readings (schema 1) states none: a root
        // such a session read and minted none guards none of its arms.
        for (SessionReader session : corpus.sessions()) {
            if (session.manifest() == null
                    || session.manifest().statesReadings()) {
                continue;
            }
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    session.sessionId(), "this session's manifest predates "
                            + "concrete readings and derived roots (schema "
                            + "1), so a root it read and minted none guards "
                            + "none of its arms and pins none of its path");
        }
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
                : lowering.pinnedReturns().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    "MethodReturnPinned:" + pinned.getKey(), "the call that "
                            + "returned this symbol is no relation the "
                            + "lowering knows and nothing its arguments rest "
                            + "on moves: it is pinned to " + pinned.getValue()
                            + " by a named assertion, and what it was "
                            + "computed from is not in the formula");
        }
        for (Map.Entry<String, String> named
                : lowering.diagnostics().entrySet()) {
            gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    named.getKey(), named.getValue());
        }

        // Valuations before the body: the body declares what pins reach.
        List<Valuation> valuations = valuations();
        List<String> pins = new ArrayList<String>();
        for (Valuation valuation : valuations) {
            pins.addAll(valuation.assertions());
        }
        return new Composition(this, lowering.body(pins), disjuncts, entries,
                valuations, clockCells, clockReadings, clockNanos,
                clockBefore);
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
        lowering.path();
        // (0a) THE CLOSURE (P3): the occurrences of this session the joins
        //      reach, and the seq each prefix runs to.  Row-level, before
        //      any lowering.
        Map<String, Long> reached = closure(session, anchor, target.seq(),
                null);
        // What a family may move at the anchor is no constant anywhere in
        // this path: not a pin after a refused join, not a variable
        // independence leaves out.  A location a reader mutated a container
        // through is held to the run's pairing.
        Set<String> repaired = repaired(session);
        Set<String> pinned = pinnedOwners(session, reached, repaired);
        repaired.removeAll(pinned);
        SmtLowering.SessionJoin rows = SmtLowering.repairing(
                corpus.join(session), repaired,
                (reader, writer) -> arms.concurrent(reader, writer, session));
        lowering.begin(session, rows, corpus.expressions(session));

        List<String> terms = new ArrayList<String>();
        List<GapRow> refusals = new ArrayList<GapRow>();
        List<ReadRow> joined = new ArrayList<ReadRow>();
        List<String> observed = new ArrayList<String>();
        Map<String, String> joins = new LinkedHashMap<String, String>();
        frameRefusals(session, reached.keySet(), refusals);

        // (0a') What phi rests on (constraint independence): conditions and
        //       reads sharing no variable with phi or a root stay out.
        List<DecisionRow> conditions = before(path.decisions, target.seq());
        conditions.addAll(reachedConditions(session, reached));
        Independence relevant = independence(session,
                Collections.singletonList(target.phiTerm()),
                familyBound(session, repaired), reached, conditions);
        //       What the fatal itself rests on ({@link #fatalRests}) and
        //       the roots alone: a location a family binds and nothing else
        //       reaches holds the formula's alternatives, not the witness (a
        //       confirming run is held to these only).
        Set<String> restsOn = independence(session,
                fatalRests(target, path.decisions),
                Collections.<String>emptySet(), reached, conditions)
                .locations();

        // (0b) Reads whose value the row states outright, bound BEFORE any
        //      lowering so every leaf naming them resolves, not just later
        //      ones.
        Set<String> answered = new LinkedHashSet<String>();
        statedReads(session, reached.keySet(), relevant, rows, refusals,
                joins, answered);

        // (1) The valuation this replay ran under, for every VARIED root
        //     (a root may be written and never branched on) and every root
        //     it read and minted none.  Declared roots this session neither
        //     minted nor read are answered in (1b), once the path's terms are
        //     whole.
        Map<String, Set<String>> unminted =
                new LinkedHashMap<String, Set<String>>();
        terms.addAll(valuationOf(session, refusals, unminted));

        // (2) Each anchor handoff, answered or not: nothing here (its family
        //     binds it; collected in `bound`).  Never a literal.
        Set<String> interactionIds = new LinkedHashSet<String>();
        Set<String> handoffs = new LinkedHashSet<String>();
        List<AttachRow> bound = new ArrayList<AttachRow>();
        handoffReads(session, interactionIds, handoffs, refusals, bound);

        // (3) State joins, read := observed write's expression, kept by
        //     symbol: a read with family alternatives must not also be
        //     asserted here.
        stateJoins(session, reached.keySet(), relevant, rows, refusals,
                joined, joins, answered);
        joined.removeIf(read -> pinned.contains(
                SmtLowering.locationKey(read.location())));
        //     A field projected, or a container queried, through one a STATE
        //     family may re-point is the object's it is
        //     ({@link SmtLowering#movable}); through any other, the run's.
        for (ReadRow read : joined) {
            if (repaired.contains(SmtLowering.locationKey(read.location()))) {
                lowering.movable(read.symbol());
            }
        }

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
        //     polarity.  A concrete fatal condition is the constant of its
        //     arm (invariant 9): `true` rests the fatal on pi_p, the path
        //     condition that reached the anchor; `false` is no path to the
        //     fatal arm in any world of this one; none stated is no phi.
        String subject = "phi of " + anchor.render();
        String published = target.phiTerm().trim();
        int fatalArm = -1;
        if (published.isEmpty() || "false".equals(published)) {
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, subject, published.isEmpty()
                            ? "the target row states no phi (invariant 9), "
                            + "so what the fatal rests on is stated by no "
                            + "row"
                            : "the anchor decided concretely on its healthy "
                            + "arm, so no world of this path reaches the "
                            + "fatal one"));
        } else {
            String phi = lowering.statedTerm(published, "phi:" + subject);
            if (!phi.isEmpty() && !unknown(phi, refusals, subject)) {
                fatalArm = terms.size();
                terms.add(phi);
            }
        }

        // (5b) Every OTHER handoff the conjunction reaches (via joins, pi,
        //      phi), by the same rule as (2).
        List<String> reaching = new ArrayList<String>(terms);
        reaching.addAll(joins.values());
        reachedHandoffs(session, reaching, interactionIds, handoffs,
                refusals, bound);

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
        //     single session could make all deliveries the path took (PIPELINE
        //     §8), the path is dropped, and what its families stated is taken
        //     back with it.
        List<String> familyTerms = new ArrayList<String>();
        List<GapRow> unproducible = new ArrayList<GapRow>();
        if (!composedFamilies.closeFamilies(ordinal, selector, session,
                interactionIds, bound, familyTerms, unproducible)) {
            composedFamilies.discard();
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

        // Nothing refuses the path from here: it is a disjunct.
        composedFamilies.commit();
        String fatal = "path_fatal__" + ordinal;
        lowering.assertNamed(fatal,
                "(=> " + selector + " " + VmTermLowering.and(terms) + ")");
        List<String> withoutFatalArm = new ArrayList<String>(terms);
        if (fatalArm >= 0) withoutFatalArm.remove(fatalArm);
        observedReads.put(path.pathId, observed);
        observedArrivals.put(path.pathId,
                arrivals(corpus.attachesOn(session, anchor)));
        heldArrivals.put(path.pathId, arrivals(bound));
        return new Disjunct(path, selector, fatal, "(=> " + selector + " "
                + VmTermLowering.and(withoutFatalArm) + ")",
                target.observedFatal(), interactionIds, restsOn);
    }

    /**
     * What the fatal a target row states rests on: its phi; a concrete
     * fatal condition states phi as the constant of its arm, which names
     * nothing, and that fatal rests on the path condition that reached the
     * anchor, the decisions before the target (CONTRACT-SPEC §2.2).
     */
    private static List<String> fatalRests(TargetRow target,
                                           List<DecisionRow> decisions) {
        String phi = target.phiTerm().trim();
        return "true".equals(phi) || "false".equals(phi)
                ? Arms.pathCondition(decisions, target.seq())
                : Collections.singletonList(target.phiTerm());
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
     * the query, which can cost z3 its whole budget; it goes with what its
     * lowering required ({@link SmtLowering#ownConditions}).  Same rule as
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
     * PLANTED it; a flip mint states no recorded value) -- and every root it
     * read and minted none, at its reading ({@link Corpus#ranRoot}), by the
     * rule its arms are guarded by ({@code Arms#arm}).
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
            RootMintRow concrete = row == null
                    ? corpus.ranRoot(entry.getKey(), session) : null;
            if (concrete != null) {
                // Read where none was minted: its terms are literals that
                // may be computed from the reading, so the path holds at it
                // alone -- pinned, varied or not, never a window.
                String literal = smtLiteral(corpus.rootValue(session,
                        concrete.rootId()), sortOf(concrete));
                if (literal.isEmpty()) continue;
                lowering.declareStated(concrete.symbol(), sortOf(concrete));
                valuation.add("(= " + concrete.symbol() + " " + literal
                        + ")");
                continue;
            }
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
            lowering.declareStated(row.symbol(), sortOf(row));
            // A declared domain is a window around THIS replay's reading;
            // pinning the exact value would answer the question in advance.
            String window = windowOf(row);
            if (!window.isEmpty()) {
                valuation.add(window);
                continue;
            }
            String literal = smtLiteral(ran, sortOf(row));
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
     * Each of the anchor's handoffs, by {@link #handoffRead}: bound by its
     * FAMILY alone, or the path is refused by name.
     */
    private void handoffReads(String session, Set<String> interactionIds,
                              Set<String> handoffs, List<GapRow> refusals,
                              List<AttachRow> bound) {
        for (AttachRow attach : corpus.attachesOn(session, anchor)) {
            handoffRead(session, attach, interactionIds, handoffs, refusals,
                    bound);
        }
    }

    /**
     * Every OTHER handoff this path's conjunction reaches (e.g. a delivered
     * value a joined write put into a container), by the same rule.
     * Unbound, each would be a free constant: a handoff variable this
     * session minted no attach for (the corpus states it of another run)
     * has no family here, and refuses the path by name.
     */
    private void reachedHandoffs(String session, List<String> terms,
                                 Set<String> interactionIds,
                                 Set<String> handoffs, List<GapRow> refusals,
                                 List<AttachRow> bound) {
        for (String name : lowering.reachedSymbols(terms)) {
            if (handoffs.contains(name)) continue;
            AttachRow attach = corpus.attach(session, name);
            if (attach != null) {
                handoffRead(session, attach, interactionIds, handoffs,
                        refusals, bound);
            } else if (corpus.handoffSymbol(name) && handoffs.add(name)) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, name, "this path names a "
                                + "handoff variable no attach row of its "
                                + "session minted, so no family of this "
                                + "run binds what it read"));
            }
        }
    }

    /**
     * One attach, stated once per symbol ({@code handoffs} holds the
     * symbols already bound): an ATTESTED producer delivered it, and its
     * FAMILY alone binds it (PIPELINE §8); nothing is conjoined here, and
     * it takes just its sort from the delivery ({@link #attestedArrival}).
     * Answered or not: an obligation's answer is what its replay planted at
     * the consumer, and a witness rests only on a value a run compatible
     * with its path delivered (hdfs-17967-pathC rb1: a flip answered the
     * DataNode's key id with 119532 while the moved serial had its producer
     * deliver 119533, and the answer, pinned as a literal, let the solver
     * move the serial past it).  Otherwise refused by name.
     */
    private void handoffRead(String session, AttachRow attach,
                             Set<String> interactionIds,
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
        if (attestedArrival(attach)) {
            bound.add(attach);
            return;
        }
        // Never pin the literal it took: the question is whether the
        // producer could have delivered another value.  Refuse by name.
        refusals.add(GapRow.of(session, GapKind.UNATTESTED_ARM,
                GapClass.DIAGNOSTIC, attach.symbol(),
                "no session of this corpus states the rows of the producer "
                        + "occurrence this delivery came from, so what was "
                        + "delivered is stated and why is not: this path "
                        + "would have to pin the read to the literal it "
                        + (attach.answered() ? "was answered with"
                        : "received")));
    }

    /** The sort a root's symbol has: a MARKER is a flag, any other a number. */
    static Sort sortOf(RootMintRow row) {
        return row.kind() == RootKind.MARKER ? Sort.BOOL : Sort.INT;
    }

    /**
     * Whether an ATTESTED arm delivers this arrival; if so, declares the
     * symbol at the arm's sort -- a codec hole's at its decoded leaf's
     * (WIRE-CODEC §6.1), which the arm is widened or read back to
     * ({@link VmTermLowering#holeArm}). States NOTHING about the value: the
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
                    export.expressionRef(), "paired-arm", null);
            if (delivered == null) continue;
            lowering.declareStated(attach.symbol(), attach.hole() == null
                    ? delivered.sort
                    : JavaSmtSorts.sortOfJava(attach.javaType()));
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
     * <p>P3 (PIPELINE §8): EARLIER VERSIONS of a reached write's location
     * are reached too, since a state is the result of every earlier mutation (e.g. what
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
     * A REFUSAL IS ITS FRAME'S: a value the run refused inside an occurrence
     * ({@link Corpus#refusedIn}) refuses a path or an arm whose closure
     * reaches that occurrence, and nothing else.  A refused attach used to
     * be BLOCKING for the whole campaign, wherever it ran (hdfs-17899-bug1
     * r1: 55 of them, all in NameNode registration handlers).
     */
    void frameRefusals(String session, Set<String> reached,
                       List<GapRow> refusals) {
        for (String occurrenceId : reached) {
            GapRow refused = corpus.refusedIn(session, occurrenceId);
            if (refused == null) continue;
            refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, refused.subject(), "this closure "
                            + "reaches an occurrence whose own run refused a "
                            + "value it computes on: " + refused.detail()));
        }
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

    /** What {@code seeds} and the variables a family binds ({@code
     *  bound}) rest on among these conditions and the reads of the reached
     *  occurrences ({@link Independence}); a read brings the construction
     *  guard of the write it observed. */
    Independence independence(String session, List<String> seeds,
                              Collection<String> bound,
                              Map<String, Long> reached,
                              List<DecisionRow> conditions) {
        return Independence.of(corpus, session, seeds, bound, conditions,
                statedRows(session, reached.keySet()),
                read -> constructionGuards(session, corpus.writeOf(session,
                        read.location(), read.observedVersion())));
    }

    /** The construction guards already found, by session and write. */
    private final Map<String, List<DecisionRow>> built =
            new LinkedHashMap<String, List<DecisionRow>>();

    /**
     * THE CONSTRUCTION GUARD of a reference write (R3-REFCONT §1.6, D5):
     * the decisions its occurrence took before it at the guard sites of the
     * mutations its method made on a container it then published
     * ({@link StaticScopeMap#constructionGuards}).  A referent rests on
     * every decision that shaped it, the ones that skipped a mutation
     * included, and those leave no node in its state: an arm delivering the
     * write, or a read joined to it, conjoins them in the polarity they took
     * ({@link Independence} keeps them), and the reads they name are joined
     * in turn.  A decision whose condition guards a conditional mutation of
     * the referent's chain (REMOVE_IF, PUT_IF, APPEND_IF) stays free, as
     * that node states it both ways.  None for a write that stored no
     * container's state.
     */
    List<DecisionRow> constructionGuards(String session, WriteRow write) {
        if (write == null || write.referentState() == null) {
            return Collections.<DecisionRow>emptyList();
        }
        return built.computeIfAbsent(session + "|" + write.location() + "@"
                + write.version(), unused -> {
            String site = write.endpoint().site();
            Set<String> sites = new LinkedHashSet<String>();
            for (String carrier : scope.carriersAt(site,
                    write.javaType(), write.location().kind())) {
                for (StaticScopeMap.Guard guard
                        : scope.constructionGuards(site, carrier)) {
                    sites.add(guard.siteId());
                }
            }
            List<DecisionRow> guards = new ArrayList<DecisionRow>();
            if (sites.isEmpty()) return guards;
            Set<JsonElement> free = mutationGuards(session,
                    write.referentState());
            for (DecisionRow decision : corpus.decisionsOf(session,
                    write.endpoint().occurrence())) {
                if (decision.seq() < write.seq()
                        && sites.contains(decision.siteId())
                        && !decides(session, decision, free)) {
                    guards.add(decision);
                }
            }
            return guards;
        });
    }

    /**
     * The guards of the conditional mutations of one container's chain
     * ({@link ContainerSmtCodec#conditionalMutation}), down to its base:
     * each version's mutation and, through the read it rests on, the
     * version before.
     */
    private Set<JsonElement> mutationGuards(String session,
                                            WriteRow.Referent state) {
        Set<JsonElement> guards = ExpressionWalk.identitySet();
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        List<JsonElement> pending = new ArrayList<JsonElement>();
        WriteRow first = corpus.writeOf(session, state.location(),
                state.version());
        if (first != null) {
            pending.add(corpus.expression(session, first.expressionRef()));
        }
        while (!pending.isEmpty()) {
            for (ExpressionWalk walk = ExpressionWalk.of(pending.remove(
                    pending.size() - 1), walked); walk.hasNext(); ) {
                JsonObject node = walk.next();
                String type = JsonFields.optionalString(node, "_type");
                if ("ContainerRelation".equals(type)
                        && ContainerSmtCodec.conditionalMutation(
                        JsonFields.optionalString(node, "operation"))) {
                    guards.add(unwrapped(node.get("guard")));
                } else if (VmRows.GUARDED_READ_TYPE.equals(type)) {
                    WriteRow below = corpus.writeOf(session,
                            SmtLowering.locationKey(JsonFields.object(node,
                                    "location")), VmRows.recordedVersion(
                                    node));
                    if (below != null) {
                        pending.add(corpus.expression(session,
                                below.expressionRef()));
                    }
                }
            }
        }
        return guards;
    }

    /**
     * Whether a decision's condition is one of these guards: the node
     * itself, or its complement over the same operands (the arm a removal
     * that did not fire states).
     */
    private boolean decides(String session, DecisionRow decision,
                            Set<JsonElement> guards) {
        if (guards.isEmpty()) return false;
        for (String reference : SmtNames.symbols(decision.term(),
                new LinkedHashSet<String>())) {
            JsonElement condition = unwrapped(corpus.expression(session,
                    reference));
            if (guards.contains(condition)) return true;
            for (JsonElement guard : guards) {
                if (condition != null && condition.isJsonObject()
                        && guard != null && guard.isJsonObject()
                        && condition.getAsJsonObject().get("_left")
                        == guard.getAsJsonObject().get("_left")
                        && condition.getAsJsonObject().get("_right")
                        == guard.getAsJsonObject().get("_right")) {
                    return true;
                }
            }
        }
        return false;
    }

    /** A value beneath the consumer boundaries around it. */
    private static JsonElement unwrapped(JsonElement value) {
        JsonElement found = value;
        while (VmExpressionIr.consumerBoundary(found)) {
            found = found.getAsJsonObject().get(VmExpressionIr.EXPRESSION);
        }
        return found;
    }

    /**
     * The anchor locations a family may re-pair that keep the run's own
     * pairing, named.  A reader of this path mutated a container through
     * one (R3-REFCONT C-4): a reached occurrence's container version whose
     * mutation names, as its owner, a read of it; another pairing would
     * mutate an object no row records the mutation of.  Or a store of one
     * holds a container through an object that is not it (a
     * {@code Collections} wrapper, a view): a query through that object
     * names no owner, so it is the run's container's answer whichever
     * object the family delivers.  Or a field or a query is asked through a
     * container query's read of it: that read names no object (a query
     * states no answer's identity), so no case per writer is the run's.
     */
    private Set<String> pinnedOwners(String session,
                                     Map<String, Long> reached,
                                     Set<String> repaired) {
        Set<String> pinned = new LinkedHashSet<String>();
        for (String key : containerOwners(session, reached)) {
            if (repaired.contains(key) && pinned.add(key)) {
                gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        "OWNER_PINNED_BY_CONTAINER_READ:" + key + "@"
                                + session, "a field or a query of this path "
                                + "is asked through a query's read of this "
                                + "container, which names no object, so its "
                                + "family is held to the arm the run took");
            }
        }
        for (Map.Entry<String, Long> at : reached.entrySet()) {
            OccurrenceAddress occurrence = corpus.occurrence(at.getKey());
            if (occurrence == null) continue;
            for (WriteRow write : corpus.writesOn(session, occurrence)) {
                if (write.seq() > at.getValue()
                        || write.location().kind() != LocationKind.MAP) {
                    continue;
                }
                JsonObject mutation = corpus.expression(session,
                        write.expressionRef());
                JsonElement owner = unwrapped(mutation == null ? null
                        : mutation.get("owner"));
                if (!VmRows.GUARDED_READ_TYPE.equals(
                        VmExpressionIr.typeOf(owner))) {
                    continue;
                }
                String key = SmtLowering.locationKey(JsonFields.object(
                        owner.getAsJsonObject(), "location"));
                if (repaired.contains(key) && pinned.add(key)) {
                    gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            "OWNER_PINNED_BY_MUTATION:" + key + "@"
                                    + session, "a reader of this path "
                                    + "mutated a container through this "
                                    + "reference, so its family is held to "
                                    + "the arm the run took: another pairing "
                                    + "would mutate an object no row "
                                    + "records the mutation of");
                }
            }
        }
        for (String key : repaired) {
            for (WriteRow store : corpus.writesOf(session, key)) {
                if (store.referentState() == null
                        && store.referentStateRefused() == null
                        || storesItsContainer(session, store)) {
                    continue;
                }
                if (pinned.add(key)) {
                    gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            "OWNER_PINNED_BY_WRAPPER:" + key + "@" + session,
                            "the store at version " + store.version()
                                    + " holds a container through an object"
                                    + " that is not it, and a query through"
                                    + " such an object names no owner, so "
                                    + "this family is held to the arm the "
                                    + "run took");
                }
                break;
            }
        }
        return pinned;
    }

    /**
     * The container locations whose query reads the anchor or a reached
     * occurrence asks a field or a query through ({@code owner}), up to its
     * cutoff.
     */
    private Set<String> containerOwners(String session,
                                        Map<String, Long> reached) {
        Set<String> owners = new LinkedHashSet<String>();
        Set<JsonElement> walked = ExpressionWalk.identitySet();
        Map<String, Long> asked = new LinkedHashMap<String, Long>(reached);
        TargetRow anchored = corpus.target(session, anchor);
        if (anchored != null) {
            asked.merge(anchor.id(), anchored.seq(), Math::max);
        }
        for (Map.Entry<String, Long> at : asked.entrySet()) {
            OccurrenceAddress occurrence = corpus.occurrence(at.getKey());
            if (occurrence == null) continue;
            StringBuilder terms = new StringBuilder();
            for (DecisionRow decision : corpus.decisionsOf(session,
                    occurrence)) {
                if (decision.seq() <= at.getValue()) {
                    terms.append(decision.term()).append(' ');
                }
            }
            for (WriteRow write : corpus.writesOn(session, occurrence)) {
                if (write.seq() <= at.getValue()) {
                    terms.append(write.expressionRef()).append(' ');
                }
            }
            TargetRow target = corpus.target(session, occurrence);
            if (target != null) terms.append(target.phiTerm());
            Matcher refs = EXPRESSION_REF.matcher(terms);
            while (refs.find()) {
                for (ExpressionWalk walk = ExpressionWalk.of(corpus.expression(
                        session, refs.group()), walked); walk.hasNext(); ) {
                    JsonElement owner = unwrapped(walk.next().get("owner"));
                    if (!VmRows.GUARDED_READ_TYPE.equals(
                            VmExpressionIr.typeOf(owner))) {
                        continue;
                    }
                    String key = SmtLowering.locationKey(JsonFields.object(
                            owner.getAsJsonObject(), "location"));
                    if (key.startsWith(LocationKind.MAP + "/")) {
                        owners.add(key);
                    }
                }
            }
        }
        return owners;
    }

    private static final Pattern EXPRESSION_REF =
            Pattern.compile("EXPR\\.[0-9a-f]+");

    /**
     * Whether a reference store stored a container itself, which a wrapper
     * or a view of one is not: the container its referent names, or,
     * refused, an object this session logs the state of.
     */
    private boolean storesItsContainer(String session, WriteRow store) {
        JsonElement stored = unwrapped(corpus.expression(session,
                store.expressionRef()));
        if (!SmtLowering.named(stored)) return false;
        String rid = Long.toString(VmRows.referencedObjectRid(
                stored.getAsJsonObject().get("_exp").getAsString()));
        return store.referentState() != null
                ? rid.equals(store.referentState().location().owner())
                : !corpus.writesOf(session, SmtLowering.locationKey(
                LocationId.of(LocationKind.MAP, rid, "-3"))).isEmpty();
    }

    /**
     * The variables a family of this path may bind: every attach of the
     * anchor (its MESSAGE family, {@link #handoffReads}), and the reads of
     * the locations a STATE family may re-pair.  Independence seeded with
     * phi and the roots alone left out a condition over them, and the
     * family set them free of it (C1 review M2).
     */
    private Set<String> familyBound(String session, Set<String> repaired) {
        Set<String> bound = new LinkedHashSet<String>();
        for (AttachRow attach : corpus.attachesOn(session, anchor)) {
            bound.add(attach.symbol());
        }
        for (ReadRow read : corpus.readsOn(session, anchor)) {
            String key = SmtLowering.locationKey(read.location());
            if (!repaired.contains(key)) continue;
            bound.add(Independence.location(key));
            if (!read.symbol().isEmpty()) bound.add(read.symbol());
        }
        return bound;
    }

    /**
     * The locations a STATE family may re-pair at the anchor ({@link
     * ComposedFamilies#stateFamilies}): read there by this session, owned
     * by a named object, by a read that could have seen a writer
     * occurrence besides the one it did ({@link Corpus#eligibleWrites}, the
     * writers the family's arms are drawn from: only an HB-concurrent one
     * is another).  A version no row wrote has no writer of its own, so
     * any eligible writer is another; but a read whose only eligible writer
     * is the one it observed, or none, has no alternative: two reads that
     * saw two ordered writers, or a hot field whose earliest versions the
     * VM's version bound dropped and whose only writer is the reader's own
     * occurrence (hdfs-17960 e1c: a configuration parser's fields in the
     * checkpoint saver), stay the run's.
     */
    private Set<String> repaired(String session) {
        Set<String> repaired = new LinkedHashSet<String>();
        Set<String> asked = new LinkedHashSet<String>();
        for (ReadRow read : corpus.readsOn(session, anchor)) {
            long version = read.observedVersion();
            if (version < 0L || !Arms.namedOwner(read.location())) continue;
            String key = SmtLowering.locationKey(read.location());
            if (repaired.contains(key) || !asked.add(key + "#" + version)) {
                continue;
            }
            WriteRow observed = corpus.writeOf(session, key, version);
            String seen = observed == null ? null
                    : observed.endpoint().occurrence().id();
            for (WriteRow write : corpus.eligibleWrites(session, key,
                    version, anchor)) {
                if (!write.endpoint().occurrence().id().equals(seen)) {
                    repaired.add(key);
                    break;
                }
            }
        }
        return repaired;
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
     * Read := THE ONE BINDING RULE ({@link SmtLowering#bind}, the guarded
     * read's too, so the two cannot disagree): JOIN, the expression of the
     * write version it observed, if it lowers with no refusal; else its
     * MINT; else PIN; else REFUSE.  A join that refused gives way to the
     * mint or the pin only where nothing it rests on can move.  No "latest
     * write", no choice between writers.
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
            long version = read.observedVersion();
            WriteRow write = corpus.writeOf(session, key, version);
            if (joins.containsKey(read.symbol())) {
                // Pinned at step 0 to what its row states: a version no row
                // wrote, its writer outside every region.  At the anchor a
                // STATE family may still offer the concurrent writers beside
                // what it returned; a mint's version is a root's.
                if (atAnchor && write == null && version >= 0L
                        && "".equals(SmtLowering.mintedReadSymbol(join,
                        version))) {
                    joined.add(read);
                }
                continue;
            }
            // A cited ref missing from its own table: BLOCKING.
            if (write != null && corpus.expression(session,
                    write.expressionRef()) == null) {
                refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, write.expressionRef(),
                        "a write row of " + key + "@" + version + " cites an "
                                + "expression its session's table does not "
                                + "hold, so the chain this read joins to is "
                                + "not in this corpus"));
                continue;
            }
            SmtLowering.Binder<Boolean> binder = new SmtLowering.Binder<Boolean>() {
                @Override
                public Term join(JsonElement value) {
                    return lowering.dispatch(value, SmtLowering.whole(value,
                            null), "state-join:" + key + "@" + version);
                }

                @Override
                public Boolean joined(Term value) {
                    lowering.declareStated(read.symbol(), value.sort);
                    // What the JVM evaluated it under holds where it does.
                    String equals = "(= " + read.symbol() + " " + value.text
                            + ")";
                    joins.put(read.symbol(), "true".equals(value.precondition)
                            ? equals : "(and " + equals + " "
                            + value.precondition + ")");
                    if (atAnchor) joined.add(read);
                    return true;
                }

                @Override
                public Boolean minted(String symbol) {
                    return mint(session, read, symbol, refusals, joins);
                }

                @Override
                public Boolean pinned() {
                    // The row's own value (non-joinable rows were asked at
                    // step 0, and one it could not place is refused there).
                    if (!answered.contains(read.symbol())
                            && !pin(session, read, refusals, joins,
                            answered)) {
                        return null;
                    }
                    return joins.containsKey(read.symbol());
                }

                @Override
                public Boolean refused(Term value, String subject,
                                       String detail) {
                    refusals.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                            GapClass.DIAGNOSTIC, key + "@" + version,
                            detail));
                    return false;
                }
            };
            // What binding the read required rides with the join that binds
            // it: stated where the conjunction asks about it (#statedJoins).
            List<String> own = lowering.ownConditions(
                    () -> lowering.bind(key, version, null, binder)
                            && joins.containsKey(read.symbol()));
            if (!own.isEmpty()) {
                own.add(0, joins.get(read.symbol()));
                joins.put(read.symbol(), VmTermLowering.and(own));
            }
        }
    }

    /**
     * MINT: the read is the symbol the placeholder of its version stated,
     * keyed by {@code mintVersion} alone (CONTRACT v2.4); a root's version
     * moves with the root.  Answers whether it binds the read.
     */
    private boolean mint(String session, ReadRow read, String minted,
                         List<GapRow> refusals, Map<String, String> joins) {
        // This row states the version; bound at step 0.
        if (minted.equals(read.symbol())) return true;
        Sort sort = lowering.declaredSort(minted);
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
                    "the read row that states this version's symbol states "
                            + "no value for it, and no root of this session "
                            + "mints it, so nothing binds it"));
            return false;
        }
        if (root != null && !lowering.stated(minted)) {
            // So the root's domain lands on the joined symbol.
            lowering.declareStated(minted, sort);
        }
        lowering.declareStated(read.symbol(), sort);
        joins.put(read.symbol(), "(= " + read.symbol() + " " + minted + ")");
        return true;
    }

    /**
     * What this session received at these attaches, one term per symbol.
     * Kept beside the path, not in it: an arrival is a consequence of its
     * producer's roots, so pinning it would pin them.
     */
    private List<String> arrivals(List<AttachRow> attaches) {
        List<String> stated = new ArrayList<String>();
        Set<String> seen = new LinkedHashSet<String>();
        for (AttachRow attach : attaches) {
            if (!seen.add(attach.symbol())) continue;
            String literal = smtLiteral(JsonFields.firstNonBlank(
                    attach.answeredValue(), attach.arrival()),
                    JavaSmtSorts.sortOfJava(attach.javaType()));
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
            String literal = smtLiteral(row.recordedValue(), sortOf(row));
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
     * Every declared CLOCK cell the formula names: its domain, its reading
     * on the recording's timeline, and its place in its node's order.
     *
     * <p>A cell is one per (root, occurrence), and its reading is the
     * SEED's.  A cell the seed never read (a region woven after it) is
     * placed by a session that read it: at the seed's reading of the
     * nearest cell (by seq) of the same clock that session also read, plus
     * the time that session's host read between the two
     * ({@link #placed}).  A cell no session can place has no instant any
     * claim could judge it moved from: BLOCKING.  Domain ({@link
     * JavaPrimitiveSmtSemantics#clockDomain}): floor = the reading, ceiling
     * = reading + window, unless {@code root-domains.jsonl} declares bounds
     * (the only way to ask for a backward move).</p>
     *
     * <p>ONE ORDER PER CLOCK OF A NODE: a cell is no earlier than the last
     * cell before it by seq -- the event the recording read it at, the order
     * a replay runs a planted clock on in ({@code runtime.NodeClocks}) --
     * that read the same clock ({@link Clock#same}: one JVM clock at one
     * tick; a node's wall clock and a monotonic one are two, and ordering
     * those against each other made every path false; a cell whose row
     * states no JVM clock is on no order, named).  Where the recording's own
     * readings of the two run the other way (two threads between reading
     * and logging), the order gives way by that much, so the recording
     * always satisfies it.  {@code earlierOf} maps each ordered cell to that
     * cell, which the claim runs its clock on from ({@code
     * ClaimPolicy#runsOn}); {@code cells} are in seq order, the order the
     * claim pins them back in.</p>
     */
    private void clocks(List<String> cells, Map<String, Long> readings,
                        Map<String, Long> ticks,
                        Map<String, String> earlierOf) {
        String seed = seed();
        List<RootMintRow> clocks = new ArrayList<RootMintRow>();
        List<RootMintRow> read = new ArrayList<RootMintRow>();
        for (Map.Entry<String, List<RootMintRow>> entry
                : corpus.roots().entrySet()) {
            RootMintRow row = seedRow(entry.getValue());
            if (row.kind() != RootKind.CLOCK
                    || !lowering.declared(row.symbol())) {
                continue;
            }
            Long reading = instant(row);
            if (reading == null) continue;
            clocks.add(row);
            if (row.sessionId().equals(seed)) {
                readings.put(row.symbol(), reading);
                read.add(row);
            }
        }
        List<RootMintRow> placedCells = new ArrayList<RootMintRow>();
        for (RootMintRow row : clocks) {
            if (!readings.containsKey(row.symbol())) {
                Long reading = placed(corpus.roots().get(row.rootId()),
                        read, readings);
                if (reading == null) {
                    gap(GapKind.DECLARATION_MISSING, GapClass.BLOCKING,
                            row.rootId(), "this clock cell reaches the "
                                    + "composition, the recording never "
                                    + "read it, and no session that read it "
                                    + "read a cell of the same clock the "
                                    + "recording read, so it has no instant "
                                    + "on the recording's timeline: no claim "
                                    + "can say whether a witness moved it");
                    continue;
                }
                readings.put(row.symbol(), reading);
            }
            long reading = readings.get(row.symbol());
            String instant = Long.toString(reading);
            placedCells.add(row);
            ticks.put(row.symbol(), row.clockNanos());
            RootDomain domain = RootDomain.resolved(row, instant,
                    declaredDomains);
            String floor = domain.min() == null ? instant
                    : integralLiteral(domain.min());
            String ceiling = domain.max() == null
                    ? JavaPrimitiveSmtSemantics.clockSkewCeiling(instant,
                            row.clockNanos())
                    : integralLiteral(domain.max());
            roots.put(row.rootId(), RootDomain.of(row.rootId(),
                    RootKind.CLOCK, instant, floor, ceiling));
            lowering.assertNamed("clock_domain__"
                            + ArtifactIO.digest(row.symbol(), 10),
                    JavaPrimitiveSmtSemantics.clockDomain(row.symbol(),
                            floor, ceiling));
            if (row.clock().source().isEmpty()) {
                gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        row.rootId(), "this clock cell's row states no JVM "
                                + "clock it reads, so it is on no clock's "
                                + "order: no cell runs on from it, and it "
                                + "from none");
            }
        }
        Map<NodeId, List<RootMintRow>> byNode =
                new LinkedHashMap<NodeId, List<RootMintRow>>();
        for (RootMintRow row : placedCells) {
            byNode.computeIfAbsent(row.occurrence().node(),
                    node -> new ArrayList<RootMintRow>()).add(row);
        }
        placedCells.sort(Comparator.comparingLong(RootMintRow::seq)
                .thenComparing(RootMintRow::symbol));
        for (RootMintRow row : placedCells) cells.add(row.symbol());
        for (List<RootMintRow> mints : byNode.values()) {
            mints.sort(Comparator.comparingLong(RootMintRow::seq));
            for (int index = 1; index < mints.size(); index++) {
                String later = mints.get(index).symbol();
                long reading = readings.get(later);
                for (int before = index - 1; before >= 0; before--) {
                    String earlier = mints.get(before).symbol();
                    long earlierReading = readings.get(earlier);
                    if (!mints.get(index).clock().same(
                            mints.get(before).clock())) {
                        continue;
                    }
                    long inversion = earlierReading - reading;
                    lowering.assertNamed("clock_order__" + ArtifactIO.digest(
                                    earlier + "|" + later, 10),
                            inversion <= 0L
                                    ? "(<= " + earlier + " " + later + ")"
                                    : "(<= (- " + earlier + " " + later
                                    + ") " + integralLiteral(
                                            Long.toString(inversion)) + ")");
                    earlierOf.put(later, earlier);
                    break;
                }
            }
        }
    }

    /**
     * A clock row's host reading, or null (named) when it states no
     * instant.
     */
    private Long instant(RootMintRow row) {
        Long reading = number(row.hostReading());
        if (reading == null) {
            gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    row.rootId(), "the mint of this clock cell states no "
                            + "instant (" + row.recordedValue() + "), so it "
                            + "has no domain and no reading");
        }
        return reading;
    }

    /**
     * How far each session's host clock read a clock cell later than the
     * recording read it (session -> cell symbol -> milliseconds or ticks of
     * that clock; {@link SmtLowering#clockBases}): its host reading less the
     * recording's, at the cell itself where the recording read it, else at
     * the nearest cell (by seq) of the same clock of the same node that both
     * read -- the same anchor {@link #placed} puts a cell on the recording's
     * timeline by.  The recording's own and a cell no shared cell anchors
     * have none.
     */
    private Map<String, Map<String, Long>> clockBases() {
        String seed = seed();
        Map<String, Map<String, Long>> bases =
                new LinkedHashMap<String, Map<String, Long>>();
        if (seed == null) return bases;
        Map<String, List<RootMintRow>> bySession =
                new LinkedHashMap<String, List<RootMintRow>>();
        for (List<RootMintRow> rows : corpus.roots().values()) {
            for (RootMintRow row : rows) {
                if (row.kind() == RootKind.CLOCK
                        && !row.sessionId().equals(seed)) {
                    bySession.computeIfAbsent(row.sessionId(),
                            session -> new ArrayList<RootMintRow>()).add(row);
                }
            }
        }
        for (Map.Entry<String, List<RootMintRow>> session
                : bySession.entrySet()) {
            // Its cells the recording read too, each with how far late.
            Map<RootMintRow, Long> anchored =
                    new LinkedHashMap<RootMintRow, Long>();
            for (RootMintRow row : session.getValue()) {
                RootMintRow recorded = corpus.rootOf(seed, row.rootId());
                Long host = number(row.hostReading());
                Long reading = recorded == null ? null
                        : number(recorded.hostReading());
                if (host != null && reading != null) {
                    anchored.put(row, host - reading);
                }
            }
            Map<String, Long> late = new LinkedHashMap<String, Long>();
            for (RootMintRow row : session.getValue()) {
                Long base = anchored.get(row);
                if (base == null) {
                    RootMintRow nearest = null;
                    for (RootMintRow anchor : anchored.keySet()) {
                        if (!anchor.occurrence().node().equals(
                                row.occurrence().node())
                                || row.clock() == null
                                || !row.clock().same(anchor.clock())) {
                            continue;
                        }
                        long distance = Math.abs(anchor.seq() - row.seq());
                        if (nearest == null || distance
                                < Math.abs(nearest.seq() - row.seq())
                                || (distance == Math.abs(nearest.seq()
                                - row.seq()) && anchor.seq() < nearest.seq())) {
                            nearest = anchor;
                        }
                    }
                    base = nearest == null ? null : anchored.get(nearest);
                }
                if (base != null && base != 0L) late.put(row.symbol(), base);
            }
            if (!late.isEmpty()) bases.put(session.getKey(), late);
        }
        return bases;
    }

    /**
     * Where a cell the recording never read sits on its timeline: for the
     * first session (of {@code rows}) that also read a cell the recording
     * read on the same clock of the same node, the recording's reading of
     * the nearest such cell (by seq, the earlier on a tie) plus the time
     * that session's host read from it to this cell.  Null when no session
     * read one.
     */
    private Long placed(List<RootMintRow> rows, List<RootMintRow> read,
                        Map<String, Long> readings) {
        for (RootMintRow cell : rows) {
            Long host = number(cell.hostReading());
            if (cell.kind() != RootKind.CLOCK || host == null) continue;
            RootMintRow nearest = null;
            long from = 0L;
            for (RootMintRow anchor : read) {
                RootMintRow same = corpus.rootOf(cell.sessionId(),
                        anchor.rootId());
                Long sameHost = same == null ? null
                        : number(same.hostReading());
                if (sameHost == null || !anchor.occurrence().node().equals(
                        cell.occurrence().node())
                        || !cell.clock().same(same.clock())) {
                    continue;
                }
                long distance = Math.abs(anchor.seq() - cell.seq());
                long best = nearest == null ? Long.MAX_VALUE
                        : Math.abs(nearest.seq() - cell.seq());
                if (distance < best || (distance == best
                        && anchor.seq() < nearest.seq())) {
                    nearest = anchor;
                    from = sameHost;
                }
            }
            if (nearest != null) {
                return readings.get(nearest.symbol()) + (host - from);
            }
        }
        return null;
    }

    private static Long number(String text) {
        try {
            return Long.valueOf(text.trim());
        } catch (NumberFormatException notAnInstant) {
            return null;
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

    /**
     * Every model CONFIRM refuted ({@link Refutations}), excluded: its path,
     * the arms it chose there, its valuation and the clock cells it moved,
     * at the model's instants, are, together, no model of this formula, so a
     * claim over it is another model or none.  A model whose path or arm
     * this corpus no longer composes cannot recur and is not stated; a root
     * or cell this query does not name constrains nothing.  Roots are named
     * as the valuations name them ({@link Corpus#anyRoot}).
     */
    private void refutations(List<Disjunct> disjuncts) {
        List<Refutations.Refuted> refuted;
        try {
            refuted = Refutations.read(corpus.iteration());
        } catch (java.io.IOException | RuntimeException unreadable) {
            gap(GapKind.CLAIM_REFUTED, GapClass.BLOCKING, Refutations.FILE,
                    "this iteration's refuted claims could not be read, so "
                            + "a claim over it may be one CONFIRM refuted: "
                            + unreadable);
            return;
        }
        int ordinal = 0;
        for (Refutations.Refuted model : refuted) {
            String path = null;
            for (Disjunct disjunct : disjuncts) {
                if (disjunct.path().pathId.equals(model.pathId)) {
                    path = disjunct.selector();
                }
            }
            if (path == null) continue;
            List<String> conjuncts = new ArrayList<String>();
            conjuncts.add(path);
            boolean composed = true;
            for (String arm : model.arms) {
                String here = Refutations.atPath(arm,
                        Refutations.ordinal(path));
                composed &= lowering.declared(here);
                conjuncts.add(here);
            }
            if (!composed) continue;
            Map<String, String> pinned = new LinkedHashMap<String, String>();
            for (Map.Entry<String, String> root
                    : model.assignment.entrySet()) {
                RootMintRow row = corpus.anyRoot(root.getKey());
                if (row == null || row.kind() == RootKind.CLOCK) continue;
                pinned.put(row.symbol(), smtLiteral(root.getValue(),
                        sortOf(row)));
            }
            // A moved clock is named by its cell's symbol.
            for (Map.Entry<String, String> cell : model.moved.entrySet()) {
                if (corpus.anyRoot(cell.getKey()) != null) continue;
                pinned.put(cell.getKey(), smtLiteral(cell.getValue(),
                        Sort.INT));
            }
            for (Map.Entry<String, String> pin : pinned.entrySet()) {
                if (pin.getValue().isEmpty()
                        || !lowering.declared(pin.getKey())) {
                    continue;
                }
                conjuncts.add("(= " + pin.getKey() + " " + pin.getValue()
                        + ")");
            }
            lowering.assertNamed("refuted_claim__" + ordinal++,
                    "(not " + VmTermLowering.and(conjuncts) + ")");
            gap(GapKind.CLAIM_REFUTED, GapClass.DIAGNOSTIC, model.pathId,
                    "CONFIRM refuted the model on this path with arms "
                            + model.arms + " at " + model.assignment
                            + (model.moved.isEmpty() ? ""
                            : " moving " + model.moved)
                            + ", so it is excluded: " + model.reason);
        }
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
            String literal = smtLiteral(entry.getValue(), sortOf(row));
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
