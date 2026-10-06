package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.JavaSmtSorts;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.compose.SmtNames;
import edu.uva.liftlab.graphchecker.compose.VmTermLowering;
import edu.uva.liftlab.graphchecker.smt.Arms;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.contract.WriteRow;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * One obligation's query: the path as its replay ran it, one decision negated,
 * over a world the corpus states. Four rules decide what a symbol may be:
 *
 * <ul>
 *   <li>a ROOT is one quantity across the corpus: free in its declared
 *       domain (a marker over both values), else PINNED to the recorded read,
 *       as the composition pins it;</li>
 *   <li>a CLOCK is per path, never equal across paths, with domain {@code
 *       [host reading, host reading + 30 days]} in the clock's own ticks:
 *       the host's reading of that execution ({@code
 *       RootMintRow#hostReading}), which a skew is off, so no model skews a
 *       clock behind its host ({@link
 *       JavaPrimitiveSmtSemantics#clockSkewCeiling}; no reading: {@code [0,
 *       Long.MAX_VALUE]}); its nearest world is the instant the execution
 *       ran it at (PIPELINE §7.5);</li>
 *   <li>a CONTROL handoff (attached at the flipped occurrence, where a
 *       replay can be answered) is bound by its family {@code OR_q (pi_q AND
 *       guard_q AND v_H = e_q)}, closed to a fixed point over forwarded
 *       handoffs; no arm = free and {@code unproducible}. EVERY
 *       OTHER handoff is bound by the arms of its OWN run only (what that
 *       run's producer computed it from, over roots and clocks the replay
 *       plants), and PINNED to its recorded arrival where none states
 *       it;</li>
 *   <li>a STATE read offers its eligible writers ({@link Arms#stateArms}) as
 *       exactly-one Bool selectors ({@code wchoice_*}), each binding it to
 *       what that writer delivered, plus the run's own choice where no one
 *       writer's arm is the run; with no writer (or none that lowers) it
 *       is pinned to the row's {@code concreteValue}, else the obligation is
 *       refused ({@code UNSTATED_VALUE}) (PIPELINE §7.5).</li>
 * </ul>
 *
 * <p>Nothing else is free: an undeclared name refuses the obligation on the
 * flipped decision and drops the conjunct (named gap) on a prefix decision.
 * Demanded conjuncts (this flip and inherited flips) get a clock {@link
 * ClockMargin}; prefix decisions do not.</p>
 */
final class FlipQuery {
    private FlipQuery() {
    }

    /** One handoff of the focused occurrence the replay can be answered at. */
    static final class Control {
        final String attachEndpointId;
        final String variable;
        /** The variable's sort ({@link VmTermLowering.Sort#smt}): how the
         *  model's value of it is spelled as an answer. */
        final String sort;
        final boolean unproducible;

        private Control(String attachEndpointId, String variable,
                        String sort, boolean unproducible) {
            this.attachEndpointId = attachEndpointId;
            this.variable = variable;
            this.sort = sort;
            this.unproducible = unproducible;
        }
    }

    /** One assembled query, or the reason there is none. */
    static final class Built {
        /** The formula: declarations and assertions, without a check-sat. */
        final String smt2;
        /** Every declared variable, in order: the names a model is asked for.
         */
        final List<String> modelSymbols;
        final String refusal;
        final List<Control> controls;
        /** query variable -> root, for model read-back: only roots the
         *  assertions REACH ({@link Builder#reached}). A root the flip does not
         *  depend on is a free solver pick, and planting it would owe an
         *  ASSIGNMENT_UNPLANTED; hence {@link Builder#rootFacts} is kept apart.
         */
        final Map<String, String> rootVariables;
        /** The same for the flipped path's clocks, apart because a clock's
         *  model is read back as a SKEW the replay adds to its own reading. */
        final Map<String, String> clockVariables;
        /** Each reader's choice of writer per location ({@code
         *  wchoice_*}). */
        final List<WriterChoice> choices;
        final List<GapRow> gaps;

        private Built(String smt2, List<String> modelSymbols, String refusal,
                      List<Control> controls, Map<String, String> rootVariables,
                      Map<String, String> clockVariables,
                      List<WriterChoice> choices, List<GapRow> gaps) {
            this.smt2 = smt2;
            this.modelSymbols =
                    Collections.unmodifiableList(modelSymbols);
            this.refusal = refusal;
            this.controls = Collections.unmodifiableList(controls);
            this.rootVariables =
                    Collections.unmodifiableMap(rootVariables);
            this.clockVariables =
                    Collections.unmodifiableMap(clockVariables);
            this.choices = Collections.unmodifiableList(choices);
            this.gaps = Collections.unmodifiableList(gaps);
        }

        boolean ok() {
            return refusal.isEmpty();
        }
    }

    /** Whether one recorded decision is a flip candidate at all: it carries a
     *  term (a branch with a symbol IS a flip target; producibility is the
     *  solver's verdict, {@link Builder#unbound}).
     *  A CONCRETE branch has no term to negate. Where candidates may sit is the
     *  closure's question (PIPELINE §7.4, {@link
     *  ObligationFactory#candidates}). */
    static boolean flippable(DecisionRow decision) {
        return Arms.predicate(decision.term());
    }

    /**
     * Whether a task's flip sites ask this decision: every decision at a
     * site they name, or the one decision an entry {@link #asked} names
     * (an open decider arm's, TargetRow.OpenArm: only the call that fed the
     * guard, never every call of the helper).
     */
    static boolean asks(Set<String> flipSites, DecisionRow decision) {
        return flipSites.contains(decision.siteId())
                || flipSites.contains(asked(decision.siteId(),
                decision.ordinal()));
    }

    /** A flip-site entry naming one decision of a site. */
    static String asked(String siteId, int ordinal) {
        return siteId + "@" + ordinal;
    }

    /** One published term with its {@code EXPR.} references lowered by the ONE
     *  lowering (as the composer does), so flip and composition read the same
     *  predicate. A term with no reference returns unchanged. */
    static String statedTerm(Corpus corpus, String sessionId,
                             String term) {
        if (term == null || term.isEmpty()) return "";
        SmtLowering lowering = corpus.lowering(sessionId);
        if (lowering == null) return term;
        String lowered = lowering.statedTerm(term, "flip:" + sessionId);
        // A refusal ("") keeps the raw term; the unknown-symbol rule names it.
        return lowered.isEmpty() ? term : lowered;
    }

    static Built build(Corpus corpus, Task task, Corpus.RecordedPath path,
                       int flipIndex) {
        return new Builder(corpus, task, path).build(flipIndex);
    }

    /** One symbol as one session named it. */
    private static final class Ref {
        private final String sessionId;
        private final String symbol;

        private Ref(String sessionId, String symbol) {
            this.sessionId = sessionId;
            this.symbol = symbol;
        }

        private String key() {
            return sessionId + "|" + symbol;
        }
    }

    /**
     * One reader occurrence's choice of writer for one location ({@code
     * wchoice_*}): the reads it made of the location, which move as a block
     * (IDENTITY §4), and the write each selector delivers them.  A model
     * that sets another selector than the recorded writer's moves the
     * pairing, which an obligation replay plants
     * ({@code ObligationFactory#planted}).
     */
    static final class WriterChoice {
        /** The reads the choice binds. */
        final List<ReadRow> reads = new ArrayList<ReadRow>();
        /** Selector -> the write it delivers (null: an arm stating none, the
         *  run's own choice among them). */
        final Map<String, WriteRow> writes =
                new LinkedHashMap<String, WriteRow>();
        /** The selector of the run as it happened: the writer the reads
         *  observed, the run's own choice where that is no one writer's arm
         *  ({@code Builder#choices}), or "" where no eligible writer wrote
         *  what they saw. */
        String recorded = "";
        /** (reader occurrence, location), the reader and the location. */
        private final String key;
        private final OccurrenceAddress reader;
        private final LocationId location;
        private final List<Choice> alternatives = new ArrayList<Choice>();
        /** Each bound read's variable -> the read, and its observed write's
         *  delivery as the query spells it (null: none, or none that
         *  lowers): what the run's choice holds it to. */
        private final Map<String, ReadRow> boundReads =
                new LinkedHashMap<String, ReadRow>();
        private final Map<String, String> observedDelivery =
                new LinkedHashMap<String, String>();
        /** The selectors a read of another version could not have seen
         *  ({@link Arms#eligible}): no choice once the block saw two. */
        private final Set<String> ineligible = new LinkedHashSet<String>();
        /** Where its exactly-one stands among the query's assertions:
         *  restated over the run's choice too when that is added. */
        private int exactlyOne;
        /** Whether the observed writer's selector delivers some read a
         *  value of another sort: no choice once the run's replaces it. */
        private boolean recordedDeliversNothing;
        /** Whether no one writer's arm is the run: the reads saw several
         *  versions, or one no row wrote. */
        private boolean asHappened;

        private WriterChoice(String key, OccurrenceAddress reader,
                             LocationId location) {
            this.key = key;
            this.reader = reader;
            this.location = location;
        }
    }

    /** One eligible writer occurrence, and the selector that picks it. */
    private static final class Choice {
        private final String selector;
        private final Arms.Arm alternative;

        private Choice(String selector, Arms.Arm alternative) {
            this.selector = selector;
            this.alternative = alternative;
        }
    }

    private static final class Builder
            implements FlipQueryText.Scope {
        private final Corpus corpus;
        private final Task task;
        private final Corpus.RecordedPath path;
        private final SmtText.Names names = new SmtText.Names();
        private final Map<String, String> sorts =
                new LinkedHashMap<String, String>();
        private final Map<String, String> meaning =
                new LinkedHashMap<String, String>();
        private final List<String> assertions = new ArrayList<String>();
        /** The ROOT rule's statements about a root's own variable (window,
         *  clock floor, or pin), kept apart from assertions so the model
         *  projection ({@link Built#rootVariables}) is not trivially "every
         *  root". */
        private final List<String> rootFacts = new ArrayList<String>();
        /**
         * query variable -> recorded literal, for bounded Int roots and clocks:
         * THE NEAREST-WORLD RULE. z3 answers at a window's boundary, and a
         * clock moved by the whole window changes what the replay does; so the
         * query minimizes sum |x - recorded|: the smallest move that still
         * flips, with margin.
         */
        private final Map<String, String> nearest =
                new LinkedHashMap<String, String>();
        /**
         * What each session's lowering states about declared names (non-null
         * identities, integral domains, container shapes; {@link
         * SmtLowering#facts}). Apart from assertions: recording facts, not the
         * claim, and no reason to keep a name in the model. Unstated, a solver
         * may null an object the recording saw non-null.
         */
        private final List<String> statedFacts = new ArrayList<String>();
        private final Set<String> explained = new LinkedHashSet<String>();
        private final Deque<Ref> pending = new ArrayDeque<Ref>();
        private final Set<String> queued = new LinkedHashSet<String>();
        private final Map<String, Control> controls =
                new LinkedHashMap<String, Control>();
        /** reader occurrence + location -> its one choice of writer. */
        private final Map<String, WriterChoice> choicesByReader =
                new LinkedHashMap<String, WriterChoice>();
        /** The flipped occurrence's own reads, by symbol ({@link
         *  #readOf}). */
        private final Map<String, ReadRow> ownReads =
                new LinkedHashMap<String, ReadRow>();
        private final Map<String, String> rootVariables =
                new LinkedHashMap<String, String>();
        private final Map<String, String> clockVariables =
                new LinkedHashMap<String, String>();
        /** Sessions whose lowering this query's terms are written in. */
        private final Set<String> lowered = new LinkedHashSet<String>();
        /** session|symbol the query bound to a variable of its own. */
        private final Set<String> bound = new LinkedHashSet<String>();
        /** session -> recorded symbol -> the query's variable for it. */
        private final Map<String, Map<String, String>> renames =
                new LinkedHashMap<String, Map<String, String>>();
        /** Every declared CLOCK cell, by variable, with its MARGIN in its
         *  own ticks: what {@code clockDomain} bounds and the margin applies
         *  to. {@link #clockVariables} (read-back) holds only the flipped
         *  path's own. */
        private final Map<String, Long> clockCells =
                new LinkedHashMap<String, Long>();
        /** Every clock variable, with the row of the execution it reads
         *  ({@link #clockOrder}). */
        private final Map<String, RootMintRow> clockRows =
                new LinkedHashMap<String, RootMintRow>();
        private final List<GapRow> gaps = new ArrayList<GapRow>();
        private String refusal = "";

        private Builder(Corpus corpus, Task task, Corpus.RecordedPath path) {
            this.corpus = corpus;
            this.task = task;
            this.path = path;
        }

        /** Whether a lowered conjunct is unusable: blank, or an application
         *  with missing arguments ({@code (not )}), which z3 answers with an
         *  error and no verdict. */
        private static boolean malformed(String term) {
            if (term == null || term.trim().isEmpty()) return true;
            for (int at = term.indexOf('('); at >= 0;
                    at = term.indexOf('(', at + 1)) {
                int index = at + 1;
                while (index < term.length()
                        && !Character.isWhitespace(term.charAt(index))
                        && term.charAt(index) != '('
                        && term.charAt(index) != ')') {
                    index++;
                }
                if (index == at + 1) continue;
                while (index < term.length()
                        && Character.isWhitespace(term.charAt(index))) {
                    index++;
                }
                if (index < term.length() && term.charAt(index) == ')') {
                    return true;
                }
            }
            return false;
        }

        private Built build(int flipIndex) {
            DecisionRow flipped = path.decisions.get(flipIndex);
            movableReads();
            for (int index = 0; index <= flipIndex; index++) {
                DecisionRow decision = path.decisions.get(index);
                Set<String> unknown = new LinkedHashSet<String>();
                // Arms.conjunct is the one "what a decision asserts" (shared
                // with the composer); renaming follows: polarity is the
                // recording's, names ours.
                boolean last = index == flipIndex;
                if (!Arms.predicate(decision.term())) {
                    // Concrete: nothing to assert, never the flipped decision.
                    continue;
                }
                String held = rename(conjunct(decision, path.sessionId),
                        path.sessionId, unknown);
                if (!unknown.isEmpty()) {
                    String named = unknown.iterator().next();
                    if (last) {
                        return refuse(GapKind.DECLARATION_MISSING,
                                decision.siteId() + "#" + decision.ordinal(),
                                "the flipped predicate names " + named
                                        + ", which no mint, attach or read of "
                                        + path.sessionId + " declares",
                                flipped);
                    }
                    gaps.add(GapRow.of(path.sessionId,
                            GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                            decision.siteId() + "#" + decision.ordinal(),
                            "prefix conjunct dropped: " + named
                                    + " is undeclared"));
                    continue;
                }
                // A term that cannot be stated (blank, or missing arguments) is
                // refused by name, never negated: z3 would reject the whole
                // query and lose the arm.
                if (malformed(held)) {
                    if (last) {
                        return refuse(GapKind.DECLARATION_MISSING,
                                decision.siteId() + "#" + decision.ordinal(),
                                "the flipped predicate lowers to a term this "
                                        + "query cannot state (\"" + held
                                        + "\"), so the flip is refused rather "
                                        + "than asked as a malformed query",
                                flipped);
                    }
                    gaps.add(GapRow.of(path.sessionId,
                            GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                            decision.siteId() + "#" + decision.ordinal(),
                            "prefix conjunct dropped: it lowers to a term "
                                    + "this query cannot state (\"" + held
                                    + "\")"));
                    continue;
                }
                // The obligation IS the complement of the recorded arm, with
                // clock margin.
                if (last) flippedText = held;
                assertions.add(last
                        ? demanded("(not " + held + ")", decision)
                        : held);
            }
            Built refused = inheritedFlips(flipped);
            if (refused != null) return refused;
            drain();
            choices();
            clockOrder();
            stateFacts();
            if (!refusal.isEmpty()) return refused(refusal, flipped);
            String free = unbound();
            if (!free.isEmpty()) {
                return refuse(GapKind.UNPRODUCIBLE_ANSWER, free,
                        "the query would declare this recorded symbol and "
                                + "bind it to nothing: no family and no pin "
                                + "states it, so the query is not causally "
                                + "closed and a model of it would answer "
                                + "with a value the chain does not reach",
                        flipped);
            }
            // A query whose FLIPPED predicate reaches no variable of its own
            // is not sent: whatever the other conjuncts bind, every name the
            // predicate rests on is a definition or a recorded fact, so its
            // arm is the recording's (UNSAT would be a false "no world", SAT
            // the seed replay); a variable a prefix decision binds is no
            // reason to ask it.
            Set<String> cone = flipCone();
            if (!moves(cone) && !framed(cone).isEmpty()) {
                // A leaf a frame's write was freed to (its writer computed
                // on an arrival it refused, SmtLowering.RefusalFrame): no
                // plant reaches it, so no replay can take the flip.
                return refuse(GapKind.UNPRODUCIBLE_ANSWER,
                        GapClass.DIAGNOSTIC, ExploreCodec.EXPLORATION,
                        flipped.siteId() + "#" + flipped.ordinal(),
                        "the flipped predicate rests only on values a "
                                + "frame wrote on an arrival it refused "
                                + framed(cone) + ": free in the formula, "
                                + "reached by no plant, so no replay can "
                                + "take this flip",
                        flipped);
            }
            if (!moves(cone)) {
                return refuse(GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        ExploreCodec.EXPLORATION,
                        flipped.siteId() + "#" + flipped.ordinal(),
                        "this query declares no variable of its own: no "
                                + "root, no clock, no handoff control and no "
                                + "movable read reaches the flipped "
                                + "predicate, so whichever arm it is the "
                                + "answer is the recording's own facts and "
                                + "not a world this corpus lacks",
                        flipped);
            }
            // One notion of reached for both read-back maps.
            Set<String> reached = reachedVariables();
            return new Built(FlipQueryText.render(corpus, task,
                    path, lowered, this, meaning, sorts, asserted(), nearest,
                    flipped, flipIndex),
                    new ArrayList<String>(sorts.keySet()), "",
                    new ArrayList<Control>(controls.values()),
                    reached(rootVariables, reached),
                    reached(clockVariables, reached),
                    new ArrayList<WriterChoice>(choicesByReader.values()),
                    gaps);
        }

        /**
         * THE PARENT'S FLIPS, asserted: a cut path exists only in its parent's
         * world ({@link Corpus.World}), so each inherited flip's occurrence
         * prefix THROUGH the flipped decision is asserted, lowered and renamed
         * in the cut session's scope. Assertions, not facts, so the projection
         * reaches their roots and clocks.
         *
         * <p>Fail closed: an unknown occurrence, a missing or opposite
         * decision, or an undeclared name in the flipped conjunct refuses by
         * name; an undeclared name in an inherited prefix conjunct drops it
         * (DIAGNOSTIC).</p>
         *
         * @return the refusal, or null when every inherited flip is stated
         */
        private Built inheritedFlips(DecisionRow flipped) {
            for (Corpus.Flip inherited
                    : corpus.world(path.sessionId).flips) {
                OccurrenceAddress at =
                        corpus.occurrence(inherited.focusedOccurrenceId);
                if (at == null) {
                    return refuseInherited(inherited, flipped);
                }
                List<DecisionRow> decisions =
                        corpus.decisionsOf(path.sessionId, at);
                DecisionRow row = null;
                for (DecisionRow candidate : decisions) {
                    if (candidate.siteId().equals(inherited.siteId)
                            && candidate.ordinal() == inherited.ordinal) {
                        row = candidate;
                    }
                }
                if (row == null || row.outcome() != inherited.outcome) {
                    return refuseInherited(inherited, flipped);
                }
                // The parent's prefix through its flipped decision;
                // Arms.pathCondition owns the polarity, as in the composition.
                List<DecisionRow> taken = new ArrayList<DecisionRow>();
                for (DecisionRow candidate : decisions) {
                    if (candidate.seq() < row.seq() + 1) taken.add(candidate);
                }
                List<String> pi = Arms.pathCondition(decisions,
                        row.seq() + 1);
                for (int index = 0; index < pi.size(); index++) {
                    DecisionRow decision = taken.get(index);
                    if (!Arms.predicate(decision.term())) continue;
                    Set<String> unknown = new LinkedHashSet<String>();
                    String held = rename(lower(pi.get(index),
                            path.sessionId), path.sessionId, unknown);
                    if (unknown.isEmpty()) {
                        // The inherited flip is demanded too: margin on it, not
                        // its prefix.
                        assertions.add(decision == row
                                ? demanded(held, decision) : held);
                        continue;
                    }
                    String named = unknown.iterator().next();
                    if (decision == row) {
                        return refuse(GapKind.ADMISSION_GAP,
                                inherited.siteId + "#" + inherited.ordinal,
                                "the flipped conjunct of the flip this path "
                                        + "inherited names " + named
                                        + ", which no mint, attach or read "
                                        + "of " + path.sessionId
                                        + " declares: " + inherited.render(),
                                flipped);
                    }
                    gaps.add(GapRow.of(path.sessionId,
                            GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                            decision.siteId() + "#" + decision.ordinal(),
                            "prefix conjunct dropped: " + named
                                    + " is undeclared"));
                }
            }
            return null;
        }

        /**
         * One DEMANDED conjunct (this flip, or an inherited one) with the clock
         * margin ({@link ClockMargin}): the replay runs a skewed reading, not
         * the model's instant. Applied to the lowered, renamed text (the only
         * form with whole atoms and this query's clock variables); unmarginable
         * atoms are named once as a diagnostic.
         */
        private String demanded(String held, DecisionRow decision) {
            ClockMargin.Strengthened asked = ClockMargin.strengthen(held,
                    clockCells);
            for (String atom : asked.unstrengthened) {
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        decision.siteId() + "#" + decision.ordinal(),
                        "the clock margin of one minute was not put on the "
                                + "atom " + atom
                                + ": its polarity is not resolved by this "
                                + "query's connectives, its operands are not "
                                + "arithmetic, or it compares clocks of two "
                                + "ticks, so the demanded arm is asked for "
                                + "as the solver's model states it"));
            }
            return asked.text;
        }

        private Built refuseInherited(Corpus.Flip inherited,
                                      DecisionRow flipped) {
            return refuse(GapKind.ADMISSION_GAP,
                    inherited.siteId + "#" + inherited.ordinal,
                    "the session this path was cut from states no decision "
                            + "for the flip it inherited: "
                            + inherited.render(), flipped);
        }

        /** THE PROJECTION: the entries of one read-back map whose variables the
         *  assertions reach ({@link #reachedVariables}). A root reached only
         *  via a dropped arm would otherwise be planted at a mint the flip
         *  never read. */
        private Map<String, String> reached(Map<String, String> declared,
                                            Set<String> names) {
            Map<String, String> kept = new LinkedHashMap<String, String>();
            for (Map.Entry<String, String> variable : declared.entrySet()) {
                if (names.contains(variable.getKey())) {
                    kept.put(variable.getKey(), variable.getValue());
                }
            }
            return kept;
        }

        /** Every variable the ASSERTIONS reach, including through the renamed
         *  definitions they mention ({@link FlipQueryText}); never via {@link
         *  #rootFacts}. */
        private Set<String> reachedVariables() {
            Set<String> names = new LinkedHashSet<String>();
            for (String assertion : assertions) {
                SmtNames.symbols(assertion, names);
            }
            for (String line : FlipQueryText.statedDeclarations(corpus,
                    lowered, this, assertions)) {
                SmtNames.symbols(line, names);
            }
            return names;
        }

        /** One term lowered, remembering the session so its declarations are
         *  rendered. */
        private String lower(String term, String sessionId) {
            String text = statedTerm(corpus, sessionId, term);
            if (text != null && !text.equals(term)) lowered.add(sessionId);
            return text;
        }

        /** Whether the rendered query already states this name. */
        @Override
        public boolean stated(String name, String sessionId) {
            if (SmtNames.preambleNames().contains(name)) return true;
            SmtLowering lowering = corpus.lowering(sessionId);
            return lowering != null && lowering.minted(name);
        }

        /** One decision as the arm its run took ({@link Arms#conjunct}),
         *  references lowered. */
        private String conjunct(DecisionRow decision, String sessionId) {
            return Arms.conjunct(lower(decision.term(), sessionId),
                    decision.outcome());
        }

        /** The fixed point: every symbol the query names gets its own rule. */
        private void drain() {
            int guard = 0;
            while (!pending.isEmpty() && refusal.isEmpty()) {
                if (++guard > 100_000) {
                    refusal = "SYMBOL_CLOSURE_DID_NOT_TERMINATE";
                    return;
                }
                Ref ref = pending.remove();
                switch (corpus.symbolKind(ref.sessionId, ref.symbol)) {
                    case ROOT:
                        root(corpus.rootBySymbol(ref.sessionId, ref.symbol));
                        break;
                    case HANDOFF:
                        handoff(corpus.attach(ref.sessionId, ref.symbol));
                        break;
                    case READ:
                        read(readOf(ref.sessionId, ref.symbol));
                        break;
                    default:
                        break;
                }
            }
        }

        /**
         * ONE ORDER PER CLOCK OF A NODE, as COMPOSE states it ({@code
         * Composer#clocks}): within one execution a cell is no earlier than
         * the cell before it (by seq) on the same clock of the same node,
         * giving way where that execution read the two the other way round.
         * Without it a model jumps a clock forward at one cell and back at
         * the next, a replay plants exactly that, and no composed world is
         * that replay's own (hdfs-11741 L1: be888ea2 +10 h, the next cell
         * 29a8b781 at the host's reading, in 485e5c2a and 92985f34).
         */
        private void clockOrder() {
            Map<String, List<Map.Entry<String, RootMintRow>>> byClock =
                    new LinkedHashMap<String,
                            List<Map.Entry<String, RootMintRow>>>();
            for (Map.Entry<String, RootMintRow> cell : clockRows.entrySet()) {
                RootMintRow row = cell.getValue();
                if (row.clock() == null || row.clock().source().isEmpty()) {
                    continue;
                }
                byClock.computeIfAbsent(row.sessionId() + "|"
                        + row.occurrence().node().render() + "|"
                        + row.clock().source() + "|" + row.clock().nanos(),
                        key -> new ArrayList<Map.Entry<String,
                                RootMintRow>>()).add(cell);
            }
            for (List<Map.Entry<String, RootMintRow>> cells
                    : byClock.values()) {
                cells.sort((one, two) -> Long.compare(one.getValue().seq(),
                        two.getValue().seq()));
                for (int at = 1; at < cells.size(); at++) {
                    String earlier = cells.get(at - 1).getKey();
                    String later = cells.get(at).getKey();
                    String inversion = inversion(
                            cells.get(at - 1).getValue(),
                            cells.get(at).getValue());
                    rootFacts.add(inversion.isEmpty()
                            ? "(<= " + earlier + " " + later + ")"
                            : "(<= (- " + earlier + " " + later + ") "
                            + inversion + ")");
                }
            }
        }

        /** How far the execution read {@code later} before {@code earlier},
         *  or "" where it read them in order (or states no instant). */
        private static String inversion(RootMintRow earlier,
                                        RootMintRow later) {
            try {
                BigInteger gap = new BigInteger(
                        earlier.recordedValue().trim()).subtract(
                        new BigInteger(later.recordedValue().trim()));
                return gap.signum() > 0 ? gap.toString() : "";
            } catch (NumberFormatException noInstant) {
                return "";
            }
        }

        // ---- the four rules ------------------------------------------

        private void root(RootMintRow minted) {
            String variable = variable(minted.sessionId(), minted.symbol());
            if (!explained.add(variable)) return;
            // A declared domain is relative to the FLIPPED path's own reading,
            // not whichever session's mint the drain reached first.
            RootMintRow own = corpus.rootOf(path.sessionId, minted.rootId());
            RootMintRow row = own == null ? minted : own;
            if (row.kind() == RootKind.CLOCK) {
                clockRows.put(variable, minted);
                // Read back only the flipped path's clock: another session's
                // instant is not one this replay can be held to.
                if (minted.sessionId().equals(path.sessionId)) {
                    clockVariables.put(variable, row.rootId());
                }
                // {@link JavaPrimitiveSmtSemantics#clockDomain}: floor = this
                // execution's host reading (a skew is off it, and never
                // below), ceiling = floor + window ({@link
                // JavaPrimitiveSmtSemantics#clockSkewCeiling}), so no model
                // flips by long overflow.  The nearest world is the instant
                // the execution ran the cell at, where its node's clock may
                // have run on off the host (RootMintRow#clockSkew).
                String floor = instant(minted.hostReading());
                rootFacts.add(JavaPrimitiveSmtSemantics.clockDomain(variable,
                        floor.isEmpty() ? "0" : floor,
                        JavaPrimitiveSmtSemantics.clockSkewCeiling(floor,
                                row.clockNanos())));
                String ran = instant(minted.recordedValue());
                if (!ran.isEmpty()) nearest.put(variable, ran);
                return;
            }
            rootVariables.put(variable, row.rootId());
            if (row.kind() == RootKind.MARKER && row.declared()) return;
            String[] domain = corpus.domainOf(row);
            if (domain == null) {
                // A declared relative window with no recorded reading is
                // unresolvable: named, not treated as "no domain".
                if (corpus.declaredDomain(row.rootId()) != null
                        && SmtText.literal(row.recordedValue(),
                                sorts.get(variable)).isEmpty()) {
                    gaps.add(GapRow.of(row.sessionId(),
                            GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            row.rootId(), "the case declares a window "
                                    + "relative to what this replay read and "
                                    + "the mint row states no reading, so "
                                    + "the root is neither enumerated nor "
                                    + "pinned"));
                    return;
                }
                pin(variable, row.recordedValue(),
                        "root " + row.rootId() + " has no declared domain");
                return;
            }
            String min = SmtText.literal(domain[0], sorts.get(variable));
            String max = SmtText.literal(domain[1], sorts.get(variable));
            if (min.isEmpty() || max.isEmpty()) {
                pin(variable, row.recordedValue(),
                        "root " + row.rootId() + " has an unreadable domain");
                return;
            }
            rootFacts.add("(and (>= " + variable + " " + min + ") (<= "
                    + variable + " " + max + "))");
            String recorded = SmtText.literal(row.recordedValue(),
                    sorts.get(variable));
            if (!recorded.isEmpty() && "Int".equals(sorts.get(variable))) {
                nearest.put(variable, recorded);
            }
        }

        /** A clock row's instant as a decimal, or "" when it states none a
         *  Java long can hold. */
        private static String instant(String reading) {
            if (reading == null || reading.trim().isEmpty()) return "";
            try {
                java.math.BigInteger instant =
                        new java.math.BigInteger(reading.trim());
                if (instant.signum() < 0
                        || !JavaPrimitiveSmtSemantics.fitsJavaLong(instant)) {
                    return "";
                }
                return instant.toString();
            } catch (NumberFormatException notAnInstant) {
                return "";
            }
        }

        private void handoff(AttachRow attach) {
            String variable = variable(attach.sessionId(), attach.symbol());
            boolean control = attach.endpoint().occurrence()
                    .equals(task.focused());
            if (!explained.add(variable)) {
                if (control) registerControl(attach, variable, false);
                return;
            }
            // Only a Control can be answered (ObligationFactory#solve applies
            // answers at the focused occurrence's attaches only).  Any other
            // handoff moves only as its own run's producer computed it: its
            // arms from that run alone, over roots and clocks the replay
            // plants, and pinned to its arrival where none states it.  Another
            // run's arrival is a value nothing would plant.
            List<String> disjuncts = new ArrayList<String>();
            Set<String> seen = new LinkedHashSet<String>();
            Map<String, List<String>> bySlot =
                    new LinkedHashMap<String, List<String>>();
            int offered = 0;
            if (attach.producer() != null) {
                Interaction slot = Interaction.of(InteractionKind.WIRE,
                        attach.producer(), attach.endpoint());
                for (Arms.Arm arm : corpus.arms().wireArms(slot,
                        attach.symbol())) {
                    if (!control
                            && !arm.sessionId().equals(attach.sessionId())) {
                        continue;
                    }
                    offered++;
                    String term = arm(arm, variable, attach.symbol());
                    if (term.isEmpty() || !seen.add(arm.slotId() + "|" + term)) {
                        continue;
                    }
                    List<String> held = bySlot.get(arm.slotId());
                    if (held == null) {
                        held = new ArrayList<String>();
                        bySlot.put(arm.slotId(), held);
                    }
                    held.add(term);
                }
                fileRefusals();
            }
            for (Map.Entry<String, List<String>> family : bySlot.entrySet()) {
                assertions.add(VmTermLowering.or(family.getValue()));
                if (family.getKey().equals(slotIdOf(attach))) {
                    disjuncts.addAll(family.getValue());
                }
            }
            if (!control) {
                if (disjuncts.isEmpty()) {
                    pinArrival(attach, variable, "a handoff of an occurrence "
                            + "this obligation cannot answer at, which no arm "
                            + "of its own run states");
                }
                return;
            }
            if (!disjuncts.isEmpty()) {
                registerControl(attach, variable, false);
                return;
            }
            // A PAIRED handoff whose every arm was dropped is REFUSED, never
            // answered with a value no producer sent. Only an UNPAIRED arrival
            // (from outside the corpus) is a free input, named unproducible.
            if (offered > 0) {
                refusal = "UNPRODUCIBLE_ANSWER:" + attach.endpoint();
                gaps.add(GapRow.of(attach.sessionId(),
                        GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                        attach.endpoint().toString(),
                        "the corpus pairs this handoff with a producer and "
                                + "none of its " + offered + " arm(s) can be"
                                + " stated by this query (the arm gaps name"
                                + " why), so the flip is not asked rather "
                                + "than answered with a value no producer "
                                + "sent"));
                return;
            }
            registerControl(attach, variable, true);
            gaps.add(GapRow.of(attach.sessionId(),
                    GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                    attach.endpoint().toString(),
                    "no producer arm in this corpus for this slot"));
        }

        /** One handoff pinned to its recorded arrival (a handoff no arm of
         *  its own run states). An arrival with no literal pins nothing and is
         *  named; the closure check then refuses the obligation. */
        private void pinArrival(AttachRow attach, String variable,
                                String why) {
            String arrival = SmtText.literal(attach.arrival(),
                    sorts.get(variable));
            if (arrival.isEmpty()) {
                gaps.add(GapRow.of(attach.sessionId(),
                        GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                        attach.endpoint().toString(),
                        why + ", and the recording states no arrival to pin "
                                + "it to"));
                return;
            }
            assertions.add("(= " + variable + " " + arrival + ")");
        }

        private String slotIdOf(AttachRow attach) {
            return attach.producer() == null ? "" : Interaction.of(
                    InteractionKind.WIRE, attach.producer(),
                    attach.endpoint()).id();
        }

        /** One arm in this query's variables. What an arm IS belongs to {@link
         *  Arms} (shared with the composer); here only renaming: roots
         *  corpus-wide, clocks per path, handoffs per INTERACTION (this query
         *  conjoins several sessions). */
        private String arm(Arms.Arm arm, String variable, String own) {
            Set<String> unknown = new LinkedHashSet<String>();
            SmtLowering.Lowered lowered = corpus.lowering(arm.sessionId())
                    .lower(arm.expressionRef());
            if (!lowered.ok()) {
                gaps.add(GapRow.of(arm.sessionId(),
                        GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        arm.slotId(), "arm dropped: its delivered "
                                + "expression " + arm.expressionRef()
                                + " does not lower"));
                return "";
            }
            String delivered = rename(lowered.text(), arm.sessionId(),
                    unknown);
            if (!unknown.isEmpty() || malformed(delivered)) {
                gaps.add(GapRow.of(arm.sessionId(),
                        GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        arm.slotId(), "arm dropped: its delivered "
                                + "expression "
                                + (unknown.isEmpty()
                                ? "lowers to a term this query cannot state"
                                : "names " + unknown.iterator().next()
                                + ", which is undeclared")));
                return "";
            }
            List<String> conjuncts = new ArrayList<String>();
            for (String term : arm.pi()) {
                // Same rule as the prefix (and the composer's pi_p): concrete
                // decisions are no conjunct, unstatable conjuncts are dropped
                // by name, and THE ARM STAYS. Dropping the whole arm leaves the
                // control with no family, and z3 then answers a value no
                // producer sent.
                if (!Arms.predicate(term)) continue;
                Set<String> undeclared = new LinkedHashSet<String>();
                String renamed = rename(lower(term, arm.sessionId()),
                        arm.sessionId(), undeclared);
                if (!undeclared.isEmpty() || malformed(renamed)) {
                    gaps.add(GapRow.of(arm.sessionId(),
                            GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                            arm.slotId(), "arm conjunct dropped: "
                                    + (undeclared.isEmpty()
                                    ? "it lowers to a term this query cannot "
                                    + "state (\"" + renamed + "\")"
                                    : undeclared.iterator().next()
                                    + " is undeclared")
                                    + "; the arm is asserted without it"));
                    continue;
                }
                conjuncts.add(renamed);
            }
            // A varied root's guard, and a root the arm's replay read where
            // it minted none: its literals hold at that reading (Arms).
            for (Map.Entry<String, RootMintRow> guarded
                    : arm.guardMints().entrySet()) {
                RootMintRow root = guarded.getValue();
                boolean read = corpus.rootOf(arm.sessionId(),
                        root.rootId()) == null;
                if (!read && !corpus.varied(root.rootId())) continue;
                // Named in the session that minted it: one variable per root.
                String rootVariable = variable(root.sessionId(),
                        root.symbol());
                String literal = SmtText.literal(
                        arm.guard().get(guarded.getKey()),
                        sorts.get(rootVariable));
                if (literal.isEmpty()) continue;
                conjuncts.add("(= " + rootVariable + " " + literal + ")");
            }
            // The family's own slot binds the consumer's variable; a nested
            // slot binds the forwarded symbol's variable in its own session.
            String target = arm.symbol().isEmpty()
                    || arm.symbol().equals(own) ? variable
                    : variable(arm.sessionId(), arm.symbol());
            conjuncts.add("(= " + target + " " + delivered + ")");
            if (!arm.attested()) {
                gaps.add(GapRow.of(arm.sessionId(), GapKind.UNATTESTED_ARM,
                        GapClass.DIAGNOSTIC, arm.slotId(),
                        "the producer ran concretely: this arm states what "
                                + "it delivered, not why"));
            }
            return VmTermLowering.and(conjuncts);
        }

        /** A read the flipped path's text names, at the row's sort. */
        private void read(ReadRow row) {
            bind(row, variable(row.sessionId(), row.symbol()));
        }

        /**
         * The flipped occurrence's reads another writer could have answered
         * ({@link #eligible}: more than one arm) are their own symbols, as
         * COMPOSE keeps the anchor's ({@code Composer#stateJoins},
         * {@code SmtLowering#rowSymbol}): inlined, the written value is a
         * constant no writer choice moves (hdfs-bugs-slowdisk-zero: the
         * detector turn's {@code maxSlowDisksToExclude <= 0}, the
         * reconfiguration's 0, its INITIAL 1).  The text then names each,
         * and its {@code wchoice_*} selectors bind it ({@link #bind}).  A
         * container's state, and a query of one, stays inlined (see {@link
         * #rename}); a placeholder's mint is a root's.
         */
        private void movableReads() {
            SmtLowering lowering = corpus.lowering(path.sessionId);
            if (lowering == null) return;
            for (ReadRow row : corpus.readsOn(path.sessionId,
                    path.occurrence)) {
                if (row.observedVersion() < 0L || row.symbol() == null
                        || row.symbol().isEmpty()
                        || row.mintVersion() != ReadRow.UNKNOWN_VERSION) {
                    continue;
                }
                ownReads.putIfAbsent(row.symbol(), row);
                // A container location's writes are states and its reads
                // answers of a query over one: no read of it is a writer's
                // value (solr-18413 G2: a map lookup bound to a map state).
                VmTermLowering.Sort sort =
                        JavaSmtSorts.sortOfJava(row.javaType());
                if (row.location().kind() == LocationKind.MAP
                        || sort.containerState()
                        || eligible(row).size() < 2) {
                    continue;
                }
                lowering.state(row.symbol(), sort);
            }
        }

        /**
         * The read a session's symbol names here: a session states one
         * symbol per location and version, so reads of one version by
         * several occurrences share it (hdfs-bugs-slowdisk-zero: the
         * detector's three turns each read the reconfigured bound), and in
         * the flipped occurrence's text it is that occurrence's own read.
         */
        private ReadRow readOf(String sessionId, String symbol) {
            ReadRow own = path.sessionId.equals(sessionId)
                    ? ownReads.get(symbol) : null;
            return own != null ? own : corpus.read(sessionId, symbol);
        }

        /** The writer occurrences one read could have taken its value from. */
        private List<Arms.Arm> eligible(ReadRow row) {
            List<Arms.Arm> eligible = corpus.arms().stateArms(row.endpoint(),
                    row.sessionId(), SmtLowering.locationKey(row.location()),
                    row.observedVersion(), !row.unnamedWriter());
            fileRefusals();
            return eligible;
        }

        /** Files every arm {@link Arms} refused since the last drain: an
         *  arm naming a root its session minted no row for is refused,
         *  filed as COMPOSE does ({@code ComposedFamilies#fileRefusals}). */
        private void fileRefusals() {
            for (String refusal : corpus.arms().drainRefusals()) {
                String[] named = refusal.split("\\|", -1);
                if (named.length != 3) continue;
                gaps.add(GapRow.of(named[1], GapKind.UNATTESTED_ARM,
                        GapClass.DIAGNOSTIC, named[0],
                        "an arm delivered by session " + named[1]
                                + " names root " + named[2] + " and that"
                                + " session states no RootMintRow for it, so"
                                + " the arm is refused"));
            }
        }

        /** One read joined to the writes it could have seen (IDENTITY §4); the
         *  caller chose the variable's sort. */
        private void bind(ReadRow row, String variable) {
            if (!explained.add(variable)) return;
            List<Arms.Arm> eligible = eligible(row);
            gaps.add(GapRow.of(row.sessionId(), GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, row.endpoint().toString(),
                    "eligible writers of " + row.location() + ": "
                            + eligible.size()));
            if (eligible.isEmpty()) {
                stated(row, variable);
                return;
            }
            // IDENTITY §4: a writer occurrence's writes move as a BLOCK
            // relative to this reader, so all its reads of this location share
            // one selector per writer.
            String location = SmtLowering.locationKey(row.location());
            String choiceKey = row.endpoint().occurrence().id() + "|"
                    + location;
            WriterChoice choices = choicesByReader.get(choiceKey);
            if (choices == null) {
                choices = new WriterChoice(choiceKey,
                        row.endpoint().occurrence(), row.location());
                int ordinal = 0;
                for (Arms.Arm alternative : eligible) {
                    String selector = names.name("choice|" + choiceKey + "|"
                                    + alternative.slotId(),
                            "wchoice_" + row.location().slot() + "_"
                                    + ordinal++);
                    declare(selector, "Bool", "this read takes "
                            + row.location() + " from slot "
                            + alternative.slotId());
                    choices.alternatives.add(new Choice(selector,
                            alternative));
                    choices.writes.put(selector, alternative.write());
                    if (alternative.write() != null
                            && alternative.write().version()
                            == row.observedVersion()) {
                        choices.recorded = selector;
                    }
                }
                choicesByReader.put(choiceKey, choices);
                choices.exactlyOne = assertions.size();
                assertions.add(Arms.exactlyOne(new ArrayList<String>(
                        choices.writes.keySet())));
            }
            // One writer choice binds every read of the block, so it is the
            // run only where every read saw that writer's one write.  Reads
            // that saw several writes (a nested region of the reader's own
            // thread wrote between two of them: hdfs-adhoc-23's
            // layoutVersion), or a version no row wrote, are each held to
            // their own by the run's choice ({@link #choices}), as COMPOSE's
            // observed arm holds them ({@code ComposedFamilies#stateFamilies});
            // and a writer a read of another version could not have seen is
            // no choice (hdfs-adhoc-16: updatePipeline's earlier read bound
            // to its own later write).
            boolean another = !choices.reads.isEmpty()
                    && choices.reads.get(0).observedVersion()
                    != row.observedVersion();
            choices.asHappened |= another || corpus.writeOf(row.sessionId(),
                    location, row.observedVersion()) == null;
            choices.reads.add(row);
            for (Choice choice : another ? choices.alternatives
                    : Collections.<Choice>emptyList()) {
                WriteRow write = choice.alternative.write();
                if (write != null && !corpus.arms().eligible(choices.reader,
                        row.sessionId(), location, corpus.writesOf(
                                row.sessionId(), location),
                        row.observedVersion(), write)) {
                    choices.ineligible.add(choice.selector);
                }
            }
            String sort = sorts.get(variable);
            Arms.Arm seen = null;
            String own = null;
            List<String> bindings = new ArrayList<String>();
            for (Choice choice : choices.alternatives) {
                String value = delivered(choice.alternative, sort);
                if (observes(choice.alternative, row)) {
                    seen = choice.alternative;
                    own = value;
                }
                if (value == null) {
                    if (choice.selector.equals(choices.recorded)) {
                        choices.recordedDeliversNothing = true;
                    } else {
                        assertions.add("(not " + choice.selector + ")");
                    }
                    continue;
                }
                if (value.isEmpty()) continue;
                bindings.add("(=> " + choice.selector + " (= " + variable
                        + " " + value + "))");
                if (!choice.alternative.attested()) {
                    gaps.add(GapRow.of(choice.alternative.sessionId(),
                            GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                            choice.alternative.slotId(),
                            "the writer ran concretely: this arm states what "
                                    + "it wrote, not why"));
                }
            }
            // Its observed write's delivery: among the choices, else (a read
            // of another version) among its own eligible arms.
            for (Arms.Arm arm : seen == null ? eligible
                    : Collections.<Arms.Arm>emptyList()) {
                if (observes(arm, row)) own = delivered(arm, sort);
            }
            choices.boundReads.put(variable, row);
            choices.observedDelivery.put(variable, own);
            if (bindings.isEmpty()) {
                stated(row, variable);
                return;
            }
            for (String binding : bindings) assertions.add(binding);
        }

        /** Whether this arm delivers the write the read observed. */
        private static boolean observes(Arms.Arm arm, ReadRow row) {
            return arm.write() != null
                    && arm.write().version() == row.observedVersion();
        }

        /**
         * Once every read is bound, each writer choice where no one writer's
         * arm is the run ({@link WriterChoice#asHappened}) gets COMPOSE's
         * rule ({@code ComposedFamilies#stateFamilies}): a writer a read of
         * another version could not have seen is no choice; where a writer
         * left is HB-concurrent with the reader, one more selector, the
         * RUN'S CHOICE, holds each read to the value it read and is the
         * recorded pairing (a model taking it plants nothing), beside the
         * writer choices, its exactly-one restated over all of them, and the
         * observed writer's selector, no longer the recorded one, is no
         * choice where it delivers a read a value of another sort; where
         * none is, there is no choice: each read is held to the value it
         * read, as COMPOSE's reads keep their own joins where no family
         * forms.  The value a read read is its observed write's delivery,
         * else its row's value; a read stating neither refuses the query by
         * name.
         */
        private void choices() {
            List<String> runOnly = new ArrayList<String>();
            for (WriterChoice choice : choicesByReader.values()) {
                if (!choice.asHappened) continue;
                List<String> own = new ArrayList<String>();
                for (Map.Entry<String, ReadRow> read
                        : choice.boundReads.entrySet()) {
                    String value = choice.observedDelivery.get(read.getKey());
                    if (value == null || value.isEmpty()) {
                        value = SmtText.literal(read.getValue()
                                .concreteValue(), sorts.get(read.getKey()));
                    }
                    if (value.isEmpty()) {
                        refusal = "UNSTATED_VALUE:" + choice.key;
                        gaps.add(GapRow.of(read.getValue().sessionId(),
                                GapKind.UNSTATED_VALUE, GapClass.BLOCKING,
                                choice.key, "no one writer's arm is the run "
                                        + "of these reads, and "
                                        + read.getKey() + " states no value "
                                        + "the run's choice could hold it "
                                        + "to"));
                        continue;
                    }
                    own.add("(= " + read.getKey() + " " + value + ")");
                }
                boolean alternative = false;
                for (Choice writer : choice.alternatives) {
                    alternative |= !choice.ineligible.contains(writer.selector)
                            && corpus.arms().concurrent(choice.reader,
                            writer.alternative.producer(),
                            choice.reads.get(0).sessionId());
                }
                if (!alternative) {
                    for (String selector : choice.writes.keySet()) {
                        own.add("(not " + selector + ")");
                    }
                    assertions.set(choice.exactlyOne, VmTermLowering.and(own));
                    runOnly.add(choice.key);
                    continue;
                }
                List<String> no = new ArrayList<String>(choice.ineligible);
                String run = names.name("choice|" + choice.key + "|run",
                        "wchoice_" + choice.location.slot() + "_run");
                declare(run, "Bool", "these reads take " + choice.location
                        + " each from the write it observed");
                for (String held : own) {
                    assertions.add("(=> " + run + " " + held + ")");
                }
                if (choice.recordedDeliversNothing
                        && !no.contains(choice.recorded)) {
                    no.add(choice.recorded);
                }
                for (String selector : no) {
                    assertions.add("(not " + selector + ")");
                }
                choice.writes.put(run, null);
                choice.recorded = run;
                assertions.set(choice.exactlyOne, Arms.exactlyOne(
                        new ArrayList<String>(choice.writes.keySet())));
            }
            for (String key : runOnly) choicesByReader.remove(key);
        }

        /**
         * What one eligible writer delivers, as this query spells it, or ""
         * where it does not lower; null where its write is of another sort
         * than the read (an array cell's whole array, a narrower cell): it
         * delivers nothing the read could be, named, and no model takes it.
         */
        private String delivered(Arms.Arm alternative, String sort) {
            SmtLowering.Lowered lowered =
                    corpus.lowering(alternative.sessionId())
                            .lower(alternative.expressionRef());
            if (!lowered.ok()) return "";
            if (!lowered.value().sort.smt.equals(sort)) {
                gaps.add(GapRow.of(alternative.sessionId(),
                        GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        alternative.slotId(), "ARM_SORT_MISMATCH: the arm "
                                + "delivers a " + lowered.value().sort.smt
                                + " and the read is a " + sort));
                return null;
            }
            Set<String> unknown = new LinkedHashSet<String>();
            String value = rename(lowered.text(), alternative.sessionId(),
                    unknown);
            return unknown.isEmpty() ? value : "";
        }

        /** The recorded value for a read nothing else explains, else a BLOCKING
         *  refusal. */
        private void stated(ReadRow row, String variable) {
            String literal = SmtText.literal(row.concreteValue(),
                    sorts.get(variable));
            if (!literal.isEmpty()) {
                assertions.add("(= " + variable + " " + literal + ")");
                return;
            }
            refusal = "UNSTATED_VALUE:" + row.endpoint();
            gaps.add(GapRow.of(row.sessionId(), GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, row.endpoint().toString(),
                    "the read joins no eligible write and the recording "
                            + "states no value for it"));
        }


        /** Renames one recorded term into query variables, declaring and
         *  enqueueing its symbols. */
        private String rename(String term, String sessionId,
                              Set<String> unknown) {
            lowered.add(sessionId);
            Map<String, String> rename = renamesOf(sessionId);
            // THE CLOSURE: a term's symbols are those REACHABLE through the
            // subterms it names (SmtLowering, as the closure planner asks), not
            // only visible ones.  What a container subterm RESTS ON (the
            // read rows of the state it is the value of) is the closure's
            // demand, not a variable of this query: the join inlined that
            // state's chain, so no text names the read, and a variable bound
            // to its writers' states would constrain nothing (for any choice
            // of writer the variable is that writer's state) while its
            // equalities over lambda-built states took z3 out of what it
            // decides.
            SmtLowering lowering = corpus.lowering(sessionId);
            for (String token : lowering.reachedSymbols(
                    Collections.singletonList(term))) {
                if (corpus.symbolKind(sessionId, token)
                        == Corpus.SymbolKind.UNKNOWN) {
                    continue;
                }
                rename.put(token, variable(sessionId, token));
                bound.add(sessionId + "|" + token);
            }
            return SmtNames.rename(term, rename,
                    name -> stated(name, sessionId), unknown);
        }

        @Override
        public Map<String, String> renamesOf(String sessionId) {
            Map<String, String> held = renames.get(sessionId);
            if (held == null) {
                held = new LinkedHashMap<String, String>();
                renames.put(sessionId, held);
            }
            return held;
        }

        /** The query variable one session's symbol stands for: a root is ONE
         *  variable corpus-wide (arm guards state each replay's reading), a
         *  clock one per session, a handoff one per INTERACTION (both
         *  endpoints), a state read one per read event (versions are
         *  session-local). */
        private String variable(String sessionId, String symbol) {
            switch (corpus.symbolKind(sessionId, symbol)) {
                case ROOT: {
                    RootMintRow row = corpus.rootBySymbol(sessionId, symbol);
                    boolean clock = row.kind() == RootKind.CLOCK;
                    String key = clock
                            ? "clock|" + row.rootId() + "|" + sessionId
                            : "root|" + row.rootId();
                    String name = names.name(key, (clock ? "clk_" : "r_")
                            + row.rootId() + (clock ? "_" + sessionId : ""));
                    // Recorded here for the margin rule; every name of a
                    // demanded conjunct passes through here first (see
                    // #rename).
                    if (clock) {
                        clockCells.put(name,
                                ClockMargin.margin(row.clockNanos()));
                    }
                    declare(name, row.kind() == RootKind.MARKER
                            ? "Bool" : "Int",
                            (clock ? "clock " : "root ") + row.rootId()
                                    + " recorded " + row.recordedValue());
                    enqueue(sessionId, symbol);
                    return name;
                }
                case HANDOFF: {
                    AttachRow row = corpus.attach(sessionId, symbol);
                    Interaction interaction = row.producer() == null ? null
                            : Interaction.of(InteractionKind.WIRE,
                                    row.producer(), row.endpoint());
                    String key = interaction == null
                            ? "unpaired|" + row.endpoint().id()
                            : "handoff|" + interaction.id();
                    String name = names.name(key, "vH_" + row.endpoint().site()
                            + "_" + row.endpoint().siteIndex().hash());
                    declare(name, sortOf(row.javaType(), name,
                            "handoff " + row.endpoint()),
                            "handoff " + row.endpoint() + " arrival "
                                    + row.arrival() + " : " + row.javaType());
                    enqueue(sessionId, symbol);
                    return name;
                }
                case READ: {
                    ReadRow row = readOf(sessionId, symbol);
                    String name = readVariable(sessionId, row);
                    declare(name, sortOf(row.javaType(), name,
                            "read " + row.endpoint()),
                            "read " + row.endpoint() + " of " + row.location()
                                    + " version " + row.observedVersion()
                                    + " : " + row.javaType());
                    enqueue(sessionId, symbol);
                    return name;
                }
                default:
                    return symbol;
            }
        }

        /** The one variable of a READ event the text names. */
        private String readVariable(String sessionId, ReadRow row) {
            return names.name("read|" + sessionId + "|"
                            + row.endpoint().id(),
                    "st_" + row.location().slot() + "_"
                            + row.endpoint().siteIndex().hash());
        }

        /** The sort the runtime declared a value at: {@link JavaSmtSorts} and
         *  {@link VmTermLowering.Sort#smt}, as in the composed query (a second
         *  vocabulary would refuse Ref reads). Only an unknown descriptor
         *  refuses. */
        private String sortOf(String javaType, String name, String subject) {
            VmTermLowering.Sort sort = JavaSmtSorts.sortOfJava(javaType);
            if (sort != VmTermLowering.Sort.UNKNOWN) return sort.smt;
            refusal = "UNSTATED_VALUE:" + subject;
            gaps.add(GapRow.of(path.sessionId, GapKind.UNSTATED_VALUE,
                    GapClass.BLOCKING, subject,
                    "the runtime declared " + name + " at javaType '"
                            + javaType + "', which is not a sort this query "
                            + "states"));
            return "Int";
        }

        private void declare(String name, String sort, String what) {
            sorts.put(name, sort);
            meaning.put(name, what);
        }

        private void enqueue(String sessionId, String symbol) {
            Ref ref = new Ref(sessionId, symbol);
            if (queued.add(ref.key())) pending.add(ref);
        }

        private void registerControl(AttachRow attach, String variable,
                                     boolean unproducible) {
            controls.put(attach.endpoint().id(), new Control(
                    attach.endpoint().id(), variable, sorts.get(variable),
                    unproducible));
        }

        /** A root with no window, pinned to its recorded value. */
        private void pin(String variable, String recorded, String why) {
            String literal = SmtText.literal(recorded, sorts.get(variable));
            if (literal.isEmpty()) {
                gaps.add(GapRow.of(path.sessionId, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, variable,
                        why + ", and no recorded value to pin it to"));
                return;
            }
            rootFacts.add("(= " + variable + " " + literal + ")");
        }

        /** A recorded symbol the query would declare and bind to nothing: the
         *  query must be CAUSALLY CLOSED (every symbol stated by a family or a
         *  pin), so it is refused by that symbol's name. */
        private String unbound() {
            for (String sessionId : lowered) {
                SmtLowering lowering = corpus.lowering(sessionId);
                if (lowering == null) continue;
                for (SmtLowering.Declaration declaration
                        : lowering.reachedBy(asserted())) {
                    if (!declaration.body.isEmpty()) continue;
                    if (corpus.symbolKind(sessionId, declaration.name)
                            == Corpus.SymbolKind.UNKNOWN) {
                        continue;
                    }
                    if (bound.contains(sessionId + "|" + declaration.name)) {
                        continue;
                    }
                    return declaration.name;
                }
            }
            return "";
        }

        private Built refuse(GapKind kind, String subject, String detail,
                             DecisionRow flipped) {
            return refuse(kind, GapClass.BLOCKING, path.sessionId, subject,
                    detail, flipped);
        }

        /** A refusal filed where the fact belongs: about the RECORDING, that
         *  session's and BLOCKING; about the wave's question, EXPLORATION's and
         *  DIAGNOSTIC. Either way the query is not sent. */
        private Built refuse(GapKind kind, GapClass cls, String sessionId,
                             String subject, String detail,
                             DecisionRow flipped) {
            gaps.add(GapRow.of(sessionId, kind, cls, subject, detail));
            return refused(kind.name() + ":" + subject, flipped);
        }

        /** No query, for the named reason. */
        private Built refused(String reason, DecisionRow flipped) {
            return new Built("", Collections.<String>emptyList(), reason,
                    new ArrayList<Control>(controls.values()),
                    rootVariables, clockVariables,
                    Collections.<WriterChoice>emptyList(), gaps);
        }

        /** The flipped decision's predicate, in this query's names. */
        private String flippedText = "";

        /**
         * Whether the flipped predicate reaches a variable of this query:
         * one it names, or one a definition it rests on names (the
         * declarations its text reaches, {@link
         * FlipQueryText#statedDeclarations}).
         */
        private Set<String> flipCone() {
            Set<String> cone = new LinkedHashSet<String>(
                    SmtNames.names(flippedText));
            for (String declaration : FlipQueryText.statedDeclarations(corpus,
                    lowered, this, Collections.singletonList(flippedText))) {
                cone.addAll(SmtNames.names(declaration));
            }
            return cone;
        }

        /** Whether a variable of this query is in the cone. */
        private boolean moves(Set<String> cone) {
            for (String name : cone) {
                if (sorts.containsKey(name)) return true;
            }
            return false;
        }

        /** The framed leaves ({@link SmtLowering#framedLeaves}) in the
         *  cone. */
        private Set<String> framed(Set<String> cone) {
            Set<String> found = new LinkedHashSet<String>();
            for (String sessionId : lowered) {
                SmtLowering lowering = corpus.lowering(sessionId);
                if (lowering == null) continue;
                for (String leaf : lowering.framedLeaves()) {
                    if (cone.contains(leaf)) found.add(leaf);
                }
            }
            return found;
        }

        /** Every text this query ASSERTS (assertions, root facts, stated
         *  facts): the one answer used for rendering, reached declarations and
         *  the closure check. Only the projection asks narrower ({@link
         *  #reachedVariables}). */
        private List<String> asserted() {
            List<String> texts = new ArrayList<String>(assertions);
            texts.addAll(rootFacts);
            texts.addAll(statedFacts);
            return texts;
        }

        /** What the recording states about declared names, renamed into query
         *  variables; a fact over an undeclared name is dropped with a named
         *  gap. */
        private void stateFacts() {
            List<String> texts = asserted();
            for (String sessionId : lowered) {
                SmtLowering lowering = corpus.lowering(sessionId);
                if (lowering == null) continue;
                Map<String, String> rename = renamesOf(sessionId);
                for (String fact : lowering.facts(texts)) {
                    Set<String> unknown = new LinkedHashSet<String>();
                    String renamed = SmtNames.rename(fact, rename,
                            name -> stated(name, sessionId), unknown);
                    if (!unknown.isEmpty()) {
                        gaps.add(GapRow.of(sessionId,
                                GapKind.DECLARATION_MISSING,
                                GapClass.DIAGNOSTIC, fact,
                                "this recording states a fact over "
                                        + unknown.iterator().next()
                                        + ", which this query does not "
                                        + "declare, so the fact is not "
                                        + "stated here"));
                        continue;
                    }
                    if (!statedFacts.contains(renamed)) {
                        statedFacts.add(renamed);
                    }
                }
            }
        }

    }
}
