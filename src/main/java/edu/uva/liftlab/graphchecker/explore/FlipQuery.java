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
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.Task;

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
 * One obligation's query: the path as its replay ran it, with one decision
 * negated, over a world the corpus states.
 *
 * <p>Four rules, and nothing else, decide what a symbol of that query may be:
 *
 * <ul>
 *   <li>a ROOT is one quantity across the corpus -- free inside the domain the
 *       case declares for it, free over both values when it is a declared
 *       marker, and PINNED to what the recording read when it has no domain,
 *       because the composition pins it there too and a flip that needs it to
 *       move could never become a finding;</li>
 *   <li>a CLOCK is per path and never an equality between paths -- every
 *       execution reads it fresh -- and its domain is the one a millisecond
 *       count in a Java {@code long} has, floored at the instant the
 *       execution it belongs to READ: {@code >= that reading} AND {@code <=
 *       Long.MAX_VALUE}, because a run that lasted longer is a run and a
 *       clock turned back is not;</li>
 *   <li>a CONTROL handoff -- one attached at the occurrence this obligation
 *       flips, which is where a replay can be answered -- is bound by its
 *       family: {@code OR_q (pi_q AND guard_q AND v_H = e_q)} over the
 *       producer paths whose export endpoint is I's producer.  The walk
 *       closes over the handoffs those arms name in turn -- a producer
 *       forwards what it was handed -- to a fixed point.  A control with no
 *       arm stays free and is named {@code unproducible}.  EVERY OTHER
 *       HANDOFF IS PINNED to the arrival its own path recorded: nothing
 *       plants a value at a delivery the obligation cannot answer at, so a
 *       family there is freedom the replay does not have;</li>
 *   <li>a STATE read is joined to the write version it observed, else pinned
 *       to the value the recording states, else the obligation is refused
 *       naming it ({@code UNSTATED_VALUE}).</li>
 * </ul>
 *
 * <p>Nothing else is free.  A token of a recorded predicate that is none of
 * the above is an undeclared name: on the flipped decision it refuses the
 * obligation, on a prefix decision it drops that conjunct with a named gap,
 * because the flipped arm is the claim and the prefix is context.</p>
 *
 * <p>A DEMANDED conjunct -- this obligation's own flip and every flip the
 * path it is cut from was run under -- is asked for with a MARGIN on each
 * comparison atom that names a clock cell ({@link ClockMargin}).  A prefix
 * decision kept at the arm the recording took is not strengthened.</p>
 */
final class FlipQuery {
    private FlipQuery() {
    }

    /** One handoff of the focused occurrence the replay can be answered at. */
    static final class Control {
        final String attachEndpointId;
        final String variable;
        final boolean unproducible;

        private Control(String attachEndpointId, String variable,
                        boolean unproducible) {
            this.attachEndpointId = attachEndpointId;
            this.variable = variable;
            this.unproducible = unproducible;
        }
    }

    /** One assembled query, or the reason there is none. */
    static final class Built {
        /** The formula: declarations and assertions, without a check-sat. */
        final String smt2;
        /**
         * Every variable this query declared, in declaration order.
         *
         * <p>What a model of it must carry, asked for by name: the roots and
         * the handoff controls the outcome reads back are all among them, and
         * a solver that is handed the names it must answer about never has to
         * parse a whole model to find them.</p>
         */
        final List<String> modelSymbols;
        final String refusal;
        final DecisionRow flipped;
        final List<Control> controls;
        /**
         * query variable -> the root it stands for, for the model read-back.
         *
         * <p>Exactly the roots the query's own assertions REACH.  A model
         * assigns a value to every variable a query declares, and a root the
         * flipped path does not depend on is one the solver picked freely --
         * so carrying it into the obligation would tell a replay to plant a
         * counterfactual nothing asked for, and the replay would then owe an
         * {@code ASSIGNMENT_UNPLANTED} for a root the flip never read.  The
         * projection is {@link Builder#reached}, over the one reachability
         * ({@link SmtLowering#reachedBy}); a root's OWN window is not a
         * reason to keep it, which is why {@link Builder#rootFacts} is a
         * list of its own.</p>
         */
        final Map<String, String> rootVariables;
        /**
         * The same, for the clocks of the path this obligation is about.
         *
         * <p>Apart from {@link #rootVariables} because a clock's model is a
         * counterfactual about a SKEW: every execution reads a clock fresh,
         * so the value a model hands back is an instant of the recording's
         * window and the replay's own instant is a different one.  The focus
         * row therefore states the difference and the replay adds it to what
         * it reads.</p>
         */
        final Map<String, String> clockVariables;
        final List<GapRow> gaps;

        private Built(String smt2, List<String> modelSymbols, String refusal,
                      DecisionRow flipped,
                      List<Control> controls, Map<String, String> rootVariables,
                      Map<String, String> clockVariables,
                      List<GapRow> gaps) {
            this.smt2 = smt2;
            this.modelSymbols =
                    Collections.unmodifiableList(modelSymbols);
            this.refusal = refusal;
            this.flipped = flipped;
            this.controls = Collections.unmodifiableList(controls);
            this.rootVariables =
                    Collections.unmodifiableMap(rootVariables);
            this.clockVariables =
                    Collections.unmodifiableMap(clockVariables);
            this.gaps = Collections.unmodifiableList(gaps);
        }

        boolean ok() {
            return refusal.isEmpty();
        }
    }

    /**
     * Whether one decision is worth an obligation: its predicate has to
     * mention something exploration can move.
     *
     * <p>A decision over constants is closed by the recording -- negating it
     * asks for a world the execution does not have -- and one over a value
     * nothing declares cannot be asked for either.</p>
     */
    /**
     * Whether one recorded decision is a flip candidate at all.
     *
     * <p>Owner's ruling, 2026-09-15: a branch that carries a symbol IS a
     * flip target.  Every symbol a term can name is a declared root, a
     * handoff a family binds, or a placeholder its own row states, so
     * pre-filtering on "does it name a ROOT or a HANDOFF" refused flips over
     * state the recording states perfectly well -- and whether a flip is
     * PRODUCIBLE is the solver's verdict, not the planner's guess:
     * {@link Builder#unbound} refuses a model that would land on a symbol
     * nothing binds, by name, as UNPRODUCIBLE_ANSWER (HANDOVER SS1.5).</p>
     *
     * <p>What is left is the one thing that is not a predicate: a CONCRETE
     * branch, published with no term because the VM had no symbolic value at
     * the site.  There is nothing to negate and no valuation that could take
     * the other arm; asking anyway asserted {@code "(not )"}, which is not
     * SMT at all.</p>
     *
     * <p>Where a candidate may SIT is a different question, and the closure
     * answers it: CLOSURE-V2 SS3 restricts candidates to the guard set the
     * demand named for that occurrence
     * ({@link ObligationFactory#candidates}).  This predicate test is what
     * is left of E7's rule -- a branch that carries a symbol is flippable --
     * and it is still one rule, asked in one place.</p>
     */
    static boolean flippable(DecisionRow decision) {
        return Arms.predicate(decision.term());
    }

    /**
     * One published term with its expression REFERENCES lowered.
     *
     * <p>The runtime publishes a predicate over a propagated value as
     * {@code (not EXPR.1f3c6978d870b1bc)} -- a reference into the session's
     * expression table -- so a query that read the token as a name asked
     * about nothing and every such decision looked unflippable.  The ONE
     * lowering resolves it (compose.SmtLowering), the same routine the
     * composer runs, so a flip and the composition it is meant to satisfy
     * cannot disagree about what the predicate says.  A term with no
     * reference in it comes back as it was.</p>
     */
    static String statedTerm(Corpus corpus, String sessionId,
                             String term) {
        if (term == null || term.isEmpty()) return "";
        SmtLowering lowering = corpus.lowering(sessionId);
        if (lowering == null) return term;
        String lowered = lowering.statedTerm(term, "flip:" + sessionId);
        // A refusal leaves "": the term names a value this replay does not
        // state, and the caller's own unknown-symbol rule names it.
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
        /**
         * What the ROOT rule states about a root's own variable: the window
         * the case declared, a clock's floor, or the pin of a root with no
         * window.
         *
         * <p>A list of its own, and not one more assertion, because the
         * model PROJECTION asks which roots this query's assertions reach
         * ({@link Built#rootVariables}).  A root's window mentions the root,
         * so a query that kept the two in one list would reach every root it
         * ever declared and the projection would keep them all -- it would
         * be a rule that decides nothing.  The rendered query states both,
         * the assertions first.</p>
         */
        private final List<String> rootFacts = new ArrayList<String>();
        /**
         * query variable -> the literal the recording read it at, for the
         * Int roots and clocks this query bounds: THE NEAREST-WORLD RULE.
         *
         * <p>A domain is a window, and z3 answers with any point of it --
         * on the boundary, as a simplex does.  The formula is satisfied
         * there; the program is not held to the formula: a clock moved by
         * the whole window rotates keys the path never read and reorders
         * the loop the flipped decision sits in, so the replay takes the
         * inherited flip the other way (bug3 v18: 41 NOT_ADMITTED, no path
         * observed the fatal; v15 passed the same corpus because z3
         * happened to answer +10.9M ms rather than +30 days).  The query
         * therefore asks for the world NEAREST the recording -- minimize
         * the sum of |x - recorded| over these -- which is the smallest
         * move that still takes the other arm, with the margin.</p>
         */
        private final Map<String, String> nearest =
                new LinkedHashMap<String, String>();
        /**
         * What each session's LOWERING states about the names this query
         * declares: an identity the execution read fields off was not
         * null, an integral leaf inside its Java domain, a container
         * subterm at the shape it was built at
         * ({@link SmtLowering#facts}).
         *
         * <p>Beside {@link #rootFacts} for the same reason: a fact about a
         * name is not a reason to keep that name in a model.  And a list
         * rather than an assertion because it is not this query's claim --
         * it is what the RECORDING says about the boundary the claim rests
         * on.  Unstated, the 18 hdfs-11741 wave-0 flips over
         * {@code (= container_dag__... nullRef)} were satisfied by making
         * an object the recording saw non-null null, declaring no variable
         * at all.</p>
         */
        private final List<String> statedFacts = new ArrayList<String>();
        private final Set<String> explained = new LinkedHashSet<String>();
        private final Deque<Ref> pending = new ArrayDeque<Ref>();
        private final Set<String> queued = new LinkedHashSet<String>();
        private final Map<String, Control> controls =
                new LinkedHashMap<String, Control>();
        /** reader occurrence + location -> its one choice of writer. */
        private final Map<String, List<Choice>> choicesByReader =
                new LinkedHashMap<String, List<Choice>>();
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
        /**
         * Every CLOCK cell this query declared, by variable name.
         *
         * <p>{@link #clockVariables} is the READ-BACK map and holds only
         * the flipped path's own cells -- a skew is a counterfactual about
         * the execution the obligation is about -- while the MARGIN
         * ({@link ClockMargin}) is a fact about what the demanded atom
         * compares, whichever execution read it.  So the two are apart, and
         * this one is exactly the set {@code clockDomain} constrains.</p>
         */
        private final Set<String> clockCells = new LinkedHashSet<String>();
        private final List<GapRow> gaps = new ArrayList<GapRow>();
        private String refusal = "";

        private Builder(Corpus corpus, Task task, Corpus.RecordedPath path) {
            this.corpus = corpus;
            this.task = task;
            this.path = path;
        }

        /**
         * Whether a lowered conjunct is one this query can put in a query.
         *
         * <p>Blank, or carrying an application whose arguments are missing
         * -- {@code (not )}, {@code (and )}, {@code (= )}.  Either is a term
         * the lowering could not state, and z3 answers a query holding one
         * with {@code (error "invalid function application, arguments
         * missing")} and decides nothing at all, so the obligation is lost
         * rather than answered.</p>
         */
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
            for (int index = 0; index <= flipIndex; index++) {
                DecisionRow decision = path.decisions.get(index);
                Set<String> unknown = new LinkedHashSet<String>();
                // What a published decision ASSERTS is one routine's answer,
                // shared with the composer (Arms.conjunct: outcome ? term :
                // (not term)), so a prefix means the same thing in the flip
                // query and in the composed one.  Renaming comes after it:
                // the polarity is the recording's, the names are this
                // query's.
                boolean last = index == flipIndex;
                if (!Arms.predicate(decision.term())) {
                    // Concrete: no predicate to assert, and (by flippable)
                    // never the decision this obligation flips.
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
                // A TERM THIS QUERY CANNOT STATE IS REFUSED BY NAME, never
                // wrapped.  The guard above catches a term that NAMES
                // something undeclared; a term that is blank, or that
                // carries an application with its arguments missing, walked
                // straight past it and was negated anyway.  hdfs-11741
                // campaign #9 wave 1: 22 of 260 obligations came back
                // `the solver did not decide this flip: (error "line 68
                // column 18: invalid function application, arguments
                // missing")` over `(assert (and (not ) (not ) (= vH_... 
                // 182905)))`.  z3 rejects the whole query, so the arm is
                // thrown away -- a flip lost to a spelling, with nothing
                // said about it.
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
                // The obligation IS the complement of the arm the recording
                // took, and nothing else -- asked with room to spare where
                // it rests on a clock ({@link #demanded}).
                assertions.add(last
                        ? demanded("(not " + held + ")", decision)
                        : held);
            }
            Built refused = inheritedFlips(flipped);
            if (refused != null) return refused;
            drain();
            stateFacts();
            if (!refusal.isEmpty()) {
                return new Built("", Collections.<String>emptyList(),
                        refusal, flipped,
                        new ArrayList<Control>(controls.values()),
                        rootVariables, clockVariables, gaps);
            }
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
            // A QUERY THAT ASKS NOTHING IS NOT SENT.  `sorts` is this
            // query's own variable table -- one entry per root, clock,
            // handoff control and movable read it renamed -- and it is
            // what z3 is asked to read back ({@code modelSymbols}).  Empty,
            // the question is "is the complement of this decision
            // satisfiable" over a formula in which every name is a
            // definition or a fact the recording pins, so the answer is
            // entailed by the recording alone and no arm of it is a world
            // the corpus lacks: an unsat here would publish "no world of
            // this corpus takes the other arm" about a decision nothing
            // declared could move, and a sat would hand back a model with
            // no value in it, which is the seed replay under another name
            // (the same fact {@code recordedValuation} names after the
            // solver has run).
            //
            // 18 of the 36 wave-0 obligations of hdfs-11741 campaign #4
            // are this, all of them the receive loop's null test
            // (`addKeys#u21`), and every one was sent and answered UNSAT.
            // Their queries carry 8 to 12 declarations, all of them the
            // session lowering's own: a `container_dag__` define-fun over
            // a recorded `identity__` constant, with the session's own
            // identity fact `(not (= identity__... nullRef))` beside it.
            // So they are not a v_C or v_H question with freedom in it --
            // there is no variable at all -- and the flip is refused here
            // instead of being spent on the solver.
            if (sorts.isEmpty()) {
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
            // One walk, for both read-back maps: the roots and the clocks
            // of one query are projected by one notion of reached.
            Set<String> reached = reachedVariables();
            return new Built(FlipQueryText.render(corpus, task,
                    path, lowered, this, meaning, sorts, asserted(), nearest,
                    flipped, flipIndex),
                    new ArrayList<String>(sorts.keySet()), "", flipped,
                    new ArrayList<Control>(controls.values()),
                    reached(rootVariables, reached),
                    reached(clockVariables, reached), gaps);
        }

        /**
         * THE PARENT'S FLIPS, asserted: the world this cut path ran in.
         *
         * <p>A path of a focused session exists only inside the world its
         * own replay ran -- the flip that replay was asked for, and every
         * flip IT inherited ({@link Corpus.World}).  A child cut from that
         * path therefore states them too: for each inherited flip, the
         * parent occurrence's own prefix THROUGH the flipped decision, in
         * the session the path was cut from, lowered and renamed in that
         * session's scope exactly as this path's own prefix is.  Without
         * them the query asks for dn1's second expiry flip under no clock
         * skew at all, and the model it answers with is a world no
         * execution had.</p>
         *
         * <p>These are {@code assertions} and not facts, so the model
         * projection reaches the clocks and roots they name: what the child
         * has to be run at includes what its parent was run at.</p>
         *
         * <p>Fail closed, though an ADMITTED session cannot be any of
         * these: an occurrence the corpus does not hold, a decision the
         * session does not state at that site and ordinal, one stating the
         * other arm, or a flipped conjunct over a name nothing declares --
         * each refuses the obligation by name.  An unknown name in an
         * inherited PREFIX conjunct drops that conjunct with the same
         * DIAGNOSTIC gap a conjunct of this path's own prefix is dropped
         * with; the flipped conjunct is the claim and is never dropped.</p>
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
                // The parent's prefix THROUGH its flipped decision: what
                // that occurrence had decided by the time it took the arm
                // this path rests on.  Arms.pathCondition owns the
                // polarity, here as in the composition.
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
                        // THE INHERITED FLIP IS DEMANDED TOO.  Its conjunct
                        // stands here at the arm the parent's obligation
                        // asked for -- the session recorded it that way
                        // BECAUSE it was flipped -- so it is strengthened
                        // exactly as this query's own flip is, and the
                        // parent's prefix around it is not.
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
         * One DEMANDED conjunct, with the margin on every clock atom of it.
         *
         * <p>A demanded outcome is one the corpus does NOT hold -- this
         * obligation's own flip, or a flip the path it is cut from was run
         * under -- and a demanded comparison over a clock is asked for with
         * room to spare, because the replay does not run the instant the
         * model names: it reads its own and moves it by the skew, while the
         * quantity the guard compares against moves with it
         * ({@link ClockMargin}).  A prefix decision kept at the arm the
         * recording took is context and is never strengthened.</p>
         *
         * <p>ON THE LOWERED, RENAMED TEXT, which is the only form that has
         * the whole atom in it: the published predicate is a reference into
         * the session's expression table, its comparison is the JVM's
         * {@code lcmp} under a {@code >= 0}, and whether a term names a
         * CLOCK is a fact about the variable THIS query declared for it.
         * Every atom the margin could not be put on is named here, once,
         * as the wave's own diagnostic.</p>
         */
        private String demanded(String held, DecisionRow decision) {
            ClockMargin.Strengthened asked = ClockMargin.strengthen(held,
                    clockCells, ClockMargin.MARGIN_MS);
            for (String atom : asked.unstrengthened) {
                gaps.add(GapRow.of(ExploreCodec.EXPLORATION,
                        GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                        decision.siteId() + "#" + decision.ordinal(),
                        "the clock margin of " + ClockMargin.MARGIN_MS
                                + "ms was not put on the atom " + atom
                                + ": its polarity is not resolved by this "
                                + "query's connectives, or its operands are "
                                + "not arithmetic, so the demanded arm is "
                                + "asked for as the solver's model states "
                                + "it"));
            }
            return asked.text;
        }

        /** The one refusal an unstated inherited flip is named by. */
        private Built refuseInherited(Corpus.Flip inherited,
                                      DecisionRow flipped) {
            return refuse(GapKind.ADMISSION_GAP,
                    inherited.siteId + "#" + inherited.ordinal,
                    "the session this path was cut from states no decision "
                            + "for the flip it inherited: "
                            + inherited.render(), flipped);
        }

        /**
         * The roots of one read-back map this query's assertions REACH.
         *
         * <p>THE PROJECTION.  A query declares a variable for every symbol
         * it named on the way to the flip, and a model assigns a value to
         * every one of them; the roots the OBLIGATION assigns are the ones
         * the flipped path depends on, and nothing else.  A root the drain
         * reached through an arm this query then dropped -- the arm's
         * expression did not lower, or one of its references was undeclared
         * -- is exactly that: declared, windowed, and mentioned by no
         * assertion.  Kept, it becomes an assignment the replay is told to
         * plant at a mint the flip never read.</p>
         *
         * <p>Reachability is {@link #reachedVariables}: the one walk the
         * query's declarations are emitted with.</p>
         */
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

        /**
         * Every variable of this query the ASSERTIONS reach.
         *
         * <p>The assertions as they stand, plus the subterms they name --
         * one term reaches its leaves through the bodies of the shared
         * definitions it mentions, and those bodies are spelled in this
         * query's variables once renamed, exactly as {@link FlipQueryText}
         * emits them.  {@link #rootFacts} is not among the texts: a root's own
         * window is not a reason to keep the root.</p>
         */
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

        /**
         * One published term, lowered, and the session it was lowered in
         * remembered: the query renders that lowering's declarations, so a
         * term and the names it rests on travel together.
         */
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

        /**
         * One decision, as the arm its run took, with its references
         * lowered.
         *
         * <p>{@link Arms#conjunct} owns the polarity and nothing here
         * repeats it; the lowering owns the references and nothing here
         * repeats that either.</p>
         */
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
                        read(corpus.read(ref.sessionId, ref.symbol));
                        break;
                    default:
                        break;
                }
            }
        }

        // ---- the four rules ------------------------------------------

        private void root(RootMintRow minted) {
            String variable = variable(minted.sessionId(), minted.symbol());
            if (!explained.add(variable)) return;
            // A declared domain is RELATIVE to what the recording read, and
            // "the recording" here is the execution this obligation is about:
            // the path being flipped.  Which session's mint row reached this
            // symbol first is an accident of the drain order, and resolving
            // +0..+3 against another replay's reading would move the window
            // the case declared.
            RootMintRow own = corpus.rootOf(path.sessionId, minted.rootId());
            RootMintRow row = own == null ? minted : own;
            if (row.kind() == RootKind.CLOCK) {
                // One variable per session (see #variable), so only the
                // reading of the path being flipped is one the replay of
                // that path reads -- another session's clock is another
                // execution's instant and no replay can be held to it.
                if (minted.sessionId().equals(path.sessionId)) {
                    clockVariables.put(variable, row.rootId());
                }
                // A CLOCK CELL IS A MILLISECOND COUNT IN A JAVA long, so
                // the floor is not the whole domain: see {@link
                // JavaPrimitiveSmtSemantics#clockDomain}, which is the one
                // place that rule is spelled.  And in a FLIP QUERY the
                // floor is not 0 either: it is what this cell's own
                // execution read ({@link #clockReading}).
                // Floor AND ceiling from the same reading: the floor is
                // what this cell's execution read, the ceiling is that
                // reading plus the stated window, so a model cannot flip an
                // expiry by overflowing the JVM's own long arithmetic
                // ({@link JavaPrimitiveSmtSemantics#clockSkewCeiling}).
                String reading = clockReading(minted, row.rootId());
                rootFacts.add(JavaPrimitiveSmtSemantics.clockDomain(variable,
                        reading.isEmpty() ? "0" : reading,
                        JavaPrimitiveSmtSemantics.clockSkewCeiling(reading)));
                if (!reading.isEmpty()) nearest.put(variable, reading);
                return;
            }
            rootVariables.put(variable, row.rootId());
            if (row.kind() == RootKind.MARKER && row.declared()) return;
            String[] domain = corpus.domainOf(row);
            if (domain == null) {
                // A DECLARED window is relative to what the replay read, so
                // a mint row that states no reading leaves the case's
                // declaration unresolvable -- which is a fact about the row,
                // not "this root has no domain", and it is named as one.
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

        /**
         * The instant this cell's own execution read, or {@code ""}.
         *
         * <p>One resolution for both ends of the domain: the floor is this
         * reading and the ceiling is this reading plus the window, so a
         * reading no row states leaves BOTH where the type puts them
         * rather than flooring at 0 under a ceiling built from nothing.</p>
         */
        private String clockReading(RootMintRow minted, String rootId) {
            String reading = corpus.rootValue(minted.sessionId(), rootId);
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
            // A HANDOFF NOBODY CAN ANSWER IS PINNED TO WHAT ARRIVED.  A
            // Control is the one kind of handoff a replay can be held to:
            // the obligation's answers are applied at the focused
            // occurrence's attaches and nowhere else (the loop over {@code
            // built.controls} in {@link ObligationFactory#solve}).  Every
            // other handoff of the query is a delivery the replay will
            // receive as its own run produces it, so a family that leaves
            // it free lets the model pick ANY recorded arrival of that slot
            // and nothing plants the one it picked.  hdfs-11741 campaign #4
            // has three of those: the block-key expiry date of a
            // balance-block delivery, free over an OR of 20 recorded
            // arrivals, and z3 answered with the minimum -- 105291 to
            // 203751ms below what the replay then received, which is the
            // whole margin of the flip it was meant to satisfy.  Pinned
            // here to the arrival THIS path recorded, by the same rule an
            // arm-less nested handoff has always been pinned by.
            if (!control) {
                pinArrival(attach, variable, "a handoff of an occurrence "
                        + "this obligation cannot answer at");
                return;
            }
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
            // Only a control reaches here, so the family it is bound by is
            // one this obligation can be answered out of.
            if (!disjuncts.isEmpty()) {
                registerControl(attach, variable, false);
                return;
            }
            // A PAIRED handoff whose every arm this query dropped is
            // REFUSED, not invented.  The corpus states who sent it; an
            // answer no producer sent is a synthesized value, and a replay
            // planted with one records a world nothing attests (bug3 v20,
            // de821262b1c957b6: the SASL key id answered 0 after its one
            // arm was dropped, the key absent, the fatal observed at the
            // recorded valuation).  Only an UNPAIRED arrival -- a value
            // from outside this corpus -- is a free input the obligation
            // may answer, and it is named unproducible.
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

        /**
         * One handoff held to the value the recording states arrived.
         *
         * <p>The one pin, for the two handoffs that get it: a nested one no
         * arm of this corpus produces, and one attached where this
         * obligation cannot answer.  An arrival the query cannot spell as a
         * literal of the variable's sort pins nothing and is named -- the
         * symbol then stays unbound, and the closure check refuses the
         * obligation by its name rather than leaving it free.</p>
         */
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

        /**
         * One arm of one slot, in this query's variables.
         *
         * <p>What an arm IS -- the delivered expression, the producer path's
         * prefix cut at the delivery, the valuation its roots ran under, and
         * whether the producer was explored -- is {@link Arms}, shared with
         * the composer so one corpus states one family. What is left here is
         * the renaming: a root is one quantity across the corpus, a clock is
         * per path, and a handoff is per INTERACTION, because this query
         * conjoins several sessions' conjunctions at once where a composed
         * one selects a single path.</p>
         */
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
                // THE SAME RULE THE PREFIX IS HELD TO (#inheritedFlips, and
                // the composer's pi_p): a concrete decision -- a branch the
                // VM published no expression for, 71 of the 95 decision
                // rows of bug3's seed -- is no conjunct, and a conjunct this
                // query cannot state is dropped by name while THE ARM
                // STAYS.  The arm is the producer's delivery; its prefix is
                // context.  Wrapped, the concrete decisions were `(and
                // (not ) (not ) (= vH_... 119980))` and z3 rejected the
                // query (bug3 v15/v18: "arguments missing", NOT_ADMITTED);
                // dropping the whole ARM for them (e23a548cc) left the
                // control's slot with no family at all, z3 answered the
                // SASL key id with 0, the replay planted a key no producer
                // ever sent, and bug3 v20 observed the fatal at the
                // recorded valuation (de821262b1c957b6).
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
            for (Map.Entry<String, String> valued : arm.guard().entrySet()) {
                RootMintRow root = corpus.rootBySymbol(arm.sessionId(),
                        valued.getKey());
                if (root == null || !corpus.varied(root.rootId())) continue;
                String rootVariable = variable(arm.sessionId(),
                        valued.getKey());
                String literal = SmtText.literal(valued.getValue(),
                        sorts.get(rootVariable));
                if (literal.isEmpty()) continue;
                conjuncts.add("(= " + rootVariable + " " + literal + ")");
            }
            // The family's own slot binds the CONSUMER's variable; a nested
            // slot binds the variable of the symbol the producer forwarded,
            // which its own session minted.
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

        /** A read the flipped path's own text names, at the row's sort. */
        private void read(ReadRow row) {
            bind(row, variable(row.sessionId(), row.symbol()));
        }

        /**
         * THE v_C VARIABLE: the container state a guard reads, bound.
         *
         * <p>Behind the name and not in it -- the join inlines, so a read of
         * a container leaves one {@code container_dag__} name whose body
         * holds the mutations and nothing that names the cell
         * ({@link SmtLowering#reachedSymbols}).  It is ONE variable of this
         * query, at the sort its WRITERS deliver: a whole-state row states
         * the {@code javaType} of the reference whose state was read
         * ({@code "L"} on every MAP_STATE row of hdfs-11741), never the
         * shape of the state, and the arms are the chains the composer
         * already builds.  Declared at the row's own type instead, the
         * query asserted {@code (= st_ (assoc_put ...))} over a
         * {@code Ref} and z3 answered the whole obligation
         * {@code (error "Sorts Ref and AssocState are incompatible")}.</p>
         *
         * <p>Writers whose expressions deliver two shapes are a corpus that
         * states one state at two sorts: refused by name, never composed
         * over.</p>
         */
        private void state(String sessionId, String symbol) {
            ReadRow row = corpus.read(sessionId, symbol);
            if (row == null) return;
            List<Arms.Arm> eligible = eligible(row);
            Set<String> shapes = new LinkedHashSet<String>();
            for (Arms.Arm arm : eligible) {
                SmtLowering.Lowered delivered =
                        corpus.lowering(arm.sessionId())
                                .lower(arm.expressionRef());
                if (delivered.ok()) shapes.add(delivered.sort());
            }
            if (shapes.isEmpty()) {
                gaps.add(GapRow.of(sessionId, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, row.endpoint().toString(),
                        "no writer of " + row.location() + " delivers an "
                                + "expression this corpus lowers, so nothing "
                                + "states the shape of the state this path's "
                                + "guard reads"));
                return;
            }
            if (shapes.size() > 1) {
                refusal = "UNSTATED_VALUE:" + row.endpoint();
                gaps.add(GapRow.of(sessionId, GapKind.UNSTATED_VALUE,
                        GapClass.BLOCKING, row.endpoint().toString(),
                        "the writers of " + row.location() + " deliver this "
                                + "one state at " + shapes + ": a state has "
                                + "one shape, and nothing is composed over a "
                                + "corpus that states two"));
                return;
            }
            String variable = readVariable(sessionId, row);
            if (explained.contains(variable)) return;
            declare(variable, shapes.iterator().next(),
                    "container state " + row.location() + " read at "
                            + row.endpoint() + " version "
                            + row.observedVersion());
            bind(row, variable);
        }

        /** The writer occurrences one read could have taken its value from. */
        private List<Arms.Arm> eligible(ReadRow row) {
            List<Arms.Arm> eligible = corpus.arms().stateArms(row.endpoint(),
                    row.sessionId(), SmtLowering.locationKey(row.location()),
                    row.observedVersion());
            fileRefusals();
            return eligible;
        }

        /**
         * Every arm {@link Arms} refused since the last drain (R4 item 3).
         *
         * <p>An arm whose delivered expression names a declared root the
         * delivering session states no {@code RootMintRow} for is refused
         * rather than emitted unguarded, and the stage that asked for the
         * arms is the stage that files the refusal -- the same rule and the
         * same kind COMPOSE files ({@code ComposedFamilies#fileRefusals}).
         * </p>
         */
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

        /**
         * One read, joined to the writes it could have seen (R-I7.1).
         *
         * <p>What the variable IS has already been decided by the caller --
         * the row's own sort for a read the text names, the writers' shape
         * for a v_C state -- and this is the one binding either gets.</p>
         */
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
            // R-I7.1: a writer occurrence's writes move as a BLOCK relative
            // to this reader, and every read of this location inside this
            // occurrence takes the same choice.  One selector per writer
            // occurrence, shared by those reads, is what says so.
            String choiceKey = row.endpoint().occurrence().id() + "|"
                    + SmtLowering.locationKey(row.location());
            List<Choice> choices = choicesByReader.get(choiceKey);
            if (choices == null) {
                choices = new ArrayList<Choice>();
                int ordinal = 0;
                for (Arms.Arm alternative : eligible) {
                    String selector = names.name("choice|" + choiceKey + "|"
                                    + alternative.slotId(),
                            "wchoice_" + row.location().slot() + "_"
                                    + ordinal++);
                    declare(selector, "Bool", "this read takes "
                            + row.location() + " from slot "
                            + alternative.slotId());
                    choices.add(new Choice(selector, alternative));
                }
                choicesByReader.put(choiceKey, choices);
                assertions.add(exactlyOne(choices));
            }
            List<String> bindings = new ArrayList<String>();
            for (Choice choice : choices) {
                String value = delivered(choice.alternative);
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
            if (bindings.isEmpty()) {
                stated(row, variable);
                return;
            }
            for (String binding : bindings) assertions.add(binding);
        }

        /** What one eligible writer delivers, as this query spells it. */
        private String delivered(Arms.Arm alternative) {
            SmtLowering.Lowered lowered =
                    corpus.lowering(alternative.sessionId())
                            .lower(alternative.expressionRef());
            if (!lowered.ok()) return "";
            Set<String> unknown = new LinkedHashSet<String>();
            String value = rename(lowered.text(), alternative.sessionId(),
                    unknown);
            return unknown.isEmpty() ? value : "";
        }

        /** The value the recording states for a read nothing else explains. */
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

        /** Exactly one of the eligible writers delivered this location. */
        private static String exactlyOne(List<Choice> choices) {
            List<String> selectors = new ArrayList<String>();
            for (Choice choice : choices) selectors.add(choice.selector);
            return Arms.exactlyOne(selectors);
        }

        // ---- naming --------------------------------------------------

        /**
         * Renames one recorded term into the query's variables, declaring and
         * enqueueing every symbol it names.
         */
        private String rename(String term, String sessionId,
                              Set<String> unknown) {
            lowered.add(sessionId);
            Map<String, String> rename = renamesOf(sessionId);
            // THE CLOSURE: the recorded symbols of a term are the ones
            // reachable from it, not the ones visible in it.  A lowered term
            // reaches its leaves through the subterms it names, so a handoff
            // inside a shared define-fun is a symbol of this term -- and
            // binding it is what gives the query an arm, the obligation an
            // answer, and the replay something to apply.  One answer, in
            // SmtLowering, which the closure planner asks too.
            SmtLowering lowering = corpus.lowering(sessionId);
            Set<String> states = new LinkedHashSet<String>();
            for (String token : lowering.reachedSymbols(term,
                    new LinkedHashSet<String>(), states)) {
                if (corpus.symbolKind(sessionId, token)
                        == Corpus.SymbolKind.UNKNOWN) {
                    continue;
                }
                rename.put(token, variable(sessionId, token));
                bound.add(sessionId + "|" + token);
            }
            // THE v_C RULE (CLOSURE-V2, X12's other half): the container
            // STATE a guard reads is behind the name and not in it -- the
            // join inlines, so a read of a map leaves one
            // container_dag__ name whose body holds the mutations and
            // nothing that names the cell.  That state is one variable of
            // this query, bound by the same READ rule every other read is
            // bound by: its writer occurrences are its arms, its recorded
            // value is its pin.  It is not RENAMED into the term -- the
            // text does not mention it -- so it is enqueued and nothing
            // more; what the term says and what it rests on are two facts
            // (SmtLowering#reachedSymbols).
            for (String symbol : states) {
                if (corpus.symbolKind(sessionId, symbol)
                        != Corpus.SymbolKind.READ) {
                    continue;
                }
                lowered.add(sessionId);
                bound.add(sessionId + "|" + symbol);
                state(sessionId, symbol);
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

        /** The names one text reaches through the subterms it mentions. */
        /**
         * The query variable one session's symbol stands for.
         *
         * <p>A root is ONE variable across the corpus, because a root is one
         * quantity and a family arm's guard is what states each replay's own
         * reading of it.  A clock is one variable per session, because every
         * execution reads it fresh.  A handoff is one variable per
         * INTERACTION -- both endpoints -- so two producers of the same port
         * are two variables and never one.  A state read is one variable per
         * read event, because a version id is a session-local name.</p>
         */
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
                    // Named where the variable is: the margin rule asks
                    // which of this query's names are clock cells, and by
                    // the time a demanded conjunct is asserted every name
                    // in it has been through here (see #rename).
                    if (clock) clockCells.add(name);
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
                    ReadRow row = corpus.read(sessionId, symbol);
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

        /**
         * The variable one READ event stands at, named once.
         *
         * <p>One variable per read EVENT, because a version id is a
         * session-local name -- and one spelling of that name, because the
         * event has two rules that may reach it: the text of the flipped
         * path names it, or a container subterm of that text RESTS on it
         * (the v_C rule).  Two spellings would be two variables for one
         * read.</p>
         */
        private String readVariable(String sessionId, ReadRow row) {
            return names.name("read|" + sessionId + "|"
                            + row.endpoint().id(),
                    "st_" + row.location().slot() + "_"
                            + row.endpoint().siteIndex().hash());
        }

        /**
         * The sort the runtime declared one value at.
         *
         * <p>{@link JavaSmtSorts} is the one Java-type vocabulary and
         * {@link VmTermLowering.Sort#smt} its one spelling, so a boxed
         * Integer is Int here exactly as it is in the composed query, and a
         * reference is Ref because the preamble this query renders declares
         * that sort.  The allowlist this replaced stated a SECOND
         * vocabulary -- Int and Bool and nothing else -- so a read the
         * composer declares at {@code Ref} refused the whole obligation
         * here.  Only the sentinel is a refusal: no Java sort is known for
         * the descriptor, so there is no variable to declare.  What a
         * recorded VALUE of that sort can be pinned to is a separate
         * question, asked where the pin is ({@link SmtText#literal}).</p>
         */
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
                    attach.endpoint().id(), variable, unproducible));
        }

        /** A root with no window, held to what the recording read. */
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

        /**
         * A RECORDED symbol the query would declare and bind to nothing.
         *
         * <p>The query has to be CAUSALLY CLOSED: every recorded symbol it
         * names is stated by a family (some producer delivered it) or by a
         * pin (the recording states it).  One left over is a value the
         * chain does not reach, and a model that assigns it has answered a
         * question the execution never asked -- which is the one thing a
         * query of this pipeline may not do.  It is refused by that
         * symbol's name; nothing here is about reproducing anything.</p>
         */
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

        /**
         * The same refusal, filed where the fact belongs.
         *
         * <p>A refusal about the RECORDING -- a flipped predicate naming
         * something no row declares, a symbol the chain does not reach --
         * is that session's, and blocking.  A refusal about THE QUESTION
         * THIS WAVE ASKED is the wave's, and diagnostic: no execution went
         * wrong, the wave offered a flip that is not an obligation.  Both
         * end the build the same way, with the refusal in {@code Built}, so
         * the query is not sent.</p>
         */
        private Built refuse(GapKind kind, GapClass cls, String sessionId,
                             String subject, String detail,
                             DecisionRow flipped) {
            gaps.add(GapRow.of(sessionId, kind, cls, subject, detail));
            return new Built("", Collections.<String>emptyList(),
                    kind.name() + ":" + subject, flipped,
                    new ArrayList<Control>(controls.values()), rootVariables,
                    clockVariables, gaps);
        }

        /**
         * Every text this query ASSERTS: the path as it ran with one
         * decision negated, and what the root rule states about the roots
         * that path reached.
         *
         * <p>One list, so that "what does this query say" has one answer --
         * the rendered assertions, the declarations they reach, and the
         * closure check are all over it.  Only the model projection asks
         * the narrower question ({@link #reachedVariables}).</p>
         */
        private List<String> asserted() {
            List<String> texts = new ArrayList<String>(assertions);
            texts.addAll(rootFacts);
            texts.addAll(statedFacts);
            return texts;
        }

        /**
         * What the recording states about the names this query declares.
         *
         * <p>Asked of each session's lowering, over the texts this query
         * asserts, and RENAMED: a fact about a recorded symbol is a fact
         * about the variable the query gave it.  A fact the rename leaves
         * an unknown name in is about a name this query does not state, so
         * it is not this query's fact -- and it is named as a gap, because
         * a constraint dropped in silence is how the identity became free
         * in the first place.</p>
         */
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
