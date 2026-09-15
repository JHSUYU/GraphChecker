package edu.uva.liftlab.graphchecker.d3.compose;

import edu.uva.liftlab.graphchecker.d3.contract.Claim;
import edu.uva.liftlab.graphchecker.d3.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.d3.contract.Family;
import edu.uva.liftlab.graphchecker.d3.contract.GapClass;
import edu.uva.liftlab.graphchecker.d3.contract.GapKind;
import edu.uva.liftlab.graphchecker.d3.contract.GapRow;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a composed, solved query supports -- and what it refuses to say.
 *
 * <p>There is no VALIDATE stage behind this (owner ruling): the composed
 * query and z3's verdicts on it ARE the deliverable, so the policy has to
 * be exact about what each verdict does and does not license.</p>
 *
 * <ul>
 *   <li><b>MARKER_FLIPPED</b> -- a declared root moved inside its declared
 *       domain reaches the fatal arm.  The polarity is what makes it a
 *       finding: ordinal 0, the run as it happened, must be unsat.</li>
 *   <li><b>CLOCK_SKEW</b> -- the fatal arm is reached with no root moved,
 *       and only because a clock cell may sit elsewhere: pinning every cell
 *       to what its session read makes it unsat.  A clock that is not
 *       necessary is a decoration, never the mechanism.</li>
 *   <li><b>MESSAGE_PAIRING_FLIPPED</b> -- a fatal-observed path of an
 *       EXPLORED session is satisfiable at the recorded roots through
 *       attested arms, while the seed session's own disjunct is not: the
 *       pairing, not a root, is what differs.</li>
 *   <li><b>RECORDED_FAILURE_EXPLAINED</b> -- the seed session observed the
 *       fatal arm and the composition reproduces it with nothing moved,
 *       every flipped valuation being decided and unsat.</li>
 *   <li><b>NO_SUPPORTED_WITNESS</b> -- everything else, including a
 *       declared occurrence no session reached.  That is an answer, not an
 *       exception.</li>
 * </ul>
 *
 * <p>Two refusals ride on top.  A formula satisfiable with every declared
 * root at its recorded value, on a session whose recording took the HEALTHY
 * arm, is the blocking alarm FORMULA_SAT_AT_RECORDED_VALUATION -- the
 * enumeration continues past it, so a polarity-decided witness is still
 * found and reported beside it.  And a witness that moves a root occurring
 * inside an UNATTESTED arm is refused: that arm has no producer path
 * condition behind it, so nothing says the delivery would survive the
 * move.</p>
 */
public final class ClaimPolicy {

    /** One valuation, and what the solver answered about it. */
    public static final class Outcome {
        private final Composer.Valuation valuation;
        private final Solver.Answer answer;
        private final Composer.Disjunct selected;

        Outcome(Composer.Valuation valuation, Solver.Answer answer,
                Composer.Disjunct selected) {
            this.valuation = valuation;
            this.answer = answer;
            this.selected = selected;
        }

        public Composer.Valuation valuation() {
            return valuation;
        }

        public Solver.Answer answer() {
            return answer;
        }

        /** The disjunct a sat model selected, or null. */
        public Composer.Disjunct selected() {
            return selected;
        }

        @Override
        public String toString() {
            return valuation + " -> " + answer.status()
                    + (selected == null ? ""
                    : " (" + selected.path().pathId() + ")");
        }
    }

    /** The claim, and every answer it was read off. */
    public static final class Decision {
        private final Claim claim;
        private final List<Outcome> outcomes;

        Decision(Claim claim, List<Outcome> outcomes) {
            this.claim = claim;
            this.outcomes = Collections.unmodifiableList(outcomes);
        }

        public Claim claim() {
            return claim;
        }

        public List<Outcome> outcomes() {
            return outcomes;
        }
    }

    private ClaimPolicy() {
    }

    /** Solves every valuation of one composition and reads the claim off. */
    public static Decision decide(Composer.Composition composition,
                                  Solver solver) {
        Decision decision = read(composition, solver);
        // AFTER the asks, over all of them: a solver error is not a verdict
        // it answered with, it is the solver saying it could not read the
        // query -- so the claim read off the other answers is a claim about
        // a formula that was never asked, and the composition refuses by
        // name instead of publishing it.
        List<String> errors = solver.errors();
        if (errors.isEmpty()) return decision;
        List<GapRow> gaps = new ArrayList<GapRow>(decision.claim().gaps());
        for (String error : errors) {
            gaps.add(GapRow.of(Composer.COMPOSITION,
                    GapKind.DECLARATION_MISSING, GapClass.BLOCKING, error,
                    "z3 answered the composed query with an error instead "
                            + "of a verdict: the lowering wrote a name or a "
                            + "literal SMT-LIB does not spell, which is a "
                            + "bug in the composition and not an answer "
                            + "about the recording"));
        }
        return new Decision(Claim.of(ClaimKind.NO_SUPPORTED_WITNESS,
                decision.claim().valuationOrdinal(),
                Collections.<String, String>emptyMap(), false, gaps),
                decision.outcomes());
    }

    private static Decision read(Composer.Composition composition,
                                 Solver solver) {
        List<GapRow> gaps = new ArrayList<GapRow>(composition.gaps());
        List<Outcome> outcomes = new ArrayList<Outcome>();
        if (composition.disjuncts().isEmpty()) {
            // The declared occurrence is the anchor, always; one no session
            // reached is a claim about the corpus, never an exception.
            return new Decision(Claim.of(ClaimKind.NO_SUPPORTED_WITNESS, 0,
                    Collections.<String, String>emptyMap(), false, gaps),
                    outcomes);
        }
        List<String> selectors = composition.selectors();
        for (Composer.Valuation valuation : composition.valuations()) {
            Solver.Answer answer = solver.ask(composition.body(),
                    valuation.assertions(), selectors,
                    valuation.ordinal() == 0);
            outcomes.add(new Outcome(valuation, answer,
                    selectedOf(composition, answer)));
        }
        Outcome recorded = outcomes.isEmpty() ? null : outcomes.get(0);

        // The alarm: the run as it happened reaches the fatal arm on a path
        // whose own recording took the healthy one.
        if (recorded != null && recorded.answer().sat()
                && recorded.selected() != null
                && !recorded.selected().fatalObserved()) {
            gaps.add(GapRow.of(recorded.selected().path().sessionId(),
                    GapKind.FORMULA_SAT_AT_RECORDED_VALUATION,
                    GapClass.BLOCKING,
                    recorded.selected().path().pathId(),
                    "this disjunct is satisfiable with every declared root "
                            + "at its recorded value, and its own recording "
                            + "took the healthy arm"));
        }

        boolean polarityDecides = recorded != null
                && recorded.answer().unsat();

        // 1. A declared root moved inside its domain.
        //
        // Polarity is a CONDITION on this claim and not a field beside it.
        // "These controls plus this rotation reach the failure" says nothing
        // unless the run as it happened does NOT reach it: a formula that is
        // satisfiable at the recorded valuation was satisfiable all along,
        // and the rotation explained nothing about the difference.
        for (Outcome outcome : outcomes) {
            if (outcome.valuation().ordinal() == 0) continue;
            if (!outcome.answer().sat() || outcome.selected() == null) {
                continue;
            }
            Set<String> refused = unattested(composition, outcome);
            if (!refused.isEmpty()) {
                gaps.add(GapRow.of(outcome.selected().path().sessionId(),
                        GapKind.UNATTESTED_ARM, GapClass.BLOCKING,
                        refused.toString(),
                        "this witness moves a root that occurs inside an "
                                + "arm no producer path condition attests, "
                                + "so it is not a supported witness"));
                continue;
            }
            if (!polarityDecides) {
                undecidedPolarity(gaps, recorded, ClaimKind.MARKER_FLIPPED);
                break;
            }
            return new Decision(Claim.of(pairing(composition, solver,
                    outcome, ClaimKind.MARKER_FLIPPED),
                    outcome.valuation().ordinal(),
                    outcome.valuation().moved(), true, gaps),
                    outcomes);
        }

        // 2. No root moves, and the clocks are necessary -- with the same
        //    polarity condition, for the same reason.
        for (Outcome outcome : outcomes) {
            if (!outcome.answer().sat() || outcome.selected() == null) {
                continue;
            }
            if (!outcome.valuation().moved().isEmpty()) continue;
            if (!clockNecessary(composition, solver, outcome)) continue;
            if (!polarityDecides) {
                undecidedPolarity(gaps, recorded, ClaimKind.CLOCK_SKEW);
                break;
            }
            return new Decision(Claim.of(pairing(composition, solver,
                    outcome, ClaimKind.CLOCK_SKEW),
                    outcome.valuation().ordinal(),
                    Collections.<String, String>emptyMap(), true,
                    gaps), outcomes);
        }

        // 3 and 4. The recorded valuation reaches the fatal arm on a path
        // that OBSERVED it -- the recording's own, or another session's.
        if (recorded != null && recorded.answer().sat()
                && recorded.selected() != null
                && recorded.selected().fatalObserved()) {
            String session = recorded.selected().path().sessionId();
            boolean seed = session.equals(composition.seedSessionId());
            if (seed && flipsRefuted(outcomes)) {
                ClaimKind kind = pairing(composition, solver, recorded,
                        ClaimKind.RECORDED_FAILURE_EXPLAINED);
                return new Decision(Claim.of(kind, 0,
                        Collections.<String, String>emptyMap(),
                        kind != ClaimKind.RECORDED_FAILURE_EXPLAINED, gaps),
                        outcomes);
            }
            if (!seed && attestedArms(composition, recorded)
                    && seedDisjunctUnsat(composition, solver)) {
                return new Decision(Claim.of(pairing(composition, solver,
                        recorded, ClaimKind.MESSAGE_PAIRING_FLIPPED), 0,
                        Collections.<String, String>emptyMap(), true, gaps),
                        outcomes);
            }
        }

        return new Decision(Claim.of(ClaimKind.NO_SUPPORTED_WITNESS,
                recorded == null ? 0 : recorded.valuation().ordinal(),
                Collections.<String, String>emptyMap(), polarityDecides,
                gaps), outcomes);
    }

    /**
     * A mechanism the formula shows and the recording does not decide.
     *
     * <p>Named rather than published as a finding: the run reached the fatal
     * arm at the recorded valuation too, so what the moved quantity explains
     * is not the difference between failing and not failing.  The alarm is
     * the same one a healthy-observed recorded-valuation model raises, and it
     * is raised here as well for a fatal-observed one, because the question
     * it asks -- "what does this witness add?" -- is the same.</p>
     */
    private static void undecidedPolarity(List<GapRow> gaps,
                                          Outcome recorded, ClaimKind kind) {
        for (GapRow gap : gaps) {
            if (gap.kind() == GapKind.FORMULA_SAT_AT_RECORDED_VALUATION) {
                return;
            }
        }
        gaps.add(GapRow.of(recorded == null || recorded.selected() == null
                        ? "composition"
                        : recorded.selected().path().sessionId(),
                GapKind.FORMULA_SAT_AT_RECORDED_VALUATION,
                GapClass.BLOCKING, kind.name(),
                "the formula shows " + kind + ", and it is satisfiable with "
                        + "every declared root at its recorded value too, so "
                        + "the recording does not decide the arm"));
    }

    /**
     * Whether this witness rests on a pairing the run did not take.
     *
     * <p>One mechanism, two kinds by the edge it is about.  Pin what the
     * selected path's own run received -- the versions its reads observed,
     * or the values its attaches arrived at -- and ask again at the same
     * valuation.  Still satisfiable means the witness works with the
     * pairing the recording had, and whatever kind it already was, it stays.
     * UNSAT means the witness needs a DIFFERENT eligible attested writer, or
     * a different producer: the pairing is the mechanism, and the kind says
     * which edge.</p>
     *
     * <p>The STATE edge is asked first because it is the narrower claim: a
     * witness that needs both is about the interleaving it needs, and the
     * wire pairing it also happens to use is not what makes it a
     * witness.</p>
     */
    private static ClaimKind pairing(Composer.Composition composition,
                                     Solver solver, Outcome outcome,
                                     ClaimKind otherwise) {
        if (outcome == null || outcome.selected() == null) return otherwise;
        String pathId = outcome.selected().path().pathId();
        if (unsatWith(composition, solver, outcome,
                composition.observedReads(pathId))) {
            return ClaimKind.STATE_PAIRING_FLIPPED;
        }
        if (unsatWith(composition, solver, outcome,
                composition.observedArrivals(pathId))) {
            return ClaimKind.MESSAGE_PAIRING_FLIPPED;
        }
        return otherwise;
    }

    /** This valuation, this disjunct, and what the run actually paired. */
    private static boolean unsatWith(Composer.Composition composition,
                                     Solver solver, Outcome outcome,
                                     List<String> observed) {
        if (observed.isEmpty()) return false;
        List<String> pinned =
                new ArrayList<String>(outcome.valuation().assertions());
        pinned.add("(assert " + outcome.selected().selector() + ")");
        pinned.addAll(observed);
        return solver.ask(composition.body(), pinned,
                Collections.<String>emptyList(), false).unsat();
    }

    /** Which disjunct a sat model selected, or null when it named none. */
    private static Composer.Disjunct selectedOf(
            Composer.Composition composition, Solver.Answer answer) {
        if (!answer.sat()) return null;
        for (Map.Entry<String, String> value : answer.values().entrySet()) {
            if (!"true".equals(value.getValue())) continue;
            Composer.Disjunct disjunct =
                    composition.bySelector(value.getKey());
            if (disjunct != null) return disjunct;
        }
        return null;
    }

    /**
     * The moved roots this witness may not move.
     *
     * <p>A root inside an arm whose producer ran concretely: the recording
     * states what that arm delivered and nothing about what it would have
     * delivered had the root been elsewhere, so a witness resting on the
     * move is resting on nothing.</p>
     */
    private static Set<String> unattested(Composer.Composition composition,
                                          Outcome outcome) {
        Set<String> refused = new LinkedHashSet<String>();
        for (String interactionId
                : outcome.selected().interactionIds()) {
            Set<String> roots =
                    composition.unattestedRoots().get(interactionId);
            if (roots == null) continue;
            for (String moved : outcome.valuation().moved().keySet()) {
                if (roots.contains(moved)) refused.add(moved);
            }
        }
        return refused;
    }

    /**
     * Whether this witness needs its clocks.
     *
     * <p>Asked the one way it can be answered: pin every clock cell to the
     * instant its session read and ask again.  Still satisfiable means the
     * clock is a decoration the model happened to move, and a claim that
     * names it would name a mechanism the formula does not need.</p>
     */
    private static boolean clockNecessary(Composer.Composition composition,
                                          Solver solver, Outcome outcome) {
        if (composition.clockCells().isEmpty()) return false;
        List<String> pinned =
                new ArrayList<String>(outcome.valuation().assertions());
        for (String cell : composition.clockCells()) {
            Long reading = composition.clockReadings().get(cell);
            if (reading == null) continue;
            pinned.add("(assert (! (= " + cell + " "
                    + JsonText.smtInteger(Long.toString(reading))
                    + ") :named clock_pinned__"
                    + JsonText.digest(cell, 10) + "))");
        }
        Solver.Answer answer = solver.ask(composition.body(), pinned,
                Collections.<String>emptyList(), false);
        return answer.unsat();
    }

    /** Whether every valuation that moved a root is decided and unsat. */
    private static boolean flipsRefuted(List<Outcome> outcomes) {
        boolean refutedOne = false;
        for (Outcome outcome : outcomes) {
            if (outcome.valuation().moved().isEmpty()) continue;
            if (!outcome.answer().decided()) return false;
            if (outcome.answer().sat()) return false;
            refutedOne = true;
        }
        return refutedOne;
    }

    /** Whether every family this disjunct reaches has an attested arm. */
    private static boolean attestedArms(Composer.Composition composition,
                                        Outcome outcome) {
        Map<String, Family> byInteraction =
                new LinkedHashMap<String, Family>();
        for (Family family : composition.families()) {
            byInteraction.put(family.interactionId(), family);
        }
        for (String interactionId : outcome.selected().interactionIds()) {
            Family family = byInteraction.get(interactionId);
            if (family == null) continue;
            boolean attested = false;
            for (int index = 0; index < family.arms().size(); index++) {
                if (family.arms().get(index).attested()) {
                    attested = true;
                    break;
                }
            }
            if (!attested) return false;
        }
        return true;
    }

    /**
     * Whether the seed session's own disjunct is unsat at the recording.
     *
     * <p>What separates "the pairing differs" from "the recording failed":
     * the recording's own path must NOT reach the fatal arm at the recorded
     * roots, or the claim is about the recording and not about a pairing.
     * A corpus with no seed session states nothing either way.</p>
     */
    private static boolean seedDisjunctUnsat(
            Composer.Composition composition, Solver solver) {
        String seed = composition.seedSessionId();
        if (seed == null) return false;
        List<String> pinned = new ArrayList<String>();
        Composer.Valuation recorded = composition.valuations().isEmpty()
                ? null : composition.valuations().get(0);
        if (recorded != null) pinned.addAll(recorded.assertions());
        boolean found = false;
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            if (!disjunct.path().sessionId().equals(seed)) continue;
            pinned.add("(assert (! " + disjunct.selector()
                    + " :named seed_disjunct__"
                    + JsonText.digest(disjunct.path().pathId(), 10) + "))");
            found = true;
        }
        if (!found) return false;
        return solver.ask(composition.body(), pinned,
                Collections.<String>emptyList(), false).unsat();
    }
}
