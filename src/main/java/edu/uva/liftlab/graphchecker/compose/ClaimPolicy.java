package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.explore.ClockMargin;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Z3;

import edu.uva.liftlab.graphchecker.contract.Arm;
import edu.uva.liftlab.graphchecker.contract.Claim;
import edu.uva.liftlab.graphchecker.contract.ClaimKind;
import edu.uva.liftlab.graphchecker.contract.Family;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.function.Function;

import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.integralLiteral;

/**
 * What a composed, solved query supports, and what it refuses to say.
 *
 * <p>There is no VALIDATE stage: the query and z3's verdicts ARE the
 * deliverable, so each claim kind states exactly what licenses it.</p>
 *
 * <ul>
 *   <li><b>MARKER_FLIPPED</b> -- a declared root moved inside its domain
 *       reaches the fatal arm, and ordinal 0 (the run as it happened) is
 *       unsat.</li>
 *   <li><b>CLOCK_SKEW</b> -- no declared root moved; pinning every clock
 *       cell to its recorded reading makes the query unsat.  The witness is
 *       asked with every clock running on wherever it can
 *       ({@link #leastClocks}), so {@link Claim#movedRoots}
 *       ({@link #movedRoots}) names only the jumps it needs.  A moved
 *       marker is asked first ({@link #mechanism}); where the clock pins
 *       refute the recorded valuation, a moved root must reach the fatal
 *       arm under those same pins.</li>
 *   <li><b>MESSAGE_PAIRING_FLIPPED</b> -- an explored session's fatal path
 *       is sat at the recorded roots through attested arms while the seed's
 *       own disjunct is not.</li>
 *   <li><b>FORMULA_SAT</b> -- a valuation satisfies the formula and none of
 *       the above names why: composer imprecision until CONFIRM says
 *       otherwise, confirmed like any claim ({@link #formulaSat}).</li>
 *   <li><b>NO_SUPPORTED_WITNESS</b> -- every valuation unsat, or an
 *       occurrence no session reached; an answer, not an exception.</li>
 * </ul>
 *
 * <p>The run as recorded is no counterfactual (owner 2026-10-04: a claim
 * moving no root is never a finding): a seed replay that observed the fatal
 * at the declared occurrence leaves no claim on the corpus, SEED_OBSERVED_FATAL
 * BLOCKING ({@link #unasked}), and a witness that is the run as recorded is
 * never FORMULA_SAT's while another moves something ({@link #asRecorded}).</p>
 *
 * <p>Two names ride on top: a formula sat as the run happened (recorded
 * roots, clocks and pairings) on a session that took the HEALTHY arm raises
 * FORMULA_SAT_AT_RECORDED_VALUATION, and enumeration continues past it; a
 * witness moving a root inside an UNATTESTED arm is not a mechanism, since
 * no producer path condition says the delivery survives the move.  Either
 * leaves a FORMULA_SAT for CONFIRM, never a gap that withholds a verdict.  A
 * witness moving configuration only is claimed after every other, clocks
 * and pairings included, and one moving a configuration whose plant leaves
 * reads of its key at the recording's value is not claimed, named.</p>
 */
public final class ClaimPolicy {

    /** One valuation, and what the solver answered about it. */
    public static final class Outcome {
        private final Composer.Valuation valuation;
        private final List<String> pinned;
        private final Z3.Answer answer;
        private final Composer.Disjunct selected;
        private final Map<String, ComposedFamilies.ArmChoice> arms;

        Outcome(Composer.Valuation valuation, List<String> pinned,
                Z3.Answer answer, Composer.Disjunct selected,
                Map<String, ComposedFamilies.ArmChoice> arms) {
            this.valuation = valuation;
            this.pinned = Collections.unmodifiableList(pinned);
            this.answer = answer;
            this.selected = selected;
            this.arms = Collections.unmodifiableMap(arms);
        }

        /**
         * What this model was asked with held at the recording beside the
         * valuation: unneeded clock cells ({@link #leastClocks}) and, where
         * the recording decides the arm, every path's own pairing.
         */
        public List<String> pinned() {
            return pinned;
        }

        /**
         * Arm selector -> the delivery this model rested on; only families
         * the selected path opened have an entry (exactly-one per family).
         */
        public Map<String, ComposedFamilies.ArmChoice> selectedArms() {
            return arms;
        }

        public Composer.Valuation valuation() {
            return valuation;
        }

        public Z3.Answer answer() {
            return answer;
        }

        /** The disjunct a sat model selected, or null. */
        public Composer.Disjunct selected() {
            return selected;
        }

        /** Whether the model is sat and names the disjunct it selected. */
        boolean witness() {
            return answer.sat() && selected != null;
        }

        @Override
        public String toString() {
            return valuation + " -> " + answer.status()
                    + (selected == null ? ""
                    : " (" + selected.path().pathId + ")");
        }
    }

    /** The claim, every answer it was read off, and the formula's own. */
    public static final class Decision {
        private final Claim claim;
        private final List<Outcome> outcomes;
        private final Z3.Answer formula;

        Decision(Claim claim, List<Outcome> outcomes) {
            this(claim, outcomes, null);
        }

        Decision(Claim claim, List<Outcome> outcomes, Z3.Answer formula) {
            this.claim = claim;
            this.outcomes = Collections.unmodifiableList(outcomes);
            this.formula = formula;
        }

        public Claim claim() {
            return claim;
        }

        public List<Outcome> outcomes() {
            return outcomes;
        }

        /**
         * z3's answer for the composed formula itself, every root free over
         * its domain (the exported candidate.smt2), or null where a named
         * claim's witness decided without it ({@link #closed}).
         */
        public Z3.Answer formula() {
            return formula;
        }
    }

    private ClaimPolicy() {
    }

    /** Solves every valuation of one composition and reads the claim off. */
    public static Decision decide(Composer.Composition composition,
                                  Z3 solver) {
        Decision decision;
        try (Disjunction asks = new Disjunction(composition, solver)) {
            decision = closed(composition, asks, read(composition, asks));
        }
        // After every ask: a solver error means some query was never read,
        // so the claim over it is refused by name.
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
                decision.outcomes(), decision.formula());
    }

    /**
     * THE FORMULA DECIDES (owner 2026-10-04: "拼出.smt。结果肯定不是sat就是
     * Unsat"): a named claim stands on its witness; otherwise the composed
     * formula is asked whole, every root free over its domain -- the text
     * COMPOSE exports as candidate.smt2 -- and its answer is the verdict.
     * Unsat closes the claim negative, whatever the enumeration of single
     * and pair moves reached (it only picks a witness's valuation);
     * undecided within the budget is a defect (BLOCKING), never a
     * refutation.  Sat is FORMULA_SAT: at the first enumerated witness a
     * replay can plant, else at the formula's own model ({@link
     * Composer.Composition#modelValuation}), which CONFIRM plants and judges
     * like any other (over-approximate, confirm strictly); an enumerated
     * witness that is the run as recorded is skipped ({@link #asRecorded}),
     * and a corpus a BLOCKING gap already withholds a verdict from names no
     * witness; the witness is refined as a named claim's is ({@link
     * #leastClocks}, {@link #withMargin}).  A sat model that
     * selects no disjunct is a defect, and so is a formula satisfiable only
     * by moving a configuration whose plant leaves reads of its key at the
     * recording's value ({@link #unplanted}): a world no replay can plant
     * (UNPRODUCIBLE_ANSWER) until those reads are planted too.
     */
    private static Decision closed(Composer.Composition composition,
                                   Disjunction asks, Decision decided) {
        Claim claim = decided.claim();
        if (claim.kind() != ClaimKind.NO_SUPPORTED_WITNESS
                || composition.disjuncts().isEmpty()) {
            return decided;
        }
        List<GapRow> gaps = new ArrayList<GapRow>(claim.gaps());
        List<Outcome> outcomes = new ArrayList<Outcome>(decided.outcomes());
        // An unsat may rest on a model the formula excludes, refuted or
        // refused: the core names it (restsOnRefutations), so it is asked
        // for whenever one is asserted.
        Outcome free = outcome(composition, asks,
                composition.free(outcomes.size()),
                Collections.<String>emptyList(),
                composition.assertsRefutations());
        Z3.Answer formula = free.answer();
        if (formula.unsat()) {
            contradictions(composition, asks, gaps);
            return new Decision(claimWith(claim, gaps), outcomes, formula);
        }
        if (!formula.decided()) {
            String reason = formula.reason();
            gaps.add(GapRow.of(Composer.COMPOSITION,
                    GapKind.DECLARATION_MISSING, GapClass.BLOCKING,
                    "formula:" + formula.status(), "z3 did not decide the "
                            + "composed formula, every root free over its "
                            + "domain, within its budget, so neither a "
                            + "witness nor a refutation is closed over it: "
                            + (reason.isEmpty() ? "it stated no reason"
                            : reason)));
            return new Decision(claimWith(claim, gaps), outcomes, formula);
        }
        // A corpus a defect already withholds a verdict from names no
        // witness: the formula's answer is stated, and nothing stands on it.
        if (claim.blocked()) {
            return new Decision(claimWith(claim, gaps), outcomes, formula);
        }
        Set<String> unplantable = new LinkedHashSet<String>();
        Outcome witness = null;
        for (Outcome outcome : outcomes) {
            if (!outcome.witness() || asRecorded(composition, outcome)) {
                continue;
            }
            if (plantable(composition, outcome, unplantable)) {
                witness = outcome;
                break;
            }
        }
        if (witness == null && free.witness()) {
            Outcome modelled = new Outcome(composition.modelValuation(
                    outcomes.size(), formula.values()),
                    Collections.<String>emptyList(), formula,
                    free.selected(), free.selectedArms());
            if (plantable(composition, modelled, unplantable)) {
                outcomes.add(modelled);
                witness = modelled;
            }
        }
        if (witness == null) {
            gaps.add(unplantable.isEmpty()
                    ? GapRow.of(Composer.COMPOSITION,
                    GapKind.ADMISSION_GAP, GapClass.BLOCKING,
                    composition.anchor().render(), "the composed formula is "
                            + "satisfiable and its model selects no path, "
                            + "so no witness is named and no refutation "
                            + "closed")
                    : GapRow.of(Composer.COMPOSITION,
                    GapKind.UNPRODUCIBLE_ANSWER, GapClass.BLOCKING,
                    composition.anchor().render(), "the formula is "
                            + "satisfiable only by moving configuration "
                            + unplantable + " whose plant leaves reads of "
                            + "its key at the recording's value, a world no "
                            + "replay can plant: a defect until those reads "
                            + "are planted"));
            return new Decision(claimWith(claim, gaps), outcomes, formula);
        }
        // Published as a named claim is: under every clock pin it can keep,
        // each jump it still makes moved with room.
        Outcome refined = withMargin(composition, asks, leastClocks(
                composition, asks, witness, composition.clockCells(), false,
                gaps), gaps);
        outcomes.set(outcomes.indexOf(witness), refined);
        return new Decision(Claim.of(ClaimKind.FORMULA_SAT,
                refined.valuation().ordinal(),
                movedRoots(composition, refined), claim.polarityDecides(),
                gaps), outcomes, formula);
    }

    /**
     * Whether this witness is the run as recorded: the seed's own path, no
     * root moved, no clock jumped ({@link #movedRoots}), no arm but its own
     * run's pairings ({@code Composition#repaired}).  No counterfactual, so
     * never FORMULA_SAT's witness while another moves something; the
     * formula's own model may still be one, which CONFIRM refuses by name
     * and the campaign then excludes ({@code compose.Refutations}).
     */
    private static boolean asRecorded(Composer.Composition composition,
                                      Outcome outcome) {
        return outcome.selected().path().sessionId.equals(
                composition.seedSessionId())
                && movedRoots(composition, outcome).isEmpty()
                && composition.repaired(outcome.selected().selector(),
                outcome.selectedArms().keySet()).isEmpty();
    }

    /** Whether a replay can plant this witness's valuation; a root it
     *  cannot is added to {@code unplantable}. */
    private static boolean plantable(Composer.Composition composition,
                                     Outcome outcome,
                                     Set<String> unplantable) {
        Set<String> partial = composition.unplanted(
                outcome.valuation().moved().keySet()).keySet();
        unplantable.addAll(partial);
        return partial.isEmpty();
    }

    /** The same claim with these gaps. */
    private static Claim claimWith(Claim claim, List<GapRow> gaps) {
        return Claim.of(claim.kind(), claim.valuationOrdinal(),
                claim.movedRoots(), claim.polarityDecides(), gaps);
    }

    /**
     * The claim the solved valuations support: first every answer the claim
     * is read off ({@link Reading}), then the claim, narrowest evidence
     * first -- a moved root (1), no moved root but the clocks or a pairing
     * (2), a moved configuration only, ranked after both, and another
     * session's path that observed the fatal at the recorded roots (3) --
     * else no supported witness.
     */
    private static Decision read(Composer.Composition composition,
                                 Disjunction asks) {
        List<GapRow> gaps = new ArrayList<GapRow>(composition.gaps());
        Decision unasked = unasked(composition, gaps);
        if (unasked != null) return unasked;
        Reading reading = new Reading(composition, asks, gaps);
        Decision claimed = reading.movedRoot(false);
        if (claimed == null) claimed = reading.clockOrPairing();
        if (claimed == null) claimed = reading.movedRoot(true);
        if (claimed == null) claimed = reading.observedElsewhere();
        return claimed != null ? claimed : reading.noWitness();
    }

    /**
     * The claim of a corpus no valuation is asked of, or null: none where no
     * session reached the occurrence, and none where the seed replay
     * observed the fatal at the declared occurrence -- the run as recorded
     * is no counterfactual, so nothing composed over this corpus is a claim
     * (the recording itself threw there, PLAN's TARGET_FATAL_IN_RECORDING,
     * a declaration defect, or the replay diverged from it).
     */
    private static Decision unasked(Composer.Composition composition,
                                    List<GapRow> gaps) {
        if (composition.disjuncts().isEmpty()) return none(gaps);
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            if (!disjunct.fatalObserved() || !disjunct.path().sessionId
                    .equals(composition.seedSessionId())) {
                continue;
            }
            gaps.add(GapRow.of(disjunct.path().sessionId,
                    GapKind.SEED_OBSERVED_FATAL, GapClass.BLOCKING,
                    composition.anchor().render(), "the seed replay "
                            + "observed the fatal at the declared occurrence "
                            + "(path " + disjunct.path().pathId + "): the run "
                            + "as recorded is no counterfactual, so no claim "
                            + "stands on this corpus -- the replay diverged "
                            + "from its recording, or, where PLAN names "
                            + "TARGET_FATAL_IN_RECORDING, the case declares "
                            + "an occurrence that throws as recorded"));
            return none(gaps);
        }
        return null;
    }

    private static Decision none(List<GapRow> gaps) {
        return new Decision(Claim.of(ClaimKind.NO_SUPPORTED_WITNESS, 0,
                Collections.<String, String>emptyMap(), false, gaps),
                new ArrayList<Outcome>());
    }

    /**
     * Every answer one composition's claim is read off, asked once in this
     * order: each path alone with every root free (a self-contradictory
     * path is refuted for every question after it), each valuation, then the
     * run as it happened -- every clock pinned to its reading and every path
     * to its own pairing ({@code Composition#recordedPairings}), which no
     * valuation pins -- and, where that refutes a free witness, the clocks
     * alone, which tells whether they decide it (CLOCK_SKEW).
     */
    private static final class Reading {
        private final Composer.Composition composition;
        private final Disjunction asks;
        private final List<GapRow> gaps;
        private final List<Outcome> outcomes;
        private final List<String> cells;
        /** Every clock at its reading and every path at its own pairing. */
        private final List<String> asHappened;
        /** The free witness of the recorded valuation, asked as happened. */
        private final Outcome asRecorded;
        /** The run as it happened refutes the recorded valuation's
         *  witness: a moved root must reach the fatal arm held so. */
        private final boolean recordingDecides;
        /** The clock pins alone refute it. */
        private final boolean clockDriven;
        /** The recorded valuation's refutation names a valuation pin; else
         *  the path refuted itself under every valuation. */
        private final boolean polarityDecides;
        private Outcome recorded;
        /** Configuration roots a witness's plant cannot reach, named. */
        private final Set<String> partial = new LinkedHashSet<String>();

        Reading(Composer.Composition composition, Disjunction asks,
                List<GapRow> gaps) {
            this.composition = composition;
            this.asks = asks;
            this.gaps = gaps;
            selfContradictory(composition, asks, gaps);
            outcomes = new ArrayList<Outcome>(inParallel(
                    composition.valuations(), valuation -> outcome(
                            composition, asks, valuation,
                            Collections.<String>emptyList(),
                            valuation.ordinal() == 0)));
            for (Outcome outcome : outcomes) {
                if (!outcome.answer().decided()) undecided(outcome, gaps);
            }
            recorded = outcomes.isEmpty() ? null : outcomes.get(0);
            cells = composition.clockCells();
            asHappened = new ArrayList<String>(pins(composition, cells));
            asHappened.addAll(composition.recordedPairings());
            asRecorded = recorded != null && recorded.witness()
                    && !asHappened.isEmpty()
                    ? outcome(composition, asks, recorded.valuation(),
                            asHappened, false) : null;
            recordingDecides = asRecorded != null
                    && asRecorded.answer().unsat();
            clockDriven = recordingDecides && !cells.isEmpty()
                    && outcome(composition, asks, recorded.valuation(),
                            pins(composition, cells), false).answer()
                            .unsat();
            if (clockDriven) {
                recorded = leastClocks(composition, asks, recorded, cells,
                        true, gaps);
                outcomes.set(0, recorded);
            }
            if (recorded != null && recorded.witness()
                    && !recorded.selected().fatalObserved()
                    && !recordingDecides) {
                gaps.add(GapRow.of(recorded.selected().path().sessionId,
                        GapKind.FORMULA_SAT_AT_RECORDED_VALUATION,
                        GapClass.DIAGNOSTIC,
                        recorded.selected().path().pathId,
                        "this disjunct is satisfiable with every declared "
                                + "root at its recorded value, and its own "
                                + "recording took the healthy arm"));
            }
            polarityDecides = recorded != null
                    && recorded.answer().unsat()
                    && namesAValuation(recorded.answer().core());
        }

        /** An undecided valuation is named: no witness there.  The verdict
         *  is the formula's own answer ({@link #closed}). */
        private static void undecided(Outcome outcome, List<GapRow> gaps) {
            String reason = outcome.answer().reason();
            gaps.add(GapRow.of(Composer.COMPOSITION,
                    GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    "valuation " + outcome.valuation().ordinal() + ":"
                            + outcome.answer().status(),
                    "z3 did not decide this valuation"
                            + (outcome.valuation().moved().isEmpty() ? ""
                            : " (moved " + outcome.valuation().moved() + ")")
                            + ", so neither a witness nor a refutation is "
                            + "closed over it: "
                            + (reason.isEmpty()
                            ? "it stated no reason" : reason)));
        }

        /**
         * 1. A declared root moved inside its domain, of this pass's rank: a
         * witness moving configuration only ranks after every other, the
         * clocks and pairings of 2 included ({@code
         * Composer#configurationOnly}).  Within a rank, a witness that is
         * its selected session's own run ({@link #ownRun}) is claimed
         * first, then the rest in the valuations' order: the order of the
         * single moves says nothing of which one a run already reached
         * (hdfs-adhoc-10 SL1: a fault ranked first in the root order was
         * claimed through a writer arm re-paired from another session,
         * which no run can realize, while the SYNC fault its own session
         * had run waited thirteen valuations behind it).  Polarity (ordinal
         * 0 unsat) is a CONDITION on the claim; when the recording decides
         * the arm, a moved root must reach the fatal arm with clocks and
         * pairings held as recorded, so neither is part of the witness.
         */
        Decision movedRoot(boolean configuration) {
            Decision own = recordingDecides
                    ? movedAsHappened(configuration, true)
                    : movedFree(configuration, true);
            if (own != null) return own;
            return recordingDecides ? movedAsHappened(configuration, false)
                    : movedFree(configuration, false);
        }

        /**
         * Each valuation asked or refined for this rank once ({@link
         * #movedRoot}'s two passes): its outcome, and the gaps doing so
         * named, which join the claim's only once the pass that claims or
         * reaches it keeps them.
         */
        private final Map<Integer, Outcome> settled =
                new LinkedHashMap<Integer, Outcome>();
        private final Map<Integer, List<GapRow>> settledGaps =
                new LinkedHashMap<Integer, List<GapRow>>();

        /** {@code found} asked as happened, or refined (leastClocks,
         *  margins), once. */
        private Outcome settle(int index, Outcome found) {
            Outcome done = settled.get(index);
            if (done != null) return done;
            List<GapRow> named = new ArrayList<GapRow>();
            done = recordingDecides
                    ? outcome(composition, asks, found.valuation(),
                    asHappened, false)
                    : withMargin(composition, asks, leastClocks(composition,
                    asks, found, cells, false, named), named);
            settled.put(index, done);
            settledGaps.put(index, named);
            return done;
        }

        /**
         * The witness of this rank to claim, or null: with {@code own}, the
         * first that is its session's own run, judged aside -- nothing it
         * names is kept unless it is claimed, so a corpus with no such
         * witness is decided as without this pass -- else the first.
         */
        private Decision movedAsHappened(boolean configuration,
                                         boolean own) {
            for (int index = 0; index < outcomes.size(); index++) {
                Outcome free = outcomes.get(index);
                if (own ? !ownCandidate(free, configuration)
                        : !movedWitness(free, configuration)) {
                    continue;
                }
                Outcome asked = settle(index, free);
                List<GapRow> named = own ? new ArrayList<GapRow>() : gaps;
                if (!asked.witness() || (own && !ownRun(asked))
                        || unattested(composition, asked, named)) {
                    continue;
                }
                if (own) gaps.addAll(named);
                outcomes.set(index, asked);
                outcomes.set(0, asRecorded);
                return claimed(mechanism(composition, asks, asked,
                        clockDriven), asked);
            }
            return null;
        }

        private Decision movedFree(boolean configuration, boolean own) {
            // Unpublishable, so not refined: each clock pinned back is a
            // round of path asks (hdfs-11741 L1: hours of leastClocks over a
            // witness its polarity then refused).  Named once, by the pass
            // in the valuations' order.
            if (own && !polarityDecides) return null;
            for (int index = 0; index < outcomes.size(); index++) {
                Outcome found = outcomes.get(index);
                if (own ? !ownCandidate(found, configuration)
                        : !movedWitness(found, configuration)) {
                    continue;
                }
                if (!polarityDecides) {
                    undecidedPolarity(gaps, recorded, "a witness moving "
                            + found.valuation().moved().keySet());
                    return null;
                }
                // Published under every clock pin it can keep, and each
                // clock it still moves moved with room.
                Outcome outcome = settle(index, found);
                List<GapRow> named = own ? new ArrayList<GapRow>(
                        settledGaps.get(index)) : gaps;
                if (own && (!ownRun(outcome)
                        || unattested(composition, outcome, named))) {
                    continue;
                }
                if (!own) gaps.addAll(settledGaps.get(index));
                outcomes.set(index, outcome);
                if (!own && unattested(composition, outcome, gaps)) continue;
                if (own) gaps.addAll(named);
                // #mechanism answers MARKER_FLIPPED or a narrower replaced
                // slot, never NO_SUPPORTED_WITNESS.
                return claimed(mechanism(composition, asks, outcome,
                        clockDriven), outcome);
            }
            return null;
        }

        /** A moved witness of this rank that may be its session's own run,
         *  asked of nothing and naming nothing: {@link #movedWitness}'s
         *  conditions without its gaps, and {@link #ownRun}'s that need no
         *  model refined -- its own pairings, its moved roots run at their
         *  values ({@code Composition#ranRoots}). */
        private boolean ownCandidate(Outcome outcome, boolean configuration) {
            return outcome.valuation().ordinal() != 0 && outcome.witness()
                    && ranked(composition, outcome, configuration)
                    && composition.unplanted(outcome.valuation().moved()
                    .keySet()).isEmpty()
                    && ownPairings(outcome)
                    && composition.ranRoots(outcome.selected(),
                    outcome.valuation().moved());
        }

        /**
         * Whether this witness is its selected session's own run: the
         * selected path observed the fatal at the anchor, every arm the
         * model takes on it is its own run's pairing ({@code
         * Composition#repaired}), and that session ran the model's world --
         * its moved roots, clocks and no planted pairing ({@code
         * Composition#ranModel}, the test CONFIRM's realizedBy applies, so
         * such a claim is confirmed by that very session).
         */
        private boolean ownRun(Outcome outcome) {
            return ownPairings(outcome) && composition.ranModel(
                    outcome.selected(), movedRoots(composition, outcome));
        }

        private boolean ownPairings(Outcome outcome) {
            return outcome.selected().fatalObserved()
                    && composition.repaired(outcome.selected().selector(),
                    outcome.selectedArms().keySet()).isEmpty();
        }

        /** A witness of a moved valuation of this rank a replay can plant. */
        private boolean movedWitness(Outcome outcome, boolean configuration) {
            return outcome.valuation().ordinal() != 0 && outcome.witness()
                    && ranked(composition, outcome, configuration)
                    && !unplanted(composition, outcome, partial, gaps);
        }

        /**
         * 2. No root moves, and the clocks are necessary -- with the same
         * polarity condition, for the same reason -- or a pairing is: the
         * claim, or null.
         */
        Decision clockOrPairing() {
            for (Outcome outcome : outcomes) {
                if (!outcome.witness()
                        || !outcome.valuation().moved().isEmpty()) {
                    continue;
                }
                ClaimKind still = mechanism(composition, asks, outcome,
                        clockDriven);
                if (still != ClaimKind.CLOCK_SKEW
                        && still != ClaimKind.STATE_PAIRING_FLIPPED
                        && still != ClaimKind.MESSAGE_PAIRING_FLIPPED) {
                    continue;
                }
                // A clock or pairing the recording decides carries its own
                // polarity (recordingDecides); recorded.answer().unsat()
                // asks with them free and so could never publish CLOCK_SKEW.
                if (!recordingDecides && !polarityDecides) {
                    undecidedPolarity(gaps, recorded, still.name());
                    return null;
                }
                Outcome roomy = withMargin(composition, asks, outcome, gaps);
                outcomes.set(outcomes.indexOf(outcome), roomy);
                return claimed(still, roomy);
            }
            return null;
        }

        /**
         * 3. The recorded valuation reaches the fatal arm on another
         * session's path that OBSERVED it (the seed's own is no claim,
         * {@link #unasked}), through attested arms, while the seed's own
         * disjunct does not: the mechanism #mechanism's pin tests name, or
         * null, named, where none fires.
         */
        Decision observedElsewhere() {
            if (recorded == null || !recorded.witness()
                    || !recorded.selected().fatalObserved()
                    || !attestedArms(composition, recorded)
                    || !seedDisjunctUnsat(composition, asks)) {
                return null;
            }
            ClaimKind kind = mechanism(composition, asks, recorded,
                    clockDriven);
            if (kind != ClaimKind.NO_SUPPORTED_WITNESS) {
                return new Decision(Claim.of(kind, 0,
                        movedRoots(composition, recorded), true, gaps),
                        outcomes);
            }
            gaps.add(GapRow.of(recorded.selected().path().sessionId,
                    GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    recorded.selected().path().pathId,
                    "this path of an explored session reaches the fatal arm "
                            + "at the recorded roots and the seed's own "
                            + "disjunct does not, and no state slot, no wire "
                            + "slot, no moved root and no clock of this "
                            + "composition is what makes the difference: "
                            + "there is no mechanism to name"));
            return null;
        }

        /** No claim stands: the recorded valuation's answer, read. */
        Decision noWitness() {
            return new Decision(Claim.of(ClaimKind.NO_SUPPORTED_WITNESS,
                    recorded == null ? 0 : recorded.valuation().ordinal(),
                    Collections.<String, String>emptyMap(), polarityDecides,
                    gaps), outcomes);
        }

        private Decision claimed(ClaimKind kind, Outcome witness) {
            return new Decision(Claim.of(kind, witness.valuation().ordinal(),
                    movedRoots(composition, witness), true, gaps), outcomes);
        }
    }

    /** Whether a moved-root witness is of this pass's rank: configuration
     *  only, or anything else ({@code Composer#configurationOnly}). */
    private static boolean ranked(Composer.Composition composition,
                                  Outcome outcome, boolean configuration) {
        return composition.configurationOnly(
                outcome.valuation().moved().keySet()) == configuration;
    }

    /**
     * Whether a witness moves a configuration root whose plant leaves other
     * reads of its key at the recording's value (a second field caching
     * it, a getter in another shape or outside the slice; {@code
     * Composition#unplanted}): no configuration a cluster could hold, so no
     * replay can confirm it as one.  Not claimed; named once per root,
     * UNPRODUCIBLE_ANSWER DIAGNOSTIC.
     */
    private static boolean unplanted(Composer.Composition composition,
                                     Outcome outcome, Set<String> named,
                                     List<GapRow> gaps) {
        Map<String, List<String>> partial = composition.unplanted(
                outcome.valuation().moved().keySet());
        for (Map.Entry<String, List<String>> root : partial.entrySet()) {
            if (named.add(root.getKey())) {
                gaps.add(GapRow.of(Composer.COMPOSITION,
                        GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                        root.getKey(), "a witness moving this configuration"
                                + " is not claimed: its plant leaves "
                                + root.getValue().size() + " read(s) of the"
                                + " key at the recording's value, so the"
                                + " world it moves to is no configuration a"
                                + " cluster could hold: "
                                + root.getValue()));
            }
        }
        return !partial.isEmpty();
    }

    /** The label every valuation pin carries ({@code Composer}'s spelling). */
    private static final String VALUATION_LABEL = "valuation__";

    /** Whether one unsat core rests on a valuation pin at all. */
    private static boolean namesAValuation(List<String> core) {
        if (core == null) return false;
        for (String label : core) {
            if (label != null && label.startsWith(VALUATION_LABEL)) {
                return true;
            }
        }
        return false;
    }

    /**
     * How many valuations are asked at once (hdfs-17899-bug2: 128 valuations
     * one at a time held COMPOSE for hours while the head's other cores sat
     * idle): four whole asks, eight z3 processes, two per ask (one per
     * arithmetic engine, {@code Z3#run}); a valuation asked path by path
     * asks its paths on the composition's pool ({@link Disjunction}).
     */
    static final int PARALLEL_ASKS = 4;

    /** Independent asks answered in parallel, read back in their order. */
    private static <T, R> List<R> inParallel(List<T> items,
                                             Function<T, R> ask) {
        List<R> answers = new ArrayList<R>();
        if (items.isEmpty()) return answers;
        ExecutorService pool = Executors.newFixedThreadPool(
                Math.min(PARALLEL_ASKS, items.size()));
        try {
            List<Future<R>> pending = new ArrayList<Future<R>>();
            for (T item : items) pending.add(pool.submit(() -> ask.apply(item)));
            for (Future<R> answer : pending) answers.add(answer.get());
            return answers;
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException("interrupted while solving",
                    interrupted);
        } catch (ExecutionException failed) {
            Throwable cause = failed.getCause();
            if (cause instanceof RuntimeException) throw (RuntimeException) cause;
            throw new IllegalStateException(cause);
        } finally {
            pool.shutdownNow();
        }
    }

    /**
     * Each path asked alone with every root free (selector forced, no
     * valuation): one unsat there answers every root question the same way,
     * and is refuted for each.  When every path is, the claim rests on those
     * refutations, so each is asked once more without its fatal arm, what
     * its own run satisfied.  Unsat there -- or refuted after observing the
     * fatal arm -- is a contradiction the composition built
     * (PATH_SELF_CONTRADICTORY: DIAGNOSTIC per path, BLOCKING for the
     * composition).  Satisfied by every path, no root of the corpus turns
     * any of them to the fatal arm: that is the claim's own answer, no gap
     * (b20h BlockTokenSecretManager-511: the key read null-checked is pinned
     * to the object the run read, its writers outside the window).  A claim
     * whose polarity rests on a refuted path is refused separately
     * ({@link #namesAValuation}).
     */
    private static void selfContradictory(Composer.Composition composition,
                                          Disjunction asks,
                                          List<GapRow> gaps) {
        int undecided = 0;
        // A sanity check, not the witness search: its own short budget.  An
        // undecided run leaves the path in the disjunction (safe direction).
        for (Z3.Answer answer : asks.selfCheck()) {
            if (!answer.decided()) undecided++;
        }
        if (undecided > 0) {
            // A budget that drops a question says so: runs stay comparable.
            gaps.add(GapRow.of(Composer.COMPOSITION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    "self-check budget " + Disjunction.SELF_CHECK_BUDGET_MS
                            + "ms",
                    undecided + " of " + composition.disjuncts().size()
                            + " path(s) were not decided within the "
                            + "self-refutation budget and stay in the "
                            + "disjunction unexamined"));
        }
    }

    /**
     * THE PATHS AN UNSAT RESTS ON, each checked against its own run: every
     * path, with the formula unsat, is unsat with every root free, so each
     * is asked once more with its fatal arm left out
     * ({@code Disjunction#withoutFatalArms}), what its own run satisfied.
     * One unsat there (or undecided within the budget), or one that
     * observed the fatal arm, contradicts its run: DIAGNOSTIC per path, and
     * BLOCKING for the composition, since an UNSAT resting on it is about
     * the formula built and not about the recording.  A path refuted by its
     * fatal arm alone is the claim's own answer, and so is one whose own
     * self-check core names a refuted claim the formula asserts ({@link
     * Disjunction#refutedBySelfCheck}): CONFIRM ran that model and
     * disagreed, and the UNSAT names the refutation it rests on ({@code
     * restsOnRefutations}).
     */
    private static void contradictions(Composer.Composition composition,
                                       Disjunction asks,
                                       List<GapRow> gaps) {
        List<Z3.Answer> withoutFatalArms = asks.withoutFatalArms();
        int contradictory = 0;
        for (int i = 0; i < withoutFatalArms.size(); i++) {
            Composer.Disjunct disjunct = composition.disjuncts().get(i);
            Z3.Answer answer = withoutFatalArms.get(i);
            if (answer.sat() && (!disjunct.fatalObserved()
                    || asks.refutedBySelfCheck(disjunct.selector()))) {
                continue;
            }
            contradictory++;
            gaps.add(GapRow.of(disjunct.path().sessionId,
                    GapKind.PATH_SELF_CONTRADICTORY, GapClass.DIAGNOSTIC,
                    disjunct.path().pathId, disjunct.fatalObserved()
                            ? "this path observed the fatal arm, and its "
                            + "conjunction is unsatisfiable with every root "
                            + "free"
                            : answer.unsat()
                            ? "this path's conjunction is unsatisfiable even "
                            + "without its fatal arm, every root free, "
                            + "though its own run satisfied it"
                            : "z3 answered " + answer.status() + " for this "
                            + "path's conjunction without its fatal arm "
                            + "within " + Disjunction.SELF_CHECK_BUDGET_MS
                            + "ms, so nothing shows it states its own run"));
        }
        if (contradictory == 0) return;
        gaps.add(GapRow.of(Composer.COMPOSITION,
                GapKind.PATH_SELF_CONTRADICTORY, GapClass.BLOCKING,
                composition.anchor().render(),
                "the composed formula is unsat, and " + contradictory
                        + " of its " + withoutFatalArms.size() + " paths "
                        + "contradict their own run, so the verdict is about "
                        + "the formula it built, not about the recording"));
    }

    /**
     * A mechanism the formula shows but the recording does not decide, raised
     * as FORMULA_SAT_AT_RECORDED_VALUATION, not published: the run reached
     * the fatal arm at the recorded valuation too, or its refutation names no
     * valuation pin.  An UNDECIDED recorded valuation is named already
     * ({@link Reading#undecided}) and is no such statement (hdfs-11741 L1: valuation 0
     * "unknown" was published as satisfiable).
     */
    private static void undecidedPolarity(List<GapRow> gaps,
                                          Outcome recorded, String shown) {
        if (recorded == null || !recorded.answer().decided()) return;
        for (GapRow gap : gaps) {
            if (gap.kind() == GapKind.FORMULA_SAT_AT_RECORDED_VALUATION) {
                return;
            }
        }
        gaps.add(GapRow.of(recorded.selected() == null
                        ? Composer.COMPOSITION
                        : recorded.selected().path().sessionId,
                GapKind.FORMULA_SAT_AT_RECORDED_VALUATION,
                GapClass.DIAGNOSTIC, shown, "the formula shows " + shown
                        + (recorded.answer().sat()
                        ? ", and it is satisfiable with every declared root "
                        + "at its recorded value too"
                        : ", and the recorded valuation's refutation names "
                        + "no valuation pin")
                        + ", so the recording does not decide the arm"));
    }

    /**
     * The mechanism this witness's own evidence names, narrowest first; no
     * caller can make it name one the witness does not show.
     *
     * <ul>
     *   <li>STATE_PAIRING_FLIPPED -- pinning the versions the path's reads
     *       observed makes it unsat: a replaced state slot.</li>
     *   <li>MESSAGE_PAIRING_FLIPPED -- the same for its attaches' arrivals:
     *       a replaced wire slot (second: a witness needing both is about
     *       the interleaving).</li>
     *   <li>MARKER_FLIPPED -- the valuation moved a declared root.</li>
     *   <li>CLOCK_SKEW -- nothing moved and the clocks are necessary
     *       ({@code clockDriven}, asked once by {@link Reading}).</li>
     *   <li>NO_SUPPORTED_WITNESS -- none of them; never a default.</li>
     * </ul>
     */
    private static ClaimKind mechanism(Composer.Composition composition,
                                       Disjunction asks, Outcome outcome,
                                       boolean clockDriven) {
        if (outcome == null || outcome.selected() == null) {
            return ClaimKind.NO_SUPPORTED_WITNESS;
        }
        String pathId = outcome.selected().path().pathId;
        if (unsatWith(asks, outcome, composition.observedReads(pathId))) {
            return ClaimKind.STATE_PAIRING_FLIPPED;
        }
        if (unsatWith(asks, outcome,
                composition.observedArrivals(pathId))) {
            return ClaimKind.MESSAGE_PAIRING_FLIPPED;
        }
        if (!outcome.valuation().moved().isEmpty()) {
            return ClaimKind.MARKER_FLIPPED;
        }
        // Nothing moved: whether the clocks are necessary was asked by
        // Reading.
        if (clockDriven) return ClaimKind.CLOCK_SKEW;
        return ClaimKind.NO_SUPPORTED_WITNESS;
    }

    /**
     * The roots this witness moved: the valuation's moved roots plus every
     * clock cell where the model's clock jumped ({@link #jump}; no valuation
     * pins a clock, so the model is the only statement of it), at the
     * model's instant.  A cell that runs on from the cell before it is one
     * {@link #leastClocks} pinned as unneeded.  A jump BACK is a jump too: a
     * cell the witness needs short of where its clock ran on to (it must
     * stay below a bound an earlier jump would carry it past) is one a
     * replay has to plant, or it runs on ahead; it is named at its model
     * instant, which can be its own reading (the clock set back to the
     * host's).  NO_SUPPORTED_WITNESS claims carry an empty map instead.
     */
    private static Map<String, String> movedRoots(
            Composer.Composition composition, Outcome outcome) {
        Map<String, String> moved = new LinkedHashMap<String, String>();
        if (outcome == null) return moved;
        moved.putAll(outcome.valuation().moved());
        Map<String, String> model = outcome.answer().values();
        for (String cell : composition.clockCells()) {
            Long jumped = jump(composition, model, cell);
            if (jumped == null || jumped == 0L) continue;
            moved.put(cell, model.get(cell).trim());
        }
        return moved;
    }

    /** This valuation, this disjunct, and what the run actually paired. */
    private static boolean unsatWith(Disjunction asks, Outcome outcome,
                                     List<String> observed) {
        if (observed.isEmpty()) return false;
        List<String> pinned =
                new ArrayList<String>(outcome.valuation().assertions());
        pinned.addAll(outcome.pinned());
        pinned.addAll(observed);
        return asks.askPath(outcome.selected().selector(), pinned,
                Collections.<String>emptyList(), false).unsat();
    }

    /** Which arm of each family this model set the selector of, and which
     *  state of each object a state arm delivers its queries saw. */
    private static Map<String, ComposedFamilies.ArmChoice> armsOf(
            Composer.Composition composition, Z3.Answer answer) {
        Map<String, ComposedFamilies.ArmChoice> taken =
                new LinkedHashMap<String, ComposedFamilies.ArmChoice>();
        if (!answer.sat()) return taken;
        for (Map.Entry<String, String> value : answer.values().entrySet()) {
            if (!"true".equals(value.getValue())) continue;
            ComposedFamilies.ArmChoice arm =
                    composition.arm(value.getKey());
            if (arm != null) {
                taken.put(value.getKey(), arm.taking(answer.values()));
            }
        }
        return taken;
    }

    /** Which disjunct a sat model selected, or null when it named none. */
    private static Composer.Disjunct selectedOf(
            Composer.Composition composition, Z3.Answer answer) {
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
     * Whether this witness moves a root inside an arm whose producer ran
     * concretely (the recording says nothing of what it would deliver had
     * the root moved); if so it is refused by name.
     */
    private static boolean unattested(Composer.Composition composition,
                                      Outcome outcome, List<GapRow> gaps) {
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
        if (refused.isEmpty()) return false;
        gaps.add(GapRow.of(outcome.selected().path().sessionId,
                GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                refused.toString(), "this witness moves a root that occurs "
                        + "inside an arm no producer path condition attests, "
                        + "so it names no mechanism and is the formula's "
                        + "alone (FORMULA_SAT)"));
        return true;
    }

    /**
     * One valuation asked for every path selector, family arm selector,
     * nested state selector, clock cell and held leaf (legalized: {@code
     * Z3.modelQuery} appends names raw), so the claim can read path,
     * delivery, the states a delivered object was queried at, clocks, and
     * what each held leaf carried off the model.
     */
    private static Outcome outcome(Composer.Composition composition,
                                   Disjunction asks,
                                   Composer.Valuation valuation,
                                   List<String> pinned, boolean wantCore) {
        return outcome(composition, asks, valuation, pinned, wantCore, null);
    }

    /**
     * The same, asked of one path only where {@code path} names it: the
     * refinement of a witness ({@link #leastClocks}, {@link #withMargin})
     * keeps the witness's path, and another path's ask (one its own run
     * refutes, asked free for its whole budget) waits for no answer it would
     * give (hdfs-11741 L1: each pin of the clock-driven witness waited 30
     * minutes on a path undecided free).
     */
    private static Outcome outcome(Composer.Composition composition,
                                   Disjunction asks,
                                   Composer.Valuation valuation,
                                   List<String> pinned, boolean wantCore,
                                   Outcome path) {
        return outcome(composition, asks, valuation, pinned, wantCore, path,
                0L);
    }

    /** The same within {@code budgetMillis} ({@code <= 0}: the solver's). */
    private static Outcome outcome(Composer.Composition composition,
                                   Disjunction asks,
                                   Composer.Valuation valuation,
                                   List<String> pinned, boolean wantCore,
                                   Outcome path, long budgetMillis) {
        List<String> asked = new ArrayList<String>(composition.selectors());
        asked.addAll(composition.armSelectors());
        asked.addAll(composition.stateSelectors());
        for (String cell : composition.clockCells()) {
            asked.add(SmtNames.legalSymbols(cell));
        }
        for (String held : composition.heldSymbols()) {
            asked.add(SmtNames.legalSymbols(held));
        }
        asked.addAll(composition.rootSymbols());
        List<String> assertions =
                new ArrayList<String>(valuation.assertions());
        assertions.addAll(pinned);
        Z3.Answer answer = path == null
                ? asks.ask(assertions, composition.selectors(), asked,
                wantCore)
                : asks.askPath(path.selected().selector(), assertions, asked,
                wantCore, budgetMillis);
        return new Outcome(valuation, pinned, answer,
                selectedOf(composition, answer), armsOf(composition, answer));
    }

    /** How long one refinement of one witness may ask ({@link
     *  #leastClocks}, {@link #withMargin}); past it the witness is published
     *  as far as it got, named. */
    static final long REFINE_BUDGET_MS = 300000L;

    /**
     * The witness under every clock pin it can keep, each cell running on
     * from the cell before it ({@link #runsOn}): a cell the witness's own
     * model runs on already is pinned without an ask (the model is one
     * under it).  Of its jumps, those outside its path's causal cone
     * ({@code Composition#cone}, what acceptance reads: {@code cone.py}) are
     * pinned first, in one ask, else one at a time in the recording's seq
     * order; then those inside it, one at a time, so a jump lands as late as
     * the witness allows.  All within {@link #REFINE_BUDGET_MS}: past it a
     * jump inside the cone stands, a cause of the fatal by the formula,
     * named DIAGNOSTIC (hdfs-11741 L1: 25 cells, each a round of path asks,
     * ran past an hour).  {@code needed}:
     * the recording already says the clocks are (clockDriven); otherwise a
     * witness that needs no jump at all is asked for first.
     */
    private static Outcome leastClocks(Composer.Composition composition,
                                       Disjunction asks, Outcome outcome,
                                       List<String> cells, boolean needed,
                                       List<GapRow> gaps) {
        if (cells.isEmpty()) return outcome;
        Map<String, String> model = outcome.answer().values();
        Set<String> cone = composition.cone(outcome.selected().selector());
        List<String> kept = new ArrayList<String>();
        List<String> outside = new ArrayList<String>();
        List<String> inside = new ArrayList<String>();
        for (String cell : cells) {
            Long jumped = jump(composition, model, cell);
            if (jumped != null && jumped == 0L) {
                kept.add(cell);
            } else if (cone.contains(cell)) {
                inside.add(cell);
            } else {
                outside.add(cell);
            }
        }
        Outcome witness = new Outcome(outcome.valuation(),
                runsOn(composition, kept), outcome.answer(),
                outcome.selected(), outcome.arms);
        long deadline = System.currentTimeMillis() + REFINE_BUDGET_MS;
        if (!needed && kept.size() < cells.size()) {
            Outcome all = outcome(composition, asks, outcome.valuation(),
                    runsOn(composition, cells), false, outcome,
                    REFINE_BUDGET_MS);
            if (all.witness()) return all;
        }
        List<String> order = new ArrayList<String>(outside);
        if (!outside.isEmpty()) {
            List<String> tried = new ArrayList<String>(kept);
            tried.addAll(outside);
            Outcome within = outcome(composition, asks, outcome.valuation(),
                    runsOn(composition, tried), false, outcome,
                    REFINE_BUDGET_MS);
            if (within.witness()) {
                kept = tried;
                witness = within;
                order.clear();
            }
        }
        order.addAll(inside);
        for (int at = 0; at < order.size(); at++) {
            long left = deadline - System.currentTimeMillis();
            if (left <= 0L) {
                refinementCut(gaps, "leastClocks", order.subList(at,
                        order.size()));
                break;
            }
            kept.add(order.get(at));
            Outcome asked = outcome(composition, asks, outcome.valuation(),
                    runsOn(composition, kept), false, outcome, left);
            if (asked.witness()) {
                witness = asked;
            } else {
                kept.remove(kept.size() - 1);
            }
        }
        return witness;
    }

    /** A refinement that ran out of {@link #REFINE_BUDGET_MS}: the witness
     *  stands as far as it got, its untried cells named. */
    private static void refinementCut(List<GapRow> gaps, String step,
                                      List<String> untried) {
        gaps.add(GapRow.of(Composer.COMPOSITION, GapKind.SOLVER_TIMEOUT,
                GapClass.DIAGNOSTIC, step, "the witness's refinement ran "
                        + "out of its " + REFINE_BUDGET_MS / 1000L + " s "
                        + "with " + untried.size() + " cell(s) untried, "
                        + "which it publishes as they stand: " + untried));
    }

    /**
     * The witness with each clock jump it makes ({@link #jump}) made
     * {@link ClockMargin#margin} (a minute in its ticks) further the same
     * way, where the formula still reaches the fatal arm there.  The model is
     * the cheapest world (a token's expiry passed by one millisecond), and
     * the confirming replay reads every clock fresh, so an instant at the
     * boundary falls back on the recorded arm: exploration's margin rule
     * (adhoc token-expired.proxy missed by 70 ms).  Every margin at once
     * first; else each jump's in seq order, kept where the witness stays: a
     * jump back that sits on its cell's floor has no room, and costs the
     * other jumps none of theirs.  Within {@link #REFINE_BUDGET_MS}.
     */
    private static Outcome withMargin(Composer.Composition composition,
                                      Disjunction asks, Outcome witness,
                                      List<GapRow> gaps) {
        Map<String, String> model = witness.answer().values();
        List<String> margins = new ArrayList<String>();
        for (String cell : composition.clockCells()) {
            Long jumped = jump(composition, model, cell);
            if (jumped == null || jumped == 0L) continue;
            long at = Long.parseLong(model.get(cell).trim());
            boolean later = jumped > 0L;
            long margin = ClockMargin.margin(
                    composition.clockNanos().get(cell));
            margins.add("(assert (! (" + (later ? ">=" : "<=") + " " + cell
                    + " " + integralLiteral(Long.toString(later
                    ? at + margin : at - margin))
                    + ") :named clock_margin__" + ArtifactIO.digest(cell, 10)
                    + "))");
        }
        if (margins.isEmpty()) return witness;
        long deadline = System.currentTimeMillis() + REFINE_BUDGET_MS;
        List<String> room = new ArrayList<String>(witness.pinned());
        room.addAll(margins);
        Outcome all = outcome(composition, asks, witness.valuation(),
                room, false, witness, REFINE_BUDGET_MS);
        if (all.witness() || margins.size() == 1) {
            return all.witness() ? all : witness;
        }
        List<String> kept = new ArrayList<String>(witness.pinned());
        Outcome roomy = witness;
        for (int at = 0; at < margins.size(); at++) {
            long left = deadline - System.currentTimeMillis();
            if (left <= 0L) {
                refinementCut(gaps, "withMargin", margins.subList(at,
                        margins.size()));
                break;
            }
            kept.add(margins.get(at));
            Outcome asked = outcome(composition, asks, witness.valuation(),
                    kept, false, witness, left);
            if (asked.witness()) {
                roomy = asked;
            } else {
                kept.remove(kept.size() - 1);
            }
        }
        return roomy;
    }

    /**
     * These cells running on from the cell before each on its node's clock
     * ({@link Composer.Composition#clockBefore}), as named pins: a cell keeps
     * that cell's skew off its reading, and a cell with none before it its
     * reading.  A clock that jumped at one cell runs on from there, as a
     * replay runs it ({@code runtime.NodeClocks}, by the same seq order), so
     * the cells after a jump are no more the witness's moves than the cells
     * before it (SOLR-18406: delete()'s clock jumped past G's reservation,
     * and the commit's next two readings were moved with it, the second one
     * outside the witness path's cone).
     */
    private static List<String> runsOn(Composer.Composition composition,
                                       List<String> cells) {
        List<String> pinned = new ArrayList<String>();
        for (String cell : cells) {
            pinned.add("(assert (! " + Composer.clockStep(cell,
                    composition.clockReadings(), composition.clockBefore(),
                    0) + " :named clock_runs_on__"
                    + ArtifactIO.digest(cell, 10) + "))");
        }
        return pinned;
    }

    /**
     * How far a model's clock jumped at one cell: its skew off its reading
     * less the skew of the cell before it on its node's clock, or null where
     * the model or the recording states no instant for either.
     */
    private static Long jump(Composer.Composition composition,
                             Map<String, String> model, String cell) {
        Long skew = skew(composition, model, cell);
        String before = composition.clockBefore().get(cell);
        if (skew == null || before == null) return skew;
        Long previous = skew(composition, model, before);
        return previous == null ? null : skew - previous;
    }

    private static Long skew(Composer.Composition composition,
                             Map<String, String> model, String cell) {
        Long reading = composition.clockReadings().get(cell);
        String answered = model.get(cell);
        if (reading == null || answered == null) return null;
        try {
            return Long.parseLong(answered.trim()) - reading;
        } catch (NumberFormatException notAnInstant) {
            return null;
        }
    }

    /** These cells at the instants the recording read, as named pins. */
    private static List<String> pins(Composer.Composition composition,
                                     List<String> cells) {
        List<String> pinned = new ArrayList<String>();
        for (String cell : cells) {
            pinned.add("(assert (! (= " + cell + " " + integralLiteral(
                    Long.toString(composition.clockReadings().get(cell)))
                    + ") :named clock_pinned__" + ArtifactIO.digest(cell, 10)
                    + "))");
        }
        return pinned;
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
            for (Arm arm : family.arms()) attested |= arm.attested();
            if (!attested) return false;
        }
        return true;
    }

    /**
     * Whether every disjunct of the seed's session is unsat at the recorded
     * roots; else the claim is about the recording, not a pairing.  No seed
     * path: false.
     */
    static boolean seedDisjunctUnsat(
            Composer.Composition composition, Disjunction asks) {
        String seed = composition.seedSessionId();
        if (seed == null) return false;
        List<String> selectors = new ArrayList<String>();
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            if (disjunct.path().sessionId.equals(seed)) {
                selectors.add(disjunct.selector());
            }
        }
        if (selectors.isEmpty()) return false;
        List<String> pinned = new ArrayList<String>();
        if (!composition.valuations().isEmpty()) {
            pinned.addAll(composition.valuations().get(0).assertions());
        }
        pinned.add("(assert " + VmTermLowering.or(selectors) + ")");
        return asks.ask(pinned, selectors, Collections.<String>emptyList(),
                false).unsat();
    }
}
