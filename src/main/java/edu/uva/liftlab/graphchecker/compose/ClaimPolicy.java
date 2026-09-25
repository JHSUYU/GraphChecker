package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.Z3;

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
 *       asked under every pin it can keep ({@link #leastClocks}), so {@link
 *       Claim#movedRoots} ({@link #movedRoots}) names only the cells it
 *       needs.  A moved marker is asked first ({@link #mechanism}); where
 *       the clock pins refute the recorded valuation, a moved root must
 *       reach the fatal arm under those same pins.</li>
 *   <li><b>MESSAGE_PAIRING_FLIPPED</b> -- an explored session's fatal path
 *       is sat at the recorded roots through attested arms while the seed's
 *       own disjunct is not.</li>
 *   <li><b>RECORDED_FAILURE_EXPLAINED</b> -- the seed observed the fatal arm
 *       and the composition reproduces it with nothing moved, every flipped
 *       valuation decided and unsat.</li>
 *   <li><b>NO_SUPPORTED_WITNESS</b> -- everything else, including an
 *       occurrence no session reached; an answer, not an exception.</li>
 * </ul>
 *
 * <p>Two refusals ride on top: a formula sat as the run happened (recorded
 * roots, clocks and pairings) on a session that took the HEALTHY arm raises
 * the blocking FORMULA_SAT_AT_RECORDED_VALUATION, and enumeration continues
 * past it; a witness moving a root inside an UNATTESTED arm is refused,
 * since no producer path condition says the delivery survives the move.</p>
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

        @Override
        public String toString() {
            return valuation + " -> " + answer.status()
                    + (selected == null ? ""
                    : " (" + selected.path().pathId + ")");
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
                                  Z3 solver) {
        Decision decision = read(composition, solver);
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
                decision.outcomes());
    }

    private static Decision read(Composer.Composition composition,
                                 Z3 solver) {
        List<GapRow> gaps = new ArrayList<GapRow>(composition.gaps());
        List<Outcome> outcomes = new ArrayList<Outcome>();
        if (composition.disjuncts().isEmpty()) {
            // An occurrence no session reached is a claim about the corpus.
            return new Decision(Claim.of(ClaimKind.NO_SUPPORTED_WITNESS, 0,
                    Collections.<String, String>emptyMap(), false, gaps),
                    outcomes);
        }
        for (Composer.Valuation valuation : composition.valuations()) {
            outcomes.add(outcome(composition, solver, valuation,
                    Collections.<String>emptyList(),
                    valuation.ordinal() == 0));
        }
        Outcome recorded = outcomes.isEmpty() ? null : outcomes.get(0);

        // Each disjunct asked alone with every root free: unsat there is a
        // self-contradictory path, not a statement about the roots.
        selfContradictory(composition, solver, gaps);

        // An undecided valuation is named and blocks: neither a witness nor
        // a refutation is closed over it.
        for (Outcome outcome : outcomes) {
            if (outcome.answer().decided()) continue;
            String reason = outcome.answer().reason();
            gaps.add(GapRow.of(Composer.COMPOSITION,
                    GapKind.DECLARATION_MISSING, GapClass.BLOCKING,
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

        // The run as it happened pins every clock to its reading and every
        // path to its own pairing (Composition#recordedPairings), not just
        // the roots: no valuation pins either.  Asked ONCE here; the answer
        // is read by the alarm, loop 1, branch 2 and #mechanism.  Unsat while
        // the free valuation is sat means a clock or a pairing reaches the
        // fatal arm; asking the clocks alone tells which (CLOCK_SKEW).
        List<String> cells = clockCellsRead(composition);
        List<String> asHappened = new ArrayList<String>(pins(composition,
                cells));
        asHappened.addAll(composition.recordedPairings());
        boolean freeSat = recorded != null && recorded.answer().sat()
                && recorded.selected() != null;
        Outcome asRecorded = freeSat && !asHappened.isEmpty()
                ? outcome(composition, solver, recorded.valuation(),
                        asHappened, false) : null;
        boolean recordingDecides = asRecorded != null
                && asRecorded.answer().unsat();
        boolean clockDriven = recordingDecides && !cells.isEmpty()
                && outcome(composition, solver, recorded.valuation(),
                        pins(composition, cells), false).answer().unsat();
        if (clockDriven) {
            recorded = leastClocks(composition, solver, recorded, cells);
            outcomes.set(0, recorded);
        }
        if (recorded != null && recorded.answer().sat()
                && recorded.selected() != null
                && !recorded.selected().fatalObserved()
                && !recordingDecides) {
            gaps.add(GapRow.of(recorded.selected().path().sessionId,
                    GapKind.FORMULA_SAT_AT_RECORDED_VALUATION,
                    GapClass.BLOCKING,
                    recorded.selected().path().pathId,
                    "this disjunct is satisfiable with every declared root "
                            + "at its recorded value, and its own recording "
                            + "took the healthy arm"));
        }

        // Polarity decides only when the unsat core names a valuation pin;
        // otherwise the path refuted itself under every valuation.
        boolean polarityDecides = recorded != null
                && recorded.answer().unsat()
                && namesAValuation(recorded.answer().core());

        // 1. A declared root moved inside its domain; polarity (ordinal 0
        // unsat) is a CONDITION on the claim.  When the recording decides
        // the arm, a moved root must reach the fatal arm with clocks and
        // pairings held as recorded, so neither is part of the witness.
        if (recordingDecides) {
            List<String> held = asHappened;
            for (int index = 0; index < outcomes.size(); index++) {
                Outcome free = outcomes.get(index);
                if (free.valuation().ordinal() == 0) continue;
                if (!free.answer().sat() || free.selected() == null) continue;
                Outcome asked = outcome(composition, solver,
                        free.valuation(), held, false);
                if (!asked.answer().sat() || asked.selected() == null) {
                    continue;
                }
                if (unattested(composition, asked, gaps)) continue;
                outcomes.set(index, asked);
                outcomes.set(0, asRecorded);
                return new Decision(Claim.of(mechanism(composition, solver,
                        asked, outcomes, clockDriven),
                        asked.valuation().ordinal(),
                        movedRoots(composition, asked), true, gaps),
                        outcomes);
            }
        }
        if (!recordingDecides) {
            for (Outcome found : new ArrayList<Outcome>(outcomes)) {
                if (found.valuation().ordinal() == 0) continue;
                if (!found.answer().sat() || found.selected() == null) {
                    continue;
                }
                // Publish the witness under every clock pin it can keep.
                Outcome outcome = leastClocks(composition, solver, found,
                        cells);
                outcomes.set(outcomes.indexOf(found), outcome);
                if (unattested(composition, outcome, gaps)) continue;
                // A moved root: #mechanism answers MARKER_FLIPPED or a
                // narrower replaced slot, never NO_SUPPORTED_WITNESS.
                ClaimKind moved = mechanism(composition, solver, outcome,
                        outcomes, clockDriven);
                if (!polarityDecides) {
                    undecidedPolarity(gaps, recorded, moved);
                    break;
                }
                return new Decision(Claim.of(moved,
                        outcome.valuation().ordinal(),
                        movedRoots(composition, outcome), true, gaps),
                        outcomes);
            }
        }

        // 2. No root moves, and the clocks are necessary -- with the same
        //    polarity condition, for the same reason.
        for (Outcome outcome : outcomes) {
            if (!outcome.answer().sat() || outcome.selected() == null) {
                continue;
            }
            if (!outcome.valuation().moved().isEmpty()) continue;
            // RECORDED_FAILURE_EXPLAINED is asked below, with the flips.
            ClaimKind still = mechanism(composition, solver, outcome,
                    outcomes, clockDriven);
            if (still != ClaimKind.CLOCK_SKEW
                    && still != ClaimKind.STATE_PAIRING_FLIPPED
                    && still != ClaimKind.MESSAGE_PAIRING_FLIPPED) {
                continue;
            }
            // A clock or pairing the recording decides carries its own
            // polarity (recordingDecides); recorded.answer().unsat() asks
            // with them free and so could never publish CLOCK_SKEW.
            if (!recordingDecides && !polarityDecides) {
                undecidedPolarity(gaps, recorded, still);
                break;
            }
            return new Decision(Claim.of(still,
                    outcome.valuation().ordinal(),
                    movedRoots(composition, outcome), true,
                    gaps), outcomes);
        }

        // 3 and 4. The recorded valuation reaches the fatal arm on a path
        // that OBSERVED it -- the recording's own, or another session's.
        if (recorded != null && recorded.answer().sat()
                && recorded.selected() != null
                && recorded.selected().fatalObserved()) {
            String session = recorded.selected().path().sessionId;
            boolean seed = session.equals(composition.seedSessionId());
            if (seed && flipsRefuted(outcomes)) {
                ClaimKind kind = mechanism(composition, solver, recorded,
                        outcomes, clockDriven);
                return new Decision(Claim.of(kind, 0,
                        movedRoots(composition, recorded),
                        kind != ClaimKind.RECORDED_FAILURE_EXPLAINED
                                && kind != ClaimKind.NO_SUPPORTED_WITNESS,
                        gaps), outcomes);
            }
            if (!seed && attestedArms(composition, recorded)
                    && seedDisjunctUnsat(composition, solver)) {
                // Which mechanism differs is #mechanism's pin tests; if
                // none fires, nothing has been established.
                ClaimKind kind = mechanism(composition, solver, recorded,
                        outcomes, clockDriven);
                if (kind != ClaimKind.NO_SUPPORTED_WITNESS) {
                    return new Decision(Claim.of(kind, 0,
                            movedRoots(composition, recorded), true,
                            gaps), outcomes);
                }
                gaps.add(GapRow.of(session, GapKind.UNSTATED_VALUE,
                        GapClass.DIAGNOSTIC, recorded.selected()
                                .path().pathId,
                        "this path of an explored session reaches the "
                                + "fatal arm at the recorded roots and the "
                                + "seed's own disjunct does not, and no "
                                + "state slot, no wire slot, no moved root "
                                + "and no clock of this composition is "
                                + "what makes the difference: there is no "
                                + "mechanism to name"));
            }
        }

        return new Decision(Claim.of(ClaimKind.NO_SUPPORTED_WITNESS,
                recorded == null ? 0 : recorded.valuation().ordinal(),
                Collections.<String, String>emptyMap(), polarityDecides,
                gaps), outcomes);
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

    /** Budget of one self-refutation run: decides a path, scans them all. */
    static final long SELF_CHECK_BUDGET_MS = 60000L;

    /**
     * Names every path whose OWN conjunction is unsat (selector forced, no
     * valuation): such a path answers every root question the same way.
     */
    private static void selfContradictory(Composer.Composition composition,
                                          Z3 solver, List<GapRow> gaps) {
        int inert = 0;
        int undecided = 0;
        // A sanity check, not the witness search: its own short budget.  An
        // undecided run leaves the path in the disjunction (safe direction).
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            List<String> forced = new ArrayList<String>();
            forced.add("(assert (! " + disjunct.selector()
                    + " :named path_alone__"
                    + ArtifactIO.digest(disjunct.path().pathId, 10) + "))");
            Z3.Answer answer = solver.ask(composition.query(forced),
                    Collections.<String>emptyList(), false,
                    SELF_CHECK_BUDGET_MS);
            if (!answer.decided()) undecided++;
            if (!answer.unsat()) continue;
            inert++;
            // DIAGNOSTIC per path (may be a corpus fact); a claim whose
            // polarity rests on it is refused separately (#namesAValuation).
            gaps.add(GapRow.of(disjunct.path().sessionId,
                    GapKind.PATH_SELF_CONTRADICTORY, GapClass.DIAGNOSTIC,
                    disjunct.path().pathId,
                    "this path's own conjunction is unsatisfiable with "
                            + "every root free, so no valuation of any root "
                            + "could have satisfied it and it contributes "
                            + "nothing to the disjunction; z3 closed on "
                            + answer.core()));
        }
        if (undecided > 0) {
            // A budget that drops a question says so: runs stay comparable.
            gaps.add(GapRow.of(Composer.COMPOSITION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    "self-check budget " + SELF_CHECK_BUDGET_MS + "ms",
                    undecided + " of " + composition.disjuncts().size()
                            + " path(s) were not decided within the "
                            + "self-refutation budget and stay in the "
                            + "disjunction unexamined"));
        }
        if (inert > 0 && inert == composition.disjuncts().size()) {
            // Every path inert: the composition is false in every world.
            gaps.add(GapRow.of(Composer.COMPOSITION,
                    GapKind.PATH_SELF_CONTRADICTORY, GapClass.BLOCKING,
                    composition.anchor().render(),
                    "all " + inert + " composed paths are unsatisfiable "
                            + "with every root free, so this composition is "
                            + "false in every world of the corpus and its "
                            + "verdicts are about the formula it built, not "
                            + "about the recording"));
        }
    }

    /**
     * A mechanism the formula shows but the recording does not decide: the
     * run reached the fatal arm at the recorded valuation too, so it is
     * raised as FORMULA_SAT_AT_RECORDED_VALUATION, not published.
     */
    private static void undecidedPolarity(List<GapRow> gaps,
                                          Outcome recorded, ClaimKind kind) {
        for (GapRow gap : gaps) {
            if (gap.kind() == GapKind.FORMULA_SAT_AT_RECORDED_VALUATION) {
                return;
            }
        }
        gaps.add(GapRow.of(recorded == null || recorded.selected() == null
                        ? Composer.COMPOSITION
                        : recorded.selected().path().sessionId,
                GapKind.FORMULA_SAT_AT_RECORDED_VALUATION,
                GapClass.BLOCKING, kind.name(),
                "the formula shows " + kind + ", and it is satisfiable with "
                        + "every declared root at its recorded value too, so "
                        + "the recording does not decide the arm"));
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
     *       ({@code clockDriven}, asked once in {@code read}).</li>
     *   <li>RECORDED_FAILURE_EXPLAINED -- the seed path reached the fatal
     *       arm at ordinal 0 and every moved valuation is decided unsat.</li>
     *   <li>NO_SUPPORTED_WITNESS -- none of them; never a default.</li>
     * </ul>
     */
    private static ClaimKind mechanism(Composer.Composition composition,
                                       Z3 solver, Outcome outcome,
                                       List<Outcome> outcomes,
                                       boolean clockDriven) {
        if (outcome == null || outcome.selected() == null) {
            return ClaimKind.NO_SUPPORTED_WITNESS;
        }
        String pathId = outcome.selected().path().pathId;
        if (unsatWith(composition, solver, outcome,
                composition.observedReads(pathId))) {
            return ClaimKind.STATE_PAIRING_FLIPPED;
        }
        if (unsatWith(composition, solver, outcome,
                composition.observedArrivals(pathId))) {
            return ClaimKind.MESSAGE_PAIRING_FLIPPED;
        }
        if (!outcome.valuation().moved().isEmpty()) {
            return ClaimKind.MARKER_FLIPPED;
        }
        // Nothing moved: whether the clocks are necessary was asked in #read.
        if (clockDriven) return ClaimKind.CLOCK_SKEW;
        if (outcome.valuation().ordinal() == 0
                && outcome.selected().fatalObserved()
                && outcome.selected().path().sessionId.equals(
                        composition.seedSessionId())
                && flipsRefuted(outcomes)) {
            return ClaimKind.RECORDED_FAILURE_EXPLAINED;
        }
        return ClaimKind.NO_SUPPORTED_WITNESS;
    }

    /**
     * The roots this witness moved: the valuation's moved roots plus every
     * clock cell the model placed off its recorded reading (no valuation
     * pins a clock, so the model is the only statement of it).  Cells at
     * their reading are ones {@link #leastClocks} pinned as unneeded.
     * NO_SUPPORTED_WITNESS claims carry an empty map instead.
     */
    private static Map<String, String> movedRoots(
            Composer.Composition composition, Outcome outcome) {
        Map<String, String> moved = new LinkedHashMap<String, String>();
        if (outcome == null) return moved;
        moved.putAll(outcome.valuation().moved());
        Map<String, String> model = outcome.answer().values();
        for (String cell : composition.clockCells()) {
            Long reading = composition.clockReadings().get(cell);
            String answered = model.get(cell);
            if (answered == null || reading == null) continue;
            String at = answered.trim();
            if (at.isEmpty() || at.equals(Long.toString(reading))) continue;
            moved.put(cell, at);
        }
        return moved;
    }

    /** This valuation, this disjunct, and what the run actually paired. */
    private static boolean unsatWith(Composer.Composition composition,
                                     Z3 solver, Outcome outcome,
                                     List<String> observed) {
        if (observed.isEmpty()) return false;
        List<String> pinned =
                new ArrayList<String>(outcome.valuation().assertions());
        pinned.addAll(outcome.pinned());
        pinned.add("(assert " + outcome.selected().selector() + ")");
        pinned.addAll(observed);
        return solver.ask(composition.query(pinned),
                Collections.<String>emptyList(), false).unsat();
    }

    /** Which arm of each family this model set the selector of. */
    private static Map<String, ComposedFamilies.ArmChoice> armsOf(
            Composer.Composition composition, Z3.Answer answer) {
        Map<String, ComposedFamilies.ArmChoice> taken =
                new LinkedHashMap<String, ComposedFamilies.ArmChoice>();
        if (!answer.sat()) return taken;
        for (Map.Entry<String, String> value : answer.values().entrySet()) {
            if (!"true".equals(value.getValue())) continue;
            ComposedFamilies.ArmChoice arm =
                    composition.arm(value.getKey());
            if (arm != null) taken.put(value.getKey(), arm);
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
                GapKind.UNATTESTED_ARM, GapClass.BLOCKING, refused.toString(),
                "this witness moves a root that occurs inside an arm no "
                        + "producer path condition attests, so it is not a "
                        + "supported witness"));
        return true;
    }

    /**
     * One valuation asked for every path selector, family arm selector and
     * clock cell (legalized: {@code Z3.modelQuery} appends names raw), so
     * the claim can read path, delivery and clocks off the model.
     */
    private static Outcome outcome(Composer.Composition composition,
                                   Z3 solver, Composer.Valuation valuation,
                                   List<String> pinned, boolean wantCore) {
        List<String> asked = new ArrayList<String>(composition.selectors());
        asked.addAll(composition.armSelectors());
        for (String cell : composition.clockCells()) {
            asked.add(SmtNames.legalSymbols(cell));
        }
        List<String> assertions =
                new ArrayList<String>(valuation.assertions());
        assertions.addAll(pinned);
        Z3.Answer answer = solver.ask(composition.query(assertions), asked,
                wantCore);
        return new Outcome(valuation, pinned, answer,
                selectedOf(composition, answer), armsOf(composition, answer));
    }

    /** The clock cells whose reading some session states, in order. */
    private static List<String> clockCellsRead(
            Composer.Composition composition) {
        List<String> cells = new ArrayList<String>();
        for (String cell : composition.clockCells()) {
            if (composition.clockReadings().get(cell) != null) cells.add(cell);
        }
        return cells;
    }

    /**
     * The witness under every clock pin it can keep: all cells pinned first;
     * otherwise pin back one at a time in recording order, keeping each pin
     * that stays sat.  The free cells are then a minimal needed set (z3's
     * unsat core is not: it names every pin).
     */
    private static Outcome leastClocks(Composer.Composition composition,
                                       Z3 solver, Outcome outcome,
                                       List<String> cells) {
        if (cells.isEmpty()) return outcome;
        Outcome all = outcome(composition, solver, outcome.valuation(),
                pins(composition, cells), false);
        if (all.answer().sat() && all.selected() != null) return all;
        List<String> kept = new ArrayList<String>();
        Outcome witness = outcome;
        for (String cell : cells) {
            kept.add(cell);
            Outcome asked = outcome(composition, solver, outcome.valuation(),
                    pins(composition, kept), false);
            if (asked.answer().sat() && asked.selected() != null) {
                witness = asked;
            } else {
                kept.remove(kept.size() - 1);
            }
        }
        return witness;
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
     * Whether the seed's own disjunct is unsat at the recorded roots; else
     * the claim is about the recording, not a pairing.  No seed: false.
     */
    private static boolean seedDisjunctUnsat(
            Composer.Composition composition, Z3 solver) {
        String seed = composition.seedSessionId();
        if (seed == null) return false;
        List<String> pinned = new ArrayList<String>();
        Composer.Valuation recorded = composition.valuations().isEmpty()
                ? null : composition.valuations().get(0);
        if (recorded != null) pinned.addAll(recorded.assertions());
        boolean found = false;
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            if (!disjunct.path().sessionId.equals(seed)) continue;
            pinned.add("(assert (! " + disjunct.selector()
                    + " :named seed_disjunct__"
                    + ArtifactIO.digest(disjunct.path().pathId, 10) + "))");
            found = true;
        }
        if (!found) return false;
        return solver.ask(composition.query(pinned),
                Collections.<String>emptyList(), false).unsat();
    }
}
