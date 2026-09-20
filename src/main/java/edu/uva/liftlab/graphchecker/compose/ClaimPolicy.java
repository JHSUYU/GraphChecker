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
 *   <li><b>CLOCK_SKEW</b> -- the fatal arm is reached with no DECLARED root
 *       moved, and only because a clock cell may sit elsewhere: pinning
 *       every cell to what its session read makes it unsat.  A clock that
 *       is not necessary is a decoration, never the mechanism.  The cells
 *       the model put elsewhere are the witness's moved roots ({@link
 *       Claim#movedRoots}, read in {@link #movedRoots}): a clock has a
 *       floor and no window, so no valuation pins one and the model is the
 *       only thing that can say where it had to sit.  A MARKER moved is
 *       MARKER_FLIPPED and is asked first -- {@link #mechanism} names the
 *       narrowest mechanism the evidence supports, and a clock beside a
 *       moved marker is not what made the difference.  A recorded
 *       valuation the clock pin refutes is decided by that pin and not by
 *       the moved-root loop, which asks whether ANOTHER declared root
 *       explains the difference and answers "no" about every clock witness
 *       there could be.</li>
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
        private final Z3.Answer answer;
        private final Composer.Disjunct selected;
        private final Map<String, ComposedFamilies.ArmChoice> arms;

        Outcome(Composer.Valuation valuation, Z3.Answer answer,
                Composer.Disjunct selected,
                Map<String, ComposedFamilies.ArmChoice> arms) {
            this.valuation = valuation;
            this.answer = answer;
            this.selected = selected;
            this.arms = Collections.unmodifiableMap(arms);
        }

        /**
         * Arm selector -> the delivery this model rested on.
         *
         * <p>Only where the model set the selector: a family is a case
         * split with exactly-one over its arms, so a sat model names one
         * arm per family it reached and nothing for the families the
         * selected path did not open.</p>
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
                                 Z3 solver) {
        List<GapRow> gaps = new ArrayList<GapRow>(composition.gaps());
        List<Outcome> outcomes = new ArrayList<Outcome>();
        if (composition.disjuncts().isEmpty()) {
            // The declared occurrence is the anchor, always; one no session
            // reached is a claim about the corpus, never an exception.
            return new Decision(Claim.of(ClaimKind.NO_SUPPORTED_WITNESS, 0,
                    Collections.<String, String>emptyMap(), false, gaps),
                    outcomes);
        }
        // WHAT A SAT MODEL MUST CARRY BACK: the selectors, so the claim
        // can say which disjunct it is about, and every CLOCK CELL, so it
        // can say where the clocks had to sit.  A clock has a floor and no
        // window, so no valuation pins one and no valuation can report one
        // either: the only statement of where a witness put a clock is the
        // model.  Legal spelling here and not at the query boundary --
        // Z3.modelQuery appends the names raw, and a cell is spelled
        // CLOCK/... .
        List<String> selectors = composition.selectors();
        List<String> asked = new ArrayList<String>(selectors);
        // AND EVERY FAMILY ARM SELECTOR.  A witness over a slot has to say
        // which delivery it rested on; the manifest publishes it per
        // family, and a claim that cannot name the arm names a mechanism
        // whose evidence is an anonymous disjunct.
        asked.addAll(composition.armSelectors());
        for (String cell : composition.clockCells()) {
            asked.add(SmtLowering.legalSymbols(cell));
        }
        for (Composer.Valuation valuation : composition.valuations()) {
            Z3.Answer answer = solver.ask(
                    composition.query(valuation.assertions()),
                    asked, valuation.ordinal() == 0);
            outcomes.add(new Outcome(valuation, answer,
                    selectedOf(composition, answer),
                    armsOf(composition, answer)));
        }
        Outcome recorded = outcomes.isEmpty() ? null : outcomes.get(0);

        // A PATH IS A QUESTION, NOT A CONTRADICTION.  Asked of each
        // disjunct on its own, with every root FREE: unsat here says
        // nothing about the roots, because there was no world of the
        // formula to put them in.  The one that shipped for two rounds was
        // pi_p carrying the anchor decision's recorded polarity beside
        // phi_p's complement of it (Composer, rule P1), and it is exactly
        // the shape no other check could see: every valuation came back
        // unsat, the claim read that as "the recording decides the arm",
        // and z3's core named only path_fatal__* and fatal_target.
        selfContradictory(composition, solver, gaps);

        // A valuation the solver did not decide is NAMED, and it blocks.
        // Neither a witness nor a refutation is closed over it, and the
        // manifest used to carry it as a bare `state=unknown` with nothing
        // to route: 17960's moved valuation sat there for 141 s and came
        // back "(incomplete quantifiers)", which says the fragment the
        // lowering wrote, not anything about the recording.
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

        // The alarm: the run as it happened reaches the fatal arm on a path
        // whose own recording took the healthy one.
        //
        // Unless the CLOCKS are what reach it.  The alarm asks "what does
        // this witness add?", and a valuation cannot pin a clock -- a clock
        // has a floor and no window, so it is free in every valuation
        // including ordinal 0 -- which makes the alarm's premise true of
        // every clock witness there could be.  What answers the question
        // for a clock is the clock pin, asked once, in #clockNecessary; on
        // a corpus with no clock cell it is false without a solver run, so
        // nothing else changes.
        //
        // THE SAME ANSWER IS WHAT SAYS THE WITNESS IS CLOCK-DRIVEN, so it
        // is asked ONCE, here, and read twice: by the alarm below and by
        // loop 1, which steps aside for a clock-driven recorded valuation
        // (see there).  Two asks would be two solver runs on one question.
        boolean clockDriven = recorded != null && recorded.answer().sat()
                && recorded.selected() != null
                && clockNecessary(composition, solver, recorded);
        if (recorded != null && recorded.answer().sat()
                && recorded.selected() != null
                && !recorded.selected().fatalObserved()
                && !clockDriven) {
            gaps.add(GapRow.of(recorded.selected().path().sessionId,
                    GapKind.FORMULA_SAT_AT_RECORDED_VALUATION,
                    GapClass.BLOCKING,
                    recorded.selected().path().pathId,
                    "this disjunct is satisfiable with every declared root "
                            + "at its recorded value, and its own recording "
                            + "took the healthy arm"));
        }

        // POLARITY DECIDES ONLY WHEN A VALUATION IS WHY.  "The run as it
        // happened does not reach the fatal arm" is a statement about the
        // recorded ROOTS, so the refutation has to rest on them: an unsat
        // whose core names no valuation assertion refuted the path's own
        // conjunction and would have refuted it under every valuation
        // there is.  11741 campaign #4 reported polarityDecides=true off a
        // core of path_fatal__0..6 + fatal_target, which is a statement
        // about the composition and not about the recording; 17960's
        // core names valuation__M_Z_field_SRC_... and still decides.
        boolean polarityDecides = recorded != null
                && recorded.answer().unsat()
                && namesAValuation(recorded.answer().core());

        // 1. A declared root moved inside its domain.
        //
        // Polarity is a CONDITION on this claim and not a field beside it.
        // "These controls plus this rotation reach the failure" says nothing
        // unless the run as it happened does NOT reach it: a formula that is
        // satisfiable at the recorded valuation was satisfiable all along,
        // and the rotation explained nothing about the difference.
        //
        // NOT ASKED AT ALL OF A CLOCK-DRIVEN RECORDED VALUATION.  Where the
        // clock pin is what refutes the recorded valuation, the polarity
        // that decides the claim is the clock's own (class doc, CLOCK_SKEW)
        // and this loop's `!polarityDecides` is a question about the moved
        // ROOTS -- whose answer is "sat" for any other windowed root the
        // case happens to declare, since moving one does the clock witness
        // no harm.  11741 is exactly that corpus: ordinal 0 sat with the
        // clocks free, ordinals >= 1 sat as well, so this loop filed the
        // blocking FORMULA_SAT_AT_RECORDED_VALUATION about a witness whose
        // mechanism it never asked about, and CLOCK_SKEW could not be
        // published beside a blocking alarm.  Loop 2 asks the clock
        // question, so a clock-driven composition goes straight there.
        if (!clockDriven) {
            for (Outcome outcome : outcomes) {
                if (outcome.valuation().ordinal() == 0) continue;
                if (!outcome.answer().sat() || outcome.selected() == null) {
                    continue;
                }
                Set<String> refused = unattested(composition, outcome);
                if (!refused.isEmpty()) {
                    gaps.add(GapRow.of(outcome.selected().path().sessionId,
                            GapKind.UNATTESTED_ARM, GapClass.BLOCKING,
                            refused.toString(),
                            "this witness moves a root that occurs inside an "
                                    + "arm no producer path condition "
                                    + "attests, so it is not a supported "
                                    + "witness"));
                    continue;
                }
                // This valuation MOVED a declared root, which is
                // MARKER_FLIPPED's own evidence, so #mechanism answers with
                // that or with the narrower slot it also replaced -- never
                // with NO_SUPPORTED_WITNESS.
                ClaimKind moved = mechanism(composition, solver, outcome,
                        outcomes);
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
            // The witness that moves nothing: its mechanism is the clocks
            // it needs or the slot it replaces.  RECORDED_FAILURE_EXPLAINED
            // is not this branch's -- the recording's own failure is asked
            // below, with the polarity of the flips.
            ClaimKind still = mechanism(composition, solver, outcome,
                    outcomes);
            if (still != ClaimKind.CLOCK_SKEW
                    && still != ClaimKind.STATE_PAIRING_FLIPPED
                    && still != ClaimKind.MESSAGE_PAIRING_FLIPPED) {
                continue;
            }
            // CLOCK_SKEW carries its OWN polarity and this is the rule that
            // says so (class doc: "pinning every cell to what its session
            // read makes it unsat").  Asking `recorded.answer().unsat()`
            // of it asks a different question -- whether the fatal arm is
            // reached at the recorded ROOTS with the clocks already free --
            // and whenever a clock is what does the work the answer is
            // "sat", so the claim could never be published: it never has
            // been, in 52+ manifests.
            if (still != ClaimKind.CLOCK_SKEW && !polarityDecides) {
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
                        outcomes);
                return new Decision(Claim.of(kind, 0,
                        movedRoots(composition, recorded),
                        kind != ClaimKind.RECORDED_FAILURE_EXPLAINED
                                && kind != ClaimKind.NO_SUPPORTED_WITNESS,
                        gaps), outcomes);
            }
            if (!seed && attestedArms(composition, recorded)
                    && seedDisjunctUnsat(composition, solver)) {
                // A path of an EXPLORED session reaches the fatal arm at
                // the recorded roots while the seed's own disjunct does
                // not.  WHICH mechanism differs is not stated by that
                // fact: it is the pin tests inside #mechanism, and where
                // neither fires nothing has been established -- the claim
                // this branch used to publish named a wire pairing over a
                // composition with no wire family at all.
                ClaimKind kind = mechanism(composition, solver, recorded,
                        outcomes);
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

    /**
     * The label every valuation pin carries ({@code Composer}'s spelling).
     */
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
     * Every path whose OWN conjunction is unsatisfiable, named.
     *
     * <p>One solver run per disjunct, with its selector forced and no
     * valuation assertion at all.  BLOCKING, because a composition that
     * refutes its own paths answers every question about every root the
     * same way and states nothing: the claim it publishes is about the
     * formula it built.</p>
     */
    private static void selfContradictory(Composer.Composition composition,
                                          Z3 solver, List<GapRow> gaps) {
        int inert = 0;
        for (Composer.Disjunct disjunct : composition.disjuncts()) {
            List<String> forced = new ArrayList<String>();
            forced.add("(assert (! " + disjunct.selector()
                    + " :named path_alone__"
                    + ArtifactIO.digest(disjunct.path().pathId, 10) + "))");
            Z3.Answer answer = solver.ask(composition.query(forced),
                    Collections.<String>emptyList(), false);
            if (!answer.unsat()) continue;
            inert++;
            // DIAGNOSTIC per path, because one such path is a statement
            // about THAT path: no world of this corpus reaches the fatal
            // arm along it, which may be a fact about the corpus and not a
            // defect -- 17960's third path is fatalObserved=false and its
            // container joins refute the fatal read whatever the marker
            // is, while the claim is found on the other two.  What is NOT
            // allowed is a claim whose POLARITY rests on such a
            // refutation, and that is asked separately (#namesAValuation).
            gaps.add(GapRow.of(disjunct.path().sessionId,
                    GapKind.PATH_SELF_CONTRADICTORY, GapClass.DIAGNOSTIC,
                    disjunct.path().pathId,
                    "this path's own conjunction is unsatisfiable with "
                            + "every root free, so no valuation of any root "
                            + "could have satisfied it and it contributes "
                            + "nothing to the disjunction; z3 closed on "
                            + answer.core()));
        }
        if (inert > 0 && inert == composition.disjuncts().size()) {
            // EVERY path inert: the disjunction is false in every world of
            // the corpus, so the composition answers every question about
            // every root the same way and states nothing at all.  That is
            // the shape that shipped for two rounds on hdfs-11741 and the
            // one no other check could see.
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
                        : recorded.selected().path().sessionId,
                GapKind.FORMULA_SAT_AT_RECORDED_VALUATION,
                GapClass.BLOCKING, kind.name(),
                "the formula shows " + kind + ", and it is satisfiable with "
                        + "every declared root at its recorded value too, so "
                        + "the recording does not decide the arm"));
    }

    /**
     * THE MECHANISM this witness's own EVIDENCE names.
     *
     * <p>A findingKind names a mechanism, so a claim may name one only
     * where the evidence for that mechanism is in this composition.  One
     * routine asks, in the order of how narrow the claim is, and there is
     * no parameter a caller can hand it to name a mechanism the witness
     * does not show:</p>
     *
     * <ul>
     *   <li>STATE_PAIRING_FLIPPED -- pin the versions the selected path's
     *       reads OBSERVED and the query is unsat: the witness needs a
     *       different eligible attested writer, a REPLACED STATE SLOT.</li>
     *   <li>MESSAGE_PAIRING_FLIPPED -- the same for the values its attaches
     *       ARRIVED at: a REPLACED WIRE SLOT.  Asked second because a
     *       witness that needs both is about the interleaving, and the wire
     *       pairing it also happens to use is not what makes it one.</li>
     *   <li>MARKER_FLIPPED -- the valuation MOVED a declared root inside
     *       the domain the case declared.</li>
     *   <li>CLOCK_SKEW -- nothing moved and the clocks are NECESSARY:
     *       pinning every clock cell to the instant its session read makes
     *       the query unsat.</li>
     *   <li>RECORDED_FAILURE_EXPLAINED -- the SEED path reached the fatal
     *       arm at the recorded valuation and every valuation that moved a
     *       root is decided and unsat.  Not a mechanism the checker found:
     *       the recording is the evidence.</li>
     *   <li>NO_SUPPORTED_WITNESS -- none of them.  Refused by name, and
     *       never a default: the branch this replaced handed
     *       MESSAGE_PAIRING_FLIPPED to a non-seed fatal-observed path whose
     *       composition had families=0 and no wire row at all, which is
     *       verification #6's wrong claim.</li>
     * </ul>
     */
    private static ClaimKind mechanism(Composer.Composition composition,
                                       Z3 solver, Outcome outcome,
                                       List<Outcome> outcomes) {
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
        if (clockNecessary(composition, solver, outcome)) {
            return ClaimKind.CLOCK_SKEW;
        }
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
     * WHICH ROOTS THIS WITNESS MOVED -- the one statement of it.
     *
     * <p>Two halves, and the claim has to carry both or it names a
     * mechanism it does not exhibit:</p>
     *
     * <ul>
     *   <li>the roots the VALUATION moved, which the enumeration asked for
     *       and pinned;</li>
     *   <li>the CLOCK CELLS the model put somewhere other than the instant
     *       its session read.  A clock has a floor and no window, so it is
     *       free in every valuation including ordinal 0 and no valuation
     *       can pin one; where it had to sit is stated by the model and by
     *       nothing else.  CLOCK_SKEW was published with {@code
     *       movedRoots {}} -- 11741 campaign #3's own claim -- which reads
     *       as "nothing had to move" about the one finding whose whole
     *       content is that something did.</li>
     * </ul>
     *
     * <p>A cell the model did not answer for, or answered at the recorded
     * instant, is not stated: it is a clock the witness did not need, and
     * {@link #clockNecessary} is what says whether any of them were.  A
     * claim that names no witness states no moved roots at all, which is
     * why the three NO_SUPPORTED_WITNESS returns hand an empty map rather
     * than asking this.</p>
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
        pinned.add("(assert " + outcome.selected().selector() + ")");
        pinned.addAll(observed);
        return solver.ask(composition.query(pinned),
                Collections.<String>emptyList(), false).unsat();
    }

    /** Which disjunct a sat model selected, or null when it named none. */
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
                                          Z3 solver, Outcome outcome) {
        if (composition.clockCells().isEmpty()) return false;
        List<String> pinned =
                new ArrayList<String>(outcome.valuation().assertions());
        for (String cell : composition.clockCells()) {
            Long reading = composition.clockReadings().get(cell);
            if (reading == null) continue;
            pinned.add("(assert (! (= " + cell + " "
                    + integralLiteral(Long.toString(reading))
                    + ") :named clock_pinned__"
                    + ArtifactIO.digest(cell, 10) + "))");
        }
        Z3.Answer answer = solver.ask(composition.query(pinned),
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
