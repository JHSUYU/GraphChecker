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
import edu.uva.liftlab.graphchecker.contract.ReadRow;

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
import java.util.concurrent.TimeUnit;
import java.util.function.Function;

import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.integralLiteral;

public final class ClaimPolicy {

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

        public List<String> pinned() {
            return pinned;
        }

        public Map<String, ComposedFamilies.ArmChoice> selectedArms() {
            return arms;
        }

        public Composer.Valuation valuation() {
            return valuation;
        }

        public Z3.Answer answer() {
            return answer;
        }

        public Composer.Disjunct selected() {
            return selected;
        }

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

        public Z3.Answer formula() {
            return formula;
        }
    }

    private ClaimPolicy() {
    }

    public static Decision decide(Composer.Composition composition,
                                  Z3 solver) {
        return decide(composition, solver, DECIDE_BUDGET_MS);
    }

    static final long DECIDE_BUDGET_MS = 1_800_000L;

    static final int SELF_CHECK_SHARE = 3;

    static Decision decide(Composer.Composition composition, Z3 solver,
                           long budgetMillis) {
        Z3 bounded = solver.until(System.nanoTime()
                + TimeUnit.MILLISECONDS.toNanos(budgetMillis));
        Decision decision;
        try (Disjunction asks = new Disjunction(composition, bounded)) {
            decision = closed(composition, asks, read(composition, asks,
                    budgetMillis / SELF_CHECK_SHARE));
        }
        if (bounded.pastDeadline()) {
            List<GapRow> gaps = new ArrayList<GapRow>(
                    decision.claim().gaps());
            gaps.add(GapRow.of(Composer.COMPOSITION, GapKind.ADMISSION_GAP,
                    GapClass.DIAGNOSTIC, "decide budget " + budgetMillis
                            + "ms", "the claim's questions ran past the "
                            + "composition's decide budget: those asked "
                            + "after it are undecided, named where they "
                            + "are, never a refutation"));
            decision = new Decision(claimWith(decision.claim(), gaps),
                    decision.outcomes(), decision.formula());
        }
        List<String> errors = solver.errors();
        if (errors.isEmpty()) return decision;
        List<GapRow> gaps = new ArrayList<GapRow>(decision.claim().gaps());
        for (String error : errors) {
            gaps.add(GapRow.of(Composer.COMPOSITION,
                    GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC, error,
                    "z3 answered a composed question with an error instead "
                            + "of a verdict: the lowering wrote a name or a "
                            + "literal SMT-LIB does not spell"));
        }
        return new Decision(claimWith(decision.claim(), gaps),
                decision.outcomes(), decision.formula());
    }

    static final String REFUSED_PATH = "z3 refused path ";

    static Set<String> refusedPaths(Claim claim) {
        Set<String> paths = new LinkedHashSet<String>();
        for (GapRow gap : claim.gaps()) {
            if (gap.subject().startsWith(REFUSED_PATH)) {
                paths.add(gap.subject().substring(REFUSED_PATH.length()));
            }
        }
        return paths;
    }

    private static Decision closed(Composer.Composition composition,
                                   Disjunction asks, Decision decided) {
        Claim claim = decided.claim();
        if (claim.kind() != ClaimKind.NO_SUPPORTED_WITNESS
                || composition.disjuncts().isEmpty()) {
            return decided;
        }
        List<GapRow> gaps = new ArrayList<GapRow>(claim.gaps());
        List<Outcome> outcomes = new ArrayList<Outcome>(decided.outcomes());
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
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    composition.anchor().render(), "the composed formula is "
                            + "satisfiable and its model selects no path, "
                            + "so no witness is named and no refutation "
                            + "closed")
                    : GapRow.of(Composer.COMPOSITION,
                    GapKind.UNPRODUCIBLE_ANSWER, GapClass.DIAGNOSTIC,
                    composition.anchor().render(), "the formula is "
                            + "satisfiable only by moving configuration "
                            + unplantable + " whose plant leaves reads of "
                            + "its key at the recording's value, a world no "
                            + "replay can plant: a defect until those reads "
                            + "are planted"));
            return new Decision(claimWith(claim, gaps), outcomes, formula);
        }
        Outcome refined = withMargin(composition, asks, leastClocks(
                composition, asks, witness, composition.clockCells(), false,
                gaps), gaps);
        outcomes.set(outcomes.indexOf(witness), refined);
        return new Decision(Claim.of(ClaimKind.FORMULA_SAT,
                refined.valuation().ordinal(),
                movedRoots(composition, refined), claim.polarityDecides(),
                gaps), outcomes, formula);
    }

    private static boolean asRecorded(Composer.Composition composition,
                                      Outcome outcome) {
        return outcome.selected().path().sessionId.equals(
                composition.seedSessionId())
                && movedRoots(composition, outcome).isEmpty()
                && composition.repaired(outcome.selected().selector(),
                outcome.selectedArms().keySet()).isEmpty();
    }

    private static boolean plantable(Composer.Composition composition,
                                     Outcome outcome,
                                     Set<String> unplantable) {
        Set<String> partial = composition.unplanted(
                outcome.valuation().moved().keySet()).keySet();
        unplantable.addAll(partial);
        return partial.isEmpty();
    }

    private static Claim claimWith(Claim claim, List<GapRow> gaps) {
        return Claim.of(claim.kind(), claim.valuationOrdinal(),
                claim.movedRoots(), claim.polarityDecides(), gaps);
    }

    private static Decision read(Composer.Composition composition,
                                 Disjunction asks, long selfCheckCapMillis) {
        List<GapRow> gaps = new ArrayList<GapRow>(composition.gaps());
        Decision unasked = unasked(composition, gaps);
        if (unasked != null) return unasked;
        Reading reading = new Reading(composition, asks, gaps,
                selfCheckCapMillis);
        Decision claimed = reading.movedRoot(false);
        if (claimed == null) claimed = reading.clockOrPairing();
        if (claimed == null) claimed = reading.movedRoot(true);
        if (claimed == null) claimed = reading.observedElsewhere();
        return claimed != null ? claimed : reading.noWitness();
    }

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

    private static final class Reading {
        private final Composer.Composition composition;
        private final Disjunction asks;
        private final List<GapRow> gaps;
        private final List<Outcome> outcomes;
        private final List<String> cells;
        private final List<String> asHappened;
        private final Outcome asRecorded;
        private final boolean recordingDecides;
        private final boolean clockDriven;
        private final boolean polarityDecides;
        private Outcome recorded;
        private final Set<String> partial = new LinkedHashSet<String>();

        Reading(Composer.Composition composition, Disjunction asks,
                List<GapRow> gaps, long selfCheckCapMillis) {
            this.composition = composition;
            this.asks = asks;
            this.gaps = gaps;
            selfContradictory(composition, asks, gaps, selfCheckCapMillis);
            Disjunction together = asks.asking(Math.min(PARALLEL_ASKS,
                    composition.valuations().size()));
            outcomes = new ArrayList<Outcome>(inParallel(
                    composition.valuations(), valuation -> outcome(
                            composition, together, valuation,
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

        Decision movedRoot(boolean configuration) {
            Decision own = recordingDecides
                    ? movedAsHappened(configuration, true)
                    : movedFree(configuration, true);
            if (own != null) return own;
            return recordingDecides ? movedAsHappened(configuration, false)
                    : movedFree(configuration, false);
        }

        private final Map<Integer, Outcome> settled =
                new LinkedHashMap<Integer, Outcome>();
        private final Map<Integer, List<GapRow>> settledGaps =
                new LinkedHashMap<Integer, List<GapRow>>();

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
                return claimed(mechanism(composition, asks, outcome,
                        clockDriven), outcome);
            }
            return null;
        }

        private boolean ownCandidate(Outcome outcome, boolean configuration) {
            return outcome.valuation().ordinal() != 0 && outcome.witness()
                    && ranked(composition, outcome, configuration)
                    && composition.unplanted(outcome.valuation().moved()
                    .keySet()).isEmpty()
                    && ownPairings(outcome)
                    && composition.ranRoots(outcome.selected(),
                    outcome.valuation().moved());
        }

        private boolean ownRun(Outcome outcome) {
            return ownPairings(outcome) && composition.ranModel(
                    outcome.selected(), movedRoots(composition, outcome));
        }

        private boolean ownPairings(Outcome outcome) {
            return outcome.selected().fatalObserved()
                    && composition.repaired(outcome.selected().selector(),
                    outcome.selectedArms().keySet()).isEmpty();
        }

        private boolean movedWitness(Outcome outcome, boolean configuration) {
            return outcome.valuation().ordinal() != 0 && outcome.witness()
                    && ranked(composition, outcome, configuration)
                    && !unplanted(composition, outcome, partial, gaps);
        }

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

        Decision observedElsewhere() {
            if (recorded == null || !recorded.witness()) return null;
            boolean attested = recorded.selected().fatalObserved()
                    && attestedArms(composition, recorded);
            List<Composer.Disjunct> worlds = worldPairings();
            if (!attested && worlds.isEmpty()
                    || !seedDisjunctUnsat(composition, asks)) {
                return null;
            }
            if (attested) {
                ClaimKind kind = mechanism(composition, asks, recorded,
                        clockDriven);
                if (kind != ClaimKind.NO_SUPPORTED_WITNESS) {
                    return new Decision(Claim.of(kind, 0,
                            movedRoots(composition, recorded), true, gaps),
                            outcomes);
                }
            }
            for (Composer.Disjunct selected : worlds) {
                Outcome witness = worldPairing(selected);
                if (witness == null) continue;
                outcomes.set(0, witness);
                return new Decision(Claim.of(
                        ClaimKind.STATE_PAIRING_FLIPPED, 0,
                        movedRoots(composition, witness), true, gaps),
                        outcomes);
            }
            gaps.add(GapRow.of(recorded.selected().path().sessionId,
                    GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    recorded.selected().path().pathId,
                    "this path of an explored session reaches the fatal arm "
                            + "at the recorded roots and the seed's own "
                            + "disjunct does not, and no state slot, no wire "
                            + "slot, no moved root, no clock and no pairing "
                            + "its world planted is what makes the "
                            + "difference: there is no mechanism to name"));
            return null;
        }

        private List<Composer.Disjunct> worldPairings() {
            List<Composer.Disjunct> worlds =
                    new ArrayList<Composer.Disjunct>();
            List<Composer.Disjunct> all = new ArrayList<Composer.Disjunct>();
            all.add(recorded.selected());
            all.addAll(composition.disjuncts());
            for (Composer.Disjunct disjunct : all) {
                if (disjunct.fatalObserved() && !worlds.contains(disjunct)
                        && !composition.takenPairings(disjunct).isEmpty()) {
                    worlds.add(disjunct);
                }
            }
            return worlds;
        }

        private Outcome worldPairing(Composer.Disjunct selected) {
            String selector = selected.selector();
            List<String> held = composition.worldRun(selected);
            if (held.isEmpty() && composition.offersArms(selector)) {
                return unclaimed(selected, "nothing holds the path to its "
                        + "session's run while a family offers it arms: no "
                        + "delivery of its own, no observed writer arm, no "
                        + "plant");
            }
            Map<String, ReadRow> taken = composition.takenPairings(selected);
            Map<String, Composer.Composition.FatalPath> clauses =
                    new LinkedHashMap<String, Composer.Composition.FatalPath>();
            for (Map.Entry<String, ReadRow> pairing : taken.entrySet()) {
                Composer.Composition.FatalPath clause =
                        composition.onFatalPath(selected, pairing.getValue());
                if (clause == null) {
                    return unclaimed(selected, "the read " + pairing.getKey()
                            + " its world re-paired is off the path's fatal"
                            + " cone: the cone names neither it, nor a store"
                            + " version its occurrence wrote, and it is not"
                            + " the anchor's");
                }
                clauses.put(pairing.getKey(), clause);
            }
            held.addAll(composition.worldClocks(selected));
            Outcome witness = outcomeOn(composition, asks,
                    composition.worldValuation(0, selected), held, false,
                    selector, 0L);
            if (!witness.answer().decided()) {
                return unclaimed(selected, "its own run under its world's "
                        + "plants, roots and clocks is undecided (" + witness
                        .answer().status() + "): no claim rests on it");
            }
            if (!witness.witness()) {
                return unclaimed(selected, "its own run under its world's "
                        + "plants, roots and clocks reaches no fatal arm "
                        + "the formula states");
            }
            Map<String, String> moved = movedRoots(composition, witness);
            Set<Composer.Composition.FatalPath> unnamed =
                    new LinkedHashSet<Composer.Composition.FatalPath>(
                            clauses.values());
            unnamed.remove(Composer.Composition.FatalPath.CONE);
            if (!moved.isEmpty() && !unnamed.isEmpty()) {
                return unclaimed(selected, "a pairing no term names lies on"
                        + " the fatal path only by its occurrence " + clauses
                        + ", and the world moved " + moved.keySet() + " too:"
                        + " nothing shows the pairing is what decides");
            }
            if (!composition.ranWorld(selected, moved, composition
                    .realizedPairings(selected).keySet())) {
                return unclaimed(selected, "the session is not the run of "
                        + "the world the witness names: it planted another "
                        + "root, clock or pairing it did not realize, or "
                        + "minted a moved root elsewhere");
            }
            gaps.add(GapRow.of(selected.path().sessionId,
                    GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    selected.path().pathId, "world-pairing claim: each "
                            + "pairing on the fatal path by " + clauses));
            return witness;
        }

        private Outcome unclaimed(Composer.Disjunct selected, String why) {
            gaps.add(GapRow.of(selected.path().sessionId,
                    GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    selected.path().pathId, "no world-pairing claim on this "
                            + "path: " + why));
            return null;
        }

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

    private static boolean ranked(Composer.Composition composition,
                                  Outcome outcome, boolean configuration) {
        return composition.configurationOnly(
                outcome.valuation().moved().keySet()) == configuration;
    }

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

    private static final String VALUATION_LABEL = "valuation__";

    private static boolean namesAValuation(List<String> core) {
        if (core == null) return false;
        for (String label : core) {
            if (label != null && label.startsWith(VALUATION_LABEL)) {
                return true;
            }
        }
        return false;
    }

    static final int PARALLEL_ASKS = 4;

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

    private static void selfContradictory(Composer.Composition composition,
                                          Disjunction asks,
                                          List<GapRow> gaps,
                                          long capMillis) {
        int undecided = 0;
        long started = System.nanoTime();
        List<Z3.Answer> answers = asks.selfCheck(capMillis);
        for (int at = 0; at < answers.size(); at++) {
            Z3.Answer answer = answers.get(at);
            if (!answer.decided()) undecided++;
            if (answer.status().startsWith("(error")) {
                gaps.add(GapRow.of(Composer.COMPOSITION,
                        GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                        REFUSED_PATH + composition.disjuncts().get(at).path()
                                .pathId, "z3 answered this path's own"
                                + " question with an error: "
                                + answer.status()));
            }
        }
        if (undecided > 0 && capMillis > 0L && System.nanoTime() - started
                >= TimeUnit.MILLISECONDS.toNanos(capMillis)) {
            gaps.add(GapRow.of(Composer.COMPOSITION,
                    GapKind.ADMISSION_GAP, GapClass.DIAGNOSTIC,
                    "self-check cap " + capMillis + "ms",
                    undecided + " of " + composition.disjuncts().size()
                            + " path(s) were not decided within the "
                            + "self-check's part of the decide budget, or "
                            + "its budget a path, and stay in the "
                            + "disjunction unexamined, never refuted on it"));
        } else if (undecided > 0) {
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
                            + (answer.memOut() ? "(" + answer.reason() + ")"
                            : "within " + Disjunction.SELF_CHECK_BUDGET_MS
                            + "ms") + ", so nothing shows it states its own"
                            + " run"));
        }
        if (contradictory == 0) return;
        gaps.add(GapRow.of(Composer.COMPOSITION,
                GapKind.PATH_SELF_CONTRADICTORY, GapClass.DIAGNOSTIC,
                composition.anchor().render(),
                "the composed formula is unsat, and " + contradictory
                        + " of its " + withoutFatalArms.size() + " paths "
                        + "contradict their own run, so the verdict is about "
                        + "the formula it built, not about the recording"));
    }

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
        if (clockDriven) return ClaimKind.CLOCK_SKEW;
        return ClaimKind.NO_SUPPORTED_WITNESS;
    }

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

    private static Outcome outcome(Composer.Composition composition,
                                   Disjunction asks,
                                   Composer.Valuation valuation,
                                   List<String> pinned, boolean wantCore) {
        return outcome(composition, asks, valuation, pinned, wantCore, null);
    }

    private static Outcome outcome(Composer.Composition composition,
                                   Disjunction asks,
                                   Composer.Valuation valuation,
                                   List<String> pinned, boolean wantCore,
                                   Outcome path) {
        return outcome(composition, asks, valuation, pinned, wantCore, path,
                0L);
    }

    private static Outcome outcome(Composer.Composition composition,
                                   Disjunction asks,
                                   Composer.Valuation valuation,
                                   List<String> pinned, boolean wantCore,
                                   Outcome path, long budgetMillis) {
        return outcomeOn(composition, asks, valuation, pinned, wantCore,
                path == null ? null : path.selected().selector(),
                budgetMillis);
    }

    private static Outcome outcomeOn(Composer.Composition composition,
                                     Disjunction asks,
                                     Composer.Valuation valuation,
                                     List<String> pinned, boolean wantCore,
                                     String selector, long budgetMillis) {
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
        Z3.Answer answer = selector == null
                ? asks.ask(assertions, composition.selectors(), asked,
                wantCore)
                : asks.askPath(selector, assertions, asked, wantCore,
                budgetMillis);
        return new Outcome(valuation, pinned, answer,
                selectedOf(composition, answer), armsOf(composition, answer));
    }

    static final long REFINE_BUDGET_MS = 300000L;

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

    private static void refinementCut(List<GapRow> gaps, String step,
                                      List<String> untried) {
        gaps.add(GapRow.of(Composer.COMPOSITION, GapKind.SOLVER_TIMEOUT,
                GapClass.DIAGNOSTIC, step, "the witness's refinement ran "
                        + "out of its " + REFINE_BUDGET_MS / 1000L + " s "
                        + "with " + untried.size() + " cell(s) untried, "
                        + "which it publishes as they stand: " + untried));
    }

    private static Outcome withMargin(Composer.Composition composition,
                                      Disjunction asks, Outcome witness,
                                      List<GapRow> gaps) {
        Map<String, String> model = witness.answer().values();
        List<String> margins = new ArrayList<String>();
        for (String cell : composition.clockCells()) {
            Long jumped = jump(composition, model, cell);
            if (jumped == null || jumped == 0L) continue;
            boolean later = jumped > 0L;
            long margin = ClockMargin.margin(
                    composition.clockNanos().get(cell));
            margins.add("(assert (! " + Composer.clockStep(cell,
                    composition.clockReadings(), composition.clockBefore(),
                    later ? ">=" : "<=", later ? jumped + margin
                    : jumped - margin) + " :named clock_margin__"
                    + ArtifactIO.digest(cell, 10) + "))");
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
