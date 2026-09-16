# REPORT-M4 — COMPOSE + CLAIM (edu.uva.liftlab.graphchecker.d3.compose)

Transcribed by the planner from the M4 agent's final message (its harness refused .md).
Branch refactor/d3-compose, worktree SPN/wt-d3-compose. Merged: staging 122bf2133 (D+M5),
contract 0fb76bc23 and v1.1 6f741ef79. TIP 317983a23. Gates: 68 @Test green;
candidate.smt2 parses in z3 4.8.12; ComposeMain smoke passes the shell's
campaign_require_claim / campaign_print_symbolic_variable_models jq contracts.

## Files (d3/compose, 8,092 main + 404 test)
Written: Composer 1244, SmtLowering 1027, ComposeMain 536, CorpusIndex 497, Solver 348,
ClaimPolicy 339, SessionReader 150, VmRows 137, JsonText 125 — 4,403.
Moved from concolic/ (D2 deletes the originals): ContainerSmtCodec 2418, VmLoweringCore
993, JavaPrimitiveSmtSemantics 635, VmTermLowering 518, VmExpressionIr 411,
JavaContainerTypes 266, JsonFields 235, JavaPrimitiveBoxing 101, JavaSmtSorts 84,
SmtSymbolTable 42 — 5,703. Test D3ComposerTest 404 (6 @Test). d3 imports nothing outside
d3.contract.

## The rule
exactly-one(selector_p); selector_p ⇒ π_p ∧ φ_p ∧ reads_p ∧ joins_p ∧ valuation_p;
selector_p ⇒ family(I) for every interaction I that p's chain reaches; root domains,
clock floors (>= 0), identity axioms. reads_p = answered, else the paired arm when
attested and carrying a movable root (R-READ), else this session's own arrival (R-PIN).
family(I) = ⋁_q (π_q ∧ guard_q ∧ v_H = e_q) over producers whose run paired that export
with this consumer (R-I2); guard_q over only the roots e_q depends on (R-GUARD); arms
flagged attested (R-I5); nested v_H closed transitively. φ_p is the published fatal arm.

## Reused / dropped
Reused: PathMergeLowering policy (definedness, container-DAG naming, identities non-null
+ distinct per session, ContainerSmtCodec.Host JOIN/PIN/UNSTATED policy, integral-domain
side conditions, free-term-on-refusal), InSessionReadResolver's observed-version rule,
selector partition, ConcolicConstraintSolver.run's z3 launch with in-JVM timeout.
Dropped: pinUnproducedArrivals, per-port root naming, request-family arm filter, ranking
election, clock windows, self-consistency binary search.

## Deviations
1. Families conjoined under their consumer's selector, not globally (I1-BISECT §2–3).
2. Arm guard = producer's decisions with seq < export.seq.
3. Clocks >= 0, no window; --clock-skew-ms accepted and ignored.
4. "One name per root" is the runtime's obligation; two rootIds sharing a symbol =
   BLOCKING gap.
5. A published term naming an undeclared symbol refuses its path (free-symbol inventory).
6. Gap classes: a refusal removing a path/arm is DIAGNOSTIC; BLOCKING = symbol collision,
   unreached anchor, UNATTESTED_ARM on an accepted witness, recorded-valuation alarm.
7. GapRow.sessionId = "composition" for composer-raised gaps.
8. The seed session = the one that focused nothing (ActivationRow.focused).
9. candidate.smt2 carries valuation 0's pins; others differ only in valuation__*.
10. A varied root with no declared domain is not pinned globally (DIAGNOSTIC gap).
11. --runtime-plan accepted, not read.

## run_engine.sh mismatches (for M5)
- do_reach still shells to concolic.RootValuationSolver (deleted by D2); ComposeMain
  already solves and writes .solver.* into the manifest → SOLVE stage becomes a no-op or
  re-reads the manifest.
- campaign_artifact_digests requires gaps.json and gap_ledger.json; the shell builds them
  from .gaps / .claim.gaps / .finalStatusRefusals, all published by the manifest.

## Explore-branch API (served)
SmtLowering.of(ExpressionTable), forSession(SessionReader), lower(ref) → Lowered{ok(),
text(), refusal(), declarations()}, sortOf(javaType) — the placeholder's surface.

## Tests (6)
polarity (ordinal 0 unsat, flip sat, MARKER_FLIPPED); two producers one port ⇒ two
families; root move inside an unattested arm refused (UNATTESTED_ARM); nested v_H closure;
two sessions' arrivals both self-consistent; unreached declaration ⇒
NO_SUPPORTED_WITNESS + DECLARATION_MISSING.
