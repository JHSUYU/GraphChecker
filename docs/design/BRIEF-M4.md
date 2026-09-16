# BRIEF M4 — COMPOSE + CLAIM (Design 3 refactor)

Prerequisite: M1 merged; read CONTRACT-SCHEMA.md, REPORT-M1.md, REFACTOR-D3.md,
DESIGN3-PLAN.md, INTERACTION-ID.md, then REPORT-I1-BISECT.txt, HANDOVER-PERPATH.txt,
REPORT-PHI.md, REPORT-IDENTITY.md, REPORT-READCONJ.md, REPORT-FIELDJOIN.md,
REPORT-ROOTENUM.md, REPORT-RECORDED.md (ClaimPolicy), REPORT-17897-WITNESS.md.

Scope (concolic/ compose side: PathMergeComposer/Lowering, ContainerSmtCodec,
InSessionReadResolver, ClaimPolicy, TargetOccurrenceElection; not explore):
1. Composition per anchor, factorized: for each admitted consumer path p:
   selector_p ⇒ π_p ∧ φ_fatal ∧ reads_p; reads_p per interaction I read by p:
   v_H(I) = answered_p(I) | e_paired(I) (attested arm whose e_q carries a declared-domain
   root) | x_p(I) (p's own session arrival); NOTHING global per phase.
2. Families keyed by interaction (both endpoints): ⋁_q (π_q ∧ guard_q ∧ v_H(I) = e_q),
   guard_q = the producer replay's valuation of ONLY the roots e_q depends on; nested
   v_H in e_q closed transitively (multi-hop transfers along the causal graph); arms
   attested (producer has π) or UNATTESTED (concrete export) — a witness may not move a
   root inside an unattested arm.
3. State joins: read := write version's expression by (writer endpoint, version);
   container-element owners followed by recorded identity; unjoined projections pinned to
   the stated value; unstated ⇒ refuse naming it.
4. Axioms: identities ≠ null, distinct per session; clocks per path, unbounded (≥ 0
   floor only); root domains relative; declared roots enumerated (Boolean over both,
   integral over domain, |δ|-ordered, bounded by --max-valuations); no free symbol other
   than declared roots and clocks (inventory row, fail closed).
5. ClaimPolicy: MARKER_FLIPPED, CLOCK_SKEW (necessary), MESSAGE_PAIRING_FLIPPED
   (fatal-observed explored path sat at the recorded roots via attested arms, seed
   disjunct unsat), RECORDED_FAILURE_EXPLAINED (seed observed the fatal arm), else
   NO_SUPPORTED_WITNESS; FORMULA_SAT_AT_RECORDED_VALUATION alarm blocks. No VALIDATE
   gate (owner ruling): the claim from DECIDE is the verdict; the deliverable is the
   composed .smt2 per anchor + z3's verdict.
6. Election: the declared occurrence, always; no artifacts ⇒ INCONCLUSIVE, never a crash.
7. Delete: pinUnproducedArrivals, per-port root naming, request-family arm filter,
   ranking election, CLOSURE_INCOMPLETE/coverage machinery superseded by per-region
   admission, gap kinds without a consumer.
Tests folded into ONE composer invariant test + ClaimPolicy + election (≤ 80 total):
healthy path unsat at ordinal 0; fatal path sat; two producers same port ⇒ two
families; unattested arm blocks a root move; nested v_H closure; per-path arrivals from
two sessions both admitted. Gate: offline on the round-2 corpora (laneR2A bug3,
laneR2B 17897, laneRB 17960 as control) until M2 recordings exist. Report REPORT-M4.md.
