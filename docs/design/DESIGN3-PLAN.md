# DESIGN3-PLAN — region-local propagation + anchor-based global merging, phased

Owner's frame (2026-09-14): every region is explored with its own focus; RPC values
are cut at anchors (record e_p, then mint v_H and continue locally); families collect
real producer alternatives per anchor; the target region discovers its own (possibly
nested) fatal condition by local concolic exploration with handoff substitution;
offline merging composes local summaries along the causal graph's partial order in a
FACTORIZED formula (C family ∧ B transfer ∧ A target, shared intermediate v_H); a
solved model is a candidate until an end-to-end replay with only real roots
materializes it (solve → materialize → validate).

## 0. What we already are, and where we deviate

| Design 3 element | GraphChecker today | deviation to remove |
|---|---|---|
| record-then-cut at the RPC boundary | export records e_p (unconditional); attach mints v_H; consumer propagates only v_H | none |
| anchor H | OccurrenceAddress + handoff phase id (port, consumer occurrence, k) | identity v1 (request family @node); v2 = lineage (IDENTITY-V2) |
| family ⋁_q (π_q ∧ v_H = e_q) | PathMergeComposer families | arms guarded by unrelated roots (R-GUARD); arms only from producers in the anchor's request family (NNCHAIN) → pair by anchor, not family; unproduced arrivals pinned globally (R-PIN) → per path |
| target-local exploration with substituted handoff values | answered handoffs applied at the attach; obligations flip one decision per wave | E1 prefers producible answers; unproducible ones are hypotheses flagged `unproducible` and rejected at merge (allowed, not preferred) |
| one focused region per replay | "linked replay": primary + companions symbolic in one run; admission couples them (an NN loop-prefix mismatch rejects the DN primary) | Phase 2: one focused occurrence (or one state-connected factor) per replay; everything else concrete/propagation-only |
| offline merge along the graph's partial order | one composed query per anchor with families as global assertions | after R-PIN/R-GUARD/R-READ the formula is factorized per path; multi-hop transfers (e_B over v_CB) must be published as arms over input handoffs (Phase 3) |
| solve → materialize → validate | DECIDE accepts on polarity + domains; no final replay | Phase 1: VALIDATE stage — end-to-end replay with roots = model, no substitution; anchors must deliver the model's values and the target must throw; else admission gap / divergence |
| parallel workers per region, merge per wave | 8 obligation workers per wave, each a full linked replay | Phase 2/5: tasks = focused regions; waves = union of frontiers; merge per wave |
| state-connected factor | DN's allKeys writers + target explored together (linked) | keep as one unit until state-version anchors exist |

## 1. Phase 0 (in flight) — composer soundness on round-2 corpora
R-PIN, R-GUARD, R-READ, MESSAGE_PAIRING_FLIPPED; E1 out-of-arm answer fix. Verdicts by
offline re-judge. Gate: 17897 and bug3 fatal-observed paths satisfiable at a valuation
the recorded polarity decides.

## 2. Phase 1 — VALIDATE (materialize the model) — DROPPED by owner ruling 2026-09-14: no confirmation replay; the composed .smt + z3 verdict is the deliverable.
Input: accepted valuation (roots δ, markers) and the selected path set. Run one
end-to-end replay with ONLY root assignments (configured-source valuation), no handoff
answers, no branch forcing. Check at every anchor of the selected paths that the
delivered value equals the model's e_q value; check the anchor occurrence throws the
annotated exception. Outcomes: CONFIRMED (finding); same anchors, different producer
path → not confirmed, path joins the next wave; anchor missing → admission gap;
new RPC/retry/binding → topology divergence → new epoch. Reuse: valuation replays
already exist (SEED runs with CONFIGURED_SOURCE_FIELD valuations); add the anchor
delivery check and the claim gate. Size: run_engine stage + ClaimPolicy gate + one row
kind. Tests folded (61 cap).

## 3. Phase 2 — focused-region replays (handoff-family phase 2)
Task = one occurrence symbolic (or one state-connected factor: writers and readers of
one concrete location on one node); all other regions concrete with exports recorded
and attaches minting v_H (entry rule: mint at every declared port, address from
context). Obligations per focused region; admission per region — an NN-side loop
mismatch no longer rejects a DN task. Arms are paired by anchor (port + consumer phase
↔ export row), never by request family; a producer with no π (unselected tick) yields
an arm flagged PRODUCER_PATH_UNATTESTED and a witness may not move roots inside it.
Gate: bug3's NN rotation explored as its own worker (needs the daemon-tick address:
IDENTITY-V2 §1/§2 or the entry rule's addressing half); REPLAY_NOT_ADMITTED counts
drop to zero on DN tasks.

## 4. Phase 3 — multi-hop transfers along the graph
A consumer region's exported expression may mention its own input handoffs
(e_B(v_CB)). Publish such exports as arms over input v_H; the composer chains
C family → B transfer → A target with shared v_H symbols; merge order = value-flow
partial order of the causal graph; a B path requiring v_CB = 10 with no C arm
delivering 10 is UNSAT, not explored again. Test case: bug1's second hop once the SASL
scope lifetime fix lands (DN→DN).

## 5. Phase 4 — identity v2 and scope
Lineage addresses (IDENTITY-V2), Server.Call scope carry, SASL inbound scope lifetime
= DataXceiver op; daemon-tick roots. This is what makes Phase 2's workers nameable on
every case.

## 6. Phase 5 — scheduling
Region tasks distributed across JVMs/machines; waves collect per-region frontiers;
epochs fork the skeleton on divergence. Cost model: replays ≈ Σ local paths, not Π.

## 7. Related-work positioning (one line)
Distributed slicing + partial re-execution (Duesterwald/Gupta/Soffa '92) reproduces
the SAME failure from a dependence graph; we explore COUNTERFACTUALS: the graph is
target-directed, refined per epoch, and its nodes carry symbolic summaries that are
composed into one SMT query, with a materializing replay as the oracle.
