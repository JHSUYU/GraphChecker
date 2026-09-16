---
name: planner-judge-against-reference-design
description: Owner instruction 2026-09-13 19:05 — hold the reference design in mind at all times; judge every component/fix against it; discard what is not derivable and call a stop early instead of patching
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3230912f-3427-4c18-a306-eb2005a43b37
  modified: 2026-09-14T00:05:28.842Z
---

Owner: "你先要对整个design合理的设计有一个大概的认识。这样很多不合理的设计你都可以摒弃了。你就可以做抉择及时叫停。"

**Why:** on 2026-09-13 the planner spent hours (a) patching symptoms of one structural defect five times (occurrence identity), (b) directing stitching workarounds (portable leaves, arm synthesis) before checking them against the design, and (c) deferring a designed consolidation "until after results". Each time the reference design would have said: not derivable → delete / consolidate now.

**The reference design (see [[graphchecker-core-design-principle]]):**
roots manual → in-JVM propagation (VM handles; carriers from the root-dependence slice; wire attach by message element) → each replay publishes root mints, root-dependent decisions (π), fatal predicate at the anchor (φ), write log, wire handoffs → EXPLORE flips root-dependent decisions on resolved π → COMPOSE: Fatal_T = ⋁_p(π_p ∧ φ_p) per anchor → z3 → 4 gates + finding kinds. Identity: one OccurrenceAddress (node, epoch, region, k-th activation in the recording window); objects by real VM identity. The graph only scopes.

**How to apply (planner checklist before assigning or approving anything):**
1. Which box of the reference design does this component/fix live in? If none → it is not derivable → delete it (or stop the work), do not fix it.
2. Does the fix decide "what matters" outside the slice, choose among writers, or synthesize a value? → reject.
3. Is this the second appearance of the same defect in different clothes? → stop patching; do the structural fix now, even if "results" are close.
4. Does the codebase carry two implementations of one notion (identity, clock, expression table, gap ledger)? → consolidate to one before anything else that depends on it.
5. A recorded value, ordinal, clock, or identity that has to be guessed or defaulted → the producer must publish it; refuse meanwhile.
6. Prefer deleting a mechanism over adding a gate for it; prefer one campaign after a complete round over a campaign per patch.
