---
name: handoff-family-phase2
description: Owner's handoff-anchor "family" idea (2026-09-13 22:xx) — assessed as a legitimate phase-2 mechanism (per-node exploration joined by substitution at the VM-recorded handoff occurrence); data and rules; not for now
metadata:
  type: project
---

Owner idea: wrap an anchor at every handoff; expressions still propagate by value; the received value is also a fresh symbol v; family(anchor) = {(π_p, e_p)} producer paths; Fatal = ⋁_p ⋁_q (π_p ∧ π_q ∧ v = e_p ∧ φ_q). Producer/consumer flips explored independently (m+n replays, per-node parallel), joined at the anchor.

**Study ($SP_NEW/d-explore/HANDOFF-FAMILY-STUDY.md, origin/main 3d9355745):** the exact half already exists and is used — VM_HANDOFF_EVENT (portId, exportEventId, attachEventId, expression at attach, producer task/occurrence as provenance); InSessionReadResolver substitutes by attachEventId. The old "family" (CBF key = hash(epoch, occurrence, port, per-port ordinal); uniqueProducerCase index search; per-arm selectors + exactlyOne) was stitching and is gone.

**Missing for phase 2:** (1) a fresh v per handoff occurrence (keyed on attachEventId alone); (2) consumer-side obligations over v (v as a materializable replay control like a configured source); (3) join exactness: v = e_p only for the SAME (exportEventId, attachEventId) pair — no port+ordinal, no "unique producer case"; loops → one v per turn scoped by the loop policy.

**Data:** bug3 laneVM10: 12 obligations, 9 on nn0 (producer), 1 on the DN target; 124/379 summaries carry handoffs → join matters. 17960: 0 handoffs (single node) → buys nothing; its difficulty is control dependence (concrete φ) — already handled by ⋁ over paths.

**Decision (planner, agreed with owner's framing):** worth doing as a designed phase-2 mechanism (matches the paper's topology epochs and per-node parallel waves), AFTER: six cases pass on the base design; occurrence identity → trace positions (handoff occurrences included); cheap speedups (parallel waves, obligation dedupe, incremental z3, SEED reuse). In-VM ite merging of side-effect-free branches ("guarded version" retention) parked after that. See [[graphchecker-core-design-principle]].

**Owner override 2026-09-13 22:30:** "我依然要把我们讨论的优化作为第一优先级…简洁的修改代码…不要过度设计验证…旧的代码全部移除" — handoff-anchored merging is P1 NOW, not phase 2. Plan: $SP_NEW/HANDOFF-MERGING-PLAN.md (R1 runtime handoff mint + answering; R2 concolic obligations over v_H; R3 family constraint at compose, join by H only; R4 delete eager attach substitution / cross-node companion linking / boundary-family vocabulary; minimal tests + one bug3 campaign).
