---
name: delete-first-no-compat
description: Owner ruling 2026-09-14 for the Design 3 refactor — old mechanisms are deleted outright and FIRST; no compatibility layers, adapters or "superseded" stubs.
metadata:
  type: feedback
---

Owner: "旧的代码全部删除，不需要任何兼容层。先做删除". In the Design 3 refactor, every superseded mechanism (linked replay/companions/slices, request-family addressing, phase-keyed handoff families, global pins, per-port naming, coverage/closure gaps, ranking election, single-row importer folds) is deleted end to end — publisher, importer, consumer, tests — before the replacement is written; no adapters.

**Why:** the owner wants a clean architecture, not a layered one; compatibility code is the bloat the refactor exists to remove.
**How to apply:** step D (deletion commits, tree compiles and suite runs after each) precedes M1; later milestones rewrite consumers against the new contract rather than adapting old ones. Keep the 21 workload-called runtime APIs ([[graphchecker-external-callers]]) and mechanisms with live readers. See [[graphchecker-refactor-goal]], [[no-validate-stage]].

**Owner 2026-09-15 15:25 ("为什么还有很多旧的东西。套旧铸址器比如这玩意肯定都给我删干净啊"):** reachability is NOT the deletion criterion — "one implementation per notion" is. A second implementation of identity, expression refs, slot tables, corpus indexes, path ids, clocks, φ carriers, dataflow graphs is deleted even when it has callers (the callers move to the surviving one). Second cleanup pass (after G1/G2): OccurrenceMinterV2 + SEED-side minting (G2), plan/SharedExpressionTable (EXPR.v1), RuntimeRefinedGraphBuilder (→ static_scope_map), compose/SlotTable (→ explore), compose/CorpusIndex (→ explore/Corpus; path ids = OccurrenceAddress.id()), ClockRootPhysics (+ its hadoop clock names), BranchWitness remainder (φ straight into TargetRow), and the selection/planning logic in the six big files beyond "which regions are instrumented, which declared-cell write sites are observed, which wire ports".
