---
name: shrink-after-17960
description: Owner ruling 2026-09-15 — once hdfs-17960 runs end to end on Design 3, the NEXT priority is deleting code (before the other five cases); audit evidence in d-refactor/REPORT-SHRINK.md
metadata:
  type: feedback
---

Owner: "17960跑通后优先删代码". Order after the first end-to-end PASS on 17960: deletion pass first, then the remaining five cases.

**Why:** the refactor replaced 36K lines of concolic/contract with 35K of d3, so src/main is 76.4K vs 71.5K on main; the owner wants the volume down, not just the structure clean.
**How to apply:** use [[graphchecker-refactor-goal]]'s shrink list (ConcolicRegionRuntime 7.8K, d3/plan 14.6K incl. ConcolicScheduler 3.4K and the eight branch-record types, RuntimeSelectedRegionFinalizer 4.5K, RuntimeRegionPlanner 3.7K, run_engine.sh dead functions) and the measured reachability tables in REPORT-SHRINK.md; delete dead classes/methods outright ([[delete-first-no-compat]]), keep the 21 workload-called runtime statics ([[graphchecker-external-callers]]), suite ≤ 80 @Test ([[test-count-cap]]); target src/main < 60K.

**Reaffirmed 2026-09-15 07:50 (owner: "17960完后，做一次代码的清理。把旧代码，兼容层,fallback全部删除"):** immediately after 17960 passes acceptance, run the cleanup round before any key case: delete old code, every compatibility layer, every fallback. Concrete inventory accumulated this session (besides REPORT-SHRINK.md and the refactor/d3-shrink WIP diff): dead `contract/ExpressionTable.REFERENCE_PREFIX`; `d3/plan/ClockRootPhysics` window/manifest/unbounded (no callers); `ComposeMain:55` javadoc for a removed option; `d3/plan/SharedExpressionTable`'s second expression-ref spelling; the P2d stamp remnants already deleted; P2c seams `selectedAtomicWriteCarrier`/`SharedFieldFlow.atomicValueField` if unused after P2c; runtime fallbacks named in REPORT-P2EF (`fieldLocation` class-name fallback stays only if named); VM `getSymbolicFieldExpression` describing the argument; `JsonFields` throws (d3/plan); shrink S2 branch-record cluster; `RuntimeRefinedGraphBuilder`. Rule: delete outright, no adapters/stubs; grep readers on staging + all branches before each deletion; one campaign (17960) after the round.

**Added 2026-09-15 10:35 (owner: "17960跑通后把所有旧的jar产物，中间产物，不再用的都给我删掉。也不要任何兼容层的东西"):** the cleanup round also deletes every old artifact, not only code: old jars/target dirs of finished worktrees, lane output dirs (laneA1–A5 …; keep only the accepted run's final dir as the case's corpus of record), scratch copies of corpora (e1/e3/e4/m4*/p2cd/p2e/corpus-*), superseded seed corpora (keep the latest per case), VM images other than the current one (build20; delete build16–19 once nothing references them), stale worktrees/branches after landing, the handover clutter in the repo root. No compatibility layer of any kind survives.
