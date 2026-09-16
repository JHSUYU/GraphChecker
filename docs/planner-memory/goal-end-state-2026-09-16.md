---
name: goal-end-state-2026-09-16
description: Owner redefined the end of the goal (2026-09-16 ~06:45 CDT): finish 11741, then STOP campaigns; final code revisit (refactor bloat, delete logically unused old code), then rewrite the README's design section clearly — that completes the goal (the other four cases are not part of it)
metadata:
  type: project
---

Owner (2026-09-16, after 17960's clean pass): "11741跑完你就先停下。然后revisit一下代码，把臃肿的部分都重构，逻辑没用的旧代码都删除。更新readme里当前的设计，写的清楚一点。你的goal就完成了。"

**Why:** the design is proven on one single-node case (17960) and one multi-node case (11741); the remaining value is a lean, readable codebase and an accurate README, not more cases.

**How to apply:** (1) run 11741 campaign #3 after X15 merges; fix what its composition exposes until the .smt states the CLOCK_SKEW chain (or stop at the owner's word); (2) no further campaigns after that; (3) final cleanup round 3 with fresh surveys: bloated files (ConcolicRegionRuntime ~7K, RuntimeSelectedRegionFinalizer, CausynthPipeline, RuntimeRegionPlanner, SeedBackwardStaticAnalyzer, ConcolicScheduler), the known residue (RuntimeRefinedGraphBuilder P-C, Identity.here degraded index, loop-body levels, ITL, second implementations flagged in reports), dead code by "logically unused" not reachability; verify offline only (accepted corpora byte-identical) plus one final 17960 + 11741 campaign as the acceptance of the refactor; (4) README: the current design (pipeline, identity v3, rows contract, closure v2, composition, gates, how to run a case) written plainly; (5) HANDOVER-D3.md final update. Supersedes the six-case scope in [[takeover-mandate-2026-09-14]].


## Update 2026-09-16 16:45 CDT — stopped by the owner
Owner: "好的，就到这里。你可以停下了。" Final instructions: commit the /opt/hadoop edits to the remote branches; commit+push GraphChecker; the remote keeps ONE branch `main` holding the current version (all modifications merged into main, other branches deleted); README summarizes the design and the to-do so a new agent can continue. State at stop: round 3 merged through r3/C3 (staging 0e3c1ab39); three unfinished mandates (FIX1, R4, PC4) merged as committed work + patches; 17960 passes offline on the kept corpus but the last live run was refused by the new per-wave gate (FIX1); 11741 has no witness yet (R4: root symbol without mint row). **How to apply:** a continuing agent starts from `main`'s README §9 and docs/HANDOVER.md; first job = run experiments/hadoop/accept on 17960 and 11741.
