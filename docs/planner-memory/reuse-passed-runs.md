---
name: reuse-passed-runs
description: Owner 2026-09-15 08:40 — reuse what already ran fine (recorded corpora, passed stages) instead of re-running; re-record only when the runtime's publication changes; a full campaign only for the final acceptance
metadata:
  type: feedback
---

Owner: "之前跑过没问题的我们直接重用不就好了".

**Why:** each full 17960 campaign costs ~18 min and each seed recording ~13 min; on 2026-09-15 several were spent re-producing corpora that composer/explore changes did not need.

**How to apply:** keep a corpus registry keyed by the runtime tip + VM image (e.g. `$SPN/d-runtime/full/17960` = P2f' rows, `$MY/corpus-p2f2-iteration`, laneA4's epoch): composer/explore work validates OFFLINE on the newest corpus whose row contract matches (ComposeMain/ExploreMain take seconds); only a runtime publication change triggers one recording (seed_case.sh to IMPORT), and only the final acceptance runs a full campaign. The harness's content-addressed caches (PLAN/INSTRUMENT) should be keyed on the inputs that matter so a jar rebuild alone does not invalidate them (harness item). Also: "跑通这个后d3文件夹这种都给我移走" / "d3就是死代码清理这方面的" (2026-09-15 08:55) — the d3 items belong to the post-17960 dead-code cleanup round: move the handover clutter (`/opt/graphchecker-handover/d3-handover/`, `HANDOVER-D3.md`, `1.out/1.err/1.time`) out of the repo root, and in the cleanup round flatten the `d3` Java package into first-class packages (contract/compose/explore/plan/smt) — no "design 3" naming left in the tree.
