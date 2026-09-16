---
name: change-first-then-verify
description: Owner directive 2026-09-15 night — finish the code changes first (batched), then one thorough verification; no per-step seed recordings
metadata:
  type: feedback
---

Owner (2026-09-15 ~23:20, after asking why coding was slow): "你先改完，再彻底验证".

**Why:** each mandate was gating itself on a fresh 17960 recording (≈10 min per seed, 2–3 per mandate) plus heavy evidence lists; the verification cost dominated the change cost. The owner wants the batch of changes (cleanup rounds + identity) completed, then one thorough verification of the whole tree.

**How to apply:** a mandate's definition of done = build clean, unit tests green, shell test green, and offline checks on KEPT corpora (aggregation over an existing trace, offline ExploreMain/ComposeMain) — no new recordings. Recordings and the full campaign happen once, on the merged tree, as the thorough verification (fresh seed → IMPORT gate → offline wave 0 → full 17960 campaign to acceptance). If that fails, analyze once with all evidence rather than bisecting by re-recording per mandate. Keep evidence requests to the decisive few. Supersedes the per-mandate seed gates in [[reuse-passed-runs]] and [[subagent-rules-of-engagement]]; consistent with [[fix-the-flow-not-the-bug]] (plan the class up front so the one verification passes).
