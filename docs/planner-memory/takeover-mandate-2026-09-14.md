---
name: takeover-mandate-2026-09-14
description: Owner mandate 2026-09-14 22:40 — Fable 5.1 planner takes over GraphChecker; design is fixed (no big redesign); delegate all code work to opus-impl (Opus 5, xhigh); finish engineering details; get all six experiments cases to a correct causal .smt
metadata:
  type: project
---

Owner (2026-09-14 22:40, "设为长期记忆"): the main agent (Fable 5.1) is the planner and design holder. It plans in detail, delegates every concrete code read/write/run to `opus-impl` subagents (Opus 5, xhigh), reviews their diffs and evidence, and never lets a subagent pull the design off course. The big design is settled (see [[graphchecker-core-design-principle]], HANDOVER-D3.md §1, d3-handover/d-design/) and must not be changed in a big way; only engineering details remain. The planner must always distinguish small patches from work that needs restructuring, and hold the big picture.

Goal: run the six `experiments/hadoop` cases (17960, 11741, 17897, 17899 bug1/bug2/bug3) end to end and produce, for each, a `.smt` whose content is the correct causal chain (root → propagated expressions → fatal predicate), judged by z3. Each case has its hooks in the `/opt/hadoop-hdfs-*` trees. Symbolized variables are finite and chosen by hand — reuse the previous choices ([[root-selection-policy]]). The planner must read and understand each bug itself (case READMEs under experiments/hadoop/*/README.md; HDFS-17960 = snapshot-count mismatch on duplicate ordered-deletion replay; 11741/17897/17899 = stale data-encryption / block key reaching `retrieveDataEncryptionKey`).

Context: pure PhD research on distributed-system reliability; nothing sensitive.

**How to apply:** start every session from /opt/GraphChecker/HANDOVER-D3.md (state, frozen rules, ordered TODO); dispatch per [[subagent-rules-of-engagement]] with exact file ownership and evidence-based acceptance; merge only after planner review; keep [[serial-campaigns-only]] (max two lanes) and [[test-count-cap]].
