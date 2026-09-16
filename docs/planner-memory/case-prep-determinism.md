---
name: case-prep-determinism
description: Case preparation rule (2026-09-15): pin every structural nondeterminism source (daemons, timers, retries, checkpoint/restart races) in the case config before recording, or the seed replay's addresses drift from the plan's
metadata:
  type: project
---

Triggered by hdfs-17960 verification #3 (2026-09-15): 13 planned tasks were refused with a uniform −1 shift of `applyEditLogOp@k`. The actual cause turned out to be an engine defect (an unpaired identity region-stack pop wiping the per-site counters, fixed by W17960), but the rule below stands: an extra or missing iteration in the replay WOULD produce exactly this signature, and the design refuses it rather than tolerating it.

**Why:** IDENTITY-V3 addresses are structural (call-site iteration counts); they are immune to timing inside an iteration but not to a different NUMBER of iterations. The design deliberately refuses tolerance/heuristic matching, so the workload must be structurally deterministic up to the target.

**How to apply (before recording any case):** disable or pin background daemons and timers that write state in the instrumented window (NN edit-log autoroll, lease/resource monitors, DN heartbeat/key-update periods), make checkpoints and restarts explicit and awaited, remove RPC retries across restarts, and keep such daemons out of the instrumented closure when they are irrelevant to the target. For 11741 check the heartbeat period, the KeyManager block-key updater timer and the balancer's dispatcher pool before the seed. Config/test edits are permitted ([[hadoop-tracing-edits-allowed]], [[workload-assertions-may-be-adjusted]]); keep the diff under d-runtime/workload/. See [[identity-v3-execution-index]].
