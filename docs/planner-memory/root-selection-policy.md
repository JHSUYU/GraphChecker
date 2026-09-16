---
name: root-selection-policy
description: Owner 2026-09-15 — the planner selects the manual roots (symbolic variables + domains) per case; no need to ask. The chosen set for the six cases is recorded here.
metadata:
  type: project
---

Owner: "合理选什么根你已经知道了哈，你手动选就行" — root selection is the planner's call.

Chosen roots (declared in each case's symbolic-inputs.jsonl / root-domains.jsonl):
- 17960: Boolean config marker HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED (both values).
- 11741, 17897, 17899 bug1/bug2/bug3 (the key-set cases):
  - HDFS.BLOCK_KEY.SERIAL_NO — INTEGRAL, relative domain [+0, +3] (rotations ahead of the recording).
  - HDFS.BLOCK_KEY.EXPIRY_DATE (+ .CURRENT / .RETIRED / INITIAL_*) at the five BlockKey construction sites on the NN — INTEGRAL, no domain (moves only through clocks).
  - every clock read (clockCallee) — CLOCK, unbounded (>= 0 floor), per path.
  - the existing Boolean fault markers (bug3's two) — MARKER.
  - NOT roots: keyUpdateInterval/tokenLifetime (constants; clocks cover the arithmetic), DEK id on the NN (derived from the serial), delivery omission (event-level; expressed as pairing findings).
**How to apply:** keep these declarations through the refactor; add a root only when a case's refusal names an unstated quantity at its source. See [[graphchecker-core-design-principle]], [[no-validate-stage]].

**Owner 2026-09-15 15:05 (11741):** the target region has many runtime instances (dn0/dn1 × balance-block#1/#2); we handle ONE — the declared selector picks it by seed order (k-th match); the other activations are ordinary occurrences. Duplicate addresses at SEED aggregation are never fatal: structurally distinguishable activations get distinct ids (one identity function, start-site frames), the rest share an address under ONE named DIAGNOSTIC gap. (G2 implements.)
**Owner 2026-09-15 15:15:** 11741's target = `hdfs-11741/dn1#epoch0/region/REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de@hdfs-11741/balancer#epoch0/balance-block#1` (dn1's first balance-block activation — the Balancer's first handshake after the rotations); the runtime identifier distinguishes it. Set in workflow.properties on staging (commit after a33cb4a9c).
