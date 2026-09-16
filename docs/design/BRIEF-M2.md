# BRIEF M2 — RUNTIME (Design 3 refactor)

Prerequisite: M1 contract merged into staging (branch refactor/d3-contract); read
SPN/d-refactor/CONTRACT-SCHEMA.md and REPORT-M1.md first, then REFACTOR-D3.md,
INTERACTION-ID.md, IDENTITY-V2.md, DESIGN3-PLAN.md, and the runtime inventory
SPN/d-runtime/REPORT-RUNTIME-INVENTORY.md. Also REPORT-ENTRY.md (entry rule, scope
losses), REPORT-B1D.md (SASL scope lifetime), REPORT-NNCHAIN.md, REPORT-ANSWER2/4
(attach/mint mechanics), graphchecker-external-callers memory (21 workload-called APIs:
grep all /opt/hadoop-* trees before deleting any public runtime member).

Scope (runtime/ + the VM-facing hooks; not concolic/):
1. Lineage scope: RuntimeTraceContext gets parent + role; Server.Call enqueue/dequeue
   carry (IPC handler pool); SaslDataTransferServer inbound scope lifetime = the
   DataXceiver op (workload diff under SPN/d-runtime/workload/, rebuild rules in the
   runbook — never rebuild a tree while a lane runs on it); daemon roots (HeartbeatManager,
   BPServiceActor, KeyManager ticks) as role#k window-local. OccurrenceMinter mints v2
   addresses; lineageLost rows where a hop is unattributable.
2. Rows per M1: Activation, Decision, Export (endpoint incl. port ordinal + attempt,
   e_p ref, handle), Attach (endpoint, v_H, arrival, answered?, pairing to the producer
   endpoint from the correlation/handle; DEGRADED producer endpoint when the exporter had
   no scope), Write/Read (endpoints + version), RootMint (kind, domain), Target (φ fatal
   polarity), Gap (closed enum). Mint v_H at EVERY declared port regardless of
   selection; export everywhere (already).
3. Focused-region replay mode: exactly one occurrence (or one state-connected factor:
   writers+readers of one location on one node) runs symbolic; every other region concrete
   with exports/attaches recorded; obligations' answered values applied at the attach as
   today; admission evidence per focused region only.
4. (No VALIDATE replay mode — owner ruling: the composed .smt + z3 verdict is the
   deliverable.)
5. Delete: companions/slices (ReplayTaskSlice, keptSlice plumbing), RPC_HANDOFF_NO_ACTIVE
   _REGION paths, request-family addressing in the minter, GapLedger kinds without a
   consumer, mechanisms the inventory lists as superseded. src/main net smaller.
Tests folded (suite ≤ 80 @Test). Gate: re-record all six cases on the new runtime (two
lanes max, FINAL_KEEP_ALL, build16 image); per case a table: lineage-complete share per
entry point, declared ports minting, interactions paired, degraded endpoints named.
Report SPN/d-refactor/REPORT-M2.md with tip and line deltas.
