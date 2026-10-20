# H3 (RPC; 04 = HBASE-30484, 10, 11, 12, 31): second session, 2026-10-19 23:50 to 2026-10-20 13:30

All five cases are finished; no process of H3's is left. Runs: `/bigtemp/vnr3ne/gc-out/hbase-rpc/accept-<TAG>`.

| case | final run | verdict | vacuity | wall |
| --- | --- | --- | --- | --- |
| hbase-adhoc-04 = HBASE-30484 | NR3-04 (HC21-04 before it) | **PASS**: SAT MARKER_FLIPPED (a lost RPC on the quota observer's connection: GetActiveMaster in NR3, EnableTable in HC21; the enable after the snapshot advanced fails, the next run skips it, the flush is refused at :163), confirmed, reproduced 7/10, control 0/10 | n/a | 889 s |
| hbase-adhoc-10 | NR19-10 | named bound (campaign_max_claims): the unassign arrives while an assign's TRSP is attached (the plausible race at :765); CONFIRM cannot hold TRSP#confirmOpened's unsetProcedure (no planned activation, TODO HBase 21) or its holds did not exit | guard symbolic | 13297 s |
| hbase-adhoc-11 | NR18-11 | named bound (budget): the unassign's state read re-paired to writes the unassign or a later test call causes (client program order, TODO HBase 15) | guard symbolic | 12145 s |
| hbase-adhoc-12 | NR16-12 | named bound (campaign_max_claims): the unassign's table-state read re-paired to the later disable (program order) | guard symbolic | 10893 s |
| hbase-adhoc-31 | NR8-31 | named bound (campaign_max_claims): rs3 handed another session's message (a cross-session delivery no run makes); the dispatcher-retry chain was never composed | guard symbolic | 12026 s |

04's three non-reproductions hit the fatal with the root planted; a procedure step ran under another hand-off nesting (TODO HBase
11). Runs before the finals are evidence: NR1STOP-10 (re-asked client-door faults, fixed by DUPLICATE_WORLD), NR5-11 (an occurrence
that throws by design), NR11VAC-11 / NR12VAC-12 (guards answered through helpers outside the scope), NR10NFS-11 (ESTALE, fixed),
NR7/14/15/17STOP (stopped once their defect was found).

## Commits
- GraphChecker `hbase-rpc` (all merged, gated): 93122386b (an order no hold realizes is checked), b9dfcedc5 (the native plant leaves out
  turn-counted orders), 07737dc35 (EXPLORE stops on a BLOCKING TARGET_FATAL_IN_RECORDING), 53a4ecfdf (04's expected mechanism);
  data: 1e1c2c93b (10/11/12 name admin.unassign's occurrence REGION.4fb04ead#1), f1b6d84f0 / a38312de2 / ca036954e (scope rows for
  11, 12, 10); docs eb81d8b5d, b6b0032eb, 96629b5bf, 924d63897, 6d17ac331, 54f5f73e0, dc106f92a (10 + TODO HBase 21).
- Tree `gc/hb-rpc` (in `gc/hbase-checks`): fb3ca18bb6 + 879705cfee (11's :769 guard compares the region state itself, the decisive
  compare last).

## Left
TODO HBase 21 (CONFIRM planning for the writers around a held read: blocks 10's race), 11 (procedure-step identity drift: 04's 3/10),
the per-path re-finding of refuted message re-pairings (31, ~10-15 min each). Unsure: 10's diagnosis is read from the refusals, not
an offline planner run; 31's dispatcher-retry chain is not proven reachable in the current scope. Leftovers: snapshots
`gc-run/hb2-rpc-1..5`, tree sets `wt/hb2-rpc-trees-1..2`, helpers `analysis/hbase-2026-10-20/h3/`; readings in `readings.md`.
