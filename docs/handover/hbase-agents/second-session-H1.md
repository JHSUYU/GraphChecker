# H1 (platform; 35, 28, 15, 14, 13, 07): second session, 2026-10-19 23:50 to 2026-10-20 13:50

Five of six cases are recorded; 07 has no verdict and waits for the exclusive run. No process of H1's is left.
Runs: `/bigtemp/vnr3ne/gc-out/hbase-platform/accept-<TAG>`.

| case | run | result | reading | time |
| --- | --- | --- | --- | --- |
| hbase-adhoc-35 | NP2-35 | UNSAT, vacuous by construction (class C: corrupt meta), no workaround | the meta entry's only other writer is the scanning thread; the throw needs two meta rows of one region | 1354 s |
| hbase-adhoc-28 | NP4-28 | UNSAT, vacuous by construction (class C: a configuration constant the JDK decides) | the bind-address check is decided in the JDK's network code; the workload never sets it | 575 s |
| hbase-adhoc-15 | NP9-15 | named bound: `campaign_max_claims` + REGION_PATH_CLOSURE_TRUNCATED (210 occurrences) | all 9 claims refuted by the client's program order (createTable returns only after its regions are open, then the merge) | 11381 s |
| hbase-adhoc-14 | NP10-14 | named bound: the campaign budget after 2 claims + a truncated closure (116) + PORT_UNRESOLVED | both claims refuted by the same program order; guard stated since tree 01b9db66da | 11129 s |
| hbase-adhoc-13 | NP18-13 | RUN_DEFECT (DECLARATION_MISSING) | guard stated after the tree workaround; the seed replay gives up the janitor's GC push to the test thread's poll wake (TODO HBase 19), so merge 2 meets the GC's lock and runs under another address | 1306 s |
| hbase-adhoc-07 | NP20STOP-07-exclusiveDecides | no verdict: the exclusive run decides (5-10 h alone, budget 43200 s, TODO HBase 1) | stopped at EXPLORE round 25: 1811 verdicts, 469 in flight; replays ~22 min, 3.7 GB; guard stated; the offline preview's claim is a state re-pairing of the restore's table-state read | ~4 h 40 min |

## Commits (all merged)
- Tree `gc/hb-platform` (each native-PASS): 01b9db66da (14's encoded-name map a ConcurrentHashMap), 6fddb3317a + 618e0dfe19 (13's
  tracked merge-qualifier map, its workload, the janitor scanned on the test thread), 0be6cddfa8 + 8514acd8f9 (07's and 12's
  table-state guards compare the state they read), dddf836200 (a region server's load report once per active master),
  64c53690e1 (07's light load).
- GraphChecker `hbase-platform`: 39bf06c65 (07's scope row) and fdec55ee8 (13's row, workload, selector), gated on lift10; docs
  a317b2af8, 745c9f443, 48fe08564, cb7c6f1fd, 85c803486, f0e7e5c20, c77f65366, 350bc12d4.
- TODO HBase items opened or filled: 15 (the four program-order cases' costs), 16 (a large start starves), 18 (a guard through a
  helper's boolean return in a try/catch), 19 (a chore under its trigger's context loses its slot).

## Left / unsure
07 (the exclusive run); 13's seed ordering (TODO HBase 11, 19). The one-report-per-master change: every native passes and no case's
chain reads a later report, but a workload that needs a later check-in would miss it. Evidence on disk: snapshots
`gc-run/hb2-platform-3` (NP16/18-13) and the shared hb-int-1/-2/-8/-12/-13; tree sets `wt/hb2-platform-trees-1,2,4..7`
(trees-3 and snapshots hb2-platform-1/-2 can go); Maven repos `m2/hbase-platform2`, `-3`; offline previews
`analysis/hbase-2026-10-20/h1/compose/`.
