# H4 (checks; nsrg, 22, 21, 08, 19, 20): second session, 2026-10-19 23:50 to 2026-10-20 06:00

All five cases are finished; no process of H4's is left. Runs: `/bigtemp/vnr3ne/gc-out/hbase-checks/accept-<TAG>`.

| case | run | verdict | vacuity / bound | time |
| --- | --- | --- | --- | --- |
| hbase-bugs-ns-rsgroup-removal (#13) | NC12-nsrg; reproduced in repro-NC12-nsrg-1 | **PASS**: SAT MARKER_FLIPPED (REQUEST fault on master0's hbase:meta Mutate in CREATE_NAMESPACE_INSERT_INTO_NS_TABLE), confirmed, reproduced natively 10/10, control 0/10 | - | 1363 s |
| hbase-adhoc-22 = HBASE-30483 | NC15-22 | **PASS**: SAT STATE_PAIRING_FLIPPED (the creation's read of the namespace total joined to the original create's addTable before the asynchronous deletion's release; the truncate writes none), confirmed, reproduced 10/10, control 0/10 | - | 1340 s |
| hbase-adhoc-21 | NC16-21 (CAUSYNTH_REGION_PATH_MAX_TASKS=256) | UNSAT_CLOSED at FIXED_POINT, 0 BLOCKING | substantive (195/195 paths free); bounds: depth 0, ordered_map_unmodeled on the max-regions TreeMap (written once, "10"; counts reach at most 9) | 2423 s |
| hbase-adhoc-08 | NC14-08 | SAT_UNCONFIRMED at `campaign_max_claims` | every claim orders a step against the test thread's synchronous order createNamespace -> createTable -> deleteNamespace (class C; TODO HBase 15) | 6507 s |
| hbase-adhoc-19, 20 | NC18-19, NC19-20 | UNSAT_CLOSED at FIXED_POINT | vacuous by construction, class C: the test builds both descriptors it compares on its own thread | 818 s, 756 s |

nsrg's own NC12 reproduce.json reads 0/10 (an ORDER between the client's own synchronous calls, identified through a resent
request in the slow replay); the 10/10 evidence is the REPRODUCE-alone rerun over a copy on a4e586d4b (the implied-order rule).

## Engine commits (GraphChecker `hbase-checks`, all merged)
- e49ff4485: a door earlier in a demanded occurrence's own turn is its control producer (nsrg's Mutate fault).
- 47975f1e3: DECIDE claims an explored session's own run first.
- 32a71ff21: a confirmed claim that reproduces in 0 native runs is kept as the fallback verdict and the loop tries the next.
- a4e586d4b: REPRODUCE leaves out an ORDER a client thread's synchronous RPC reply implies (`contract.ClientProgramOrder`).
- docs/report.py: eac03ec58, 5e5376862, 9fa11c0f9, 47938e937, eb4e480db, 1ecdacc06.

## Tree (gc/hb-checks, in gc/hbase-checks)
100878f553: RSGroupInfoManagerImpl keeps its groups in a tracked map mutated in resetRSGroupMap (nsrg).

## Left
TODO HBase 15 (client program order in COMPOSE; JOIN rows, parked: 2-3 days). 19's real race (a column family added between the
client's read and a no-reopen modify) needs a workload with two concurrent modifies. The RSGroupStartupWorker WAKE-count drift adds a
GROW per EXPLORE round in nsrg (cost only). Readings: `/bigtemp/vnr3ne/analysis/hbase-2026-10-20/readings.md`.
