# HBase: the final .smt of every case

Each case's final formula (`<case>.smt2.gz`, gzip of the run's `schedule/final/candidate.smt2`) and its claim
(`<case>.claim.json`); `index.tsv` names the run each came from (`/bigtemp/vnr3ne/gc-out/hbase-final/<run>`).
The runs: `system/hbase` snapshots `hb-int-16` (319428f7d; F1*, F2*) and `hb-int-17` (e53c3c882: the same engine plus
the gap-ledger fix and the per-case configuration; F3S), tree `graphchecker/hbase-checks` b5d5cc6a20, image vm-force12.
Owner 2026-10-20/21: runs under 30 min kept from the concurrent round (F1*); every longer case run alone on all 14 hosts
(F2*), and 11 12 14 15 again alone with their scope cut (F3S). Every case's configuration is in
`experiments/hbase/*/case.sh` and `workflow.properties`.

**Run one case:** `CAUSYNTH_CUSTOM_JDK_HOME=<image> GC_TREES=<tree set> tools/rounds/launch-run.sh <snapshot of system/hbase> <case> <tag>` (OPERATIONS.md §10; the tree set:
`GC_TREES=<dir> experiments/hbase/prepare-trees.sh hbase-checks`); **all:** `tools/rounds/run-series.sh <round>
experiments/hbase/hbase-cases.tsv system/hbase=<snapshot>`. The table below is `final-stats.py` over the run dirs:
seeding = PREFLIGHT..IMPORT and ZKKEYS (static passes, recording, seed replay); exploration = EXPLORE; compose+solver =
COMPOSE + SOLVE + DECIDE; other = CONFIRM + EMIT + REPRODUCE; refuted claims = the compose and CONFIRM of the claims
CONFIRM refuted before the last one (their number in brackets; `stage_metrics.tsv` times only the last claim, so this is
the wall the stages leave uncovered: 07, 08, 10); regions / occurrences = the final closure. The columns sum to the wall
but for up to 30 s of stage start-up per case (233 s in all). Of the 15.0 h, exploration takes 39 %, seeding 29 %, the
refuted claims 16 %, other 9 % and compose+solver 7 %.

| case | run | mode | claim | mechanism | native | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hbase-adhoc-04 | F1B-adhoc-04 | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 839 | 438 | 342 | 5 | 47 | - | 8 | 68 | 9 |
| hbase-adhoc-07 | F2S-adhoc-07 | alone | SAT_UNCONFIRMED | STATE_PAIRING_FLIPPED | - | 5250 | 774 | 1221 | 293 | 559 | 2404 (3) | 19 | 183 | 6 |
| hbase-adhoc-08 | F2S-adhoc-08 | alone | SAT_UNCONFIRMED | STATE_PAIRING_FLIPPED | - | 2897 | 557 | 445 | 70 | 419 | 1406 (3) | 5 | 68 | 41 |
| hbase-adhoc-10 | F2S-adhoc-10 | alone | SAT_UNCONFIRMED | STATE_PAIRING_FLIPPED | - | 12638 | 954 | 5189 | 1134 | 630 | 4732 (3) | 10 | 344 | 19 |
| hbase-adhoc-11 | F3S-adhoc-11 | alone | SAT_UNCONFIRMED | STATE_PAIRING_FLIPPED | - | 2439 | 1470 | 441 | 24 | 488 | - | 12 | 426 | 1 |
| hbase-adhoc-12 | F3S-adhoc-12 | alone | SAT_UNCONFIRMED | STATE_PAIRING_FLIPPED | - | 3449 | 743 | 1849 | 298 | 542 | - | 14 | 509 | 41 |
| hbase-adhoc-13 | F2S-adhoc-13 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 4359 | 1146 | 2998 | 128 | 72 | - | 27 | 458 | 89 |
| hbase-adhoc-14 | F3S-adhoc-14 | alone | SAT_UNCONFIRMED | STATE_PAIRING_FLIPPED | - | 2674 | 1924 | 1 | 24 | 695 | - | 19 | 935 | 0 |
| hbase-adhoc-15 | F3S-adhoc-15 | alone | SAT_UNCONFIRMED | STATE_PAIRING_FLIPPED | - | 4671 | 646 | 1972 | 1536 | 495 | - | 15 | 671 | 26 |
| hbase-adhoc-19 | F2S-adhoc-19 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1042 | 534 | 475 | 20 | 6 | - | 17 | 134 | 8 |
| hbase-adhoc-20 | F2S-adhoc-20 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1056 | 540 | 477 | 26 | 6 | - | 17 | 134 | 8 |
| hbase-adhoc-21 | F2T-adhoc-21 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1137 | 599 | 474 | 37 | 17 | - | 16 | 291 | 38 |
| hbase-adhoc-22 | F2B-adhoc-22 | alone | SAT_CANDIDATE | STATE_PAIRING_FLIPPED | 10/10 | 946 | 508 | 385 | 12 | 34 | - | 9 | 123 | 12 |
| hbase-adhoc-24 | F1T-adhoc-24 | concurrent | SAT_CANDIDATE | STATE_PAIRING_FLIPPED | - | 1489 | 835 | 637 | 4 | 7 | - | 4 | 9 | 7 |
| hbase-adhoc-28 | F1T-adhoc-28 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1131 | 709 | 407 | 8 | 4 | - | 1 | 1 | 3 |
| hbase-adhoc-31 | F1H-adhoc-31 | concurrent | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 1605 | 622 | 956 | 11 | 7 | - | 16 | 62 | 24 |
| hbase-adhoc-34 | F1T-adhoc-34 | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 9/10 | 1016 | 638 | 186 | 5 | 181 | - | 11 | 25 | 2 |
| hbase-adhoc-35 | F1U-adhoc-35 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 1674 | 627 | 909 | 117 | 14 | - | 23 | 126 | 24 |
| hbase-adhoc-37 | F1U-adhoc-37 | concurrent | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 646 | 450 | 170 | 4 | 4 | - | 1 | 1 | 3 |
| hbase-bugs-master-active-time | F1B-bugs-master-active-time | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 8/10 | 1135 | 437 | 343 | 5 | 343 | - | 11 | 64 | 8 |
| hbase-bugs-backup-lock-reply-lost | F1B-bugs-backup-lock-reply-lost | concurrent | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 689 | 399 | 186 | 4 | 79 | - | 2 | 3 | 1 |
| hbase-bugs-ns-rsgroup-removal | F2B-bugs-ns-rsgroup-removal | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 1337 | 369 | 909 | 10 | 29 | - | 7 | 40 | 29 |

22 of 22 cases; wall 54119 s (15.0 h); seeding 15919, exploration 20972, compose+solver 3775, other 4678, refuted claims 8542 s

## Reading per case

- **hbase-adhoc-04**: **PASS** (HBASE-30484): a REQUEST fault on the quota observer's GetActiveMaster loses the enable after the snapshot advanced
- **hbase-adhoc-07**: named bound: SAT, every claim refuted by CONFIRM as the client thread's program order (the restore follows the synchronous disable); scope cut: TestCausynthRestoreSnapshot, no client faults
- **hbase-adhoc-08**: named bound: SAT, every claim refuted by CONFIRM (client program order)
- **hbase-adhoc-10**: named bound: SAT, every claim refuted by CONFIRM; exploration stopped PLANNER_HEAP_EXCEEDED at 12288 MB
- **hbase-adhoc-11**: named bound: SAT, the claim refuted by CONFIRM; scoped (no client faults, first claim, 3600 s campaign, 16384 MB)
- **hbase-adhoc-12**: named bound: SAT, the claim refuted by CONFIRM; scoped as 11
- **hbase-adhoc-13**: RUN_DEFECT (closure truncated at 64 tasks, 150 occurrences; an unresolved snapshot port); the formula is vacuous: the second merge's hasMergeRegions read states no version (the VM marks the map's writer set incomplete)
- **hbase-adhoc-14**: named bound: SAT over the seed corpus (seeding took 1925 s of the 3600 s campaign, no exploration round fit), the claim refuted by CONFIRM; scoped as 11
- **hbase-adhoc-15**: named bound: SAT, the claim refuted by CONFIRM; scoped as 11
- **hbase-adhoc-19**: UNSAT, vacuous by construction (class C: the test builds both descriptors it compares)
- **hbase-adhoc-20**: UNSAT, vacuous by construction (class C)
- **hbase-adhoc-21**: UNSAT_CLOSED at the fixed point, substantive (closure bound 128 tasks)
- **hbase-adhoc-22**: **PASS** (HBASE-30483): no fault; the creation's quota read joined to the truncated table's original count
- **hbase-adhoc-24**: SAT, confirmed in the VM (no native STORE_HOLD): a procedure member's barrier read held past the coordinator's 60 s timeout reads no node and throws at ZKProcedureMemberRpcs:210 -- caught there (subprocedure null, nothing written): a misleading log, not a functional bug
- **hbase-adhoc-28**: UNSAT, vacuous by construction (class C: a configuration constant the JDK decides)
- **hbase-adhoc-31**: UNSAT_CLOSED, vacuous: start codes are run constants. The run row says RUN_DEFECT: 3 stale EXPLORE gaps of generations 3-10, superseded by the gap-ledger fix merged after the run (354755d4e); re-ledgered offline: 0 BLOCKING
- **hbase-adhoc-34**: SAT, confirmed, 9/10: a ZooKeeper READ fault on refreshKeys -- reachable fault handling, not a new bug
- **hbase-adhoc-35**: UNSAT, vacuous by construction (class C: needs a corrupt hbase:meta)
- **hbase-adhoc-37**: UNSAT, vacuous: its workload has no window where /hbase/master is absent (needs a failover workload)
- **hbase-bugs-master-active-time**: **PASS** (owner bug #11): master1's configured clock skew -2001 ms (owner-approved workaround: active time = start code + a configured skew)
- **hbase-bugs-backup-lock-reply-lost**: **PASS** (owner bug #12): the lock CAS's reply lost (HBASE_RPC RESPONSE fault); control 0/10
- **hbase-bugs-ns-rsgroup-removal**: **PASS** (owner bug #13): a REQUEST fault on the master's namespace hbase:meta Mutate lets removeRSGroup read 0 namespaces
