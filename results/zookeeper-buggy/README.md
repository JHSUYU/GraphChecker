# ZooKeeper: the old bugs put back (buggy-detect), each case alone on liftlab (round E1)

Each case's final formula is `<case>.smt2.gz` (the gzip of the run's `schedule/final/candidate.smt2`) and its claim
`<case>.claim.json`, both from round E1; `index.tsv` names the run each came from (under `/bigtemp/vnr3ne/gc-out/`). The
cases are `experiments/zookeeper/zookeeper-buggy-cases.tsv`, each case's README the bug, what was put back, the workload and
every run. `docs/handover/BUGGY-DETECT.md` has all four systems' table: the CloudLab runs of 2026-10-26, B1 and E1.

E1 (2026-10-29, the owner: every case alone, for the time breakdown): this branch's snapshot
`/u/vnr3ne/gc-run/bd-zookeeper-1`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1` (`experiments/zookeeper/prepare-trees.sh` from
the fork's `*-bug-<jira>` branches), one case at a time on the 11 liftlab workers (lift02-06, 08-10, 12-14) with nothing
else running: `tools/rounds/launch-round.sh` with that one case in `CASES`, the next case started once the summary row
was written and no process of the run was left (`/bigtemp/vnr3ne/analysis/buggy-detect-exclusive-2026-10-28/series-E1.sh`),
`CASE_TIMEOUT_SECONDS=21600`. Detected = SAT, CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with the
control 0/N, report.py PASS.

Again: `GC_OUT=<dir> results/zookeeper-buggy/collect-results.sh experiments/zookeeper/zookeeper-buggy-cases.tsv <round>` copies the
files, and `results/zookeeper-buggy/final-stats.py --cases experiments/zookeeper/zookeeper-buggy-cases.tsv --round <round> --out <dir>`
makes the table (seeding = PREFLIGHT..IMPORT and ZKKEYS; exploration = EXPLORE; compose+solver = COMPOSE + SOLVE +
DECIDE; other = CONFIRM + EMIT + REPRODUCE; refuted claims = the claims CONFIRM refuted before the last; regions /
occurrences = the final closure; rounds = EXPLORE's generations).

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| zk-buggy-710 | ZOOKEEPER-710 | zk-adhoc-02 | E1-zk-buggy-710 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 311 | 165 | 108 | 10 | 21 | - | 3 | 33 | 5 |
| zk-buggy-2886 | ZOOKEEPER-2886 | zk-adhoc-02 | E1-zk-buggy-2886 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 300 | 157 | 107 | 10 | 21 | - | 3 | 32 | 5 |

2 of 2 cases ran (E1); wall 611 s; seeding 322, exploration 215, compose+solver 20, other 42

Both cases as in B1: the same mechanism (STATE_PAIRING_FLIPPED), native 10/10, the control 0/10, within 2 % of B1's
wall.

## N1 (2026-10-29): the whole exploration, each case alone

The cases whose E1 exploration ended WITNESSED, again alone, with `CAUSYNTH_STREAM_STOP_AT_WITNESS=false` (`run_engine.sh` `stream_stop_at_witness`, `docs/design/PIPELINE.md`): no
session is a witness, every exploration runs to FIXED_POINT, and COMPOSE, SOLVE, DECIDE and CONFIRM run once over the
whole corpus (snapshot `/u/vnr3ne/gc-run/bd-zookeeper-2`; runs under
`/bigtemp/vnr3ne/gc-out/buggy-detect-full`; `docs/handover/BUGGY-DETECT.md` "Time, the whole exploration" compares
them with E1). The formulas and claims above stay E1's.

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| zk-buggy-710 | ZOOKEEPER-710 | zk-adhoc-02 | N1-zk-buggy-710 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 589 | 164 | 366 | 6 | 46 | - | 3 | 34 | 12 |
| zk-buggy-2886 | ZOOKEEPER-2886 | zk-adhoc-02 | N1-zk-buggy-2886 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 595 | 160 | 375 | 10 | 47 | - | 3 | 34 | 12 |

2 of 2 cases ran (N1); wall 1184 s; seeding 324, exploration 741, compose+solver 16, other 93

## B1 (2026-10-28): the cases side by side, for comparison

The same snapshot and trees, the cases beside each other and beside the other systems' on the liftlab workers
(`launch-round.sh` with several cases in `CASES`); the runs are under `/bigtemp/vnr3ne/gc-out/buggy-detect`.

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| zk-buggy-710 | ZOOKEEPER-710 | zk-adhoc-02 | B1-zk-buggy-710 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 308 | 162 | 113 | 6 | 22 | - | 3 | 34 | 5 |
| zk-buggy-2886 | ZOOKEEPER-2886 | zk-adhoc-02 | B1-zk-buggy-2886 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 294 | 150 | 114 | 3 | 23 | - | 3 | 33 | 5 |

2 of 2 cases ran (B1); wall 602 s; seeding 312, exploration 227, compose+solver 9, other 45
