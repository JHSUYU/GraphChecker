# ZooKeeper: the old bugs put back (buggy-detect), round B1 on liftlab

Each case's final formula is `<case>.smt2.gz` (the gzip of the run's `schedule/final/candidate.smt2`) and its claim
`<case>.claim.json`; `index.tsv` names the run each came from (under `/bigtemp/vnr3ne/gc-out/`). The cases are
`experiments/zookeeper/zookeeper-buggy-cases.tsv`, each case's README the bug, what was put back, the workload and every run.
`docs/handover/BUGGY-DETECT.md` has all four systems' table, the CloudLab runs of 2026-10-26 beside B1.

B1 (2026-10-28): this branch's snapshot `/u/vnr3ne/gc-run/bd-zookeeper-1`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1`
(`experiments/zookeeper/prepare-trees.sh` from the fork's `*-bug-<jira>` branches), the cases beside each other and beside
the other systems' on the liftlab workers (`tools/rounds/launch-round.sh` with `CASES`), `CASE_TIMEOUT_SECONDS=21600`.
Detected = SAT, CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with the control 0/N, report.py PASS.

Again: `GC_OUT=<dir> results/zookeeper-buggy/collect-results.sh experiments/zookeeper/zookeeper-buggy-cases.tsv <round>` copies the files, and
`results/zookeeper-buggy/final-stats.py --cases experiments/zookeeper/zookeeper-buggy-cases.tsv --round <round> --out <dir>` makes the table
(seeding = PREFLIGHT..IMPORT and ZKKEYS; exploration = EXPLORE; compose+solver = COMPOSE + SOLVE + DECIDE; other =
CONFIRM + EMIT + REPRODUCE; regions / occurrences = the final closure; rounds = EXPLORE's generations).

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| zk-buggy-710 | ZOOKEEPER-710 | zk-adhoc-02 | B1-zk-buggy-710 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 308 | 162 | 113 | 6 | 22 | 3 | 34 | 5 |
| zk-buggy-2886 | ZOOKEEPER-2886 | zk-adhoc-02 | B1-zk-buggy-2886 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 294 | 150 | 114 | 3 | 23 | 3 | 33 | 5 |

2 of 2 cases ran (B1, beside each other on liftlab); wall 602 s; seeding 312, exploration 227, compose+solver 9, other 45
