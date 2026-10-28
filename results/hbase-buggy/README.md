# HBase: the old bugs put back (buggy-detect), round B1 on liftlab

Each case's final formula is `<case>.smt2.gz` (the gzip of the run's `schedule/final/candidate.smt2`) and its claim
`<case>.claim.json`; `index.tsv` names the run each came from (under `/bigtemp/vnr3ne/gc-out/`). The cases are
`experiments/hbase/hbase-buggy-cases.tsv`, each case's README the bug, what was put back, the workload and every run.
`docs/handover/BUGGY-DETECT.md` has all four systems' table, the CloudLab runs of 2026-10-26 beside B1.

B1 (2026-10-28): this branch's snapshot `/u/vnr3ne/gc-run/bd-hbase-1`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1`
(`experiments/hbase/prepare-trees.sh` from the fork's `*-bug-<jira>` branches), the cases beside each other and beside
the other systems' on the liftlab workers (`tools/rounds/launch-round.sh` with `CASES`), `CASE_TIMEOUT_SECONDS=21600`.
Detected = SAT, CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with the control 0/N, report.py PASS.

Again: `GC_OUT=<dir> results/hbase-buggy/collect-results.sh experiments/hbase/hbase-buggy-cases.tsv <round>` copies the files, and
`results/hbase-buggy/final-stats.py --cases experiments/hbase/hbase-buggy-cases.tsv --round <round> --out <dir>` makes the table
(seeding = PREFLIGHT..IMPORT and ZKKEYS; exploration = EXPLORE; compose+solver = COMPOSE + SOLVE + DECIDE; other =
CONFIRM + EMIT + REPRODUCE; regions / occurrences = the final closure; rounds = EXPLORE's generations).

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hbase-buggy-20642 | HBASE-20642 | hbase-adhoc-04 | B1-hbase-buggy-20642 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 0/10, by shape 10/10; control 0/10 | 1393 | 329 | 272 | 11 | 100 | 681 (5) | 3 | 40 | 3 |
| hbase-buggy-15039 | HBASE-15039 | hbase-adhoc-34 | B1-hbase-buggy-15039 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 755 | 315 | 303 | 7 | 124 | - | 5 | 7 | 4 |

2 of 2 cases ran (B1, beside each other on liftlab); wall 2148 s; seeding 644, exploration 575, compose+solver 18, other 224
