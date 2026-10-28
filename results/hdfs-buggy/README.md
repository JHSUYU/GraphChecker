# HDFS: the old bugs put back (buggy-detect), round B1 on liftlab

Each case's final formula is `<case>.smt2.gz` (the gzip of the run's `schedule/final/candidate.smt2`) and its claim
`<case>.claim.json`; `index.tsv` names the run each came from (under `/bigtemp/vnr3ne/gc-out/`). The cases are
`experiments/hadoop/hdfs-buggy-cases.tsv`, each case's README the bug, what was put back, the workload and every run.
`docs/handover/BUGGY-DETECT.md` has all four systems' table, the CloudLab runs of 2026-10-26 beside B1.

B1 (2026-10-28): this branch's snapshot `/u/vnr3ne/gc-run/bd-hdfs-1`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1`
(`experiments/hadoop/prepare-trees.sh` from the fork's `*-bug-<jira>` branches), the cases beside each other and beside
the other systems' on the liftlab workers (`tools/rounds/launch-round.sh` with `CASES`), `CASE_TIMEOUT_SECONDS=21600`.
Detected = SAT, CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with the control 0/N, report.py PASS.

Again: `GC_OUT=<dir> results/hdfs-buggy/collect-results.sh experiments/hadoop/hdfs-buggy-cases.tsv <round>` copies the files, and
`results/hdfs-buggy/final-stats.py --cases experiments/hadoop/hdfs-buggy-cases.tsv --round <round> --out <dir>` makes the table
(seeding = PREFLIGHT..IMPORT and ZKKEYS; exploration = EXPLORE; compose+solver = COMPOSE + SOLVE + DECIDE; other =
CONFIRM + EMIT + REPRODUCE; regions / occurrences = the final closure; rounds = EXPLORE's generations).

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hdfs-buggy-11741 | HDFS-11741 | hdfs-adhoc-11 | B1-buggy-11741 | SAT_CANDIDATE | PASS | CLOCK_SKEW | yes | 10/10; control 0/10 | 884 | 285 | 460 | 109 | 25 | - | 14 | 36 | 10 |
| hdfs-buggy-17383 | HDFS-17383 | hdfs-adhoc-12 | B1-buggy-17383 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 572 | 320 | 218 | 4 | 27 | - | 10 | 14 | 2 |
| hdfs-buggy-12931 | HDFS-12931 | hdfs-adhoc-11 | B1-buggy-12931 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 368 | 209 | 127 | 3 | 25 | - | 12 | 15 | 1 |
| hdfs-buggy-5766 | HDFS-5766 | hdfs-adhoc-11 | B1-buggy-5766 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 516 | 220 | 261 | 4 | 28 | - | 13 | 15 | 7 |
| hdfs-buggy-10609 | HDFS-10609 | hdfs-adhoc-11 | B1-buggy-10609 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 506 | 254 | 221 | 4 | 24 | - | 21 | 32 | 2 |
| hdfs-buggy-14075 | HDFS-14075 | hdfs-adhoc-45 | B1-buggy-14075 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 463 | 321 | 114 | 4 | 21 | - | 3 | 4 | 2 |
| hdfs-buggy-14311 | HDFS-14311 | hdfs-adhoc-24 | B1-buggy-14311 | UNSAT_CLOSED | FAIL | NO_SUPPORTED_WITNESS | no | - | 2333 | 1117 | 1177 | 17 | 8 | - | 21 | 370 | 11 |

7 of 7 cases ran (B1, beside each other on liftlab); wall 5642 s; seeding 2726, exploration 2578, compose+solver 145, other 158

**hdfs-buggy-14311** is not detected, as on CloudLab (a capability limit, closed by the owner): the formula is
UNSAT_CLOSED and substantive (`tools/analysis/vacuity.py`: 9 paths, 8 of them free; 1 of 5 reads offered another
writer). The re-pairing the bug needs, volume 2's `layoutVersion` read paired with volume 1's upgrade-task write, is
never realized (the case README and `docs/handover/BUGGY-DETECT.md` name why).
