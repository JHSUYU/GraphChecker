# HDFS: the old bugs put back (buggy-detect), each case alone on liftlab (round E1)

Each case's final formula is `<case>.smt2.gz` (the gzip of the run's `schedule/final/candidate.smt2`) and its claim
`<case>.claim.json`, both from round E1; `index.tsv` names the run each came from (under `/bigtemp/vnr3ne/gc-out/`). The
cases are `experiments/hadoop/hdfs-buggy-cases.tsv`, each case's README the bug, what was put back, the workload and
every run. `docs/handover/BUGGY-DETECT.md` has all four systems' table: the CloudLab runs of 2026-10-26, B1 and E1.

E1 (2026-10-29, the owner: every case alone, for the time breakdown): this branch's snapshot
`/u/vnr3ne/gc-run/bd-hdfs-1`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1` (`experiments/hadoop/prepare-trees.sh` from
the fork's `*-bug-<jira>` branches), one case at a time on the 11 liftlab workers (lift02-06, 08-10, 12-14) with nothing
else running: `tools/rounds/launch-round.sh` with that one case in `CASES`, the next case started once the summary row
was written and no process of the run was left (`/bigtemp/vnr3ne/analysis/buggy-detect-exclusive-2026-10-28/series-E1.sh`),
`CASE_TIMEOUT_SECONDS=21600`. Detected = SAT, CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with the
control 0/N, report.py PASS.

Again: `GC_OUT=<dir> results/hdfs-buggy/collect-results.sh experiments/hadoop/hdfs-buggy-cases.tsv <round>` copies the
files, and `results/hdfs-buggy/final-stats.py --cases experiments/hadoop/hdfs-buggy-cases.tsv --round <round> --out <dir>`
makes the table (seeding = PREFLIGHT..IMPORT and ZKKEYS; exploration = EXPLORE; compose+solver = COMPOSE + SOLVE +
DECIDE; other = CONFIRM + EMIT + REPRODUCE; refuted claims = the claims CONFIRM refuted before the last; regions /
occurrences = the final closure; rounds = EXPLORE's generations).

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hdfs-buggy-11741 | HDFS-11741 | hdfs-adhoc-11 | E1-buggy-11741 | SAT_CANDIDATE | PASS | CLOCK_SKEW | yes | 10/10; control 0/10 | 1123 | 299 | 634 | 149 | 26 | - | 14 | 36 | 9 |
| hdfs-buggy-17383 | HDFS-17383 | hdfs-adhoc-12 | E1-buggy-17383 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 530 | 331 | 158 | 8 | 27 | - | 10 | 14 | 1 |
| hdfs-buggy-12931 | HDFS-12931 | hdfs-adhoc-11 | E1-buggy-12931 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 400 | 244 | 119 | 8 | 21 | - | 12 | 15 | 1 |
| hdfs-buggy-5766 | HDFS-5766 | hdfs-adhoc-11 | E1-buggy-5766 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 391 | 241 | 117 | 4 | 21 | - | 13 | 15 | 1 |
| hdfs-buggy-10609 | HDFS-10609 | hdfs-adhoc-11 | E1-buggy-10609 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 556 | 273 | 244 | 8 | 24 | - | 21 | 32 | 2 |
| hdfs-buggy-14075 | HDFS-14075 | hdfs-adhoc-45 | E1-buggy-14075 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 490 | 348 | 112 | 3 | 20 | - | 3 | 4 | 2 |
| hdfs-buggy-14311 | HDFS-14311 | hdfs-adhoc-24 | E1-buggy-14311 | UNSAT_CLOSED | FAIL | NO_SUPPORTED_WITNESS | no | - | 2521 | 1188 | 1285 | 22 | 9 | - | 21 | 377 | 12 |

7 of 7 cases ran (E1); wall 6011 s; seeding 2924, exploration 2669, compose+solver 202, other 148

**hdfs-buggy-14311** is not detected, as on CloudLab and in B1 (a capability limit, closed by the owner): the formula
is UNSAT_CLOSED and substantive (`tools/analysis/vacuity.py`: 9 paths, 8 of them free; 1 of 5 reads offered another
writer). The re-pairing the bug needs, volume 2's `layoutVersion` read paired with volume 1's upgrade-task write, is
never realized (the case README and `docs/handover/BUGGY-DETECT.md` name why).

hdfs-buggy-11741 took longer alone (1123 s) than in B1 (884 s) over the same closure (14 regions, 36 occurrences) and
the same work (178 admitted replays, B1 180): every replay ran slower, on every worker (median 119 s, B1 95 s), and so
did the head's COMPOSE (149 s, B1 108 s). The hosts are alike and nothing else ran; not explained. The other five
detected cases took 391-556 s alone, within 10 % of B1 or faster.

## B1 (2026-10-28): the cases side by side, for comparison

The same snapshot and trees, the cases beside each other and beside the other systems' on the liftlab workers
(`launch-round.sh` with several cases in `CASES`); the runs are under `/bigtemp/vnr3ne/gc-out/buggy-detect`.

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hdfs-buggy-11741 | HDFS-11741 | hdfs-adhoc-11 | B1-buggy-11741 | SAT_CANDIDATE | PASS | CLOCK_SKEW | yes | 10/10; control 0/10 | 884 | 285 | 460 | 109 | 25 | - | 14 | 36 | 10 |
| hdfs-buggy-17383 | HDFS-17383 | hdfs-adhoc-12 | B1-buggy-17383 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 572 | 320 | 218 | 4 | 27 | - | 10 | 14 | 2 |
| hdfs-buggy-12931 | HDFS-12931 | hdfs-adhoc-11 | B1-buggy-12931 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 368 | 209 | 127 | 3 | 25 | - | 12 | 15 | 1 |
| hdfs-buggy-5766 | HDFS-5766 | hdfs-adhoc-11 | B1-buggy-5766 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 516 | 220 | 261 | 4 | 28 | - | 13 | 15 | 7 |
| hdfs-buggy-10609 | HDFS-10609 | hdfs-adhoc-11 | B1-buggy-10609 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 506 | 254 | 221 | 4 | 24 | - | 21 | 32 | 2 |
| hdfs-buggy-14075 | HDFS-14075 | hdfs-adhoc-45 | B1-buggy-14075 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 463 | 321 | 114 | 4 | 21 | - | 3 | 4 | 2 |
| hdfs-buggy-14311 | HDFS-14311 | hdfs-adhoc-24 | B1-buggy-14311 | UNSAT_CLOSED | FAIL | NO_SUPPORTED_WITNESS | no | - | 2333 | 1117 | 1177 | 17 | 8 | - | 21 | 370 | 11 |

7 of 7 cases ran (B1); wall 5642 s; seeding 2726, exploration 2578, compose+solver 145, other 158
