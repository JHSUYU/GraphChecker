# HBase: the old bugs put back (buggy-detect), each case alone on liftlab (round E1)

Each case's final formula is `<case>.smt2.gz` (the gzip of the run's `schedule/final/candidate.smt2`) and its claim
`<case>.claim.json`, both from round E1; `index.tsv` names the run each came from (under `/bigtemp/vnr3ne/gc-out/`). The
cases are `experiments/hbase/hbase-buggy-cases.tsv`, each case's README the bug, what was put back, the workload and
every run. `docs/handover/BUGGY-DETECT.md` has all four systems' table: the CloudLab runs of 2026-10-26, B1 and E1.

E1 (2026-10-29, the owner: every case alone, for the time breakdown): this branch's snapshot
`/u/vnr3ne/gc-run/bd-hbase-1`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1` (`experiments/hbase/prepare-trees.sh` from
the fork's `*-bug-<jira>` branches), one case at a time on the 11 liftlab workers (lift02-06, 08-10, 12-14) with nothing
else running: `tools/rounds/launch-round.sh` with that one case in `CASES`, the next case started once the summary row
was written and no process of the run was left (`/bigtemp/vnr3ne/analysis/buggy-detect-exclusive-2026-10-28/series-E1.sh`),
`CASE_TIMEOUT_SECONDS=21600`. Detected = SAT, CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with the
control 0/N, report.py PASS.

Again: `GC_OUT=<dir> results/hbase-buggy/collect-results.sh experiments/hbase/hbase-buggy-cases.tsv <round>` copies the
files, and `results/hbase-buggy/final-stats.py --cases experiments/hbase/hbase-buggy-cases.tsv --round <round> --out <dir>`
makes the table (seeding = PREFLIGHT..IMPORT and ZKKEYS; exploration = EXPLORE; compose+solver = COMPOSE + SOLVE +
DECIDE; other = CONFIRM + EMIT + REPRODUCE; refuted claims = the claims CONFIRM refuted before the last; regions /
occurrences = the final closure; rounds = EXPLORE's generations).

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hbase-buggy-20642 | HBASE-20642 | hbase-adhoc-04 | E1-hbase-buggy-20642 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 0/10, by shape 10/10; control 0/10 | 1504 | 334 | 332 | 15 | 4 | 819 (7) | 3 | 40 | 3 |
| hbase-buggy-15039 | HBASE-15039 | hbase-adhoc-34 | E1-hbase-buggy-15039 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 8/10; control 0/10 | 850 | 303 | 409 | 10 | 113 | - | 5 | 9 | 6 |

2 of 2 cases ran (E1); wall 2354 s; seeding 637, exploration 741, compose+solver 25, other 117

hbase-buggy-20642: 819 s of its wall are the 7 claims CONFIRM refuted before the last (B1: 681 s, 5 claims); native
REPRODUCE by exact id 0/10 and by IDENTITY §9 shape 10/10 (accepted by the owner), as in B1. hbase-buggy-15039 reproduced
natively 8/10 alone (B1 10/10, the fresh-clone check F1 9/10), the control 0/10.

## N1 (2026-10-29): the whole exploration, each case alone

The cases whose E1 exploration ended WITNESSED, again alone, with `CAUSYNTH_STREAM_STOP_AT_WITNESS=false` (`run_engine.sh` `stream_stop_at_witness`, `docs/design/PIPELINE.md`): no
session is a witness, every exploration runs to FIXED_POINT, and COMPOSE, SOLVE, DECIDE and CONFIRM run once over the
whole corpus (snapshot `/u/vnr3ne/gc-run/bd-hbase-2`; runs under
`/bigtemp/vnr3ne/gc-out/buggy-detect-full`; `docs/handover/BUGGY-DETECT.md` "Time, the whole exploration" compares
them with E1). The formulas and claims above stay E1's.

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hbase-buggy-20642 | HBASE-20642 | hbase-adhoc-04 | N1-hbase-buggy-20642 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 0/10, by shape 10/10; control 0/10 | 1720 | 320 | 463 | 51 | 110 | 776 (2) | 3 | 40 | 27 |
| hbase-buggy-15039 | HBASE-15039 | hbase-adhoc-34 | no run |  |  |  |  |  |  |  |  |  |  |  |  |  |  |

1 of 2 cases ran (N1); wall 1720 s; seeding 320, exploration 463, compose+solver 51, other 110

## B1 (2026-10-28): the cases side by side, for comparison

The same snapshot and trees, the cases beside each other and beside the other systems' on the liftlab workers
(`launch-round.sh` with several cases in `CASES`); the runs are under `/bigtemp/vnr3ne/gc-out/buggy-detect`.

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hbase-buggy-20642 | HBASE-20642 | hbase-adhoc-04 | B1-hbase-buggy-20642 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 0/10, by shape 10/10; control 0/10 | 1393 | 329 | 272 | 11 | 100 | 681 (5) | 3 | 40 | 3 |
| hbase-buggy-15039 | HBASE-15039 | hbase-adhoc-34 | B1-hbase-buggy-15039 | SAT_CANDIDATE | PASS | STATE_PAIRING_FLIPPED | yes | 10/10; control 0/10 | 755 | 315 | 303 | 7 | 124 | - | 5 | 7 | 4 |

2 of 2 cases ran (B1); wall 2148 s; seeding 644, exploration 575, compose+solver 18, other 224
