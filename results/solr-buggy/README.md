# Solr: the old bugs put back (buggy-detect), each case alone on liftlab (round E1)

Each case's final formula is `<case>.smt2.gz` (the gzip of the run's `schedule/final/candidate.smt2`) and its claim
`<case>.claim.json`, both from round E1; `index.tsv` names the run each came from (under `/bigtemp/vnr3ne/gc-out/`). The
cases are `experiments/solr/solr-buggy-cases.tsv`, each case's README the bug, what was put back, the workload and
every run. `docs/handover/BUGGY-DETECT.md` has all four systems' table: the CloudLab runs of 2026-10-26, B1 and E1.

E1 (2026-10-29, the owner: every case alone, for the time breakdown): this branch's snapshot
`/u/vnr3ne/gc-run/bd-solr-1`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1` (`experiments/solr/prepare-trees.sh` from
the fork's `*-bug-<jira>` branches), one case at a time on the 11 liftlab workers (lift02-06, 08-10, 12-14) with nothing
else running: `tools/rounds/launch-round.sh` with that one case in `CASES`, the next case started once the summary row
was written and no process of the run was left (`/bigtemp/vnr3ne/analysis/buggy-detect-exclusive-2026-10-28/series-E1.sh`),
`CASE_TIMEOUT_SECONDS=21600`. Detected = SAT, CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with the
control 0/N, report.py PASS.

Again: `GC_OUT=<dir> results/solr-buggy/collect-results.sh experiments/solr/solr-buggy-cases.tsv <round>` copies the
files, and `results/solr-buggy/final-stats.py --cases experiments/solr/solr-buggy-cases.tsv --round <round> --out <dir>`
makes the table (seeding = PREFLIGHT..IMPORT and ZKKEYS; exploration = EXPLORE; compose+solver = COMPOSE + SOLVE +
DECIDE; other = CONFIRM + EMIT + REPRODUCE; refuted claims = the claims CONFIRM refuted before the last; regions /
occurrences = the final closure; rounds = EXPLORE's generations).

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| solr-buggy-6101 | SOLR-6101 | solr-adhoc-19 | E1-solr-buggy-6101 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 632 | 283 | 292 | 8 | 32 | - | 4 | 52 | 21 |
| solr-buggy-6197 | SOLR-6197 | solr-adhoc-19 | E1-solr-buggy-6197 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 539 | 273 | 220 | 8 | 34 | - | 4 | 31 | 15 |
| solr-buggy-9440 | SOLR-9440 | solr-adhoc-31 | E1-solr-buggy-9440 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 576 | 336 | 143 | 4 | 71 | - | 6 | 36 | 9 |

3 of 3 cases ran (E1); wall 1747 s; seeding 892, exploration 655, compose+solver 20, other 137

solr-buggy-9440 reproduced natively 10/10 alone (B1, side by side: 6/10; CloudLab 10/10), the control 0/10. Alone,
Solr's seeding takes 273-336 s (B1: 539-657 s, with the three Solr cases seeding at once) and every case finishes in
539-632 s (B1: 884-988 s).

## B1 (2026-10-28): the cases side by side, for comparison

The same snapshot and trees, the cases beside each other and beside the other systems' on the liftlab workers
(`launch-round.sh` with several cases in `CASES`); the runs are under `/bigtemp/vnr3ne/gc-out/buggy-detect`.

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| solr-buggy-6101 | SOLR-6101 | solr-adhoc-19 | B1-solr-buggy-6101 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 884 | 539 | 302 | 6 | 33 | - | 4 | 42 | 16 |
| solr-buggy-6197 | SOLR-6197 | solr-adhoc-19 | B1-solr-buggy-6197 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 988 | 653 | 291 | 5 | 35 | - | 4 | 32 | 16 |
| solr-buggy-9440 | SOLR-9440 | solr-adhoc-31 | B1-solr-buggy-9440 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 6/10; control 0/10 | 907 | 657 | 158 | 5 | 81 | - | 6 | 36 | 4 |

3 of 3 cases ran (B1); wall 2779 s; seeding 1849, exploration 751, compose+solver 16, other 149
