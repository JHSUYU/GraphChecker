# Solr: the old bugs put back (buggy-detect), round B1 on liftlab

Each case's final formula is `<case>.smt2.gz` (the gzip of the run's `schedule/final/candidate.smt2`) and its claim
`<case>.claim.json`; `index.tsv` names the run each came from (under `/bigtemp/vnr3ne/gc-out/`). The cases are
`experiments/solr/solr-buggy-cases.tsv`, each case's README the bug, what was put back, the workload and every run.
`docs/handover/BUGGY-DETECT.md` has all four systems' table, the CloudLab runs of 2026-10-26 beside B1.

B1 (2026-10-28): this branch's snapshot `/u/vnr3ne/gc-run/bd-solr-1`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1`
(`experiments/solr/prepare-trees.sh` from the fork's `*-bug-<jira>` branches), the cases beside each other and beside
the other systems' on the liftlab workers (`tools/rounds/launch-round.sh` with `CASES`), `CASE_TIMEOUT_SECONDS=21600`.
Detected = SAT, CONFIRM realizes it in the VM, native REPRODUCE reproduces it k/N with the control 0/N, report.py PASS.

Again: `GC_OUT=<dir> results/solr-buggy/collect-results.sh experiments/solr/solr-buggy-cases.tsv <round>` copies the files, and
`results/solr-buggy/final-stats.py --cases experiments/solr/solr-buggy-cases.tsv --round <round> --out <dir>` makes the table
(seeding = PREFLIGHT..IMPORT and ZKKEYS; exploration = EXPLORE; compose+solver = COMPOSE + SOLVE + DECIDE; other =
CONFIRM + EMIT + REPRODUCE; regions / occurrences = the final closure; rounds = EXPLORE's generations).

| case | bug | point | run | claim | report.py | mechanism | CONFIRM | native REPRODUCE | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| solr-buggy-6101 | SOLR-6101 | solr-adhoc-19 | B1-solr-buggy-6101 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 884 | 539 | 302 | 6 | 33 | - | 4 | 42 | 16 |
| solr-buggy-6197 | SOLR-6197 | solr-adhoc-19 | B1-solr-buggy-6197 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 10/10; control 0/10 | 988 | 653 | 291 | 5 | 35 | - | 4 | 32 | 16 |
| solr-buggy-9440 | SOLR-9440 | solr-adhoc-31 | B1-solr-buggy-9440 | SAT_CANDIDATE | PASS | MARKER_FLIPPED | yes | 6/10; control 0/10 | 907 | 657 | 158 | 5 | 81 | - | 6 | 36 | 4 |

3 of 3 cases ran (B1, beside each other on liftlab); wall 2779 s; seeding 1849, exploration 751, compose+solver 16, other 149
