# Solr: the final .smt of every case

Each case's final formula is `<case>.smt2.xz`, the xz of the run's `schedule/final/candidate.smt2` (Solr's formulas run
to 830 MB: xz keeps every file far under GitHub's 100 MB, where gzip left 146 MB), and its claim `<case>.claim.json.xz`;
`unxz -k <file>` restores them. `index.tsv` names the run each came from (under `/bigtemp/vnr3ne/gc-out/`).

**The 8 bug checks PASS** (SAT, confirmed in the VM, reproduced natively; SGF7, 2026-10-14/16): SOLR-18406 and
SOLR-18413 (CLOCK_SKEW), and the six bug_study checks reindex-cleanup, migrate-buffer-leak, overseer-lock-leak,
snapshot-no-active, restore-construction, tra-start-overwrite. **Every one of the 12 study checks has its `.smt`**: 38
SAT (confirmed in the VM, native 0/10: the PULL replicas' getLeader hang), 21 UNSAT_CLOSED, 07 a substantive UNSAT, the
rest an UNSAT the run names its limits for (one reading per case below; each UNSAT read with `tools/analysis/vacuity.py`).

The runs: the bug checks and 38 21 10 40 keep their SGF7/SGF9 records (`system/solr` of 2026-10-14..19, tree
`graphchecker/solr-checks` 12d23091d1, images vm-force8/vm-force10). The eight cases SGF9 left without a clean result ran
again on `system/solr` with the fixes they found (owner 2026-10-22: finish them, cap a growing case; STATE §S), each
alone for its time: X1 on snapshot sr-5 (3351d5979: 09 13 39 19 14), X1B and X1C on sr-6 (f4e8cb84d: 07, then 05 and 31
after the servers went down), the same tree, image vm-force10, 12-13 lifts. Their configuration is in
`experiments/solr/solr-adhoc/case.sh` (05 07 14 31: no client faults, the first claim; 14: at most 117 composed paths)
and `workflow.properties` (`explore_budget_s` 7200: the exploration runs at most 2 h, owner 2026-10-22).

**Run one case:** `CAUSYNTH_CUSTOM_JDK_HOME=<image> GC_TREES=<tree set> tools/rounds/launch-run.sh <checkout of
system/solr> <case> <tag>` (it holds the shell until the case ends; REPRODUCE §6 builds the image and the tree from
GitHub). **Run all:** `tools/rounds/run-series.sh <round> experiments/solr/solr-cases.tsv system/solr=<checkout>`.

The table below is `final-stats.py` over the run dirs. Its columns:
- seeding: PREFLIGHT..IMPORT and ZKKEYS (static passes, recording, seed replay)
- exploration: EXPLORE (at most 7200 s for the owed cases)
- compose+solver: COMPOSE + SOLVE + DECIDE
- other: CONFIRM + EMIT + REPRODUCE
- refuted claims: the compose and CONFIRM of claims CONFIRM refuted before the last (none here)
- regions / occurrences: the final closure (distinct regions; its execution-plan rows); rounds: EXPLORE's generations

| case | run | mode | claim | mechanism | native | wall (s) | seeding (s) | exploration (s) | compose+solver (s) | other (s) | refuted claims (s) | regions | occurrences | rounds |
| --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| solr-18406 | SGF7-18406 | alone | SAT_CANDIDATE | CLOCK_SKEW | 10/10 | 828 | 338 | 430 | 13 | 39 | - | 13 | 44 | 10 |
| solr-18413 | SGF7-18413 | alone | SAT_CANDIDATE | CLOCK_SKEW | 8/10 | 2019 | 521 | 1200 | 11 | 260 | - | 25 | 269 | 2 |
| solr-bugs-reindex-cleanup | SGF7-bugs-reindex-cleanup | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 1113 | 459 | 507 | 97 | 44 | - | 12 | 86 | 2 |
| solr-bugs-migrate-buffer-leak | SGF7-bugs-migrate-buffer-leak | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 699 | 379 | 278 | 5 | 32 | - | 11 | 63 | 9 |
| solr-bugs-overseer-lock-leak | SGF7-bugs-overseer-lock-leak | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 875 | 303 | 373 | 10 | 184 | - | 5 | 43 | 15 |
| solr-bugs-snapshot-no-active | SGF7-bugs-snapshot-no-active | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 878 | 408 | 420 | 4 | 39 | - | 14 | 119 | 1 |
| solr-bugs-restore-construction | SGF7-bugs-restore-construction | alone | SAT_CANDIDATE | MARKER_FLIPPED | 10/10 | 610 | 315 | 249 | 7 | 33 | - | 7 | 66 | 9 |
| solr-bugs-tra-start-overwrite | SGF7-bugs-tra-start-overwrite | alone | SAT_CANDIDATE | STATE_PAIRING_FLIPPED | 10/10 | 943 | 311 | 595 | 5 | 29 | - | 5 | 35 | 4 |
| solr-adhoc-05 | X1C-adhoc-05 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 11503 | 789 | 7278 | 3152 | 254 | - | 18 | 280 | 56 |
| solr-adhoc-07 | X1B-adhoc-07 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 9541 | 808 | 7286 | 1072 | 342 | - | 18 | 324 | 88 |
| solr-adhoc-09 | X1-adhoc-09 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 1951 | 516 | 1268 | 131 | 27 | - | 18 | 137 | 36 |
| solr-adhoc-10 | SGF9-adhoc-10 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 5532 | 738 | 4430 | 277 | 65 | - | 25 | 498 | 44 |
| solr-adhoc-13 | X1-adhoc-13 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 1912 | 517 | 1025 | 342 | 20 | - | 23 | 253 | 54 |
| solr-adhoc-14 | X1-adhoc-14 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 13686 | 665 | 7250 | 5437 | 293 | - | 20 | 406 | 37 |
| solr-adhoc-19 | X1-adhoc-19 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 3809 | 393 | 3153 | 185 | 76 | - | 10 | 49 | 78 |
| solr-adhoc-21 | SGF9-adhoc-21 | alone | UNSAT_CLOSED | NO_SUPPORTED_WITNESS | - | 994 | 342 | 618 | 23 | 7 | - | 21 | 72 | 33 |
| solr-adhoc-31 | X1C-adhoc-31 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 10909 | 784 | 7251 | 1617 | 1214 | - | 24 | 635 | 87 |
| solr-adhoc-38 | SGF9-adhoc-38 | alone | SAT_CANDIDATE | MARKER_FLIPPED | 0/10 | 922 | 337 | 226 | 10 | 344 | - | 14 | 86 | 11 |
| solr-adhoc-39 | X1-adhoc-39 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 5077 | 646 | 4110 | 259 | 53 | - | 21 | 305 | 81 |
| solr-adhoc-40 | SGF9-adhoc-40 | alone | RUN_DEFECT | NO_SUPPORTED_WITNESS | - | 8731 | 719 | 5673 | 2209 | 116 | - | 26 | 418 | 45 |

20 cases; wall 82532 s (22.9 h); seeding 10288, exploration 53620, compose+solver 14866, other 3471, refuted claims 0 s

## Reading per case

- **The 8 bug checks** (SGF7): PASS, each SAT with its mechanism, confirmed in the VM and reproduced natively
  (18413: fatal 10/10 natively, 8 of them at the anchor with the claim's order held); STATUS "Solr checks" has each
  causal chain.
- **solr-adhoc-38** (SGF9): SAT MARKER_FLIPPED, confirmed in the VM (the witness session itself), native 0/10: the PULL
  replicas' getLeader hang, as SGF7.
- **solr-adhoc-21** (SGF9): UNSAT_CLOSED, 18 paths composed, none refused.
- **solr-adhoc-10, -40** (SGF9): formula UNSAT at FIXED_POINT, closure truncated past the task bound (named); 40 also 2
  hard-lane solver timeouts and one occurrence no session ran.
- **solr-adhoc-07** (X1B): UNSAT, substantive. Exploration at the 2 h cap; 295 paths with guard terms, 254 free (the
  core-map read offered another writer: its re-pairing explored), no witness; 1 ADMISSION_GAP named.
- **solr-adhoc-09** (X1): UNSAT, vacuous by construction (class C). DeleteReplicaCmd:277 throws on `!callable.call()`,
  and the callable returns the constants `Boolean.TRUE`/`FALSE`; the cause (both 30 s `waitForCoreNodeGone` waits timing
  out) is control flow inside the lambda that no term carries.
- **solr-adhoc-14** (X1): UNSAT, vacuous by construction (class C). SplitShardCmd:164 tests the `Stat` ZooKeeper
  `exists()` returned for the parent leader's live znode, which no root carries; its counterfactual, the leader's
  session lost, is planted by no explored world. 117 of 419 admitted paths composed (the cap). Its first finished run.
- **solr-adhoc-05** (X1C): UNSAT, vacuous (NO_ROOT). ZkController:1273 re-reads the cluster state after `waitForState`
  saw the replica; its slice's reads are offered no other writer on any of the 349 paths (no earlier writer is eligible
  once the watch saw the replica). Its first finished run (SGF8 out of heap, SGF9 at its budget in DECIDE).
- **solr-adhoc-39** (X1): UNSAT, vacuous (NO_ROOT). 249 paths reach the target; its guard reads the immutable `Aliases`
  map (its one writer its INITIAL), and the check's counterfactual, re-pairing the `AliasesManager.aliases` reference,
  lies outside that slice; 7 ADMISSION_GAP named.
- **solr-adhoc-19** (X1): UNSAT, vacuous (NO_ROOT). 7 paths composed, 6 not reaching the target (the unplaced clock
  cells, `Composer#unplacedClocks`, refuse the rest); 24 ADMISSION_GAP named.
- **solr-adhoc-13** (X1): named bound. Formula UNSAT at FIXED_POINT over a truncated closure; none of its 123 composed
  paths reaches the target occurrence (RoutedAlias.java:350), so the UNSAT says nothing of it.
- **solr-adhoc-31** (X1C): named bound. Exploration at the 2 h cap; formula UNSAT over 134 composed paths, none reaching
  the target occurrence (CollectionsHandler:1477, FORCELEADER's refusal), so the UNSAT says nothing of it; 35
  TOPOLOGY_DIVERGENCE (replays whose cluster diverged from the recording's) and 17 ADMISSION_GAP named. Its first finished
  run (SGF9 killed at round 26; X1 died at the 1024-task bound, fixed).
