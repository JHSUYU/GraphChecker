# START HERE: `system/solr-buggy-detect` -- old Solr bugs put back by hand, detected on liftlab

You are the next lead (a coding agent that may run up to 5 coding agents). This branch is `system/solr` (the 20 Solr
ad hoc cases, finished 2026-10-26, `results/solr/`) plus the old Solr bugs that make an ad hoc check's own throw fail,
put back by hand on today's tree, and the engine support they needed. Repo: `/u/vnr3ne/GraphChecker`, GitHub
`git@github.com:JHSUYU/GraphChecker.git`, branch `system/solr-buggy-detect`. Each bug's tree is a branch of the Solr fork
(`https://github.com/JHSUYU/solr.git`): `graphchecker/solr-checks` (12d23091d1) with that one bug put back. The other
systems' branches are README "Branches"; the experiment across the four systems is [BUGGY-DETECT.md](BUGGY-DETECT.md).

## 1. The cases

| case | bug | point | fork branch (tree `$GC_TREES/solr-bug-<jira>`) | CloudLab, 2026-10-26 | liftlab B1 |
| --- | --- | --- | --- | --- | --- |
| solr-buggy-9440 | SOLR-9440: a node whose watch on a collection was dropped keeps its frozen `DocCollection`, where the killed leader is still ACTIVE: FORCELEADER is refused | solr-adhoc-31 | `graphchecker/solr-bug-9440` 1e7324c461 | SAT, native 10/10 (S9440b) | B1: SAT, CONFIRM, native 6/10, control 0/10, report.py PASS, 907 s; CloudLab 10/10 (B1-solr-buggy-9440) |
| solr-buggy-6101 | SOLR-6101: under `legacyCloud=false` SPLITSHARD's sub-shard core-admin CREATE carries no `coreNodeName` and the node refuses it | solr-adhoc-19 | `graphchecker/solr-bug-6101` 040ae6d4c6 | SAT, native 10/10 (S6101g) | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 884 s (B1-solr-buggy-6101) |
| solr-buggy-6197 | SOLR-6197: the same in MIGRATE, for its temporary collection's replica on the target leader | solr-adhoc-19 | `graphchecker/solr-bug-6197` f5d86cbd8a | SAT, native 10/10 (S6197g) | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 988 s (B1-solr-buggy-6197) |
| (solr-buggy-6763) | SOLR-6763 | solr-adhoc-38 | none | not reachable on today's code (masked by SOLR-7844): a README only, no run | -- |

The list is [`experiments/solr/solr-buggy-cases.tsv`](../../experiments/solr/solr-buggy-cases.tsv), the trees
[`experiments/solr/trees.tsv`](../../experiments/solr/trees.tsv); each case's README
(`experiments/solr/solr-buggy-<jira>/README.md`) has the bug, what was put back and why, the workload and its tree
workarounds, every declaration, the runs and their reading. The engine support, reviewed: native REPRODUCE plants a
field-backed CONFIG root at the plan's reads of its field, guarded by a GETFIELD count (61e881776, e5c894636,
ad3d08028; STATE §B). The CloudLab record of 2026-10-26 is the case READMEs' rounds (their `/bulk` paths were that
cluster's); the CloudLab port itself is the tag `archive/system/solr-cloudlab`.

## 2. Read, in this order

1. This file; [BUGGY-DETECT.md](BUGGY-DETECT.md) (the standard, every system's verdicts, the owner's decisions).
2. [STATE.md](STATE.md) §B (this branch) and §S (the ad hoc cases it carries); the three case READMEs.
3. [TODO.md](TODO.md) "Buggy-detect" -- what is left.
4. [LESSONS.md](LESSONS.md), [RULES.md](RULES.md), [CHECKING.md](CHECKING.md), [OPERATIONS.md](OPERATIONS.md),
   [PARALLEL.md](PARALLEL.md), [AGENTS.md](AGENTS.md); `docs/REPRODUCE.md` §6 to run the cases from a fresh clone.

## 3. Running the buggy cases on liftlab (round B1)

The workers are lift02-15 but lift11 (the control host, where the sessions run) and lift07 (unreachable since
2026-10-23); Maven and Ant only on lift02-06 and lift08-10. Image `/bigtemp/vnr3ne/vm-force10/j2sdk-image` (this
branch's VM sources are `system/solr`'s).

1. **The trees** (`bd-trees-1`: every bug tree of the four systems; Solr's three): from a checkout of this branch,
   `experiments/solr/prepare-trees.sh <tree>...` clones each fork branch of `trees.tsv`, builds it with Ant against the
   checkout's jar and runs its workload once natively (`PASSED` per workload, `== <tree>: ready`):

   ```bash
   cd <checkout of system/solr-buggy-detect>
   LIFTS="lift04 lift05 lift06 lift08 lift09 lift10" tools/onlift.sh -g 8 env GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1 \
     GC_M2=/bigtemp/vnr3ne/m2/bd-1 experiments/solr/prepare-trees.sh solr-bug-9440 solr-bug-6101 solr-bug-6197
   ```

   Never rebuild a tree a run reads.
2. **The snapshot**: `tools/lib/worktree-add.sh /u/vnr3ne/gc-run/bd-solr-1 <commit> --detach`, then `mvn -q -o package
   -DskipTests` in it on a lift with Maven (`tools/onlift.sh` as above). `bd-solr-1` is 1bddceee1.
3. **The cases**, all three at once (or one: `CASES=solr-buggy-9440`), from lift11:

   ```bash
   cd /u/vnr3ne/gc-run/bd-solr-1 && env -u BASH_ENV \
     GC_OUT=/bigtemp/vnr3ne/gc-out/buggy-detect GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1 GC_M2=/bigtemp/vnr3ne/m2/bd-1 \
     LIFTS="lift02 lift03 lift04 lift05 lift06 lift08 lift09 lift10 lift12 lift13 lift14" \
     CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force10/j2sdk-image CASE_TIMEOUT_SECONDS=21600 PRUNE=0 \
     CASES="solr-buggy-9440 solr-buggy-6101 solr-buggy-6197" tools/rounds/launch-round.sh /u/vnr3ne/gc-run/bd-solr-1 B1
   ```

   Each case writes `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-<case>/` (a round name is written once: a rerun takes
   a new one). `tools/rounds/round-status.sh B1` (same `GC_OUT`) shows each case's stage; `tools/rounds/stop-run.sh
   B1-<case>`, alone on its command line, stops one. Solr cases at most 3 at once: a head step wants ~23 GB (STATE §S).
4. **Reading a result.** `accept.sh` ends each run with `report.py`: `accept-B1-<case>/summary.tsv` (the verdict row)
   and `report/<case>/report.md` (the claim, the witness's mechanism, the causal cone). PASS needs the case's
   `EXPECTED_MECHANISM` row in `experiments/accept/report.py` (all three `MARKER_FLIPPED`: 6101 and 6197 by the CONFIG
   root `legacyCloud==true` moved to `false`, 9440 by a `SolrZkClient`/`ZooKeeper` fault, no clock), CONFIRM in the VM
   and native REPRODUCE k/N with control 0/N (`out/<case>/schedule/final/reproduce.json`). Then
   `GC_OUT=/bigtemp/vnr3ne/gc-out/buggy-detect tools/rounds/round-verify.sh B1` (how EXPLORE ended, z3 on the
   formula, gaps, moved roots), `tools/analysis/vacuity.py --latest --detail <run dir>` for an UNSAT, and
   `tools/analysis/smt-legend.py <run>/out/<case> --repo <tree>` to read the `.smt` against the tree. The B1 verdicts go
   into BUGGY-DETECT.md and the case READMEs beside CloudLab's.

## 4. The 20 ad hoc cases

They run here as on `system/solr` (its START-HERE): tree `graphchecker/solr-checks` (`/bigtemp/vnr3ne/wt/sg3j-trees`),
`experiments/solr/solr-cases.tsv`, their records in `results/solr/` (runs of `system/solr`). This branch's engine differs
from `system/solr`'s by the native CONFIG plant alone (61e881776, e5c894636, ad3d08028: `ConfirmMain`, `PlantSites`,
`PlantAgent`, `RecordingPlant`).

## 5. Rules you must keep (each in RULES.md or LESSONS.md)

- Old code is deleted for good: one implementation per concept, no flags or fallbacks.
- Read the existing mechanism before building one; a small general workaround beats a huge engine change.
- Measure first, prove the mechanism, then fix. No byte-identity requirement (owner 2026-10-18): a change is right when
  the cases' `.smt` hold the right causal chain and a SAT replays (CONFIRM in the VM, REPRODUCE natively).
  Completeness > precision: a speed rule that ends or skips exploration is argued against every reader of what it
  skips (OPTIMIZATIONS 1.37, reverted).
- Heaps sized with run_engine's own functions; replays/solvers <= 70 % of a host, one head JVM <= 88 %; a long-lived
  JVM is charged its heap's footprint (OPTIMIZATIONS 1.36, reverted).
- Always `env -u BASH_ENV`; kill only by explicit pid; never `git add -A`; never `rm -rf $VAR/...` unquoted (the tool
  blocks it); commit trailer `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`; push GraphChecker only with the
  owner's OK (the fork JHSUYU/solr may be pushed; apache never).
- Decide engineering yourself and report; at most 5 coding agents; read-only analysts as needed.

## 6. Where things are

- The owed cases (2026-10-22..26): `/bigtemp/vnr3ne/analysis/solr-2026-10-22/lead/` (RUNS.txt: every run and
  decision; vacuity-<run>.txt; final/: the series drivers and their logs); runs
  `/bigtemp/vnr3ne/gc-out/solr-final/accept-<round>-<case>` (X1/X1B/X1C the records; R1-R4 concurrent, *STOP*: lost or
  stopped).
- Evidence before: `/bigtemp/vnr3ne/analysis/solr-2026-10-18/` -- final9/ (the round: RESULTS.txt, c19, c39, c39b, growchain,
  growshape, fixedpoint, z3slot), resume/ (the agents' briefs), and the rewrite's studies (redundancy, world-dedup,
  gen1, hold, ...).
- Runs: `/bigtemp/vnr3ne/gc-out/solr/accept-<round>-<case>`: the SGF7 bug checks and SGF9 38 21 10 40 of record
  (the superseded runs were deleted in the 2026-10-22 cleanup).
- Tools: `results/solr/final-stats.py`, the driver and watchdog under final9/, HeapOwners
  (`analysis/solr-2026-10-18/redundancy/tool/`), the offline COMPOSE recipe `analysis/solr-2026-10-18/hold/compose-run.sh`.
