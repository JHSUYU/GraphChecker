# START HERE: GraphChecker's Solr work -- every case has its `.smt` (2026-10-26)

You are the next lead (a coding agent that may run up to 5 coding agents). This file is self-contained: where Solr
stands, what to read, what is left, how to run a case, and where everything is. Repo: `/u/vnr3ne/GraphChecker`, GitHub
`git@github.com:JHSUYU/GraphChecker.git`; Solr's code is the branch `system/solr` (pushed; worktree
`/bigtemp/vnr3ne/wt/gc-solr`). The adapter
(the Solr tree) is the fork's `graphchecker/solr-checks` (`https://github.com/JHSUYU/solr.git`, 12d23091d1). From GitHub:
clone the two; [../REPRODUCE.md](../REPRODUCE.md) builds the image and the tree and runs every case. The old Solr bugs put
back by hand (SOLR-9440, -6101, -6197) are the branch `system/solr-buggy-detect` (its own START-HERE); the other systems'
branches are README "Branches".

## 1. Where Solr stands

All 20 cases have their final `.smt`, claim and time row in [`results/solr/`](../../results/solr/README.md):
- the 8 bug checks PASS (SGF7: SAT, confirmed in the VM, native 10/10; 18413 fatal 10/10);
- the 12 study checks: 38 SAT (confirmed in the VM, native 0/10), 21 UNSAT_CLOSED, 07 a substantive UNSAT, and 05 09 10 13
  14 19 31 39 40 UNSAT with their limits named (vacuous by construction, NO_ROOT, or a truncated closure; one reading
  each in `results/solr/README.md` and STATUS "Solr checks").

The eight cases SGF9 left without a clean result (05 07 09 13 14 19 31 39) were finished on 2026-10-22..26 (owner: "完成剩余
几个没跑完case的adhoc check。如果case扩大，控制一下scope，降低我们的用时"): they found five engine defects, fixed on
`system/solr` (STATE §S), and then each ran alone for its time (series X1/X1B/X1C). The owner's caps: the exploration runs
at most 2 h (`explore_budget_s` 7200), 05 07 14 31 run without client faults and with one claim, 14 composes at most
117 paths.

## 2. Read, in this order

1. This file.
2. [STATE.md](STATE.md) §S -- what is on `system/solr`, the fork, the images, how the owed cases ran.
3. `results/solr/README.md` -- every case's verdict, time and regions, one reading each.
4. [TODO.md](TODO.md) "Solr: after the owed cases" -- what is left, each with its evidence.
5. [LESSONS.md](LESSONS.md) -- the traps (shell, zombies and hung agents, NFS, heaps, Java 8 concurrency), how to
   measure, how to debug. Read all of it before running anything.
6. [RULES.md](RULES.md), [AGENTS.md](AGENTS.md), [OPERATIONS.md](OPERATIONS.md), [PARALLEL.md](PARALLEL.md),
   [CHECKING.md](CHECKING.md), [OPTIMIZATIONS.md](OPTIMIZATIONS.md) (every optimization, done, reverted and owed).
7. `docs/design/PIPELINE.md` for the stage you touch; `docs/REPRODUCE.md` to run the Solr cases from a fresh clone.

## 3. Running a case

From a fresh clone: [../REPRODUCE.md](../REPRODUCE.md) (GraphChecker `system/solr`, the image built from the same
branch -- the runtime refuses an older image by name --, the fork's tree, one case or the series). On liftlab (the
workers are lift02-15 but lift11, the control host where the sessions run, and lift07, unreachable since 2026-10-23;
Maven and Ant only on lift02-06 and lift08-10):

1. A snapshot of the head: `tools/lib/worktree-add.sh /u/vnr3ne/gc-run/<name> <commit> --detach`, then
   `mvn -q -o package -DskipTests` on a lift with Maven (`LIFTS='lift04 lift05 lift06 lift08 lift09 lift10'
   tools/onlift.sh -g 4`); never rebuild a snapshot a run reads.
2. The cases, with the series driver of 2026-10-22: `SNAP=<snapshot> TREES=/bigtemp/vnr3ne/wt/sg3j-trees MAX_CLAIMS=3
   WORKERS='<the workers>' HEADS=lift10 /bigtemp/vnr3ne/analysis/solr-2026-10-22/lead/final/series2.sh <round>
   <concurrency> <case>...` (each run detached on its head, `gc-out/solr-final/accept-<round>-<case>`; image
   `VM_IMAGE`, default vm-force10). Run Solr cases one at a time for their time, at most 3 at once otherwise: the 21.5 GB
   head steps starve beside more (R1-14's planner never started among 8). The last snapshot is `/u/vnr3ne/gc-run/sr-6`.
3. Watch with `/bigtemp/vnr3ne/analysis/solr-2026-10-22/lead/lead-watch3.sh` (run ends, series lines, a log quiet 25
   min, a lift past 80 %) and `lead/watchdog.sh`; after each case `tools/analysis/vacuity.py --latest --detail <run>`, a
   reading, the STATUS row; `results/solr/final-stats.py` prints the table over `results/solr/index.tsv`.

## 4. Rules you must keep (each in RULES.md or LESSONS.md)

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

## 5. Where things are

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
