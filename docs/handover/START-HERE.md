# START HERE: taking over GraphChecker's Solr work (handover 2026-10-18)

You are the new lead (a coding agent that may run up to 5 coding agents). This file is self-contained: the mission,
what to read, the open work, how to run the final round, and where everything is. The details behind each line are in
the documents it names. Repo: `/u/vnr3ne/GraphChecker`; integration worktree `/bigtemp/vnr3ne/wt/gc-solr-merge`
(branch `solr-int`), Solr's branch worktree `/bigtemp/vnr3ne/wt/gc-solr` (`system/solr` = `solr-int`, head at the stop
7bd3c5fc8 or later). Nothing ran at the stop; nothing was pushed.

## 1. Mission and completion condition

Finish the Solr rewrite (five open workstreams), merge everything into `system/solr`, then rerun all 20 Solr cases
(`experiments/solr/solr-cases.tsv`), each ALONE on lift02-10 + lift12-15, bug checks first, and debug what breaks.

Done when: the five workstream branches are merged into `system/solr` and gated; the 20 cases each have a result
meeting the acceptance below; STATUS "Solr checks", STATE §S, TODO, OPTIMIZATIONS and LESSONS are updated.

Acceptance: the 8 bug checks (solr-18406, solr-18413, the 6 solr-bugs-*) are SAT + CONFIRMED + native-reproduced;
the 12 study checks (solr-adhoc-*) end SAT or UNSAT (or at a named bound) with claims equal to or more complete than the
old ones (STATUS "Solr checks"); each case has its time breakdown (`/bigtemp/vnr3ne/analysis/solr-2026-10-14/final-stats.py`)
and a light `.smt` reading (`/bigtemp/vnr3ne/analysis/solr-2026-10-14/final-readings.md`).

## 2. Read, in this order

1. This file.
2. [STATE.md](STATE.md) §S -- where things stand, what is merged, what is shelved.
3. [TODO.md](TODO.md) "Solr: the rewrite" -- each workstream's branch, worktree, head, gated vs WIP, exact next steps,
   traps, the generational-bound design with its numbers, and "How to resume: five coding agents".
4. [REFACTOR-PLAN.md](REFACTOR-PLAN.md) -- the owner-approved plan (workstreams A-H, rules, order).
5. [LESSONS.md](LESSONS.md) -- the traps (shell, zombies and hung agents, NFS, heaps, Java 8 concurrency), how to
   measure performance, how to debug and verify. Read all of it before running anything.
6. [RULES.md](RULES.md) (the owner's standing rules, quoted; "The 2026-10-17/18 rulings" first),
   [AGENTS.md](AGENTS.md) (how to brief, split and merge agents; lessons of the rewrite), [OPERATIONS.md](OPERATIONS.md)
   (hosts, ledger, builds, rounds; §9 the 2026-10-18 additions), [PARALLEL.md](PARALLEL.md), [CHECKING.md](CHECKING.md)
   (how a verdict and `.smt` are checked), [OPTIMIZATIONS.md](OPTIMIZATIONS.md) (every optimization, done and owed).
7. When working on a piece: `docs/design/PIPELINE.md` (the stage you touch), `docs/STATUS.md`, and the analysis
   evidence under `/bigtemp/vnr3ne/analysis/solr-2026-10-18/` (one subdirectory per study, named in TODO).

## 3. What is on system/solr (gated)

The GROW pipeline; the superstep + window closure walk; the parallel round and Frontier with its memory fix; the
live-set planner hold rule; gzip rows through one opener (old plain run dirs must be GzCopy'd before the new code reads
them); EMIT's gap ledger in Java (07: 710 -> ~80 s); the holding composer (07: 309/309 paths, UNSAT_CLOSED; it had
composed 1); the compaction of the corpus and walk state (05 r5 planner 12.7 -> 3.5 GB, RSS 20.8 -> 10.6 GB, round
549 -> 398 s). Shelved, never merge: session sharding (branches solr-parplan, solr-shard).

## 4. The open work: five coding agents, one row each (details: TODO "How to resume")

| agent | work | branch (head) | hosts | estimate |
|---|---|---|---|---|
| 1 scheduler | goal 4 (planner/solvers charged their measured need), goal 6 tests + docs (a GROW re-run that can yield no obligation does not hold the fixed point; COMPOSE waits for its paths' re-runs, havocs otherwise), one clean full shell-suite run, a canary of solr-adhoc-13 | solr-stream2 (dd0a1ce64; goals 1-3, 5 gated) | lift05-07, lift11 gates | 2-3 h |
| 2 exploration | KeyGate (no key folds a SAT/ADMITTED with an UNSAT answer) on 07, 05 r2, 14, Z3S-18413; merge the solr-armkey key; then the generational bound (a world flipped at F offers only decisions after F; skip B when it precedes F with the parent's path and the parent answered UNSAT/NOT_FLIPPABLE, or ADMITTED with F owed) | solr-explore (ee0edfcb1, WIP) | lift08, lift14 | 3-5 h, critical path |
| 3 VM decode | each expression definition sent once per session (VM `exp/expression.cpp` + the Java decoder), skip the truncation scan, parallel record decode | solr-replay (fc70638e2: the stall-end fix, gated) | lift15 (VM build), lift13 | 3-5 h, critical path |
| 4 replay end | the replay need from the 90th percentile of peaks + an out-of-heap rerun; stop at the window close after checking every reader of the post-close rows | new solr-replay-end from fc70638e2 | lift09, lift10, lift12 | 2-3 h |
| 5 serial + NFS | split SEED's ~450 unattributed s (the static pass is only 91 of 540 s), INSTRUMENT and the seed replay by phase, then cache/parallelize; gzip the worker schedule and flip query files; solver read seed 20 -> ~160 MB/s | solr-serial (a28597a8f, nothing committed) | lift02-04 | 2-4 h |

Merge order: each branch gated on its own, then into `solr-int` (agent 3 before agent 4; merging solr-replay conflicts
only in OPTIMIZATIONS.md row numbers), a full integration gate (mvn package with tests +
`src/test/shell/run_engine_campaign_helpers_test.sh`, on an idle host -- the shell suite has timing-sensitive cases),
then fast-forward `system/solr`. Expected construction ~4-6 h, integration ~1 h.

**World depth (owner, 2026-10-18):** in theory unbounded. Once the generational bound and the key are in, make
"no cap" the default (delete the depth-0 lines in `experiments/solr/solr-adhoc/case.sh`; let run_engine's
`region_path_max_world_depth` and the engine default mean unbounded); keep the parameter as the owner's manual cap
(named BOUNDED when it cuts). First measure offline on 14 and 39 that obligations per generation fall with depth and
stay near the estimates (14: ~26K/5.2K/1.0K at depths 1/2/3; 39: ~5.7K/3.7K/2.4K); if a generation grows or exceeds
them tenfold, stop and report before the final round. Estimate for 14 unbounded: ~2.5-3.5 h (give it a 5-6 h budget).

## 5. Running the final round

1. Build a snapshot of the integrated head: `tools/lib/worktree-add.sh /u/vnr3ne/gc-run/<name> <commit> --detach`,
   then `mvn -q -o package -DskipTests` on a lift (`tools/onlift.sh -g 4`); never rebuild a snapshot a run reads.
2. Keep every agent off the pool while a case runs (lift11 only); run cases one at a time with the driver
   `/bigtemp/vnr3ne/analysis/solr-2026-10-16/final-seq5.sh <snapshot> /bigtemp/vnr3ne/wt/sg3j-trees lift06 <case:budget>...`
   started detached on lift06 (see `start-sgf8*.sh` beside it; round log `/bigtemp/vnr3ne/gc-out/solr/SGF8-seq.log`; a
   new round prefix keeps old evidence apart). Rename a stopped case's dir to an evidence name before a rerun.
3. Arm the watchdog (`bash /bigtemp/vnr3ne/analysis/solr-2026-10-18/watchdog.sh`, re-arm after each alarm) and a
   case-end waiter on the round log; handle zombies, NFS D-states and stalls at once (LESSONS §2-4).
4. After each case: final-stats, a reading, the STATUS row; report its time breakdown to the owner.

## 6. Rules you must keep (each in RULES.md or LESSONS.md)

- Old code is deleted for good: one implementation per concept, no flags or fallbacks.
- Read the existing mechanism (and system/hdfs, the VM) before building one; a small general workaround beats a huge
  engine change; every workaround is named in STATUS.
- Measure first, prove the mechanism, then fix. No byte-identity requirement any more (owner 2026-10-18 evening,
  "由于我们改动很大。不再要求做语义一致逐字节比较。跑出.smt包含正确的因果链即可，小问题不用死磕"): a change is right when the cases' `.smt` hold the right causal chain and a SAT
  replays (CONFIRM in the VM, REPRODUCE natively); small issues are not ground on. Dedup only what is provably
  equivalent (completeness > precision); over-approximate in COMPOSE, confirm strictly.
- Heaps sized with run_engine's own functions, never by hand; replays/solvers <= 70 % of a host, one head JVM <= 88 %.
- Always `env -u BASH_ENV`; kill only by explicit pid; never `git add -A`; commit trailer
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`; push GraphChecker only with the owner's OK (the fork
  JHSUYU/solr may be pushed; apache never).
- Decide engineering yourself and report; ask the owner only about his own rules. At most 5 coding agents; read-only
  analysts as needed; one review at complex places (concurrency, schedule, soundness).
- Stop protocol: when the owner says stop (or token use reaches ~95 %), every agent commits gated work plus a
  'WIP (not gated): <what>' commit on its branch, kills its JVMs, reports in <= 8 lines; you update STATE/TODO/LESSONS.

## 7. Where things are

- Branches/worktrees: TODO "Solr: the rewrite" (and its cleanup list of worktrees and old snapshots to remove once no run
  reads them).
- Evidence: `/bigtemp/vnr3ne/analysis/solr-2026-10-18/` -- idle-pool (why the pool idled), replay-tail (stall
  run-ons, safe stop), redundancy (heap by owner), obligation-redundancy, world-dedup (the generational bound's numbers),
  capabilities/INVENTORY.md (what the engine, system/hdfs and the VM already do), compact, compose-batch, explore,
  replay-e, int-gate*.
- Tools: GzCopy (`analysis/solr-2026-10-17/nfs/tool/`), HeapOwners (`analysis/solr-2026-10-18/redundancy/tool/`),
  the watchdog, final-stats.py, the driver.
- Runs: `/bigtemp/vnr3ne/gc-out/solr/accept-<round>-<case>`; old SGF7/SGF8 dirs are evidence.
