# START HERE: GraphChecker's Solr work after the final round SGF9 (2026-10-19)

You are the next lead (a coding agent that may run up to 5 coding agents). This file is self-contained: where Solr
stands, what to read, what is left, how to run a case, and where everything is. Repo: `/u/vnr3ne/GraphChecker`, GitHub
`git@github.com:JHSUYU/GraphChecker.git`; Solr's branch is `system/solr` (pushed; integration worktree
`/bigtemp/vnr3ne/wt/gc-solr-merge` on `solr-int` = `system/solr`, worktree `/bigtemp/vnr3ne/wt/gc-solr`). The Solr tree
is the fork's `graphchecker/solr-checks` (`https://github.com/JHSUYU/solr.git`, 12d23091d1). Nothing runs on any lift.

## 1. Where Solr stands

The 2026-10-18 rewrite (REFACTOR-PLAN workstreams A-H) is merged into `system/solr`, and the final round SGF9 ran the
12 study checks each alone on lift02-10 + lift12-15 at world depth 0 (the 8 bug checks keep their SGF7 results: SAT,
confirmed, native 10/10). The owner ended the round on 2026-10-19 ("剩余的case我们不跑了，不要了"): 14, 07 and 31 were
not rerun. Each case's latest result and time is STATUS "Solr checks"; the round's per-case notes are
`/bigtemp/vnr3ne/analysis/solr-2026-10-18/final9/RESULTS.txt`.

- Results on the rewritten engine: 38 SAT, confirmed in the VM (922 s); 21 UNSAT_CLOSED (994 s); 39 UNSAT_CLOSED
  (1200 s); 09, 13, 10, 40, 19 formula UNSAT at FIXED_POINT with named blockers (1417, 1762, 5532, 8731, 2672 s); 05
  composed all 340 paths but its decide answered nothing (every scoped z3 out of memory at the fixed pair slot) and it
  ended at its 14400 s budget.
- The round found three defects whose fixes are on `system/solr` but which no case has run on yet: the z3 pair slot
  (a memout re-asks at twice the slot while the host holds it), COMPOSE's hold let go before it lowers the body (05
  out of heap otherwise), and the fixed point beside unlanded GROW re-runs (reverted: 39 composed 8 paths where SGF8
  composed 57; 19, 13, 09 also ended with re-run sessions no round planned over). The cases whose results they affect
  are listed in TODO "Solr: after SGF9".

## 2. Read, in this order

1. This file.
2. [STATE.md](STATE.md) §S -- what is on `system/solr`, the fork, the images, the round.
3. [TODO.md](TODO.md) "Solr: after SGF9" -- what is left, in order, each with its evidence.
4. [LESSONS.md](LESSONS.md) -- the traps (shell, zombies and hung agents, NFS, heaps, Java 8 concurrency), how to
   measure, how to debug. Read all of it before running anything.
5. [RULES.md](RULES.md), [AGENTS.md](AGENTS.md), [OPERATIONS.md](OPERATIONS.md), [PARALLEL.md](PARALLEL.md),
   [CHECKING.md](CHECKING.md), [OPTIMIZATIONS.md](OPTIMIZATIONS.md) (every optimization, done, reverted and owed),
   [REFACTOR-PLAN.md](REFACTOR-PLAN.md) (the rewrite's plan, done).
6. `docs/design/PIPELINE.md` for the stage you touch; `docs/REPRODUCE.md` §6 to run the Solr cases from a fresh clone.

## 3. Running a case

From a fresh clone: [../REPRODUCE.md](../REPRODUCE.md) §6 (GraphChecker `system/solr`, the image built from the same
branch -- the runtime refuses an older image by name --, the fork's tree, one case or the series). On this cluster:

1. A snapshot of the head: `tools/lib/worktree-add.sh /u/vnr3ne/gc-run/<name> <commit> --detach`, then
   `mvn -q -o package -DskipTests` on a lift (`tools/onlift.sh -g 4`); never rebuild a snapshot a run reads.
2. One case at a time, detached on lift06, with the round driver
   `/bigtemp/vnr3ne/analysis/solr-2026-10-18/final9/final-seq9.sh <snapshot> /bigtemp/vnr3ne/wt/sg3j-trees lift06 <case:budget>...`
   (`PREFIX=<round>`, `VM_IMAGE=/bigtemp/vnr3ne/vm-force10/j2sdk-image`; check the first case's `.job` names that
   image). Give the big cases (05, 07, 14) 21600 s: 05's exploration alone took 10701 s.
3. Arm `/bigtemp/vnr3ne/analysis/solr-2026-10-18/final9/watchdog9p.sh` and a case-end waiter on the round log; after
   each case `analysis/solr-2026-10-14/final-stats.py <round>`, a reading, the STATUS row.

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

- Evidence: `/bigtemp/vnr3ne/analysis/solr-2026-10-18/` -- final9/ (the round: RESULTS.txt, c19, c39, c39b, growchain,
  growshape, fixedpoint, z3slot), resume/ (the agents' briefs), and the rewrite's studies (redundancy, world-dedup,
  gen1, hold, ...).
- Runs: `/bigtemp/vnr3ne/gc-out/solr/accept-<round>-<case>` (SGF9: the round; SGF9KILLED/STOP/REGR/VM8: evidence).
- Tools: final-stats.py, the driver and watchdog under final9/, GzCopy, HeapOwners, the offline COMPOSE recipe
  `analysis/solr-2026-10-18/hold/compose-run.sh`.
