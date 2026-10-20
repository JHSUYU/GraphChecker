# START HERE: GraphChecker's HBase work, handed over on 2026-10-19 night

You are the next lead (a coding agent that may run up to 5 coding agents). This file is self-contained: where HBase
stands, what to read, what is left, how to run a case, and where everything is. Repo: `/u/vnr3ne/GraphChecker`, GitHub
`git@github.com:JHSUYU/GraphChecker.git`. HBase's branch is `system/hbase` (local only, not pushed yet: pushing
GraphChecker needs the owner's OK). Its integration worktree is `/bigtemp/vnr3ne/wt/gc-hbase-merge`, on `hbase-int`
(= `system/hbase`); the plain worktree is `/bigtemp/vnr3ne/wt/gc-hbase`. The HBase tree is the fork's
`graphchecker/hbase-checks` (`https://github.com/JHSUYU/hbase.git`, 985a0dfe91, pushed; local `/u/vnr3ne/hbase`
branch `gc/hbase-checks`). Nothing runs on any lift. Solr and HDFS are finished: STATE §S and §0, on their own branches.

## 1. Where HBase stands

The owner's goal (2026-10-19): "基于我们solr现在这么好的代码基础，完成对hbase的adhod check". The checks are
`docs/checks/HBASE.md`: 17 study checks plus the owner's five bugs, 22 cases in `experiments/hbase/hbase-cases.tsv`.
In one day a lead and five coding agents built the platform on Solr's engine and fixed what HBase exposed:
- run determinism: names, ports, start codes, one master at a time, meta on rs0, procedure steps, no WAL, chores off;
- doors: `HBASE_RPC` RPC doors, and ZooKeeper as on Solr;
- identity: async continuations and timers;
- the VM: enums, sorted maps;
- PLAN, COMPOSE and CONFIRM: about 15 general fixes;
- `tools/analysis/vacuity.py`, which says whether an UNSAT is vacuous.

The owner stopped everything at 23:10 for this handover. At the stop:
- **PASS:** hbase-bugs-backup-lock-reply-lost. SAT, confirmed in the VM, reproduced natively 10/10 (control 0/10), 551 s.
- **SAT confirmed in the VM:** hbase-adhoc-04 = HBASE-30484 (one lost EnableTable request, 631 s). REPRODUCE did not
  run natively (TODO HBase 3), and its `.smt` has not been read by hand yet.
- **Fixed, but not rerun:**
  - HBASE-30483 (22): the right claim was composed and refused only by a CONFIRM shortcut that is now fixed.
  - master-active-time (#11): its "moves nothing" claims came from an unplaced clock. Fixed; offline it now gives a
    CLOCK_SKEW claim.
  - ns-rsgroup-removal (#13): a tree workaround is merged that gives its check a tracked value and a fault-opened window.
- **Vacuous UNSATs:** 08, 13, 34, 37, and 31 on its old workload. Each one's reason is in HBASE.md §E.
- **No result yet:** every other case was stopped mid-run, failed early on a defect that is now fixed, or was never run.

## 2. Read, in this order

1. This file.
2. [STATE.md](STATE.md) §H: what is on `system/hbase` and the tree, the results table, and where everything is.
3. [TODO.md](TODO.md) "HBase": item 1 lists the next runs, in order; the other items are the open engine problems,
   each with its evidence.
4. [LESSONS.md](LESSONS.md), all of it, especially §9 HBase: run determinism first, vacuity, "moves nothing" claims,
   workarounds that remove what another fix needs, fault kinds, and use of the cluster.
5. `docs/checks/HBASE.md` §E: every case's target, workload, selector, scope and state.
6. [RULES.md](RULES.md): the owner's rulings, including today's HBase rulings: no WAL, local IO, small scope, several
   counterfactuals, fill in lost context in system code, workaround over grinding.
   Then [CHECKING.md](CHECKING.md) (trap 24: vacuous UNSAT), [OPERATIONS.md](OPERATIONS.md) §10 (HBase runs),
   [AGENTS.md](AGENTS.md) and [PARALLEL.md](PARALLEL.md).
7. The five agents' handover notes, [hbase-agents/H1-H5.md](hbase-agents/) (copies of `/bigtemp/vnr3ne/analysis/hbase-2026-10-19/handover/H1-H5.md`). They hold the exact
   run directories, snapshots, tree sets, launch helpers, per-case next steps, traps and leftovers.
   - H1: the platform (15, 13, 14, 35, 28, 07).
   - H2: ZooKeeper (#11, 24, 34, 37).
   - H3: RPC (#12, 10, 11, 12, 31).
   - H4: checks and workloads (04, 22, nsrg, 08, 19, 20, 21).
   - H5: engine analysis, offline tools.
8. `docs/design/PIPELINE.md` for the stage you touch, and `docs/REPRODUCE.md` §7 to run HBase from a fresh clone.

## 3. Running a case

[OPERATIONS.md](OPERATIONS.md) §10 has the steps:
1. Snapshot `system/hbase`.
2. Build a tree set from `gc/hbase-checks` with its own Maven repository.
3. Launch one case, detached, with its head on its own host, image `vm-force12`, and every host as a replay worker.
4. Watch it with the watchdog.
5. When it ends, run `vacuity.py`, write the reading, then update HBASE.md §E and the STATUS row.

Built tree sets you can use at once:
- `/bigtemp/vnr3ne/wt/hb-checks-trees-20` (985a0dfe91, nsrg's workaround)
- `/bigtemp/vnr3ne/wt/hb-platform-trees-9` (f9340f2aab, 16 workloads)

A case is done as follows:
- **Bug check:** SAT, CONFIRMED in the VM, REPRODUCED natively, with the bug's causal chain.
- **Study check:** SAT confirmed, or UNSAT at the fixed point that vacuity.py does not call vacuous, or a named bound.
  In every case the `.smt` must be read against the HBase code.

## 4. Rules you must keep (each is in RULES.md or LESSONS.md)

- General fixes only. A per-system adapter or workaround is small and named in STATUS "Per-system surface".
  A workaround may make an order controllable or a value trackable, but it never switches the fatal outcome itself.
- Read the existing mechanism before building one. Time-box an engine challenge to about 45 min, then use a workaround
  (owner).
- Measure first, prove the mechanism, then fix. Completeness > precision: over-approximate in COMPOSE, confirm strictly.
- HBase changes are judged by HBase's cases only; Solr is not rerun.
- Heaps: replays and solvers use at most 70 % of a host; a head is charged its full heap for life.
- Shell and git:
  - Always `env -u BASH_ENV`; kill only by explicit pid; never `git add -A`; never `rm -rf $VAR/...` unquoted.
  - Commit trailer: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
  - Push GraphChecker only with the owner's OK. The HBase fork may be pushed; apache never.
- Decide engineering yourself and report. At most 5 coding agents, one branch and worktree each; the lead merges after
  a gate.
