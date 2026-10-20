# START HERE: GraphChecker's HBase work (second session handover, 2026-10-20)

You are the next lead (a coding agent that may run up to 5 coding agents). This file is self-contained: where HBase
stands, what to read, what is left, how to run a case, and where everything is. Repo: `/u/vnr3ne/GraphChecker`, GitHub
`git@github.com:JHSUYU/GraphChecker.git`. HBase's branch is `system/hbase` (local only, not pushed yet: pushing
GraphChecker needs the owner's OK). Its integration worktree is `/bigtemp/vnr3ne/wt/gc-hbase-merge`, on `hbase-int`
(= `system/hbase`); the plain worktree is `/bigtemp/vnr3ne/wt/gc-hbase`. The HBase tree is the fork's
`graphchecker/hbase-checks` (`https://github.com/JHSUYU/hbase.git`, pushed; local `/u/vnr3ne/hbase` branch
`gc/hbase-checks`). Solr and HDFS are finished: STATE §S and §0, on their own branches.

## 1. Where HBase stands

The owner's goal (2026-10-19): "基于我们solr现在这么好的代码基础，完成对hbase的adhod check". The checks are
`docs/checks/HBASE.md`: 17 study checks plus the owner's five bugs, 22 cases in `experiments/hbase/hbase-cases.tsv`.
Two sessions (2026-10-19 and the night to 2026-10-20) of a lead and five coding agents built the platform on Solr's engine
and ran every case. **All five of the owner's bugs PASS** (SAT, confirmed in the VM, reproduced natively, control 0/N):

| bug | case | mechanism | native |
| --- | --- | --- | --- |
| #12 lost backup-lock reply | hbase-bugs-backup-lock-reply-lost | HBASE_RPC RESPONSE fault on the lock CAS's reply | 10/10 |
| HBASE-30484 | hbase-adhoc-04 | REQUEST fault on the quota observer's GetActiveMaster: the enable after the snapshot advanced is lost | 7/10 |
| HBASE-30483 | hbase-adhoc-22 | STATE re-pairing, no fault: the creation's read of the namespace total joined to the truncated table's original count before the asynchronous deletion's release | 10/10 |
| #13 namespace create vs removeRSGroup | hbase-bugs-ns-rsgroup-removal | REQUEST fault on the master's hbase:meta Mutate: the held insertion retry lets removeRSGroup read 0 namespaces | 10/10 |
| #11 non-monotonic master active time | hbase-bugs-master-active-time | the new master's configured clock skew -2001 ms (owner-approved direct workaround: active time = start code + a configured skew) | 3/10 |

The study checks (each row: HBASE.md §E, STATUS "HBase checks"):
- **PASS:** 34 (a ZooKeeper READ fault on refreshKeys: the key stays missing).
- **UNSAT, substantive:** 21.
- **Class C, vacuous by construction:** 19, 20 (the test builds both descriptors it compares), 28 (a configuration constant the JDK
  decides), 35 (needs a corrupt hbase:meta).
- **Named bound** (every claim refuted by CONFIRM, mostly because it orders a step against the test thread's synchronous program
  order, TODO HBase 15; for 10 a hold CONFIRM cannot place, TODO HBase 21): 08, 10, 11, 12, 14, 15, 31.
- **Vacuous, waiting on an engine model:** 24, 37 (a znode's absence as state, TODO HBase 10).
- **Vacuous, the check's read states no version:** 13 (the seed's order holds since TODO HBase 19's fix and the tree's
  finished-step hand-off; the second merge's `hasMergeRegions` read is unjoinable, the VM's map writer set incomplete:
  HBASE.md §E).
- **No verdict yet:** 07: its replays (~22 min, 3.7 GB each) cannot converge on a shared pool; the exclusive run decides
  (NP20-07 stopped at EXPLORE round 25 with 1811 verdicts and 469 in flight).

## 2. Read, in this order

1. This file.
2. [STATE.md](STATE.md) §H: what is on `system/hbase` and the tree, the results table, and where everything is.
3. [TODO.md](TODO.md) "HBase": item 1 is the next phase (the owner's exclusive series); the other items are the open engine
   problems, each with its evidence.
4. [LESSONS.md](LESSONS.md), all of it, especially §9 HBase.
5. `docs/checks/HBASE.md` §E: every case's target, workload, selector, scope, runs and state.
6. [RULES.md](RULES.md) (the owner's rulings, including the HBase ones), [CHECKING.md](CHECKING.md) (trap 24: vacuous UNSAT),
   [OPERATIONS.md](OPERATIONS.md) §10 (HBase runs), [AGENTS.md](AGENTS.md), [PARALLEL.md](PARALLEL.md).
7. The agents' handover notes in [hbase-agents/](hbase-agents/): `H1-H5.md` (first session) and `second-session-H*.md`
   (exact run dirs, snapshots, tree sets, commits, traps and leftovers).
8. `docs/design/PIPELINE.md` for the stage you touch; `docs/REPRODUCE.md` §7 to run HBase from a fresh clone.

## 3. Running a case

[OPERATIONS.md](OPERATIONS.md) §10 has the steps (snapshot `system/hbase`; a tree set of `gc/hbase-checks` with its own Maven
repository; launch detached with the head on its own host, image `vm-force12`, every host a worker; watch; afterwards
`tools/analysis/vacuity.py` on every UNSAT, the reading, HBASE.md §E and the STATUS row). The second session's helpers:
`/bigtemp/vnr3ne/analysis/hbase-2026-10-20/launch.sh <topic> <snapshot> <case> <TAG> [budget]`, `wait-run.sh`, `watchdog.sh`.
Shared builds at the handover: see STATE §H ("Where things are").

A case is done as follows:
- **Bug check:** SAT, CONFIRMED in the VM, REPRODUCED natively, with the bug's causal chain.
- **Study check:** SAT confirmed, or UNSAT at the fixed point that vacuity.py does not call vacuous, or a named bound.
  In every case the `.smt` must be read against the HBase code.

## 4. Rules you must keep (each is in RULES.md or LESSONS.md)

- General fixes only. A per-system adapter or workaround is small and named in STATUS "Per-system surface".
  A workaround may make an order controllable or a value trackable, but it never switches the fatal outcome itself.
- Read the existing mechanism before building one. Time-box an engine challenge to about 45 min, then use a workaround
  (owner). The time model is handled by workarounds only.
- Measure first, prove the mechanism, then fix. Completeness > precision: over-approximate in COMPOSE, confirm strictly.
- HBase changes are judged by HBase's cases only; Solr is not rerun.
- Heavy replays are fine: the final verdicts come from an exclusive series, each case alone on the whole cluster (owner
  2026-10-20); do not narrow a case only because its replays are heavy under shared load.
- Heaps: replays and solvers use at most 70 % of a host; a head is charged its full heap (12288 MB for HBase) for life.
- Shell and git:
  - Always `env -u BASH_ENV`; kill only by explicit pid; never `git add -A`; never `rm -rf $VAR/...` unquoted.
  - Move a worktree's checked-out branch only inside that worktree (never `git branch -f`); after any merge check
    `git status` for unmerged paths before gating or snapshotting.
  - Commit trailer: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
  - Push GraphChecker only with the owner's OK. The HBase fork may be pushed; apache never.
- Decide engineering yourself and report. At most 5 coding agents, one branch and worktree each; the lead merges after
  a gate.

## 5. What is left

1. **The owner's exclusive series** (TODO HBase 1): every case once alone on all 14 hosts, for its final verdict and its time
   breakdown, as HDFS's EX1. 07 needs about 5-10 h alone (heavy replays plus a serial claim loop): give it a 12 h budget.
2. **07**: no verdict yet; its HBASE.md §E row says what NP20-07 reached; the exclusive run decides it.
3. **Engine items with the most return** (TODO HBase): 15 (the client thread's happens-before as JOIN rows, 2-3 days: it would
   close 08, 12, 14, 15 and shorten 07's and nsrg's claim loops), 10 (a znode's absence as state: 24, 37), 9 (data through a region's store).
4. **Push `system/hbase`** to GitHub once the owner agrees.
