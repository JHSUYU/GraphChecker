# START HERE: GraphChecker's HBase work (second session handover, 2026-10-20)

You are the next lead (a coding agent that may run up to 5 coding agents). This file is self-contained: where HBase
stands, what to read, what is left, how to run a case, and where everything is. Repo: `/u/vnr3ne/GraphChecker`, GitHub
`git@github.com:JHSUYU/GraphChecker.git`. HBase's code is the branch `system/hbase`
(pushed 2026-10-22). Its integration worktree is `/bigtemp/vnr3ne/wt/gc-hbase-merge`, on `hbase-int`
(= `system/hbase`); the plain worktree is `/bigtemp/vnr3ne/wt/gc-hbase`. The HBase tree is the fork's
`graphchecker/hbase-checks` (`https://github.com/JHSUYU/hbase.git`, pushed; local `/u/vnr3ne/hbase` branch
`gc/hbase-checks`): the adapter. **From GitHub:** clone the two and check out those branches;
[../REPRODUCE.md](../REPRODUCE.md) §7 builds the VM image and the tree and runs every case. Solr and HDFS are
finished: STATE §S and §0, on their own branches.

## 1. Where HBase stands (final series, 2026-10-20/21)

The owner's goal (2026-10-19): "基于我们solr现在这么好的代码基础，完成对hbase的adhod check". The checks are
`docs/checks/HBASE.md`: 17 study checks plus the owner's five bugs, 22 cases in `experiments/hbase/hbase-cases.tsv`.
**HBase is finished**: every case ran once more on the final engine (the final series, owner 2026-10-20/21: runs under 30
min kept from a concurrent round, every longer case alone on all 14 hosts, 11 12 14 15 again alone with a scope cut).
**Every case's final `.smt`, claim, time breakdown and region count are in [`results/hbase/`](../../results/hbase/README.md)**;
every case's run configuration is in `experiments/hbase/*/case.sh` and `workflow.properties`.

**All five of the owner's bugs PASS** on the final engine (SAT, confirmed in the VM, reproduced natively, control 0/N):

| bug | case | mechanism | native |
| --- | --- | --- | --- |
| #12 lost backup-lock reply | hbase-bugs-backup-lock-reply-lost | HBASE_RPC RESPONSE fault on the lock CAS's reply | 10/10 |
| HBASE-30484 | hbase-adhoc-04 | REQUEST fault on the quota observer's GetActiveMaster: the enable after the snapshot advanced is lost | 10/10 |
| HBASE-30483 | hbase-adhoc-22 | STATE re-pairing, no fault: the creation's read of the namespace total joined to the truncated table's original count | 10/10 |
| #13 namespace create vs removeRSGroup | hbase-bugs-ns-rsgroup-removal | REQUEST fault on the master's hbase:meta Mutate: removeRSGroup reads 0 namespaces | 10/10 |
| #11 non-monotonic master active time | hbase-bugs-master-active-time | the new master's configured clock skew -2001 ms (owner-approved workaround: active time = start code + a configured skew) | 8/10 |

The study checks (`results/hbase/README.md` has each one's reading):
- **SAT, confirmed:** 34 (a ZooKeeper READ fault on refreshKeys, 9/10: reachable fault handling, not a new bug); 24 (in the VM:
  a member's barrier read past the coordinator's timeout reads no node and throws at ZKProcedureMemberRpcs:210, caught there:
  a misleading log, not a functional bug; no native STORE_HOLD).
- **UNSAT:** 21 (substantive); 19, 20, 28, 35 (vacuous by construction, class C); 37 (vacuous: no absent window in its
  workload); 31 (vacuous: start codes are run constants; its row's RUN_DEFECT was stale generation gaps, fixed after the run).
- **Named bound** (SAT, every claim refuted by CONFIRM as the client thread's synchronous program order, TODO HBase 15):
  07, 08, 10, 11, 12, 14, 15.
- **RUN_DEFECT, the formula vacuous:** 13 (the second merge's `hasMergeRegions` read states no version, TODO HBase 19).

**Run a case:** a snapshot of `system/hbase` (`git worktree add --detach`, `mvn -q -o package -DskipTests`), a tree set of the
fork's `graphchecker/hbase-checks` (`GC_TREES=<dir> HBASE_MAVEN_REPO=<repo> experiments/hbase/prepare-trees.sh hbase-checks`;
pass the variables inside the command when you use `tools/onlift.sh`, which forwards no environment), then
`CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force12/j2sdk-image GC_TREES=<tree set> tools/rounds/launch-run.sh <snapshot> <case> <tag>`
on a head that reaches every worker (never lift02/03, which cannot reach lift15), or every case with
`tools/rounds/run-series.sh`. OPERATIONS.md §10 has the details.

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
   close 08, 12, 14, 15 and shorten 07's and nsrg's claim loops), 10 (what remains of a znode's absence as state: 37's failover workload, INITIAL absence, expiries), 19 (what keeps 13 vacuous:
   its second merge's `hasMergeRegions` read states no version), 9 (data through a region's store).
4. **Push `system/hbase`** to GitHub once the owner agrees.
