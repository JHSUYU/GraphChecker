# START HERE: `system/hbase-buggy-detect` -- the old HBase bugs put back, on HBase's ad hoc engine (liftlab)

You are the next lead (a coding agent that may run up to 5 coding agents). This branch is `system/hbase` (HBase's ad hoc
checks, finished 2026-10-21: §1-§5 below) plus the old HBase bugs that make an ad hoc check fail, put back by hand on
today's tree, and the engine support they needed (§0; the four systems' table: [BUGGY-DETECT.md](BUGGY-DETECT.md)). Repo:
`/u/vnr3ne/GraphChecker`, GitHub `git@github.com:JHSUYU/GraphChecker.git`, branch `system/hbase-buggy-detect` (local
`bd-liftlab-hbase`, worktree `/bigtemp/vnr3ne/wt/gc-hbase-bd`). The trees are the HBase fork's
(`https://github.com/JHSUYU/hbase.git`) `graphchecker/hbase-bug-<jira>`, each `graphchecker/hbase-checks` b5d5cc6a20 with
one bug put back, its workload and the point's target marker. HDFS, ZooKeeper and Solr are on their own branches
(README "Branches").

## 0. The old HBase bugs (owner 2026-10-26: only a bug whose witness fires the point's own declared throw counts)

| case | bug | point | tree (`experiments/hbase/trees.tsv`) | CloudLab, 2026-10-26 | liftlab, B1 |
| --- | --- | --- | --- | --- | --- |
| hbase-buggy-15039 | HBASE-15039: a token rejected before the ZooKeeper watcher applied its key | hbase-adhoc-34 (AuthenticationTokenSecretManager:139) | `hbase-bug-15039` (c2cecb3756) | SAT, STATE re-pairing, native 10/10, control 0/10 (HB15039b) | B1 (lead fills in) |
| hbase-buggy-20642 | HBASE-20642: a retried disableTable attempt draws a new nonce | hbase-adhoc-04 (AbstractStateMachineTableProcedure:163) | `hbase-bug-20642` (1ba966bb6c) | SAT, MARKER_FLIPPED (lost DisableTable reply), native 10/10 by IDENTITY §9 shape, 0/10 exact, control 0/10 (HB20642f; accepted by the owner 2026-10-27) | B1 (lead fills in) |
| hbase-buggy-28533 | HBASE-28533: a failed split's PREPARE rollback leaves the parent SPLITTING | hbase-adhoc-15 (MergeTableRegionsProcedure:507) | `hbase-bug-28533` (de71623820) | not reachable on today's code: README only, no run (closed by the owner) | no run |

The runnable cases are `experiments/hbase/hbase-buggy-cases.tsv` (case, branch, budget 21600 s, bug, point); each case
directory's README has the bug, what was put back and why, the workload, every declaration and the runs. Their expected
mechanisms are `experiments/accept/report.py`'s `EXPECTED_MECHANISM` rows. The engine support on this branch only:
948e4779f (the reply legs of a turn's earlier requests are control producers, SYMBOL-SCOPE, PIPELINE §7.2) and
93a168e87 + 298508ffa (IDENTITY §9's order rule in one implementation, `runtime/AnswerOrder`, for a replay and for a
native REPRODUCE run; `reproduced` stays exact-only, `reproducedByShape` is counted apart, PIPELINE §10b). The rest --
the host ledger, heaps (`engine_memory_mb` 12288), launch tools -- is `system/hbase`'s.

**Run them on liftlab** (the lead's series B1, 2026-10-28; workers lift02-15 but lift07 and lift11, OPERATIONS §1):
1. **Snapshot** of this branch (never rebuild one a run reads): `bash tools/lib/worktree-add.sh
   /u/vnr3ne/gc-run/bd-hbase-<n> <commit> --detach`, then in it `env -u BASH_ENV tools/onlift.sh -g 4 mvn -q -o package
   -DskipTests`. B1's is `/u/vnr3ne/gc-run/bd-hbase-1` (b978bacb8).
2. **The tree set** `/bigtemp/vnr3ne/wt/bd-trees-1` (every bug tree of the four systems; Maven repositories under
   `/bigtemp/vnr3ne/m2/bd-1`, one per tree, `hbase_bigtemp_vnr3ne_wt_bd-trees-1_hbase-bug-<jira>`): from the snapshot,
   `env -u BASH_ENV tools/onlift.sh -g 8 env GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1 GC_M2=/bigtemp/vnr3ne/m2/bd-1
   experiments/hbase/prepare-trees.sh hbase-bug-15039 hbase-bug-20642` (it clones each fork branch into
   `$GC_TREES/<tree>`, installs the snapshot's jar into the tree's Maven repository, builds, and runs each case's workload
   once natively: one `PASSED` line each). Never build a tree a run reads.
3. **Launch**, from lift11, with the image `vm-force12`:
   ```bash
   cd /u/vnr3ne/gc-run/bd-hbase-1 && env -u BASH_ENV GC_OUT=/bigtemp/vnr3ne/gc-out/buggy-detect \
     GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1 GC_M2=/bigtemp/vnr3ne/m2/bd-1 \
     LIFTS="lift04 lift05 lift06 lift08 lift09 lift10 lift12 lift13 lift14 lift15" \
     CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force12/j2sdk-image CASE_TIMEOUT_SECONDS=21600 PRUNE=0 \
     CASES="hbase-buggy-15039 hbase-buggy-20642" tools/rounds/launch-round.sh /u/vnr3ne/gc-run/bd-hbase-1 B1
   ```
   One case: `CASES=hbase-buggy-20642`. A round tag runs a case once (`accept-<ROUND>-<case>`); a rerun takes a new tag.
   `LIFTS` leaves out lift02 and lift03: `launch-round.sh` may head a case on any host of `LIFTS` but lift11, and those
   two cannot reach lift15, so PREFLIGHT refuses a run they head with lift15 among its workers ("campaign_worker_hosts
   names lift15, which this host cannot reach": B1's first launch of both HBase cases, 2026-10-28 00:11, headed on lift02
   and lift03). Keeping lift02 and lift03 instead means leaving out lift15.
4. **Read the result** in `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-<case>/`: `summary.tsv` and
   `report/<case>/report.md` (report.py's PASS: the expected mechanism, CONFIRM, native REPRODUCE k/N, control 0/N);
   `tools/rounds/round-verify.sh B1` (how EXPLORE ended, z3 on the exported `final/candidate.smt2`, gaps, roots);
   `python3 tools/analysis/vacuity.py --latest --detail <run dir>` on an UNSAT; `tools/analysis/smt-legend.py <run
   dir>/out/<case>` to read the chain against the bug tree's code; `final/reproduce.json` and `final/reproduce/plant.log`
   for the native runs (hbase-buggy-20642 counts `reproducedByShape`; its `ADDRESS_UNSTABLE` lines name each by-shape
   run). Then the case README's result section and BUGGY-DETECT.md's B1 column.

## 1. Where HBase's ad hoc checks stand (`system/hbase`, final series, 2026-10-20/21)

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
`tools/rounds/run-series.sh`; the workers are lift02-15 but lift07 (unreachable since 2026-10-23) and lift11 (the control
host): give `LIFTS` the other twelve. OPERATIONS.md §10 has the details.

## 2. Read, in this order

1. This file.
2. [STATE.md](STATE.md) §H: what is on `system/hbase` and the tree, the results table, and where everything is.
3. [TODO.md](TODO.md) "HBase": the open engine problems, each with its evidence, parked.
4. [LESSONS.md](LESSONS.md), all of it, especially §9 HBase.
5. `docs/checks/HBASE.md` §E: every case's target, workload, selector, scope, runs and state.
6. [RULES.md](RULES.md) (the owner's rulings, including the HBase ones), [CHECKING.md](CHECKING.md) (trap 24: vacuous UNSAT),
   [OPERATIONS.md](OPERATIONS.md) §10 (HBase runs), [AGENTS.md](AGENTS.md), [PARALLEL.md](PARALLEL.md).
7. `docs/design/PIPELINE.md` for the stage you touch; `docs/REPRODUCE.md` §7 to run HBase from a fresh clone.

## 3. Running a case

[OPERATIONS.md](OPERATIONS.md) §10 has the steps (snapshot `system/hbase`; a tree set of `gc/hbase-checks` with its own Maven
repository; launch detached with the head on its own host, image `vm-force12`, every host a worker; watch; afterwards
`tools/analysis/vacuity.py` on every UNSAT, the reading, HBASE.md §E and the STATUS row). The second session's helpers:
`/bigtemp/vnr3ne/analysis/hbase-2026-10-20/launch.sh <topic> <snapshot> <case> <TAG> [budget]`, `wait-run.sh`, `watchdog.sh`.
The final series' snapshots, tree set and image: STATE §H ("Where things are").

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

This branch owes the old bugs' liftlab series B1 (§0, TODO "Old HBase bugs"). Nothing is owed for HBase's ad hoc
checks: every case has its final verdict (`results/hbase/`), `system/hbase` and the fork's
`graphchecker/hbase-checks` are on GitHub, and REPRODUCE §7's fresh-clone check passed (2026-10-22). Optional engine work,
most return first (TODO "HBase"): 15 (the client thread's happens-before as JOIN rows, 2-3 days: it would close 08, 12,
14, 15 and shorten 07's and nsrg's claim loops; parked as `archive/local/hbase-e15`), 10 (what remains of a znode's
absence as state: 37's failover workload, INITIAL absence, expiries), 19 (what keeps 13 vacuous: its second merge's
`hasMergeRegions` read states no version), 9 (data through a region's store).
