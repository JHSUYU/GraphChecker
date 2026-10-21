# START HERE: GraphChecker's ZooKeeper ad hoc checks (prepared 2026-10-21)

You are the next lead (a coding agent that may run up to 5 coding agents). This file is self-contained: the goal, the
cases, what to read, the work in order, how to run a case, the rules, and where everything is.
- **Repo:** `/u/vnr3ne/GraphChecker`, GitHub `git@github.com:JHSUYU/GraphChecker.git`.
- **Branch:** `system/zookeeper` (local; pushing GraphChecker needs the owner's OK), worktree `/bigtemp/vnr3ne/wt/gc-zookeeper`.
- **Engine:** HBase's final engine (`system/hbase` 5b4b6bae9), plus the ZooKeeper preparation.
- **Tree:** the fork https://github.com/JHSUYU/zookeeper (local repo `/u/vnr3ne/zookeeper`).
- **Finished systems:** HDFS, Solr and HBase. STATE §0, §S and §H describe them, on their own branches; HBase's takeover
  file is [hbase-START-HERE.md](hbase-START-HERE.md).

## 1. The goal and where it stands

The owner (2026-10-21): "接下来的下一步，我要做zookeeper上的adhoc check。类似hbase。然后zookeeper上呢，我们本来已经有了些adhoc check的
target，需要囊括这几个bug。这几个bug也要选adhoc check，看合适的workload。用一样的hbase规则" and "zookeeper上要做的适配跟hbase,hdfs,solr
都是类似的". So: ZooKeeper's ad hoc checks, run the way HBase's were, under the same rules. The adaptation is of the same
kind as the other systems': an automatic cluster, a message door per wire, typed FAULT doors.

**The 16 cases** (`docs/checks/ZOOKEEPER.md` §E has each one's marker, workload, counterfactual, needs and fit):

| case | what | needs |
| --- | --- | --- |
| zk-bugs-trunc-sync | **ZOOKEEPER-5094 (PR 2459)**: a follower whose TRUNC sync ends before NEWLEADER keeps a database ahead of its log; its restart throws at ZKDatabase:341 | tree, quorum adapter, learner door |
| zk-bugs-observer-master | **ZOOKEEPER-5088 (PR 2454)**: a proposal pending at an ObserverMaster follower's sync gets no INFORM; the observer throws at ZKDatabase:341 | tree, quorum adapter, learner door + zxids |
| zk-bugs-quota-init | **the partial quota**: createQuota's limit node without its stat node; the retry's getData NoNode; enforcement fails open | tree |
| zk-bugs-election-offer | **the orphaned election offer**: LeaderElectionSupport fails on a vanished competitor and keeps its own offer | tree |
| zk-bugs-container-reuse | **the container cleanup** deletes a replacement node at the same path | tree |
| zk-bugs-retry-seq-quota | bug_study #32: ZooInspector's retry re-creates a sequential node, the hard quota refuses the next create | tree |
| zk-adhoc-01 02 03 04 06 07 10 11 12 13 | the study.txt items of §D (05, 08, 09 dropped) | tree; all but the 01/03 stand-in need the quorum adapter |

The first five are the owner's bugs. A bug check is done when it is SAT, confirmed in the VM and reproduced natively, with
the bug's causal chain.

**State:** prepared, nothing run.
- The case declarations are in `experiments/zookeeper/`. The tree has the adapter cherry-picked, but it is not built
  and its RESPONSE door must be rewritten (§4 item 1).
- Four workloads are still to be written; each has an outline.
- The quorum adapter is designed (Z2's D1-D9) but not built.

## 2. Read, in this order

1. This file, then [STATE.md](STATE.md) §Z (branches, tree, Maven repositories, evidence).
2. [TODO.md](TODO.md) "ZooKeeper": items 1-6 are the work in order.
3. `docs/checks/ZOOKEEPER.md` §E (the cases), then §A-§D (the study analysis; §E corrects its line numbers).
4. The agents' notes: [zookeeper-agents/Z1.md](zookeeper-agents/Z1.md) (every site and workload read on master; what the
   self-written tests must do; the adapter port and its conflicts) and [zookeeper-agents/Z2.md](zookeeper-agents/Z2.md)
   (the two quorum bugs: check rows, workload outlines, the design list D1-D9 with sizes and files).
5. How HBase was done, the template: [hbase-START-HERE.md](hbase-START-HERE.md), STATE §H, `docs/checks/HBASE.md` §D/§E, and
   `results/hbase/README.md` (what the end product looks like: every case's `.smt`, claim and time/region table).
6. [LESSONS.md](LESSONS.md), all of it (§9 HBase applies almost word for word); [RULES.md](RULES.md) (the owner's rulings,
   with the 2026-10-21 ZooKeeper ones); [CHECKING.md](CHECKING.md) (trap 24: vacuous UNSAT); [OPERATIONS.md](OPERATIONS.md)
   §10 (HBase runs: the same mechanics); [AGENTS.md](AGENTS.md); [PARALLEL.md](PARALLEL.md).
7. `docs/design/PIPELINE.md` for the stage you touch; `docs/design/IDENTITY.md` for nodes, contexts and hand-offs.

## 3. The work, in order (TODO "ZooKeeper")

1. **The tree.** Finish `gc/zk-checks` (`/bigtemp/vnr3ne/wt/zookeeper-checks`; the fork's master eab165995 + the adapter).
   - Rewrite the RESPONSE door the way HBase's `CausynthRpc` answers. Its old code calls engine entry points that no
     longer exist (Z1.md §3).
   - Add the markers.
   - Write the four workloads: `CausynthContainerReuseTest`, `CausynthZooKeeperRetryQuotaTest`, `CausynthTruncSyncTest`,
     `CausynthObserverMasterSyncTest`. Each must pass natively under JDK 8; the two quorum ones must pass 10/10.
   - Build all workloads with `experiments/zookeeper/prepare-trees.sh`.
   - Push the result as the fork's `graphchecker/zookeeper-checks`.
2. **The client-level cases** (quota-init, election-offer, container-reuse, retry-seq-quota, zk-adhoc-01/03 on the
   ClientBase stand-in).
   - Read each target occurrence off a SEED (`zk-bugs/case.sh` marks the placeholders).
   - Run each case to its verdict.
3. **The quorum adapter** (D3, D7, D8): QuorumPeer ensembles as an automatic cluster. Its canary is
   `QuorumPeerMainTest#testQuorum`.
4. **The learner-stream door** (D4): QuorumPacket as a message, plus a FAULT door on the sync's reads. This makes 5094
   runnable, and the quorum study checks.
5. **zxid carriage** (D5) for 5088's right `.smt`; optionally D6, the txn log as a store, for 5094's full chain.
6. **The final series**, as HBase's, then `results/zookeeper/`.

**A split for agents** (one branch and worktree each; the lead merges after a gate):
- **A:** item 1's adapter fix, markers and the two client-level workloads, then item 2.
- **B:** the two quorum workloads (needs A's port first, or writes them on the fork's master and A merges them).
- **C:** D3, D7 and D8.
- **D:** D4 and D5, after C.

## 4. Running a case

Mechanics as HBase's (OPERATIONS.md §10):
1. **Snapshot** `system/zookeeper`: `git worktree add --detach`, then `mvn -q -o package -DskipTests` on a lift. Never
   rebuild a snapshot a run reads.
2. **Tree set:** `env -u BASH_ENV tools/onlift.sh -h <host> -g 8 env GC_TREES=<dir> ZOOKEEPER_MAVEN_REPO=<repo> bash
   experiments/zookeeper/prepare-trees.sh`.
   - It clones `trees.tsv`'s fork branch into `<dir>/zookeeper-checks` if absent, installs each workload module, runs each
     workload natively, and prints PASSED/FAILED per case.
   - `onlift.sh` forwards no environment: put the variables inside the command.
   - For a tree branch not yet pushed: `git -C /u/vnr3ne/zookeeper worktree add --detach <dir>/zookeeper-checks <commit>`
     first.
3. **Launch** from a head that reaches every worker. Never lift02/03 (they cannot reach lift15), never the lead's gate
   host.

   `CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force12/j2sdk-image GC_TREES=<dir> GC_OUT=<out>
   tools/rounds/launch-run.sh <snapshot> <case> <tag>`

   HBase's wrapper `/bigtemp/vnr3ne/analysis/hbase-2026-10-20/launch.sh` (and `wait-run.sh`, `watchdog.sh`) shows the
   detached form; copy it with `GC_OUT=/bigtemp/vnr3ne/gc-out/zookeeper-<topic>`.
4. **A series:** `tools/rounds/run-series.sh <round> experiments/zookeeper/zookeeper-cases.tsv system/zookeeper=<snapshot>`,
   or HBase's `/bigtemp/vnr3ne/analysis/hbase-2026-10-20/lead/series.sh` (pass `SNAP`, `HEADS`; per-case settings belong
   in `case.sh`).
5. **After a case:**
   - run `tools/analysis/vacuity.py --latest --detail <run>` on every UNSAT;
   - read the `.smt` against the code with `tools/analysis/smt-legend.py`;
   - update the §E row and the STATUS row;
   - get the time/region table from `results/hbase/final-stats.py` (adjust its paths).

## 5. Rules you must keep (RULES.md and LESSONS.md have each)

- General fixes only. A per-system adapter piece or workaround is small and named in STATUS "Per-system surface". A
  workaround may make an order controllable or a value trackable; it never switches the fatal outcome.
- Reuse the existing adapter shapes: HBase's CausynthHBaseCluster/CausynthRpc, HDFS's IPC door, Solr's ZooKeeper store hooks.
  Name the closest one for each new piece.
- Read the existing mechanism before building one. Time-box an engine challenge to about 45 min, then work around it
  (owner). The time model is handled by workarounds only.
- Measure first, prove the mechanism, then fix. Completeness > precision: over-approximate in COMPOSE, confirm strictly.
- A roughly right `.smt` per case is the bar (owner 2026-10-20). The false-positive filter (CONFIRM/REPRODUCE) handles
  refuted claims; precision work waits.
- ZooKeeper changes are judged by ZooKeeper's cases only.
- Java 8 for every workload. Workloads are existing unit tests where one exercises the bug; a self-written
  `Causynth*Test` only where none does, and it must pass natively on the buggy tree.
- Per-case run settings (scope cuts, claim caps, budgets, heaps) live in `case.sh` / `workflow.properties`.
- The final series: runs under 30 min may run concurrently; every longer case runs alone on all 14 hosts; scope a
  too-slow case.
- Heaps: replays and solvers use at most 70 % of a host; a head is charged its heap for life.
- Shell and git:
  - Always `env -u BASH_ENV`. Kill only by explicit pid. Never `git add -A`. Never `rm -rf $VAR/...` unquoted.
  - Never `git branch -f` a checked-out branch. After a merge, check `git status` for unmerged paths.
  - Commit trailer: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
  - Push GraphChecker only with the owner's OK. The ZooKeeper fork may be pushed; apache never.
- Decide engineering yourself and report. At most 5 coding agents.

## 6. Where things are

STATE §Z has the full list. In short:
- **GraphChecker:** `system/zookeeper` at `/bigtemp/vnr3ne/wt/gc-zookeeper`.
- **Tree:** `/u/vnr3ne/zookeeper` `gc/zk-checks` at `/bigtemp/vnr3ne/wt/zookeeper-checks`; the fork's refs are fetched as
  `refs/remotes/jhsuyu/*`.
- **Maven repository:** `/bigtemp/vnr3ne/m2/zookeeper-quorum-bugs`, filled online for master.
- **VM image:** `/bigtemp/vnr3ne/vm-force12/j2sdk-image`.
- **Hosts:** lift02-15, 48 cores and 30 GB each.
- **Preparation evidence:** `/bigtemp/vnr3ne/analysis/zookeeper-2026-10-21/`.
