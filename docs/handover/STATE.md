# State: Solr finished -- every case has its `.smt` (2026-10-26)

Solr: section S below. The other systems live on their own branches (README "Branches"): HDFS on `system/hdfs-liftlab`,
HBase on `system/hbase`, ZooKeeper on `system/zookeeper`, each system's old bugs on `system/<x>-buggy-detect`. This
branch was made from `system/hdfs1` and still carries its HDFS cases and engine (§0); the HDFS record is
`system/hdfs-liftlab`. Read this file, then [TODO.md](TODO.md) (what is left), [RULES.md](RULES.md),
[CHECKING.md](CHECKING.md), [AGENTS.md](AGENTS.md), [OPERATIONS.md](OPERATIONS.md) and [PARALLEL.md](PARALLEL.md). The
design is in [../design/](../design/README.md); every check's state is in [../checks/README.md](../checks/README.md);
done / partial / missing per requirement in [../STATUS.md](../STATUS.md).

## S. Solr: every case has its `.smt` (the owed cases, 2026-10-22..26) -- read this first if you take over Solr

The owner's goal (2026-10-22): "请你去solr上。完成剩余几个没跑完case的adhoc check。如果case扩大，控制一下scope，降低我们的用时。
要checkout到system/solr，以及solr我们fork的repo分支上", the debugging and fixing as on ZooKeeper and HBase. The owed cases were
the eight SGF9 left without a clean result (the TODO of 2026-10-19, "Solr: after SGF9" item 1): 14, 07, 31 never finished on the rewritten
engine; 39, 19, 13, 09 ended with GROW re-runs no round planned over; 05 was decided offline only. All eight now have
their final run, each alone on the cluster (series X1/X1B/X1C, the owner: "他们都能通过后。你要让他们独占集群再跑一遍，看看每
个case的用时是多少"); every Solr case's final `.smt`, claim and time row is in [`results/solr/`](../../results/solr/README.md).

**`system/solr`** (GitHub, pushed again 2026-10-26; worktree `/bigtemp/vnr3ne/wt/gc-solr`):
the SGF9 body plus, each gated (mvn package, `src/test/shell/run_engine_campaign_helpers_test.sh`):
- one task per exposed occurrence (5e22da799): GROW's planner tasks an exposed occurrence the plan holds already no
  more (R1-19 died at a weave that refused g33's duplicate taskId);
- a GROW plan within the campaign's task bound (f4e8cb84d): an exposure past `ExecutionTask#maxCampaignTasks` (1024)
  is not tasked, the closure truncated there (X1-31 died at a weave that refused g25's 1025th task);
- `explore_budget_s` (0f56b6efb; solr-adhoc 7200, owner: "exploration上限给2小时"): EXPLORE's own cap, ending it as at
  the campaign budget;
- `compose_max_paths` (3351d5979; solr-adhoc-14 117): a case caps its composed paths from the start (R2-14 composed
  235 of 260 paths at 16384 and at 21504 MB, each out of heap, then hit its case budget);
- the report probe's bounds (ddd01c892 `PROBE_BUDGET_SECONDS` 900 over the whole probe, 81ef0125e no per-path split past
  `PROBE_SPLIT_MAX_MB` 2048: R3-05's per-path probe held its summary row 48+ min, X1C-05's split wrote 29 GB);
- the scope cut of 05 07 14 31 (92d12dde3, `solr-adhoc/case.sh`): no client faults (`client_fault_transports=(NONE)`:
  an empty list fails every client door), the first claim only;
- `tools/analysis/vacuity.py` from `system/hbase` (b31a6e446), to read each UNSAT.

**The tree:** unchanged, the fork's `graphchecker/solr-checks` 12d23091d1 (tree set `/bigtemp/vnr3ne/wt/sg3j-trees`);
image `/bigtemp/vnr3ne/vm-force10/j2sdk-image`.

**How the cases ran** (decision log `/bigtemp/vnr3ne/analysis/solr-2026-10-22/lead/RUNS.txt`):
- R1-R4 (2026-10-22, concurrent, `gc-out/solr-final/accept-R*`): eight at once starved the 21.5 GB head steps (R1-14's
  planner never started in 30 min), so Solr runs at concurrency <= 3; lift11 (the control host) is no worker since
  R2-05's served planner took it to 86 %. These runs found the fixes above; their verdicts agree with X1's.
- X1 (snapshot `/u/vnr3ne/gc-run/sr-5`, 3351d5979), X1B and X1C (`sr-6`, f4e8cb84d): each owed case alone on 13 lifts
  (X1C on 12: lift07 unreachable after the servers went down on 2026-10-23). Drivers
  `analysis/solr-2026-10-22/lead/final/series2.sh` (`WORKERS`), `chain-X1*.sh`; monitor `lead/lead-watch3.sh`.

**The owed cases' final verdicts** (each alone; `results/solr/README.md` has the time and region table):

| case | run | verdict | wall (s) |
| --- | --- | --- | ---: |
| solr-adhoc-09 | X1 | UNSAT, vacuous by construction (class C): the throw tests the constant Boolean the delete callable returns | 1951 |
| solr-adhoc-13 | X1 | named bound: truncated closure, no composed path reaches the target | 1912 |
| solr-adhoc-39 | X1 | UNSAT, vacuous (NO_ROOT): the guard reads the immutable Aliases map; the reference's re-pairing is outside its slice | 5077 |
| solr-adhoc-19 | X1 | UNSAT, vacuous (NO_ROOT): 7 paths, 6 not reaching the target (unplaced clock cells) | 3809 |
| solr-adhoc-14 | X1 | UNSAT, vacuous by construction (class C): the guard tests ZooKeeper `exists()`'s Stat; needs the leader's session lost | 13686 |
| solr-adhoc-07 | X1B | UNSAT, substantive: 254 of 295 paths free (the core-map re-pairing explored), no witness | 9541 |
| solr-adhoc-05 | X1C | UNSAT, vacuous (NO_ROOT): the re-read after `waitForState` is offered no other writer on any of 349 paths | 11503 |
| solr-adhoc-31 | X1C | named bound: no composed path of 134 reaches the target; 35 TOPOLOGY_DIVERGENCE, 17 ADMISSION_GAP named | 10909 |

The other twelve keep their records: the eight bug checks SGF7 (SAT, confirmed, native), 38 21 10 40 SGF9.

## 0. What this branch inherited from HDFS (`system/hdfs1`, 2026-10-06..08)

The HDFS group ended on 2026-10-08 as two branches (owner 2026-10-06): `system/hdfs`, the locked body d6737d26b with
39 cases closed by round HL1 and its reruns, and `system/hdfs1`, the other 7 cases (07, 11741, 21, 29, 30, 39, 40) and
every engine change after the lock; every HDFS case then ran alone for its time (series EX1,
[../design/PERFORMANCE.md](../design/PERFORMANCE.md) §6), and STATUS "HDFS checks" holds the 46 readings, each naming
the branch and run that closed it. `system/solr` was made from `system/hdfs1`. Both HDFS branches stay on the remote as
history; `system/hdfs-liftlab` (2026-10-27) replaces them as the HDFS record.

What `system/hdfs1` added to the locked body, each merged with its gate (git log has the numbers):
- **Open arms** (`hdfs-open-arms` 3bdf1ec4f): a faithful replay that never enters an open arm's occurrence refutes that
  world (`WORLD_REFUTED`); configuration domains from the recorded comparisons; a version no activation wrote is named
  (`UNATTRIBUTED_STORE`) and re-pairable through its own symbol. Closed 39 and 40 first.
- **The Cone fix** (3e7becca7): a body's Cone read once and indexed by selector (11741's COMPOSE was quadratic).
- **Wait deadline** (`hdfs-wait-deadline` 9565537f2): a timed wait that takes its WAKE slot returns no sooner than its
  own deadline (29, 30: a DataNode skipped heartbeats and the NameNode chose the other recovery primary).
- **Codec capture** (`hdfs-codec-capture` d502ddbc7): the IPC and DataTransfer doors walk the protobuf message they
  carry; a field's value is exported at its builder's setter and staged by the door; the engine's plumbing is never
  state; an arm's input shape names its deliverers as a sorted set. Reviewed: open defects 52-56.
- **21's workaround** (`hdfs1-21-workaround` 085b9a9ed): tree `gc/hdfs-study-r7-21` and `loop-bounds-21.jsonl`.
- **07's workaround** (`hdfs1-07-wa` 98e283425): tree `gc/hdfs-study-r8` and world depth 6 for 07 only.
- **Open-arm keys** (`hdfs1-open-arm-keys` fd0b0cd8a): each path's open arm judged by its own flip's answers where it
  has any, else the shared verdict; a replay that did not run its world is asked once more; a flip no variable reaches
  is UNSAT on its path (`NOT_FLIPPABLE`) unless a HELD value or refused construct feeds it.
- **The relay plan and solver sizing** (`hdfs1-relay-plan` ffda51bfb, what closed 07): PLAN follows a reply a client
  relays into its next request; a read no write explains is held to its object's identity; host solvers and retried
  solves run at the case's engine heap, at most two solves per host (STATUS open defects 61-63).

## 1. The goals (verbatim) and what they mean

The 2026-10-04 goal (the four systems):

> 请你阅读graphchecker的source code和vm代码。先了解这个Tool在处理的adhoc coordinaiton。以及我们的处理方式。然后阅读graphchecker远端study分支上的study.txt。里面记录了4个system的adhoc coordianotin位置，以及他们对应的cluster based unit test。同时，~/bug_study下是一些可能是adhoc coordianot有关的bug。请你仔细阅读graphchecker的readme。给每一个系统上，adhoc coordiaont check都加上我们的annotation。并编号，然后去check他们。…最终我们的目的是，四个system。我们的graphchecker创建四个对应分支。这四个分支代码主体都是一样的。只是每个system可能有一些小适配，workaround。…总之每个系统上我们就要检查若干adhoc coordination。跑出他们的.smt。如果这个点包含我们已有的bug。那应该是.smt跑通。然后你最终跑完这4个system上所有adhoc check。

The 2026-10-05/06 goal (HDFS), its target and acceptance:

> 跑通 HDFS 上全部 46 个 case：36 个 study 检查点 hdfs-adhoc-NN，加 10 个已知 bug 的 named case。完成标准： 1. 每个 case
> 都导出 final/candidate.smt2， - SAT：CONFIRM 已确认，至少移动了一个根，polarityDecides 为真，并做了 native reproduction；
> - UNSAT：exploration 正常到达 FIXED_POINT，并且单独用 z3 重解该文件得到 unsat。 … 2. 10 个已知 bug 全部 PASS，且机制符合
> mandate … 3. 每个 .smt 都人工对照 HDFS 代码核对因果链、符号变量和符号传播 … 写进 docs/STATUS.md。 找到新 bug 最好，
> 找不到也可以接受，前提是 .smt 正确。

The owner's later rulings that changed it (RULES has each verbatim): no exclusive runs; the time-model family (21 22
23 24 25 34 35 52) by workarounds, an approximately right `.smt` enough; lock what is right on `system/hdfs`, the rest
on `system/hdfs1`, two branches as the end state; the last open cases by per-case workarounds; reasonable parallelism
that serves throughput.

## 2. GraphChecker branches (repo `~/GraphChecker`, remote `origin` = github)

The remote keeps, per system, its ad hoc branch and its old-bug branch (README "Branches"): `system/hdfs-liftlab` and
`system/hdfs-buggy-detect`, `system/solr` (this branch) and `system/solr-buggy-detect`, `system/hbase` and
`system/hbase-buggy-detect`, `system/zookeeper` and `system/zookeeper-buggy-detect`; besides them `main` (the
2026-10-03 body, round V25) and, as history, `system/hdfs` and `system/hdfs1` (§0). The CloudLab ports (2026-10-24..28)
are the tags `archive/system/<x>-cloudlab`.

Every other remote branch was deleted on 2026-10-08, bundled first: `/bigtemp/vnr3ne/handover/2026-10-08/graphchecker-remote-branches.bundle`
(`study`, `hdfs-compose-perf-wip`, `hdfs-container-writers`; `git fetch <bundle> 'refs/remotes/origin/*:refs/remotes/bundle/*'`
gets them back). The study's data moved to `docs/checks/` (`study.txt`, `SELECTION.md`, `new-bugs.txt`).

The local branches of the Solr work (the integration branch `solr-int`, the agents' `solr-*`) and of the HDFS group
were removed in the 2026-10-28 cleanup; the unmerged work TODO names is named there by its head commit
(`solr-growshape` 727d48ea5, `solr-armkey` 3bfdca7bc, `solr-portname` b80976bb7, `hdfs1-confirm-first` da913cd7c, the
shelved `solr-parplan` 3df494a3a / `solr-shard` d3b663462).

## 3. The Solr tree, the VM image, snapshots

| tree (`$GC_TREES/<name>`) | branch | what it is |
| --- | --- | --- |
| `/bigtemp/vnr3ne/wt/sg3j-trees/lucene-solr-checks` (a link to `/bigtemp/vnr3ne/wt/lucene-solr-zktrace2`, a worktree of `~/lucene-solr-8_11`) | local `gc/solr-zktrace2` 12d23091d1 = the fork's `graphchecker/solr-checks` (`JHSUYU/solr`, pushed 2026-10-16, unchanged since) | THE Solr tree of every `system/solr` case since SGF8 (`experiments/solr/trees.tsv`; REPRODUCE clones it). Its history: `gc/solr-checks` (the 12 study markers, the bug checks' markers and workloads on `gc/solr-bugs` f65aaf7), `gc/solr-body`, `gc/solr-zk-next`, `gc/solr-zk-doors`, `gc/solr-zk2`, `gc/solr-final9` 0ce3deafed, `gc/solr-zktrace` 8fde6b812c -- local branches of `~/lucene-solr-8_11`, their worktrees removed |

The HDFS trees this branch's inherited HDFS cases name (`experiments/hadoop/trees.tsv`) ran at `hadoop-hdfs-study-r7`
(`gc/hdfs-study-r7` bd72fcc1a13 in `~/hadoop`, every HDFS case but 07, 21 and 11741), `hadoop-hdfs-study-r8`
(e3dab6266a7 = the fork's `graphchecker/hdfs-checks-adhoc07`, 07), `hadoop-hdfs-21` (`gc/hdfs-study-r7-21` c360d869629,
21) and `hadoop-hdfs-11741-r6` (6c86fca9a2b = `graphchecker/hdfs-11741`); their worktrees were removed in the 2026-10-28
cleanup (`experiments/hadoop/prepare-trees.sh` makes one anew from the fork). The fork's `graphchecker/hdfs-checks`
(899c200cc8e) and `graphchecker/hdfs-checks-adhoc21` (25b4f1e531) have since moved on with `system/hdfs-liftlab` (its
STATE). The ZooKeeper and HBase trees are those branches' (`graphchecker/zookeeper-checks`, `graphchecker/hbase-checks`).

VM images (`CAUSYNTH_CUSTOM_JDK_HOME`): **`/bigtemp/vnr3ne/vm-force10/j2sdk-image`** serves this branch (sources
96214b520, `SOURCE.txt` and `smoke.log` beside it; the runtime refuses an older image by name); `vm-force12`
serves `system/hbase` and `system/hdfs-liftlab`, `vm-force13` `system/zookeeper`, `vm-hg5` the two former HDFS branches,
`vm-model-guards2` `main`. `tools/vm/build-image.sh` rebuilds an image from a checkout's `third_party/` sources on lift15
(the one lift with gcc-6). The VM's dead natives (VM.md §8) and `exportLeaf`/`mintLeaf` can go in the next VM build.

Snapshots in `~/gc-run/` (frozen; `tools/rounds/snapshot-gc.sh` refuses one in use): `sr-5` (3351d5979, series X1) and
`sr-6` (f4e8cb84d, X1B and X1C).

## 4. Where the analyses and evidence live

- `docs/checks/` (in the repo): the selection, the per-system point tables, the verified bugs.
- Solr: START-HERE §5 (the owed cases' `analysis/solr-2026-10-22/lead/`, the rewrite's `analysis/solr-2026-10-18/`, the
  runs of record in `gc-out/solr` and `gc-out/solr-final`); `results/solr/index.tsv` names each case's run.
- The HDFS group's: `/bigtemp/vnr3ne/gc-out/hdfs-study/` (its rounds), `hdfs-excl/` (series EX1, `PRUNE=0`: the offline
  gate's corpora), `hdfs-21w/`, `hdfs-codec-capture/`, `hdfs1-open-arm-keys/` (agents' runs);
  `/bigtemp/vnr3ne/analysis/excl-2026-10-07/` (the EX1 driver), `study-2026-10-06b/`, `cleanup-2026-10-08/`.
- `/bigtemp/vnr3ne/handover/`: bundles of deleted branches (`2026-10-08/`), WIP patches of stopped agents.
- Older: `/bigtemp/vnr3ne/analysis/study-2026-10-04/`, `study-2026-10-05/`, `/bigtemp/vnr3ne/specs/` (proposals cited
  by code comments), `~/bug_study/`.
