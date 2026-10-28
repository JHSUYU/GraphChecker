# State: HDFS on liftlab (system/hdfs-liftlab, THE HDFS branch); the former HDFS bodies; the other systems' branches

This branch, `system/hdfs-liftlab`: section L below (THE HDFS branch, replacing `system/hdfs` and `system/hdfs1`: every
HDFS case on HBase's engine with liftlab's memory-ledger scheduling; the trees the Hadoop fork's `graphchecker/hdfs-checks*`
and `graphchecker/hdfs-11741`; the final series H1; [../REPRODUCE.md](../REPRODUCE.md) §0-§5). The HDFS group on its
earlier bodies (`system/hdfs`, `system/hdfs1`; §0, history) is finished: all 46 cases have an exported `.smt` read by
hand against the HDFS code, one row each in [../STATUS.md](../STATUS.md) "HDFS checks" (07, the last, closed on
2026-10-07: EX1-adhoc-07e on `system/hdfs1` 8c446418b). Every case then ran alone on the ten lifts for its time breakdown
(series EX1, `/bigtemp/vnr3ne/gc-out/hdfs-excl`; the 46 rows are [../design/PERFORMANCE.md](../design/PERFORMANCE.md) §6).
The other systems (HBase, ZooKeeper, Solr) and the old-bug branches are on their own branches (§O, §2). Read this file,
then [TODO.md](TODO.md) (what is left, in order), [RULES.md](RULES.md), [CHECKING.md](CHECKING.md),
[AGENTS.md](AGENTS.md), [OPERATIONS.md](OPERATIONS.md) and [PARALLEL.md](PARALLEL.md). The design is in
[../design/](../design/README.md); every check's state is in [../checks/README.md](../checks/README.md); done / partial /
missing per requirement in [../STATUS.md](../STATUS.md).

## L. HDFS on liftlab (system/hdfs-liftlab, 2026-10-26/27) -- read this first if you take over HDFS

The owner's goal (2026-10-26, verbatim): "跑完solr之后。再把hdfs除了11741以外的所有adhod check跑一遍。使用的版本是system/hdfs-cloudlab
但是有一个问题，那个的并行都在cloudlab上。所以为了我们liftlab的并行，你要把system./solr等的并行，弄到system/hdfs-liftlab。你懂吧，就是
cloudlab分支都能跑通了，只是并行在不同的集群上。然后测出45个hdfs adhoc hcdck的time break down，包括seeding, exploraiton,(compose+solver)
每个独占集群。" Then: "最终system/hdfs-liftlab一个分支就能彻底取代原先的system/hdfs和system/hdfs1了哈". The lead's decision log is
`/bigtemp/vnr3ne/analysis/hdfs-2026-10-26/lead/RUNS.txt`.

**`system/hdfs-liftlab`** (THE HDFS branch; `system/hdfs` and `system/hdfs1` are history): `system/hbase` 26910df2a
(whose code is 5b4b6bae9's) plus the HDFS port -- the Hadoop shim and its door entry points, DECIDE's own arms and own-run
ask, REPRODUCE's plant of a pure re-pairing, the case declarations on HBase's process, the fork's workarounds
([START-HERE.md](START-HERE.md) §1 lists them) -- first built and run on CloudLab (2026-10-24, rounds F1-F8; that head is
the tag `archive/system/hdfs-cloudlab`, 3411a49f8), whose scheduling 2acb6e9f7, 3a9b0a688, 76828e529, 3ed666321 and
c3f820ed1 revert; then e2a6aebf9, `tools/lib/gc-env.sh`'s liftlab defaults (`GC_BULK=/bigtemp/vnr3ne`,
`GC_REPO=~/GraphChecker`, `Z3_BIN=~/.local/bin/z3`, `LIFTS` lift02-15 but lift11, `GC_CONTROL_HOST=lift11`), and
system/solr's four general fixes (43ac04c1e one task per exposed occurrence, b4c24f9e3 a GROW plan within the task bound,
6a1d5fd6a and f7c095f00 the report probe's budget and split bound). `run_engine.sh` and
`src/test/shell/run_engine_campaign_helpers_test.sh` equal `system/hbase`'s: the host ledger charges memory (70 % of a
host), every choice among hosts takes the most memory room, as `system/hbase` and `system/solr` (PIPELINE §7.7, PARALLEL).
Gate green (`mvn package` with the tests, the shell test; on lift14, `lead/gate1-*.log`, `lead/gate2-*.log`). Pushed
a3e1881d5 (2026-10-27). Integration worktree `/bigtemp/vnr3ne/wt/gc-hdfs-liftlab`.

**The cluster** (OPERATIONS §1): liftlab, lift02-15, 48 cores and 30 GB each, `/bigtemp/vnr3ne` and the home over NFS;
lift11 the control host (the lead's sessions; neither a worker nor a head); lift07 unreachable since the servers went down
on 2026-10-23; lift02 and lift03 cannot reach lift15, so they are workers, never heads. The workers: the other 12, lift02-06,
lift08-10, lift12-15. Maven and Ant only on lift02-06 and lift08-10.

**The image:** `/bigtemp/vnr3ne/vm-force12/j2sdk-image` (`system/hdfs-liftlab`'s VM sources are `system/hbase`'s).

**The trees** (`experiments/hadoop/trees.tsv`, the fork `https://github.com/JHSUYU/hadoop.git`): tree set
`/bigtemp/vnr3ne/wt/hl-trees-1` = `hadoop-hdfs-study-r7` (the fork's `graphchecker/hdfs-checks` 899c200cc8e: every case
but hdfs-adhoc-21 and hdfs-11741) and `hadoop-hdfs-21` (`graphchecker/hdfs-checks-adhoc21` 25b4f1e531f), each with its
Maven repository under `GC_M2=/bigtemp/vnr3ne/m2/hl-1`; made by `experiments/hadoop/prepare-trees.sh` on lift12 in ~20
minutes (`lead/prepare-hl-trees-1.log`): 30 workloads PASSED, 0 FAILED; 45 of 45 cases valid (`lead/validate.sh`).
hdfs-11741's tree (`hadoop-hdfs-11741-r6` = `graphchecker/hdfs-11741`) is not in the set: the series leaves 11741 out
(owner).

**The snapshots:** `/u/vnr3ne/gc-run/hl-1` (e2a6aebf9) and `/u/vnr3ne/gc-run/hl-2` (f7c095f00), built.

**The series H1** (2026-10-26 23:55 to 2026-10-27 17:34): the 45 cases of `experiments/hadoop/hdfs-cases.tsv` but
hdfs-11741, in the table's order, one at a time (concurrency 1), each alone with the 12 lifts as workers and its head on
lift10, trees `hl-trees-1`, image `vm-force12`, each case's budget the table's `budget_s`; runs
`/bigtemp/vnr3ne/gc-out/hdfs-final/accept-H1-<case without hdfs->`. The drivers are in
`/bigtemp/vnr3ne/analysis/hdfs-2026-10-26/lead/`: `launch.sh <topic> <snapshot> <case> <TAG> [budget s]` (one run into
`gc-out/hdfs-<topic>`; env `GC_TREES` required, `WORKERS`, `VM_IMAGE`, `STOP_AFTER`), `final/series.sh <round>
<concurrency> <case>...` (env `SNAP`, `TREES` required, `WORKERS`, `HEADS`; log `final/series-<round>.log`; `touch
final/series-<round>.STOP` stops further starts), `lead-watch.sh` (one line per run end, series line, stall, full host),
`watchdog.sh` (D-state processes, orphaned z3s, a host above 85 % or refusing ssh), `validate.sh <snapshot> <tree set>`.
The 45 alone in 62555 s (17.4 h; seeding 26126, exploration 32924, compose+solver 2775, other 534 s); hl-1 ran the first
25, hl-2 the other 20; every verdict equals the port's rounds F1-F7. `results/hdfs/` holds H1's rows, `.smt` and
claims, and hdfs-11741's row from the port's F7 (owner).

## O. The other systems, on their own branches

Each system's state, plan and recipe are its own branch's STATE, TODO, START-HERE and REPRODUCE; this branch carries
their code only as far as `system/hbase` (26910df2a) and `system/solr`'s four fixes above.
- **HBase** (finished 2026-10-21): `system/hbase` (its STATE §H, `results/hbase/`), the fork `JHSUYU/hbase`
  `graphchecker/hbase-checks`; `system/hbase-buggy-detect`.
- **ZooKeeper** (finished 2026-10-22): `system/zookeeper` (its STATE §Z, `results/zookeeper/`), the fork
  `JHSUYU/zookeeper` `graphchecker/zookeeper-checks`; `system/zookeeper-buggy-detect`.
- **Solr** (finished 2026-10-26): `system/solr` (its STATE §S, `results/solr/`), the fork `JHSUYU/solr`
  `graphchecker/solr-checks`; `system/solr-buggy-detect`.
- **The old HDFS bugs put back by hand**: `system/hdfs-buggy-detect` (this branch plus the cases
  `experiments/hadoop/hdfs-buggy-<jira>`, their trees `hadoop-hdfs-bug-<jira>` = the fork's `graphchecker/hdfs-bug-<jira>`,
  and the engine support they needed; its `docs/handover/BUGGY-DETECT.md`).
## 0. The end state: two branches (owner 2026-10-06) -- superseded by §L (2026-10-27)

Since 2026-10-27 `system/hdfs-liftlab` (§L) replaces both branches below; they stay on the remote for history, with the
rounds and evidence of §4.

- **`system/hdfs`** (the locked body d6737d26b plus docs): 39 cases closed by round HL1 and its reruns -- the nine named
  bugs other than 11741 (17897, 17899-bug1/2/3, 17967-pathA/B/C, 17960, slowdisk-zero) and 30 study checks (05 06 08 09
  10 11 12 14 15 16 19 20 22 23 24 25 26 27 28 31 33 34 35 37 38 45 48 49 50 52). Locked: only docs land on it.
- **`system/hdfs1`**: the other 7 cases -- 07, 11741, 21, 29, 30, 39, 40 -- and every engine change made
  after the lock. Its STATUS carries all 46 rows, each naming the branch and run that closed it.
- Nothing merges back into `system/hdfs` or `main` (owner: "最终就是两个分支，system/hdfs和system/hdfs1").

What `system/hdfs1` adds to the locked body, each merged with its gate (git log has the numbers):
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

The remote keeps two branches per system, both on liftlab: its ad hoc checks and its old bugs put back (README "The
branches"). THE HDFS branch is `system/hdfs-liftlab` (§L, 2026-10-27); the two HDFS branches before it stay for history:

| remote branch | what it is |
| --- | --- |
| `main` (default) | the 2026-10-03 body (round V25, 14/14 on the named HDFS, Solr and ZooKeeper cases; VM `vm-model-guards2`, HDFS tree `gc/hdfs-unified-dtx`) |
| `system/hdfs-liftlab` | **THE HDFS branch** (§L): every HDFS case on HBase's engine, liftlab's memory-ledger scheduling, `results/hdfs/`; trees: the fork `JHSUYU/hadoop` `graphchecker/hdfs-checks`, `-adhoc21`, `hdfs-11741`. Replaces the two below |
| `system/hdfs` | history: the locked HDFS body and its 39 cases (§0) |
| `system/hdfs1` | history: the newest HDFS body of 2026-10-08 and the other 7 cases (§0) |
| `system/hdfs-buggy-detect` | this branch plus the old HDFS bugs put back by hand (§O); trees: the fork's `graphchecker/hdfs-bug-<jira>` |
| `system/solr`, `system/solr-buggy-detect` | the Solr group (from `system/hdfs1`) and its old bugs; tree: the fork `JHSUYU/solr` `graphchecker/solr-checks` (§O) |
| `system/hbase`, `system/hbase-buggy-detect` | the HBase group (from `system/solr`) and its old bugs; tree: the fork `JHSUYU/hbase` `graphchecker/hbase-checks` (§O) |
| `system/zookeeper`, `system/zookeeper-buggy-detect` | the ZooKeeper group (from `system/hbase`) and its old bugs; tree: the fork `JHSUYU/zookeeper` `graphchecker/zookeeper-checks` (§O) |

The CloudLab ports' heads are tags, not branches: `archive/system/{hdfs,hbase,zookeeper,solr}-cloudlab`.

Every other remote branch was deleted, bundled first: `/bigtemp/vnr3ne/handover/2026-10-08/graphchecker-remote-branches.bundle`
(`study`, `hdfs-compose-perf-wip`, `hdfs-container-writers`; `git fetch <bundle> 'refs/remotes/origin/*:refs/remotes/bundle/*'`
gets them back). The study's data moved to `docs/checks/` (`study.txt`, `SELECTION.md`, `new-bugs.txt`). The parked
local branches were turned into local tags on 2026-10-28, `archive/local/<branch>` in `~/GraphChecker` (not on the
remote), so a document's "branch X" of parked work is the tag `archive/local/X`; those holding work for later:

| local tag `archive/local/...` | head | state |
| --- | --- | --- |
| `hdfs1-prefix-span`, `hdfs-rule1`, `hdfs-u18-fix` | `40127e2b5`, `7d2819214`, `8ed56ddeb` | not for merge: the merged-span prefix (superseded by TODO HDFS §3's design), rule 1 and the own-fault key (missed the throughput bar, open defect 51) |
| `solr-bug-reindex` | `12283e3f1` | Solr #04 and Solr replay fidelity; SBR26 13/14 (solr-18413 regressed) |
| `hb-schedule` + `hb-sync` | `1fb4a475a`, `53f16e8b6` | one per-session happens-before relation; reviewed, not merged |
| `hbase-startup` | `3afb27f13` | HBase #14; two design questions (`system/hbase` TODO "HBase") |
| `hbase-e15` | `7940b6d09` | HBase's parked happens-before work (`system/hbase` TODO "HBase" 15), tree branch `gc/hb-e15` (231d8c7246) |
| `wire-codec-p1` | `3e9cb3182` | WIRE-CODEC; superseded for HDFS by codec capture |
| `solr-explore`, `solr-armkey`, `solr-growshape`, `solr-parplan`, `solr-shard` | `b0e712ceb`, `3bfdca7bc`, `727d48ea5`, `3df494a3a`, `d3b663462` | Solr's unmerged speed work (OPTIMIZATIONS 5.3, 5.6, 5.19) |

The other `archive/local/*` tags (`perf-vm-readout`, `solr-portname`, `solr-sc`, `solr-sc-836`, `solr-sg3-dry1`,
`solr-sg3-dry2`, `vm-ref-compare`) hold superseded experiments. Every branch merged into `system/hdfs1` and the superseded
ones (`hdfs-time-model`, `hdfs-clock-replay`, `hdfs-construction-only-values`, the `main-*` merge branches, ...) carry
nothing still owed.

## 3. System trees (the code under test)

The HDFS trees are worktrees of `~/hadoop`; its remote `origin` is the fork `git@github.com:JHSUYU/hadoop.git`, which keeps
one branch per tree a case reads (`experiments/hadoop/trees.tsv`; the old-bug trees `graphchecker/hdfs-bug-<jira>` besides). Each case's `case.sh` names its
tree as `$GC_TREES/<name>` (`tools/lib/gc-env.sh`: `/bigtemp/vnr3ne/wt` here); `experiments/hadoop/prepare-trees.sh` makes
any of them anew from the fork ([../REPRODUCE.md](../REPRODUCE.md) §3). **`system/hdfs-liftlab` reads three of them, at the
fork's current heads** (§L): `graphchecker/hdfs-checks` 899c200cc8e (every case but 21 and 11741; 07 too, so
`graphchecker/hdfs-checks-adhoc07` is read by no current case), `graphchecker/hdfs-checks-adhoc21` 25b4f1e531f and
`graphchecker/hdfs-11741` 6c86fca9a2b; H1's tree set is `/bigtemp/vnr3ne/wt/hl-trees-1`. The table names every tree
by its directory under `GC_TREES` and the local branch it was checked out at (in `~/hadoop`, `~/lucene-solr-8_11`,
`~/zookeeper`, `~/hbase`). On disk today (2026-10-28) are only the current tree sets: `hl-trees-1` (r7 and 21 at the
fork's heads), `bd-trees-1` (the old-bug trees of the four systems, `system/<x>-buggy-detect`), `sg3j-trees` (Solr),
`hb-int-trees-6` (HBase), `zk-int-trees-12` (ZooKeeper), and `lucene-solr-zktrace2`; the former bodies' and `main`'s worktrees below were removed and
are made again from their branch by `prepare-trees.sh` or `git worktree add`:

| tree (`$GC_TREES/<name>`) | local branch, head | remote branch | used by |
| --- | --- | --- | --- |
| `hadoop-hdfs-study-r7` | `gc/hdfs-study-r7` `bd72fcc1a13` | `graphchecker/hdfs-checks` (since moved on to 899c200cc8e, §L) | every HDFS case but 07, 21 and 11741 on both former branches (43 cases): trunk 734dd8a67cd with the 49 study points' markers, the named cases' markers and workloads, the adapter, the IPC, SASL and DataTransfer doors, and the time family's workarounds (STATUS "Per-system surface") |
| `hadoop-hdfs-study-r8` | `gc/hdfs-study-r8` `e3dab6266a7` | `graphchecker/hdfs-checks-adhoc07` | `system/hdfs1`'s hdfs-adhoc-07 only (`case.sh`): r7 + QJM's reply maps in the loggers' order |
| `hadoop-hdfs-21` | `gc/hdfs-study-r7-21` `c360d869629` | `graphchecker/hdfs-checks-adhoc21` (since moved on to 25b4f1e531f, §L) | hdfs-adhoc-21 only (`case.sh`): r7 + the DataNode handshake on its own joined thread |
| `hadoop-hdfs-11741-r6` | `gc/hdfs-11741-r6` `6c86fca9a2b` | `graphchecker/hdfs-11741` | hdfs-11741: trunk 734dd8a67cd with HDFS-11741's fix reverted, its own hook generation |
| `sg3j-trees/lucene-solr-checks` (worktree of `~/lucene-solr-8_11`) | `gc/solr-zktrace2` `12d23091d1` | `graphchecker/solr-checks` on the fork `JHSUYU/solr` (pushed 2026-10-16) | THE Solr tree of every `system/solr` case (that branch's REPRODUCE clones it) |
| `lucene-solr-storing` | `gc/solr-unified-storing` `04f8489` | none | solr-18406, solr-18413 (`main`) |
| `hbase-checks` (`/u/vnr3ne/hbase`) | `gc/hbase-checks` `b5d5cc6a20` | `graphchecker/hbase-checks` on the fork `JHSUYU/hbase` | THE HBase tree of every `system/hbase` case (that branch's REPRODUCE clones it) |
| `zookeeper-checks` (`/u/vnr3ne/zookeeper`) | `gc/zk-checks` `51b213562` | `graphchecker/zookeeper-checks` on the fork `JHSUYU/zookeeper` | the ZooKeeper tree of every `system/zookeeper` case (that branch's STATE §Z and REPRODUCE) |
| `zookeeper-unified`, `zookeeper-hb` | `gc/zk-unified` `8f18cf3a4`, `gc/zk-unified-hb` `47ddc8b36` | none (never push: apache remote) | the zk-bugs cases (`main`) |

The fork's 16 older `gc/*` branches (the per-bug trees, `gc/hdfs-unified`, `gc/hdfs-unified-dtx`, `gc/hdfs-bugs`,
`gc/hdfs-study-r5`/`r6`, `gc/hdfs-11741`/`-r5`) were deleted from the remote, bundled first in
`/bigtemp/vnr3ne/handover/2026-10-08/hadoop-gc-branches.bundle`; `main`'s cases read `gc/hdfs-unified-dtx` (local in
`~/hadoop`, tree `hadoop-hdfs-dtx`). The old-bug trees (`hadoop-hdfs-bug-<jira>` = the fork's
`graphchecker/hdfs-bug-<jira>`) are `system/hdfs-buggy-detect`'s (its `trees.tsv`; tree set `/bigtemp/vnr3ne/wt/bd-trees-1`).

VM image `/bigtemp/vnr3ne/vm-force12/j2sdk-image` serves `system/hdfs-liftlab` (its VM sources are `system/hbase`'s).
VM image `/bigtemp/vnr3ne/vm-hg5/j2sdk-image` serves both former HDFS branches (sources `hdfs-vm-hg5` 742f13363, the same in
both branches' `third_party/`; `tools/vm/build-image.sh` rebuilds it from either);
`vm-model-guards2` serves `main`. No VM change was made since. The VM's dead natives (VM.md §8) and
`exportLeaf`/`mintLeaf` can go in the next VM build.

Snapshots in `~/gc-run/` (frozen; `tools/rounds/snapshot-gc.sh` refuses one in use): `hl-1` (`system/hdfs-liftlab`
e2a6aebf9) and `hl-2` (f7c095f00), series H1. The former bodies' snapshots (`hl1`, `rp5`) were removed; a snapshot of a
commit is made again by `tools/lib/worktree-add.sh` (OPERATIONS §4).

## 4. Rounds and evidence

Outputs under `/bigtemp/vnr3ne/gc-out/<dir>/accept-<round>-<n>/` (`sweep-<round>-cases.tsv` maps n to the case).

| round | body | what it closed |
| --- | --- | --- |
| H1 (2026-10-26/27, §L) | `system/hdfs-liftlab` e2a6aebf9 and f7c095f00 (snapshots `hl-1`, `hl-2`), tree set `hl-trees-1`, `vm-force12`; one case at a time on 12 lifts, `/bigtemp/vnr3ne/gc-out/hdfs-final/accept-H1-*` | the 45 cases but 11741, each alone, with its time breakdown (`results/hdfs/`) |
| HL1 + reruns (HL1R-19, HL1R-pathC) | `system/hdfs` d6737d26b, `hdfs-study` | the 39 cases of `system/hdfs` |
| HF1 | `system/hdfs1` c3e10284f, `hdfs-study` | 29 30 40 (39 ran RUN_DEFECT there: CHECKING trap 18) |
| HF2 | the same, 14400 s | 11741 PASS (CLOCK_SKEW, 5168 s) |
| W21 | `hdfs1-21-workaround`, `hdfs-21w` | 21 (time family, residue named) |
| CC8-07 | `hdfs1-07-wa`, `hdfs-codec-capture` | none: stopped in COMPOSE after its fixed point |
| HF3 | `system/hdfs1` afd8db1b5, `hdfs-study`, 10800 s | none: 07 RUN_DEFECT (FIXED_POINT, z3 unsat, no BOUNDED/UNBOUND; 38 self-contradictory paths, an unstated file read, 69 unfinished obligations; STATUS 61-63) |
| EX1 (2026-10-07) | exclusive series, one case at a time on the ten lifts, `/bigtemp/vnr3ne/gc-out/hdfs-excl`; driver `/bigtemp/vnr3ne/analysis/excl-2026-10-07/excl-driver.sh` | 07 (EX1-adhoc-07e, system/hdfs1 8c446418b: UNSAT), and every case's time breakdown and closure size (PERFORMANCE §6) |
| OK3, OK4, OK5 | `hdfs1-open-arm-keys` fd0b0cd8a, `hdfs1-open-arm-keys` | 39 twice (UNSAT, clean), 40 (UNSAT) |
| agents' gates | own `GC_OUT`s | OA2-OA5 (open arms), WD1-WD3 (wait deadline; WD3: 17897 PASS), CC1-CC8 (codec capture), PS1-PS2 (prefix span), P1A-P3C (time family probes) |

Per check: [../STATUS.md](../STATUS.md) "HDFS checks" (verdict and the hand reading) and
[../checks/README.md](../checks/README.md) (state per row). How each is checked: [CHECKING.md](CHECKING.md).
New bugs: none. The 10 named bugs pass by mandate (11741 CLOCK_SKEW; the others MARKER_FLIPPED by an IPC door fault,
17960 by its configuration, slowdisk-zero by STATE re-pairing).

## 5. Where the analyses and evidence live

- `docs/checks/` (in the repo): the selection, the per-system point tables, the verified bugs.
- `/bigtemp/vnr3ne/analysis/study-2026-10-06b/`: the 2026-10-06 session's agent briefs (`brief-*.md`), the `.smt` readings draft
  (`status-readings.md`), `anchor-check.py` (whether each case's seed reached its declared occurrence) and notes
  (`smt-checks.md`).
- The agents' evidence runs of 2026-10-06/07 (open arms, wait deadline, time-r6, codec capture, rule 1, W21, the open-arm
  keys) are no longer on disk; their findings are in STATUS and §0.
- `/bigtemp/vnr3ne/analysis/hdfs-2026-10-26/`: series H1's drivers, gates, tree-set log and decision log (§L).
- `/bigtemp/vnr3ne/analysis/excl-2026-10-07/` (the EX1 driver), `cleanup-2026-10-08/` (the cleanup's briefs);
  `/bigtemp/vnr3ne/gc-out/hdfs-excl` (EX1's runs, PRUNE=0: the offline gate's corpora) and `hdfs-study` (the former
  bodies' rounds) are kept.
- `/bigtemp/vnr3ne/handover/`: bundles of deleted branches (`2026-10-08/`: the remote branches of §2 and §3; older
  dated bundles), WIP patches of stopped agents, the 10-06 scratch.
- Older: `/bigtemp/vnr3ne/analysis/study-2026-10-04/`, `study-2026-10-05/`, `/bigtemp/vnr3ne/specs/` (proposals cited
  by code comments), `~/bug_study/`.
