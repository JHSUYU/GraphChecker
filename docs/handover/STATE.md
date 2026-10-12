# State: HDFS finished; Solr stopped for a handover (2026-10-12)

Solr: section S below. The HDFS group is finished: all 46 cases have an exported `.smt` read by hand against the HDFS code, one row each in
[../STATUS.md](../STATUS.md) "HDFS checks" (07, the last, closed on 2026-10-07: EX1-adhoc-07e on `system/hdfs1`
8c446418b). Every case then ran alone on the ten lifts for its time breakdown (series EX1,
`/bigtemp/vnr3ne/gc-out/hdfs-excl`; the 46 rows are [../design/PERFORMANCE.md](../design/PERFORMANCE.md) §6). The owner
then stopped the work; on 2026-10-08 the code, scripts and documents were cleaned ("清理所有无用的文档/死代码/没用的脚本
fallback") and the remotes cut down to what is kept (§2, §3). Nothing runs on any lift and no agent is working. Read this
file, then [TODO.md](TODO.md) (what is left, in order), [RULES.md](RULES.md), [CHECKING.md](CHECKING.md),
[AGENTS.md](AGENTS.md), [OPERATIONS.md](OPERATIONS.md) and [PARALLEL.md](PARALLEL.md). The design is in
[../design/](../design/README.md); every check's state is in [../checks/README.md](../checks/README.md); done / partial /
missing per requirement in [../STATUS.md](../STATUS.md).

## S. Solr at the owner's stop (2026-10-12) -- read this first if you take over Solr

The owner stopped the Solr group again on 2026-10-12 (~14:00) for a handover to another agent ("停止所有的agent，任务。
更新对应的文档。我要让别的coding agent接手"). Every agent and run is stopped (no GraphChecker process on any lift), every
branch committed (unfinished work as `WIP:`), nothing pushed. The plan, in order, is [TODO.md](TODO.md) "Solr"; the
agents' own reports are `/bigtemp/vnr3ne/analysis/solr-2026-10-11/HANDOVER-2026-10-12.md`; every case's latest evidence
is [../STATUS.md](../STATUS.md) "Solr checks".

- **`system/solr` `8bd4a0cfb` + this docs commit** (worktree `/bigtemp/vnr3ne/wt/gc-solr`, image
  `/bigtemp/vnr3ne/vm-force5/j2sdk-image`): everything gated so far (TODO Solr §0): the study checks' engine fixes (force2,
  Root:WAKE, D1b, admitted reach, lambda deciders), Z1 (ZooKeeper store state and provenance), the native realized order
  (stable names, the claim's cone), the moved-member rule, the timed-wait door with GROW of unplanned invocations, the
  GROW swap fix. Canaries on it pass native 10/10.
- **Three branches in flight, merge in this order** (TODO Solr §1): `solr-zk-doors` 9f0b81058 (READ doors + R4; reviewed,
  canaries PASS; left: lock-leak/restore/reindex canaries, then a full 40), `solr-explore2` fe8c7434f (EX; left: a review
  re-check, the offline gate and live 07/21 convergence), `solr-zk2` 7023c526b WIP (Z2; left: 18413 SAT twice, tra's final
  SAT + native, snapshot SAT, a re-check). `solr-sg3` 2ca18a2b5 is a dry-run integration of all three plus
  `seed_replay_time_factor=130`; the final Solr tree `gc/solr-final` 86f762adb1 is merged and built against it (2 of 17
  workloads run natively).
- **Bug checks:** 6 of 8 with full evidence (SAT, confirmed, native 10/10, chain read in pre-readings): 18406, 18413,
  migrate on system/solr; overseer-lock-leak, restore-construction, reindex-cleanup on Z1's code (round IZ1 + Z1's Y11;
  reindex needed its workload's createAlias made tolerant). tra-start-overwrite: witness claimed live and CONFIRMED on
  `solr-zk2` (Z2N) before the swap race (fixed) took the final verdict. snapshot-no-active: workload rewritten so a stale
  Overseer view can exist; not yet SAT.
- **Study checks:** none final. Their guards mostly read ZooKeeper cluster-state content (Z2), and 07/21/05/31/39 need
  EX to converge; 09 needs the timed-wait door (merged) and EX; 40 the READ doors; 13 the final tree's workarounds.
  Expected verdicts per case: `/bigtemp/vnr3ne/analysis/solr-2026-10-11/SG3-reading-checklist.md`.
- **Solr trees** (`~/lucene-solr-8_11`, unshallowed): `gc/solr-final` 86f762adb1 (the final tree), built from
  `gc/solr-zk-next` 22930889c8 + `gc/solr-zk-doors-r` 2346cafecd + `gc/solr-zk2-next` b2605b6bd7 + 13's workarounds.
  Nothing pushed to the fork yet.
- **Briefs, designs, notes:** `/bigtemp/vnr3ne/analysis/solr-2026-10-11/` (this session), `.../solr-2026-10-08/` (before).

## 0. The end state: two branches (owner 2026-10-06)

- **`system/hdfs`** (the locked body d6737d26b plus docs): 39 cases closed by round HL1 and its reruns -- the nine named
  bugs other than 11741 (17897, 17899-bug1/2/3, 17967-pathA/B/C, 17960, slowdisk-zero) and 30 study checks (05 06 08 09
  10 11 12 14 15 16 19 20 22 23 24 25 26 27 28 31 33 34 35 37 38 45 48 49 50 52). Locked: only docs land on it.
- **`system/hdfs1`** (this branch): the other 7 cases -- 07, 11741, 21, 29, 30, 39, 40 -- and every engine change made
  after the lock. Its STATUS carries all 46 rows, each naming the branch and run that closed it.
- Nothing merges back into `system/hdfs` or `main` (owner: "最终就是两个分支，system/hdfs和system/hdfs1"). The next system
  starts from `system/hdfs1`, the newer body (TODO).

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

The remote keeps three branches (2026-10-08, by the lead):

| remote branch | what it is |
| --- | --- |
| `main` (default) | the 2026-10-03 body (round V25, 14/14 on the named HDFS, Solr and ZooKeeper cases; VM `vm-model-guards2`, HDFS tree `gc/hdfs-unified-dtx`) |
| `system/hdfs` | the locked HDFS body and its 39 cases (§0) |
| `system/hdfs1` | the newest body and the other 7 cases (§0); where the next system starts |

Every other remote branch was deleted, bundled first: `/bigtemp/vnr3ne/handover/2026-10-08/graphchecker-remote-branches.bundle`
(`study`, `hdfs-compose-perf-wip`, `hdfs-container-writers`; `git fetch <bundle> 'refs/remotes/origin/*:refs/remotes/bundle/*'`
gets them back). The study's data moved to `docs/checks/` (`study.txt`, `selection.txt`, `new-bugs.txt`). The local
branches still exist (`git branch`, their worktrees in `git worktree list`); those holding parked work for later:

| local branch | head | state |
| --- | --- | --- |
| `system/solr` | `system/hdfs1` + the Solr plan (worktree `/bigtemp/vnr3ne/wt/gc-solr`) | the Solr group's branch (TODO Solr): 20 cases, the 8 bug checks SAT |
| `system/hbase`, `system/zookeeper` | `fe3a5f1a0` (= `main`) | each system's branch-to-be: `system/hdfs1` is merged into it when its turn comes (TODO) |
| `hdfs1-confirm-first` | `da913cd7c` | no witness attempt starts while a confirmation is queued, running or returned; merge only if a confirmation is seen waiting > 10 min (TODO HDFS §5) |
| `hdfs1-prefix-span`, `hdfs-rule1`, `hdfs-u18-fix` | `40127e2b5`, `7d2819214`, `8ed56ddeb` | not for merge: the merged-span prefix (superseded by TODO HDFS §3's design), rule 1 and the own-fault key (missed the throughput bar, open defect 51) |
| `solr-bug-reindex` | `12283e3f1` | Solr #04 and Solr replay fidelity; SBR26 13/14 (solr-18413 regressed). For the Solr turn |
| `hb-schedule` + `hb-sync` | `1fb4a475a`, `53f16e8b6` | one per-session happens-before relation; reviewed; for the ZooKeeper turn |
| `hbase-startup` | `3afb27f13` | HBase #14; two design questions (TODO HBase) |
| `wire-codec-p1` | `3e9cb3182` | WIRE-CODEC; superseded for HDFS by codec capture |

Every branch merged into `system/hdfs1` (`git branch --merged system/hdfs1`) and the superseded ones (`hdfs-time-model`,
`hdfs-clock-replay`, `hdfs-construction-only-values`, the `main-*` merge branches, ...) carry nothing still owed.

## 3. System trees (the code under test)

The HDFS trees are worktrees of `~/hadoop`; its remote `origin` is the fork `git@github.com:JHSUYU/hadoop.git`, which keeps
four branches, one per tree a case reads (2026-10-08; `experiments/hadoop/trees.tsv`). Each case's `case.sh` names its
tree as `$GC_TREES/<name>` (`tools/lib/gc-env.sh`: `/bigtemp/vnr3ne/wt` here); `experiments/hadoop/prepare-trees.sh` makes
any of them anew from the fork ([../REPRODUCE.md](../REPRODUCE.md) §3):

| tree (worktree) | local branch, head | remote branch | used by |
| --- | --- | --- | --- |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r7` | `gc/hdfs-study-r7` `bd72fcc1a13` | `graphchecker/hdfs-checks` | every HDFS case but 07, 21 and 11741 on both branches (43 cases): trunk 734dd8a67cd with the 49 study points' markers, the named cases' markers and workloads, the adapter, the IPC, SASL and DataTransfer doors, and the time family's workarounds (STATUS "Per-system surface"). Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-r7` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r8` | `gc/hdfs-study-r8` `e3dab6266a7` | `graphchecker/hdfs-checks-adhoc07` | hdfs-adhoc-07 only (`case.sh`): r7 + QJM's reply maps in the loggers' order. Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-r8` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-21` | `gc/hdfs-study-r7-21` `c360d869629` | `graphchecker/hdfs-checks-adhoc21` | hdfs-adhoc-21 only (`case.sh`): r7 + the DataNode handshake on its own joined thread |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-r6` | `gc/hdfs-11741-r6` `6c86fca9a2b` | `graphchecker/hdfs-11741` | hdfs-11741: trunk 734dd8a67cd with HDFS-11741's fix reverted, its own hook generation. Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-r6` |
| `/bigtemp/vnr3ne/wt/lucene-solr-storing` | `gc/solr-unified-storing` `04f8489` | none | solr-18406, solr-18413 (`main`) |
| `/bigtemp/vnr3ne/wt/lucene-solr-checks` | `gc/solr-checks` `3bcca50` | to be `graphchecker/solr-checks` on the fork `JHSUYU/solr` (owner 2026-10-08; TODO Solr §2), never an apache remote | the Solr group's one tree, every `system/solr` case: `gc/solr-bugs` `f65aaf7` (`gc/solr-unified-storing2` + the reindex marker) + the 12 study markers, the five new bug markers, the six bug workloads, the full-distributed tests' hook, the routed-alias tests' configset, the reindex latch's bound (STATUS "Per-system surface") |
| `/bigtemp/vnr3ne/wt/lucene-solr-body` | `gc/solr-body` `7e51565080` | (part of the final `graphchecker/solr-checks`) | the Solr body's tree hooks: the HTTP send in `executeMethod`, `CausynthRandom` (node order, seeded draws), `CausynthPorts`, `CausynthBounds` (SocketProxy, SolrConfigHandler), the store READ turn's SolrZkClient read hooks; agent M's rounds |
| `/bigtemp/vnr3ne/wt/lucene-solr-zk2`, `-zk3` | `gc/solr-zk-next` `53d81b09b1` | (part of the final tree) | Z1's hooks (`gc/solr-zk`: `decoded`, the queue-head tick, consumed items, the compared version on `stored`) + `gc/solr-body` 3bcf5616c2 |
| `/bigtemp/vnr3ne/wt/lucene-solr-zkdoors` | `gc/solr-zk-doors` `92c234a5d1` | (part of the final tree) | `gc/solr-zk-next` + `gc/solr-body` + the ZooKeeper READ doors' hooks (`causynthReading`, `causynthReplied` with the lost reply's local unwatch); built (agent RD's runs: `GC_TREES=/bigtemp/vnr3ne/wt/zkdoors-trees`) |
| `/bigtemp/vnr3ne/wt/pno-trees/lucene-solr-checks` | `gc/solr-zk2` `914e56311a` | (part of the final tree) | Z2's codec capture (`Utils.toJSON`/`fromJSON`) on `gc/solr-zk-next`; built |
| `/bigtemp/vnr3ne/wt/sg2b-trees/lucene-solr-checks` | detached `88425b0` | none | the tree of rounds SG2b/SG2c and agent F2's runs |
| `/bigtemp/vnr3ne/wt/lucene-solr-bugs` | `gc/solr-bugs` `f65aaf7` | none | `gc/solr-checks`' base; `solr-bug-reindex`'s rounds |
| `/bigtemp/vnr3ne/wt/zookeeper-unified`, `zookeeper-hb` | `gc/zk-unified` `8f18cf3a4`, `gc/zk-unified-hb` `47ddc8b36` | none (never push: apache remote) | the zk-bugs cases (`main`) |
| `/bigtemp/vnr3ne/wt/hbase-unified` | `gc/hbase-unified` `1051825287` | none (never push: apache remote) | HBase cases; must drop `CausynthRpc.java:61-62`'s `, call.param` before any run on the new body |

The fork's 16 older `gc/*` branches (the per-bug trees, `gc/hdfs-unified`, `gc/hdfs-unified-dtx`, `gc/hdfs-bugs`,
`gc/hdfs-study-r5`/`r6`, `gc/hdfs-11741`/`-r5`) were deleted, bundled first in
`/bigtemp/vnr3ne/handover/2026-10-08/hadoop-gc-branches.bundle`; `main`'s cases read `gc/hdfs-unified-dtx`
(`/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx`, local). Any other Hadoop worktree under `/bigtemp/vnr3ne/wt/` is superseded.

VM image `/bigtemp/vnr3ne/vm-hg5/j2sdk-image` serves both HDFS branches (sources `hdfs-vm-hg5` 742f13363, the same in
both branches' `third_party/`; `tools/vm/build-image.sh` rebuilds it from either);
`vm-model-guards2` serves `main`. No VM change was made since. The VM's dead natives (VM.md §8) and
`exportLeaf`/`mintLeaf` can go in the next VM build.

Snapshots in `~/gc-run/` (frozen; `tools/rounds/snapshot-gc.sh` refuses one in use): `hl1` (`system/hdfs`'s locking
round) and `rp5` (`system/hdfs1`'s code of the EX1 series; its jar is the offline gate's baseline for this body).

## 4. Rounds and evidence

Outputs under `/bigtemp/vnr3ne/gc-out/<dir>/accept-<round>-<n>/` (`sweep-<round>-cases.tsv` maps n to the case).

| round | body | what it closed |
| --- | --- | --- |
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
- Agents' evidence: `/bigtemp/vnr3ne/gc-out/hdfs-open-arms/` (S), `hdfs-wait-deadline/` and `hdfs-time-r6/` (T: probes,
  `probe-table.py`), `hdfs-codec-capture/` (C), `hdfs-rule1/` (R: key gates, probes), `hdfs-21w/` (W21),
  `hdfs1-open-arm-keys/` (T's 39 runs).
- `/bigtemp/vnr3ne/analysis/excl-2026-10-07/` (the EX1 driver), `cleanup-2026-10-08/` (the cleanup's briefs).
- `/bigtemp/vnr3ne/handover/`: bundles of deleted branches (`2026-10-08/`: the remote branches of §2 and §3; older
  dated bundles), WIP patches of stopped agents, the 10-06 scratch.
- Older: `/bigtemp/vnr3ne/analysis/study-2026-10-04/`, `study-2026-10-05/`, `/bigtemp/vnr3ne/specs/` (proposals cited
  by code comments), `~/bug_study/`.
