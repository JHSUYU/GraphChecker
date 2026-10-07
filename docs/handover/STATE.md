# State at the end of the HDFS group (2026-10-06 night)

The HDFS group is finished but for one case: 45 of its 46 cases have an exported `.smt` read by hand against the HDFS
code, one row each in [../STATUS.md](../STATUS.md) "HDFS checks"; 07's last run was stopped before its verdict (TODO
HDFS §0). The owner then stopped the work ("这3个跑完就可以停。然后更新所有文档里要更新的位置…存在的问题也要写好"; "07不用跑了。
留个todo就行。39跑完就完了"): nothing runs on any lift and every agent has stopped. Read this file, then
[TODO.md](TODO.md) (what is left, in order), [RULES.md](RULES.md), [CHECKING.md](CHECKING.md), [AGENTS.md](AGENTS.md),
[OPERATIONS.md](OPERATIONS.md) and [PARALLEL.md](PARALLEL.md). The design is in [../design/](../design/README.md);
every check's state is in [../checks/README.md](../checks/README.md); done / partial / missing per requirement in
[../STATUS.md](../STATUS.md).

## 0. The end state: two branches (owner 2026-10-06)

- **`system/hdfs`** (head 04b1f4110 = the locked body d6737d26b plus docs): 39 cases closed by round HL1 and its reruns
  -- the nine named bugs other than 11741 (17897, 17899-bug1/2/3, 17967-pathA/B/C, 17960, slowdisk-zero) and 30 study
  checks (05 06 08 09 10 11 12 14 15 16 19 20 22 23 24 25 26 27 28 31 33 34 35 37 38 45 48 49 50 52). Locked: only docs
  land on it.
- **`system/hdfs1`** (this branch): the other 7 cases -- 11741, 21, 29, 30, 39, 40 closed, 07 open (TODO HDFS §0) -- and
  every engine change made after the lock. Its STATUS carries all 46 rows, each naming the branch and run that closed it.
- Nothing merges back into `system/hdfs` or `main` (owner: "最终就是两个分支，system/hdfs和system/hdfs1"). The next system
  starts from `system/hdfs1`, the newer body (TODO).

What `system/hdfs1` adds to the locked body, each merged with its gate (git log has the numbers):
- **Open arms** (agent S, `hdfs-open-arms` 3bdf1ec4f): a faithful replay that never enters an open arm's occurrence
  refutes that world (`WORLD_REFUTED`); configuration domains from the recorded comparisons; a version no activation
  wrote is named (`UNATTRIBUTED_STORE`) and re-pairable through its own symbol. Closed 39 and 40 first.
- **The Cone fix** (3e7becca7): a body's Cone read once and indexed by selector (11741's COMPOSE was quadratic).
- **Wait deadline** (agent T, `hdfs-wait-deadline` 9565537f2): a timed wait that takes its WAKE slot returns no sooner
  than its own deadline (29, 30: a DataNode skipped heartbeats and the NameNode chose the other recovery primary).
- **Codec capture** (agent C, `hdfs-codec-capture` d502ddbc7): the IPC and DataTransfer doors walk the protobuf message
  they carry; a field's value is exported at its builder's setter and staged by the door; the engine's plumbing is
  never state; an arm's input shape names its deliverers as a sorted set. Reviewed: open defects 52-56.
- **21's workaround** (agent R, `hdfs1-21-workaround` 085b9a9ed): tree `gc/hdfs-study-r7-21` and `loop-bounds-21.jsonl`.
- **07's workaround** (agent C, `hdfs1-07-wa`): tree `gc/hdfs-study-r8` and world depth 6 for 07 only.
- **Open-arm keys** (agent T, `hdfs1-open-arm-keys`): each path's open arm judged by its own flip's answers where it
  has any, else the shared verdict; a replay that did not run its world is asked once more; a flip no variable reaches
  is UNSAT on its path (`NOT_FLIPPABLE`) unless a HELD value or refused construct feeds it.

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

## 2. GraphChecker branches (repo `~/GraphChecker`, remote `origin` = github; nothing pushed since the 10-06 handover)

| branch | head | worktree | state |
| --- | --- | --- | --- |
| `system/hdfs` | `04b1f4110` | `/bigtemp/vnr3ne/wt/gc-hdfs` (full checkout) | locked HDFS body d6737d26b + docs; 39 cases |
| `system/hdfs1` | (head) | `/bigtemp/vnr3ne/wt/gc-hdfs1` | the newest body; 7 cases; §0 |
| `main` | `fe3a5f1a0` | `~/GraphChecker` | the 2026-10-03 body (V25 14/14). `system/solr`, `system/hbase`, `system/zookeeper` = `main` |
| `hdfs1-confirm-first` | `da913cd7c` | `/bigtemp/vnr3ne/wt/gc-hdfs1-confirm-first` | parked (TODO): no witness attempt starts while a confirmation is queued, running or returned; merge only if a confirmation is seen waiting > 10 min |
| `hdfs1-prefix-span`, `hdfs-rule1`, `hdfs-u18-fix` | `40127e2b5`, `7d2819214`, `8ed56ddeb` | `/bigtemp/vnr3ne/wt/gc-hdfs1-prefix-span` | parked, not for merge: the merged-span prefix and the time-cut key (superseded by TODO §3b's design), rule 1 and the own-fault key (missed the throughput bar) |
| `hdfs-time-model`, `hdfs-clock-replay` | `49f502302`, `22520bf02` | | the reverted time model and its predecessor: delete |
| `hdfs-refactor-compose` | `ac2f58490` | `/bigtemp/vnr3ne/wt/gc-hdfs-refactor-compose` | behaviour-preserving COMPOSE refactor, steps 1-4; TODO cleanup |
| `hdfs-compose-perf-wip`, `hdfs-construction-only-values`, `hdfs-container-writers` | | | measurement / parked / superseded: delete |
| merged into `system/hdfs1`, deletable | | | `hdfs-int`, `hdfs-export-weave`, `hdfs-frontier-depth`, `hdfs-solver-fallback`, `hdfs-ipc-handoff-name`, `hdfs-open-arms`, `hdfs-wait-deadline`, `hdfs-codec-capture`, `hdfs1-21-workaround`, `hdfs1-07-wa`, `hdfs1-open-arm-keys`, and the older list of the 10-06 handover (git history); remove their worktrees first (`git worktree list`) |
| `solr-bug-reindex` | `12283e3f1` | `.claude/worktrees/agent-a6cdfa854234df67e` | Solr #04 + Solr replay fidelity; SBR26 13/14 (solr-18413 regressed). For the Solr turn. |
| `hb-schedule` + `hb-sync` | `1fb4a475a`, `53f16e8b6` | `.claude/worktrees/agent-aea16c87adafb5d81` | one per-session happens-before relation; reviewed; for the ZooKeeper turn |
| `hbase-startup` | `3afb27f13` | `/bigtemp/vnr3ne/wt/gc-hbase-startup` | HBase #14; two design questions (TODO HBase) |
| `wire-codec-p1` | `3e9cb3182` | `.claude/worktrees/wire-codec-p1` | WIRE-CODEC; superseded for HDFS by codec capture |
| `study` | `b9da03fc1` | `/bigtemp/vnr3ne/wt/gc-study` | `study.txt`, `selection.txt`; the tables are also in `docs/checks/` |

## 3. System trees (the code under test)

| tree (worktree) | branch, head | used by |
| --- | --- | --- |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r7` | `gc/hdfs-study-r7` `bd72fcc1a13` | every HDFS case but 07, 21 and 11741 on both branches. r6 + the time family's workarounds (STATUS "Per-system surface"). Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-r7` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-21` | `gc/hdfs-study-r7-21` `c360d869629` | hdfs-adhoc-21 only (`case.sh`): r7 + the DataNode handshake on its own joined thread |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r8` | `gc/hdfs-study-r8` `e3dab6266a7` | hdfs-adhoc-07 only (`case.sh`): r7 + QJM's reply maps in the loggers' order. Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-r8` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-r6` | `gc/hdfs-11741-r6` `6c86fca9a2b` | hdfs-11741. Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-r6` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r6` | `gc/hdfs-study-r6` `7e81b3a588c` | the base of r7; r6 = r5 + the IPC hand-off naming + the codec door calls (OPERATIONS §1) |
| `hadoop-hdfs-study-r7b`, r5, r4, r3, `-11741-r5`/`-r4`/`-verb`, `-study-next`, `-study-startup`, `-study`, `-bugs`, `-dtx*`, `-w6` | | superseded; kept only for the runs that name them (r7b can go) |
| `/bigtemp/vnr3ne/wt/lucene-solr-storing` | `gc/solr-unified-storing` `04f8489` | solr-18406, solr-18413 (main); also `lucene-solr-bugs`, `lucene-solr-storing2`; study markers not added yet |
| `/bigtemp/vnr3ne/wt/zookeeper-unified`, `zookeeper-hb` | `gc/zk-unified` `8f18cf3a4`, `gc/zk-unified-hb` `47ddc8b36` | the zk-bugs cases (main); never push (apache remote) |
| `/bigtemp/vnr3ne/wt/hbase-unified` | `gc/hbase-unified` `1051825287` | HBase cases; must drop `CausynthRpc.java:61-62`'s `, call.param` before any run on the new body |

VM image `/bigtemp/vnr3ne/vm-hg5/j2sdk-image` serves both HDFS branches (sources `hdfs-vm-hg5` 742f13363);
`vm-model-guards2` serves `main`. No VM change was made since. The VM's dead natives (VM.md §8) and
`exportLeaf`/`mintLeaf` can go in the next VM build.

Snapshots in `~/gc-run/` (frozen; `tools/rounds/snapshot-gc.sh` refuses one in use): `hl1` (system/hdfs's locking round),
`hf1` (system/hdfs1's code at c3e10284f: HF1, HF2), `cc8` (07's workaround), `w21` (21's), `oak1` (T's open-arm keys).
Every older one (`int1`-`int6`, `ho1`, `wd1`, `ps1`, `ps2`, `cc1`-`cc7`, `cc-base*`, `oa0`-`oa5`, `r1a`, `r1b`, `u18a`,
`t7a`-`t7d`, `t8`, `hg9`, `sw1`, `aw4`, `aw5`, `ar3`, `fd2`, `cw3`, `tm16`, `a4base`) can go.

## 4. Rounds and evidence

Outputs under `/bigtemp/vnr3ne/gc-out/<dir>/accept-<round>-<n>/` (`sweep-<round>-cases.tsv` maps n to the case).

| round | body | what it closed |
| --- | --- | --- |
| HL1 + reruns (HL1R-19, HL1R-pathC) | `system/hdfs` d6737d26b, `hdfs-study` | the 39 cases of `system/hdfs` |
| HF1 | `system/hdfs1` c3e10284f, `hdfs-study` | 29 30 40 (39 ran RUN_DEFECT there: CHECKING trap 18) |
| HF2 | the same, 14400 s | 11741 PASS (CLOCK_SKEW, 5168 s) |
| W21 | `hdfs1-21-workaround`, `hdfs-21w` | 21 (time family, residue named) |
| CC8-07 | `hdfs1-07-wa`, `hdfs-codec-capture` | none: 07 reached its fixed point, stopped in COMPOSE by the owner's end (TODO HDFS §0) |
| OK3, OK4, OK5 | `hdfs1-open-arm-keys` fd0b0cd8a, `hdfs1-open-arm-keys` | 39 twice (UNSAT, clean), 40 (UNSAT) |
| agents' gates | own `GC_OUT`s | OA2-OA5 (open arms), WD1-WD3 (wait deadline; WD3: 17897 PASS), CC1-CC8 (codec capture), PS1-PS2 (prefix span), P1A-P3C (time family probes) |

Per check: [../STATUS.md](../STATUS.md) "HDFS checks" (verdict and the hand reading) and
[../checks/README.md](../checks/README.md) (state per row). How each is checked: [CHECKING.md](CHECKING.md).
New bugs: none. The 10 named bugs pass by mandate (11741 CLOCK_SKEW; the others MARKER_FLIPPED by an IPC door fault,
17960 by its configuration, slowdisk-zero by STATE re-pairing).

## 5. Where the analyses and evidence live

- `docs/checks/` (in the repo): the selection, the per-system point tables, the verified bugs.
- `/bigtemp/vnr3ne/analysis/study-2026-10-06b/`: this session's agent briefs (`brief-*.md`), the `.smt` readings draft
  (`status-readings.md`), `anchor-check.py` (whether each case's seed reached its declared occurrence) and notes
  (`smt-checks.md`).
- Agents' evidence: `/bigtemp/vnr3ne/gc-out/hdfs-open-arms/` (S), `hdfs-wait-deadline/` and `hdfs-time-r6/` (T: probes,
  `probe-table.py`), `hdfs-codec-capture/` (C), `hdfs-rule1/` (R: key gates, probes), `hdfs-21w/` (W21),
  `hdfs1-open-arm-keys/` (T's 39 runs).
- Older: `/bigtemp/vnr3ne/analysis/study-2026-10-04/`, `study-2026-10-05/`, `/bigtemp/vnr3ne/handover/` (bundles of
  deleted branches, the 10-06 scratch), `/bigtemp/vnr3ne/specs/` (proposals cited by code comments), `~/bug_study/`.
