# State: `system/hbase-buggy-detect` -- HBase's ad hoc checks (finished 2026-10-21) plus the old HBase bugs put back

This branch is `system/hbase` (section H: HBase finished, the adapter the HBase fork's `graphchecker/hbase-checks`;
[../REPRODUCE.md](../REPRODUCE.md) §7) plus the old HBase bugs that make an ad hoc check fail, put back by hand on
today's tree, and the engine support they needed (section B; [BUGGY-DETECT.md](BUGGY-DETECT.md) has every system's
table; REPRODUCE §B runs them from a fresh clone). Every other system is on its own pair of branches (§2). Read this
file, then [START-HERE.md](START-HERE.md), [TODO.md](TODO.md) (what is left), [RULES.md](RULES.md),
[CHECKING.md](CHECKING.md), [AGENTS.md](AGENTS.md), [OPERATIONS.md](OPERATIONS.md) and [PARALLEL.md](PARALLEL.md). The
design is in [../design/](../design/README.md); every check's state is in [../checks/README.md](../checks/README.md);
done / partial / missing per requirement in [../STATUS.md](../STATUS.md).

## B. The old HBase bugs (`system/hbase-buggy-detect`, liftlab)

The owner's goal (2026-10-26): from the owner's list of old bugs, those that make an ad hoc check's OWN declared throw
fail, put back with small changes on today's trees and detected on each system's branch. HBase's three:
hbase-buggy-15039 (HBASE-15039 at hbase-adhoc-34), hbase-buggy-20642 (HBASE-20642 at hbase-adhoc-04) and
hbase-buggy-28533 (HBASE-28533 at hbase-adhoc-15: README only, not reachable at its own throw on today's code; the
owner closed it as it stands). Each case directory's README has the bug, the put-back commits, the workload, every
declaration and the runs.

**The branch** (GitHub `system/hbase-buggy-detect`; local `bd-liftlab-hbase`, worktree `/bigtemp/vnr3ne/wt/gc-hbase-bd`):
`system/hbase` 26910df2a, then the CloudLab work it was made on (the cases, their trees, the engine support below, and
CloudLab's scheduling layer, `archive/system/hbase-cloudlab`), then b978bacb8: CloudLab's scheduling layer reverted --
`run_engine.sh`, `tools/` and the case settings are `system/hbase`'s (the host ledger charges memory, 70 % of a lift; a
head step's heap 12288 MB, the buggy cases' too) with REPRODUCE by shape kept. The engine support, each reviewed:
948e4779f (the reply legs of a demanded message's doors are its control producers, in PLAN and EXPLORE: SYMBOL-SCOPE,
PIPELINE §7.2), 93a168e87 + 298508ffa (IDENTITY §9's order rule in one implementation, `runtime/AnswerOrder`, for a
replay and a native REPRODUCE run; `reproduced` exact-only, `answeredByShape`/`reproducedByShape` counted apart,
`ADDRESS_UNSTABLE` in `plant.log`: PIPELINE §10b); rejected and reverted: 455a6dd66 (017dcf890).

**The trees:** the HBase fork's `graphchecker/hbase-bug-15039` (c2cecb3756), `-20642` (1ba966bb6c), `-28533`
(de71623820), each from `graphchecker/hbase-checks` b5d5cc6a20 (`experiments/hbase/trees.tsv`). On liftlab: the tree set
`/bigtemp/vnr3ne/wt/bd-trees-1` (every bug tree of the four systems, each system's `prepare-trees.sh` with
`GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1 GC_M2=/bigtemp/vnr3ne/m2/bd-1`; HBase's two workloads PASSED natively,
2026-10-28), the snapshot `/u/vnr3ne/gc-run/bd-hbase-1` (b978bacb8), the image `/bigtemp/vnr3ne/vm-force12`.

**Results:**

| case | CloudLab, 2026-10-26 | liftlab, B1 (`/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-<case>`) |
| --- | --- | --- |
| hbase-buggy-15039 | HB15039b: SAT `STATE_PAIRING_FLIPPED`, confirmed, native 10/10, control 0/10, report.py PASS, 1211 s | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 755 s (B1-hbase-buggy-15039) |
| hbase-buggy-20642 | HB20642f: SAT `MARKER_FLIPPED` (the first DisableTable's lost reply), confirmed, native 10/10 by IDENTITY §9 shape, 0/10 exact, control 0/10; accepted by the owner 2026-10-27 (HB20642e: 866 s, report.py PASS) | B1: SAT, CONFIRM, native by IDENTITY §9 shape 10/10 (exact id 0/10), control 0/10, report.py PASS, 1393 s; 5 claims CONFIRM refuted first, 681 s (B1-hbase-buggy-20642) |
| hbase-buggy-28533 | not run (not reachable on today's code) | not run |

B1's first launch (2026-10-28 00:11) headed both HBase cases on lift02 and lift03, which cannot reach lift15: PREFLIGHT
refused them (kept as `accept-B1STOP-*`); relaunched at 00:22 with heads lift04 and lift06.

## H. HBase (finished: final series 2026-10-21) -- read this first if you take over HBase

The owner's goal: "基于我们solr现在这么好的代码基础，完成对hbase的adhod check" (RULES "HBase: the goal and its scope").
The first session (2026-10-19, a lead and five coding agents) built the HBase platform on `system/solr`'s engine; the owner
stopped it for a handover at 23:10. The second session (2026-10-19 23:40 to 2026-10-20, a new lead and five agents: H1
platform, H2 ZooKeeper, H3 RPC, H4 checks, H5 engine analysis) took over from START-HERE and ran every case of
`experiments/hbase/hbase-cases.tsv`. **All five of the owner's bugs PASS.** Read [START-HERE.md](START-HERE.md), then
[TODO.md](TODO.md) "HBase" (the parked engine items), then LESSONS §9.

**`system/hbase`** (the code; pushed to GitHub 2026-10-22, owner; worktree `/bigtemp/vnr3ne/wt/gc-hbase`): `system/solr`'s engine plus the first
session's HBase work (doors `HBASE_RPC` and ZooKeeper, continuation and timer identity, the VM's enums and sorted maps,
PLAN/COMPOSE/CONFIRM fixes, `tools/analysis/vacuity.py`) and, from the second session, each gated:
- heads: `engine_memory_mb` 12288 for both HBase workflow files (measured peaks ~3 GB; a head is charged its heap for life);
- CONFIRM/REPRODUCE: an order no hold realizes is checked at its later end (93122386b); the native plant leaves out orders
  in turn-counted roots (b9dfcedc5) and orders a client thread's synchronous replies imply (a4e586d4b,
  `contract.ClientProgramOrder`); a moved root's mint is looked up in the arm session that names it (2a42e96d4); a STATE
  row whose reader the plan holds behind the anchor is not required (86cdb2603); CONFIG roots are planted natively at their
  getter, and an answer equal to what the producer sent is no plant (49c5698b7, 57de8ed4e);
- identity/schedule: a hand-off serves only work another thread started (4a06f9d88); a claimed hand-off held where it runs
  is held at its claim's entry, with structural and cycle fallbacks (4f80eb7f3, a4b7879e9);
- PLAN/EXPLORE: an own-turn door that ran earlier is a control producer (e49ff4485); PLAN's fetches cover declared reads'
  receivers (f6e07b3c9); DUPLICATE_WORLD: a world is replayed once (ddcbbb8ec); EXPLORE stops at once on a BLOCKING
  TARGET_FATAL_IN_RECORDING (07737dc35); readers re-open a file replaced under them (ESTALE, c27f51a03);
- COMPOSE/DECIDE: an enum compare over reads that do not move is its writer's name, an untaken fatal over an unmodelled
  operation is held to its movers (8cb3cdfeb); an explored session's own run is claimed first (47975f1e3); a confirmed
  claim that reproduces 0/N is a fallback and the loop tries the next (32a71ff21); the free-model witness keeps roots
  outside the selected path's cone at their recorded values (275e72578); fatal-observing explored worlds are valuations
  (49c5698b7);
- data: case rows, scopes and selectors (`experiments/hbase/hbase-adhoc/checks.tsv`), `hbase-bugs/root-domains.jsonl`
  (#11's skew roots), 34's ZOOKEEPER client faults, report.py's expected mechanisms for every bug check.

**The tree:** `/u/vnr3ne/hbase` branch `gc/hbase-checks` = the fork's `graphchecker/hbase-checks`
(`https://github.com/JHSUYU/hbase.git`, pushed after every merge): Apache HBase master 1790942bb2 backported to Java 8 with
the adapter and the named workarounds (STATUS "Per-system surface", HBase column). The second session added: the
encoded-region map as a ConcurrentHashMap (14), 34's workload, the light loads of 24 and 07, nsrg's tracked group map,
#11's automatic-mode active time (start code + a configured skew, per-master constant keys), the state guards of 07, 11, 12
comparing the enum they read, 13's merge-qualifier map and synchronous janitor scan, and one region-server load report per
active master. Its final head is b5d5cc6a20 (2026-10-21): plus the ZooKeeper tombstone hooks and the procedure member's
narrow anchor (24), a finished procedure's last hand-off after its locks are released (13), and 07's focused workload
`TestCausynthRestoreSnapshot`.

**Results:** the final series (2026-10-20/21) is `results/hbase/README.md` on `system/hbase`: every case's final `.smt`,
claim, verdict, time breakdown and closure size, from the run dirs `/bigtemp/vnr3ne/gc-out/hbase-final/accept-<run>`
(F1* concurrent, kept under 30 min; F2* alone; F3S alone and scoped; `*STOP*` dirs are stopped runs, evidence only). The five
bugs PASS: #12 10/10, 04 = HBASE-30484 10/10, 22 = HBASE-30483 10/10, #13 10/10, #11 8/10; 34 and 24 SAT confirmed (not new
bugs); 21 UNSAT substantive; 19 20 28 35 37 31 UNSAT vacuous; 07 08 10 11 12 14 15 named bounds (client program order,
TODO HBase 15); 13 RUN_DEFECT, vacuous (TODO HBase 19). Earlier runs per case: `docs/checks/HBASE.md` §E and STATUS "HBase
checks".

**Where things are:** the final series' drivers and tables `/bigtemp/vnr3ne/analysis/hbase-2026-10-20/lead/` (`series.sh`,
`excl.sh`, `excl2.sh`, `final-stats.py`, `collect-results.sh`, the series logs) beside the second session's briefs, helpers
and evidence in `/bigtemp/vnr3ne/analysis/hbase-2026-10-20/` (`readings.md`, the agents' E1-E4 and H1-H5 reports); run outputs
`/bigtemp/vnr3ne/gc-out/hbase-final` (the development runs' outputs are deleted);
the final snapshots `/u/vnr3ne/gc-run/hb-int-16` (319428f7d) and `hb-int-17` (e53c3c882); the final tree set
`/bigtemp/vnr3ne/wt/hb-int-trees-6` (b5d5cc6a20, Maven repository `/bigtemp/vnr3ne/m2/hbase-int6`); the image
`/bigtemp/vnr3ne/vm-force12`. The parked happens-before work (TODO HBase 15) is the tag `archive/local/hbase-e15` (7940b6d09, not merged)
and the tree branch `gc/hb-e15` (231d8c7246).

## 1. The goals (verbatim)

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

| remote branch | what it is |
| --- | --- |
| `main` (default) | the 2026-10-03 body (round V25, 14/14 on the named HDFS, Solr and ZooKeeper cases; VM `vm-model-guards2`, HDFS tree `gc/hdfs-unified-dtx`) |
| `system/hdfs-liftlab` | THE HDFS branch: every HDFS case on HBase's engine with liftlab's scheduling (`results/hdfs/`); replaces `system/hdfs` (the locked body, 39 cases) and `system/hdfs1` (the other 7), which stay on the remote as history (series EX1 ran on them) |
| `system/hdfs-buggy-detect` | `system/hdfs-liftlab` plus the old HDFS bugs put back |
| `system/solr` | the Solr group (finished 2026-10-26), from `system/hdfs1`; tree: the fork `JHSUYU/solr` `graphchecker/solr-checks` |
| `system/solr-buggy-detect` | `system/solr` plus the old Solr bugs put back |
| `system/hbase` | the HBase group (§H; pushed 2026-10-22), from `system/solr`; tree: the fork `JHSUYU/hbase` `graphchecker/hbase-checks` |
| `system/hbase-buggy-detect` | this branch: `system/hbase` plus HBASE-15039, -20642 and -28533 put back (§B; trees `graphchecker/hbase-bug-<jira>`) |
| `system/zookeeper` | the ZooKeeper group (pushed 2026-10-22; its own STATE §Z), from `system/hbase`; tree: the fork `JHSUYU/zookeeper` `graphchecker/zookeeper-checks` |
| `system/zookeeper-buggy-detect` | `system/zookeeper` plus the old ZooKeeper bugs put back |

The CloudLab branches of 2026-10-24..28 are deleted from the remote; their heads are the tags
`archive/system/{hdfs,hbase,zookeeper,solr}-cloudlab`. Every older remote branch was deleted, bundled first:
`/bigtemp/vnr3ne/handover/2026-10-08/graphchecker-remote-branches.bundle` (`study`, `hdfs-compose-perf-wip`,
`hdfs-container-writers`; `git fetch <bundle> 'refs/remotes/origin/*:refs/remotes/bundle/*'` gets them back). The
study's data moved to `docs/checks/` (`study.txt`, `SELECTION.md`, `new-bugs.txt`). Parked local work is kept as tags
`archive/local/<branch>` in `~/GraphChecker` (not pushed; the branches themselves were deleted on 2026-10-28):

| tag `archive/local/...` | head | state |
| --- | --- | --- |
| `hbase-e15` | `7940b6d09` | the client thread's happens-before through procedures (TODO HBase 15), with the tree branch `gc/hb-e15` (231d8c7246, `/u/vnr3ne/hbase`); not merged |
| `hbase-startup` | `3afb27f13` | HBase #14; two design questions (TODO HBase) |
| `hb-schedule`, `hb-sync` | `1fb4a475a`, `53f16e8b6` | one per-session happens-before relation; reviewed |
| `hdfs1-prefix-span`, `hdfs-rule1`, `hdfs-u18-fix` | `40127e2b5`, `7d2819214`, `8ed56ddeb` | not for merge: the merged-span prefix (superseded by TODO HDFS §3's design), rule 1 and the own-fault key (missed the throughput bar, open defect 51) |
| `solr-bug-reindex` | `12283e3f1` | Solr #04 and Solr replay fidelity; SBR26 13/14 (solr-18413 regressed) |
| `solr-growshape` | `727d48ea5` | GROW rows carrying their shape (TODO "Engine items found on Solr" 3); gated, not merged |
| `solr-explore`, `solr-parplan`, `solr-shard` | `b0e712ceb`, `3df494a3a`, `d3b663462` | the generational bound D2 (unsound as reviewed) and session sharding (shelved) |
| `wire-codec-p1` | `3e9cb3182` | WIRE-CODEC (TODO "Cross-cutting") |

## 3. System trees, VM images, snapshots

| tree | branch | used by |
| --- | --- | --- |
| `/u/vnr3ne/hbase` (local branch `gc/hbase-checks` `b5d5cc6a20`) | `graphchecker/hbase-checks` on the fork `JHSUYU/hbase` | THE HBase tree of every `system/hbase` case (REPRODUCE §7 clones it; §H); the final tree set `/bigtemp/vnr3ne/wt/hb-int-trees-6/hbase-checks` (Maven repository `/bigtemp/vnr3ne/m2/hbase-int6`) |
| `graphchecker/hbase-bug-{15039,20642,28533}` on the same fork | one old HBase bug put back on `graphchecker/hbase-checks` each | `system/hbase-buggy-detect`'s cases |
| the HDFS, Solr and ZooKeeper trees | the forks' `graphchecker/*` branches (README) | their systems' branches; each branch's STATE §3 and `experiments/<sys>/trees.tsv` |

VM images: `/bigtemp/vnr3ne/vm-force12/j2sdk-image` (built from this branch's VM sources; HBase and `system/hdfs-liftlab`),
`vm-force10` (`system/solr`), `vm-force13` (`system/zookeeper`), `vm-hg5` (the former HDFS bodies `system/hdfs`,
`system/hdfs1`), `vm-model-guards2` (`main`); each with its `SOURCE.txt` and `smoke.log`. The VM's dead natives
(VM.md §8) and `exportLeaf`/`mintLeaf` can go in the next VM build.

Snapshots in `~/gc-run/` (frozen; `tools/rounds/snapshot-gc.sh` refuses one in use): HBase's final series ran on
`hb-int-16` (319428f7d) and `hb-int-17` (e53c3c882); this branch's series B1 runs `bd-hbase-1` (b978bacb8).

## 4. Where the analyses and evidence live

- `docs/checks/` (in the repo): the selection, the per-system point tables, the verified bugs.
- HBase: `/bigtemp/vnr3ne/analysis/hbase-2026-10-19/` (the first session's briefs, gates and offline tools) and
  `hbase-2026-10-20/` (the second session's and the final series', §H "Where things are"); run outputs
  `/bigtemp/vnr3ne/gc-out/hbase-final` and `hbase-fresh` (the fresh-clone check).
- `/bigtemp/vnr3ne/handover/`: bundles of deleted branches (`2026-10-08/`: the remote branches of §2 and the Hadoop
  fork's older `gc/*` branches, `hadoop-gc-branches.bundle`; older dated bundles), WIP patches of stopped agents.
- Older: `/bigtemp/vnr3ne/analysis/study-2026-10-04/`, `study-2026-10-05/`, `study-2026-10-06b/`, `excl-2026-10-07/`,
  `cleanup-2026-10-08/`, `/bigtemp/vnr3ne/specs/` (proposals cited by code comments), `~/bug_study/`.
