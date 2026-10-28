# State: HDFS finished; Solr ended; HBase finished; ZooKeeper finished (2026-10-22)

ZooKeeper: section Z below (the latest work). HBase: section H. Solr: section S. The HDFS group is finished: all 46 cases have an exported `.smt` read by hand against the HDFS code, one row each in
[../STATUS.md](../STATUS.md) "HDFS checks" (07, the last, closed on 2026-10-07: EX1-adhoc-07e on `system/hdfs1`
8c446418b). Every case then ran alone on the ten lifts for its time breakdown (series EX1,
`/bigtemp/vnr3ne/gc-out/hdfs-excl`; the 46 rows are [../design/PERFORMANCE.md](../design/PERFORMANCE.md) §6). The owner
then stopped the work; on 2026-10-08 the code, scripts and documents were cleaned ("清理所有无用的文档/死代码/没用的脚本
fallback") and the remotes cut down to what is kept (§2, §3). Nothing runs on any lift and no agent is working. Read this
file, then [TODO.md](TODO.md) (what is left, in order), [RULES.md](RULES.md), [CHECKING.md](CHECKING.md),
[AGENTS.md](AGENTS.md), [OPERATIONS.md](OPERATIONS.md) and [PARALLEL.md](PARALLEL.md). The design is in
[../design/](../design/README.md); every check's state is in [../checks/README.md](../checks/README.md); done / partial /
missing per requirement in [../STATUS.md](../STATUS.md).

## Z. ZooKeeper (finished 2026-10-22: the final series on integrations 12-13) -- read this first if you take over ZooKeeper

The 2026-10-21 session had two parts. The day session (a lead and the read-only agents Z1, Z2) prepared the checks. The
evening session (a lead and five coding agents) built and ran them:
- **A:** the tree, the client-level cases, ClaimPolicy own-run-first, the CONFIRM hold at the first instrumented serve.
- **B:** the quorum-bug workloads, 5094 and 5088.
- **C:** the automatic quorum cluster, the session expirer, election idle polls, the leader's ACK queue.
- **D:** the learner-stream door, self-ACK, the seeded-Random rule, region-exit claim closing, D5 txn headers.
- **E:** the VM's failed-CAS comparand, queue item identity, native standing occurrences, CONFIRM/COMPOSE moved roots,
  GROW's exposed tasks, the mint lookup.

The work was merged in integrations 6-13, each a snapshot of `system/zookeeper` paired with a tree set of
`gc/zk-checks` (16/16 natives each), then the final series ran (`results/zookeeper/`). START-HERE.md is the takeover
document; lead/RUNS.txt is the full log of runs and decisions.

**GraphChecker.**
- `system/zookeeper` (pushed to GitHub 2026-10-22, owner; worktree `/bigtemp/vnr3ne/wt/gc-zookeeper`): the code. A fresh
  clone of it and of the fork's `graphchecker/zookeeper-checks` (the adapter) runs every case (REPRODUCE §8). It is
  `system/hbase` 5b4b6bae9 plus:
  - `experiments/zookeeper/` (HBase's layout; per-case settings in `zk-bugs/case.sh`, `zk-adhoc/checks.tsv` + `case.sh`,
    `workflow.properties`; `doors.jsonl` with the ZK_QUORUM and ZK_SNAPSHOT rows);
  - the engine and VM changes each STATUS row and PIPELINE/IDENTITY section names;
  - `docs/checks/ZOOKEEPER.md` §E, and STATUS "ZooKeeper checks" and "Per-system surface" (ZooKeeper column).
- The agents' branches `zk-tree` (A), `zk-qwork` (B; c19d30112 is 5094's world depth 1), `zk-quorum` (C), `zk-learner`
  (D) and `zk-engine` (E) are merged (git log has each merge); the branches and their worktrees are deleted.
- The old bugs put back on this engine (ZOOKEEPER-710, -2886) are the branch `system/zookeeper-buggy-detect`.

**The tree.** The fork https://github.com/JHSUYU/zookeeper.
- Its master eab165995 is the buggy base; PR 2459's and PR 2454's fixes are its branches `fix-trunc-sync-shutdown-state`
  and `fix/observer-master-pending-proposals`.
- `graphchecker/zookeeper-checks` = local `gc/zk-checks` (`/u/vnr3ne/zookeeper`), pushed after each integration: the
  final series ran on 51b213562 (`gc/zk-hostseed`, the RO client's constant host seed for 04 and 13, on the final
  `gc/zk-checks` 2b6e17bf8). It holds the adapter, the markers, the workloads and the tree workarounds (STATUS
  "Per-system surface"). The fork's branch has since moved to 889f0e96 (2026-10-25: 7aa086bb `QuorumBase` starts its
  peers from the highest id down, 07a2f0df/889f0e96 a workload's wait of `CONNECTION_TIMEOUT` or more for a server never
  times out), the base of the buggy-detect trees `graphchecker/zk-bug-<jira>`; the local `gc/zk-checks` stays at 51b213562.
- The agents' tree branches are merged into it: `gc/zk-tree` (A), `gc/zk-tree-contfb` (A, container-reuse's fallback),
  `gc/zk-quorum-bugs` (B), `gc/zk-quorum` (C) and `gc/zk-learner` (D). `gc/zk-unified` and `gc/zk-unified-hb` are the
  old branch-3.9 trees.
- Maven repositories: `/bigtemp/vnr3ne/m2/zookeeper-int11`, `-int12` (the final tree sets'); the other integrations' and
  the agents' are deleted.

**Snapshots, images, tree sets.**
- Snapshots: `/u/vnr3ne/gc-run/zk-int-12` (d4fbcd97c) and `zk-int-13` (d73c28302 = the final engine, D's COMPOSE fix on
  12); the earlier integrations' (6 797c9d5ad, 7 b18c7a484, 8 494d2a9af, 9 c01b741ac, 10 ac69ab4b1, 11 8524ead2f) and the
  agents' are deleted.
- Tree sets: `/bigtemp/vnr3ne/wt/zk-int-trees-11` (2b6e17bf8) and `zk-int-trees-12` (51b213562, for 04 and 13), the
  final series'. Never rebuild one a run reads.
- Image: `/bigtemp/vnr3ne/vm-force13/j2sdk-image` = vm-force12 plus the failed-CAS comparand (OPERATIONS.md images row).
  Every run from integration 9 on uses it.

**Runs.**
- `/bigtemp/vnr3ne/gc-out/zookeeper-final`: the series. F0/F0B are the selector seeds. F1B/F1S/F1C/F1D/F1E/F1F ran concurrently. F2B/F2S ran alone. lead/final/PLAN.md §5 lists them.
- `/bigtemp/vnr3ne/gc-out/zookeeper-fresh`: the fresh-clone check (REPRODUCE §8). The agents' runs (tags
  ZA*/ZB*/ZC*/ZD*/ZE*, which STATUS and TODO cite) are deleted; lead/RUNS.txt records each.

**Evidence.** `/bigtemp/vnr3ne/analysis/zookeeper-2026-10-21/`:
- `lead/RUNS.txt`: every run, decision and owner ruling;
- `lead/readings.md`;
- `lead/final/` (PLAN.md, the series drivers, README-draft.md);
- the agents' briefs (`lead/*.txt`), the gate and integration-build logs;
- Z1/Z2's reports and native logs.

## H. HBase (finished: final series 2026-10-21) -- read this first if you take over HBase

The owner's goal: "基于我们solr现在这么好的代码基础，完成对hbase的adhod check" (RULES "HBase: the goal and its scope").
The first session (2026-10-19, a lead and five coding agents) built the HBase platform on `system/solr`'s engine; the owner
stopped it for a handover at 23:10. The second session (2026-10-19 23:40 to 2026-10-20, a new lead and five agents: H1
platform, H2 ZooKeeper, H3 RPC, H4 checks, H5 engine analysis) took over from START-HERE and ran every case of
`experiments/hbase/hbase-cases.tsv`. **All five of the owner's bugs PASS.** Read `system/hbase`'s START-HERE (HBase's
takeover file), then [TODO.md](TODO.md) "HBase", then LESSONS §9.

**`system/hbase`** (the code; pushed to GitHub 2026-10-22, owner; = `hbase-int`; worktrees `/bigtemp/vnr3ne/wt/gc-hbase` and
`/bigtemp/vnr3ne/wt/gc-hbase-merge`, the latter for merges and gates on lift11): `system/solr`'s engine plus the first
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
`/bigtemp/vnr3ne/gc-out/hbase-final` and `hbase-fresh` (the development runs are deleted);
the final snapshots `/u/vnr3ne/gc-run/hb-int-16` (319428f7d) and `hb-int-17` (e53c3c882); the final tree set
`/bigtemp/vnr3ne/wt/hb-int-trees-6` (b5d5cc6a20, Maven repository `/bigtemp/vnr3ne/m2/hbase-int6`); the image
`/bigtemp/vnr3ne/vm-force12`. The parked happens-before work (TODO HBase 15) is the tag `archive/local/hbase-e15` (7940b6d09, not merged) and
tree branch `gc/hb-e15` (231d8c7246).

## S. Solr after the final round SGF9 (2026-10-19) -- read this first if you take over Solr

The owner stopped the 2026-10-18 final round to rewrite the engine's bottlenecks (workstreams A-H: data representation, the holding composer, the
scheduler, the exploration core, replay and VM, serial fixed cost, NFS, cleanup); the
rewrite was merged into `system/solr` and the final round SGF9 ran the 12 study checks, each alone on lift02-10 +
lift12-15, at world depth 0, on VM `vm-force10` and the tree set `sg3j-trees`. The owner ended it on 2026-10-19 and had
everything gathered on `system/solr`, pushed with the fork's tree, and documented ("剩余的case我们不跑了，不要了"). Nothing
runs on any lift. Read `system/solr`'s START-HERE (Solr's takeover file) first, then [TODO.md](TODO.md) "Solr: after SGF9".

**`system/solr`** (GitHub `JHSUYU/GraphChecker`, pushed 2026-10-19; = `solr-int`, worktrees
`/bigtemp/vnr3ne/wt/gc-solr`, `/bigtemp/vnr3ne/wt/gc-solr-merge`) holds, gated: the compaction of the corpus and walk
state; the holding composer (every session's rows held until a sweep finds the old generation past 60 %, let go before
the body is lowered); the GROW pipeline (a GROW re-run holds the fixed point until it lands: OPTIMIZATIONS 1.37
reverted); the superstep + window walk; the parallel round and Frontier; the stream scheduler (replays spread by room,
multi-question solvers, z3 answers reused by query text, the served planner charged its heap's footprint: 1.36
reverted); the VM's one-channel read-out with parallel record decode and the replay's stop at its window close; the
replay need from the 90th percentile of peaks with an out-of-heap rerun; SEED's serial speedups; gzip rows through one
opener (old plain run dirs must be GzCopy'd); EMIT's gap ledger in Java; the nearest world for every sort; the z3 pairs
of the decide re-asked at twice their slot after a memout while a host holds it. Its VM sources are under
`third_party/` (image `/bigtemp/vnr3ne/vm-force10/j2sdk-image`, built from this branch; the runtime refuses an older
image by name). Not merged (tags `archive/local/<branch>`): session sharding (solr-parplan, solr-shard: shelved), the generational bound D2
(solr-explore a2bd510cb: unsound as reviewed), GROW rows carrying their shape (solr-growshape 727d48ea5: gated, its
read-out cost unmeasured; TODO).

**The tree:** the fork `https://github.com/JHSUYU/solr.git` branch `graphchecker/solr-checks` = local
`gc/solr-zktrace2` 12d23091d1 (2026-10-16; `/u/vnr3ne/lucene-solr-8_11`, worktree set `/bigtemp/vnr3ne/wt/sg3j-trees`):
Solr `branch_8_11` with the adapter, every case's target marker and the bug checks' workloads. No Solr source changed
after it.

**Results** (STATUS "Solr checks" has each case's row; times `analysis/solr-2026-10-14/final-stats.py SGF9`):

| case | SGF9 snapshot | result | wall (s) | seeding / exploration / compose+solver |
| --- | --- | --- | --- | --- |
| solr-adhoc-38 | sgf9e baa62b2d6 | SAT MARKER_FLIPPED, confirmed in the VM, native 0/10 (as SGF7) | 922 | 335 / 226 / 10 (+344 CONFIRM, REPRODUCE) |
| solr-adhoc-21 | sgf9 495d754b5 | UNSAT_CLOSED, 18 paths | 994 | 340 / 618 / 23 |
| solr-adhoc-39 | sgf9e | UNSAT_CLOSED, 8 paths (SGF8 57: the re-runs' round never ran) | 1200 | 501 / 672 / 17 |
| solr-adhoc-09 | sgf9c 662745589 | formula UNSAT at FIXED_POINT, 1 BLOCKING (truncated closure) | 1417 | 356 / 886 / 135 |
| solr-adhoc-13 | sgf9b f3032afa4 | formula UNSAT at FIXED_POINT, 1 BLOCKING (truncated closure), 127 paths | 1762 | 508 / 922 / 296 |
| solr-adhoc-19 | sgf9c | formula UNSAT at FIXED_POINT, 2 of 44 paths composed (unplaced clock cells) | 2672 | 411 / 1991 / 164 |
| solr-adhoc-10 | sgf9c | formula UNSAT at FIXED_POINT, 1 BLOCKING (truncated closure), 370 paths | 5532 | 734 / 4430 / 277 |
| solr-adhoc-40 | sgf9c | formula UNSAT at FIXED_POINT, 4 BLOCKING, 315 paths | 8731 | 715 / 5673 / 2209 |
| solr-adhoc-05 | sgf9d 19fe33ff0 | MISSING: budget in DECIDE (340/340 paths composed, every z3 memout); re-decided offline with the slot fix: NO_SUPPORTED_WITNESS, 340 unsat, 22 at the path limit | 14400 | 807 / 10701 / ~2880 |
| solr-adhoc-14, -07, -31 | not rerun (owner) | SGF8 evidence: 14 SGF8OOM, 07 1 of 309 composed (offline 309/309 UNSAT_CLOSED), 31 SGF9KILLED at round 26 | | |

Against SGF7/SGF8 the rewritten engine is faster on every case it finished (21 2363 -> 994 s, 13 3076 -> 1762, 09
6887 -> 1417, 19 6752 -> 2672 and to its fixed point instead of the budget, 10 7660 -> 5532 and to its fixed point instead
of PLANNER_HEAP_EXCEEDED, 40 no claim -> 8731 s, 38 1222 -> 922). Fewer paths in 39 (and re-run sessions unplanned in 19,
13, 09) came from the fixed point beside GROW re-runs, fixed after those runs.

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

The remote keeps two branches per system (README "The branches"):

| remote branch | what it is |
| --- | --- |
| `main` (default) | the 2026-10-03 body (round V25, 14/14 on the named HDFS, Solr and ZooKeeper cases; VM `vm-model-guards2`, HDFS tree `gc/hdfs-unified-dtx`) |
| `system/hdfs-liftlab` | every HDFS case on `system/hbase`'s engine (2026-10-27); replaces `system/hdfs` (the locked body, 39 cases, §0) and `system/hdfs1` (the other 7, §0), which stay on origin as history |
| `system/solr` | the Solr group (§S; pushed 2026-10-19), from `system/hdfs1`; tree: the fork `JHSUYU/solr` `graphchecker/solr-checks` |
| `system/hbase` | the HBase group (§H; pushed 2026-10-22), from `system/solr`; tree: the fork `JHSUYU/hbase` `graphchecker/hbase-checks` |
| `system/zookeeper` | the ZooKeeper group (§Z; pushed 2026-10-22), from `system/hbase`; tree: the fork `JHSUYU/zookeeper` `graphchecker/zookeeper-checks` |
| `system/<x>-buggy-detect` (x = hdfs, hbase, zookeeper, solr) | `system/<x>` plus the old bugs put back on that system's tree, one case each, and their engine support (`docs/handover/BUGGY-DETECT.md` there); trees: the forks' `graphchecker/<x>-bug-<jira>` |

The CloudLab branches `system/<x>-cloudlab` are deleted; their heads are the tags `archive/system/<x>-cloudlab`.

Every other remote branch was deleted, bundled first: `/bigtemp/vnr3ne/handover/2026-10-08/graphchecker-remote-branches.bundle`
(`study`, `hdfs-compose-perf-wip`, `hdfs-container-writers`; `git fetch <bundle> 'refs/remotes/origin/*:refs/remotes/bundle/*'`
gets them back). The study's data moved to `docs/checks/` (`study.txt`, `SELECTION.md`, `new-bugs.txt`). The local
branches that held parked, unmerged work are kept as tags `archive/local/<branch>` (2026-10-28; the merged local
branches are deleted, `hdfs1-confirm-first` among them: merged into `system/solr` 2026-10-08):

| tag `archive/local/...` | state |
| --- | --- |
| `hdfs1-prefix-span`, `hdfs-rule1`, `hdfs-u18-fix` | not for merge: the merged-span prefix (superseded by TODO HDFS §3's design), rule 1 and the own-fault key (missed the throughput bar, open defect 51) |
| `solr-bug-reindex` | Solr #04 and Solr replay fidelity; SBR26 13/14 (solr-18413 regressed) |
| `hb-schedule` + `hb-sync` | one per-session happens-before relation; reviewed, not merged |
| `hbase-startup` | HBase #14; two design questions (TODO HBase) |
| `hbase-e15` | the client thread's happens-before as JOIN rows (TODO HBase 15), not merged |
| `solr-growshape`, `solr-explore`, `solr-parplan`, `solr-shard` | GROW rows carrying their shape (TODO Solr 3); the generational bound D2 (unsound as reviewed); session sharding (shelved) |
| `wire-codec-p1` | WIRE-CODEC; superseded for HDFS by codec capture |

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
| `/bigtemp/vnr3ne/wt/sg3j-trees/lucene-solr-checks` (worktree of `~/lucene-solr-8_11`) | `gc/solr-zktrace2` `12d23091d1` | `graphchecker/solr-checks` on the fork `JHSUYU/solr` (pushed 2026-10-16, unchanged since) | THE Solr tree of every `system/solr` case since SGF8 (SGF8, SGF9; REPRODUCE §6 clones it); its history is the local branches `gc/solr-checks`, `gc/solr-bugs`, `gc/solr-body`, `gc/solr-zk-next`, `gc/solr-zk-doors`, `gc/solr-zk2` of `~/lucene-solr-8_11` (their worktrees are deleted) |
| `/bigtemp/vnr3ne/wt/lucene-solr-storing` | `gc/solr-unified-storing` `04f8489` | none | solr-18406, solr-18413 (`main`) |
| `/u/vnr3ne/hbase` | `gc/hbase-checks` `b5d5cc6a20` | `graphchecker/hbase-checks` on the fork `JHSUYU/hbase` | THE HBase tree of every `system/hbase` case (REPRODUCE §7 clones it; STATE §H) |
| `/u/vnr3ne/zookeeper` | `gc/zk-checks` `51b213562` | `graphchecker/zookeeper-checks` on the fork `JHSUYU/zookeeper` | THE ZooKeeper tree of every `system/zookeeper` case (REPRODUCE §8 clones it; STATE §Z; the final series' tree sets `/bigtemp/vnr3ne/wt/zk-int-trees-11`, `-12`) |
| `$GC_TREES/zookeeper-bug-710`, `zookeeper-bug-2886` (made by `prepare-trees.sh` on `system/zookeeper-buggy-detect`) | none (clones of the fork) | `graphchecker/zk-bug-710`, `graphchecker/zk-bug-2886` (and their `-control` branches, the fixed code) | the buggy-detect cases `zk-buggy-710`, `zk-buggy-2886` (that branch's `BUGGY-DETECT.md`) |
| `/bigtemp/vnr3ne/wt/zookeeper-unified`, `zookeeper-hb` | `gc/zk-unified` `8f18cf3a4`, `gc/zk-unified-hb` `47ddc8b36` | none (never push: apache remote) | the zk-bugs cases (`main`) |

The fork's 16 older `gc/*` branches (the per-bug trees, `gc/hdfs-unified`, `gc/hdfs-unified-dtx`, `gc/hdfs-bugs`,
`gc/hdfs-study-r5`/`r6`, `gc/hdfs-11741`/`-r5`) were deleted, bundled first in
`/bigtemp/vnr3ne/handover/2026-10-08/hadoop-gc-branches.bundle`; `main`'s cases read `gc/hdfs-unified-dtx`
(`/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx`, local). Any other Hadoop worktree under `/bigtemp/vnr3ne/wt/` is superseded.
The fork's `graphchecker/hdfs-checks` (899c200cc8e) and `graphchecker/hdfs-checks-adhoc21` (25b4f1e531f) have moved
past the local heads above (the HDFS work of 2026-10-24 on; `system/hdfs-liftlab` documents the trees it runs).

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
