# GraphChecker

GraphChecker is an academic research tool in software engineering. It studies how open-source
distributed Java systems (HDFS, Solr, ZooKeeper) fail under fault, clock and ordering counterfactuals.

It starts from one recorded run of a system's own cluster test that does **not** fail, plus one
declared failure site (a `throw`, named by its class and source line). It then asks whether a
small change could have made that run fail at that site, and it answers with a witness. The
changes it considers are a transport fault, a skewed clock, a flipped configuration value, or a
different pairing of a message or of shared state.

A witness is a quantifier-free SMT formula (`candidate.smt2`), a claim naming what moved
(`claim.json`), and one replay confirming that the program agrees (`confirm.json`). Replays run
on a concolic OpenJDK 8 (Zero) that keeps a symbolic expression under every value. The formula
is composed from many focused replays, and the solver picks the nearest world. What the rows do
not state is refused by name, never defaulted.

**If you are taking over this project, read §0–§3 first, in order.** They say where the work
stands, which branches are in flight, what to do next, the owner's standing rules, how to run
agents in parallel, and how the servers and tools work. The capability inventory (done / partial
/ not done per requirement) is [docs/STATUS.md](docs/STATUS.md); the design of the code on
`main` is [docs/design/](docs/design/README.md).

---------------------------------------------------------------------------------------------------

## 0. State (2026-10-03 morning; a lead session with four coding agents is live)

The 2026-10-02 night session's handover (uncommitted diffs under `/bigtemp/vnr3ne/handover/`) was taken up by
a new lead session, which works the owner's 2026-10-02 goal (§0.1) with four coding agents (§0.4). Read
§0.1-§0.6 in order, then §1-§3.

### 0.1 The goal (verbatim) and the owner's rulings since

The owner's active goal, verbatim (2026-10-02):

> 这是一个软件工程的学术项目，研究开源系统的稳定性。我是做system reliability研究的。请你设为长期记忆。请你阅读readme.md。理解当前的任务进度，并完成它。按照readme文档里建议的工作方式来进行。完成里面的todo。这个todo有一个不同，solr, hdfs里的adhoc check。请你去阅读～/bug_study下solr, hdfs的bug描述。相信你阅读完具体仓库的代码，你会很清楚我们在解决什么样的问题。如果solr, hdfs的文档里。请你选出里面确实是真实的，adhoc coordiaotin的bug（你要去system source code确认）。然后如果有，拿他们替换solr, hdfs里现在的adhoc check large scale。同理，请你clone hbase和zookeeper。在bug_study下的.txt找到hbase, zookeepr的高质量，并且优先选择在我们工具能力范围之内。能比较方便detect到的作为hbase, zookeepr的adhoc check。跑出因果链正确的.smt。 detect到他们。hbase和zookeeper也要像solr, hdfs一样。在一个branch里插入annotation。检查多个adhod check。请你先阅读graphchecker的完整代码，了解细节。你的整体设计要general，简洁。不要让代码变得过于臃肿

In short: finish the TODO below the README way; the ad-hoc checks of HDFS and Solr are REPLACED by real
ad hoc coordination bugs from `~/bug_study/{HDFS,Solr}.txt` (each verified in the system's source); HBase and
ZooKeeper become systems 3 and 4, each with ONE tree branch carrying the adapter, the bugs' target markers
(`@CausynthExceptionTarget`) and the workloads; each check ends in a causally correct `.smt` that is SAT (a
witness), its chain checked by hand against the system's code.

The owner's rulings of the same evening (binding; also in §1):
1. **Symbolic scope is the top priority** ("但是我们要实现symbolic scope啊？就是自动囊括进来更多的symbolized
   variable。我允许你根据具体case做一些小调整。这是最高优先级，先实现这个"). Moderate and bug-driven ("适度支持吧。
   只要能包括进来一些更优质的coordination bug即可…bug确实高质量…但是因为我们symbolic scope支持的不够。那你的symbolic
   scope就要改进了"): when a high-quality coordination bug is out of reach only because the scope is too narrow,
   widen the scope GENERALLY for it. All three kinds of widening are in bounds: configuration values (startup
   and run-time reconfiguration, String/enum too), shared-state re-pairing (STATE/MESSAGE pairing, more
   containers), and request arguments -- but prefer the first two (the third finds input validation bugs).
2. **The large-scale ad-hoc discovery pipeline is deleted** (owner chose "删除"): `tools/adhoc` discovery and
   selection (sites, workloads, coverage, reach, select, targets, slice, score, cover, prescreen, buildkey,
   batch, nightly, funnel), `run_engine.sh`'s batch campaign, `plan.PlanUnion`, the 155/127 sweep checks, the
   20+20 pick lists. Kept: `sweep.sh` (a list of case ids, one campaign each), `fanout.sh`, `triage.py`,
   `findings.py`, `tools/lib/annotated.py`. Done on branch `retire-adhoc-pipeline` (§0.4).
3. **A self-written cluster test may be a bug's workload** when the bug is truly high quality ("如果这个bug本身
   真的非常高质量。我允许你自己一个cluster based unit test for it…当然，bug质量要是不高就算了").
4. **IO rule**: a bug whose causal chain crosses file or HDFS-namespace state (where symbolic propagation stops)
   is not forced ("我怕有些牵扯到io，会让我们的符号传播挂掉。如果是这样的话，就不强求"); RPC and ZooKeeper chains are
   fine, and HBase/ZooKeeper may need their protocol headers extended to carry the causal context, as HDFS's
   `RpcHeader.proto` does ("hbase/zookeepr你可能也要修改communication protocol的header").
5. **Acceptance per bug**: the tool exports a reasonable `.smt` and z3 finds it SAT ("这些bug你要看能不能让我们的tool
   导出合理的.smt，然后check发现sat"), the claim's mechanism is the bug's, CONFIRM confirms, and the chain is
   checked by hand.
6. Clean up everything unused (code, artifacts, docs) as you go (owner: "优先清理所有不用的代码，产物，文档").

The previous goal (Phase 1: correct `.smt` for the 11 named cases -- done; Phase 2: 20 hand-picked ad-hoc
checks per system) is superseded by this one; Phase 1's eleven cases stay the regression baseline.

### 0.2 Where things stand

- **main** (local; `origin/main` = `4027318f5`; push only when the owner asks) = this commit: the V9 main plus,
  one large change per live round, `symbolic-scope` (V10 11/11, V11), `system-zookeeper` + the recorded-address
  identity rule (V12, V13), `vm-streams` (V14 12/12, VM `vm-streams2`), `retire-adhoc-pipeline` (V15),
  `seed-functional` (V16 + V16b 12/12, snapshot `~/gc-run/p229`), `preWindow-loop-root` (V17 12/12, snapshot
  `~/gc-run/p230`), `zk-election-offer` (V18 13/13, snapshot `~/gc-run/p231`; hdfs-11741 on its rerun V18b: the first run
  met the 11741 balancer race) `pairing-port` (the race fixed, DataTransfer doors, the eight named HDFS cases on the
  dtx tree; rounds PP1 + PP1b 13/13 and 11741 twice, snapshot `~/gc-run/pp1`) and `vm-model-guards` (V19 13/13,
  snapshot `~/gc-run/p232`, VM `vm-model-guards2`). The thirteen regression cases are the eleven named ones plus
  `zk-bugs-quota-init` and `zk-bugs-election-offer`. The HDFS
  RPC-fault cases move either direction of one IPC door from round to round (`Client$Connection#sendRpcRequest`
  or `Client#getRpcResponse`, the target DataNode's heartbeat request or response lost): the same chain, valid
  under the mechanism mandate.
- **VM**: main's is `/bigtemp/vnr3ne/vm-model-guards2/j2sdk-image` (round V19; vm-streams2 + the model guards); `vm-w4h` serves older rounds; `vm-w4i`,
  `vm-nr41` kept for the parked branches of §0.4.
- **Trees** (never rebuild one a run reads; each new tree builds with its own Maven repo `/bigtemp/vnr3ne/m2/<name>`):

| tree (worktree) | branch, head | of | what |
| --- | --- | --- | --- |
| `~/hadoop-hdfs-unified` | `gc/hdfs-unified` `89f4c5348df` | `~/hadoop` | the base of the dtx and bugs trees; the eight named HDFS cases ran here until `pairing-port` merged |
| `~/hadoop-hdfs-11741` | `gc/hdfs-11741` | `~/hadoop` | hdfs-11741 (unchanged) |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` | `gc/hdfs-unified-dtx` `51f1e058380` | `~/hadoop` | the eight named HDFS cases (since `pairing-port`, rounds PP1/PP1b): `gc/hdfs-unified` + the DataTransfer op's envelope (two adapter commits), Maven repo `/bigtemp/vnr3ne/wt/dtx/m2` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-bugs` | `gc/hdfs-bugs` `89f4c5348df` + WIP | `~/hadoop` | HDFS bug_study #15 (§0.3); its last commit is a SCAFFOLD ("BlockReceiver's close tolerates a removed replica", to be replaced); uncommitted: the target marker in `RoundRobinVolumeChoosingPolicy` and the workload `TestCausynthSlowDiskZeroMax` (`handover/tree-gc-hdfs-bugs-wip.patch`) |
| `/bigtemp/vnr3ne/wt/lucene-solr-storing` | `gc/solr-unified-storing` `663e0ef` | `~/lucene-solr-8_11` | solr-18406, solr-18413 (unchanged) |
| `/bigtemp/vnr3ne/wt/lucene-solr-bugs` | `gc/solr-bugs` `01aa353` | `~/lucene-solr-8_11` | the storing tree + Solr bug_study #04's target marker |
| `/bigtemp/vnr3ne/wt/zookeeper-unified` | `gc/zk-unified` `8f18cf3a4` | `~/zookeeper` (apache/zookeeper, cloned 2026-10-02) | ZooKeeper `branch-3.9` (the newest Java 8 line) + adapter: `CausynthZk` (client requests as messages: `ClientCnxn`, `PrepRequestProcessor`, `FinalRequestProcessor`), `CausynthZkCluster` (automatic ClientBase clusters), the zk-bugs targets, the quota workload `CausynthQuotaRetryTest`; both workloads pass natively |
| `/bigtemp/vnr3ne/wt/hbase-unified` | `gc/hbase-unified` `868dc52c11` | `~/hbase` | `codex/hbase-jdk8-concolic` (HBase master backported to Java 8, 4cf574a957) + adapter `fa92e1b0b8` (`CausynthHBaseCluster` automatic mini cluster; HBase RPC causal context: `RPC.proto` field, `CausynthRpc`, `Call`, `ServerCall`, `CallRunner`) + bug #14's target marker; NOT yet built or run on JDK 8 |

- **Outputs kept**: `/bigtemp/vnr3ne/gc-out/accept-{V14,V16,V16b,V17}-*` (the last rounds of the twelve),
  `evidence/` (the real STATE false positive `fp-commit-gs-state-v75|v77`), `hosts/` (the ledger); the agents'
  runs under `gc-out/{solr-bugs,zk-bugs,hdfs-bugs,slowdisk-dev,hbase-bugs}/`. Snapshots: `~/gc-run/p229` (V16),
  `p230` (V17) and the agents' frozen snapshots of their branches; remove with `tools/rounds/snapshot-gc.sh`
  once not needed.
- **Cleanup done 2026-10-02**: VM images w4e/f/g; the whole home `~/gc-out` (942 old runs); every `/bigtemp`
  round output but V7/V8/V9; `ab/` gate outputs; stale analyses and the ADHOC-INFRA spec; `w5-scratch`; stale
  worktrees under `wt/` and `.claude/worktrees/`; 30 snapshots. 14 obsolete unmerged branches are archived in
  `/bigtemp/vnr3ne/handover/archived-branches-2026-10-02.bundle`.
- **Cleanup done 2026-10-03**: 62 branches deleted (§0.4: 20 merged into main, 25 merged `worktree-agent-*`,
  the 14 archived in the 2026-10-02 bundle, 2 archived in `handover/archived-branches-2026-10-03.bundle`, one
  WIP port) and the clean worktrees of finished agents under `.claude/worktrees/`; the repo-level deletion is
  branch `retire-adhoc-pipeline`.

### 0.3 The bug_study verdict: 60 bugs, what qualifies

Four read-only investigators read every bug against the source (HDFS on `~/hadoop-hdfs-unified`, Solr on 8.11,
HBase on master/`branch-2.6`/the Java 8 backport, ZooKeeper on master/`branch-3.9`); the lead then read the
code of every pick himself. All 60 defects are real in the studied versions except Solr #10 (absent in 8.11),
ZooKeeper #14 (master only) and HBase #13 (not in 2.6). What qualifies is the intersection of: a real ad hoc
coordination bug, high quality, a chain that stays in memory (IO rule), and a single counterfactual GraphChecker
can plant (a door fault, a clock, a configuration value, a re-pairing) from a run of a passing cluster test.

**Picks** (case ids = `<experiment>-<arg>`; each tree marks the throw with that id):

| case id | bug | fatal throw | counterfactual | workload | needs | state |
| --- | --- | --- | --- | --- | --- | --- |
| `zk-bugs-quota-init` | ZooKeeper #01: `SetQuotaCommand.createQuota` creates the limit znode, then the stat znode, in two requests; a lost reply of the limit create leaves no stat, the retry takes the update branch and `getData(statPath)` hits NoNode; meanwhile `ZooKeeperServer.checkQuota` sees no stat, logs "should not happen" and returns: the hard quota is silently off | server NoNode guard (`FinalRequestProcessor` handleGetDataRequest, ~:692 on 3.9; the tree marks the one the agent chose) | ZOOKEEPER WRITE door fault on the limit `create` (catalog door: the write happened, the client sees ConnectionLoss) | `CausynthQuotaRetryTest` (self-written: set a hard quota retrying on ConnectionLoss, then raise it) | client->server causal context (done in the tree), a campaign | PASS (round ZK8; a regression case since V12): MARKER_FLIPPED, confirmed, chain checked by hand |
| `zk-bugs-election-offer` | ZooKeeper #05: `LeaderElectionSupport.determineElectionStatus` lists offers then `getData`s each; a competitor's concurrent `stop()` delete makes it NoNode; `start()` goes FAILED and never deletes its own committed offer, which blocks every later candidate | the same server NoNode guard, reached by `toLeaderOffers`'s getData (LES ~:310) | STATE re-pairing of the server's node lookup with the competitor's delete | `LeaderElectionSupportTest#testOfferShuffle` (or `#testNodes3`) | the serving-thread concurrency rule (below); STATE pairing end to end | PASS (EO6, EO7; round V18 on main): STATE_PAIRING_FLIPPED, confirmed, chain checked by hand -- the first confirmed STATE witness; a regression case since V18 |
| `solr-bugs-reindex-cleanup` | Solr #04 on 8.11: a same-target REINDEXCOLLECTION creates its own alias `X -> .rx_X_n` (RCC ~:444); any failure after it runs `cleanup` (RCC ~:773), whose DELETE of the target throws in `DeleteCollectionCmd.checkAliasReference` (~:245) on that alias; cleanup has no try/catch, so the source's read-only reset (RCC ~:810-815) never runs: the source stays read-only | DCC ~:245 `SolrException` "is part of aliases" | one SolrJ HTTP or ZooKeeper door fault after the alias step (e.g. the checkpoint DELETE's UNLOAD response, RCC ~:466-468) | `ReindexCollectionTest#testSameTargetReindexing` (2 nodes) | nothing new | branch `solr-bug-reindex`, SB11 stopped in EXPLORE with no verdict: every obligation replay ran the whole 26-min test; a replay whose question closed is to conclude (in progress) |
| `hdfs-bugs-slowdisk-zero` | HDFS #15: `DataNodeDiskMetrics`'s detector replaces `slowDisksToExclude` only `if (maxSlowDisksToExclude > 0)` (~:151); setting the documented "disabled" value 0 by run-time reconfiguration never clears a published list; `FsVolumeList` (~:111) filters the only SSD out | `RoundRobinVolumeChoosingPolicy.chooseVolume` `DiskOutOfSpaceException("No more available volumes")` (~:82-83) | STATE re-pairing: one detector iteration reads `maxSlowDisksToExclude` before the reconfiguration (version 0, value 1, between flagging the SSD and the reconfig) and publishes [SSD]; later iterations read 0 and never clear it | `TestCausynthSlowDiskZeroMax` (self-written, WIP in the tree: flag the SSD slow by `addSlowDiskForTesting`, reconfigure 1 -> 0, write an ALL_SSD file) | version-0 writer arm (from `fix-no-root`, in `state-pairing`); STATE pairing end to end | branch `slowdisk-dev` (SD1, SD2): the stream model makes the chooser's guard symbolic; the detector turns' `max > 0` flips wait for the INITIAL arm (`state-pairing` `94e1390fc`, ported onto `zk-election-offer`) and an obligation replay that plants a moved writer choice by ORDER |
| `hbase-bugs-master-active-time` | HBase #14: `HMaster.masterActiveTime = EnvironmentEdgeManager.currentTime()` (~:986) travels with remote procedures; `MasterRpcServices.throwOnOldMaster` (~:2620-2629) refuses a report whose initiating time exceeds the current master's: wall clocks compared across masters as an epoch | `throwOnOldMaster`'s `MasterNotRunningException` | CLOCK: the OLD master's activation clock jumps forward (clock domains move forward only), its value crosses old master -> RS -> new master | `TestSplitWALProcedure#testMasterRestart` or `TestSnapshotVerifyProcedure#testRestartMaster` (3 RS) | the clock rule through an interface delegate (`EnvironmentEdge`, WIP in `system-hbase`), the HBase RPC causal context + derived protobuf ports, masters on distinct node clocks; JDK 8 feasibility | parked (branch `system-hbase`, round HBA1): builds and runs on Java 8; three blockers (§0.4) |

**Second tier** (not a TODO: the owner dropped them 2026-10-03; real, high-quality coordination bugs that need STATE/MESSAGE pairing and a self-written
concurrent workload; take them once the picks' pairing works): ZooKeeper #08 (concurrent `delquota -N/-B`,
read-modify-write with version -1, `ZooKeeperServer` QuotaExceeded), #02 (concurrent parent/child setquota);
Solr #05 (DELETENODE vs count DELETEREPLICA empties a shard), #06 (CREATESNAPSHOT recounts replicas after a
DELETENODE), #02 (CREATEALIAS during DELETE), #12(b) (two MIGRATEs share a temp collection name); HBase #12
(CloneSnapshot rollback deletes another CreateTable's namespace-quota entry); HDFS #07 (SPS queue limit check
outside the write lock; needs a `LinkedList` model in the VM).

**Rejected, by reason**: deterministic API-sequence or argument bugs, no counterfactual to plant (HDFS #01, 02,
03, 06, 08, 13, 14; Solr #11, 13, 14; ZooKeeper #12; HBase #08); need a reconfiguration plus an out-of-band
disk change or a test spy (HDFS #04, 05, 09, 10; HBase #06, 09); chains through file/HDFS-namespace state
(HBase #03 HFile archive rename, #05 DeleteNamespace listing, #11 snapshot HDFS ACL, #10, #15; Solr #01 backup
purge); several flips or a thread schedule at once (HDFS #12, ZooKeeper #04, 11, 13, 15; Solr #15); the throw is
only the fault's echo (ZooKeeper #06 WriteLock: its own comment accepts the behaviour); invalid operator input
only (HDFS #11); contrib REST (ZooKeeper #09, 10); queue parent recreation needing an extra admin action
(ZooKeeper #07); client-tool static flag (HBase #02); string/enum config with a ZooKeeper watch chain (HBase
#04, #07). **HDFS has no pick with today's scope except #15** (which needs the STATE pairing work).

**The serving-thread concurrency rule ZooKeeper #05 needs** (on main since V18: a claimed occurrence's
`threadKey` is the START it claims, and CONFIRM holds an ORDER on claimed work at its submitter's send,
`Confirmation#submitter`): `smt/Arms#concurrent` calls two
occurrences on one thread ordered (`sameThread`). A ZooKeeper server applies every client's request on its
pipeline threads, so a getData and another session's delete are always "ordered", though their order is the
queue's arrival order, a race between two clients. General refinement: for work claimed from a queue or an
executor (IDENTITY.md §6 claims), compare the claims' starters, not the consumer thread: two claimed
occurrences on one consumer thread are concurrent when their starters are; CONFIRM then must hold the queue
submission order (ORDER edges on the submitters).

### 0.4 Branches (heads at 2026-10-03; WIP = uncommitted, saved under `/bigtemp/vnr3ne/handover/`)

`main`: §0.2. Merged and kept for now: `system-zookeeper`, `vm-streams` (its worktree `wt/gc-vm-streams`),
`seed-functional`, `preWindow-loop-root`, `zk-election-offer`, `pairing-port`, `vm-model-guards`, `main-sf`, `main-pw`,
`main-eo`, `main-pp`, `main-vg` (candidates of V16-V19 and PP1). Live agents: A1 (`slowdisk-dev`), A2 (`solr-bug-reindex`), A6 (read-out streaming);
merge order: `replay-address-only` (A5), the ledger's leased charges (A5), `slowdisk-dev`'s INITIAL/ORDER work,
`solr-bug-reindex`'s pieces, one per round.

| branch | head | content | state / next step |
| --- | --- | --- | --- |
| `state-pairing` | `aa961ff78` | `fix-no-root`'s commits carried onto an older main (NO_ROOT fixes, final containers as cells, D0 by test, `94e1390fc` Writers_W(l)'s writer at version 0), case `hdfs-bugs-slowdisk-zero` | the source of `slowdisk-dev`'s INITIAL port; delete once that merges |
| `slowdisk-dev` | `5fe7ef941` | main-sf + `preWindow-loop-root` + the case's declarations; a tracked read through an accessor (`65f231091`), a demanded container state tied to the read that returned the container (`5fe7ef941`) | agent A1: merge `zk-election-offer`, port `94e1390fc` (one re-paired query: A5's `SmtLowering#movedQuery`), obligation replays plant a moved writer choice by CONFIRM's ORDER rows; then SD3 |
| `solr-bug-reindex` | `35cdd1e6b` | case `reindex-cleanup` (tree `gc/solr-bugs`, two declared loop bounds); seeded random draws, the recorded-address identity rule (on main), the codec boundary for scope growth, region roots only at writers, recording rows only inside occurrences, CLAIMs keyed by the START they claim, stall rules (a response settles once its request ended, no fabricated timeout) | agent A2: a focused replay concludes once its question closed; then SB12; its pieces merge one per round |
| `system-hbase` | `11ddd06e1` | HBase harness (`experiments/hbase`, case `hbase-bugs-master-active-time` on `gc/hbase-unified`); an interface delegate's clock is a CLOCK root when every implementation in scope is one (`RootCatalog#dispatchesToClocks`) | Phase A done (Java 8 builds and runs, round HBA1 in `gc-out/hbase-bugs/`); parked on three blockers: the old master's activation time is written before the window (no root); a WAKE turn's k counts arrivals of every thread at one wait site (seed replay stalls); async start chains nest without bound (contexts up to 686 KB). When it resumes, its `experiments/hbase/system.sh` drops the keys the pipeline retirement retired (`system_cluster_class`, `system_roots`, `system_package`, `system_node_class`, `classpath_test`) |
| `pairing-port` | `b818815fe` + this docs commit | `dtx-on-main` (DataTransfer messages and doors) and `fix-11741-pairing` (11741's balancer race) ported onto `main-eo`, the review rework done: CONFIRM takes a delivery into the anchor from another producer of its question only where the arm's session answered the anchor, compares site index, attempt and value, names each substitution (`ADDRESS_UNSTABLE`); a slot's answered bit is read off its opening session, so no landing order matters; the named HDFS cases move to the dtx tree | rounds `PP1` + `PP1b` (snapshot `pp1`, `gc-out/pairing-port/`): 13/13 and 11741 twice; merged into main (`main-pp`) |
| `pairing-on-main`, `dtx-on-main`, `fix-11741-pairing` | `efaa032d7`, `e3b2efb1f`, `9fd01c95f` + WIPs (`pairing-on-main-wip.patch`, `fix-11741-pairing-review-rework-wip.patch`) | the sources of `pairing-port` | contained in main through `pairing-port` (`7ad095d0f` dropped: main's `c5878482f` covers it); to delete |
| `fix-no-root` | `2e931192e` + WIP `fix-no-root-hb-edges-wip.patch` and its four new files `fix-no-root-hb-edges-wip-untracked.patch` (in worktree `agent-a5fe8997…`) | NO_ROOT fixes + version-0 writer; HB-edges WIP | commits carried by `state-pairing`; the HB-edges WIP is not |
| `fix-hdfs-seed-stalls` | `bfd7492bd` | one rule set for seed-replay stalls | needs a live round on the 11 cases and the new checks |
| `replay-random-draws` | `d656860b2` | every random draw recorded and replayed | on `dtx-on-main` (in `pairing-port`); needs a live round |
| `fix-replay-equivalent-context` | `71fedd858` | a root admitted by its address alone (`2758f815d`); its other three commits are `pairing-port`'s | ported onto main + `pairing-port` as `replay-address-only` (one commit); needs a live round, then delete |
| `perf-vm-readout`, `vm-ref-compare` | `3cbea0bee`, `bba1ee25d` | VM read-out per activation; reference compare with an enum constant | parked; each needs a VM review (images `vm-w4i`, `vm-nr41`) |
| `worktree-agent-a49c8bf5715a00c40` | `90ca7724e` | WIRE-CODEC W3/W6 + the first WP-D integration | deferred; the source of W3/W6 when they are taken up |

Deleted 2026-10-03 (each verified merged into main, or identical to its head in
`/bigtemp/vnr3ne/handover/archived-branches-2026-10-02.bundle`): merged -- `admission-relevance`,
`agent-11741-{L1,anchor,refine,regress,timeline}`, `fix-17960-unstated-value`, `fix-a40h2-stopped`,
`fix-adhoc-crashes`, `fix-anchor-identity-replay`, `fix-confirm-flakiness`, `fix-confirm-flakiness-watch`,
`loopbound-scope`, `perf-demand-tracking`, `perf-slow-replays`, `phase1-lock`, `r1-roots-wp0-wpe`,
`stream-in-flight-cap`, `vm-bcp0-crash`, and 25 merged `worktree-agent-*` (all but the live agents'
`aea16c87…`, `a6cdfa85…`); bundle -- `adhoc-pick2`, `datatransfer-doors`, `fix-18413-watcher-deliveries`,
`fix-hdfs-seed-stalls-pre-p219`, `fix-no-root-nodtx`, `fix-replay-equivalent-context-r2`,
`fix-solver-string-blowup`, `fix-unattested-hoff-arm`, `lock-infra`, `schedule-stall-planned`,
`schedule-stall-release`, `worktree-agent-{a2a3969b…,a3b05c98…,a92b9448…}`. Then, on the lead's word: `symbolic-scope`
(merged), `symbolic-scope-wip-p1` (a WIP full port of `d7d7aa216`), and `r1-roots-wpd-wpf1`, `gc/config-roots-soundness`
(the port's sources, archived in `handover/archived-branches-2026-10-03.bundle`).

### 0.5 TODO, in order

One large change per live round of the eleven named cases; a change that turns a passing case into a failure
does not merge until fixed (§1). The new checks join the round once they pass.

1. **Symbolic scope (top priority).** `symbolic-scope` is merged (V10). Then, bug-driven and general: (a) STATE
   pairing end to end on HDFS #15 (`slowdisk-dev`, A1: the INITIAL arm and ORDER-planted pairings); (b) the
   serving-thread concurrency rule for ZooKeeper #05 (on main, V18); (c) the
   clock rule through an interface delegate for HBase #14 (committed on `system-hbase`, parked with HBase); (d) configuration values set by run-time reconfiguration
   (`ReconfigurableBase.reconfigureProperty`'s new value as a CONFIG root, its domain from the parser's accepted
   values and the compared literals) and String/enum configuration (a finite-set domain), when a pick needs them.
   After each piece: offline gate, live round of the 11, `.smt` chain check of the cases it can touch.
2. **The checks, one by one to a SAT, confirmed, hand-checked `.smt`**: `solr-bugs-reindex-cleanup` (needs nothing
   new), `zk-bugs-quota-init`, `hdfs-bugs-slowdisk-zero`, `zk-bugs-election-offer`, `hbase-bugs-master-active-time`
   (HBase first needs Phase A feasibility). Each new check: workload passes natively 5x; campaign to IMPORT; full
   campaign; read the chain against the code; add it to `experiments/accept/report.py` and STATUS "Acceptance".
3. ~~Merge the pipeline retirement~~ (done, V15).
4. **README TODO carried over**: ~~`pairing-on-main`~~ (`pairing-port`, rounds PP1/PP1b, on main), then one round
   each: `fix-hdfs-seed-stalls`, `replay-random-draws`, `fix-replay-equivalent-context` (rebased). (`perf-expr-store`
   was measured and dropped: no heap effect; the replay heap is the whole read-out page the publication decodes,
   being streamed instead.)
5. ~~Second-tier bugs~~: dropped by the owner (2026-10-03, "second tier bugs都先不管了。不用作为你的todo").
6. Then the deferred WIRE-CODEC W3/W6 (`worktree-agent-a49c8bf5715a00c40`), one piece per round.

### 0.6 Open problems

| class | state |
| --- | --- |
| STATE_PAIRING: one confirmed witness so far (ZooKeeper #05, on main since V18); a re-pairing whose reader path the recording never ran (HDFS #15) needs the INITIAL arm and an obligation replay that plants the moved writer choice | `zk-election-offer`, `slowdisk-dev` |
| `Arms#concurrent` knows happens-before only from anchor ancestry and one thread: sequential requests of one test thread through a queue (Solr's Overseer tasks) look concurrent, so they join the closure and each other's factor (Solr #04: 105 of 137 obligations on the test's later sub-tests) | lead's design item; start from `handover/fix-no-root-hb-edges-wip*.patch` (OrderRow START/QUEUE edges); request/response completion edges still to design |
| A focused replay runs to the workload's end even once its question is closed (Solr #04: 26-min replays after a 4.5-min answer) | `solr-bug-reindex` (A2) |
| Clocks behind an interface delegate (HBase `EnvironmentEdgeManager`) are not roots | WIP in `system-hbase` |
| Configuration roots | `symbolic-scope` |
| A value crossing processes through a file, a stream with no door, or HDFS namespace state is lost | by the IO rule, such bugs are not picked; open for the engine |
| Seed replays that stall on their own recording (heartbeat vs block report by clock, late HTTP between concurrent Overseer tasks) | `fix-hdfs-seed-stalls` (HDFS); Solr has no rule yet |
| Replay heap (large Solr seeds); a trace aggregation that needs 4 GB (SB1) | `perf-expr-store`; measure SB1 |
| DataNode registration order before the window | owner: not now (prototype `handover/startup-order-prototype.patch`) |
| UNPRODUCIBLE_ANSWER (an IPC answer resting on an unstated value) | seen once on `dtx-on-main`, not traced |
| Enum constant compared by reference | `vm-ref-compare`, parked |

Designs and analyses outside the repo: `/bigtemp/vnr3ne/specs/WIRE-CODEC-proposal.md`, `R1-ROOTS-proposal.md`
(its "Designer decisions" bind), `R3-REFCONT-proposal.md`, `R3-shapes.md`, `C2.md`, `F14.md`, `DOCS.md`; the
owner's requirements R1-R6 `/bigtemp/vnr3ne/analysis/audit/COMMON.md`; the tree inventories
`/bigtemp/vnr3ne/analysis/unify/`; the bug descriptions `~/bug_study/*.txt`; WIP patches and the branch bundle
`/bigtemp/vnr3ne/handover/`.

---------------------------------------------------------------------------------------------------

## 1. The owner's standing rules (long-term; they override defaults)

The owner is a PhD student doing academic research on open-source system stability. Reply to the
owner in **Chinese**, answer a direct question first (before continuing the work), keep answers
short. The design decisions are the lead's (the agent coordinating the work), made after reading
the code; implementers follow a written design. Decisions that change what the owner asked for
(the bug checks, the recording window, what counts as a root) go to the owner with a
recommendation.

**The 2026-10-02 goal's rulings** (§0.1 has them verbatim)
- **Symbolic scope first**, bug-driven and moderate: when a high-quality coordination bug is out of reach
  only because a value is not symbolic or a read is not re-pairable, widen the scope generally for it;
  small per-case adjustments (a case's declarations) are allowed.
- **Checks are real bugs**, each verified in the system's source, marked in its tree with
  `@CausynthExceptionTarget`, one campaign each; a self-written cluster test may be the workload of a truly
  high-quality bug; a low-quality bug is skipped.
- **IO rule:** a bug whose causal chain crosses file or HDFS-namespace state is not forced; a system's
  protocol header may be extended to carry the causal context (HDFS `RpcHeader.proto`, HBase `RPC.proto`).
- **Acceptance per check:** a SAT `.smt` whose claim has the bug's mechanism, confirmed, its chain checked by
  hand against the code.
- **Clean as you go:** unused code, artifacts and docs are deleted, not kept "just in case".

**Engineering**
- **General fixes only.** No per-case code, no fixes derived from a case's expected verdict, no
  dead code, no fallback paths, no flags to keep an old path. Per-system code is allowed only as a
  small adapter or a declaration row, listed in STATUS "Per-system surface". Every stop/skip rule
  and every performance optimization is general.
- **Global view:** read all the code a concept touches (every stage) before changing it; fix the
  class of bug, not the instance. Docs may be stale — the code and the owner's current
  requirements are the reference.
- **Refactor bloat along the way** in the same commits as the goal work that touches it.
- **JVM-level relation preservation:** symbolic propagation is at the JVM level (shadows on slots,
  fields, objects), not KLEE's byte level. Every value moved outside interpreted bytecode is
  HOOKED, MODELED, or DETECTED-AND-PINNED by name — never lost silently. Shadows never belong to
  a JVM-shared identity (cached boxes, interned Strings, `Boolean.TRUE`).
- **No recorded-order pruning:** never drop candidate writers because they come after the read in
  the recording.
- **The question is one declared occurrence** `(r,c,i)` fixed at the seed; a campaign stops at its
  first witness when the case says so.
- **Lean tests:** table-driven, one test class per new class, delete tests of removed mechanisms.
- **Docs track the code:** docs describe HEAD only; update `docs/STATUS.md` and the design docs in
  the same commit as the change; delete what becomes outdated.
- **Time optimization never ends:** after every round, measure where each campaign's time went
  (`timeline.py`) and cut work that produced nothing, with a general rule, gated so verdicts do not
  move. A check should take tens of minutes; an occasional run past an hour is fine, but runs of
  hours usually mean a defect (a stall, a starved step, an exploding closure): find it.
- **The closure revolves around the declared target region `(r,c)`** (the seed graph too): prune
  branches that lost it; for HDFS only the target DataNode matters. Never encode a case's chain.
- **The closure keeps every static writer** of a demanded location; never drop writers the
  recording did not exercise (an untaken branch's write is what a flip enables). Over budget:
  recorded writers first, the rest cut by a named `PLAN_CLOSURE_CUT`.
- **Over-approximate, confirm strictly:** COMPOSE/EXPLORE may produce false SATs (CONFIRM refutes
  them, the model is excluded, the next claim follows); composer imprecision is a performance item,
  never a blocker. CONFIRM is the last filter and must stay strict (never loosen what it compares
  without an equal check; every substitution named). Completeness outranks precision: a guard
  that can make a real witness UNSAT is worse than a false positive.
- **Roots from general rules only;** a small per-system adapter is allowed and listed in STATUS
  "Per-system surface"; never a root chosen per case or by the expected mechanism.
- **Delete what automation replaces:** every automating merge deletes the old code, manual tools,
  hand rows and scripts it replaced.
- **Lock, then one change at a time:** keep the last all-passing main; integrate one large change
  per live round; stacking several big changes is what made rounds regress repeatedly
  (2026-10-01).

**Acceptance**
- **What a real PASS is:** the claim, polarityDecides, the mechanism's roots in
  `claim.movedRoots`, confirmed, cone gate — a PASS line or a finding kind alone is not acceptance.
- **Mechanism mandate:** 17899 bug1/2/3, 17897, 17967 A/B/C are MARKER_FLIPPED by an IPC door
  fault (either direction); 17960 by its config; 11741 by clocks (or a fault); the Solr cases by
  clocks (CLOCK_SKEW).
- **After every engine change, check the `.smt` causal chains** of the cases it can touch against
  the system code (e.g. 11741: `allKeys` ite/put/remove, keyId across the wire, the solver's
  choice).
- **Real false-positive examples only:** never construct false positives; FP-filter examples come
  from real runs.

**Git and safety**
- **Push only when the owner asks** (each request covers that moment, not later commits). Never
  `git add -A`. Commit only when the change is built and tested.
- Before every commit: `mvn -q -o package` and `bash src/test/shell/run_engine_campaign_helpers_test.sh`
  (both via `onlift.sh`, §3).
- Commit messages end with `Co-Authored-By: <model> <noreply@anthropic.com>`. Commits in the
  Solr/HDFS trees use `git -c user.name="Zhenyu Li" -c user.email=zhl136@ucsd.edu`.
- Never edit the owner's dotfiles. Never rebuild a tree or edit a snapshot a campaign runs on.
  Never remove a `~/gc-run/p<N>` a running round uses: `tools/rounds/snapshot-gc.sh` removes one
  only when no process on any lift names it.
- Solr's test SecurityManager may be changed if it interferes (owner's permission); today it is
  off via `-Dtests.useSecurityManager=false`.

---------------------------------------------------------------------------------------------------

## 2. Working with agents in parallel (the owner's rules, long-term)

The owner wants throughput: "这里明显能并行的你就并行。你自己管理好代码分支，之后的merge什么即可" /
"这种多个job明显可以并行啊" / "总之，你要积极主动地利用多agent。去审查代码细节。一旦你有不确定就要去找". And
a budget: "合理分配多agent", "减轻一些fan out的规模".

**When to use an agent**
- Any job with **no dependency on another job runs NOW, in parallel, whatever phase it belongs
  to**: independent work packages, offline gates, live rounds, investigations. Serialize only on a
  real dependency (a package needs another's merged API; a round needs a fix merged).
- Root-causing a failed campaign, implementing a written work package, a code audit of a stage,
  and an independent review of a large diff are agent jobs.
- The moment you are unsure about a code detail (what a function does, whether a capability
  exists, why a run failed), send an agent to find out instead of assuming.
- Do small things yourself: a targeted grep/read, a small fix, conflict resolution, merges,
  reviewing a short diff.

**How many and how**
- About **6–7 agents at once**; no agent spawns sub-agents; ask for short reports (≤ 15–20 lines);
  no idle polling loops (use a background command that exits on the condition, or a monitor).
- Every coding agent gets its **own git worktree** (`isolation: worktree`) and branch, a disjoint
  file area where possible, and a prompt that states: the goal, the evidence (paths to runs), the
  spec section, the rules (general code, docs in the same commit, lean tests, never push, never
  `git add -A`, the pre-commit commands), the validation to run (offline gate cases and rounds),
  and the report format.
- Continue an agent with its previous context (send it a message) rather than starting a new one
  when the next task is in the same area.
- **The lead owns main:** review every diff before merging; resolve conflicts yourself; keep main
  green (`mvn package` + shell test after each merge).
- **Review policy:** small/medium changes — the lead reviews. Large or high-risk batches (VM,
  replay/schedule, identity, soundness of COMPOSE/CONFIRM) — ONE independent review agent per
  batch, BEFORE merging, then a live round. Reviewers are read-only and cite file:line.
- **Merge gate:** the offline regression gate (`tools/regress/offline-ab.sh`, §3) for every change
  to SEED/PLAN/EXPLORE/COMPOSE/CONFIRM; a live round for VM, runtime, identity or replay changes.
  Verdicts and moved roots must not change unless the change is meant to change them, and then the
  `.smt` chains are checked by hand.
- Campaigns run from **frozen snapshots** (`~/gc-run/p<N>`), never from the working tree. Scripts
  set their own environment (`tools/lib/gc-env.sh`, `onlift.sh`).

**The mechanics in Claude Code** (what the previous lead actually did)
- Start a coding agent with the Agent tool: `subagent_type: general-purpose`,
  `isolation: "worktree"`, `run_in_background: true`. A read-only reviewer or investigator needs no
  worktree. You are notified when an agent finishes; never predict its result before that.
- Continue a finished or running agent with `SendMessage` (its id); it keeps its context. Stop one
  with `TaskStop`.
- Watch rounds with a `Monitor` on `round-monitor.sh … | grep --line-buffered 'DONE '` (it expires
  after 30 min; re-arm it; a re-armed monitor re-reports finished cases). For a single wait, run a
  background Bash command that loops `until <condition>; do sleep 30; done` and exits.
- A typical cycle: a round finishes → read each failure yourself (summary, log, report, gaps: a few
  minutes) → one agent per distinct root cause with the evidence paths → review its diff → merge →
  new snapshot → next round, while other agents keep working on independent packages.
- Prompt skeleton for a coding agent: *context* (repo, main sha, what is on main that matters) →
  *problem with evidence* (run paths, error lines, row ids) → *task* (trace the code first; fix
  generally; what not to touch) → *rules* (worktree only, never push, never `git add -A`, commit
  trailer, `mvn -q -o package` + shell test via `onlift.sh` before each commit, docs + STATUS in the
  same commit, lean tests) → *validation* (exact `offline-ab.sh` command and cases; a live run on
  its own snapshot with its own round name when runtime/VM changes) → *report* (≤ 15 lines: commits,
  evidence, gate lines, what is left).
- Keep a short state note current for yourself (the previous lead used
  `~/.claude/projects/-u-vnr3ne-GraphChecker/memory/phase2-status-2026-10-02.md`), and keep
  README §0 current when you hand over.

**How the 2026-10-02 night lead ran the agents** (eleven agents over the session, seven at once)
- **Investigators first, read-only, one per system.** To choose the checks, four general-purpose agents (no
  worktree, no build, no runs) each read one system's bug descriptions against its source and returned ONE
  compact table: per bug, present in our version (file:line of the fatal throw), real?, coordination?, the
  single counterfactual that flips a passing run and where, the best existing workloads, a fit rating, then
  their top picks. The lead then read the code of every pick itself before deciding; an investigator's
  table is evidence, not a decision.
- **One coding agent per work package, never two on one package:** `isolation: worktree`, `run_in_background`,
  a branch named in the brief, an explicit base ("from main c2c920098", or "main + merge X"), and for a new
  system or bug its OWN system tree (a new worktree of the system repo on a new `gc/<name>` branch under
  `/bigtemp/vnr3ne/wt/`, built with its own Maven repo `/bigtemp/vnr3ne/m2/<name>`), so no agent rebuilds a tree
  a round or another agent reads.
- **The brief** (each was ~40-60 lines): context and what to read first (README sections, design docs, the
  model adapter or commit to port), the bug or goal with file:line evidence the lead verified, the design to
  follow (the lead's, stated as rules, e.g. "the adapter registers each server as a node with the objects it
  runs work through; open the window once the cluster is up"), phases with a GATE where the agent stops and
  reports (e.g. HBase: feasibility on JDK 8 and the VM before any adapter), the rules (general code, no dead
  code, docs + STATUS in the same commit, lean tests, never push, never `git add -A`, commit identity and
  trailer, `mvn -q -o package` + shell test via `onlift.sh` before each commit), validation (the offline gate
  on the newest all-PASS round for engine changes; at most ONE live campaign at a time, from a frozen snapshot
  of the agent's own branch, in the agent's own `GC_OUT`, stopped before reporting), and a report of at most
  15-20 lines.
- **Scope changes mid-flight go by `SendMessage`** to the running agent (e.g. "drop check 3: its throw is the
  fault's echo"), never by a second agent.
- **The lead keeps for itself:** reading and verifying bugs, the design, merges and conflict resolution, live
  rounds of the eleven cases, `.smt` chain checks, the cleanup of artifacts, and memory/README.
- **Budget:** seven agents at once burned the account's weekly usage limit in about two hours (2026-10-02
  ~19:40-21:00), stopping all of them mid-edit. Run at most 3-4 coding agents at once, give each a package
  that can commit in small finished steps (commit after every working step, not at the end), and keep WIP
  small. When the limit hits, follow the last bullet of the lessons below (save WIP patches, reap runs).

**Lessons from 2026-10-02 (the last lead's day: 8 coding agents, 2 reviewers, rounds V4–V9)**
- **Tell every agent its base** explicitly ("from main X", or "on the V7 stack = main + dtx + …"):
  work that depends on an unmerged branch (DataTransfer identity, for instance) must sit on it, and
  the merge order then follows the dependency.
- **Agents' own live runs share the cluster with your rounds.** Several agents each running
  campaigns (plus your round) push every lift to its ledger ceiling, so heads wait for memory and
  times double. Ask agents for offline evidence first, at most one live run at a time, in their own
  `GC_OUT` (`/bigtemp/vnr3ne/gc-out/<branch>-*`), and to stop what they started before reporting.
  Judge a crowded round by verdicts and per-obligation replay times, not wall time.
- **Brief reviewers with the owner's principles** (over-approximate, confirm strictly; completeness
  first), so they rank findings the way the owner does. Both reviews this day found real blockers
  that live rounds had passed (a budget that would stop ad-hoc exploration after ~10 min; a
  CONFIRM substitution comparing no value).
- **A failure in a validation round is not automatically the branch's fault:** rerun the case on
  plain main (`M1` showed 11741 passes on main by the order it gets) before blaming or merging.
- **The account's usage limit can stop every agent at once,** mid-edit. Resume each with
  `SendMessage` ("continue where you were"); they keep their context.
- **When agents are stopped for good,** save any uncommitted diff as a patch
  (`/bigtemp/vnr3ne/handover/`), then reap their runs on every lift by a path only those runs carry
  (their worktree or `GC_OUT` directory), feeding the pattern through stdin (`ssh <lift> 'bash -s' <
  script`), never on your own command line (§3.8), and remove ledger entries whose pid is gone
  (`$CAUSYNTH_HOST_LEDGER/explorations/`).

---------------------------------------------------------------------------------------------------

## 3. Servers, storage, environment and tools

### 3.1 Hosts and storage

| what | where / how |
| --- | --- |
| hosts | `lift06`…`lift15` (ten), 48 cores and 30 GB each. All ten are used for every fan-out (obligations, rounds, sweeps, builds). `lift11` is the owner's interactive machine: it is a **worker but never a campaign head** (`launch-round.sh` enforces it). Never blow up a host's memory: every start goes through the host ledger (below). |
| home | `/u/vnr3ne` is NFS-shared by all lifts, **100 GB quota** (it has been full twice). Keep bulk data off it. |
| bulk storage | `/bigtemp/vnr3ne` (NFS pool, automounted on every lift, owner-approved): round outputs `gc-out/`, VM images `vm-*/`, specs, analyses, gate outputs `ab/`, helper scripts `bin/`, agent worktrees `wt/`. `test -w` does not trigger the automount; `ls` it first. |
| local scratch | `/localtmp/$USER` on each lift (replay working directories go to `/localtmp/$USER/graphchecker/`). |
| stock JDK 8 | `/usr/lib/jvm/java-8-openjdk-amd64`. **Trap:** the owner's dotfiles export `JAVA_HOME=java-11`, which lift11–15 lack, and `bash -c` under ssh re-reads `~/.bashrc`. Do not edit the dotfiles; use `onlift.sh`, which unsets `SSH_CLIENT` and sets Java 8. |
| z3 | `~/.local/bin/z3` (4.14.1) |
| concolic VM images | main's current VM: **`/bigtemp/vnr3ne/vm-model-guards2/j2sdk-image`** (vm-streams2 + the model guards: no model records a condition, a muted body's choice is a guard on its chain; branch `vm-model-guards` af18b3a5d, merged dda07c51b after round V19 13/13). `vm-streams2` (vm-w4h + the java.util.stream model, branch `vm-streams` fe68c3409, merged 770a64c8f after round V14; a jar before 770a64c8f refuses its STATE_COLLECT versions by name) serves rounds V14-V18. `vm-w4h` (the previous one: vm-w4e + the `frame::metadata_do` fix + caches cleared when metadata is freed + demand-driven tracking) serves rounds up to V13. Parked, unreviewed: `vm-w4i` (per-activation tracked-location read-out, branch `perf-vm-readout`; a jar from that branch refuses vm-w4h by name), `vm-nr41` (reference-compare identity, branch `vm-ref-compare`). Older images are deleted (2026-10-02). Pass an image as `CAUSYNTH_CUSTOM_JDK_HOME` (a sweep: `VM_IMAGE`), never as `JAVA_HOME`. A Java side that needs natives an image lacks refuses the replay by name (`ConcolicVmBroker#requireCurrentCapabilities`). |
| HDFS trees | `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` (worktree of `~/hadoop`, branch `gc/hdfs-unified-dtx`: `gc/hdfs-unified`, trunk 734dd8a67cd, plus the DataTransfer op's envelope; its own Maven repo `/bigtemp/vnr3ne/wt/dtx/m2`): ONE tree for the eight named cases (hdfs-17897, 17899-bug1/2/3, 17960, 17967-pathA/B/C) -- one adapter, every workload, the known bugs' pre-fix code and target markers; its commit-by-commit inventory is `/bigtemp/vnr3ne/analysis/unify/hdfs-inventory.md`. hdfs-11741 keeps `~/hadoop-hdfs-11741` (`gc/hdfs-11741`); the older per-case trees `~/hadoop-hdfs-<case>` (`gc/<case>`) stay for the runs that used them |
| Solr trees | One Solr 8.11 tree line, `~/lucene-solr-unified` (branch `gc/solr-unified`, a worktree of `~/lucene-solr-8_11`): the shared adapter, both cases' workloads and target markers, the two kept scaffold patches (inventory: `/bigtemp/vnr3ne/analysis/unify/solr-inventory.md`); solr-18406 and solr-18413 name its successor `gc/solr-unified-storing` (`/bigtemp/vnr3ne/wt/lucene-solr-storing`: the same plus SolrZkClient's `MessageDoors#storing` write brackets). The older per-case worktrees (`gc/solr`, `~/lucene-solr-18406`, `~/lucene-solr-18413`, `~/lucene-solr-8_11-adhoc`) serve only rounds started on them. Ant build; native Ant tests need `-Dtests.useSecurityManager=false`. `~/solr` is apache/solr main (blobless: never `git grep` a commit there). |
| ZooKeeper tree | `/bigtemp/vnr3ne/wt/zookeeper-unified` (branch `gc/zk-unified` on `branch-3.9`, a worktree of `~/zookeeper`): the adapter (`CausynthZk`, `CausynthZkCluster`), the `zk-bugs` cases' target markers and the quota workload. Maven build into its own repository `/bigtemp/vnr3ne/m2/zookeeper` (`experiments/zookeeper/build.sh`, which installs the GraphChecker jar there; never `~/.m2`). Build a case's workload before its first run: `SKIP_GRAPHCHECKER_INSTALL=1 bash experiments/lib/run.sh experiments/zookeeper/zk-bugs <case> build`. Its only remote is apache/zookeeper: never push it. |
| HBase and bug trees | `gc/hbase-unified`, `gc/solr-bugs`, `gc/hdfs-bugs` under `/bigtemp/vnr3ne/wt/` (§0.2); clone `~/hbase`; private Maven repos `/bigtemp/vnr3ne/m2/<name>` |
| owner's memory notes | `~/.claude/projects/-u-vnr3ne-GraphChecker/memory/` (one fact per file, index `MEMORY.md`) |

### 3.2 Helper commands (outside the repo)

```bash
/bigtemp/vnr3ne/bin/onlift.sh [-g <min-free-GB>] [-h <host>] <command...>
    # run a command in the current directory on the least-loaded lift (or <host>) with the Java 8 +
    # Maven toolchain; use it for mvn, the shell test, VM builds, offline stages, anything heavy.
    # `onlift.sh -h` with no host hangs; always give a host or omit -h.
/bigtemp/vnr3ne/bin/pick-lift.sh [min-free-GB]   # prints the best lift
```

### 3.3 Build, test, commit

```bash
cd ~/GraphChecker
/bigtemp/vnr3ne/bin/onlift.sh -g 10 bash -c 'mvn -q -o package && bash src/test/shell/run_engine_campaign_helpers_test.sh'
```

Keep `-o` (offline): `~/.m2` is shared over NFS. `mvn package` also builds the `hadoop-shim`
classifier jar from `src/shim/java`, which the HDFS trees call. A snapshot needs all three jars in
`target/` (`-jar-with-dependencies`, `-hadoop-shim`, plain).

VM: build with `third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh`
(or the recipe under `/bigtemp/vnr3ne/vm-w1/work/`, see `docs/design/VM.md`), ~1 h for a full JDK,
via `onlift.sh -g 12`. Smoke tests: `scripts/causynth_smoke_test.sh` with `JDK_HOME` = the image.
Never overwrite an image a round uses; build a new directory.

### 3.4 Rounds (live campaigns)

```bash
git worktree add --detach ~/gc-run/p<N> <commit>
(cd ~/gc-run/p<N> && /bigtemp/vnr3ne/bin/onlift.sh -g 10 mvn -q -o package -DskipTests)
GC_OUT=/bigtemp/vnr3ne/gc-out CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-model-guards2/j2sdk-image \
  tools/rounds/launch-round.sh ~/gc-run/p<N> <round>              # all 11 cases, heads chosen by room
CASES="hdfs-17960 solr-18413" ... tools/rounds/launch-round.sh ... # a subset (or any case id)
DRY=1 ... tools/rounds/launch-round.sh ...                         # the heads it would choose
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/round-monitor.sh '<round>-*' | grep --line-buffered 'DONE '
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/stop-run.sh <round>-<case> ...
```

- Every tool takes `GC_OUT` from `tools/lib/gc-env.sh` (default `/bigtemp/vnr3ne/gc-out`).
- A launch must name its VM image (`CAUSYNTH_CUSTOM_JDK_HOME`; a sweep's `VM_IMAGE`): there is no
  default image.
- `launch-round.sh` chooses each case's head host at launch from the hosts' room in the ledger
  (`campaign_host_room`): the heaviest case first (its `engine_memory_mb`, `tools/lib/heads.sh`
  `case_engine_heap_mb`), each to the host with the most room among those heading the fewest
  cases, so no host heads two before every host heads one; `lift11` heads nothing. A head only drives its campaign: every
  engine JVM, the seed and CONFIRM replays and REPRODUCE's runs go wherever there is room, its own
  host first (PIPELINE §7.7).
- A round's cases explore uncapped (`stream_max_in_flight=0`): each keeps as many obligations in
  flight as the hosts admit, so one case alone may take the whole cluster. A sweep ("Run the bug
  checks") caps them so the cases it runs at once share it: `sweep.sh` gives every case
  `CAUSYNTH_STREAM_MAX_IN_FLIGHT` = the lifts' obligation slots for its `obligation_memory_mb`
  (`run_engine.sh` `campaign_pool_slots`: on each lift as many replays as fit under the 70 %
  ceiling at their charge, at most its cores; the ten lifts hold 30 of 6000 MB), and each capped
  exploration keeps its share in flight: those slots over the capped explorations running now
  (their entries in `$CAUSYNTH_HOST_LEDGER/explorations/`), at least one, read again at every start
  (`campaign_stream_has_slot`). Ten exploring cases keep 3 each; one left alone keeps all 30.
  A sweep's head is admitted (`fanout.sh` `NEED_MB`) for the room it reserves on its host, what
  its planner or composer starts at (`tools/lib/heads.sh` `case_head_reserve_mb`, 8 GB), not
  its engine heap: a40's Solr heads asked for 16 GB and waited while one case's 27-32 replays
  filled the lifts.
- A round name is written once (`accept-<round>-<case>` exists → refused). Names used so far:
  `v*`, `r1`–`r9`, `ra1`, `rb1`, `i1`–`i3`, `stream*`, `fast*`, `g1`, `F1`, `F1b`, `F2`, `K*`, `L*`, `N1`,
  `V1`–`V8`, `V4h`, `V5h`, `V7b`, `M1`, `CF1`, `STO1`, agents' `a37f*`, `ee*`, `agent-*`, `w4-*`, `R5x*`,
  `r6s*`, `R7*`, `nr*`. Use a fresh name (e.g. `V9`, `V10`, …).
- Typical wall time on main (round `V8`, cluster shared with a few agent runs): HDFS cases 5–11 min,
  11741 ~27 min, solr-18406 ~15 min, solr-18413 ~23 min. After the campaign, the acceptance report's
  `probe.sh` (z3 per alternative path, 600 s each) can add up to 30 min before the summary row is
  written; it is reported, not a gate.
- **How the last lead used the servers:** one round at a time, at most ~6–8 cases at once (batch 1
  = six cases, then the rest as cases finish); sweeps with 1 head per host
  (`sweep.sh … 1`); agents' verification runs in their own `GC_OUT`; every start through the ledger
  (≤ 70 % memory per lift); `lift11` (the owner's machine, where the lead session runs) works but
  never heads; builds with `onlift.sh -g 10`.

### 3.5 The offline regression gate (merge gate)

```bash
AB_ACCEPT_ROOT=/bigtemp/vnr3ne/gc-out AB_OUT=/bigtemp/vnr3ne/ab/<name> [AB_STAGES="IMPORT EXPLORE.N COMPOSE"] \
  tools/regress/offline-ab.sh --round r8 --round r7 <baseline.jar> <candidate.jar> [case...]
```

Re-runs every stage that is a pure function of a recorded round (SEED.static, SEED.trace, PLAN,
EXPLORE.0, SOLVE.0, IMPORT, EXPLORE.N, COMPOSE, CONFIRM planning) with both jars and compares.
No replay: it cannot see VM, runtime or identity changes — those need a live round. Read the
header for `AB_HEAP_MB`, `AB_BASELINE_REPO` (when declarations differ between sides), `AB_HOSTS`.
Keep jars in `/bigtemp/vnr3ne/ab/jars/`.

### 3.6 Reading a campaign

`summary.tsv` (verdict row) → `logs/<case>.log` (`[campaign:error] stage=… reason=…`) →
`report/<case>/report.md` (blocking gaps, witness findings, causal cone) → `out/<case>/schedule/final/`
(`claim.json`, `candidate.smt2`, `candidate_composition_manifest.json`, `confirm.json`, `gaps.json`)
→ how EXPLORE ended `iteration-0000/exploration.json` → per planner round
`iteration-0000/obligations-<NNNN>/<id>/` (`obligation_query.smt2`, `obligation_result.jsonl`,
`replay.log`) → sessions `iteration-0000/sessions/<id>/`
(`targets.jsonl` has `reachedAnchor` and `observedFatal`). `experiments/accept/cone.py` and
`probe.sh` re-check a published formula. `tools/analysis/timeline.py`
breaks a campaign's time down by stage.


### 3.7 A snapshot for a branch that needs another tree

There is no override for a case's tree: each `experiments/<system>/<case>/case.sh` names its `repo=`. To
validate a branch that needs a different tree (no branch does today; `pairing-port` needed
`/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` before its merge), edit those lines in the **snapshot only**, uncommitted,
never on main:

```bash
git worktree add -q --detach ~/gc-run/p<N> <main>
cd ~/gc-run/p<N> && git merge --no-ff -q <branch> -m "Validation merge: <branch>"     # resolve docs conflicts by keeping both sides
sed -i 's#repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx$#repo=<tree>#' \
  experiments/hadoop/hdfs-17967/case.sh experiments/hadoop/hdfs-17899/case.sh \
  experiments/hadoop/hdfs-17960/case.sh experiments/hadoop/hdfs-17897/case.sh
/bigtemp/vnr3ne/bin/onlift.sh -g 10 bash -c 'cd ~/gc-run/p<N> && mvn -q -o package && bash src/test/shell/run_engine_campaign_helpers_test.sh'
```

The `case.sh` files of 17899 and 17967 hold indented `repo=` lines (one per sub-case), hence no `^` there.
11741 keeps `~/hadoop-hdfs-11741`. A tree built for one branch must not be installed into the shared
`~/.m2` (use `MAVEN_REPO_LOCAL`, `experiments/hadoop/build.sh`), or it changes the jars every other tree's
build resolves. A Solr workload must be built in the Solr tree the case names before its first run:
`SKIP_GRAPHCHECKER_INSTALL=1 bash experiments/lib/run.sh experiments/solr/<case> "" build` from the snapshot.

### 3.8 Traps the last leads fell into

- **pkill can kill your own shell.** `pkill -f <pattern>` matches every process whose command line
  contains the pattern, including the shell that runs it, and a heredoc counts as part of that command
  line. The lead session runs on `lift11`, which is also a worker. Use `[x]`-style patterns, kill by pid,
  or send the script to `ssh <lift> 'bash -s'` from a file written earlier. `stop-run.sh` is safe.
- **A head's command line does not carry its output path** (`run_engine.sh --config …`): `pgrep -f
  accept-<round>-<case>` finds the workers, not the head, and says "dead" for a live run. Tell a live run by
  `ps -g $(cat accept-<round>-<case>/pgid)` on its head host.
- **A starved head step looks like a hang:** a step that needs more than the ledger can ever free on a busy
  lift waits silently (`waiting for memory for a head step … on any host`). Main now holds the best host for a
  waiting step and starts GROW's planner at 2 GB; if a log goes quiet for many minutes, read the step's own
  stderr (`obligations-<NNNN>/grow-stderr.log`).
- **Never rebuild a tree that someone reads.** Agents run checks on `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` and the
  Solr trees too: check `pgrep -fc '[h]adoop-hdfs-dtx'` (etc.) on every lift first; replays read the tree's
  `target/classes` directly.
- **Parallel coverage or test runs can corrupt a tree's `target/test-classes`** (a broken `ssl-client.xml`
  once failed every HDFS workload; the backup is in `/bigtemp/vnr3ne/analysis/corrupt-test-classes/`).
- **A monitor re-armed on `round-monitor.sh` re-reports every finished case;** filter out the ones you have.
- **One run is not a verdict on a flaky case.** 11741 (balancer dispatcher timing) and solr-18413 (ZooKeeper
  watch timing, Overseer queue) have real races; a CONFIRM refutation there can be the race, not the branch.
- **Composite changes hide their culprit.** When several branches are stacked in one snapshot and a case fails,
  run the case on plain main and on main + one branch before deciding.
- **The home quota is 100 GB** and has filled twice: round outputs, VM images and worktrees of other trees go
  to `/bigtemp/vnr3ne`. Remove old snapshots with `tools/rounds/snapshot-gc.sh` (it refuses one in use).

---------------------------------------------------------------------------------------------------

## The pipeline

One campaign per case, driven by `run_engine.sh`: one `campaign_<stage>` shell function per
stage, which calls Java mains in the jar.

```
SEED        static fatal slice + scope map (Soot), one recording on stock JDK 8
PLAN        the occurrences to replay, the declared target resolved, the roots to mint
INSTRUMENT  weave hooks into the scoped classes, verify the woven bytecode
REPLAY      seed replay on the concolic VM -> the seed session (one file per row kind)
IMPORT      row-contract gate over every session (contract/RowInvariants)
EXPLORE     one streaming pool: plan flip obligations in rounds (explore/ExploreMain), solve
            each, replay it focused on its world (runtime/FocusedReplay), land each session
            as it returns, grow the woven regions (GROW); end at the first witness COMPOSE
            accepts
COMPOSE     merge all sessions into one disjunction over the anchor, solve it per
            valuation with z3, decide the claim (compose/ComposeMain: Composer, ClaimPolicy)
SOLVE/DECIDE  check and print the solver verdict and the claim COMPOSE published
CONFIRM     re-run the witness world, check its edges (explore/ConfirmMain)
EMIT        final/result.json, gaps.json, run-manifest.json
REPRODUCE   after the verdict: run a confirmed witness natively, N runs at once over
            the lifts, the recording weave on the stock JDK planting only its fault
            markers, each ending at the fatal at its anchor (runtime/RecordingPlant)
```

The stages, their gates and the claim kinds are specified in
[docs/design/PIPELINE.md](docs/design/PIPELINE.md).

## Run one case

A case directory holds declarations only. `experiments/<system>/<case>/` contains:

- `case.sh`: the tree, the workload test, the target occurrence and the analysis scope;
- `workflow.properties`: budgets and inputs. `run_engine.sh` accepts only the keys it knows, so
  an unknown key is refused;
- `target.yaml`: `exception_target: <name> <binary class name> <source line> [<thrown type>]`.
  The engine finds the one `throw new` at that line of the class or of a class nested in it (a
  lambda body, an anonymous class) in the compiled classes; the tree is not rebuilt. The thrown
  type is needed only when the line holds two throws. A known bug's case keeps no `target.yaml`:
  its tree marks the bug's target throw with `@CausynthExceptionTarget("<case id>[,<case
  id>...]")` (the case id is `<case dir>-<case arg>`, e.g. `hdfs-17899-bug1`), and `run.sh`
  derives the spec from the marker (`tools/lib/annotated.py <system dir> <tree> <case id>`, into
  `$CAUSYNTH_OUTPUT_DIR/declared-target.yaml`). A bug check is such a case ("Run the bug
  checks");
- optionally `communication-mappings.jsonl` (`WIRE_FLOW` rows; the fault doors are the engine's
  library catalog, `docs/design/SYMBOL-SCOPE.md` §4.2), `root-domains.jsonl` and
  `loop-bounds*.jsonl`.

Everything executable is in `experiments/lib/`; its README gives the workload rules. Per-system
parts are in `experiments/<system>/{system.sh,build.sh,classpath.py}`.

```bash
experiments/lib/run.sh experiments/hadoop/hdfs-17960 "" build      # build the tree, run the workload once
export CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-model-guards2/j2sdk-image
CASES=hdfs-17960 bash experiments/accept/accept.sh                  # campaign + probe + report
```

A case id names its experiment by its longest prefix, for example `hdfs-17899-bug1` or
`solr-18413`.

`accept.sh` runs the campaign, a z3 probe and `report.py`. `experiments/accept/README.md` says
what PASS means. `report.py`'s table names the nine HDFS cases, the two Solr cases and the two
ZooKeeper cases (`zk-bugs-quota-init`, `zk-bugs-election-offer`); a case it does not name cannot
pass. Before each case `accept.sh` waits for `MIN_FREE_GB` free where `OUT`
is written.

`tools/lib/gc-env.sh` states, once for every tool and for `run_engine.sh`, the output root
`GC_OUT` (default `/bigtemp/vnr3ne/gc-out`), the host ledger `CAUSYNTH_HOST_LEDGER` (default
`/bigtemp/vnr3ne/gc-out/hosts`, one for the cluster whatever `GC_OUT` a run writes) and the hosts
`LIFTS` (lift06–15).

Obligations of a campaign, and GROW's re-runs, fan out over the hosts in
`CAUSYNTH_CAMPAIGN_WORKER_HOSTS`, round-robin, as many on a host as its ledger admits, up to its
cores. A head's own steps go to its host when it has room, else to the pool's host with the most
room (`campaign_head_charged`, run there through `run_engine.sh --run-placed`). Every start on a
host is charged to the ledger first, at its measured need, for as long as it runs: an obligation or
a re-run, which is its replay (`obligation_memory_mb`), a host's solver of the exploration (its
start's need; PIPELINE §7.5), a campaign head's engine JVM (its main's measured need, else
`engine_memory_mb`, and once more at `engine_memory_mb` if it runs out; PIPELINE §7.7), its seed and
CONFIRM replays (seven times the recording's measured peak when above `obligation_memory_mb`, else
that), REPRODUCE's runs (the recording's peak), an offline gate's JVM (its heap) and a `fanout.sh`
job (its `NEED_MB`). A start goes only when both the host's live charges and its real use
(`MemTotal` less `MemAvailable`), each with the start and a head's held room, stay within
`CAUSYNTH_HOST_MAX_USED_PCT` (70) percent of `MemTotal`; a charge lives by a lease its holder renews
(`$CAUSYNTH_HOST_LEDGER/<host>/charges/`, 120 s), so a killed run's charges lapse, and is released
the moment what it ran returns. A running workload JVM that outgrows its
charge is granted the excess, charged on the ledger, unless the host's real use (`MemTotal` less
`MemAvailable`) would pass that ceiling with it; only then is it ended (`campaign_watch_workload`,
`campaign_host_try_grow`): what the ledger promised other starts is no reason to end it. A head's "waiting for memory for a head step" line goes to stderr
(its stdout is often an artifact).

## Run the bug checks

A bug check is a real historical bug declared like a named case: a case directory (above) without
a `target.yaml`, whose tree marks the bug's throw with `@CausynthExceptionTarget("<case id>")`, run
as one campaign. A list of case ids, one per line, runs through `tools/adhoc/sweep.sh`: one
campaign per case, at most `heads-per-host` heads on each lift and every case's obligations on all
of them, every start through `fanout.sh` and the host ledger (§3.4); each case gets
`CASE_TIMEOUT_SECONDS` (5400 s by default) and `PRUNE=1`, and a sweep started again resumes. Give
a sweep its own `GC_OUT`, so that `findings.py` reads that sweep's cases only (the host ledger
stays the cluster's one):

```bash
cd ~/gc-run/p<N>        # a built snapshot of main (§3.4; a case on another tree, §3.7)
out=/bigtemp/vnr3ne/gc-out/checks-<round>
GC_OUT=${out} VM_IMAGE=/bigtemp/vnr3ne/vm-model-guards2/j2sdk-image setsid nohup \
  bash tools/adhoc/sweep.sh ~/gc-run/p<N> <round> <cases-file> 1 > ${out}-sweep.log 2>&1 < /dev/null &
GC_OUT=${out} tools/rounds/round-monitor.sh '<round>-*' | grep --line-buffered 'DONE '
GC_OUT=${out} python3 tools/adhoc/triage.py <round>         # class, stage, reason per case
python3 tools/adhoc/findings.py ${out} --ledger /bigtemp/vnr3ne/gc-out/findings/ledger.jsonl \
  --annotated experiments/<system> <tree>                    # confirmed witnesses by mechanism
```

Case `n` of the file writes `$GC_OUT/accept-<round>-<n>` (`sweep-<round>-cases.tsv` maps n to the
id); the sweep waits for head room by itself (a quiet log at the start is the ledger, not a hang).
`triage.py` classes each case: CONFIRMED, CONFIG_ONLY (confirmed, every moved root a
configuration), REFUTED (a real false positive: keep it), NO_ROOT, NO_WITNESS, STOPPED (stage and
reason), DEAD, RUNNING, PENDING. `findings.py` writes `findings.tsv`, one row per mechanism among
the confirmed witnesses (the target site, the finding kind and each moved root's kind, site, node
role and context), weighted by kind and native reproduction (REPRODUCE), the configuration-only
ones last; the ledger marks each new, known or dismissed (`dismissed.tsv` beside it), and
`--annotated` names the known bug whose marked throw a witness's campaign declared: a check that
found its own bug again. Hand-check every CONFIRMED witness against the code.

## Outputs

`accept.sh` and the round and sweep tools write `$GC_OUT/accept-<suffix>/`:

| path | holds |
| --- | --- |
| `summary.tsv`, `logs/<case>.log`, `report/<case>/{report.md,row.tsv,status}` | the verdict row, the campaign log, the readable report |
| `out/<case>/` | SEED's static artifacts: `static_scope_map.jsonl`, `scope_frontier.jsonl`, `region_skeletons.jsonl.gz`, `candidate_dataflow_edges.jsonl.gz`, and the recording under `runtime/` |
| `out/<case>/schedule/stage_metrics.tsv` | time per stage |
| `out/<case>/schedule/iteration-0000/` | `execution_task_plan.jsonl`, `concolic_region_plan.jsonl`, `recorded_schedule.jsonl`, `sessions/<id>/`, `obligations-<NNNN>/` (per planner round: one worker directory per obligation), `obligation_results.jsonl`, `exploration.json`, `witness-attempts/` |
| `…/sessions/<id>/` | one replay's rows: `activations`, `decisions`, `reads`, `writes`, `exports`, `attaches`, `roots`, `targets`, `gaps`, `schedule` (`.jsonl`), `expressions.jsonl`, `manifest.json` |
| `out/<case>/schedule/final/` | `result.json`, `claim.json`, `gaps.json`, `candidate.smt2`, `candidate_composition_manifest.json`, `confirm.json`, `reproduce.json`, `run-manifest.json` |

A flip query can be re-solved by hand with `z3 -smt2 obligation_query.smt2`.

## Repository map

```
run_engine.sh                     the campaign driver (every stage)
src/main/java/edu/uva/liftlab/graphchecker/
  causynth/    Soot pass: fatal slice, root catalog, door weave, weaving and its verification,
               region finalization, wire-flow catalog, declared-target line resolver
  plan/        static scope map, scope growth, task plan, declared sites, lineage scan,
               work-start and timed-wait shapes
  runtime/     recording and replay hooks, identity and attribution, schedule (ScheduleLog),
               mints, message and store doors (MessageDoors), focused replay, confirmation,
               VM broker
  explore/     corpus, closure, branches, frontier, flip queries, obligations, wave graph, ExploreMain,
               ConfirmMain
  compose/     Composer, families, SMT lowering, container codec, string identities, ClaimPolicy,
               ComposeMain
  contract/    row kinds, holes, wire declarations, identity types, gap registry, session layout,
               IMPORT gate, row pool
  smt/         expression IR, arms and families, z3 driver
  annotation/  Debug.makeSymbolicBoolean; @CausynthExceptionTarget (the trees' compile ABI only)
src/shim/java/                    the Hadoop shim (org.apache.hadoop.ipc.*) the HDFS trees call
src/test/                         unit tests; shell/run_engine_campaign_helpers_test.sh
third_party/OpenJDK-Concolic-Execution-Engine/   the concolic VM (hotspot/src/share/vm/concolic,
                                  interpreter/bytecodeInterpreter.cpp) and its smoke tests
experiments/lib/                  the one harness every case runs through
experiments/accept/               accept.sh, report.py, cone.py, probe.sh
experiments/hadoop/, experiments/solr/   per-system scripts and cases
tools/lib/                        gc-env.sh (GC_OUT, host ledger, LIFTS for every tool), alive.sh
                                  (which runs a process on any lift still names), heads.sh (a
                                  case's configuration, its head's weight and
                                  room, and which host heads it)
tools/rounds/                     launch, monitor and stop campaigns on the lifts; snapshot-gc.sh
tools/adhoc/                      sweep.sh (a list of cases over the lifts), fanout.sh, triage.py,
                                  findings.py
tools/regress/                    offline-ab.sh: the offline merge gate
tools/analysis/                   timeline.py (where a campaign's wall time went), rootcov.py (roots
                                  and symbolic predicates per campaign)
docs/STATUS.md                    done / partial / not done, per requirement; open defects
docs/design/                      the design of main (index: docs/design/README.md)
```
