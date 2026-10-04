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
stands, the current design (§0.4), which branches are in flight, what to do next, the owner's standing rules, how to run
agents in parallel, and how the servers and tools work. The capability inventory (done / partial
/ not done per requirement) is [docs/STATUS.md](docs/STATUS.md); the design of the code on
`main` is [docs/design/](docs/design/README.md).

---------------------------------------------------------------------------------------------------

## 0. Handover (state at 2026-10-03 night; every agent stopped, nothing running)

The lead session of 2026-10-02 night → 2026-10-03 (one lead, four coding agents A1/A2/A5/A6, read-only
reviewers) was stopped by the owner ("请你停止所有agent…全部清楚写到readme上去"). Every agent stopped its runs
and committed its finished work; the little that was uncommitted is saved under `/bigtemp/vnr3ne/handover/`
(§0.5). Nothing runs on any lift. Read §0.1-§0.7 in order, then §1-§3. The design of the code on `main` is
summarised in §0.4 and specified in [docs/design/](docs/design/README.md); what is done / partial / not done
per requirement is [docs/STATUS.md](docs/STATUS.md).

### 0.1 The goal (verbatim) and the owner's rulings since

The owner's active goal, verbatim (2026-10-02):

> 这是一个软件工程的学术项目，研究开源系统的稳定性。我是做system reliability研究的。请你设为长期记忆。请你阅读readme.md。理解当前的任务进度，并完成它。按照readme文档里建议的工作方式来进行。完成里面的todo。这个todo有一个不同，solr, hdfs里的adhoc check。请你去阅读～/bug_study下solr, hdfs的bug描述。相信你阅读完具体仓库的代码，你会很清楚我们在解决什么样的问题。如果solr, hdfs的文档里。请你选出里面确实是真实的，adhoc coordiaotin的bug（你要去system source code确认）。然后如果有，拿他们替换solr, hdfs里现在的adhoc check large scale。同理，请你clone hbase和zookeeper。在bug_study下的.txt找到hbase, zookeepr的高质量，并且优先选择在我们工具能力范围之内。能比较方便detect到的作为hbase, zookeepr的adhoc check。跑出因果链正确的.smt。 detect到他们。hbase和zookeeper也要像solr, hdfs一样。在一个branch里插入annotation。检查多个adhod check。请你先阅读graphchecker的完整代码，了解细节。你的整体设计要general，简洁。不要让代码变得过于臃肿

The 2026-10-02 night session restated it as a /goal: "阅读readme.md 按照里面声明的东西设为你的长期记忆，使用里面多agent协作的方式。
合理使用多agent handle子task。但是不要无限制地让子agent fan out。完成readme的todo。我建议你先阅读graphcheckr的source code，对细节有一个把控".

In short: the ad-hoc checks of HDFS and Solr are REPLACED by real ad hoc coordination bugs from
`~/bug_study/{HDFS,Solr}.txt` (each verified in the system's source); HBase and ZooKeeper become systems 3 and 4,
each with ONE tree branch carrying the adapter, the bugs' target markers (`@CausynthExceptionTarget`) and the
workloads; each check ends in a causally correct `.smt` that is SAT, confirmed, its chain checked by hand.

The owner's rulings (binding; also in §1):
1. **Symbolic scope is the top priority**, moderate and bug-driven ("适度支持吧…bug确实高质量…但是因为我们symbolic
   scope支持的不够。那你的symbolic scope就要改进了"): widen the scope GENERALLY for a high-quality bug out of reach;
   configuration values, shared-state re-pairing and request arguments are all in bounds, the first two preferred.
2. **The large-scale ad-hoc discovery pipeline is deleted** (done, V15).
3. **A self-written cluster test may be a bug's workload** when the bug is truly high quality; otherwise prefer
   the system's EXISTING unit tests as workloads (2026-10-02: "zookeeper, hbase这些worklaod尽量都利用已有的unit
   test。然后手动修改communication protocol。插hook。小的workaround手动改一点是允许的。但尽量general").
4. **IO rule**: a chain through file or HDFS-namespace state is not forced; protocol headers may be extended.
5. **Acceptance per bug**: a SAT `.smt` whose claim has the bug's mechanism, confirmed, chain checked by hand.
6. **Clean up everything unused** as you go.
7. **Every system on Java 1.8** ("整体system都要在java1.8版本上"; the VM is OpenJDK 8 Zero).
8. **Read the code before a fix or a design choice**, look further, decide from the whole ("做bug fix，design choice前。我建议你多阅读些已有代码，看的更远些，考虑整体").
9. **A long run usually hides a correctness bug; stop it at once and debug** ("用时过长的case往往都有问题…这种你一看就发现有问题。就不要盲目等待，及早停下开始debug").
10. **Second-tier bugs are dropped** (2026-10-03: "second tier bugs都先不管了。不用作为你的todo").
11. **The lead decides engineering questions without asking** (2026-10-03: "之后这种权限我都给你，刚刚这种不要再问…你对整体项目哪里可以小小workaround，哪里需要general更简洁已经有了自己很好的把控"):
    priorities, agent assignment, resuming parked work, merge order. Still the owner's: pushing, and changes
    to what the owner asked for (the bug checks, the recording window, what counts as a root).
12. **An early recording window for bugs whose fatal value is set during cluster startup** (2026-10-03, HBase
    #14: "ok。我同意option1，对于这类bug特殊处理一下"): an OPT-IN per case (`recording_window=startup`), never the
    default.

### 0.2 Where things stand

- **main** = this handover's docs commit on `3007804da` (the code round V25 ran), pushed to `origin/main` on
  2026-10-03 at the owner's request, together with the Hadoop fork's (`JHSUYU/hadoop`) `gc/hdfs-unified`,
  `gc/hdfs-unified-dtx`, `gc/hdfs-11741` and `gc/hdfs-bugs`. The ZooKeeper, HBase and Solr trees have no fork
  (their only remote is Apache upstream) and stay local, as do the branches of §0.5. Every change since
  the 2026-10-02 handover went in one at a time, each through a live round of all regression cases:

| round | snapshot | merged | result |
| --- | --- | --- | --- |
| V10, V11 | p222-p227 | `symbolic-scope` (configuration roots, root demand, scope growth) | 11/11, 7/7 |
| V12, V13 | | `system-zookeeper` + the recorded-address identity rule | quota-init fixed by the rule |
| V14 | p227 | `vm-streams` (java.util.stream model; image `vm-streams2`) | 12/12 |
| V15 | | `retire-adhoc-pipeline` | 3/3 subset |
| V16, V16b | p229 | `seed-functional` (stream pipelines and functional arguments in the SEED slice) | 12/12 |
| V17 | p230 | `preWindow-loop-root` (a hop names an unnamed region's occurrence; deciders as writers) | 12/12 |
| V18, V18b | p231 | `zk-election-offer` (ZooKeeper #05; serving-thread rule; anchor-only re-pairing) | 13/13 |
| PP1, PP1b | pp1 | `pairing-port` (11741 balancer race; DataTransfer doors; HDFS cases on the dtx tree) | 13/13, 11741 twice |
| V19 | p232 | `vm-model-guards` (no model records a condition; image `vm-model-guards2`) | 13/13 |
| V20 | p233 | `host-ledger-lease` (a start's charge holds for the JVM's life, by a lease) | 13/13 |
| V21 | p234 | `replay-address-only` + `readout-stream` (VM read-out pages streamed) | 13/13 |
| V22c | p236 | `hbase-identity` (a claim ends at its entry's exit; queue items carry the putter's scope) | 13/13 (V22 failed on a cross-node queue refusal, fixed) |
| V23 | p237 | `slice-matched-returns` (matched call/return in the SEED slice) | 13/13 |
| V24, V24b | p238 | `slowdisk-dev` (HDFS #15: INITIAL arm, ORDER-planted pairings, world re-pairing) | 14/14 |
| V25 | p239 | `replay-heap-bound` (no O(n²) per-window re-import; pages decoded as captured) + `launch-run.sh` on all lifts | 14/14 |

- **The fourteen regression cases**: the eleven named ones (hdfs-11741, 17897, 17899-bug1/2/3, 17960,
  17967-pathA/B/C, solr-18406, solr-18413) plus three bug_study checks: `zk-bugs-quota-init`,
  `zk-bugs-election-offer`, `hdfs-bugs-slowdisk-zero`. Typical wall time on a shared cluster: HDFS RPC cases
  6-12 min (up to 30 when the lifts are busy), 11741 25-40 min, 17960 11-14 min, solr-18406 15-20 min,
  solr-18413 20-25 min, quota-init ~10 min, election-offer 13-60 min (CONFIRM refutes false positives at 300 s
  each; `hb-schedule` cuts that), slowdisk-zero ~9 min. The HDFS RPC-fault cases move either direction of one IPC
  door from round to round (`Client$Connection#sendRpcRequest` / `Client#getRpcResponse`): the same chain.
- **VM**: main's image is `/bigtemp/vnr3ne/vm-model-guards2/j2sdk-image` (§3.1 lists all images).
- **Recordings run on stock HotSpot** (JDK 8); only replays run on the concolic VM.
- **Trees** (never rebuild one a run reads; each tree builds with its own Maven repo `/bigtemp/vnr3ne/m2/<name>`
  or the path given):

| tree (worktree) | branch, head | of | what |
| --- | --- | --- | --- |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-next` | `gc/hdfs-study-next` | `~/hadoop` | EVERY HDFS case but 11741 on `system/hdfs` from round HG2: `gc/hdfs-study` + node-startup brackets for automatic clusters (restarts by epoch), the startup window, weak adapter registries, the heartbeat tick on its NameNode, the IPC door naming its request's operation, HDFS-2 #09's workload removed; Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-next` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-verb` | `gc/hdfs-11741-verb` | `~/hadoop` | hdfs-11741 on `system/hdfs`: `gc/hdfs-11741` + the IPC door naming its request's operation; Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-verb` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study` | `gc/hdfs-study` | `~/hadoop` | round HG1's HDFS tree (branch `system/hdfs`): `gc/hdfs-unified-dtx` + bug #15's workload + the study's 51 ad hoc check markers (`hdfs-adhoc-NN`) + the MiniJournalCluster hooks + HDFS-2 #09's workload (`TestCausynthReencryptNegativeSleep`); Maven repo `/bigtemp/vnr3ne/m2/hdfs-study` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` | `gc/hdfs-unified-dtx` `51f1e058380` | `~/hadoop` | `gc/hdfs-unified` + the DataTransfer op's envelope: the base of `gc/hdfs-study`; main's eight named HDFS cases run it; Maven repo `/bigtemp/vnr3ne/wt/dtx/m2` |
| `~/hadoop-hdfs-11741` | `gc/hdfs-11741` | `~/hadoop` | hdfs-11741 |
| `~/hadoop-hdfs-unified` | `gc/hdfs-unified` `89f4c5348df` | `~/hadoop` | base of the dtx and bugs trees |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-bugs` | `gc/hdfs-bugs` | `~/hadoop` | HDFS #15 (`hdfs-bugs-slowdisk-zero`) on main; folded into `gc/hdfs-study` |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx-w6`, `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-w6` | `gc/hdfs-unified-dtx-w6` `93e481224d3`, `gc/hdfs-11741-w6` `9eb9b9bcf0c` | `~/hadoop` | for `wire-codec-p1` (W6-HDFS: IPC doors pass payloads, upstream SASL name); built, clean |
| `/bigtemp/vnr3ne/wt/lucene-solr-storing` | `gc/solr-unified-storing` `04f8489` | `~/lucene-solr-8_11` | solr-18406, solr-18413; `04f8489` = the per-collection refresh lock in `ZkStateReader` (the upstream race of §0.7) |
| `/bigtemp/vnr3ne/wt/lucene-solr-bugs` | `gc/solr-bugs` `f65aaf7` | `~/lucene-solr-8_11` | Solr #04 (`solr-bugs-reindex-cleanup`): target marker; `9d572a4` the same refresh lock (built); `f65aaf7` the `spelledAs` adapter (committed, NOT built: needs a jar with `MessageDoors.spelledAs`, i.e. `solr-bug-reindex`) |
| `/bigtemp/vnr3ne/wt/zookeeper-unified` | `gc/zk-unified` `8f18cf3a4` | `~/zookeeper` | ZooKeeper `branch-3.9` + adapter (`CausynthZk`, `CausynthZkCluster`), the zk-bugs targets, `CausynthQuotaRetryTest`; Maven repo `/bigtemp/vnr3ne/m2/zookeeper` |
| `/bigtemp/vnr3ne/wt/zookeeper-hb` | `gc/zk-unified-hb` `f334025ee` | `~/zookeeper` | for `hb-schedule`: + a RESPONSE door (FinalRequestProcessor reply → caller); Maven repo `/bigtemp/vnr3ne/m2/zookeeper-hb` |
| `/bigtemp/vnr3ne/wt/hbase-unified` | `gc/hbase-unified` `8b83a08afc` | `~/hbase` | HBase master backported to Java 8 + adapter (`CausynthHBaseCluster`, `RPC.proto` causal context, `CausynthRpc`/`ServerCall`/`CallRunner`) + #14's target; the startup window; lifts the mini cluster's 30 s master limits; built against the `hbase-startup` jar (Maven repo `/bigtemp/vnr3ne/m2/hbase`); native 3/3 |

- **Regression outputs kept**: `/bigtemp/vnr3ne/gc-out/accept-V1[0-9]*-*`, `accept-V2[0-5]*-*` (V24/V25 are the
  newest all-pass rounds), `gc-out/pairing-port/accept-PP1*`; agents' runs under
  `gc-out/{solr-bugs,zk-bugs,hdfs-bugs,slowdisk-dev,hb-schedule,wire-codec,hbase-bugs,...}/`;
  `gc-out/evidence/` (real false positives; `solr-bugs/evidence/` the ZkStateReader-race jstacks).
- **Snapshots** `~/gc-run/`: p222-p239, pp1, sb19, hba2, w6c1-w6c4, zk1, zk5-5, zk5-6, zk7, zk9, hb1, sp1.
  Keep p238/p239 (V24/V25) and the agents' newest (sb19, w6c4); the rest may go with
  `tools/rounds/snapshot-gc.sh` (it refuses a snapshot a process names).

### 0.3 The bug_study verdict: 60 bugs, what qualifies

Four read-only investigators read every bug against the source; the lead read every pick's code. All 60
defects are real in the studied versions except Solr #10 (absent in 8.11), ZooKeeper #14 (master only) and
HBase #13 (not in 2.6). A pick is a real ad hoc coordination bug, high quality, with a chain that stays in memory
(IO rule) and a single counterfactual GraphChecker can plant (a door fault, a clock, a configuration value, a
re-pairing) from a run of a passing cluster test.

**Picks** (case ids `<experiment>-<arg>`; each tree marks the throw with that id):

| case id | bug | fatal throw | counterfactual | workload | state |
| --- | --- | --- | --- | --- | --- |
| `zk-bugs-quota-init` | ZooKeeper #01: `SetQuotaCommand.createQuota` creates the limit znode, then the stat znode; a lost reply of the limit create → the retry takes the update branch → `getData(statPath)` NoNode; meanwhile `checkQuota` sees no stat and returns: the hard quota is silently off | server NoNode guard, `FinalRequestProcessor.handleGetDataRequest` (~:703) | ZooKeeper WRITE door fault on the limit `create` | `CausynthQuotaRetryTest` (self-written) | **PASS**, regression case since V12 |
| `zk-bugs-election-offer` | ZooKeeper #05: `LeaderElectionSupport` lists offers (`getChildren`) then `getData`s each; a competitor's concurrent `stop()` deletes its offer → NoNode → `start()` goes FAILED and never deletes its own offer, blocking every later candidate | the same NoNode guard, via `toLeaderOffers` (LES ~:310) | STATE re-pairing: the server's node-map lookup re-paired to the competitor's delete (`assoc_remove`) | `LeaderElectionSupportTest#testOfferShuffle` | **PASS**, regression case since V18: the first confirmed STATE_PAIRING witness |
| `hdfs-bugs-slowdisk-zero` | HDFS #15: `DataNodeDiskMetrics`' detector replaces `slowDisksToExclude` only `if (maxSlowDisksToExclude > 0)` (~:151); reconfiguring max to the documented "disabled" 0 never clears a published list; `FsVolumeList` filters the only SSD out | `RoundRobinVolumeChoosingPolicy.chooseVolume` `DiskOutOfSpaceException` ("No more available volumes") | STATE re-pairing to the INITIAL: a detector turn reads max before the reconfiguration (1) and publishes [SSD] | `TestCausynthSlowDiskZeroMax` (self-written; no existing test reaches it) | **PASS**, regression case since V24 (chain: INITIAL 1 vs reconfig 0 → `max > 0` → `limit(max)` store → `chooseVolume` read → `size() < 1`) |
| `solr-bugs-reindex-cleanup` | Solr #04 on 8.11: a same-target REINDEXCOLLECTION creates its alias `X -> .rx_X_n` (RCC ~:444); any failure after it runs `cleanup` (~:773), whose DELETE of the target throws in `DeleteCollectionCmd.checkAliasReference` (~:245) on that alias; no try/catch, so the source's read-only reset (~:810) never runs | DCC ~:245 "is part of aliases" | a ZooKeeper (or HTTP) door fault after the alias step, e.g. `setData` of the reindexing state | `ReindexCollectionTest#testSameTargetReindexing` | **not yet**: branch `solr-bug-reindex` (§0.5) fixes replay fidelity; no witness yet (the post-alias doors never got verdicts: SB12-SB14 queue starvation, SB16/SB18/SB19 recording hang and seed-replay bound, all fixed on the branch) |
| `hbase-bugs-master-active-time` | HBase #14: `HMaster.masterActiveTime = EnvironmentEdgeManager.currentTime()` (~:986) travels with remote procedures; `MasterRpcServices.throwOnOldMaster` (~:2620) refuses a report whose initiating time exceeds the current master's: wall clocks compared across masters as an epoch | `throwOnOldMaster`'s `MasterNotRunningException` | CLOCK: the OLD master's activation clock runs fast; its value crosses old master → RS → new master | `TestSplitWALProcedure#testMasterRestart` | **in progress**: branch `hbase-startup` (§0.5): the owner-approved startup window, per-waiter WAKE count; HBA2 (old design) died in the seed replay |

Second tier: dropped by the owner (ruling 10). **Rejected, by reason**: deterministic API-sequence or argument
bugs (HDFS #01, 02, 03, 06, 08, 13, 14; Solr #11, 13, 14; ZooKeeper #12; HBase #08); need a reconfiguration plus an
out-of-band disk change or a test spy (HDFS #04, 05, 09, 10; HBase #06, 09); chains through file/HDFS-namespace
state (HBase #03, #05, #10, #11, #15; Solr #01); several flips or a thread schedule at once (HDFS #12, ZooKeeper
#04, 11, 13, 15; Solr #15); the throw is the fault's echo (ZooKeeper #06); invalid operator input only (HDFS #11);
contrib REST (ZooKeeper #09, 10); needs an extra admin action (ZooKeeper #07); client-tool static flag (HBase
#02); string/enum config with a ZooKeeper watch chain (HBase #04, #07).

### 0.4 The current design (what `main` does, stage by stage)

A campaign (`run_engine.sh campaign`, driven per case by `experiments/accept/accept.sh`) runs SEED → PLAN →
INSTRUMENT → REPLAY → IMPORT → EXPLORE (rounds of obligations, each a focused replay) → COMPOSE → CONFIRM → EMIT →
REPRODUCE. Specs: [PIPELINE.md](docs/design/PIPELINE.md) (stages, campaign driver, ledger),
[IDENTITY.md](docs/design/IDENTITY.md) (occurrences, attribution, schedule), [SYMBOL-SCOPE.md](docs/design/SYMBOL-SCOPE.md)
(what becomes symbolic), [CONTRACT-SPEC.md](docs/design/CONTRACT-SPEC.md) (rows), [VM.md](docs/design/VM.md).

1. **SEED: the static slice and the recording.** `causynth/SeedBackwardStaticAnalyzer` slices backward from the
   declared throw's guards (Soot). Library calls are followed by contract: container queries and mutations,
   accessors, stateful receivers, clocks, `java.util.stream` pipelines and functional arguments (the slice enters
   a lambda's body and its captures). A callee formal that only its return needs is demanded only at call sites
   whose result is demanded (`causynth/ReturnOnlyFormals`, matched call/return; a formal that becomes an effect
   re-queues every caller that met it). Roots come by category, never per case (`RootCatalog`: CLOCK, FAULT
   markers at woven doors, HOOK, READ placeholders, CONFIG keys via `ConfigRoots`); `RootDemand` walks back from the
   target's guards to the nearest boundary of each class; scope growth adds classes to a budget and stops at a
   declared codec. The recording runs the workload on stock HotSpot with the woven trace recorder
   (`runtime/CausynthTraceRecorder`): regions, occurrences, the schedule (`ScheduleLog`: START/CLAIM/SEND/RECV/WAKE
   events keyed (kind, context, site, k)), the window opened by each system's cluster adapter once the cluster is
   up.
2. **Identity.** An occurrence is (node, region, context, index). A context is a Root (a tick, a client step,
   a WAKE turn), an Anchor (the producer endpoint of the message it serves) or Lost; the index is the frame
   path from the root with per-site invocation counts; nested regions fold into the enclosing occurrence. Nodes
   are registered by each system's cluster adapter (`MessageDoors.registerNode`); a thread belongs to a node by
   the attribution rules (explicit scope, a registered object on its frames, inherited source, its starter's
   reference). Claimed work (executor tasks, queue items) is keyed by the START it claims and carries its
   putter's scope; a work entry's claim ends at its exit. A hop names a region standing unnamed. An activation
   at an address the recording opened answers no other question.
3. **PLAN** (`RuntimeSelectedRegionFinalizer`, `DemandWalk`) plans the occurrences the seed replay captures: the
   closure around the declared target `(r,c)`, crossing a stored field to the occurrences that ran its store or
   decided against it where something the engine moves reaches the guard. Over `schedule_max_jobs` the nearest
   whole demand depths are kept and the rest named `PLAN_CLOSURE_CUT`.
4. **INSTRUMENT** weaves the region hooks, message doors (FAULT markers on both directions of every door), loop
   bounds, random draws and timed waits into the case's classes (Soot), verified by the JVM verifier.
5. **REPLAY** runs the workload on the concolic VM (OpenJDK 8 Zero, `third_party/OpenJDK-Concolic-Execution-Engine`):
   every value carries a symbolic expression (shadows on slots, fields, objects; JVM-level, never byte-level);
   containers are modelled as ASSOCIATIVE/INDEXED chains (`ContainerExpression`), a muted body's choice as a guard
   on its chain; shared fields keep version logs (INITIAL/WRITE/RMW/STATE) so a read states the write it saw.
   The schedule prefix of the recording is enforced (`ScheduleLog`): every event waits for its slot; the stall
   rules release what the run will not make (a waiter passes what its flow did not make, a settled cause, a
   response once its request ended, a watchdog give-up after 15 s); WAKE turns are never sooner than recorded.
   Read-out pages stream to the publication thread as they are captured; a branch window skips expression
   nodes already imported.
6. **IMPORT** checks the row invariants and publishes the seed session.
7. **EXPLORE** (`explore/`): `ClosurePlanner` turns the closure into tasks (a focused occurrence plus its
   state-connected factor); `ObligationFactory` proposes flips of a task's recorded paths (fault decisions first,
   at most `maxFlipsPerPath` per path per round, worlds nested at most 3 flips deep); `FlipQuery` asks z3 for
   the nearest world (roots, clock skews, handoff answers, writer choices `wchoice_*` including a location's
   INITIAL); a SAT model becomes an obligation replay that plants that world (root values at their mints, clock
   skews, answered handoffs, and a moved writer choice by CONFIRM's ORDER rows, held until the reader's
   occurrence closes) and checks that the flip was taken (ADMITTED / NOT_ADMITTED by name / UNSAT). A flip whose
   predicate rests only on recorded facts is refused. A replay that observes the fatal at the declared
   occurrence ends exploration (the first witness).
8. **COMPOSE** (`compose/Composer`, `SmtLowering`, `ContainerSmtCodec`) builds one formula over every admitted
   session: per message and per shared-state read a family of writer arms (`writer_arm_*`, exactly one), each
   arm guarded by the path condition of the occurrence that produced it; a read may be re-paired when the anchor
   made it or the selected session's world planted a pairing on it (one entry point); eligibility is one rule
   (`Arms#eligible`: the observed writer, an INITIAL where every write in between is HB-concurrent and none a
   constructor's, and other HB-concurrent writers); a value nothing moves is pinned by one predicate
   (`SmtLowering#moves`) shared with EXPLORE. Claims: MARKER_FLIPPED (a fault or configuration marker moved),
   CLOCK_SKEW (a clock moved), STATE_PAIRING_FLIPPED (only a pairing moved: `repairedArms`), each with
   `polarityDecides` (the recorded valuation is UNSAT, the witness SAT). A codec value crosses by its LEAF/
   PROTOBUF template (round-trip contract on `wire-codec-p1`).
9. **CONFIRM** replays the witness world from the recording, holding the chosen edges (ORDER of writers, STATE
   pairings incl. INITIAL, WIRE deliveries) and checks that the anchor observes the fatal; strict: every
   substitution (a producer that answered the question) is named; a session counts as "itself the run" only if
   its world plants no pairing.
10. **EMIT / REPRODUCE**: `candidate.smt2`, `claim.json`, `confirm.json`; native runs that plant fault markers
    (a pairing or clock world reports NATIVE_PLANT_UNSUPPORTED). Acceptance: `experiments/accept/report.py`
    (+ `cone.py`: the moved roots in the witness cone).
11. **The campaign driver** (`run_engine.sh`): a head per case drives the stages; heavy steps go wherever the
    host ledger has room; obligations stream over every host in `LIFTS` (`campaign_stream_*`; optional cap
    `CAUSYNTH_STREAM_MAX_IN_FLIGHT`). The **host ledger** (`$CAUSYNTH_HOST_LEDGER`, `/bigtemp/vnr3ne/gc-out/hosts`):
    a start goes only where the host's live charges and its real use both stay within 70% of MemTotal; a charge
    is a file whose mtime is a 120 s lease renewed by the JVM's watcher, so a killed run's charges lapse.

**Designs on branches, not on main yet** (§0.5): a per-session happens-before relation replacing anchor ancestry
(`hb-schedule`) plus signal and store-notification edges (`hb-sync`); the Solr replay-fidelity set (a store
write's turn before the call, stall/release rules, recorded random draws, a focused replay that concludes once
its question closed, the explore queue's cap/dispatch rules, `RECORDING_STALLED`) on `solr-bug-reindex`; the
WIRE-CODEC W3/W6 codec ports and envelopes on `wire-codec-p1`; the opt-in startup window on `hbase-startup`.

### 0.5 Branches in flight (heads at the stop; WIP = uncommitted, saved under `/bigtemp/vnr3ne/handover/`)

Merge order (one per live round, each after its pre-merge review is clean, §2): **`solr-bug-reindex` →
`hb-schedule` → `hb-sync` → `wire-codec-p1` → `hbase-startup`** (`replay-heap-bound`'s docs commit any time).
Every branch below is committed, built, unit- and shell-tested unless it says otherwise.

| branch (worktree) | head (base) | content | state / next step |
| --- | --- | --- | --- |
| `solr-bug-reindex` (`.claude/worktrees/agent-a6cdfa854234df67e`) | `28cf76a45` (main `32057d44b` merged in) | Solr #04 case `solr-bugs-reindex-cleanup` (selector `#1`, two declared loop bounds, `schedule_max_jobs=64`) and Solr replay fidelity as ONE change: recorded random draws keyed by the schedule's stance (`Randoms`, `ScheduleDraw`), the stall rule set (6ff0134d9, ef20dfdbc, 35cdd1e6b), a LATE state for watchdog give-ups, the lock-owner early release (named `schedule-reversed` when a waiting writer holds a lock another thread blocks on), a store write's turn BEFORE the ZooKeeper call keyed by its location in run-stable names (`ffb7afcf6`; session ids and ports become node names via `MessageDoors.spelledAs`), `AT_QUESTION_CLOSED` (a focused replay concludes once every started focused/factor member and pairing consumer published), the explore queue (a path's cap counts arms waiting to start; dispatch round → world size → stable demand rank), region roots dropped only for pure accessors, `RECORDING_STALLED` (trace/stdout silent 600 s → jstack + named end), `launch-round.sh` forwards `CAUSYNTH_STREAM_MAX_IN_FLIGHT`; 161bdff92 (CLAIM keyed by its START) | review (13 items) fixed and committed; its offline gate on V24 was cut at the stop: SEED+PLAN pass on all 14, IMPORT…CONFIRM never ran. Next: rerun `/bigtemp/vnr3ne/ab/sbr-review/gate.sh` (jars `main-7da26b96e` vs `solr-bug-reindex-28cf76a45`), merge main, build the bugs tree with `f65aaf7` once nobody reads it, the storing tree's `spelledAs` adapter after the merge (`/bigtemp/vnr3ne/gc-out/solr-bugs/agent-tools/spelledAs-adapter.patch`), then the live round of the 14 + `solr-bugs-reindex-cleanup` (the witness: #2's post-alias `setData` doors) |
| `recording-stall-guard` (`/bigtemp/vnr3ne/wt/gc-recording-stall-guard`) | `fc26fd6e7` (main `48c76f9b9`) | `RECORDING_STALLED` alone (cherry-pick of `solr-bug-reindex`'s) | delete once `solr-bug-reindex` merges (same content) |
| `hb-schedule` (`.claude/worktrees/agent-aea16c87adafb5d81`) | `1fb4a475a` (main `32057d44b`) | one per-session happens-before relation (`smt/HappensBefore`, sparse vector clocks over `schedule.jsonl`; new event fields `handoff`, `thread`, `event` = the VM clock; rows join by VM event id) REPLACES anchor ancestry (`Arms#concurrent/#ancestor/#chainKnown/#sameThread` deleted); program order per served request; SEND→RECV, START↔CLAIM, request/response pairs; unknown stays ordered; a ZooKeeper RESPONSE door (tree `gc/zk-unified-hb`) | live: zk-election-offer CONFIRM refutations 7→1 (3608 s → ~1600 s), quota-init PASS. Its review fixes are on `hb-sync`. Merges after `solr-bug-reindex` (rebase; make `ScheduleReach` read the claimant from the CLAIM's own context/thread) |
| `hb-sync` (same worktree) | `92a151697` (on `hb-schedule`) | non-slot `sync` give/take rows (`ScheduleSync`); signals as handoffs (`Syncs`: a notify/signal's per-signal key to the wait it woke; a latch's countDowns to its await; a work's end to `join`/`Future.get`); the store→notification `take` at the unawaited receipt (the first-row inference deleted); CONFIRM's question rule (`Confirmation.Question`, ONE gate shared with WIRE: substitute only when the model's own address never ran and exactly one candidate answers, held to the model's value); review B1 (a claim's program order split by request), B2, B3, #4 (a message key includes its attempt), #6 (claimed order key carries the thread id) | review fixes committed; still open: #5 (ZooKeeper takes a reply only when `readResponse` got it, uncommitted in `/bigtemp/vnr3ne/wt/zookeeper-hb`, saved `handover/zk-unified-hb-wip-2026-10-03.patch`), #7 docs (README/STATUS wording), NITs 8-10 (VM id 0, seq-0 in `before()`, `toString` javadoc). Then the offline gate on V24 and a live run of both ZooKeeper cases + hdfs-11741, comparing arm counts with main (B3 may now refuse 11741's WIRE substitution and Z4's renumbered delete: check those first) |
| `wire-codec-p1` (`.claude/worktrees/wire-codec-p1`) | `3e9cb3182` (main `32057d44b`) | WIRE-CODEC as one HDFS change: c90ccee00's codec boundary in the one catalog reader, W3 codec ports by rule (`CodecPortRule`, `CodecKeyIndex`), W6-HDFS (`experiments/hadoop/wire.jsonl`, IPC doors pass payloads, the HDFS WIRE_FLOW rows deleted), the LEAF round-trip contract (`codec_roundtrip__*` named assertions), the offline gate's codec declarations, CSE7 envelope compaction (a producer stated once per message), `CodecRuntime#occurrenceHere` under the door's carried scope, a dropped hole makes the claim INCONCLUSIVE + BLOCKING (never UNSAT_CLOSED); trees `gc/hdfs-unified-dtx-w6`, `gc/hdfs-11741-w6` (built); WIP `handover/wire-codec-p1-wip-2026-10-03.patch` = the untracked `tools/regress/offline-ab-fresh.sh` (a gate whose later stages read each side's own fresh slice) | canaries: 17897 PASS (chain checked); 11741 had 0 envelope drops in its seed and dn1 pairs the key fields, but no verdict yet (W6C4 local-only, W6C5 stopped). Next: rebase onto main, relaunch 11741 + 17897 through `launch-round.sh`, chain check (does EXPLORE focus nn0's key-roll occurrence? many `addKeys#u21` refused as ADMISSION_GAP: confirm it is the no-variable refusal), offline gate, then its round |
| `hbase-startup` (`/bigtemp/vnr3ne/wt/gc-hbase-startup`) | `275f58abd` (main `32057d44b`) | HBase #14: `system-hbase`'s harness and interface-delegate clock rule (8691e378c), the per-waiter WAKE count (8b55037c5), the opt-in `recording_window=startup` + node-startup brackets (`MessageDoors.beginNodeStartup(kind, role, sourceId)` for a construction, `beginNodeStartup(node)` for a registered node's thread start, `endNodeStartup(token)`) | not gated (its gate was stopped part-way, `/bigtemp/vnr3ne/ab/hbase-startup-5d81654e0`); HBA2 (older design, snapshot `~/gc-run/hba2`) died in the seed replay ("Master not active after 30000ms", 8 schedule stalls). Next: snapshot `275f58abd`, offline gate on V24, HBA3 to IMPORT; the expected blocker is that the OLD master's activation is not planned, so its time has no path to the target |
| `replay-heap-bound` | `a20dd5a59` | = `066371dfd` (merged, V25) + a docs commit (STATUS open item: the once-per-channel VM dedup with its numbers) | merge the docs commit any time |
| `replay-heap-bound-store` | `503432bf0` | a per-activation expression store (made the heap blow up) | parked; delete unless the VM dedup revives it |
| `state-pairing` | `aa961ff78` | the source of `slowdisk-dev`'s INITIAL port | delete (merged in content, V24) |
| `fix-hdfs-seed-stalls` | `bfd7492bd` | superseded by `solr-bug-reindex` except `a85c60a9a`/`5b871ae0e` (a DataNode turn numbered by the DataTransfer op it took in) | port those two after `solr-bug-reindex` merges, then delete |
| `fix-no-root` | `2e931192e` + WIP `handover/fix-no-root-hb-edges-wip*.patch` | NO_ROOT fixes (carried by `state-pairing`) + an HB-edges WIP (superseded by `hb-schedule`) | delete with its worktree `agent-a5fe8997…` |
| `system-hbase` | `11ddd06e1` | contained in `hbase-startup` (8691e378c) | delete once `hbase-startup` merges |
| `perf-vm-readout`, `vm-ref-compare` | `3cbea0bee`, `bba1ee25d` | VM read-out per activation; reference compare with an enum constant (TODO 1(d)'s starting point) | parked; each needs a VM review (images `vm-w4i`, `vm-nr41`) |
| `worktree-agent-a49c8bf5715a00c40` | `90ca7724e` | the original WIRE-CODEC W3/W6 work | superseded by `wire-codec-p1`; delete when it merges |
| merged and kept for now | | `system-zookeeper`, `vm-streams`, `seed-functional`, `preWindow-loop-root`, `zk-election-offer`, `pairing-port`, `vm-model-guards`, `host-ledger-lease`, `replay-address-only`, `readout-stream`, `hbase-identity`, `slice-matched-returns`, `slowdisk-dev`, and the round candidates `main-sf`, `main-pw`, `main-eo`, `main-pp`, `main-vg`, `main-ll`, `main-v21`, `main-v22`, `main-v22c`, `main-v23`, `main-v24`, `main-v25` | all contained in main; delete at the next cleanup (`main-v22` = the failed V22 candidate) |

Archived and deleted 2026-10-03: `pairing-on-main`, `dtx-on-main`, `fix-11741-pairing` (`handover/archived-branches-2026-10-03b.bundle`),
`replay-random-draws`, `fix-replay-equivalent-context` (their own bundles); `perf-expr-store` (measured, no effect).
Earlier deletions: §0.2 of the 2026-10-02 README (git history).

### 0.6 TODO, in order

1. **Merge the in-flight branches, one per live round** (§0.5 order). For each: finish the open review items,
   offline gate on the newest all-pass round (V24/V25 recordings), a frozen snapshot, a live round of the 14
   regression cases (plus the branch's own case), `.smt` chain checks of the cases it touches, then main.
2. **Solr #04 (`solr-bugs-reindex-cleanup`) to a confirmed witness** after `solr-bug-reindex` merges (SB20): the
   post-alias ZooKeeper door faults of the declared REINDEX (#2). Expected: the alias exists → cleanup's DELETE
   throws at `checkAliasReference`. Check that happens-before (`hb-schedule`/`hb-sync`) orders the test's later
   sub-tests after #2 (store→notification + latch edges); if not, they stay concurrent writers (completeness
   allows it; cost only).
3. **HBase #14** on `hbase-startup` (HBA3): plan the old master's activation (its `masterActiveTime` clock read
   now inside the window), its value crossing old master → RS → new master through the HBase protobuf ports.
4. **WIRE-CODEC (TODO 6)**: `wire-codec-p1`'s 11741 canary verdict and chain check, then its round; P3 (Solr
   `wire.jsonl`, 18406/18413/reindex-cleanup) after `solr-bug-reindex`; P4 retires the WIRE_FLOW machinery.
5. **TODO 4 leftovers**: `fix-hdfs-seed-stalls`' two DataTransfer-turn commits after `solr-bug-reindex`.
6. **Performance** (measured, queued): the VM sends each expression node once per channel (STATUS open item;
   SB19: 125 MB of branch windows, pages decoded at 0.39 MB/s, 418 s waiting at the bound); a plan budget
   derived from the seed's measured cost instead of a fixed `schedule_max_jobs`.
7. **TODO 1(d)**: run-time reconfiguration values and String/enum configuration as roots, only when a pick needs
   them (`vm-ref-compare` is the starting point).
8. **Cleanup**: delete the merged branches and candidates (§0.5), stale snapshots (§0.2), the parked branches'
   worktrees, `/bigtemp/vnr3ne/readout-stream/` (4.2 GB measurement data) once its numbers are in STATUS.

### 0.7 Open problems

| class | state |
| --- | --- |
| Happens-before knows only anchor ancestry + one thread on main: sequential requests of one test thread through a queue look concurrent (Solr #04: 105 of 137 obligations on later sub-tests), CONFIRM refutes such false positives at 300 s each | `hb-schedule` + `hb-sync` |
| An upstream Solr race: `ZkStateReader` lets a stale fetch resurrect a deleted collection (each watch event on its own pool thread, nothing orders fetch vs apply; still on Solr main, cf. SOLR-12544); under `CausynthBounds` a delete's `waitForState` hangs forever | worked around in both Solr trees (per-collection refresh lock); a real bug the harness surfaced |
| Replay fidelity for Solr: ZooKeeper writes admitted only after they ran, so writes to one path raced and elections flipped | `solr-bug-reindex` (store-write turn) |
| A focused replay runs to the workload's end even once its question closed | `solr-bug-reindex` (`AT_QUESTION_CLOSED`) |
| Seed replays near their bound on large Solr tests (concolic compute in `CreateCollectionCmd` loops; single-thread page decoding) | `replay-heap-bound` merged; the VM dedup queued (§0.6 item 6) |
| Values set before the recording window (cluster startup) are no roots | opt-in startup window on `hbase-startup` (owner ruling 12) |
| DataTransfer ops carry correlation only (no values) | by decision until a pick needs their values |
| A value crossing a file, a stream with no door, or HDFS namespace state is lost | IO rule: such bugs are not picked |
| UNPRODUCIBLE_ANSWER (an IPC answer resting on an unstated value) | seen once on `dtx-on-main`, not traced |
| Enum constant compared by reference | `vm-ref-compare`, parked |

Designs and analyses outside the repo: the code maps `/bigtemp/vnr3ne/analysis/codemap-2026-10-02/` (00-contract …
07-vm, 08-hdfs15-design; each ends with design notes); `/bigtemp/vnr3ne/specs/WIRE-CODEC-proposal.md` (its
decisions bind), `R1-ROOTS-proposal.md`, `R3-REFCONT-proposal.md`, `R3-shapes.md`, `C2.md`, `F14.md`, `DOCS.md`;
the owner's requirements R1-R6 `/bigtemp/vnr3ne/analysis/audit/COMMON.md`; the tree inventories
`/bigtemp/vnr3ne/analysis/unify/`; the bug descriptions `~/bug_study/*.txt`; WIP patches and branch bundles
`/bigtemp/vnr3ne/handover/`.

---------------------------------------------------------------------------------------------------

## 1. The owner's standing rules (long-term; they override defaults)

The owner is a PhD student doing academic research on open-source system stability. Reply to the
owner in **Chinese**, answer a direct question first (before continuing the work), keep answers
short. The design decisions are the lead's (the agent coordinating the work), made after reading
the code; implementers follow a written design. **The lead decides engineering questions without
asking** (priorities, which agent takes what, resuming parked work, merge order: "之后这种权限我都给你，
刚刚这种不要再问"), acts, and reports what it decided. Decisions that change what the owner asked for
(the bug checks, the recording window, what counts as a root) and pushing go to the owner with a
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
- **Java 1.8 for every system** ("整体system都要在java1.8版本上"): every tree and workload builds and runs on JDK 8
  (the VM is OpenJDK 8 Zero); verify it first in a new system's feasibility phase.
- **Workloads are the system's existing unit tests where possible** ("zookeeper, hbase这些worklaod尽量都利用已有的unit
  test。然后手动修改communication protocol。插hook。小的workaround手动改一点是允许的。但尽量general"): search the test tree
  first; protocol headers and hooks may be added by hand; a self-written test only when no existing test
  reaches the bug (say why in STATUS).
- **An early recording window is opt-in per case** for a bug whose fatal value is set during cluster startup
  (`recording_window=startup`, HBase #14; owner 2026-10-03); every other case keeps the window opened once the
  cluster is up.
- **Second-tier bugs are not a TODO** (owner 2026-10-03).

**Engineering**
- **General fixes only.** No per-case code, no fixes derived from a case's expected verdict, no
  dead code, no fallback paths, no flags to keep an old path. Per-system code is allowed only as a
  small adapter or a declaration row, listed in STATUS "Per-system surface". Every stop/skip rule
  and every performance optimization is general.
- **Global view, read before you decide:** read all the code a concept touches (every stage) before
  a fix or a design choice, look further, decide from the whole ("做bug fix，design choice前。我建议你多阅读些
  已有代码，看的更远些，考虑整体"); fix the class of bug, not the instance. Docs may be stale — the code and
  the owner's current requirements are the reference. Verify a diagnosis in code before briefing an agent
  with it (this lead's wrong guesses cost hours: a VM image blamed for a hang that ran on stock HotSpot, a
  memory charge misread).
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
- **A run that looks wrong is stopped at once and debugged, never waited out** ("用时过长的case往往都有问题…
  就不要盲目等待，及早停下开始debug"): a log silent for minutes, a stage far beyond its usual time, a host over its
  memory gate. Take a jstack, read the schedule and the ledger, name the cause in code. 2026-10-03 examples:
  a recording hung on an upstream Solr race; ZooKeeper writes admitted after they ran; an O(n²) re-import; a
  canary confined to one host.
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
- **3–4 coding agents at once** (the owner's budget: "不要无限制地让子agent fan out"; seven at once burned the weekly
  usage limit in two hours on 2026-10-02) plus short read-only reviewers; no agent spawns sub-agents; ask for short reports (≤ 15–20 lines);
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
- Keep a short state note current for yourself (the 2026-10-03 lead used
  `~/.claude/projects/-u-vnr3ne-GraphChecker/memory/lead-session-2026-10-02d.md`, one dated paragraph per
  milestone), and keep README §0 current: a docs commit after every merged round.

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

**How the 2026-10-03 lead ran the agents** (one lead, four coding agents, six reviewers; rounds V16-V25,
eleven merges into main, none reverted)
- **Four coding agents at once, each owning one area for the whole session:** A1 (STATE pairing for HDFS #15,
  then happens-before), A2 (Solr #04 and Solr replay fidelity), A5 (ZooKeeper #05, `pairing-on-main`, the
  ledger lease, the slicer's matched calls, WIRE-CODEC), A6 (VM: streams, model guards, read-out streaming, heap;
  then HBase). Continuing an agent in its area by `SendMessage` kept its context; new areas went to whoever freed
  up first. No agent spawned sub-agents (one reviewer did; tell reviewers "do NOT spawn sub-agents").
- **Design before code for anything that changes identity, the schedule or what is symbolic:** the agent reads
  the code and sends a ≤ 20-line design; the lead approves, adjusts (often "one mechanism, not two: reuse X"),
  or rejects; only then code. Agents also stop and ask when their own diagnosis turns out wrong (A5 did, twice:
  each time the corrected cause was different and the planned fix would have done nothing).
- **A pre-merge review agent for every soundness/schedule/VM batch** (vm-model-guards, slowdisk-dev,
  slice-matched-returns, solr-bug-reindex, hb-schedule + hb-sync): read-only, briefed with the owner's principles
  (completeness first, CONFIRM strict, one mechanism), ≤ 40 lines, blockers first, file:line and a concrete
  scenario each. Every one found real blockers that the offline gate and the live runs had passed (a vacuous
  INITIAL check, a CONFIRM rule looser than WIRE's, false orders that silently drop alternatives, declared target
  regions dropped by a root rule). The author fixes them all; the lead decides the disputed ones.
- **Merges in a dedicated worktree** `/bigtemp/vnr3ne/wt/main-pw`: per round a branch `main-<x>` from main, `git
  merge --no-ff` the change, resolve conflicts by hand (two implementations of one concept become one interface),
  `mvn -q -o package` + shell test via `onlift.sh`, commit, `git worktree add --detach ~/gc-run/p<N>`, build it,
  `launch-round.sh` all regression cases, a `Monitor` on `round-monitor.sh`; on all-PASS fast-forward `main` to
  the candidate, then a README/STATUS docs commit for that round.
- **Canaries before a full round** for large changes (WIRE-CODEC: 11741 + 17897 first), always launched through
  `launch-round.sh` (all ten lifts).
- **Watch the agents' runs as well as your own:** read their logs when a stage is long; three of the session's
  biggest finds came from the lead checking a run that "was still going" (SB16's hung recording, SB11's memory
  overload, a canary on one host).

**Lessons from 2026-10-03**
- **Strict is not broad.** Tightening CONFIRM ("only a world that plants nothing is itself the run") forced
  replays for nine passing cases for no soundness gain; the reviewer caught it. Check which existing cases rely
  on a path before tightening it.
- **Narrowing roots needs the declared targets in view:** "region roots only at writers" would have dropped
  11741's target region and the clock regions.
- **Every false happens-before order silently drops real alternatives** (a completeness loss no gate shows):
  test each new edge kind against a batching or broadcast counterexample (a queue consumer flushing several
  clients' requests; a monitor with two notifiers).
- **One transport or queue thread may serve many nodes** (Hadoop IPC's `RpcRequestSender`): never refuse or key
  work by the thread's node.
- **Recordings run on stock HotSpot, replays on the VM:** check which JVM ran before blaming the image.
- **A host overload is first a ledger question:** the ramp-only charges let slow-growing Solr replays
  overcommit every host (fixed: leased charges).
- **A tree rebuild under someone's run corrupts their results silently** (A2 rebuilt a Solr tree under A6's
  replays): `pgrep` on all lifts before any tree build, every time.

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
| concolic VM images | `system/hdfs`'s VM: **`/bigtemp/vnr3ne/vm-size-source/j2sdk-image`** (vm-model-guards2 + an INDEXED size skips element sets; branch `hdfs-replay-windows` 73f0d0329, 70/70 smokes; a jar before it composes the same formulas). main's current VM: **`/bigtemp/vnr3ne/vm-model-guards2/j2sdk-image`** (vm-streams2 + the model guards: no model records a condition, a muted body's choice is a guard on its chain; branch `vm-model-guards` af18b3a5d, merged dda07c51b after round V19 13/13). `vm-streams2` (vm-w4h + the java.util.stream model, branch `vm-streams` fe68c3409, merged 770a64c8f after round V14; a jar before 770a64c8f refuses its STATE_COLLECT versions by name) serves rounds V14-V18. `vm-w4h` (the previous one: vm-w4e + the `frame::metadata_do` fix + caches cleared when metadata is freed + demand-driven tracking) serves rounds up to V13. `vm-model-guards` and `vm-streams` are the first builds of those branches, superseded (deletable). Parked, unreviewed: `vm-w4i` (per-activation tracked-location read-out, branch `perf-vm-readout`; a jar from that branch refuses vm-w4h by name), `vm-nr41` (reference-compare identity, branch `vm-ref-compare`). Older images are deleted (2026-10-02). Pass an image as `CAUSYNTH_CUSTOM_JDK_HOME` (a sweep: `VM_IMAGE`), never as `JAVA_HOME`. A Java side that needs natives an image lacks refuses the replay by name (`ConcolicVmBroker#requireCurrentCapabilities`). |
| HDFS trees | `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` (worktree of `~/hadoop`, branch `gc/hdfs-unified-dtx`: `gc/hdfs-unified`, trunk 734dd8a67cd, plus the DataTransfer op's envelope; its own Maven repo `/bigtemp/vnr3ne/wt/dtx/m2`): ONE tree for the eight named cases (hdfs-17897, 17899-bug1/2/3, 17960, 17967-pathA/B/C) -- one adapter, every workload, the known bugs' pre-fix code and target markers; its commit-by-commit inventory is `/bigtemp/vnr3ne/analysis/unify/hdfs-inventory.md`. hdfs-11741 keeps `~/hadoop-hdfs-11741` (`gc/hdfs-11741`); the older per-case trees `~/hadoop-hdfs-<case>` (`gc/<case>`) stay for the runs that used them |
| Solr trees | One Solr 8.11 tree line, `~/lucene-solr-unified` (branch `gc/solr-unified`, a worktree of `~/lucene-solr-8_11`): the shared adapter, both cases' workloads and target markers, the two kept scaffold patches (inventory: `/bigtemp/vnr3ne/analysis/unify/solr-inventory.md`); solr-18406 and solr-18413 name its successor `gc/solr-unified-storing` (`/bigtemp/vnr3ne/wt/lucene-solr-storing`: the same plus SolrZkClient's `MessageDoors#storing` write brackets). The older per-case worktrees (`gc/solr`, `~/lucene-solr-18406`, `~/lucene-solr-18413`, `~/lucene-solr-8_11-adhoc`) serve only rounds started on them. Ant build; native Ant tests need `-Dtests.useSecurityManager=false`. `~/solr` is apache/solr main (blobless: never `git grep` a commit there). |
| ZooKeeper trees | `/bigtemp/vnr3ne/wt/zookeeper-hb` (`gc/zk-unified-hb`, + the RESPONSE door, for `hb-schedule`; Maven repo `/bigtemp/vnr3ne/m2/zookeeper-hb`). `/bigtemp/vnr3ne/wt/zookeeper-unified` (branch `gc/zk-unified` on `branch-3.9`, a worktree of `~/zookeeper`): the adapter (`CausynthZk`, `CausynthZkCluster`), the `zk-bugs` cases' target markers and the quota workload. Maven build into its own repository `/bigtemp/vnr3ne/m2/zookeeper` (`experiments/zookeeper/build.sh`, which installs the GraphChecker jar there; never `~/.m2`). Build a case's workload before its first run: `SKIP_GRAPHCHECKER_INSTALL=1 bash experiments/lib/run.sh experiments/zookeeper/zk-bugs <case> build`. Its only remote is apache/zookeeper: never push it. |
| HBase and bug trees | `gc/hbase-unified`, `gc/solr-bugs`, `gc/hdfs-bugs`, `gc/hdfs-unified-dtx-w6`, `gc/hdfs-11741-w6` under `/bigtemp/vnr3ne/wt/` (§0.2); clones `~/hbase`, `~/zookeeper`, `~/hadoop`, `~/lucene-solr-8_11`; private Maven repos `/bigtemp/vnr3ne/m2/<name>` |
| merge worktree | `/bigtemp/vnr3ne/wt/main-pw`: where the lead builds each round's candidate branch `main-<x>` (§2) |
| host ledger | `$CAUSYNTH_HOST_LEDGER` = `/bigtemp/vnr3ne/gc-out/hosts/<lift>/charges/<mb>.<host>.<pid>.<time>.<rand>`: a charge's mtime is its 120 s lease, renewed every 10 s by its holder; a lapsed lease no longer counts (it is deleted at ten leases); `explorations/` = the capped explorations running. `ls` the charges of a host to see what holds it |
| evidence and agent tools | `/bigtemp/vnr3ne/gc-out/solr-bugs/{evidence,agent-tools,scripts}` (jstacks of the ZkStateReader-race hangs, A2's `watch-sb.sh`/`watch-stall.sh` run watchers, the storing tree's `spelledAs-adapter.patch`); `/bigtemp/vnr3ne/readout-stream/` (A6's `measure-seed.sh`, `measure-obl.sh`, `compare.py` and the retained-heap tool `heap/tool/HeapRetained.java`: how replay memory was measured; 4.2 GB of data); `/bigtemp/vnr3ne/gc-out/hb-schedule/` (Z1–Z5 with their `run.sh` recipes); `/bigtemp/vnr3ne/ab/` (offline gates; jars in `ab/jars/`) |
| code maps | `/bigtemp/vnr3ne/analysis/codemap-2026-10-02/`: 00-contract, 01-smt, 02-plan, 03-causynth, 04-runtime, 05-explore, 06-compose, 07-vm (each ends with design notes), 08-hdfs15-design |
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
CASES="hdfs-17960 solr-18413" ... tools/rounds/launch-round.sh ... # a subset (or any case id); the 14 regression
#   cases: hdfs-11741 hdfs-17897 hdfs-17899-bug1 hdfs-17899-bug2 hdfs-17899-bug3 hdfs-17960 hdfs-17967-pathA
#   hdfs-17967-pathB hdfs-17967-pathC solr-18406 solr-18413 zk-bugs-quota-init zk-bugs-election-offer hdfs-bugs-slowdisk-zero
# tools/rounds/launch-run.sh <snapshot> <case> <suffix>: one run, its obligations also over all of LIFTS
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
  A sweep's head is admitted (`fanout.sh` `ADMIT_MB`, no lifelong charge: its campaign reserves the room) for the room it reserves on its host, what
  its planner or composer starts at (`tools/lib/heads.sh` `case_head_reserve_mb`, 8 GB), not
  its engine heap: a40's Solr heads asked for 16 GB and waited while one case's 27-32 replays
  filled the lifts.
- A round name is written once (`accept-<round>-<case>` exists → refused). Names used so far:
  `v*`, `r1`–`r9`, `ra1`, `rb1`, `i1`–`i3`, `stream*`, `fast*`, `g1`, `F1`, `F1b`, `F2`, `K*`, `L*`, `N1`,
  `V1`–`V25`, `V4h`, `V5h`, `V7b`, `V16b`, `V18b`, `V22b`, `V22c`, `V24b`, `PP1`, `PP1b`, `M1`, `CF1`, `STO1`, agents' `a37f*`,
  `ee*`, `agent-*`, `w4-*`, `R5x*`, `r6s*`, `R7*`, `nr*`, `SB*`, `SBX*`, `SBR*`, `EO*`, `ZK*`, `SD*`, `HB*`, `HBA*`,
  `W6C*`, `Z*`, `G*` (in their own `GC_OUT`). Use a fresh name (the next round is `V26`).
- Typical wall time on main (round `V25`, cluster shared with agent runs): HDFS RPC cases 7–12 min (up to 30
  on a busy cluster), 17960 ~12 min, 11741 ~34 min, solr-18406 ~20 min, solr-18413 ~23 min, quota-init ~10 min,
  election-offer ~34 min, slowdisk-zero ~9 min. After the campaign, the acceptance report's
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
- **Launch a canary through `launch-round.sh`** (or `launch-run.sh` from `3007804da` on): before that,
  `launch-run.sh` left a run's obligations on its head host alone (W6C2-W6C4 ran on lift11, 2-3 replays at a time).
- **Recordings run on stock HotSpot; only replays run on the concolic VM image.** A recording hang is never the
  image's fault.
- **The Solr trees carry a workaround for an upstream `ZkStateReader` race** (a stale fetch resurrects a deleted
  collection; a delete's `waitForState` then hangs forever under `CausynthBounds`). A new Solr tree needs the same
  per-collection refresh lock (`gc/solr-unified-storing` `04f8489`).
- **A `Monitor` expires after 30 minutes;** re-arm it for the cases still running and filter the ones you have.
- **Lapsed ledger charges are still files** until ten leases pass: judge a host by the charges whose mtime is
  younger than 120 s, not by `ls | wc -l`.
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

- `case.sh`: the tree, the workload test, the target occurrence and the analysis scope; the test
  is a class and a method `m`, or one invocation of a parameterized test or class, `m[k]` (`m[i][j]`
  when both are: the class's, then the method's), k from 1 in the argument sources' order, as JUnit
  numbers them (`runtime/JUnitInvocation`);
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
that, never more than half a host's ceiling), REPRODUCE's runs (the recording's peak), an offline gate's JVM (its heap) and a `fanout.sh`
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
`CASE_TIMEOUT_SECONDS` (5400 s by default) and `PRUNE=1` (`PRUNE=0` keeps every artifact, for a measurement sweep, e.g. `CAUSYNTH_CAMPAIGN_STOP_AFTER=SEED`, which reaches each head on its job's command line), and a sweep started again resumes. Give
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
configuration), REFUTED (a real false positive: keep it), UNSAT, RUN_DEFECT (a defect of the run
or the engine to fix: no verdict), STOPPED (stage and reason), DEAD, RUNNING, PENDING. `findings.py` writes `findings.tsv`, one row per mechanism among
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
experiments/{hadoop,solr,zookeeper}/  per-system scripts and cases (hadoop/hdfs-bugs, zookeeper/zk-bugs:
                                  the bug_study checks; HBase's harness is on branch hbase-startup)
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
