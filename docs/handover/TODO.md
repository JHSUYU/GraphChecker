# TODO after the HDFS group (2026-10-08)

Order:
1. HDFS is finished (STATE §0): its follow-up items below are optional engine work, done when a later system needs
   them or before a clean final acceptance run.
2. Solr.
3. HBase.
4. ZooKeeper.

The owner: "hdfs所有的case跑完为一组，不要有回归。然后就到另一个系统". Each system is finished when every one of its
checks has an exported `.smt` that is right (SAT confirmed, or UNSAT at the fixed point) and every known bug of it
passes. Branch, tree and path details are in [STATE.md](STATE.md); every check with its state in
[../checks/README.md](../checks/README.md) and its reading in [../STATUS.md](../STATUS.md); commands in
[OPERATIONS.md](OPERATIONS.md); speed and the cluster in [../design/PERFORMANCE.md](../design/PERFORMANCE.md).

## HDFS (finished: `system/hdfs` 39 cases, `system/hdfs1` 7; trees r7, r7-21, r8, 11741-r6 = the fork's `graphchecker/*` branches; image `vm-hg5`)

46 of 46 cases closed with a hand-read `.smt` (STATUS "HDFS checks"); no new bug; every case ran alone on the ten
lifts for its time breakdown (EX1, PERFORMANCE §6). What is left is the general work the
workarounds stand in for, the defects the session found, and the cleanup. None of it reopens a closed case unless a
change alters its formula; any engine change below reruns the affected cases on `system/hdfs1` (one change per round,
RULES "Lock, then one change at a time").

### 1. The two-phase final acceptance run (owner 2026-10-06, for later)
For one clean run of all 46 on one body (once the items below are in or declined): (1) the ~36 short cases a few at a
time (6-8 concurrent: their time is serial SEED, recording and seed replay, so exclusivity buys them little); (2) the
deep closures (11741 08 09 05 06 11 14, 07) one at a time with the whole cluster (their cost is hundreds of obligation
replays, which fan out: 09 has 653 verdicts over 9 tasks and 7 regions). Expected ~4-5 h in all versus ~9-10 h with
every case exclusive. Note: the 39 cases of `system/hdfs` ran on the locked body, which lacks codec capture, open
arms, the wait deadline and the open-arm keys; a run of them on `system/hdfs1` is that final run's first check.
11741 needs `CASE_TIMEOUT_SECONDS=14400`.

### 2. The general fixes the workarounds stand in for
- **21**: a loop root's prefix as its own occurrence (§3) and the stranded activation (§4); then 21 runs on r7 without
  its tree and loop-bounds file.
- **07**: index a decoded reply's consumer by the send ordinal of the request it answers, not by the order the code reads
  it (STATUS open defect 57; `MessageDoors#send` records correlation id -> ordinal, `Identity#endpointAt`,
  `WireExport#attachLeaf`; ~50 lines + a test). Needed for HBase and ZooKeeper too (they iterate replies out of
  `HashMap`s). Then 07 runs on r7 without r8, and its world depth back at the default if it converges.
- **The time family** (21 22 23 24 25 34 35 52): the r7 workarounds (STATUS "Per-system surface") stay; the time model
  is never ground on (RULES).

### 3. A loop root's prefix as its own occurrence (general fix for 21's tree workaround; design ready)
A LOOP_BODY_ROOT occurrence's activations are its loop's iterations, so what its root method runs before the loop
is observed by none (21: `BPServiceActor.run`'s handshake, `checkNNVersion`). Merging the prefix into the first
iteration (branch `hdfs1-prefix-span` 1f14e68c7) stretched the actor occurrence over the whole service loop: its
offerService iteration never reaches a terminal, so an admitted replay's rows go unpublished (PS2-21: a BLOCKING
nested cut on an unstated flip), and every arm is keyed by the heartbeats delivered after it (PS1-11: 1319 asks).
Design: (1) the prefix's address is the loop-body occurrence's plus one index frame `<loopRuntimeId>:prefix@0`
(`OccurrenceAddress#prefix`, one function for PLAN and the runtime); (2) PLAN gives a LOOP_BODY_ROOT region whose
root method calls region work before the loop header a PREFIX task (same region, node and loop-root hook group,
rootAuthority `LOOP_PREFIX`), and the declared anchor goes on it when the root-method call it is reached through
lies outside the loop body; (3) `LoopAccounting#enterLoopRoot` opens the prefix task's activation, the first body
entry ends it NORMAL (published) and admits the body's own as on the merged body, the root's exit ends it with no
iteration, a cut ends it CUT; it counts against no loop-body budget; `PrefixSpan#atBody` and the "one activation,
two spans" text go; (4) no key change. Offline (PS1-11, current key): the actor's (arm, key) pairs 17008 merged,
7216 split (prefix 5327, body 1889); the prefix joins 11's closure as an `allKeys` writer, which the merged body
never did. Still owed with it: an activation stranded at session end publishes CUT (no ADMITTED verdict over
unpublished rows).

### 4. A stranded activation's rows (21's residue; evidence: W21's 3 BLOCKING gaps)
An activation whose root is still running when the session ends is stranded (`ConcolicResultPublisher#
strandWithoutTerminal`, TERMINAL_NEVER_REACHED): its path is withheld, only its mints publish, yet the replay's
verdict can stand ADMITTED (`FocusedReplay` saw the flipped arm taken). A nested path then cut from that session
inherits a flip the session does not state: W21 (`/bigtemp/vnr3ne/gc-out/hdfs-21w/accept-W21`), BLOCKING EXPLORE
`ADMISSION_GAP`s `updateActorStatesFromHeartbeat` u93#2/#3/#5 at the actor body occurrence 1bc6719160f7e094
(obligations ce70720a45fc2503, 12f86ac9a0cf4a8a, 97207921c23d9e9c); 4 of W21's 5 sessions stranded that body
(PS2-21: the same at u93#4). Fix, one of: (a) a stranded activation publishes CUT, as a bounded cut does: the VM
region closes only on its own thread, so the strand asks the owner thread to end at its next hook (a held
schedule wait released at session end) through `LoopAccounting#endAtCut`, the barrier waits for it under the same
grace, and one that reaches no hook makes its replay's obligations admit nothing
(`FocusedReplay#noteUnsettledPublication`), no new verdict; or (b) no nested path is cut from a session whose
flipped activation published no rows. Today's corpora of 07 (CC7), 11741 (AW5), 29 30 40 (HF1) and 39 (WD3) hold
no stranded activation, so either touches only perpetual bodies like 21's actor.


### 5. Defects found this session (STATUS "Open defects" has each with its fix)
- **52-56, codec capture review**: a getter on a message no door decoded attaches nothing, silently (52); SEED derives
  no port for a two-field getter or an unresolved class (53); a refused setter export leaves the builder's earlier
  element bound (54); the input-shape key does not record which producer fed which site (55); a protobuf object kept
  as state is not tracked as state (56). None is on a closed case's path (the review read 07, 11741, 12).
- **58/59, open-arm bookkeeping** (T): an obligation id carries no path and no world, so two worlds can share one; and
  the id drifts as the corpus grows. 39 closes, but its closure varied run to run before the open-arm keys (CHECKING
  trap 18).
- **51**: the arm key's u18#3 gap (rule 1 and the own-fault key missed the throughput bar; branches parked).
- **Confirm-first** (`hdfs1-confirm-first` da913cd7c, parked): a returned confirmation is decided only by the next
  step, behind any witness attempt in flight. With the Cone fix that costs minutes (HF2: 15 min from queue to
  accepted); merge if a confirmation is seen waiting > 10 min.
- **Scope (B)**, widening that would only make right formulas more flippable: 29/30 the block-pool map written at
  DataNode start-up and `bpServiceToActive`'s in-window writer gated by HA state; 17's lease and 39's IBR ordering
  (turns on threads with no schedule events); an identity compare of a tracked reference with an enum constant states
  no VM term (VM.md §5.2); 05's thread-local buffer invariant; String fields (21's versions; defect 34); 14's retry
  identity and its constant arm; 11's u18#3 key gap; 20's txid.
- A possible flake: Mockito `UnfinishedStubbingException` in `TestBlockRecovery2`.

### 6. Speed (PERFORMANCE.md §5)
- **Incremental planning** (owner 2026-10-07: "这个优化记做todo吧"; the first speed item): on branch
  `solr-incr-plan`, for the lead's merge. One planner JVM serves an exploration's rounds (`ExploreMain --serve`,
  PIPELINE §7.1/§7.9), keeping the corpus's rows with what each session's rows alone give, the static map and the
  slot table, whose rounds write only their changes; within a round `dependence` and the closure's re-walked
  pieces are computed once. Gate `offline-ab.sh` `EXPLORE.serve` identical on EX1 07e, 11741, 09, 17899-bug2, 39
  and SC1 solr-18406/18413 (07e: 2960 s fresh against 1667 s served, late rounds 300-360 against 150-180 s;
  PERFORMANCE §5 item 0). Live (`/bigtemp/vnr3ne/gc-out/solr-incr-plan`): INC1-adhoc-09 UNSAT_CLOSED as EX1,
  76 rounds and 443 s of planning (EX1: 16 rounds, 234 s); INC2-solr-18413 SAT_CANDIDATE CLOCK_SKEW confirmed.
  Still open: (1) rounds now come more often, each over fewer new sessions, and 09 asked 675 obligations (634
  flips) against EX1's 566 (535): measure whether frequent rounds propose arms under keys that later drift, and
  whether a round should wait for more landings; (2) `Value#hashCode` recomputes deep part hashes, about half of
  a late served 07e round's samples: a cached hash needs an immutability audit of the 35 contract values; (3) the
  closure is still built whole each round.
- **A host solver answers one question at a time** at 12-14 GB resident on 07's corpus: more answers per solver JVM
  (or a smaller one) would lift the solve throughput and the memory every lift gives replays.
- 11741 takes 1.5 h on the cluster (HF2: witness at ~60 min, confirmed at ~75 min, 5168 s in all).
- The ledger's ~1.6x over real use (step charges at their start heap).

### 7. Cleanup still owed (RULES: every change deletes what it replaces)
- The four-hop door API: `MessageDoors` should call `RuntimeTraceContext` directly.
- `CausynthTraceRecorder`'s offline aggregation into its own class; `CausynthPipeline`'s weaves apart from the analysis
  orchestration.
- The COMPOSE refactor's step 5 (steps 1-4 are in): `Composer.compose`/`run` as named steps; `SmtLowering` ->
  `VmTermLowering` + `SmtSymbolTable`; gated identical (`offline-ab.sh`, COMPOSE).
- The VM's dead natives and `exportLeaf`/`mintLeaf` with the next VM build (STATE §3).
- Loop-bound rows keyed structurally, not by Jimple unit ordinals (a tree change renumbers `#uN`).
- Left by the 2026-10-08 cleanup, each needing a decision: `DependencyRole` (its constant is hashed into task
  digests: deleting it re-keys every arm); STATUS open defects 14-16 (ClosurePlanner's fallback, SelectorResolution's
  degraded address, ScheduleLog's malformed timeout: semantic changes, design first); the two option parsers
  (`LongOptions`, `parseArgs`: merging changes how a bad command line is refused).
- `offline-ab.sh` `ab_stage_seed_static` tests `-s GROWN` on the gate host right after another host wrote it; over NFS
  it can miss the file (one spurious SEED.static difference on 2026-10-08): wait for it, or read it on the writer.

## Solr (next; `system/solr` = `system/hdfs1` `da152b3cb`, worktree `/bigtemp/vnr3ne/wt/gc-solr`)

The owner (2026-10-08): "跑完solr上所有adhoc check对应的unit test ... adhoc check必须要包含这些bug。也就是他们的.smt必须是sat。
然后要么用已有的unit test。如果没有，你写一个合适的cluster based unit test。我们远端不是已经有fork的solr吗。你就在上面类似地创建
分支即可，类似hdfs". The Solr group is these 20 cases (counts as `docs/checks/SELECTION.md`); it is finished when:
- each of the 8 bug checks ends `SAT_CANDIDATE`: its witness confirmed by a replay and reproduced natively, its `.smt`'s
  chain the bug's (read against the 8.11.4 code, CHECKING.md);
- each of the 12 study checks has a right `.smt`: SAT confirmed, or UNSAT at its fixed point;
- the group runs with no regression (solr-18406 and solr-18413 first: both passed on `main`, V25).
- the false SATs of a shared variable's other versions are filtered (owner 2026-10-08: "对shared variable的multi version做好处理，然后被我们的validation filter掉false positive。sat变成unsat"). COMPOSE re-pairs a read with any version of its location
  (RULES: no recorded-order pruning, every static writer), so a stale or impossible version can make a false SAT;
  CONFIRM, unchanged and strict, refutes it, the model is excluded and the next claim follows (PIPELINE "A claim CONFIRM
  did not confirm is followed by the next", `refuted_claims.jsonl`, `campaign_next_claim`), until the case ends
  `UNSAT_CLOSED` with `restsOnRefutations`, each refutation read against the code (CHECKING). It must converge: one
  claim per version must not exhaust `campaign_max_claims` (8) and end `SAT_UNCONFIRMED`. A CONFIRM replay that does
  not reach the exception, or times out or stalls, is a false positive (owner 2026-10-08, simplified: "如果replay跑不到
  exception。或者超时卡死，就直接定义为false positive"), excluded, and the next claim follows. Shown on real runs only (RULES): the
  study checks SOLR.md expects refuted (solr-adhoc-05 and -13, stale reads of watched cluster state and aliases) and
  any other; no real witness of the 8 bug checks may be filtered.

The 8 bug checks (the owner's bug reports 5-10 of 2026-10-08 and two merged upstream fixes). A workload passes
natively: the recording does not throw at the target, the witness is the engine's (a fault, a clock, a re-paired
read). Where no existing test reaches the path, write a MiniSolrCloudCluster test in the tree (`TestCausynth*`, as the
two named cases did); its shape below is the counterfactual's need, the test's details are yours:

| case | bug | target (8.11.4) | workload | the witness the `.smt` must allow | state |
| --- | --- | --- | --- | --- | --- |
| solr-18406 (= solr-adhoc-22) | SOLR-18406, apache/solr PR 4820: a follower's `filecontent(G)` after the leader deleted G (reservation expired) | `IndexDeletionPolicyWrapper:179` via `ReplicationHandler:1626` (`DirectoryFileStream.initWrite`); marked | `TestCausynthPullReplicaReservation#pullReplicaFetchesAcrossALeaderCommit` (ours, exists) | CLOCK_SKEW on the reservation | PASS on `main` (V25); not run on this body |
| solr-18413 | SOLR-18413, apache/solr PR 4862: an unexpired MIGRATE routing rule names a deleted target; the source leader's update throws after applying locally | `DistributedZkUpdateProcessor:934` (`getNodesByRoutingRules`: "Could not find collection"); marked | `TestCausynthMigrateRuleTarget#updateAfterRuleExpiryAndTargetDeletion` (ours, exists; the recorded rule has expired) | CLOCK_SKEW on the rule's expiry | PASS on `main` (V25); seed replay stalls on `solr-bug-reindex` |
| solr-bugs-reindex-cleanup | owner #5 (bug study #04): cleanup's `DELETE(T)` refuses a T an alias names, so S stays read-only | `DeleteCollectionCmd:246` (the alias-reference check) inside `ReindexCollectionCmd#cleanup`, the window's first DELETE; marked | `TestCausynthReindexAbortAlias#abortAfterAnAliasOfTheTargetIsRemoved` (ours): REINDEX S->T async held at `TestInjection.reindexLatch` once S is read-only and T exists, `CREATEALIAS A->T`, `DELETEALIAS A` (a failure logged), ABORT, release, at most 30 status polls, an add to S (replaces `testSameTargetReindexing`) | a SOLR_HTTP REQUEST fault on DELETEALIAS (owner 2026-10-08; the report's concurrent CREATEALIAS is ordered by HB here: DELETEALIAS completes before ABORT, and `checkAliasReference` re-reads ZooKeeper after `update()`) | workload passes natively; not run |
| solr-bugs-migrate-buffer-leak | owner #6 (#17): a failure after REQUESTBUFFERUPDATES leaves T BUFFERING; a retried MIGRATE is refused | `CoreAdminOperation:186` "not in active state" at the second MIGRATE's buffer request; marked; its selector from the first recording | `TestCausynthMigrateBufferLeak#twoMigratesIntoOneTarget` (ours): two synchronous MIGRATEs into one target, the first's outcome unchecked before the second | a FAULT at a door after the first MIGRATE's buffer step (routing-rule offer, source-leader lookup, a shard request) | workload passes natively; selector open |
| solr-bugs-overseer-lock-leak | owner #7 (#50): `OperationTimeout` in `markTaskAsRunning` leaks the collection lock; later tasks never run | `DistributedZkUpdateProcessor:238` "is read-only" (8.11.4 :236), the add after the task that never ran: the leak's own throw, a sync wait's timeout (`CollectionsHandler:383`), never comes in an automatic cluster; marked | `TestCausynthOverseerLockLeak#addAfterAnAsyncReadOnlyOff` (ours): CREATE C, sync readOnly=true, async readOnly off under a fixed request id, at most 30 REQUESTSTATUS polls 1 s apart, ADD | ZooKeeper `OperationTimeout` at `runningMap.put` (`DistributedMap.put` -> `SolrZkClient#makePath`'s own `keeper.create`, no HOOK row: agent M checks the catalog door covers it) | workload passes natively; not run |
| solr-bugs-snapshot-no-active | owner #8 (#16): CREATESNAPSHOT skips non-ACTIVE replicas and records success | `BackupCmd:207` "Unable to find any live replica with a snapshot"; the report's zero-request case reaches no throw (BACKUP skips a shard the snapshot lacks, :331-336); marked | `TestCausynthSnapshotBackup#backupFromASnapshotAfterItsLeaderIsGone` (ours): 1 shard x 2 replicas, CREATESNAPSHOT M, DELETEREPLICA the leader R1, BACKUP commitName=M incremental=false | the Overseer's view of R2 non-ACTIVE at `CreateSnapshotCmd:102` (STATE/CLOCK on its cluster-state read): M holds R1 only | workload passes natively; not run |
| solr-bugs-restore-construction | owner #9 (#26): a failed RESTORE leaves T's shards CONSTRUCTION; the retry takes the existing-collection path, which never activates them | `HashBasedRouter:67` "No active slice" at the add to T; marked; its selector from the first recording | `TestCausynthRestoreRetry#restoreTwiceThenAdd` (ours): BACKUP S, RESTORE B->T twice, an add to T, nothing waiting for T's shards in between | a FAULT at the first RESTORE's RESTORECORE / apply-buffer request | workload passes natively; selector open |
| solr-bugs-tra-start-overwrite | owner #10 (#20): the date-math start rewrite writes a stale aliases snapshot over a newer alias | `BaseCloudSolrClient:901` "Collection not found: B" (`requestWithRetryOnStaleState`, before `sendRequest`'s :1140) at the request via B; marked; its selector from the first recording | `TestCausynthTraStartAlias#requestViaAnAliasCreatedBeforeTheFirstDocument` (ours): a TRA whose start is date math on a fixed day, its collection off the Overseer's node, `CREATEALIAS B->D` before its first ADD, a request via B | the routing node's `getAliases()` capture re-paired with the version before B (STATE); the workload never reads that node's alias view | workload passes natively; selector open |

The 12 study checks (existing tests; rows with guard and site in [../checks/README.md](../checks/README.md) "solr"):

| case | site (8.11.4) | workload |
| --- | --- | --- |
| solr-adhoc-05 | `ZkController:1274` (`register`) | `AddReplicaTest#testAddMultipleReplicas` |
| solr-adhoc-07 | `ZkController:1326` (`register`) | `AddReplicaTest#testAddMultipleReplicas` |
| solr-adhoc-09 | `DeleteReplicaCmd:278` (`deleteCore`) | `DeleteReplicaTest#deleteReplicaAndVerifyDirectoryCleanup` |
| solr-adhoc-10 | `MaintainRoutedAliasCmd:117` | `TimeRoutedAliasUpdateProcessorTest#test` |
| solr-adhoc-13 | `RoutedAlias:350` (`doSynchronous`) | `TimeRoutedAliasUpdateProcessorTest#testPreemptiveCreation` |
| solr-adhoc-14 | `SplitShardCmd:167` (`split`) | `SplitShardTest#doTest` |
| solr-adhoc-19 | `CoreContainer:1330` (`create`) | `DeleteReplicaTest#deleteReplicaFromClusterStateLegacy` (`AddReplicaTest` never sets `legacyCloud`, so no writer of the guard's property; SOLR.md) |
| solr-adhoc-21 | `CoreContainer:1765` (`reload`, an assert) | `api.collections.CollectionReloadTest#testReloadedLeaderStateAfterZkSessionLoss` |
| solr-adhoc-31 | `CollectionsHandler:1477` (`forceLeaderElection`) | `ForceLeaderTest#testReplicasInLowerTerms` (not `@Nightly` in our tree; an `AbstractFullDistribZkTestBase` test: the base class registers its servers and opens the window, `CausynthSolrCluster#registerServers`) |
| solr-adhoc-38 | `DistributedZkUpdateProcessor:1031` (8.11.4 :1023; `doDefensiveChecks`) | `TestPullReplica#testAddDocs` |
| solr-adhoc-39 | `RoutedAliasUpdateProcessor:247` | `TimeRoutedAliasUpdateProcessorTest#test` |
| solr-adhoc-40 | `RoutedAliasUpdateProcessor:133` | `TimeRoutedAliasUpdateProcessorTest#test` |

**1. The body.** `system/solr` is `system/hdfs1` (fast-forwarded 2026-10-08); round SC1 (2026-10-08, the storing
tree as is) passed solr-18406 and solr-18413 on it. Branch `solr-body` (agent M) brings what the Solr cases need of
`solr-bug-reindex` by intent and closes the body's Solr gaps; its Solr side is `gc/solr-body`: `RECORDING_STALLED`, the
store-write turn (`WRITE`, `RunNames`/`spelledAs`; a conflict ends when the earlier write is taken or given up -- the
branch's LATE state was solr-18413's 103,812-stall regression), a consumed queue item as the message it serves, the
Solr request start (`CausynthHttp#requestStarting`, `outboundRequest` of the request's verb) and the door at every
call a hook's class makes of a moved door method (`SolrZkClient#makePath`, by control flow, every doorless call named),
scope growth stopping at a codec (the catalog's `CODEC` rows: JavaBin) and trace rows only inside an opened occurrence
(round MB2: 1.78 of reindex-cleanup's 2.0 GB trace was outside every occurrence, JavaBin's encode and decode most of
it; the aggregation thrashed at 2 GB), a workload's request that stands past the traced activation it began in
(solr-adhoc-31's test request, begun in `createServers`), a cloud client's attempt free of the last response its thread
read (`MessageDoors#callStarting`, solr-adhoc-13), and every jetty started in the window a node from its first moment
(STATUS "Per-system surface"). Still open there:
- `solr-bug-reindex`'s state roots at writers and non-accessors, only if PLAN still overflows after those two;
- Seed-replay stalls of the study checks (round SG1, classified by `/bigtemp/vnr3ne/gc-out/solr-body/scripts/
  stall_summary.py`): a poll owing its own context's frontier now polls with no move, and a held wait is let go a grace
  into an idle stall (IDENTITY §8); the writes keyed by a queue item's own path went with `storingChild`. Still to
  measure before/after on solr-adhoc-19 and -07; `solr-bug-reindex`'s other rules (`ScheduleReach`, `ScheduleWait`, the
  lock owner's early slot, the draw scope over the test's own classes, the queue order, `AT_QUESTION_CLOSED`) come in
  only when a Solr seed replay on this body shows the stall each answers.
Merge the parked `hdfs1-confirm-first` if a confirmation is seen waiting behind witness attempts.

**2. One tree, on the fork.** Done on the cluster (2026-10-08): `gc/solr-checks` (`/bigtemp/vnr3ne/wt/lucene-solr-checks`,
a worktree of `~/lucene-solr-8_11`) is `gc/solr-bugs` (`f65aaf7`: the storing line, the `spelledAs` adapter, the
reindex marker, both named workloads) plus the 12 study markers, the five new bug markers, the six bug workloads, the
AbstractFullDistribZkTestBase hook (solr-adhoc-31) and the reindex latch's bound (STATUS "Per-system surface"); every
case's tree (`experiments/solr/trees.tsv`). Left to the lead: unshallow `~/lucene-solr-8_11` (a shallow clone of
`apache/lucene-solr` `branch_8_11`, `faca81b`, 8.11.4, a history `apache/solr` does not hold: `git fetch --unshallow
https://github.com/apache/lucene-solr.git branch_8_11`) and push the branch to the fork
`https://github.com/JHSUYU/solr.git` as `graphchecker/solr-checks` (more branches only for a case that needs its own
tree; never an apache remote). The Solr side of [../REPRODUCE.md](../REPRODUCE.md) §6 is
`experiments/solr/{trees.tsv,prepare-trees.sh,solr-cases.tsv}` and `run-series.sh`'s case table.

**3. The cases.** Declared: `experiments/solr/solr-adhoc` (the 12 study checks, `checks.tsv`), `solr-bugs` (the six
bug-study checks), `solr-18406`, `solr-18413`, all on `lucene-solr-checks`; every workload passes natively there
(`/bigtemp/vnr3ne/gc-out/solr-cases/native-*`). Open: the selectors of migrate-buffer-leak, restore-construction and
tra-start-overwrite (their target throw runs more than once in the window; each case declares none, so PLAN refuses
and lists the occurrences, until its first recording names the one), read off a recording once `system/solr`'s jar
has `MessageDoors#spelledAs` (agent M's port; until then the tree's workloads run only against `solr-bug-reindex`'s
jar); and solr-18413's selector, read on `main`'s body, re-read there. Dev runs one case at a time, then the group of 20 (concurrently, through the ledger). A bug check that ends UNSAT is not done:
find which link of its chain the formula lacks (a door, a root, a writer the closure cut) and fix it generally. The
cross-cutting "Force the fatal arm" item below is for this system.

## HBase (`system/hbase` = main today)

**0.** Before any HBase run on the new body: `hbase-unified` `CausynthRpc.java:61-62` drops `, call.param` (the payload
door is gone with WIRE-CODEC); rebuild hbase-client.

**1. Settle `hbase-startup`'s two design questions** (the lead decides; see [STATE.md](STATE.md) §2):
- An identity rule for threads started by libraries (ZooKeeper's EventThread, Netty event loops). They must not
  inherit their racing creator's frames.
- Message-bound exports for a value exported on one thread and sent by another after a queue (what WIRE-CODEC's
  message-bound exports did; the body no longer carries WIRE-CODEC, so design it on the current WIRE path).

**2. HBase #14 (master-active-time) to a confirmed CLOCK witness.**

**3. Mark the 17 checked study points** (`docs/checks/HBASE.md`):

```
04r 07r 08 10 11 12 13 14 15 19 20 21 22 24 31 34 37
```

04 and 07 are re-sited to the server: `AbstractStateMachineTableProcedure.java:163` and `SnapshotManager.java:1046`.

**4. The two admitted bugs.** backup-lock-reply-lost: needs a RESPONSE door on HBase RPC (`checkAndMutate` with
NO_NONCE). ns-rsgroup-removal: STATE re-pairing of `removeRSGroup`'s namespace read.

**5. Run the group of 20.**

## ZooKeeper (`system/zookeeper` = main today)

**1. Merge `hb-schedule` + `hb-sync`** onto the new body. Run the offline gate on V25; live runs of quota-init,
election-offer and 11741, comparing arm counts and refutations with V25. The ZooKeeper tree with the RESPONSE door is
`gc/zk-unified-hb` `47ddc8b36`.

**2. A quorum adapter.** Every selected ZooKeeper study test is a quorum test. Register each quorum peer as a node;
open the window once the quorum is up.

**3. Mark the 10 checked points** (`docs/checks/ZOOKEEPER.md`):

```
01 02 03 04 06 07 10 11 12 13
```

05 is a dead throw; 08 and 09 have no path.

**4. zk-bugs-container-reuse (#33).** A self-written ClientBase test; STATE re-pairing of the client's node-map lookup
to the cleanup's delete, the election-offer mechanism.

**5. Run the group of 13.**

## Cross-cutting (engine), when a system needs it

**Force the fatal arm inside the target region (owner 2026-10-08; from the next system on, HDFS stays as closed).** The
owner: "事实上我觉得这里我们就可以直接针对这个region强制反转，记录条件然后throw出exception啊。即使他不符合真的因果。但我们会结合
symbolic propagation联立的。请你把它设为todo"; "这样做也更加合理吧"; "hdfs就算了"; "这样绝对是doable的。我们完全可以做到强制
反转，你可以通过soot,vm等结合实现。然后在那个target region里记录下path conditon即可。就可以之后直接用了".
- Today: a check's fatal condition is the recorded predicate of each guard a run evaluated, asserted at its fatal
  polarity in the formula; the throw itself never runs. A guard nested behind an outer one the recording did not pass
  (`if (a) { if (b) { throw } }` with `a` false) has no predicate until a flip of `a` and a faithful replay reach it
  (nested flips, at most 3 deep); a guard no replay reaches leaves the check without its condition.
- Proposed: in a replay, at the declared target occurrence `(r, c, i)` only, every branch between the region's entry
  and the marked throw is forced to the arm that leads to the throw; the VM records each forced guard's symbolic
  predicate with the polarity it was forced to, and the throw fires. The forced path is not a causal world: COMPOSE
  asserts each forced predicate at its fatal polarity, joined with the cross-node symbolic propagation over the same
  leaves, and z3 decides whether one valuation of the roots makes them all true at once. CONFIRM is unchanged and
  strict (a replay with the moved roots and no forcing must reach the throw).
- How (Soot + VM): Soot computes, on the region's static fatal slice, which arm of each guard reaches the marked throw
  and weaves the forcing points with the region's other hooks; the VM forces those arms at the declared occurrence and
  records the region's path condition; that condition is kept as an artifact of the case and used directly by
  EXPLORE's flip queries and by COMPOSE from then on, not rediscovered by nested flips.
- To settle before coding: (1) forcing at the declared occurrence only, never at the region's other occurrences;
  (2) a row recorded after the first forced branch is a forced world's (mark it `FORCED`): it may state a condition but never a writer arm or a handoff for other paths,
  or infeasible states feed the closure; (3) the replay ends at the throw, as the first-witness stop does; (4) a
  forced condition no replay confirms is at most `FORMULA_SAT`; (5) the VM's forcing directive (by branch site and
  occurrence, in `bytecodeInterpreter.cpp`'s branch bytecodes, carried by the replay plan) is a VM change and a new
  image; (6) measure on Solr's first cases whether nested flips and replays drop.

**WIRE-CODEC (`wire-codec-p1`; the system body carries none of it).** Resume only when a system's chain needs a
codec hole (a value carried inside an opaque payload); then rebase it onto the body, which deleted its runtime.

**VM performance.** The VM sends each expression node once per channel (STATUS open item 41). A plan budget should
be derived from the seed's measured cost.
