# TODO: HDFS finished, Solr in progress (handover 2026-10-09)

Order:
1. HDFS is finished (STATE §0): its follow-up items below are optional engine work, done when a later system needs
   them or before a clean final acceptance run.
2. Solr: in progress, stopped by the owner for a handover on 2026-10-09 (section "Solr": what is merged, the
   branches in flight in merge order, the owner-priority ZooKeeper READ doors, the open problems, the final round).
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
- **Confirm-first**: merged on `system/solr` (2026-10-08): solr-18406 SG3V's confirmation waited 46 min behind a witness
  attempt's COMPOSE that waited for head memory.
- **Scope (B)**, widening that would only make right formulas more flippable: 29/30 the block-pool map written at
  DataNode start-up and `bpServiceToActive`'s in-window writer gated by HA state; 17's lease and 39's IBR ordering
  (turns on threads with no schedule events); an identity compare of a tracked reference with an enum constant states
  no VM term (VM.md §5.2); 05's thread-local buffer invariant; String fields (21's versions; defect 34); 14's retry
  identity and its constant arm; 11's u18#3 key gap; 20's txid.
- A possible flake: Mockito `UnfinishedStubbingException` in `TestBlockRecovery2`.

### 6. Speed (PERFORMANCE.md §5)
- **Incremental planning** (owner 2026-10-07: "这个优化记做todo吧"; the first speed item): merged on
  `system/solr` (7e7bb64c2, 2026-10-08; not on the HDFS branches). One planner JVM serves an exploration's rounds (`ExploreMain --serve`,
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

## Solr (in progress; `system/solr` `7abebd846`, worktree `/bigtemp/vnr3ne/wt/gc-solr`; owner stop and handover 2026-10-09)

**Goal** (owner 2026-10-08, /goal): the 20 Solr cases below each get an `.smt` whose causal chain is right.
- The 8 bug checks end `SAT_CANDIDATE`: the witness is confirmed by a CONFIRM replay and reproduced natively, and the
  `.smt`'s chain is the bug's chain (read against 8.11.4, CHECKING.md).
- The 12 study checks: a SAT is confirmed, an UNSAT stands at its fixed point. A study SAT that passes validation is a
  new-bug candidate: check it is realistic, search JIRA, record it.
- Every `.smt` is read by hand and its row written in STATUS "Solr checks".
- solr-18406 and solr-18413 never regress. The end is one round of all 20 with no regression.
- False SATs from a shared variable's other versions are filtered by validation. COMPOSE over-approximates on purpose
  (no recorded-order pruning, every static writer); CONFIRM stays strict. Owner, simplified: a CONFIRM replay that does
  not reach the exception, or times out or stalls, is a false positive. It is excluded and the next claim follows, up
  to 8 claims; then the case ends "every SAT filtered as FP", not RUN_DEFECT. Each refutation an UNSAT rests on
  (`restsOnRefutations`) is read against the code.
- One Solr tree (base `gc/solr-bugs`), pushed to the fork `https://github.com/JHSUYU/solr.git` branch
  `graphchecker/solr-checks`; never apache. Reproducible from a fresh clone (REPRODUCE §6).
- Owner additions:
  - Force the fatal arm (Cross-cutting).
  - Every SAT gets a native validation replay that controls the symbolic values and the partial orders.
  - Per-system branches; regression is judged within Solr only.
  - **ZooKeeper READ doors in the fault catalog (owner priority, 2026-10-09; §2, `solr-zk-doors`).**

### 0. What `system/solr` holds (merged, green: mvn + the shell test)

Merged since the HDFS state:
- the served, incremental planner;
- the forced fatal arm, plus the VM's `Collectors.toMap` and enum models;
- confirm-first;
- the owner's FP rule (3ce1ddd08);
- the Solr body: the HTTP send in `executeMethod`, the stall rules (`solr-body` 3d0bd661b; its `DOOR_SEND_OUTSIDE_REGION`
  rule is replaced on `solr-zk-state` by the sending turn's doors, f7080b2e0);
- the store READ turn: a SolrZkClient read of a written location takes its turn at the location (key `MessageDoors#turn`),
  never blocks the frontier, and yields to a model's order past the cut (`solr-body` 873fdaa20, Solr `gc/solr-body`
  7e51565080; gated on `~/gc-run/sbm23`: 39 and 19 seeds match their anchors, 18406 native 10/10, 18413 and migrate PASS);
- the closure's precision, reviewed twice:
  - confinement by causal context, `CLOSURE_CONFINED` rows, `result.json confinedWriters`;
  - an arm's key by the region's static reads;
  - a stall after a flip keeps its flips;
  - the served planner stopped by pid (`solr-explore` fc5c6fa94);
- the VM fix for a String shadow's field demand-mint (`solr-vm5` 058c29b9e);
- native order-holding: the realized order of the confirmed session (`solr-native-order` 2d9f89f28);
- a growing round's proposals queued, not re-emitted (`explore-inflight` 345799304);
- `report.py`'s expected mechanism for all 8 bug checks (b921f8a3e).
- ZooKeeper store state, Z1 (`solr-zk-state` 184995cdb, agent Z1, reviewed and re-checked): store versions as STORE locations (rows keyed occurrence|seq|location|version, store paths' lives `<path>#<n>`), dynamic provenance (decoded objects hold the version they were parsed from; skipped objects stated; a decode waits for an in-flight write at its path), CAS chains, a batching turn started by every item it took in, door families always placed, (i') turn-wide doors, the witness path's STORE reads as stated rows CONFIRM compares by writer (no ORDER rows), the engine's own output under the VM's pause (`ConcolicVmBroker#asEngineWork`; it never loads the broker), logging calls under the concolic pause; vm-force6's read-out window reverted. Evidence: solr-18413 seed 7 min (was > 40), SAT native 10/10; reindex-cleanup SAT native 10/10 (Solr `gc/solr-zk-next` 22930889c8: the workload's createAlias tolerant); IZ1 overseer-lock-leak and restore-construction SAT native 10/10.
- the study checks' engine fixes (`solr-study` 01eda3dc0, agent ST, reviewed twice): solr-force2's D1/D2/D3 with the review's fixes (the way guard by the anchor's site, one iteration's passability with handler edges, a throw's own disjuncts by the general rule, every cut of a non-reaching path named, engine defects never loop bounds, one work cap); the Root:WAKE rule (39's seed 3/3, 31's 2/2); D1b (the FORCE run's armed occurrence exempt from K_L); an anchor reached only by an admitted session (`RestsOn#reached`); deciders through a lambda (09); per-loop K_L.

Image: **`/bigtemp/vnr3ne/vm-force5/j2sdk-image`** (OPERATIONS). Canary round SG2c on 9f317aba3: 18406, 18413 and
migrate-buffer-leak PASS (confirmed, FORCED_TARGET).

### 1. Branches in flight (every one committed, none merged, none pushed). Merge in this order

| # | branch (GraphChecker) | head | Solr tree branch | what it is | gated? / what is left before the merge |
| --- | --- | --- | --- | --- | --- |
| 4 | `solr-zk-doors` | d01c330f5 (system/solr 293c8a303 merged) | `gc/solr-zk-doors` eee0e1bd7a (worktree `/bigtemp/vnr3ne/wt/lucene-solr-zkdoors`, built: Solr 92c234a5d1, `GC_TREES=/bigtemp/vnr3ne/wt/zkdoors-trees`) | **ZooKeeper READ doors (owner priority)**, on Z1 d9700c84b + solr-body | A1 (the getData door after the reply; a lost reply removes the local watcher, a Solr-tree workaround) and B2 (a demanded STORE read demands the plan's fetches of its location) committed; gate (b) waits for Z1's read-out decision and the Root:WAKE rule (RD2's seed stalled on both), then 40 re-recorded until its first target runs off the Overseer, gate (d) |
| 5 | `solr-zk2` (Z2) | see `git log solr-zk2` (solr-zk-state db0382de4 merged) | `gc/solr-zk2-next` b2605b6bd7 (`GC_TREES=/bigtemp/vnr3ne/wt/pno-trees2`) | stale cluster-state views. Content capture at the codec: `Utils.toJSON`/`fromJSON` → `StoreContent`, ports `<transport>#CONTENT:<loc>#<pointer>`, at most 1024 leaves and depth 16; 18413's WIRE_FLOW rows stay (the decode's RoutingRule is built outside every region: its expireAt reaches the guard as an INITIAL constant). `LocationKind.VIEW` (`<transport>@<node>`) and `SmtLowering#throughView`; the pairing flip (`PairingFlip`), the decode hold (`VIEW_HOLD`, `Confirmation#decoding`, `MessageDoors#refreshing`), the world-pairing claim (ClaimPolicy's observed-elsewhere rule) | Agent Z2 (2026-10-11, `brief-z2.md`). Review fixes B1-B3, (a)-(d) and the re-check's B2-real-shape, (b), (c), (d), LOW committed. Gate 3 open: snapshot-no-active and tra-start-overwrite SAT confirmed with native ≥ 1/10 (round Z2M tra: STATE_PAIRING_FLIPPED claimed live, run aborted by the grown-tree re-run race, agent ST), 18413 SAT with its WIRE_FLOW rows (two runs, coalesced-watch CONFIRM), one run of 40 |

`hdfs1-confirm-first` and `explore-inflight` are merged. Every other `solr-*` branch is merged or superseded.

### 2. ZooKeeper READ doors (owner priority 2026-10-09; branch `solr-zk-doors`)

Why: an external study found two Solr failures. Both throw sites are our study checks: solr-adhoc-40's
`RoutedAliasUpdateProcessor:133` "alias must exist", and solr-adhoc-09's `DeleteReplicaCmd:278` "Could not remove
replica". The lead read them against 8.11.4 and apache/solr main: one root cause, still in main.
- A ZooKeeper watch callback whose re-read fails with ConnectionLoss or SessionExpired only logs, and the watch is never
  re-armed: `ZkStateReader.AliasesManager#process`, and the collection `StateWatcher#refreshAndWatch`.
- Re-init (`createClusterStateWatchersAndUpdate`) runs only after a real session expiry. A loss that outlives
  `retryOnConnLoss` without an expiry leaves the node's view stale for good.
- Consumers that never re-read: `RoutedAliasUpdateProcessor#getAliasProps` (no `update()`); `DeleteReplicaCmd`'s two 30 s
  `waitForCoreNodeGone` waits on the local view.
- JIRA has no report of this mechanism. SOLR-16257 (a race between `watchedCollectionStates` and `collectionWatches`)
  is different. SOLR-12256, SOLR-12261 and SOLR-4739 are related eventual-consistency issues. A JQL search of SOLR for
  "cannot talk to ZK" finds nothing on this.

Our catalog had ZooKeeper WRITE doors only, so the engine could not inject this. The design (lead's):
- READ door rows for `ZooKeeper#getData(String,Watcher,Stat)`, `#exists(String,Watcher)`, `#getChildren(String,Watcher)`
  and `#getChildren(String,Watcher,Stat)`; faults ConnectionLoss, SessionExpired, OperationTimeout.
- Placed **before** the request: a failed read never reaches the server, so no watch is registered.
- Relocated for Solr by HOOK rows to SolrZkClient's read methods, **before** `zkCmdExecutor.retryOperation`, so the
  caller sees the fault after retries.
- A read door roots **no region**: the Overseer polls constantly. Its marker is read in the occurrence that runs the
  call. It is flippable only on the demanded data flow:
  - the fetch whose decode produced an object the demand reads (Z1 provenance);
  - or a fetch of a location whose STATE family read the demand holds.
  Every other read door is woven but never asked, and the plan log counts both kinds.

State of 6cbc40a93 (WIP; unit and shell tests pass):
- Done:
  - catalog rows (`DATA_FLOW`, before `submitRequest`);
  - HOOK `before` support (`DoorWeave#moved`, backward);
  - the Solr hooks before `SolrZkClient#causynthReading`;
  - read markers root nothing and trigger no other admission rule;
  - fetch occurrences on `STORE_DECODED` rows (`RecordedStore#fetchesOf`/`#fetchesAt`);
  - `RuntimeSelectedRegionFinalizer#askFetches` (`STORE_FETCH_V1`), with plan-log counts;
  - docs.
- Left:
  - build `gc/solr-zk-doors` with its natives (`experiments/solr/build.sh <tree> F0993D5343E20BA4 '<Class#method>'`;
    never while `mvn package` runs);
  - verify two assumptions: SolrZkClient's read methods sit in the fetching occurrence's region (else a fold), and
    EXPLORE reaches the fetch occurrence;
  - gate (b): a live 40 seed with only data-flow reads flippable (counts);
  - gate (c): 18406, 18413 and migrate PASS with no growth from polls;
  - gate (d): if 40 reaches a witness by a read fault at the routing node's aliases fetch, confirm it and reproduce it
    natively. That is the external study's candidate, rediscovered.
- 09's mechanism also needs a timed wait's outcome (a timeout against a signal) as a schedule choice: Cross-cutting
  "Timed-wait outcomes", not in this group.

### 3. Open problems (each with its evidence)

- **a. 18413 under Z1:** seed time 2429-5200+ s (SG2c on system/solr: 569 s). Measured 2026-10-11 (Y1, alone on lift07/lift14;
  jstacks in `/bigtemp/vnr3ne/gc-out/solr-zk/accept-Y1-413-f{5,6}/jstack`): every sample a region close waits on the publication
  thread's read-out decoding. The cause (Y2, counters): one reused logging encoder's byte array tracked by value, re-listed at
  every close (STATUS defect 38). vm-force6's window saved under 20 %: reverted. Fix: a logging call runs under the VM's pause.
- **b. reindex-cleanup:** Z9 (zk16) SAT, confirmed, native 0/10, before order-holding. Z10 grew on the planner's
  re-emission, now fixed (`explore-inflight`). Rerun on the merged head with native order-holding. Its witness is a
  SessionExpired at a ZooKeeper create in the REINDEX Overseer task (OVERSEER_TASK#2). SessionExpired chains are
  accepted as the bug's chain; the owner's DELETEALIAS request fault is not required.
- **c. "Reached" by admitted sessions only** (coded on `solr-study`: `RestsOn#reached`, read by `RestsOn#admitted` and
  `ClosurePlanner#plan`; F2V4 19: a non-admitted replay that threw the target made COMPOSE drop 63 unreached paths).
- **d. The Root:WAKE rule (`solr-study` 7d54eb435; seeds: 39 3 of 3, 31 2 of 2):** an event of a timed-wait loop's turn
  (`Root:WAKE/<wait>#k`) at a slot not yet due is held like a poll past its count (`ScheduleLog#waitsAtLocked`,
  `#timedWaitTurn`), so it never bounds a range give-up, and let go it takes that slot (PIPELINE §5, IDENTITY §8).
  In 31's runs no non-READ event of such a turn ever found a recorded slot, so the rule changes nothing there. Open
  (not approved): the frontier side, a turn's recorded slot the replay makes under another k -- 25-38 % of the seeds'
  stall time (31: 53-65 s of 279-298 s; 39: 149-195 s of 510-724 s), all seeds matching anyway. Evidence:
  `Root:WAKE/ZkDistributedQueue.peekElements#k` was recorded at #106 and replayed at #423-#499; MB29s/MB30s gave up
  666-4251 slots and node1 won the election node3 won in the recording. 31's MB32s miss was not this drift (it
  ended on ForceLeaderTest.java:232's assert).
- **e. Study checks after D1:** 07 (8490 in flight before the explore merge; 64 tasks plus 171 cut by the task bound
  after it), 21 (2023 in flight) and 14 must reach their fixed points; measure the growth on the merged body. 05:
  FORCE reaches its target (D1b, SF3); with createInstances' K_L 16 (SF5) its closure grew past 290 obligations
  of ZooKeeper write fault doors in 2 h and was stopped (the EX redundancy class): rerun after EX. 09: its forced
  deciders are concrete, `waitForCoreNodeGone`'s timed waits never expire; the timed-wait door (a FAULT marker
  at a timed wait whose result is on the traced flow) is approved and in coding. 10: not yet
  run whole (it plans 356 tasks).
- **e2. EXPLORE redundancy (package EX, agent RD on `solr-explore2`, brief `analysis/solr-2026-10-11/brief-explore-redundancy.md`):** IB1's 07/21 spent ~83 % of their proposals re-asking arms in fault worlds that changed nothing at the task (the obligation key carries inherited prefixes, `ObligationFactory.keyed`, and exact feeder ids, `Corpus.inputShape`), and 07's closure truncation (`ClosurePlanner`, first-come) dropped recorded `create` writers for 59 static `getCore` candidates, against the recorded-writers-first rule. Fixes: key by the effect at the task, feeders by context-shape class, recorded writers first in the cut, an ADMITTED flip settles. Design gate for the key, review before merge.
- **i. solr-adhoc-13's seed is compute-bound** (diagnosis 2026-10-11 on IS1/IB1-7: ~1300 s compute + ~850 s stalls; the test body covered recorded 10.9-21.5 s of 35 s in 2200 s; the Overseer poll turns `Root:WAKE/ZkDistributedQueue.peekElements` are misnumbered from the first CREATE on: two Overseer threads share the wait's counter and every wake reads /overseer_elect/leader, 1117 reads against 41 recorded -- the clock family). Workarounds (owner: the time family by workarounds), in the final tree `gc/solr-final`: `TimeRoutedAliasUpdateProcessorTest#testPreemptiveCreation` ends after `addOneDocSynchCreation(numShards, alias2)` (:302) -- the declared occurrence is `first` (the doSynchronous call at :301), both aliases' creations and writers stay; ZkStateReader's CacheCleaner sleep bounded by CausynthBounds (it woke 91 times in the replay, never in the recording). Both listed in STATUS "Per-system surface".
- **f. SG2b's UNSATs of 19 and 21 are void** (D2: their fatal was composed from the wrong throw). SG2-era UNSATs of 07,
  19 and 21 likewise.
- **g. New-bug candidates:**
  1. 19, a stale cluster-property view at core creation: in F2V4 an unforced replay threw the target (session
     `0c227a75f31cbf87-7ca7ab71`, node1 read non-legacy while the CREATE carried no coreNodeName). Confirm it through
     Z2 (the `legacyCloud` leaf), then check realism and JIRA.
  2. The lost watch above (§2).

### 4. Then: the final round and the fork

1. Merge §1 in order. The one Solr tree is the local branch `gc/solr-final` (`ec89b03ac3`, worktree
   `/bigtemp/vnr3ne/wt/lucene-solr-final`): `gc/solr-body` + `gc/solr-zk-next-r` + `gc/solr-zk-doors` + `gc/solr-zk2`
   + solr-adhoc-13's workarounds; every case's workload and target marker checked present there (solr-study2).
   - It becomes the tree `lucene-solr-checks` (`experiments/solr/trees.tsv`: the fork's `graphchecker/solr-checks`),
     built by `experiments/solr/prepare-trees.sh` from the merged, built engine head -- not before;
   - never rebuild a tree a run reads.
2. Round SG3: all 20 at once through the ledger (`tools/adhoc/sweep.sh`, `CASE_TIMEOUT_SECONDS=10800`, 14 needs the
   full budget). Verify with `tools/rounds/round-verify.sh`. Read every `.smt` by hand and write its STATUS row;
   record every FP filtered as "COMPOSE SAT → CONFIRM refute → excluded → UNSAT_CLOSED".
3. The fork. `~/lucene-solr-8_11` is **unshallowed** (2026-10-09). Push `gc/solr-final` as `graphchecker/solr-checks`
   to `https://github.com/JHSUYU/solr.git`, never apache, and only with the owner (the lead pushes).
   `experiments/solr/trees.tsv`, `solr-cases.tsv` (07's budget 21600) and REPRODUCE §6 (GraphChecker `system/solr`,
   its image, the tree from the fork, the 20 by `run-series.sh`) are written; verify §6 from a fresh clone once the
   fork and the merged engine are pushed.

### 5. Where things live

- Lead log and decisions: memory `lead-session-2026-10-08-solr`.
- **The four agents' own handover reports** (heads, gates, run dirs, gotchas): `/bigtemp/vnr3ne/analysis/solr-2026-10-08/HANDOVER-2026-10-09.md`.
- Briefs and designs: `/bigtemp/vnr3ne/analysis/solr-2026-10-08/`: `AGENT-RULES.md`, `brief-*.md`,
  `design-force-fatal-arm.md`, `design-zk-state.md`, `design-enum-model.md`, `design-force-study.md`.
- Lead rounds: `/bigtemp/vnr3ne/gc-out/solr` (SG1, SG1R, SG2, SG2b, SG2c; `rounds/*.cases`).
- Per branch:
  - `gc-out/solr-body` (MB*): keep MB28s/31s/32s/33s and MB32c; MB29s/30s show the drift. Scripts `seed_gate.sh`,
    `stall_summary.py`.
  - `gc-out/solr-zk` (Z8, Z9, Z10, RG-*): scripts `rowdiff2.py`, `obltab.py`, `gate.sh`.
  - `gc-out/solr-zk2` (Z2B-19, stopped Z2C and Z2D).
  - `gc-out/solr-force2` (F2V1-F2V4).
  - `gc-out/solr-native-order`.
- Snapshots worth keeping: `~/gc-run/sbm23`, `sbm19`, `zk13`, `zk16`, `zk17`, `pnz6`, `pnz3-nocap`, `f2d`, `sg2b`,
  `sg2c`, `pe5`. Removable: `pnz1-5`, `zk14-15`, `sg1*`, `sg2`. Check `pgrep` on all lifts first.
- Images: `vm-force5` (system/solr and Z1); `vm-force1..4` and `vm-force6` (Z1's reverted read-out window) superseded.
- Trees:
  - `/bigtemp/vnr3ne/wt/sg2b-trees` (Solr 88425b0, the SG2b/SG2c tree);
  - `pno-trees2` (gc/solr-zk2-next, solr-zk2's tree); `pno-trees` (gc/solr-zk2, one commit behind);
  - `lucene-solr-zk2`/`-zk3` (gc/solr-zk-next);
  - `lucene-solr-zkdoors` (unbuilt);
  - `lucene-solr-body` (gc/solr-body).
- Gotchas:
  - A command line that names a run's path together with `stop-run.sh` gets killed: run `stop-run.sh` alone.
  - The `gc-solr-zk` worktree has `third_party` checked out.
  - CHECKING trap 22 became 23 in the solr-force2 merge.

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
symbolic propagation联立的。请你把它设为todo"; "这样绝对是doable的。我们完全可以做到强制反转，你可以通过soot,vm等结合实现。然后在那个
target region里记录下path conditon即可。就可以之后直接用了". Built on branch `solr-force-arm` (PIPELINE §7.10; design
`/bigtemp/vnr3ne/analysis/solr-2026-10-08/design-force-fatal-arm.md`, the lead's rulings: always run the FORCE replay, no
transplant onto other paths, nested flips kept, no flip waiting for the forced ones): SEED's forcing table, the VM's forcing native (image
`vm-force1`), the FORCE run first in every campaign, its forced session held apart, its forced flip asking the whole way to
the throw, its path one more COMPOSE disjunct, CONFIRM unforced; solr-18413 and solr-18406 PASS with it (FA4). Merged on
`system/solr` (fa70dae08, image vm-force4+). A loop bound counts only iterations that decided on a symbol (the CREATE-a-core
checks' FORCE runs were cut by a concrete loop), a branch both of whose arms reach the throw is never forced, and a path
stopped on the way is BOUNDED (`solr-force2`, PIPELINE §5, §8). `seedFlipsAfterForcedFlip` was 0 in every Solr run of
agent F2 (so the seed path's anchor flips and open-arm asks may be deletable: decide on SG3's numbers). Waiting on Z2:
solr-adhoc-19's forced flip (its phi reads `clusterProperties`, parsed from ZooKeeper JSON).

**WIRE-CODEC (`wire-codec-p1`; the system body carries none of it).** Resume only when a system's chain needs a
codec hole (a value carried inside an opaque payload); then rebase it onto the body, which deleted its runtime.

**VM performance.** The VM sends each expression node once per channel (STATUS open item 41). A plan budget should
be derived from the seed's measured cost.

**Timed-wait outcomes (owner 2026-10-09 discussion; not in the Solr group).** A guard decided by whether a timed wait
(`CountDownLatch#await(timeout)`, `waitForState`) timed out or was signalled is concrete today: the signal travels through
JDK synchronization the VM does not track (solr-adhoc-09: `DeleteReplicaCmd:278` needs both 30 s `waitForCoreNodeGone`
waits to time out). A general model: a timed wait's outcome is a schedule choice -- the signal before or after the
timeout -- that a flip may ask and CONFIRM holds by an ORDER row. Needed for the external study's DeleteReplica candidate
(Solr §2) beside the ZooKeeper READ doors.
