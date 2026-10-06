# TODO at the handover of 2026-10-05 morning

Order:
1. HDFS to the end, as one group with no regression.
2. Then Solr.
3. Then HBase.
4. Then ZooKeeper.

The owner: "hdfs所有的case跑完为一组，不要有回归。然后就到另一个系统". Each system is finished when every one of its
checks has an exported `.smt` that is right (SAT confirmed, or UNSAT at the fixed point) and every known bug of it
passes (owner 2026-10-05: no exclusive runs required; keep all ten lifts full; the goal is a right `.smt` per check). Branch, tree and path details are in
[STATE.md](STATE.md); every check with its live state in [../checks/README.md](../checks/README.md); commands in
[OPERATIONS.md](OPERATIONS.md); speed and the cluster in [../design/PERFORMANCE.md](../design/PERFORMANCE.md).

## HDFS (current system; `system/hdfs`, tree `gc/hdfs-study-r4`, image `vm-hg5`)

Where it stands (STATE §4): 9 of 10 known bugs PASS; 7 study verdicts on the merged body + 10 to rerun; 8 open with a
fix landed or a rerun owed; 2 with a named defect; 9 in the time-model class; no new bug. Do these in order; 1-4 can
run in parallel (one coding agent each, at most 4), each validated alone, merged one at a time.

### 1. Land the finished WIP (small)
- **`hdfs-compose-cost`** (07's COMPOSE: the quadratic self-check fixed, progress lines): run
  `/bigtemp/vnr3ne/ab/hdfs-refactor-compose/cost-gate.sh` with the branch jar against system/hdfs (byte-identical
  COMPOSE outputs on V25/HG4/HG5A/HG7), write PIPELINE §8's note, merge. Then add the reserve for a COMPOSE never
  measured: twice the last planner round's wall time (the planner reads the same corpus), never below
  `campaign_reserve_s`.
- **`hdfs-refactor-compose`**: merge system/hdfs into it, re-gate steps 1-4 (identical outputs), merge; then step 5
  (Composer.compose/run as step methods over one per-path context; the SmtLowering split: VM-term lowering into
  VmTermLowering, declarations/rendering into a new SmtSymbolTable; SmtLowering.binary by operand sort), each step
  gated identical. Brief `brief-refactor-compose.md`.

### 2. hdfs-adhoc-14: the r4 trees -- done (R4A, `/bigtemp/vnr3ne/gc-out/hdfs-r4`)
Every HDFS `case.sh` names the r4 trees (`hdfs-anchored-index`). R4A: 14 UNSAT_CLOSED at FIXED_POINT (was RUN_DEFECT;
REGION.084d06ab stands on `Anchor:3093ec49939a753e@HADOOP_IPC/test` with index `[doAs@0]`, instrumented and answering
its task in every session); 21's PLAN as before (stopped at 80 seed give-ups, the time-model class); bug1, 17897,
17960 PASS; 11741 confirmed CLOCK_SKEW, its key id the open binding of §4. r3 is never touched again.

### 3. The time model (the start-up/clock family: 01 17 21 22 23 35 43, + 52; 25 34 regression canaries)
- On `hdfs-time-model` (review, then merge; PIPELINE §5 "application clocks", STATUS row "A replay's application
  time follows its order"): every application clock read goes through `Clocks`, every schedule row and STARTUP mark
  is stamped, a replay reads its order's timeline (`max(last, min(hi, lo + elapsed))`), a CLOCK root's skew sits on
  top of it (`RootMintRow#baseReading`). Seed give-up lines, model (rounds TM8-TM13, `gc-out/hdfs-time-model/probe/
  runs.txt`) against no model (SL2, D2B; HG8F under load): 25 0-2 / 8, 87; 34 0 / 6, 91; 35 0 / 81, 85; 23 37-38 /
  83, 86; 22 0-43 / 66, 32-85; 01 30-61 / 84, 85; 52 4 and 72 / 72, 84; 43 96 / 88, 90; 21 12-138 / 81, 89; 17 18-122
  / 85, 87. Where the clock decided (25 34 35, 22 on TM13, 52's extra heartbeat) the give-ups are gone; the rest vary run to
  run and are not the clock.
- Left, not the clock, by first divergence: an IPC handler's `CallQueueManager.take` racing another (21, 52, 34 on
  TM12, 17 after its NameNode restart; the lock turn below); a DataNode's IBR wait woken where the recording's was
  not (`waitTillNextIBR` "unrecorded WAKE"), then NotReplicatedYet (22 23 01 43); client polling loops (01's 200
  `getBlockLocations` slots, 22's `getDatanodeReport`/`create`).
- Open, clock-shaped: in some recordings of 17 (TM10, TM12, TM13, not TM8 or TM13D) every DataNode's in-window turn
  #1 finds its heartbeat not due though turn #0 ran before the window opened (no in-window #0 event) and time stood
  at the last registration; the 3 s interval puts turn #1 within 7 ms of the recording's due time. Read the turn's
  reads with a CLOCKDIAG-style probe of the actor thread from turn #0 through turn #1 (round TM13D's probe logged only
  the first 40 reads).
- Fidelity: a soft WAKE taken late is stamped up to seconds past the next slot's instant (52: 2480 events past the
  next slot by more than 1 ms; LeaseRenewer, JvmPauseMonitor, GcTimeMonitor), since time runs on to the first
  blocking slot's instant; `/bigtemp/vnr3ne/gc-out/hdfs-time-model/probe/drift.py` measures it per run.
- D2's lock turn (answered, not built): hold an adapter-named lock's entry (FSNamesystem's write lock) as a slot,
  keyed by the lock's location, like the store-write turn; build it when a case's first divergence is a lock race
  (52's on r5 + the model is not).

### 4. hdfs-11741: the key id's binding across the wire
The witness is confirmed CLOCK_SKEW and its allKeys reads are complete (PS3), but the SASL data-encryption key id
arrival came out FREE (PS1), bound (PS2, PASS) and HELD (PS3) in three runs: COMPOSE refuses the SASL sender arms
("rests on a value the recording does not state") beside ~100 ASSOC_VIEW_UNORDERED map-view gaps. Find which unstated
value refuses the sender's export arm and why it differs between runs; a view ordering the chain does not state must
not refuse an arm whose value does not depend on the order. Evidence `/bigtemp/vnr3ne/gc-out/hdfs-address-shared/
accept-PS{1,2,3}-11741`. Done when the key id is bound by its message family in all three offline and in one live run
(report.py PASS, cone.py clean), and the `.smt` chain is checked by hand (allKeys `assoc_put` under the expiry `ite`s,
the clocks of nn0's `updateKeys` and dn1's `addKeys` moved and in the cone, the key id across the wire).

### 5. The other open checks
- **32 swapped for 05** (owner 2026-10-05, "32直接换成05吧"): 32's map removal runs in the actor thread's exit, unnamed
  work started before the window; an identity rule for a thread's exit as a lineage hop would bring it back.
- **07/08/09** (QJM, deep closures): rerun each ALONE on the whole cluster with a longer budget (`CASE_TIMEOUT_SECONDS`
  10800, `launch-run.sh`), after `hdfs-compose-cost`; they must reach FIXED_POINT and COMPOSE. Then measure EXPLORE's
  re-asked arms (07: 203 arms asked ~7.8 times under different dependence digests; 47 of 189 changed verdict) and its
  1 GB `slots.jsonl` rewritten every round before changing anything.
- **24 26 37** (budget-cut in HG5A), **33** (FREEZE fixed), **50** (array identity fixed): rerun.
- The owner's bound rule (RULES): a declared bound may stop exploration only as a named, rare last resort. Mark an
  end at the declared bound (REGION_PATH_WAVE_BUDGET_REACHED) visibly in result.json (`bounded: {by, detail}`),
  report.py and triage.py; count such cases every round.
- Scope batch 2 (the owner's top priority "让更多的都可翻转"): 29/30 recoveryId (a SCOPE boundary for system callees
  out of scope; growth spends on demanded rows; follow receivers built by calls); 17 the lease grant state; 15/39 a
  turn for tracked-write ordering (complete vs IBR); 07 an export capture where the QJM client sets the segment it
  attached from jn1's prepareRecovery response into its acceptRecovery request (`setStateToAccept`), so jn0 pairs by
  HANDLE instead of an unattested arrival.
- A possible flake: Mockito `UnfinishedStubbingException` in `TestBlockRecovery2`.
- **Swap the too-challenging**: a check still a RUN_DEFECT after a reasonable fix round is replaced by an alternate,
  in this order: 05 or 06 (QJM output stream, NN->JN; clean UNSAT in HG2), then 04 (client ack timeout, CLOCK), then 38
  or 45. Never 42, 44, 46, 47. Update `checks.tsv`, `selection.txt` (branch `study`) and `docs/checks/` with the reason.

### 6. Speed (PERFORMANCE.md §5)
- The ledger's remaining ~1.6x over real use is step charges at their start heap (kept: a refused growth would end a
  planner).

### 7. The next round, then the end of HDFS
1. After 1-4 land: a full round of the 46 on the merged body (`tools/adhoc/sweep.sh`, 2 heads/host, `PRUNE=0`, the
   next name `HG8`); watch with `round-watch.sh`, `round-slow.sh <round> HG7` (or HG5A), stop cases at 80+ seed
   give-ups only if the time model has not landed; verify each finished case with `round-verify.sh`.
2. Cases the sweep's time limit cut: rerun with a longer budget (a large closure must converge).
3. The final verdict of each of the 46 on the final body (concurrently, through the ledger).
4. Check every `.smt` by hand: causal chain, symbols, propagation, against the HDFS code; write the chain of each SAT
   and a one-line reading of each UNSAT into STATUS.
5. Merge `system/hdfs` into `main`; push only when the owner asks.

### 8. Cleanup still owed (RULES: every change deletes what it replaces)
- Cleanup batch 1, phase 2 (`brief-cleanup-1.md`): the items in files that were busy (MapFields.safe/Text.safe copies,
  LineageScan's classFiles copy, ScheduleLog.prefixFile, run_engine.sh's `input_flag=-j` branch, the test-only
  accessors where a test can use the real path), `src/test/resources/external-callers.txt`'s stale rows (they point at
  old /opt checkouts; current trees call MessageDoors, not CausynthTraceRecorder), the forwarding layers (the door API
  is four hops: tree -> shim -> MessageDoors -> CausynthTraceRecorder -> RuntimeTraceContext; MessageDoors should call
  RuntimeTraceContext directly), CausynthTraceRecorder's ~1,100 lines of offline aggregation into its own class,
  CausynthPipeline's weaves apart from analysis orchestration, DependencyRole (a digest change).
- The VM's dead natives and `exportLeaf`/`mintLeaf` with the next VM build (STATE §3).
- Loop-bound rows keyed structurally, not by Jimple unit ordinals (`loopSiteId` `...>#u53`): one statement added to a
  method (r5 deleted `Client#sendRpcRequest`'s hand `endInbound()`) shifts every later `#uN` and refuses the case's
  `loop-bounds.jsonl` (BOUNDED_LOOP_BODY_BOUND_SITE_UNDECLARED) until its rows are renumbered by hand.
- Merged branches and their worktrees, stale snapshots (STATE §2-§3), `/bigtemp/vnr3ne/readout-stream/` (4.2 GB) once
  its numbers are in STATUS, finished agents' `gc-out` dirs, `/bigtemp/vnr3ne/gc-out/diag-11741` after 11741 passes.

## Solr (next; `system/solr` = main today)

**1. Bring the body.** Merge `main` (with the HDFS body) into `system/solr`. The WIRE-CODEC runtime is gone from the
body; check that no Solr tree hook calls a removed door (`MessageDoors` payload/bytes overloads; the 3-arg
`stored`/`fetched` stay). Close the `MessageDoors.consumed` gap (a consumed Overseer item states its message key).
The Solr trees' `CausynthHttp` ends the served exchange by hand before each send: replace it by the request start at
the client's invoke point (`MessageDoors#requestStarting`/`#requestEnded`, IDENTITY §3), ending a received response only.
Rebase `solr-bug-reindex` onto it and fix its solr-18413 regression first:
- The seed replay stalls 103,812 times. A store-write slot is held while the Overseer's
  `waitForCoreAdminAsyncCallToComplete` poll outruns its recorded WAKE count. Read the jstacks in
  `gc-out/sbr/evidence/` (the time model of HDFS §3 may cover it).
- Then SBR26b: give SEED's trace aggregation the heap a 2.1 GB trace needs, or stream it.

**2. Mark the checks.** Mark the 13 checked study points in one Solr tree branch, from `docs/checks/SOLR.md` and
`SELECTION.md`:

```
05 07 09 10 13 14 19 21 22 31 38 39 40
```

22 is solr-18406's throw (already marked). Each point gets its cluster test as the workload and an experiment
directory like `experiments/hadoop/hdfs-adhoc` (a `checks.tsv`).

**3. The five admitted bugs:** migrate-buffer-leak #17, overseer-lock-leak #50, snapshot-no-active #16,
restore-construction #26, tra-start-overwrite #20. For each: the marker, the workload (an existing test where one
reaches it), the doors or roots its counterfactual needs (`docs/checks/VERIFIED-BUGS.md`), then a dev run.

**4. reindex-cleanup (#04).** The witness is #2's post-alias `setData` door faults.

**5. Run the group.** All 20 cases with no regression of solr-18406 and solr-18413, `.smt` checks, then exclusive
runs.

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

**WIRE-CODEC (`wire-codec-p1`; the system body carries none of it).** Resume only when a system's chain needs a
codec hole (a value carried inside an opaque payload); then rebase it onto the body, which deleted its runtime.

**VM performance.** The VM sends each expression node once per channel (STATUS open item 41). A plan budget should
be derived from the seed's measured cost.
