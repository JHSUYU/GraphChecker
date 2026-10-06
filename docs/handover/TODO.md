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

### 3. The time model (the start-up/clock family: 01 17 21 22 23 25 34 35 43)
- The cause (HG6 probes, DW1-DW5a): a DataNode actor's turn decides by `monotonicNow` (heartbeat, block report due,
  `BPServiceActor.Scheduler`) and by state set on threads that make no schedule events (block-report leases, IBRs),
  while the VM replay runs slower than the recording; start-up state (a DataNode's next heartbeat) is set from the
  live clock before or as the window opens. The total order (`ScheduleLog`) orders events but not clock VALUES.
- The design proposed on `hdfs-time-model` (`ccbf0f8a0`'s commit message), to review before any code: the recording
  stamps every schedule event and STARTUP mark with its clock readings; every application clock read goes through
  `Clocks` (as the parked C1 did); in a replay the application sees the recording's timeline, never past the stamp of
  the frontier slot (before the window: the next STARTUP mark), never backwards; a declared CLOCK root keeps its skew
  on top (CLOCK_SKEW still works); no read is keyed (C1b's shared keys and C1's run cap avoided). Expected: 17 and 43
  gain most; 22-25, 34, 35 where turns read the clock (their IPC-handler and monitor waits are timed waits, not clock
  reads); 21 and 01 partly.
- C1's lessons (`hdfs-clock-replay` 22520bf02): replaying in-window reads alone mixes two timelines (state set before
  the window from the live clock); keying pre-window reads by node|handoffs handed threads each other's times.
- Validation: probe 01 17 21 22 23 25 34 35 43 twice each (give-ups, target reached) against HG5A and DW5a; then
  11741, 17897, bug1, 16, 17960 to verdict (CLOCK_SKEW in 11741 must still move its clocks). A schedule/time change:
  a review agent before the merge, then the next full round.
- If after one reasonable round a check still cannot reach its target, swap it (below) rather than dragging on.

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
- The owner's bound rule (RULES): every BOUNDED case of a round (`round-verify.sh`'s count, `result.json` `bounded`)
  is read: a large closure gets the cluster and a longer budget, a redundant one is an engine defect. HG8F/HG8W: 05,
  06, 08, 09 and 11741 read only `region_path_max_paths_per_region` (32) recorded paths of some tasks (17-194 task
  rounds each).
- Scope batch 2, sorted by the 46-check goal (the formula is wrong or incomplete first): (A) fixes in flight --
  `hdfs-decider-open` (15, 17, 39, maybe 16, 40: a guard on a helper's return whose deciding branch has an open arm;
  `BlockInfo.java:374`) and then `hdfs-relay-export` (07: the QJM client relays jn1's prepareRecovery segment into
  acceptRecovery, `QuorumJournalManager.java:374/394`, `setStateToAccept`; jn0's StartTxId/EndTxId handoffs have no
  producer). (B) right for what the code does, widening only makes more flippable, AFTER the 46:
  - 29/30 recoveryId: the anchors decide on the block-pool map (written at DN startup, removed at shutdown) and
    `bpServiceToActive` (`BPOfferService.java:536`; its in-window writer `:612` is gated by the NN's HA state, constant
    ACTIVE without HA); `BlockRecoveryWorker.java:177` is a way guard both seeds passed.
  - 17 (block-report lease) and 39 (IBR ordering): turns on threads that make no schedule events (the DN actor's lease,
    the NN's `enqueueBlockOp` thread, `BlockManager.java:5595`) -- the time-model/turn work.
  - An identity compare of a tracked reference with an enum constant states no term (VM.md §5.2): with one, 39's open
    arm would move by writer arm instead of by replay.
  - 05: decided by a thread-local buffer invariant (`QuorumOutputStream.java:106`).
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

**CONFIRM: a session "itself the run" may have planted more than the model moved** (claim-loop review, 2026-10-05).
`explore.Moved#ranBy` -- `ConfirmMain#realizedBy` and COMPOSE's own-run rank both judge by it -- checks the model's
moved roots at their values, its clocks and that the world planted no pairing, but not roots the session's world
planted beyond the model's moved set (`rootAssignments` outside `movedRoots`): such a session ran another world, yet
confirms the claim without a replay. The realized sessions seen so far plant exactly the moved root (SL1-4 hdfs-adhoc-10
`2aa5e579a4a739bf-95b10301`, CL1 `b0e2952cbf454340-ca8612dd`: one assignment each). Strict: a planted root outside the
model's moved set at a value other than its recorded one is no realization (a replay decides). Strictness of CONFIRM:
a review agent reads the change.
