# TODO at the handover of 2026-10-04 night

Order:
1. HDFS to the end, as one group with no regression.
2. Then Solr.
3. Then HBase.
4. Then ZooKeeper.

The owner: "hdfs所有的case跑完为一组，不要有回归。然后就到另一个系统". Each system is finished when every one of its
checks has an exported `.smt` that is right (SAT confirmed, or UNSAT) and every known bug of it
passes. The final acceptance runs each case alone on the whole cluster. Branch and path details are
in [STATE.md](STATE.md); commands are in [OPERATIONS.md](OPERATIONS.md).

## HDFS (current system; `system/hdfs`, tree `gc/hdfs-study-r3`, image `vm-hg5`)

**Status 2026-10-05 04:00 (lead).** Done and merged into `system/hdfs`: §1e (bug2, `hdfs-request-in-hand`), measured replay charges (`hdfs-measured-charges`), the FREEZE digest and array-identity fixes. HG5A ran the HG5 body (STATE §4). In flight, one agent each: §1 decisive-verdicts (fixing its review's 4 blockers, then merge), §2 HG6 = `hdfs-draw-sites2` (probes), identity (`hdfs-address-shared`: rule B done; next the planned-shape rule for hdfs-11741's regression, then the putter's frames for 14; 07's shared getSegmentInfo endpoint), closure E1 for 16 (`hdfs-closure`, after §1), cleanup batch 1 (`hdfs-cleanup-1`). Merge order: decisive, HG6, address-shared, closure, cleanup phase 2. Then the next round of the 46 (§3) on the merged body. Parked: the QJM obligation snowball (dependence-key granularity), the 8 GB head reserve (heads peak at median 0.7 GB, p99 7.8), SEED's Soot passes being IO-bound on NFS during a sweep's first wave.

### 1. Finish `hdfs-decisive-verdicts` (one coding agent)

The worktree is `/bigtemp/vnr3ne/wt/gc-hdfs-decisive-verdicts` and the brief is
`/bigtemp/vnr3ne/analysis/study-2026-10-04/brief-decisive-fix2.md`. The lead's decisions are in that
brief and bind.

**a-d, g, h: done on the branch** (lead review pending, then the merge into `system/hdfs`):
- a. CONFIRM: `refutes` only for "CONFIRM refutes:" (the run as recorded); every "CONFIRM refused:"
  is a RUN_DEFECT; a way-guard witness is planted and judged by the fatal, its closure cut at the
  manifest's `cutoff` (37723587e).
- b. One rule for values COMPOSE cannot bind (`SmtLowering#unbound`): FREE where the stated
  producer moves, HELD "producer unstated" where no row states it (unattested arrivals, reads of
  versions no write states, frames found through the refused attach's VM handle); `concrete[]`
  rows state `pathId` and `reason`; UNSAT_CLOSED's meaning stated (7f19e2eba). A read of a
  container state the VM marked incomplete keeps being refused (honest: an unhooked mutation ran
  between its version and the read; the hold tried in 9119bde4a was reverted, 0105a1b4a); the fix is
  admission of that unplanned occurrence, owned by the identity agent (11741 `allKeys`,
  hdfs-adhoc-32).
- c, d. `restsOnRefutations`; report.py FREE/HELD wording, witness rows first (ce7df0152); a refuted
  model is no part of the run's own world (e44a4a632).
- g. The run as recorded is a world: a writer whose block the run broke gets the observed arm
  (a6681529b; hdfs-adhoc-16 decides). QJM 07's 57 contradictions have another cause: an identity
  defect (every `Journal#getSegmentInfo` export of `SegmentStateProto.EndTxId` in a session states
  one producer endpoint, so each arm binds both arrivals at `acceptRecovery` to one value).
- h. EXPLORATION_CUT: a forced end that still owed arms is one BLOCKING row, so no UNSAT closes
  over that corpus (0f0d331f7).

**e. bug2's lost key-id binding.** The cause is found: `Identity#requestInHand` (ffa0cb4d3). After
an IPC door fault the request gets no receipt and stays "in hand". Every later thread start on that
thread then appends `:NamenodeProtocol.getBlockKeys` to its name, so the SPS daemon's occurrence,
which sends the key id, gets an address no plan instrumented.
- Fix, on branch `hdfs-request-in-hand` (worktree `/bigtemp/vnr3ne/wt/gc-hdfs-request-in-hand`): a
  message door's marker that comes out true clears the request in hand (`Identity#doorFaulted`),
  called by a replay's mint (`RootMint`, which learns the marker's name from the scope map's FAULT
  input, `marker`) and by a native plant (`RecordingPlant#marker`); a LOCAL_IO door's does not.
- Live, snapshot `~/gc-run/rih1` (`99e8512d9`), image `vm-hg5`, `/bigtemp/vnr3ne/gc-out/hdfs-request-in-hand/
  accept-RIH1-17899-bug{1,2,3}`: all three PASS, MARKER_FLIPPED by the target DataNode heartbeat's IPC
  response door, confirmed, reproduced natively 10/10; cone.py without the FREE exemption (`0219d06b8`)
  finds the moved root in the cone and 0 unbound boundary variables. bug2's one fatal boundary variable,
  `data-encryption-key-id` at the DataNode's SASL server, is bound by its message family to the SPS's
  producer; no session names a start by a faulted request's verb. Next: merge.
- Done when bug2's witness binds the key id across the wire and `cone.py` passes without the
  exemption.

**f. Gate.** Offline gate on V25, HG4's 46 and HG5A's 07/08/09/16/17/24/32:
`/bigtemp/vnr3ne/ab/hdfs-decisive-verdicts/finish/` (`gate-head.sh`, `table.py`). Then a review agent
re-reads the soundness batch before the merge into `system/hdfs`.

### 2. Finish HG6 = `hdfs-draw-sites2` (one coding agent)

Worktree `/bigtemp/vnr3ne/wt/gc-hdfs-draw-sites`, branch `hdfs-draw-sites2`; runs in
`/bigtemp/vnr3ne/gc-out/hdfs-draw-sites/accept-DW*` (one line each in `hg6/runs.txt`), snapshots `~/gc-run/hds11`
(the branch before the merge of `4bfe1a6e1`) and `hds12` (the same without the turn rule).

**a. Canaries.** 17897 PASS, MARKER_FLIPPED (DW1). 11741 (DW2, stopped after 63 min): its exposure
`f9fb3c4ff841e29b` composes UNSAT_CLOSED NO_SUPPORTED_WITNESS (the witness path rests on an
UNSTATED_VALUE map read), as on HG5A-36; no BLOCKING `TOPOLOGY_DIVERGENCE` (41 DIAGNOSTIC ones).

**b. Probes** (seed replay, stopped after IMPORT). The give-ups listed at the stop on `3a27177b3` were
counts of replays killed early (43 had taken 151 of 8074 slots), so the base is HG5A (system/hdfs):

| case | HG5A: lines / slots given up / taken of order | DW3 (branch) | DW4 (branch without the turn rule) |
| --- | --- | --- | --- |
| 17 | 97 / 1578 / 2022 of 2268 | 89 / 170 / 1897 of 2062 | |
| 21 | 47 / 89 / 2322 of 2651 | 108 / 230 / 1894 of 2037 | 158 / 291 / 1502 of 1656 |
| 43 | 39 / 213 / 3707 of 7883, target not reached | 59 / 310 / 4021 of 7937, not reached | |
| 23 | 144 / 408 / 6293 of 13056 | 234 / 386 / 5018 of 10852 | |

22, 25, 34, 35 (the same `testVersions` workload as 23) and 01 were not probed on the branch. The
large counts are the clock class: a DataNode actor's turn decides by `monotonicNow` (heartbeat and
block report due, `BPServiceActor.Scheduler`) and by state event-less threads set (the NameNode's
block-report leases, at most 6 pending for 17's 9 DataNodes; a block's IBR), and the VM replay runs
slower than the recording: 43's dn2 turn #2 sent a heartbeat its recorded turn did not (seq 105) and
its IBR came after its slot was given up; 17's turn-#1 block reports were not made; 23's IPC handlers
and `CacheReplicationMonitor` time out where the recording's never did. 21's
`OCCURRENCE_ADDRESS_SHARED` remains (one heartbeat endpoint for every turn of the DataNode actor run
occurrence opened under the test's request): `hdfs-address-shared`'s package.

**c. Review and merge.**
- A review agent reads the batch (schedule/identity: high risk).
- Then merge into `system/hdfs` (the branch already holds `4bfe1a6e1`).
- With the next commit to the r3 tree (not before: every HDFS case reads it): delete
  `DataXceiver.java:301-302`'s hand `CausynthMessagePropagation.endInbound()` before `beginTick`;
  `MessageDoors#beginTick` ends the served exchange itself now.
- Delete `hdfs-draw-sites`, `hds8`-`hds12` and `/bigtemp/vnr3ne/wt/gc-hdfs-seed-stalls` afterwards.

### 3. The next live round of the 46

Run it on `system/hdfs` with both merged: tree r3, image `vm-hg5` (unless a VM change lands). The
command and the case list `rounds/HG5.cases` are in [OPERATIONS.md](OPERATIONS.md) §4.

**Watch.** Use the round watcher. Compare every case's time with HG4's. Stop and debug any case far
slower than its history.

**Read each result.**
- **UNSAT**: `candidate.smt2` is the full free-root formula, and a standalone z3 re-solve gives
  unsat.
- **SAT**: confirmed, and the chain is checked against the code.
- **RUN_DEFECT**: a bug to fix.

### 4. The remaining HDFS defects (after HG6), by class

**Start-up family 21–25, 34, 35.** What remains after HG6. Each one's seed replay must reach its
target with few give-ups.

**Clock/draw class 01, 17, 43.**

**Performance.**
- QJM 07/08/09 (~82 min) and 15 (~61 min): obligations refused at planning (ADMISSION_GAP) dominate
  EXPLORE. Cut them with a general rule.
- 16: a z3 timeout in the re-compose after a refutation.
- 07: self-contradictory paths.

**Scope batch 2** (the owner's top priority: "让更多的都可翻转").
- 29/30: recoveryId. A SCOPE boundary for system callees out of scope; growth spends on demanded
  rows; follow receivers built by calls.
- 17: the lease grant state.
- 15/39: a turn for tracked-write ordering (complete vs IBR).
- 07 (later, SEED): an export capture where the QJM client sets the segment it attached from jn1's prepareRecovery response into its acceptRecovery request (`setStateToAccept`), and jn1's own response export of it, so jn0's attach pairs by HANDLE instead of arriving unattested (hdfs-wire-half, `f4a325af7`).

**A possible flake.** Mockito `UnfinishedStubbingException` in `TestBlockRecovery2`.

**Swap the too-challenging.** A check still a RUN_DEFECT after a reasonable fix round is replaced
by an alternate, in this order:
1. 05 or 06 (QJM output stream, NN→JN control plane; clean UNSAT in HG2).
2. Then 04 (client ack timeout, CLOCK).
3. Then 38 or 45.

Never use 42, 44, 46 or 47. Update `checks.tsv`, `selection.txt` (branch `study`) and the
per-system table with the reason.

### 5. The end of HDFS

1. Run each of the 46 cases alone on the whole cluster.
2. Check every `.smt` by hand: causal chain, symbols, propagation. Write the chain of each SAT and a
   one-line reading of each UNSAT into STATUS.
3. Merge `system/hdfs` into `main`. Every system branch takes the body from there.

## Solr (next; `system/solr` = main today)

**1. Bring the body.** Merge `main` (with the HDFS body) into `system/solr`. Rebase
`solr-bug-reindex` onto it and fix its solr-18413 regression first:
- The seed replay stalls 103,812 times. A store-write slot is held while the Overseer's
  `waitForCoreAdminAsyncCallToComplete` poll outruns its recorded WAKE count. Read the jstacks in
  `gc-out/sbr/evidence/`.
- Then SBR26b: give SEED's trace aggregation the heap a 2.1 GB trace needs, or stream it.

**2. Mark the checks.** Mark the 13 checked study points in one Solr tree branch, from
`/bigtemp/vnr3ne/analysis/study-2026-10-04/solr.md` and `SELECTION.md`:

```
05 07 09 10 13 14 19 21 22 31 38 39 40
```

22 is solr-18406's throw (already marked). Each point gets its cluster test as the workload and an
experiment directory like `experiments/hadoop/hdfs-adhoc` (a `checks.tsv`).

**3. The five admitted bugs:**
- migrate-buffer-leak #17
- overseer-lock-leak #50
- snapshot-no-active #16
- restore-construction #26
- tra-start-overwrite #20

For each: the marker, the workload (an existing test where one reaches it), the doors or roots its
counterfactual needs (`VERIFIED.md` has each one's chain and counterfactual), then a dev run.

**4. reindex-cleanup (#04).** The witness is #2's post-alias `setData` door faults.

**5. Run the group.** All 20 cases with no regression of solr-18406 and solr-18413, `.smt` checks,
then exclusive runs.

## HBase (`system/hbase` = main today)

**1. Settle `hbase-startup`'s two design questions** (the lead decides; see
[STATE.md](STATE.md) §2):
- An identity rule for threads started by libraries (ZooKeeper's EventThread, Netty event loops).
  They must not inherit their racing creator's frames.
- Message-bound exports for a value exported on one thread and sent by another after a queue. This
  is WIRE-CODEC's message-bound exports, so align with `wire-codec-p1`.

**2. HBase #14 (master-active-time) to a confirmed CLOCK witness.**

**3. Mark the 17 checked study points:**

```
04r 07r 08 10 11 12 13 14 15 19 20 21 22 24 31 34 37
```

04 and 07 are re-sited to the server: `AbstractStateMachineTableProcedure.java:163` and
`SnapshotManager.java:1046`. Tables are in `hbase.md`.

**4. The two admitted bugs.**
- backup-lock-reply-lost: needs a RESPONSE door on HBase RPC (`checkAndMutate` with NO_NONCE).
- ns-rsgroup-removal: STATE re-pairing of `removeRSGroup`'s namespace read.

**5. Run the group of 20.**

## ZooKeeper (`system/zookeeper` = main today)

**1. Merge `hb-schedule` + `hb-sync`.**
- Run the offline gate on V25.
- Live runs of quota-init, election-offer and 11741, comparing arm counts and refutations with V25.
- The ZooKeeper tree with the RESPONSE door is `gc/zk-unified-hb` `47ddc8b36`.

**2. A quorum adapter.** Every selected ZooKeeper study test is a quorum test. Register each quorum
peer as a node; open the window once the quorum is up.

**3. Mark the 10 checked points:**

```
01 02 03 04 06 07 10 11 12 13
```

05 is a dead throw; 08 and 09 have no path. Tables are in `zookeeper.md`.

**4. zk-bugs-container-reuse (#33).** A self-written ClientBase test; STATE re-pairing of the
client's node-map lookup to the cleanup's delete, the election-offer mechanism.

**5. Run the group of 13.**

## Cross-cutting (engine), when a system needs it

**WIRE-CODEC (`wire-codec-p1`; the system body carries none of it).** It needs an 11741 canary
verdict and a chain check, then its
round. The Solr `wire.jsonl` (P3) comes after `solr-bug-reindex`. P4 retires the WIRE_FLOW
machinery.

**VM performance.** The VM sends each expression node once per channel (STATUS open item 41). A plan
budget should be derived from the seed's measured cost.

**C1 (clock replay).** Only if a later case needs it, with the start-up time model in
`hdfs-clock-replay`'s commit message.

**Cleanup.**
- The merged branches and their worktrees ([STATE.md](STATE.md) §2).
- The stale snapshots in `~/gc-run`.
- `/bigtemp/vnr3ne/readout-stream/` (4.2 GB of measurement data) once its numbers are in STATUS.
- `gc-out` dirs of finished agent runs.
