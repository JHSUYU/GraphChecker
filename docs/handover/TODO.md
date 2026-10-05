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

### 1. Finish `hdfs-decisive-verdicts` (one coding agent)

The worktree is `/bigtemp/vnr3ne/wt/gc-hdfs-decisive-verdicts` and the brief is
`/bigtemp/vnr3ne/analysis/study-2026-10-04/brief-decisive-fix2.md`. The lead's decisions are in that
brief and bind.

**a. Build the WIP and settle refusals.** Build `66c22f440`. In `run_engine.sh`
`campaign_confirm_claim`, set `refutes=true` only when the reason says "CONFIRM refutes:". Every
other refusal ("CONFIRM refused:") is a RUN_DEFECT. Update the shell test and `ConfirmMainTest`.

**b. Item 2: one rule for values COMPOSE cannot bind.** Apply
`/bigtemp/vnr3ne/ab/hdfs-decisive-verdicts/fix2/frame-wip.patch`, then:
- An arrival with no attested producer is held at its recorded value and named "producer
  unstated" in `concrete[]`.
- So is a read whose writer no row states.
- A FRAME finds its producer through the refused attach's handle and the export row; its
  `movesWith` is that producer's roots. It is FREE when those roots move.
- State exactly what UNSAT_CLOSED means, in STATUS.md and in `ComposeMain`: no world of the
  explored corpus reaches the fatal, given the marker valuations each path ran and the held
  `concrete[]` values.

**c. Item 5.** An UNSAT whose unsat core names a `refuted_claim__` publishes `restsOnRefutations`.
The free-formula ask and the self-check must request the core whenever refutations were asserted.

**d. Item 7.** Fix the stale docs. `report.py` calls FREE rows "free (over-approximated)", and its
row cut never hides the witness path's rows.

**e. bug2's lost key-id binding.** The cause is found: `Identity#requestInHand` (ffa0cb4d3). After
an IPC door fault the request gets no receipt and stays "in hand". Every later thread start on that
thread then appends `:NamenodeProtocol.getBlockKeys` to its name, so the SPS daemon's occurrence,
which sends the key id, gets an address no plan instrumented.
- Fix, on branch `hdfs-request-in-hand` (worktree `/bigtemp/vnr3ne/wt/gc-hdfs-request-in-hand`): a
  message door's marker that comes out true clears the request in hand (`Identity#doorFaulted`),
  called by a replay's mint (`RootMint`, which learns the marker's name from the scope map's FAULT
  input, `marker`) and by a native plant (`RecordingPlant#marker`); a LOCAL_IO door's does not.
- Next: the review agent (identity change), then a live bug2 run, then bug1 and bug3 once each.
- Done when bug2's witness binds the key id across the wire and `cone.py` passes without the
  exemption.

**f. Gate.** Run the offline gate on V25 and on the HG4 corpora (none has run on these changes).
Then a review agent re-reads the soundness batch before the merge into `system/hdfs`.

### 2. Finish HG6 = `hdfs-draw-sites` (one coding agent)

The worktree is `/bigtemp/vnr3ne/wt/gc-hdfs-draw-sites`; probe snapshot `~/gc-run/hds8`.

**a. Canaries.** Rerun the 11741 and 17897 canaries to a verdict. On 11741, check whether the 3
BLOCKING `TOPOLOGY_DIVERGENCE` gaps (seen with C1) survive without C1.

**b. Gate and probes.** Run the V25 gate with `AB_HEAP_MB=4096`. Finish 17, 21, 43, 23, 25 and 35 to
a verdict, plus 01, which was not rerun. Their give-ups at the stop, on `3a27177b3`:

| case | give-ups |
| --- | --- |
| 16 | 3, and finished |
| 22 | 10 |
| 23 | 19 |
| 24 | 2 |
| 25 | 17 |
| 32 | 19 |
| 34 | 2 |
| 35 | 18 |
| 17 | 52 |
| 21 | 17 |
| 43 | 1 |

17's 52 give-ups need a look of their own: with C1 and no hold it had 18 and finished.

**c. Review and merge.**
- A review agent reads the batch (schedule/identity: high risk).
- Then merge into `system/hdfs`. The branch is based on `d916851fa`, before campaign-schedule, and
  runs CONFIRM inline: keep `system/hdfs`'s CONFIRM-as-pool-job and its remote-wait fix
  (`71df98a00`).
- Delete `hds8` and `/bigtemp/vnr3ne/wt/gc-hdfs-seed-stalls` afterwards.

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

**WIRE-CODEC (`wire-codec-p1`).** It needs an 11741 canary verdict and a chain check, then its
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
