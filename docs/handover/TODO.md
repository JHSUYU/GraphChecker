# TODO at the handover of 2026-10-06

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

## HDFS (current system; `system/hdfs` 176acc689 + this handover's docs, trees r5 -> r6, image `vm-hg5`)

Where it stands (STATE §4, checks [../checks/README.md](../checks/README.md), how to check [CHECKING.md](CHECKING.md)):
known bugs 9/10 PASS on the merged body (HG9B) and 11741 PASS with a clean cone on (b2) (AR3) and on the time model
(TM16); study checks done 20 (19 UNSAT + 10 SAT), fixed on a branch and owed only a merge/rerun 6 (12 14 05 06 08 09),
in work 2 (07 39), the time-model family 8 (21 22 23 24 25 34 35 52); no new bug. Every in-flight branch is listed in
STATE §2 with its head, gate state and next step. One coding agent per area (AGENTS.md); each merge is one change,
gated, then the next.

### 1. Merge what is gated or nearly (in this order; each: merge system/hdfs into it, build + shell test, merge)
1. **`hdfs-export-weave`** (A1; STATE §2): every static export site woven, the witness chain closure (chain mode,
   `WITNESS_CHAIN_OPEN`), verdict-based cone gating (`unboundOffWitness`, `UNSAT_CHAIN_OPEN`). Owed: a second AW-11741 and
   AW-12 on its head (AW4-12: SAT, unbound 0, off-witness 3; AW4-11741 PASS, all 11 handoffs bound). Fixes 12.
2. **`hdfs-frontier-depth`** (D1): set-valued arm keys, `EXPLORE.drift`, and the owed-path bound (count only paths
   offering an owed arm; paths beyond the bound deferred, never dropped). 05 06 08 09 reached FIXED_POINT with
   `bounded: null`, 17897 PASS; owed: 11741 x2 on its head with `CASE_TIMEOUT_SECONDS=10800` (FD3/FD3b were stopped
   unfinished at the handover).
3. **`hdfs-solver-fallback`** (D1): a host solver killed at its memory hold is placed through the ledger by its
   measured peak, or fails by name at once (it asked 16 GB on its pinned host and waited 3900 s). Owed: one live case.
4. **`hdfs-time-model`**: merged, then REVERTED on hdfs-int (8f9acc7c4, 2026-10-06): its body made 19, 26 and 37 miss
   their declared occurrence (a timed-out monitor wait waiting for its WAKE turn with the program's monitor held); the
   time family runs on the r7 tree's workarounds instead (owner: the time model by workarounds only). Delete
   `hdfs-clock-replay` and `hdfs-time-model` once HDFS is done.
5. **The r6 trees + `hdfs-ipc-handoff-name`** (A2, stacked on the time model): build both r6 trees properly
   (OPERATIONS §1 "HDFS trees (next)"), javap the hooks on a case's classpath, rerun every HDFS workload test on r6,
   switch every `case.sh` in one commit; gate: 21's and 52's stalls by blocking slot before/after (`probe/stalls.py`),
   17897/bug1/17960 unchanged, one non-clock case. Then the full time-model family on the merged body.
6. **`hdfs-codec-capture`** (A4; design approved, a plan-only WIP commit): after export-weave. The IPC door walks the
   message (export from the message's own fields at the outbound door; bind each decoded element to its message object
   after the parse; attach at the demanded getter from the receiver's binding; a relay re-stages the original producer);
   the engine's runtime classes and generated protobuf messages/builders are never state; the setter capture loop and
   the three protobuf WIRE_FLOW rows deleted. First step: check that Soot loads a generated getter's body
   (`Scene.forceResolve(owner, BODIES)`; else ASM). Fixes 07 (relayed segment) and 11741's HELD carrier read. Gate:
   07, 12, 11741 with cone unbound 0; producer growth on 07 and 11741 unchanged or explained (exports are stated at the
   door's occurrence); a review agent before the merge.
7. **Rule 1**: measured and not merged (the throughput bar): the kept conditions of the prefix closure as the key
   (`hdfs-rule1` 7d2819214) asked 470 arms on 05 in 30 min against the merged key's 187 in all; the own-fault key
   (`hdfs-u18-fix` 8ed56ddeb) 269 in 27 min. The merged key keeps the u18#3 gap (STATUS open defect 51).

### 2. The time-model family (21 22 23 24 25 34 35 52) after the merges above
A2's first divergences on tm13-tm16 (`/bigtemp/vnr3ne/gc-out/hdfs-time-model/probe/runs.txt`): 25 34 35 seed replays
clean (0-2 give-ups) except under load (25: 238 at `Shell.runCommand` starts) or the NameNode edit path after an
addBlock meets NotReplicatedYet (25: 89, 22); 22 varies 0-66 between runs (a DataNode heartbeat turn not due in the
window: a recorded 2999.2 ms gap; its recordings' start-up took 9-283 s); 21: 14 of 17 stalls are the IPC Reader's
hand-off naming (fixed by `hdfs-ipc-handoff-name`), its first a heartbeat SEND that never happened; 23: 0 give-ups on
tm13; 52: a late `FSEditLogAsync` claim at slot 1710 (open), then the NameNode restart phase; 24 not probed yet.
**Relaxed by the owner (2026-10-06, RULES):** for these eight, workarounds are allowed and an approximately right
`.smt` is enough (residual gaps named in STATUS). **Quick workarounds to try first** (owner 2026-10-06 asked for fast ones; RULES "Workarounds, with measure": one general
point in the HDFS adapter/test configuration, listed in STATUS, never chosen by a case's expected mechanism; check that
no selected check's guard reads the setting it changes):
- **Quiesce before the window** (21 22 23): in `CausynthCluster`'s automatic mode, before opening the recording window,
  trigger one heartbeat and one full block report per DataNode (`MiniDFSCluster#triggerHeartbeats`,
  `#triggerBlockReports`) and wait for the IBR queues to drain, so start-up timing state is settled outside the window
  (22's start-up varied 9-283 s and a slow one puts more heartbeat turns inside it).
- **No external processes in the test cluster** (25): `fs.getspaceused.classname` to a JVM-only implementation, so no
  `du`/`df` fork (`Shell.runCommand`) runs during a replay.
- **IBRs sent at once** (22 23): `dfs.blockreport.incremental.intervalMsec=0`, removing `waitTillNextIBR`'s timed wait.
Validate each by probes (seed give-ups, target reached, two runs each), then 17897, bug1, 17960, 11741 unchanged.
If a check still cannot reach its target after that round, swap it (only 04 is left as an alternate; RULES).

### 3. The other open checks
- **39** (RUN_DEFECT, `OPEN_ARM_UNANSWERED`) and **40** (an UNSAT resting on `dfs.namenode.replication.min`'s [1,1]):
  on `hdfs-open-arms` (agent S, approved designs A and B): a faithful replay that never entered the open arm's
  occurrence refutes its world (`WORLD_REFUTED`) and the flip is asked again without it; an integral configuration's
  domain takes every literal a recorded decision compares it with, within its own validation. In testAppendTwice the
  arm `uc != null` is unreachable (the append runs after `close()`, which needs the block COMPLETE: replication 1,
  minReplication >= 1), so 39 is expected to close UNSAT on refuted worlds; 40's flip `minReplication >= 2` fails the
  workload's create. Owed: the offline gate on HI2 corpora, live 39 40 15 16 38 17960, a review agent on A.
- **07**: codec capture (§1.6); its UNSAT has 6 unbound relayed-segment handoffs today.
- **Scope (B)**, after the 46 (right formulas that widening would only make more flippable): 29/30 recoveryId (the
  block-pool map written at DN startup; `bpServiceToActive`'s in-window writer gated by HA state); 17's lease and 39's
  IBR ordering (turns on threads with no schedule events); an identity compare of a tracked reference with an enum
  constant states no VM term (VM.md §5.2); 05's thread-local buffer invariant.
- A possible flake: Mockito `UnfinishedStubbingException` in `TestBlockRecovery2`.
- **Swap the too-challenging**: a check still a RUN_DEFECT after a reasonable fix round is replaced by an alternate.
  Used (owner 2026-10-05): 05 for 32; 06, 38, 45 for 01, 17, 43; only 04 (client ack timeout, CLOCK) is left; never
  42, 44, 46, 47. Update `checks.tsv`, `selection.txt` (branch `study`) and `docs/checks/` with the reason.

### 3b. A loop root's prefix as its own occurrence (design; 21 runs on a tree workaround meanwhile)
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

### 4. Speed (PERFORMANCE.md §5)
- 11741's replays under the time model (258 s median vs 165-207 s); the ledger's ~1.6x over real use (step charges at
  their start heap).

### 5. The final round, then the end of HDFS
1. After §1 (and §2's workarounds) land: a full round of the 46 on the merged body (`tools/adhoc/sweep.sh`, 2 heads
   per host, `PRUNE=0`, **`CASE_TIMEOUT_SECONDS=10800`**, the next name `HG11`, case list
   `/bigtemp/vnr3ne/gc-out/hdfs-study/rounds/HDFS46.cases`); watch with `round-watch.sh`/`round-slow.sh <round> HG9`.
2. Verify each finished case with `round-verify.sh` and CHECKING.md §1 (no BOUNDED, no UNBOUND, FIXED_POINT or
   confirmed); rerun anything cut at a longer budget.
3. Hand-check every `.smt` (CHECKING.md §2: legend, chain, symbols, propagation against the HDFS code); write the chain
   of each SAT and a one-line reading of each UNSAT into STATUS.
4. Merge `system/hdfs` into `main`; push only when the owner asks.

### 5b. Later (owner 2026-10-06): the two-phase final run
For a clean final acceptance run after the two branches are done: (1) the ~36 short cases a few at a time (6-8
concurrent: their time is serial SEED, recording and seed replay, so exclusivity buys them little); (2) the deep
closures (11741 08 09 05 06 11 14, 07) one at a time with the whole cluster (their cost is hundreds of obligation
replays, which fan out: 09 has 653 verdicts over 9 tasks and 7 regions), agents offline meanwhile. Expected ~4-5 h in
all versus ~9-10 h with every case exclusive. Not now: today each branch only runs its cases to their `.smt`.

### 6. Cleanup still owed (RULES: every change deletes what it replaces)
- Cleanup batch 1, phase 2 (`brief-cleanup-1.md`): MapFields.safe/Text.safe copies, LineageScan's classFiles copy,
  ScheduleLog.prefixFile, run_engine.sh's `input_flag=-j` branch, test-only accessors, `src/test/resources/
  external-callers.txt`'s stale rows, the four-hop door API (MessageDoors should call RuntimeTraceContext directly),
  CausynthTraceRecorder's offline aggregation into its own class, CausynthPipeline's weaves apart from orchestration,
  DependencyRole.
- `hdfs-refactor-compose` step 5 (Composer.compose/run as steps; SmtLowering -> VmTermLowering + SmtSymbolTable), gated
  identical; merge system/hdfs into it first.
- The VM's dead natives and `exportLeaf`/`mintLeaf` with the next VM build (STATE §3).
- Loop-bound rows keyed structurally, not by Jimple unit ordinals (a tree change renumbers `#uN`).
- Merged branches and their worktrees (STATE §2), stale snapshots (`tools/rounds/snapshot-gc.sh`), finished agents'
  `gc-out` dirs, `/bigtemp/vnr3ne/gc-out/diag-11741`, `/bigtemp/vnr3ne/readout-stream/` once its numbers are in STATUS.

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

**5. Run the group.** All 20 cases with no regression of solr-18406 and solr-18413, `.smt` checks (CHECKING.md), then
the final round of the group (concurrently, through the ledger).

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
