# HDFS key-rotation failure experiments

This directory drives four bounded GraphChecker experiments for stale HDFS
data-encryption keys:

| Case | Vulnerable path | Workload |
| --- | --- | --- |
| `hdfs-17897` | striped file checksum | `TestEncryptedTransfer.testCausynthStripedFileChecksumRpcFailure` |
| `hdfs-17899-bug1` | Balancer `Dispatcher.PendingMove` | `TestBalancerWithEncryptedTransfer.testEncryptedBalancer1` |
| `hdfs-17899-bug2` | SPS `BlockDispatcher.moveBlock` | `TestExternalStoragePolicySatisfier.testCausynthSpsKeyRefreshRpcFailure` |
| `hdfs-17899-bug3` | `DataNode.DataTransfer.run` | `TestCausynthDataTransferRpcFailure.testReplicationAfterModeledKeyRefreshRpcFailure` |

`hdfs-17897` uses Hadoop `156dd3b276457e49736638f1b57b05d78b558a7e`
(the parent of its fix). The three HDFS-17899 cases use
`734dd8a67cd6df56b59ff75aa43de57834a0d248` (the parent of that fix). The
build explicitly emits Java 8 bytecode because the bounded concolic VM is a
Java 8 VM, even when Maven itself runs on Java 17.

## Modeled RPC failure

Each workload has one named explicit input:

```java
boolean rpcFails = CausynthFault.makeSymbolicBoolean("rpcFails");
```

For the three HDFS-17899 paths it guards the one block-key refresh that chooses
between the connector/DataNode's old state `S0` and the NameNode's refreshed
state `S2`. The successful concrete seed uses `rpcFails=false` and installs
`S2`; the alternate relation uses `rpcFails=true` and retains `S0`. The stale
key then flows through the ordinary data-transfer SASL username and reaches
the server's exact `allKeys.get(keyId) == null` exception target.

HDFS-17897 uses one `rpcFails` value for the whole striped block-group checksum
attempt. It models failure before every DataNode checksum RPC in that one
attempt, so the client exhausts the group and reaches the vulnerable final
`PathIOException`. It does not create a different fault variable per DataNode.

The fault is not an unconstrained post-hoc SMT variable. It is a normal
explicit-symbolic input recorded in the producer task, propagated through a
real concolic summary, and connected to the selected fatal occurrence by the
same exact RPC/heap edge ledger as the other inputs.

## Bounded model

The experiments reuse the schema-4 RPC projections in
`protocol-stubs.jsonl`. Complex `ExportedBlockKeys` values remain concrete
containers with a bounded observed shape; selected scalar leaves such as
`keyId` and `expiryDate` are separate symbolic ports. A producer with every
demanded output captured but no materialized solver input is retained as one
witnessed constant relation. Missing demanded outputs are still incomplete.

Long-lived roots arm the VM at the closest safe semantic point. If demanded
effects execute inside one unique target call, replay starts immediately
before that call; if they occur after an undemanded target, it starts on the
normal return edge. This avoids both recording an unrelated service prefix and
skipping writes performed by the target.

## Commands

Run one case with:

```bash
experiments/hdfs/hdfs-key-rotation/run.sh hdfs-17899-bug3 prepare
experiments/hdfs/hdfs-key-rotation/run.sh hdfs-17899-bug3 tasks
experiments/hdfs/hdfs-key-rotation/run.sh hdfs-17899-bug3 candidates
```

or run all three stages with:

```bash
experiments/hdfs/hdfs-key-rotation/run.sh hdfs-17899-bug3 full
```

Replace the case name with any row in the table. `prepare` verifies the exact
Hadoop revision, builds Hadoop/GraphChecker, verifies class-file major version
52, constructs the test classpath, and runs the concrete Java 8 workload.
`tasks` records and analyzes the workload and publishes the target-first
schedule. `candidates` replays the indexed tasks, closes selected paths,
composes `candidate.smt2`, and invokes Z3.

Artifacts are isolated under `experiments-output/<case>/`. A completed target
campaign must contain:

```text
candidates/<campaign>/candidate.smt2
candidates/<campaign>/composition.json
candidates/<campaign>/z3-result.json
candidates/<campaign>/result.json
```

Acceptance requires a closed composition with no missing confirmed edge, a Z3
verdict, the intended target occurrence, and a model/unsat audit that makes the
role of `rpcFails` explicit. A satisfiable formula is not by itself evidence
for the bug unless the satisfying assignment uses the fault relation and the
recorded stale-key producer lineage.

## Handoff status (2026-08-11)

The acceptance goal is deliberately narrower than “produce any SAT file”:

1. produce one gap-free, causally closed `candidate.smt2` for each of the four
   rows above;
2. run Z3 and verify that the intended target occurrence is reachable with
   the scheduled explicit fault input `rpcFails=true` and with the recorded
   producer/RPC/state lineage, not merely with the concrete seed value
   `rpcFails=false`.

No case is accepted yet.  Bug 3 is at the last producer-flip boundary; the
other three have workload/configuration scaffolding but have not yet produced
a fresh schedule or candidate.

| Case | Current state | Next blocking action |
| --- | --- | --- |
| `hdfs-17899-bug3` | Fresh trace, plan, 6-task schedule, all seed summaries, gap-free false-path SMT, and Z3 report exist.  The one exact `rpcFails` flip was solved but its replay ended before publishing a selected output. | Synchronize the test with completion of the asynchronous key-update command, rerun the fault producer, then require Z3 SAT at `rpcFails=true`. |
| `hdfs-17899-bug1` | `KeyManager` fault relation and Balancer workload configuration exist in the dirty Hadoop worktree. | Run `prepare`, `tasks`, and `candidates`; audit that the selected Dispatcher/SASL target is fed by the stale-key fault case. |
| `hdfs-17899-bug2` | A minimal same-DataNode DISK-to-SSD SPS workload and the `KeyManager` fault relation exist in the dirty Hadoop worktree. | Run the Java 8 baseline, then the full workflow; audit `BlockDispatcher.moveBlock` to the exact server key lookup. |
| `hdfs-17897` | A 3-DataNode XOR-2-1 striped checksum workload, one block-group-wide `rpcFails`, and the final `PathIOException` target exist in the dirty Hadoop worktree. | Run the Java 8 baseline and full workflow; verify the one fault Boolean governs every DN attempt in the group and reaches the final target. |

### Implemented GraphChecker design

The current GraphChecker changes are shared by all four cases:

- explicit fault-return events become ordinary symbolic input actions with
  authority `EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1`;
- explicit-fault producer seeds retain replayable branch witnesses instead of
  taking the relation-only fast path;
- the path worklist emits only branch flips whose predicate actually depends
  on the explicit fault symbol, so unrelated service/configuration branches
  are not explored as experiment dimensions;
- outputs selected from the same exact producer invocation and source path are
  scheduled as one atomic task, preserving the union of outputs, inputs,
  branches, exact edges, and occurrence catalog; different exact invocations
  are never merged;
- RPC scalar leaves, interface-to-translator calls, nested heap fields,
  container state, exact read-from edges, and `String.split`/`parseInt` aliases
  use their normal recorded lineage rather than HDFS method-name heuristics;
- the candidate runner has an opt-in gate
  `CAUSYNTH_REQUIRE_EXPLICIT_FAULT_TRUE=true`.  A false-only SAT probe no longer
  terminates a key-rotation experiment, and final publication fails unless one
  Z3 valuation sets every scheduled explicit fault input to true.

Do not remove that last gate to make a run green.  Its first use found the
current bug-3 replay problem instead of publishing the false seed as the
answer.

### Bug 3: exact current evidence

The current canonical schedule is under
`experiments-output/hdfs-17899-bug3/`:

```text
target occurrence: REGION.61e62f41-34c6-3a5d-b610-b639dc3f4838@TestCausynthDataTransferRpcFailure.testReplicationAfterModeledKeyRefreshRpcFailure#call479963
target task:       TASK.SEED.9d9f52b603ed1ac8ea709c2246c8deacf4a5950637070915424f2092fdf98fc4
fault occurrence:  REGION.17ced2f2-35e3-3044-bf92-041761c7230b@TestCausynthDataTransferRpcFailure.testReplicationAfterModeledKeyRefreshRpcFailure#call477286
fault task:        TASK.SEED.f828e3c1c1d6087a939c5511b463900b9183161dd5b9113c1443a9260f9aceb7
fault port:        REGION.17ced2f2-35e3-3044-bf92-041761c7230b.in.978ad820-9d80-3a32-ba29-27ddb0909eb1
```

The index contains one target plus five producer tasks.  All six fresh seed
summaries are present and reusable.  The target and 12 confirmed edges compose
without gaps.  The current (rejected) Z3 result is:

```text
rpcFails=false -> sat
rpcFails=true  -> unsat
reach formula  -> (= rpcFails false)
```

The runner correctly rejected it.  See:

```text
experiments-output/hdfs-17899-bug3/run-candidates-20260811-073606.log
experiments-output/hdfs-17899-bug3/candidates/REGION.61e62f41-34c6-3a5d-b610-b639dc3f4838-call479963-86edaeaa/
```

The fault worklist contains exactly one flip: branch `u12` in the experimental
`BlockTokenSecretManager.addKeys(ExportedBlockKeys,boolean,boolean)`, from
`rpcFails=false` to `true`.  Z3 produced `SAT_MODEL_READY` for that flip.  The
replay nevertheless recorded `REPLAY_PRODUCED_NO_RESULT`.

This is a workload synchronization bug, not a missing RPC or field edge.  The
test waits only 10 seconds for the source DataNode's key to equal the fresh
key.  That predicate can never become true on the intended failure path.  With
the concolic VM, the test began cluster shutdown at 12:41:10, while the command
processor reached the selected `addKeys` call only at 12:41:38.  Consequently
the semantic output hook did not publish a result before the workload exited.

The next change should be minimal and test-only: wait for completion of the
asynchronous key-update command independently of whether it installed the new
key.  Preferred options, in order:

1. add a test-visible completion counter/latch around
   `BPOfferService.applyKeyUpdateCommand`, incremented in `finally`, and wait
   for one increment after `triggerHeartbeat`;
2. as a quick diagnostic only, raise the wait to at least 120 seconds.  A
   fault replay should halt at the selected output boundary before the full
   timeout, but this is less deterministic than the completion signal.

After that change, rebuild the Hadoop Java-8 test classes and rerun bug 3.  A
quick continuation can reuse the trace/schedule if only the test wait changes,
but the canonical acceptance run should regenerate `tasks` because a workload
class changed:

```bash
experiments/hdfs/hdfs-key-rotation/run.sh hdfs-17899-bug3 prepare
experiments/hdfs/hdfs-key-rotation/run.sh hdfs-17899-bug3 tasks
CAUSYNTH_REGION_JOBS=4 CAUSYNTH_PATH_JOBS=2 \
  experiments/hdfs/hdfs-key-rotation/run.sh hdfs-17899-bug3 candidates
```

Acceptance must show both a successful `rpcFails=true` path replay and a final
Z3 valuation with that port true.  A `CANDIDATE_READY` manifest by itself is
not sufficient.

### Remaining case-specific work

#### HDFS-17899 bug 1: Balancer Dispatcher

- Baseline: Hadoop `734dd8a67cd6df56b59ff75aa43de57834a0d248`.
- Workload: `TestBalancerWithEncryptedTransfer.testEncryptedBalancer1`.
- Fault site: `KeyManager.BlockKeyUpdater.refreshBlockKeys()` chooses between
  the cached `lastBlockKeys` state and a fresh `namenode.getBlockKeys()` result.
- Target: the annotated server
  `BlockTokenSecretManager.retrieveDataEncryptionKey` missing-key throw reached
  from `Dispatcher.PendingMove.dispatch -> SaslDataTransferClient.socketSend`.
- Required audit: the selected target must be the Balancer transfer, not the
  earlier DFSClient/DataStreamer handshake; the fault=true case must retain
  the old KeyManager state and be load-bearing in the SASL key-id lineage.

#### HDFS-17899 bug 2: SPS BlockDispatcher

- Baseline: the same HDFS-17899 parent.
- Workload:
  `TestExternalStoragePolicySatisfier.testCausynthSpsKeyRefreshRpcFailure`.
- Current design uses one DataNode with DISK and SSD volumes, one block at
  replication 1, then policy `ONE_SSD`.  This still traverses the real
  `BlockDispatcher.moveBlock` TCP/SASL path while eliminating a second
  DataNode, target selection, and the target-to-source proxy SASL handshake.
- Sequence: capture connector state S0; rotate NameNode keys twice; install S2
  in the single DataNode; invoke one explicit KeyManager refresh; start
  external SPS; request the DISK-to-SSD move.
- Required audit: false refresh completes the move; true retains S0 and the
  first SPS-to-DataNode handshake reaches the annotated missing-key target.

#### HDFS-17899 bug 3: DataNode DataTransfer

- Workload:
  `TestCausynthDataTransferRpcFailure.testReplicationAfterModeledKeyRefreshRpcFailure`.
- Two DataNodes, replication 1.  The target is explicitly given S2.  A real
  NameNode `KeyUpdateCommand` is sent to the source; the fault decides whether
  the source installs S2 or retains S0; `DataNode.transferBlock` then opens the
  encrypted connection to the target.
- Complete the synchronization fix described above, then rerun and audit the
  exact `BPOfferService -> BlockTokenSecretManager.addKeys -> DataTransfer ->
  SASL -> retrieveDataEncryptionKey` chain.

#### HDFS-17897: striped checksum

- Baseline: Hadoop `156dd3b276457e49736638f1b57b05d78b558a7e`, the
  parent of the HDFS-17897 fix.
- Workload: `TestEncryptedTransfer.testCausynthStripedFileChecksumRpcFailure`;
  three DataNodes and the XOR-2-1 erasure-coding policy.
- Fault site: one `rpcFails` is created per block-group checksum attempt and is
  consulted before every `tryDatanode`, rather than creating a different
  Boolean for each DataNode.
- Target: the final annotated `PathIOException` in
  `FileChecksumHelper.checksumBlocks()` after the group cannot obtain a
  checksum.
- Required audit: the same fault root governs all attempts, `rpcFails=true`
  reaches the final exception, and no earlier ordinary checksum path is
  mistaken for the selected target.

### Repositories and uncommitted Hadoop patches

The GraphChecker commit does **not** contain the dirty Hadoop worktrees.  Do
not reset or clean them before exporting reproducible patches:

```text
/tmp/hdfs-17899-vulnerable  HEAD 734dd8a67cd6df56b59ff75aa43de57834a0d248
/tmp/hdfs-17897-vulnerable  HEAD 156dd3b276457e49736638f1b57b05d78b558a7e
```

Both contain the generic RPC/schema-4 tracing edits and case-specific
annotations/workloads.  The first new agent task should export those dirty
changes into versioned patch files under this experiment directory and make
`run.sh prepare` apply/verify them.  Until that is done, the current host
worktrees are the source of truth and must be preserved.

### Validation already run

The current Java changes passed:

```bash
mvn -q -Dtest=ConcolicRegionRuntimeTest,ConcolicSummaryImporterTest,RegionPathWorklistTest test
mvn -q -DskipTests package
```

The candidate-gating shell change passed `bash -n`, `git diff --check`, and a
negative fixture using the current false-only Z3 report.  Before final
publication, run the broader targeted suite (or full `mvn -q test`), package,
`bash -n` on both runners, and `git diff --check` again.

### Final per-case acceptance commands

For each case, after its candidate completes:

```bash
INDEX=experiments-output/<case>/schedule/runtime_workflow_schedule_index.json
CAMPAIGN=$(jq -er '.target.campaignId' "$INDEX")
OUT=experiments-output/<case>/candidates/$CAMPAIGN
test -s "$OUT/candidate.smt2"
jq -e '.state == "CANDIDATE_READY" and (.gaps | length) == 0' \
  "$OUT/composition.json"
jq -e '
  .state == "CANDIDATE_READY"
  and any(.roots.booleanInputs[]?; .portId | length > 0)
  and any(.valuations[]?; .status == "sat" and any(.values[]; . == true))
' "$OUT/z3-result.json"
```

Then join the true Boolean root back to the execution task input action and
require authority `EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1`; do not rely only on
the position of `true` in the valuation array.  Record the exact target
occurrence, fault port, task IDs, plan/index hashes, Z3 verdict, and canonical
artifact directory in this README only after that audit passes.
