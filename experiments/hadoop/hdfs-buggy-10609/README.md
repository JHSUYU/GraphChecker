# HDFS-10609 put back (hdfs-buggy-10609, point hdfs-adhoc-11)

## The bug

[HDFS-10609](https://issues.apache.org/jira/browse/HDFS-10609) (fix 3ae652f8211, 2016): when a
writer adds a DataNode to its pipeline (`DataStreamer.addDatanode2ExistingPipeline`), it asks a
DataNode already holding the replica to copy it to the new one (`DataStreamer.transfer`, a
TRANSFER_BLOCK over a SASL connection to the source). If the source cannot re-compute the client's
data-encryption key, its SASL handshake throws `InvalidEncryptionKeyException`; `transfer` did not
catch it (unlike `createBlockOutputStream`, which clears the key and retries), so
`addDatanode2ExistingPipeline`'s retries ask again with the same cached key and the writer aborts
("Uncaught InvalidEncryptionKeyException during pipeline recovery may abort downstream
applications"). The fix wraps the transfer in a `RefetchEncryptionKeyPolicy`: on the exception, clear
the key and try again, twice, then throw.

Point hdfs-adhoc-11 (`docs/checks/HDFS.md`, `checks.tsv`) is the exception's origin on the
DataNode: `BlockTokenSecretManager.retrieveDataEncryptionKey`'s missing-key throw, a key-id lookup
that misses when the NameNode's rotation and the DataNode's key set disagree.

## What was put back, on graphchecker/hdfs-bug-10609

The fork's branch is `graphchecker/hdfs-checks` (899c200cc8e) plus two commits:

- **The bug, by hand** (633feb60e1f, `HDFS-10609 put back: ...`): `transfer` makes one attempt (the
  `StreamerStreams` it builds, the TRANSFER_BLOCK it sends, the streams closed) with no catch, as
  before the fix, instead of the `do { ... } while (policy.continueRetryingOrThrow())` loop
  (DataStreamer :1591-1608 on 899c200cc8e); the `RefetchEncryptionKeyPolicy` class (:123-155), which
  only `transfer` used, is removed. The fix's restructuring (`StreamerStreams`,
  `computeTransferWriteTimeout`/`ReadTimeout`) and its test accessors change no behaviour and stay.
  The fix's test `TestEncryptedTransfer#testLongLivedClientPipelineRecovery` is removed (it asserts
  the policy: the key cleared once), with the three imports only it used.
- **The workload and the target** (bec4a7e0e52): `TestCausynthEncryptedAppendTransfer`, and `hdfs-buggy-10609`
  added to the marker on `retrieveDataEncryptionKey`'s throw (line 584).

## The workload

`org.apache.hadoop.hdfs.TestCausynthEncryptedAppendTransfer#testStaleEncryptionKeyFailsAppendTransfer`:
TestEncryptedTransfer#testEncryptedAppendRequiringBlockTransfer's shape (an append whose block has
fewer replicas than the file wants, so the writer adds a DataNode and has the replica transferred to
it) with hdfs-17897's key window. Two DataNodes; before the window a file of one replica is written to
`dn0` (`CausynthCluster.createOnNode`) and its replication raised to 3, and the block keys are pinned
(S+1 current, S+2 next everywhere; S = `Integer.MAX_VALUE / 10609`). Inside the window:

1. nn0 rotates twice (`KEY_MANAGER_TICK`; S+3 current).
2. Every DataNode is marked for a key update and takes the keys over one heartbeat of its own, in
   name order (`CausynthCluster.refreshKeysFromNameNode`, `DNA_ACCESSKEYUPDATE`).
3. The client fetches nn0's current encryption key over its own RPC (`cache-encryption-key`): S+3.
4. `append-block`: `append`, a write and an `hflush`. The append's pipeline set-up
   (`setupPipelineForAppendOrRecovery`) finds one DataNode where the file wants three
   (`ReplaceDatanodeOnFailure` DEFAULT: replication 3, an append), asks nn0 for another DataNode
   (`getAdditionalDatanode`: dn1) and has dn0 transfer the replica to it -- the client's first
   connection to dn0 in the request -- before it connects the pipeline.

The recording succeeds (dn0 holds S+3; the pipeline ends with dn0 and dn1). A world in which dn0's
key-update heartbeat fails leaves dn0 without S+3, and its SASL handler's `retrieveDataEncryptionKey`
throws on the transfer's connection.

Two settings in the workload's own configuration, each named here:
- `dfs.heartbeat.interval` 6 h: a DataNode's daemon heartbeat runs at its registration only and the
  key updates are delivered by the workload's heartbeats alone (hdfs-buggy-11741's lesson).
- `dfs.namenode.redundancy.interval.seconds` 6 h: nn0's redundancy monitor computes its work at
  start-up and not again, so the under-replicated block keeps its one replica until the append and no
  heartbeat answer of the window carries a replication command.

What the put-back changes in the witness world: the throw is dn0's and happens with or without the
fix; the bug is what the writer does after it (the transfer's exception escapes, the append aborts).
In this world the fixed writer would fail too: its retry presents a refetched key, nn0's current one,
which dn0 lacks; the fix rescues a key that expired on the DataNode. The study's mechanism for this
bug (a lost `KeyUpdateCommand` reply, as hdfs-17897) is what the case asks for.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget` naming `hdfs-buggy-10609` (beside hdfs-adhoc-11 and the named block-key cases) on `retrieveDataEncryptionKey`'s missing-key `throw new` (line 584) |
| the occurrence | `target_occurrence` in `case.sh` | `hdfs-10609/dn0#epoch0/region/REGION.7c569c3f-...@hdfs-10609/client#epoch0/append-block#1`: dn0's SASL handler occurrence under the client's append request |
| fault doors | the library catalog | the transport doors (`FAULT:HADOOP_IPC:REQUEST`, ...), as every HDFS case; none of its own |
| hook-minted roots | the tree | `HDFS.BLOCK_KEY.SERIAL_NO`, `HDFS.BLOCK_KEY.EXPIRY_DATE*` (`CausynthSymbolicSource.symbolize` in `BlockTokenSecretManager`) |
| root domains | `root-domains.jsonl` | hdfs-17897's row: `HDFS.BLOCK_KEY.SERIAL_NO` from +0 to +3 |
| wire mappings | `../communication-mappings.jsonl` | the SASL key id (`data-encryption-key-id`); block keys over the IPC door |
| scope | `case.sh` | the block-key family (`blockkey_scope`) plus `DFSClient` and `DataStreamer` (hdfs-17897's pattern: the client class that caches the key and the class of the operation) |
| world depth | `case.sh` | 0 (RULES) |
| loop bounds | `loop-bounds.jsonl` | hdfs-17897's two rows at 8 |
| mechanism | `experiments/accept/report.py` | `hdfs-buggy-10609`: RPC_FAILURE (`MARKER_FLIPPED` by an `ipc.Client` fault, no clock) |

The run's budget is `hdfs-buggy-cases.tsv`'s 21600 s.

## Result: SAT, MARKER_FLIPPED by a lost key-update heartbeat request, confirmed and reproduced 10/10 (B10609a, PASS)

Round B10609a (2026-10-26, snapshot `/bulk/gc-run/hb10609-1` = GraphChecker 1355227ba, tree set
`/bulk/trees/b10609` = bec4a7e0e52, `/bulk/gc-out/hdfs-buggy/10609`): 768 s, `SAT_CANDIDATE`
`FINAL_READY`, `report.py` **PASS**: `MARKER_FLIPPED` at valuation 1, `polarityDecides` true (the
recorded valuation, ordinal 0, is unsat), no gap, no defect, nothing bounded, `cone.json` unbound
empty; EXPLORE ended `WITNESSED` after 3 rounds (72 obligation verdicts, 30 planned tasks: the
DataStreamer and the second DataNode make the closure about twice hdfs-buggy-12931's).
`round-verify.sh`: `end=(WITNESSED) z3=timeout moved=1 polarityDecides=True leaves=203 confirmed`.

- **The moved root** is `REGION.763d087e-....in.48ceee4c-...` = true: the `FAULT:HADOOP_IPC:REQUEST`
  door (`ipc.Client$Connection.sendRpcRequest`) of dn0's key-update heartbeat
  (`DatanodeProtocol.sendHeartbeat` under the workload's `heartbeat#1` on dn0): the request never
  reaches nn0; dn1's heartbeat runs as recorded.
- **The chain in the formula** (`final/candidate.smt2`, read by hand): `path_fatal__0` (the selected
  path, its own run's session 05117422, every arm attested there) is `allKeys.get(keyId) == null` on
  dn0's map (BlockTokenSecretManager :582-584), the map built by `container_dag` puts of the two pinned
  keys only (202421 = S+1, 202422 = S+2): with the marker true no heartbeat answer's keys are put;
  `keyId` is the SASL handoff of the client's key id (`data-encryption-key-id`,
  `message_family__0__919c5dedca8c`), bound by `message_family__0__cf882a483546` to the client's
  received key 202423 (S+3: nn0's `generateDataEncryptionKey` from its current key, over
  `cache-encryption-key`).
- **CONFIRM**: "the selected session 0511742251622289-4c08054a is itself the run: it took every edge the
  model chose (2 arm(s), all its own deliveries), ran every moved root at the model's value, and
  observed the fatal at the anchor".
- **REPRODUCE**: 10/10 natively (the plant: the REQUEST fault on dn0's heartbeat; the fatal at the
  anchor in every run), control 0/10. In the native runs the throw is met on the transfer's connection
  (the client logs "Error transferring data from" dn0 to dn1): HDFS-10609's path, the client's first
  connection to dn0 in the request.
- **The moved root is necessary**: z3 on the exported file with the selected path asserted: sat; with
  the marker pinned to its recorded false as well: unsat. z3 alone on the whole exported file (9
  paths, 575 KB) does not decide within `round-verify.sh`'s 300 s; COMPOSE's path-scoped asks decided
  it, as for hdfs-buggy-11741.

**What the check detects here, and what it does not.** As for hdfs-buggy-12931: the point's throw is
on dn0, upstream of the client code the bug lives in, so the same world fires it with or without the
fix. Natively, with a scratch program (not committed) that drops dn0's key-update answer, refreshes
dn1 and then appends: on this tree, one throw on dn0, "Error transferring data from" dn0 to dn1, then
"Failed to replace a bad datanode on the existing pipeline due to no more good datanodes being
available to try" (the second try excludes dn1) and the append fails; with the fixed client
(graphchecker/hdfs-checks' `hadoop-hdfs-client` classes first on the class path), two throws on dn0
(the policy's retry presents a refetched key, nn0's current one, which dn0 still lacks), then the same
failure. The witness shows the bug's trigger reaching the point's own throw on the bug's own path (the
transfer); it does not separate the put-back writer from the fixed one, which differs only after the
throw.
