# HDFS-17967

## The bug

[HDFS-17967](https://issues.apache.org/jira/browse/HDFS-17967), upstream PR
[8698](https://github.com/apache/hadoop/pull/8698). Three data-transfer paths open their own
SASL-encrypted connection to a peer and present a data-encryption key derived from the
sender's current block key. When the peer can no longer resolve that key id it answers
`ERROR_UNKNOWN_KEY`; the sender rebuilds the exception and abandons the whole operation
instead of clearing its cached key and retrying once, which is what the PR adds.

| Case | Who opens the connection | Who rejects | In-frame end of the failure |
| --- | --- | --- | --- |
| `pathA` | the pipeline HEAD, on `DataXceiver.writeBlock` (`DataXceiver.java:811`) | the MIRROR | `DataXceiver.java:913 throw e` |
| `pathB` | the move TARGET, on `DataXceiver.replaceBlock` (`DataXceiver.java:1241`) | the PROXY | `DataXceiver.java:1285 throw ioe` |
| `pathC` | the RECONSTRUCTING node, on `StripedBlockWriter.init` | the reconstruction TARGET | `StripedWriter.java:122 throw new IOException("All targets are failed.")` |

All three run on the unified HDFS tree `/u/vnr3ne/hadoop-hdfs-unified`, branch `gc/hdfs-unified` (trunk 734dd8a67cd; inventory `/bigtemp/vnr3ne/analysis/unify/hdfs-inventory.md`). It has the bug: no HDFS-17967 fix is in trunk (its
`DataXceiver.java` handles no `InvalidEncryptionKeyException` in the relays). Do not base
this case on the upstream follow-up branch `HDFS-17899-followup-invalid-encryption-key`: it
has the fix, so there is no fatal arm to reach.

## The one target site, and why it is not any of the three throws

The target has to be a `throw new` **whose backward slice reaches the state the mechanism
turns on**. For all three paths that is the `allKeys` miss in
`BlockTokenSecretManager.retrieveDataEncryptionKey`, which is also the target of HDFS-11741,
HDFS-17897 and all three HDFS-17899 cases. It is not convenience.

The three in-frame ends above cannot be it. A and B are rethrows, and a target is a
constructed exception handed straight to `athrow` (`causynth/ExceptionTargetLineResolver`).
C is a real `throw new`, and it was the target first — but its only operand is a
`String`, so nothing classifies the key-management methods as writers of tracked state, they
lose `STATE_WRITER_ENTRY`, and `RuntimeRegionPlanner#validRootAuthority` refuses the whole
recording by name:

```
region skeleton has no authoritative execution context root:
  <org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: boolean updateKeys()>
```

The client-side reconstruction in `DataTransferSaslUtil` fails the same way, for the same
reason. So the three paths share one `exception_target` — `hdfs-17967` — and are told
apart by `declared_target_occurrence`, exactly as HDFS-17899's three bugs are.

## What these cases declare

`workflow.properties`, `root-domains.jsonl`,
`communication-mappings.jsonl` and `loop-bounds.jsonl` are shared by all three; `case.sh`
carries what is per case, including the per-case analysis scope.

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget` naming `hdfs-17967-pathA`, `-pathB` and `-pathC` on `BlockTokenSecretManager.retrieveDataEncryptionKey`'s missing-key `throw new` (line 582); `run.sh` derives each case's spec from it |
| the occurrence | `target_occurrence` in `case.sh` | `pathA` `hdfs-17967/mirror-dn#epoch0/region/REGION.7c569c3f…#1`; `pathB` `…/proxy-dn#…`; `pathC` `…/target-dn#…`. `REGION.7c569c3f` is the per-connection `SaslDataTransferServer` callback handler, the region every passing case in this family anchors on |
| clock roots | the program text (`causynth/RootCatalog`) | every read the slice reaches of a clock -- a JVM clock or a method returning one under constant arithmetic (`Timer.now()`, `Time.now()`, `Time.monotonicNow()`) -- is a root, and the occurrence that reads it is admitted as a root reader |
| root domains | `root-domains.jsonl`, one row | `HDFS.BLOCK_KEY.SERIAL_NO`, `+0` to `+3`: the recorded value and up to three rotations past it |
| analysis scope | `case.sh` (`scope`) | a shared narrow set (the SASL client/server, the key managers, `PBHelper`, `ipc/Client`), plus `DFSClient` for A and the erasure-coding reconstruction families for C |

**Fault points.** Every mapped transport door mints its fault point unconditionally:
`FAULT:HADOOP_IPC:REQUEST` in `Client$Connection.sendRpcRequest` and
`FAULT:HDFS_SASL:REQUEST` in `SaslDataTransferClient.doSaslHandshake`, the same code in every
tree. The recorded polarity is false; true throws the transport's failure before the request
leaves. `ipc/Client` stays in the analysis scope: the door and the IPC message-propagation
calls the causal context travels on live in the same file.

## The workloads

Every path is driven by a bespoke test, and every one of them drives the mechanism **two
links from the root**. An occurrence IS its causal address and an `ANCHOR` context digests
the producer endpoint, which digests an occurrence, so a long chain has to reproduce byte for
byte between the planning pass and the replay; a client-driven path A was refused on identity
(`OCCURRENCE_ANCHOR_UNMATCHED`) every time, never on the mechanism.

| Case | Test | Shape |
| --- | --- | --- |
| `pathA` | `TestCausynthWriteBlockMirrorStaleKey` | three DataNodes, no client in the window. `Sender.java:155` strips the sender from the target list, so `source.transferBlock(block, [head, mirror], …)` sends WRITE_BLOCK to the head with the mirror downstream and the head opens the mirror connection itself |
| `pathB` | `TestCausynthReplaceBlockProxyStaleKey` | three DataNodes; the mover is the test, reproducing `Dispatcher.PendingMove.dispatch` (`SaslDataTransferClient.socketSend` then `Sender.replaceBlock`). `DFSTestUtil.replaceBlock` cannot be used: raw socket, `DUMMY_TOKEN`, no SASL |
| `pathC` | `TestCausynthStripedReconstructTargetStaleKey` | four DataNodes and a user-defined XOR-2-1 policy at a **1 KiB** cell, so the window moves 2 KiB instead of 2 MiB on an interpreter-only replay VM. The reconstruction task is handed to the chosen node's `ErasureCodingWorker` directly, so the reconstructing node, the sources, the missing index and the target are all fixed by the test rather than by the NameNode's redundancy monitor |

Every one of them follows the block-key window rule (`../lib/README.md`: the key flows the
RPC's way). Inside the window the master rotates twice under `rotate-block-keys`; every
DataNode is marked for a key update and takes the new keys over exactly one heartbeat of its
own, whose answer carries the `KeyUpdateCommand`; the presenter (head, target, reconstruction
worker) then presents the master's current key to the verifier (mirror, proxy, target). The
recording succeeds, asserted by `recordingPrecondition`s. A world where the verifier's heartbeat
failed -- its request never reached the NameNode, or the NameNode's answer was lost -- leaves
the verifier without that key: the fatal, with every clock at the recording. Nothing is
decided by wall-clock timing: rotations and heartbeats are driven explicitly by the test.

## Build and run

From this directory, replacing `pathA` as needed:

```bash
../../lib/run.sh . pathA build      # installs the current GraphChecker API, builds that worktree,
                          # runs the concrete workload test, refuses unless it alone passes
../../lib/run.sh . pathA validate
../../lib/run.sh . pathA campaign
```

`lib/run.sh` sets a per-case `CAUSYNTH_OUTPUT_DIR` and `CAUSYNTH_CACHE_DIR`; override
`CAUSYNTH_OUTPUT_DIR` with a fresh directory per campaign. Or run the acceptance harness
(`experiments/accept/README.md`), which does campaign, z3 probe and report together:

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
CASES="hdfs-17967-pathA hdfs-17967-pathB hdfs-17967-pathC" bash experiments/accept/accept.sh
```

## What the harness expects

`report.py` passes each path on `claim` `SAT_CANDIDATE` confirmed, `finalStatus` `FINAL_READY`,
no BLOCKING gap at any stage, `polarityDecides` true, and `findingKind` `MARKER_FLIPPED` whose
`movedRoots` hold an IPC door fault flipped to true and no clock cell.
