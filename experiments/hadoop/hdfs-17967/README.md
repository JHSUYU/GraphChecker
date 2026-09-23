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

Each case has its own Hadoop worktree, so its source changes and compiled classes stay
independent:

| Case | Worktree | Branch |
| --- | --- | --- |
| `pathA` | `/u/vnr3ne/hadoop-hdfs-17967` | `gc/hdfs-17967` |
| `pathB` | `/u/vnr3ne/hadoop-hdfs-17967-b` | `gc/hdfs-17967-pathB` |
| `pathC` | `/u/vnr3ne/hadoop-hdfs-17967-c` | `gc/hdfs-17967-pathC` |

All three are cut from `gc/hdfs-17899-bug3-current`, which still has the bug (its
`DataXceiver.java` holds **0** occurrences of `InvalidEncryptionKeyException` against **5**
on the upstream fix branch `HDFS-17899-followup-invalid-encryption-key`) and already carries
the instrumentation stack. Do not base this case on the upstream follow-up branch: it has
the fix, so there is no fatal arm to reach.

## The one annotated site, and why it is not any of the three throws

`@CausynthExceptionTarget` has to sit on a `throw new` **whose backward slice reaches the
state the mechanism turns on**. For all three paths that is the `allKeys` miss in
`BlockTokenSecretManager.retrieveDataEncryptionKey`, which is also where HDFS-11741,
HDFS-17897 and all three HDFS-17899 cases are annotated. It is not convenience.

The three in-frame ends above cannot carry it. A and B are rethrows, and
`@CausynthExceptionTarget` is `@Target(TYPE_USE)`, so it can only sit on a constructed type.
C is a real `throw new`, and it was annotated there first — but its only operand is a
`String`, so nothing classifies the key-management methods as writers of tracked state, they
lose `STATE_WRITER_ENTRY`, and `RuntimeRegionPlanner#validRootAuthority` refuses the whole
recording by name:

```
region skeleton has no authoritative execution context root:
  <org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: boolean updateKeys()>
```

The client-side reconstruction in `DataTransferSaslUtil` fails the same way, for the same
reason. So the three paths share one `exception_target_id` — `hdfs-17967` — and are told
apart by `declared_target_occurrence`, exactly as HDFS-17899's three bugs are.

## What these cases declare

`workflow.properties`, `target.yaml`, `symbolic-inputs.jsonl`, `root-domains.jsonl`,
`communication-mappings.jsonl` and `loop-bounds.jsonl` are shared by all three; `case.sh`
carries what is per case, including the per-case analysis scope.

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | `@CausynthExceptionTarget("hdfs-17967")` in each worktree's `BlockTokenSecretManager`; `target.yaml` | `exception_target_id: hdfs-17967` |
| the occurrence | `target_occurrence` in `case.sh` | `pathA` `hdfs-17967/mirror-dn#epoch0/region/REGION.7c569c3f…#1`; `pathB` `…/proxy-dn#…`; `pathC` `…/target-dn#…`. `REGION.7c569c3f` is the per-connection `SaslDataTransferServer` callback handler, the region every passing case in this family anchors on |
| clock roots | `symbolic-inputs.jsonl` | three callee rows (`Timer.now`, `Time.now`, `Time.monotonicNow`) plus per-method clock cells on `BlockTokenSecretManager.updateKeys()` and `.addKeys(ExportedBlockKeys,boolean)`. Without them `CLOCK_SKEW` is unreachable by construction and key EXPIRY cannot be expressed at all |
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

Three properties every one of them has to keep:

* **A rotation gap, running the right way.** The key the failing party puts on the wire is
  serials BEHIND the master's current one. With a zero gap nothing can expire, so every
  composed path is either self-contradictory or satisfied at the recorded valuation. Each
  workload pins the block keys, rotates the master twice inside the window, refreshes every
  DataNode so all of them can still verify block tokens, and then rolls back **only** the
  failing party's `currentKey`.
* **Asymmetry.** Two participants skewed identically share one address
  (`OCCURRENCE_ADDRESS_SHARED`) and one consumer gets paired with two producers
  (`TOPOLOGY_DIVERGENCE`).
* **Nothing decided by wall-clock timing.** Rotations are driven explicitly inside a request
  scope on a registered source, never by the key-updater daemon; heartbeats are sent
  synchronously by the test; `dfs.namenode.stale.datanode.interval` is pushed past any
  replay, because suppressed heartbeats plus a slow VM otherwise make every DataNode look
  stale and block placement silently gives a one-node pipeline.

The recording stays HEALTHY in all three: a DataNode RETAINS its older keys until they
expire, and that expiry is exactly what a witness has to buy with a clock move. Each workload
asserts the gap itself, so a mistake surfaces as a one-line assertion failure instead of a
campaign refusal three stages later.

## Build and run

From this directory, replacing `pathA` as needed:

```bash
../lib/run.sh . pathA build      # installs the current GraphChecker API, builds that worktree,
                          # runs the concrete workload test, refuses unless it alone passes
../lib/run.sh . pathA validate
../lib/run.sh . pathA campaign
```

`lib/run.sh` sets a per-case `CAUSYNTH_OUTPUT_DIR` and `CAUSYNTH_CACHE_DIR`; override
`CAUSYNTH_OUTPUT_DIR` with a fresh directory per campaign. Or run the acceptance harness
(`experiments/hadoop/accept/README.md`), which does campaign, z3 probe and report together:

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
CASES="hdfs-17967-pathA hdfs-17967-pathB hdfs-17967-pathC" bash experiments/hadoop/accept/accept.sh
```

## What the harness expects

`report.py` passes each path on `claim` `SAT_CANDIDATE`, `finalStatus` `FINAL_READY`, empty
`blockers` and no open BLOCKING gap, `polarityDecides` true, non-empty `movedRoots`, and a
`findingKind` of `CLOCK_SKEW` or `MARKER_FLIPPED`. `CLOCK_SKEW` is the mechanism the
workloads are written for.
