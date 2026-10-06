# HDFS-17899

## The bug

[HDFS-17899](https://issues.apache.org/jira/browse/HDFS-17899). A stale data-encryption key
reaches `BlockTokenSecretManager.retrieveDataEncryptionKey` on a DataNode after a key-refresh
RPC has failed. The consumer of the key — Balancer, SPS or a source DataNode — keeps using
the key it holds; the DataNode that has to verify it has already rotated. The three cases
share that one target and differ only in which request flow carries the key to it. Every
tree carries 11741's expiry check, so a stale key reaches the check only through a failed
RPC: the witness is an IPC door fault flipped to true with every clock at the recording —
the request that never reached the NameNode (`FAULT:HADOOP_IPC:REQUEST`, minted in every
tree at `Client$Connection.sendRpcRequest`) or the NameNode's answer lost after it applied
the request (`FAULT:HADOOP_IPC:RESPONSE`, at `Client.getRpcResponse`), to a DataNode or to
the application.

| Case | Request flow |
| --- | --- |
| `bug1` | NameNode -> Balancer -> DataNode |
| `bug2` | NameNode -> SPS -> DataNode |
| `bug3` | NameNode -> source DataNode -> target DataNode |

All three run on the HDFS tree `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r6`, branch `gc/hdfs-study-r6` (on `system/hdfs`; it descends from `gc/hdfs-unified-dtx`, the unified tree `gc/hdfs-unified`, trunk 734dd8a67cd, inventory `/bigtemp/vnr3ne/analysis/unify/hdfs-inventory.md`, plus the DataTransfer op's envelope); HDFS-17899's fix (62729b06d70) landed after that base.

## The workloads

All three are bespoke tests, and each drives the mechanism **two links from the root**. An
occurrence IS its causal address and an `ANCHOR` context digests the producer endpoint, which
digests an occurrence, so a long chain has to reproduce byte for byte between the planning
pass and the replay.

| Case | Test | Shape |
| --- | --- | --- |
| `bug1` | `TestCausynthBalancerCachedKey` (`…server.balancer`) | the master rotates twice in-window, each DataNode takes the keys over one heartbeat, the Balancer's KeyManager fetches them (`fetch-block-keys`) and presents the current key in one REPLACE_BLOCK (`balance-block`) |
| `bug2` | `TestExternalStoragePolicySatisfier#testCausynthSpsKeyRefreshRpcFailure` | the same order with the SPS: rotate twice, one heartbeat of the target DataNode, the SPS `updateBlockKeys` (`refresh-block-keys`), the move presents the current key |
| `bug3` | `TestCausynthDataTransferRpcFailure` | rotate twice, one heartbeat each of target and source, the source replicates to the target presenting the current key (`replicate-block`) |

The mover of `bug1` is the test itself, holding a real `KeyManager`: its cached
`DataEncryptionKey` IS the defect, and `Balancer` and `Dispatcher`, which no part of the
mechanism touches, are out of the analysis scope.

Every workload has to leave a **rotation gap running the right way**: the key the failing
party puts on the wire is serials BEHIND the master's current one, while the consumer still
RETAINS it, so the recording stays healthy and a witness has to make one party present a key
the verifying DataNode does not hold — which in these trees only a failed RPC does. Each
workload asserts the gap itself.

## What these cases declare

`workflow.properties` and `root-domains.jsonl` are shared by all three (the wire flows are every
HDFS case's `../communication-mappings.jsonl`); `case.sh` carries what is per case.

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget` naming `hdfs-17899-bug1`, `-bug2` and `-bug3` on `BlockTokenSecretManager.retrieveDataEncryptionKey`'s missing-key `throw new` (line 582); `run.sh` derives each case's spec from it |
| the occurrence | `target_occurrence` in `case.sh`, exported as `CAUSYNTH_TARGET_OCCURRENCE` | `bug1` `hdfs-17899/target-dn#epoch0/…@hdfs-17899/balancer#epoch0/balance-block#1`; `bug2` `…/target-dn#epoch0/…@hdfs-17899/sps#epoch0/satisfy-storage-policy#1`; `bug3` `…/target-dn#epoch0/…@hdfs-17899/source-dn#epoch0/replicate-block#1`. Left empty, the run keeps every observed occurrence |
| clock roots | the program text (`causynth/RootCatalog`) | every read the slice reaches of a clock -- a JVM clock or a method returning one under constant arithmetic (`Timer.now()`, `Time.now()`, `Time.monotonicNow()`) -- is a root, and the occurrence that reads it is admitted as a root reader |
| fault points | the engine's library catalog (`docs/design/SYMBOL-SCOPE.md` §4.2), not this directory | every catalog door of a class the system calls is woven with its Boolean fault points: `FAULT:HADOOP_IPC:REQUEST` in `Client$Connection.sendRpcRequest` (the key-refresh RPC failure), `FAULT:HADOOP_IPC:RESPONSE`, `FAULT:HDFS_SASL:REQUEST` in `SaslDataTransferClient.doSaslHandshake`, `FAULT:HDFS_DATA_TRANSFER:REQUEST` in `datatransfer.Sender.send` and `FAULT:HDFS_DATA_TRANSFER:RESPONSE` after each response or ack parse of a class in scope (`DataNode$DataTransfer`'s close ack, `BlockDispatcher`'s response). The recorded polarity is false; true throws the transport's failure before the request leaves (after the response arrives) |
| hook-minted roots | the Hadoop checkouts | `CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.SERIAL_NO", …)` roots the counter each new `BlockKey` takes its id from; `…("HDFS.BLOCK_KEY.EXPIRY_DATE", …)` roots the inherited `DelegationKey#expiryDate`. A hook site owns its field (`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED`), so neither is listed in `symbolic-inputs.jsonl` |
| root domains | `root-domains.jsonl`, one row | `HDFS.BLOCK_KEY.SERIAL_NO`, `declaredDomainMin "+0"`, `declaredDomainMax "+3"`: the recorded value and up to three rotations past it, relative because the serial starts at a `SecureRandom` int and increments once per roll. A root with no row is pinned to its recording; a clock has a floor of zero and no window |
| wire mappings | `../communication-mappings.jsonl` (every HDFS case's one declaration), one `WIRE_FLOW` row | `data-encryption-key-id` (`CALL_ARGUMENT` at the SASL client, `METHOD_PARAMETER` 0 of `retrieveDataEncryptionKey`: the key id travels inside the SASL user name, where no automatic port sees it). The block keys' ids and expiry dates and the NameNode's data-encryption key id are protobuf message fields: derived ports, which the IPC door walks (SYMBOL-SCOPE §6.2-6.3). Declared ports are tracked and mint nothing: the consumer gets the producer's own propagated expression |
| loop bounds | `loop-bounds.jsonl` (five rows) for `bug1`/`bug2`, `loop-bounds-datanode.jsonl` (four rows) for `bug3`, every row at `loopBodyBound: 8`; `causynth_loop_default_bound=8` | `case.sh` selects the file and `run.sh` exports it as `CAUSYNTH_LOOP_BOUNDS` |

## Build and run

Each case has its own Hadoop worktree, so its source changes and compiled classes stay
independent, and each replay loads that checkout's common, client and HDFS classes. From
this directory, replacing `bug1` as needed:

```bash
../../lib/run.sh . bug1 build      # installs the current GraphChecker API, builds that checkout,
                         # runs the concrete workload test, refuses unless it alone passes
../../lib/run.sh . bug1 validate
../../lib/run.sh . bug1 campaign
```

`lib/run.sh` sets a per-case `CAUSYNTH_OUTPUT_DIR` and `CAUSYNTH_CACHE_DIR`; override
`CAUSYNTH_OUTPUT_DIR` with a fresh directory per campaign. Each workload opens its recording
boundary only after its stable node and application sources and aliases are registered. The
in-tree acceptance harness (`experiments/accept/README.md`) runs campaign, z3 probe
and report together, one case at a time:

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
CASES="hdfs-17899-bug1 hdfs-17899-bug2 hdfs-17899-bug3" bash experiments/accept/accept.sh
```

## What the harness expects

`report.py` passes each of the three on `claim` `SAT_CANDIDATE` confirmed, `finalStatus`
`FINAL_READY`, no BLOCKING gap at any stage, `polarityDecides` true, `valuationOrdinal` >= 1,
and `findingKind` `MARKER_FLIPPED` whose `movedRoots` hold an IPC door fault flipped to true
and no clock cell.
