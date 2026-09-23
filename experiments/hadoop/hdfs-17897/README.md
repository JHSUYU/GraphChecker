# HDFS-17897

## The bug

[Hadoop PR #8364](https://github.com/apache/hadoop/pull/8364). The striped-file checksum
loop treats an `InvalidEncryptionKeyException` from a DataNode as an ordinary per-DataNode
I/O failure and ultimately throws `PathIOException`, instead of clearing the cached
data-encryption key and retrying. The workload caches a key in the DFS client, performs two
production key rotations and updates each DataNode through the block-key RPC. The client
then presents the stale key, the DataNode rejects the SASL handshake, and the checksum loop
turns that into the wrong failure. Whether the DataNode rejects the key is again a
disagreement between two nodes about which key set is current, so the two flows meet at the
DataNode: the client's cached key on one side, the DataNode's own refreshed `allKeys` on the
other. The fault points are the transport doors' (`FAULT:HADOOP_IPC:REQUEST`,
`FAULT:HDFS_SASL:REQUEST`), the same in every tree; the workload declares none of its own.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | `@CausynthExceptionTarget` in the Hadoop checkout; `target.yaml` | `exception_target_id: hdfs-17897` |
| the occurrence | `declared_target_occurrence` in `workflow.properties` | `hdfs-17897/dn0#epoch0/region/REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de@hdfs-17897/client#epoch0/striped-file-checksum#1` — the campaign composes and judges that one and reports the others |
| clock roots | `symbolic-inputs.jsonl`, three callee-level rows | `<org.apache.hadoop.util.Timer: long now()>`, `<org.apache.hadoop.util.Time: long now()>` and `<org.apache.hadoop.util.Time: long monotonicNow()>`, each `"kind": "CLOCK"`, so every call site of those clocks in the application scope is a root |
| declared region roots | `symbolic-inputs.jsonl`, two method rows | `BlockTokenSecretManager.updateKeys()` and `.addKeys(ExportedBlockKeys,boolean)`: declared methods are region roots by declaration, independent of the backward slice |
| hook-minted roots | the Hadoop checkout, not this directory | `CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.SERIAL_NO", …)` roots the counter each new `BlockKey` takes its id from; `…("HDFS.BLOCK_KEY.EXPIRY_DATE", …)` roots the inherited `DelegationKey#expiryDate`. A hook site owns its field (`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED`), so neither field appears in `symbolic-inputs.jsonl` |
| root domains | `root-domains.jsonl`, one row | `HDFS.BLOCK_KEY.SERIAL_NO`, `declaredDomainMin "+0"`, `declaredDomainMax "+3"`: the recorded value and up to three rotations past it, relative because the serial starts at a `SecureRandom` int and increments once per roll. A root with no row is pinned to its recording |
| wire mappings | `communication-mappings.jsonl`, four `WIRE_FLOW` rows | `namenode-data-encryption-key-id`, `block-key-id`, `block-key-expiry-date` (`CALL_ARGUMENT` into the proto builder, `CALL_RETURN` out of the proto getter) and `data-encryption-key-id` (`CALL_ARGUMENT` at the SASL client, `METHOD_PARAMETER` 0 of `retrieveDataEncryptionKey`). The key ids on the wire are declared cut ports, not roots: they are tracked and mint nothing, because `attachCommunicationLeaf` installs the producer's own propagated expression at the consumer |
| loop bounds | `loop-bounds.jsonl`: two rows at `loopBodyBound: 8`; `causynth_loop_default_bound=8` | the retained expiry scan and the bounded block-key reply conversion. The file's header says which key-plumbing loops stay undeclared because their trip count is an exact array length |

**No clock window is declared, and none exists to declare.** A clock root is free above zero
and nothing else: the composer asserts one `clock_floor__…` per declared clock symbol
(`compose/Composer.java`) and the flip query states the same rule (`explore/FlipQuery.java`
— "a CLOCK is per path, unbounded, with a `>= 0` floor only"). `workflow.properties` records
why: a bound on two nodes' difference is a number somebody picked, and the checker has no
physics to appeal to. What the execution fixes is stated where it belongs — the order a
node's own readings came in, and the value each path read.

## Build and run

Hadoop checkout `/u/vnr3ne/hadoop-hdfs-17897`, branch `gc/hdfs-17897-striped-checksum`. Replay
concurrency is fixed at `concolic_worker_count=8` in `workflow.properties`. From this
directory:

```bash
../lib/run.sh . "" build        # installs the current GraphChecker API, builds the tree,
                      # runs the concrete workload test, refuses unless it alone passes
../lib/run.sh . "" validate
../lib/run.sh . "" campaign
```

Use a fresh `CAUSYNTH_OUTPUT_DIR` per campaign. The in-tree acceptance harness
(`experiments/hadoop/accept/README.md`) runs campaign, z3 probe and report together:

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
CASES=hdfs-17897 bash experiments/hadoop/accept/accept.sh
```

## What the harness expects

`report.py` passes this case on `claim` `SAT_CANDIDATE`, `finalStatus` `FINAL_READY`, empty
`blockers` and no open BLOCKING gap, `polarityDecides` true, `valuationOrdinal` >= 1,
non-empty `movedRoots`, and `findingKind` `CLOCK_SKEW`. This is the one case whose expected
set has a single entry: `EXPECTED_MECHANISM` in `report.py` names no other mechanism for it,
so a witness of any other kind fails the case rather than passing it.

## Status

Prepared, not run under the current design. No claim, and no artifacts are committed for
this case.
