# HDFS-17899 campaigns

The three cases share one target: a stale data-encryption key reaches
`BlockTokenSecretManager.retrieveDataEncryptionKey` after a modeled key-refresh
RPC failure.

For every case, the graph chooses the relevant region and communication
closure. The custom JDK carries the exact symbolic key expression through the
listed RPC chain and anchors it at each consumer. Each region records only its
local path condition. Closure-wide symbolic merging combines those cases, and
each selected shared read retains a complete bounded GuardedRead snapshot of
the writer expressions available to the SMT choice.

The manual symbolic roots are the NameNode's key id, time and expiry, and they
come from two authorities. Two are minted by configured-source hooks in
`BlockTokenSecretManager.updateKeys`:
`CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.SERIAL_NO", this, ...)` roots
`<org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: int
serialNo>`, the counter each new `BlockKey` takes its id from, and
`CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.EXPIRY_DATE", nextKey, ...)`
roots `<org.apache.hadoop.security.token.delegation.DelegationKey: long
expiryDate>` (the field `BlockKey` inherits). A hook site owns its field: every
competing field-read candidate for it is stamped
`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED` and left concrete, so each root is
minted once, at its hook -- which is why neither field is listed in
`symbolic-inputs.jsonl`. The third root, the clock
`<org.apache.hadoop.util.Timer: long now()>.return`, has no hook and is still
declared there for both regions; the same file is shared by all three cases.
The key ids observed on the wire are carriers, not roots of their own: they
carry the NameNode's minted `serialNo`.

| Case | Request flow | Hadoop worktree |
| --- | --- | --- |
| `bug1` | NameNode -> Balancer -> DataNode | `/opt/hadoop-hdfs-17899-bug1` |
| `bug2` | NameNode -> SPS -> DataNode | `/opt/hadoop-hdfs-17899-bug2` |
| `bug3` | NameNode -> source DataNode -> target DataNode | `/opt/hadoop-hdfs-17899-bug3` |

Build each Hadoop checkout with `./run.sh bug1 build`, replacing `bug1` as
needed, then run `./run.sh bug1 campaign`. The shared build script installs the
current GraphChecker API before compiling Hadoop. Each replay loads the
common, client and HDFS classes from that case's own checkout.

Set `CAUSYNTH_OUTPUT_DIR` to a fresh directory for each campaign. The result and
its SMT, path closures and provenance are written under `schedule/final` there.
The trace pass starts paused; each workload opens the recording boundary only
after its stable node/application sources and aliases have been registered.
A fresh run must close every selected consumer-anchor family and reproduce the
complete root-to-target causal chain before its SAT result is accepted.
