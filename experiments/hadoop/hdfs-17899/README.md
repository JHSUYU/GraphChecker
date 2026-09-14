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
declared there -- by the two static sites it is read at,
`BlockTokenSecretManager.updateKeys()` and `.addKeys(...)`, which PLAN resolves
to whichever regions cover them; the same file is shared by all three cases.
The key ids observed on the wire are carriers, not roots of their own: they
carry the NameNode's minted `serialNo`.

One more declaration is per case rather than shared: `target_occurrence` in
`case.sh` names the occurrence of the annotated site the campaign is about --
an occurrence address, or the request family and k, as
`hdfs-17899/sps#epoch0/satisfy-storage-policy#1` does for `bug2`. The campaign
composes and judges that occurrence and reports the others; left empty it
keeps every observed one, which is what a recording that never took the fatal
arm needs. `bug1` leaves it empty: laneB1c observed four occurrences of the
site and its recording took the healthy arm at all four, so which one can fail
is not something that corpus states.

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
