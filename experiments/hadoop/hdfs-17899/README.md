# HDFS-17899 campaigns

The three cases share one target: a stale data-encryption key reaches
`BlockTokenSecretManager.retrieveDataEncryptionKey` after a modeled key-refresh
RPC failure.

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
The checked-in artifacts preserve the previously successful campaign baseline.
They are compared with fresh runs when the Hadoop bytecode or mappings change;
a previous SAT result alone does not validate a changed run.
