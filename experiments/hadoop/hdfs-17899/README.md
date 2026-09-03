# HDFS-17899 campaigns

The three cases share one target: a stale data-encryption key reaches
`BlockTokenSecretManager.retrieveDataEncryptionKey` after a modeled key-refresh
RPC failure.

| Case | Request flow | Hadoop worktree |
| --- | --- | --- |
| `bug1` | NameNode -> Balancer -> DataNode | `/opt/hadoop-hdfs-17899-bug1` |
| `bug2` | NameNode -> SPS -> DataNode | `/opt/hadoop-hdfs-17899-bug2` |
| `bug3` | NameNode -> source DataNode -> target DataNode | `/opt/hadoop-hdfs-17899-bug3` |

Run a campaign with `./run.sh bug1 campaign`, replacing `bug1` as needed.
Each artifact directory contains the composed `candidate.smt2`, final result,
path-closure evidence, the direct Z3 output, and a gzip-compressed composition
manifest. All three checked-in candidates are `FINAL_READY`, `REACHABLE`, have
zero gaps, and return `sat` from `/usr/local/bin/z3 candidate.smt2`.
