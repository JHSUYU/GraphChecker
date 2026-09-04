# HDFS-17897 campaign

This experiment detects the striped-file checksum failure fixed by Hadoop
PR #8364. The normal seed caches data-encryption key `G` in the DFS client and
performs two production key rotations, then uses the block-key RPC to update
each DataNode. GraphChecker
symbolically propagates the wire key IDs and the DataNode's bounded `allKeys`
state; the failure model derives that `G` is absent without a test hook that
replaces the map. The buggy checksum loop treats the returned
`InvalidEncryptionKeyException` as an ordinary per-DataNode I/O failure and
ultimately throws `PathIOException` instead of clearing the cache and retrying.

The causal graph joins two flows at the DataNode and carries the result back:

```text
client -> NameNode (cached key G) -> DataNode request --+
                                                     +-> SASL rejection -> client checksum failure
DataNode -> NameNode (current key G+1) -> DN state ----+
```

Run `./run.sh campaign`.  Replay concurrency is fixed at 8 in
`workflow.properties`.
