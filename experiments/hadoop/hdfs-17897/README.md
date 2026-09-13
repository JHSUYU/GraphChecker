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

The causal graph selects the two flows that meet at the DataNode:

```text
client -> NameNode (cached key G) -> DataNode request --+
                                                     +-> SASL rejection -> client checksum failure
DataNode -> NameNode (current key G+1) -> DN state ----+
```

Values follow the live execution rather than graph edges. The custom JDK
propagates the key expressions across each RPC and shared-state read, leaving a
consumer anchor at every boundary. Region-local path conditions are merged in
closure-wide waves. Each selected shared read carries a bounded GuardedRead
snapshot of every retained writer expression; its exactly-one selector is
coupled to the corresponding writer case and local path condition.

The symbolic roots come from two authorities. The block key's expiry,
`<org.apache.hadoop.security.token.delegation.DelegationKey: long expiryDate>`
(the field `BlockKey` inherits), is minted by the configured-source hook
`CausynthSymbolicSource.symbolize("HDFS.BLOCK_KEY.EXPIRY_DATE", nextKey, ...)`
in `BlockTokenSecretManager.updateKeys`, not by `symbolic-inputs.jsonl`. The
hook site owns that field: every competing field-read candidate for it is
stamped `CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED` and left concrete, so the root
is minted once, at the hook. `symbolic-inputs.jsonl` still declares the clock,
`<org.apache.hadoop.util.Timer: long now()>.return`, for both regions. The wire
key IDs and `allKeys` are carriers, not roots: the file narrows which inputs may
*mint*, never which are symbolized.

Run `./run.sh campaign`.  Replay concurrency is fixed at 8 in
`workflow.properties`.
