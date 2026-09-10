# HDFS-11741 campaign

The workload retains the original HDFS-11741 behavior: the Balancer caches a
DataEncryptionKey and does not check its expiry on reuse. The Hadoop checkout
ports that cache predicate to the same current tracing and RPC interfaces used
by the other experiments.

The Balancer caches a key before two ordinary NameNode key rotations. DataNodes
refresh through the block-key RPC. The manually selected NameNode-side
`keyId` and `allKeys` values remain explicit symbolic roots. The custom JDK
propagates their expressions through the fixed sequence of replies into the
Balancer and DataNode state. Consumer anchors retain each receive boundary,
and selected shared reads retain bounded GuardedRead snapshots of their writer
expressions. The target is a DataNode lookup that cannot find the Balancer's
cached key.

The causal graph selects this closure and its instrumentation sites. Each
region contributes its own path condition; the composer recursively merges the
consumer-anchor families and directly lowers their propagated expressions.
Retained key-update loops use the configured fixed unroll, while every repeated
RPC and shared-state access keeps its boundary occurrence and candidate writer
versions.

Hadoop checkout: `/opt/hadoop-hdfs-11741`, branch `gc/hdfs-11741-current`.
Run `./run.sh build`, then `./run.sh campaign` from this directory. Set
`CAUSYNTH_OUTPUT_DIR` to a fresh directory for each campaign. The trace starts
after all stable sources and aliases are registered and before the cache and
key-map transitions, so cluster startup cannot create unregistered regions.
