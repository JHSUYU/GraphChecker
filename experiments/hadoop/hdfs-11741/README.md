# HDFS-11741 campaign

The workload retains the original HDFS-11741 behavior: the Balancer caches a
DataEncryptionKey and does not check its expiry on reuse. The Hadoop checkout
ports that cache predicate to the same current tracing and RPC interfaces used
by the other experiments.

The Balancer caches a key before two ordinary NameNode key rotations. DataNodes
refresh through the block-key RPC. GraphChecker explores the key IDs and expiry
values carried by those replies and the resulting production key-map updates.
The target is a DataNode lookup that cannot find the Balancer's cached key.

Hadoop checkout: `/opt/hadoop-hdfs-11741`, branch `gc/hdfs-11741-current`.
Run `./run.sh build`, then `./run.sh campaign` from this directory. Set
`CAUSYNTH_OUTPUT_DIR` to a fresh directory for each campaign. The trace starts
after all stable sources and aliases are registered and before the cache and
key-map transitions, so cluster startup cannot create unregistered regions.
