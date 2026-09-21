# hbase-replication production source reading (2026-09-19)

All **21** files under `hbase-replication/src/main` were read in full in this
continuation. SHA-256 and line counts were rechecked against the workspace
before their entries were marked `full` in
[the main-source index](hbase-main-reading-index.tsv). The module contains
3,447 lines of Java and no other `src/main` files. This covers the storage
module, not the many replication procedures and source/sink workers in
`hbase-server`.

## Coordination semantics checked

- `ZKReplicationPeerStorage` uses one strict ZooKeeper multi for four peer
  znodes and lazily creates missing current/new sync-state nodes for old peers.
  `FSReplicationPeerStorage` writes state/disabled markers first and peer
  config last; its listing filters out directories without config. Both
  implementations expose the same peer-storage interface, but differ in
  how incomplete peers become visible.
- `ReplicationPeers` maintains the RegionServer's local cache. Its `createPeer`
  reads config, enable flag, current sync state, and new sync state separately;
  explicit refreshes update cached fields. `ReplicationPeerImpl` stores both
  sync-state halves in one volatile int for an atomic local read.
- `TableReplicationQueueStorage` stores WAL offsets, serial last-sequence IDs,
  and HFile refs in a table. `setOffset` uses a conditional multi-row mutation
  for offsets plus serial sequence IDs; `claimQueue` uses a conditional
  delete/put for ownership transfer. `ReplicationQueueId` encodes owner,
  peer, and optional source server, relying on forbidden `-` in peer IDs.
- `ZKReplicationQueueStorageForMigration` destructively iterates legacy
  queue/sequence/HFile-ref trees, removing each previous subtree on the next
  iterator call. `CopyReplicationPeers` reads each source peer and rejects
  non-`NONE` intermediate sync state before copying; its existing test covers
  only quiescent migration.
- `ReplicationStorageFactory` defaults to ZooKeeper peer storage for upgrade
  compatibility and table queue storage. The remaining interfaces, value
  types, and helpers were read in full and added no independently qualifying
  exception path.

## Candidate handling and exclusions

The peer-create lost-ACK path is documented separately in
[replication-peer-zk-multi-lost-ack.md](replication-peer-zk-multi-lost-ack.md).
It is verified by a storage-layer test but conservatively excluded from the
independent count because it shares `RecoverableZooKeeper.multi`'s ambiguous
reply/replay root with the RSGroup deletion finding.

An older peer missing `new-sync-rep-state` can race its removal while
`ZKReplicationPeerStorage.getSyncReplicationState` lazily repairs the missing
child. `ZKUtil.createWithParents` recreates the just-deleted parent as an
empty ghost peer, after which `getPeerConfig` takes its explicit empty-data
`ReplicationException` branch. The separate mini-ZK test now passes and this
distinct repair/removal race is counted provisionally; see
[zk-peer-sync-repair-remove-race.md](zk-peer-sync-repair-remove-race.md).

`TableReplicationQueueStorage.getReplicableHFiles(peerId)` uses a prefix scan
that can include a different peer whose ID begins with this ID. The known
production callers here are diagnostic/maintenance paths and tests; no
qualifying explicit exception caused by that relation was established.
Likewise, a lost response after conditional `claimQueue` might cause a later
retry to return an empty map, but that path currently has no demonstrated
`if`-guarded exception target. Neither was counted.

At the time of this module pass the source index reached 57/3,289 full reads;
later metrics/logging reads raised it to 86/3,289. Byte inventory and source
search are not being described as semantic reading.
