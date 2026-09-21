# HBase ZooKeeper source and workload reading (2026-09-19)

The [HBase test index](hbase-test-reading-index.tsv) marks all 12 Java files under
`hbase-zookeeper/src/test/java` as `full`. Their current SHA-256 hashes and line
counts were rechecked before changing the statuses. The
[main-source index](hbase-main-reading-index.tsv) inventories 3,289 `src/main`
files. The ZooKeeper package and direct client dependencies are being read
file by file; the index records only complete reads so far:

- `MasterAddressTracker.java`: active and backup Master znode reads, writes,
  watchers, and versioned `deleteIfEquals`.
- `ZKNodeTracker.java`: local cached data, watcher callbacks, blocking and
  refresh branches.
- `ZKLeaderManager.java`: deprecated, documented as unused; leader znode
  acquisition and release.
- `RecoverableZooKeeper.java`: connection retry, create, delete, setData, and
  multi-operation semantics.
- `ReadOnlyZKClient.java` in `hbase-client`: asynchronous task queue, retry,
  completion, idle close, and explicit client close.
- `ClusterStatusTracker`, `DeletionListener`, `EmptyWatcher`, `InstancePending`,
  `MasterMaintenanceModeTracker`, `PendingWatcher`: cluster-state publication,
  deletion detection, and event handoff; maintenance tracker is explicitly
  documented as unused.
- `MetaTableLocator`: meta location/state znode publication, retrieval, and
  timeout path. Its `getMetaRegionState` can return null when interrupted, but
  this was not counted as a coordination bug without a qualifying branch and
  workload.
- `HQuorumPeer`, `MiniZooKeeperCluster`, `ZKAclReset`, `ZKAuthentication`,
  `ZKClusterId`, `ZKDump`, `ZKListener`, `ZKMainServer`, `ZKServerTool`,
  `ZKSplitLog`: configuration, auth, cluster ID, diagnostic, and test-cluster
  paths. `ZKSplitLog` is deprecated; no new failure candidate was counted.
- `ZKUtil`, `ZKWatcher`: watcher installation and delivery, znode operations,
  `multiOrSequential` error branches, ACL handling, connection events, and
  exception propagation. `ZKWatcher.keeperException` rethrows; methods that
  call it do not silently turn Keeper errors into absence.

## Workload coverage and exclusions

`TestRecoverableZooKeeper` injects one `ConnectionLossException` after a
successful `setData` and checks the version-reconciliation path. It does not
exercise an acknowledgement loss after a successful `multi` transaction.
`TestZKMulti` exercises transactional failure, optional sequential fallback,
and recursive deletes; it has no transport-failure injection after commit.
`TestMasterAddressTracker` tests steady Master/backup publication and removal;
`deleteIfEquals` reads a `Stat` and deletes with its version, so a newer
different znode cannot be deleted merely because it replaced the observed
one. `TestZKNodeTracker` covers creation, deletion, update and blocking
waiters. `TestReadOnlyZKClient` covers normal reads, missing nodes, session
expiration, timeout, and an outstanding request across idle-close time.

The remaining small tests cover ACL creation and interruption without a
server (`TestZKUtilNoServer`), ZooKeeper configuration and command-line
parsing (`TestHQuorumPeer`, `TestZKMainServer`), `InstancePending` wakeup,
leader transfer in the deprecated `ZKLeaderManager`, `ZKUtil` create/delete
and an existing ACL creation race, and `HBaseZKTestingUtil` helpers.

## Pending causal check

`RecoverableZooKeeper.multi` retries the identical operation list after an
ambiguous connection failure. `RSGroupInfoManagerImpl.saveRSGroupMapToZK`
submits deletes for removed groups through `ZKUtil.multiOrSequential(...,
false)`. If the first transaction commits and only its acknowledgement is
lost, retrying a delete against the now absent group could return `NONODE`.
The ZK utility would propagate it and the RSGroup manager would call
`masterServices.abort` and throw `IOException`. This requires a controlled
unit test, a full public-call trace, and prior-issue comparison before it can
be counted. The existing 51-count ledger does not include this candidate.

The repository-wide byte inventory and file indexes are not substitutes for
reading the remaining source files; the `semantic_status` columns expose that
gap explicitly.
