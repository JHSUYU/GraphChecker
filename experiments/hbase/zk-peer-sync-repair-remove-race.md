# ZK peer sync-state repair can recreate a removed peer

## Causal path and exact predicate

1. An old-format ZooKeeper peer has a valid config at the peer parent but no `new-sync-rep-state` child. This is the supported condition in `ReplicationPeerStorageTestBase.testNoSyncReplicationState`. Master `ReplicationPeerManager.create` loads and repairs only the current sync state at line 708; it does not initialize the missing new-state child. RegionServer `ReplicationPeers.createPeer` reads config, enabled flag, current state, then new state at lines 155–159.
2. `ZKReplicationPeerStorage.getSyncReplicationState` reads an absent new-state child, then at line 220 sees that the parent exists. The targeted test pauses the reader immediately after that real ZooKeeper `exists` result is returned.
3. `ZKReplicationPeerStorage.removePeer` calls `ZKUtil.deleteNodeRecursively` and completes. The test verifies that the parent is absent before the reader resumes. Master removal is a procedure action; the RegionServer read uses a different watcher and is not serialized by the RegionServer's per-peer procedure lock.
4. The reader's `ZKUtil.createSetData` sees the child absent. `ZKUtil.createWithParents` catches `NoNodeException` and recursively creates the missing peer parent with `new byte[0]`, then creates the new-state child. The reader returns `SyncReplicationState.NONE` despite the peer having been removed.
5. `listPeerIds` now includes the empty peer parent. `ZKReplicationPeerStorage.getPeerConfig` reads its empty data and executes `if (data == null || data.length == 0)` at line 176, directly throwing `ReplicationException("Replication peer config data shouldn't be empty, peerId=...")`. There is no nested cause in this direct throw.

This is a real storage-level ZooKeeper race. The test does not restart a Master or RegionServer. The startup consequence is a source-based inference: Master `ReplicationPeerManager.create` iterates `listPeerIds` and calls `getPeerConfig` before it can initialize; RegionServer `ReplicationPeers.init` likewise lists peers, and its `createPeer` calls `getPeerConfig`. RegionServer `Replication.initialize` wraps the resulting `ReplicationException` in `IOException("Failed replication handler create", e)`.

## Verification

- Test: `/u/vnr3ne/hbase/hbase-replication/src/test/java/org/apache/hadoop/hbase/replication/TestZKPeerSyncRepairRemoveRace.java:53`. It uses a real mini ZooKeeper cluster and spies only on the reader's `RecoverableZooKeeper.exists` return to impose the order. The writer performs the real `removePeer`. Assertions check the parent is initially gone, subsequently reappears with zero-length config, appears in the peer listing, and causes the named `ReplicationException` on config read. A healthy old-format peer repaired without concurrent removal retains its config.
- Command: `JAVA_HOME=/tmp/hbase-jdk17/usr/lib/jvm/java-17-openjdk-amd64 PATH=/tmp/hbase-jdk17/usr/lib/jvm/java-17-openjdk-amd64/bin:$PATH mvn -pl hbase-replication -am test -Dtest=TestZKPeerSyncRepairRemoveRace -Dsurefire.failIfNoSpecifiedTests=false -Dcheckstyle.skip -Drat.skip -Dspotbugs.skip`
- Evidence: `/u/vnr3ne/hbase/hbase-replication/target/surefire-reports/org.apache.hadoop.hbase.replication.TestZKPeerSyncRepairRemoveRace.txt` reports one test, zero failures/errors/skips; `/tmp/hbase-zk-peer-sync-repair-remove-race.log` reports `BUILD SUCCESS`. The test asserts the exception, so Surefire has no failure stack trace.
- SMT: `/u/vnr3ne/hbase/hbase-replication/src/test/resources/adhoc-coordination/zk-peer-sync-repair-after-removal.smt2`; `/tmp/hbase-z3/usr/bin/z3` returns `sat`, `unsat`, `unsat` for the race, healthy repair, and modern-format controls respectively.
- Initial Maven invocation with default JDK 11 stopped at Maven Enforcer before any tests. The JDK 17 invocation above succeeded.

## Existing tests and prior issues

`ReplicationPeerStorageTestBase.testNoSyncReplicationState` tests lazy repair with no remover. `TestZKReplicationPeerStorage` runs it against mini ZooKeeper. `TestReplicationStateBasic` reads/refreshes peer cache without peer removal during state initialization. None covers the parent-exists/read-repair window.

Targeted ASF Jira searches on 2026-09-19 for `ZKReplicationPeerStorage`, sync state, peer removal, `createWithParents`, and ghost znodes did not find this failure. [HBASE-16135](https://issues.apache.org/jira/browse/HBASE-16135), [HBASE-12769](https://issues.apache.org/jira/browse/HBASE-12769), and [HBASE-17077](https://issues.apache.org/jira/browse/HBASE-17077) concern leftover replication queues after peer removal. Novelty is provisional; the search is not exhaustive.
