# Disabled marker survives a partial filesystem peer removal

`FSReplicationPeerStorage.removePeer` deletes `peer_config` before deleting
the peer directory (`hbase-replication/.../FSReplicationPeerStorage.java:128-140`).
A crash between those operations leaves the old disabled marker. On restart,
`listPeerIds` includes only directories with a readable `peer_config`
(`:174-191`), so `ReplicationPeerManager.create` omits the old peer
(`hbase-server/.../ReplicationPeerManager.java:685-709`). The persisted
`RemovePeerProcedure` resumes at `UPDATE_PEER_STORAGE`, but
`ReplicationPeerManager.removePeer` returns without storage cleanup when its
new map lacks the ID (`:301-307`; `ModifyPeerProcedure.java:203-215`).

When an enabled peer is later added under the same ID,
`FSReplicationPeerStorage.addPeer` writes the config but only *creates* a
disabled marker for a disabled add; it never removes a preexisting one for an
enabled add (`:99-121`). The Master stores enabled in its map
(`ReplicationPeerManager.java:285-298`), while the RegionServer's
`ReplicationPeers.init/createPeer` reads disabled from storage
(`hbase-replication/.../ReplicationPeers.java:69-73,153-168`). A requested
enable is rejected by the Master at `ReplicationPeerManager.java:216-220`
with `DoNotRetryIOException: ... has already been enabled`.

`TestFSReplicationPeerResurrectionMismatch` uses a real local filesystem peer
storage, Master manager, and RegionServer peer loader. It injects the crash
point by deleting `peer_config`, rather than killing and replaying a complete
Master procedure. Surefire:
`hbase-server/target/surefire-reports/org.apache.hadoop.hbase.master.replication.TestFSReplicationPeerResurrectionMismatch.txt`,
1 test, 0 failures, 0 errors, 0 skipped; the assertion checks the exception.

The [SMT model](/u/vnr3ne/hbase/hbase-server/src/test/resources/adhoc-coordination/fs-peer-reuse-disabled-marker.smt2)
ties storage, Master, and RegionServer state to the target exception branch.
Z3 returns `sat` with orphan cleanup absent and `unsat` if replay cleans the
orphan directory. The clean-replay arm is a counterfactual control.
