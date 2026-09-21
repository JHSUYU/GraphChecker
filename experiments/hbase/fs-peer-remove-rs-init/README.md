# Filesystem peer removal during RegionServer replication initialization

`ReplicationPeers.init` first enumerates peer IDs and then loads each peer's
configuration. `FSReplicationPeerStorage.removePeer` deletes `peer_config`
before removing the directory. If Master removal happens after a RegionServer
enumerates a valid ID but before it calls `getPeerConfig`, the latter sees null
data and the explicit `if (data == null || data.length == 0)` throws
`ReplicationException`. `Replication.initialize` wraps that in
`IOException("Failed replication handler create", cause)`.

The [unit test](/u/vnr3ne/hbase/hbase-server/src/test/java/org/apache/hadoop/hbase/replication/regionserver/TestFSPeerRemovalDuringReplicationInit.java:88) uses real filesystem storage and real `Replication.initialize` with a latch after `listPeerIds`. It removes the peer from separate Master-side storage, then asserts both exception messages/classes and the empty RegionServer cache. [Surefire](/u/vnr3ne/hbase/hbase-server/target/surefire-reports/org.apache.hadoop.hbase.replication.regionserver.TestFSPeerRemovalDuringReplicationInit.txt) reports 1 test, 0 failures, 0 errors. It uses a mocked `Server` interface and does not boot a full RegionServer. The [SMT ordering model](/u/vnr3ne/hbase/hbase-server/src/test/resources/adhoc-coordination/fs-peer-remove-during-rs-init.smt2) returns `sat` for removal between enumeration and read, `unsat` for removal after the read.

Sources: `FSReplicationPeerStorage.java:127-140,174-190,209-220`, `ReplicationPeers.java:69-73,154-156`, and `Replication.java:100-108`. Novelty is provisional. Targeted Jira/GitHub searches found no exact report; [HBASE-26963](https://issues.apache.org/jira/browse/HBASE-26963) concerns a bad peer causing removal to hang, not this startup race.
