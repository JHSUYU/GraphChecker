# Replication peer creation after a lost ZooKeeper multi acknowledgement

Status: **storage-layer exception verified; novelty and end-to-end procedure
impact provisional**. It shares the low-level `RecoverableZooKeeper.multi` retry mechanism
with the separate RSGroup deletion candidate, but its operation, error code,
and downstream consequence differ.

## Causal path and target predicate

1. `ZKReplicationPeerStorage.addPeer` (lines 97-116) builds a four-create
   ZooKeeper transaction for peer config, enabled state, current sync state,
   and new sync state, then calls `ZKUtil.multiOrSequential(..., false)`.
2. `RecoverableZooKeeper.multi` (lines 666-691) prepares and replays the same
   operation list after `CONNECTIONLOSS`, `OPERATIONTIMEOUT`, or
   `REQUESTTIMEOUT`. It does not check whether an ambiguous first attempt
   already committed.
3. If the first multi commits but its reply is lost, the replay observes the
   already-present peer node. ZooKeeper raises `NODEEXISTS`; the
   `ZKUtil.multiOrSequential` `NODEEXISTS` branch (lines 1279-1302) rethrows
   because `runSequentialOnMultiFailure` is false. `addPeer` catches it and
   throws `ReplicationException("Could not add peer with id=...")`.
4. `ReplicationPeerManager.addPeer` (lines 285-298) updates its local `peers`
   map only *after* `peerStorage.addPeer` returns, so that map remains absent
   after the exception while the ZooKeeper peer is present.
   `ModifyPeerProcedure.UPDATE_PEER_STORAGE` (lines 203-214) suspends on
   `ReplicationException`; on resume, the manager's `peers.containsKey`
   retry guard is false and it attempts the already-present ZK create again.
   The public add procedure can thus remain stuck until outside repair.

The explicit target is the `NODEEXISTS` branch in `ZKUtil.multiOrSequential`
and the `ReplicationException` thrown by `ZKReplicationPeerStorage.addPeer`.
The contradictory coordination state is *peer present in ZK* plus *peer absent
from the Master's local map/procedure progress*, caused by an ambiguous reply.

## Reproduction and model

`hbase-replication/src/test/java/org/apache/hadoop/hbase/replication/TestZKReplicationPeerMultiLostAckAdd.java`
uses a real mini ZooKeeper cluster. A `ZooKeeper` subclass commits the first
target `multi` with `super.multi`, then throws `ConnectionLossException` to
simulate loss of the acknowledgement. The test checks a normal creation
control, two target multi calls, the exact `NodeExistsException` cause, and
all four resulting znodes. [Surefire](/u/vnr3ne/hbase/hbase-replication/target/surefire-reports/org.apache.hadoop.hbase.replication.TestZKReplicationPeerMultiLostAckAdd.txt)
reports 1 test, 0 failures, 0 errors, and
[/tmp/hbase-replication-peer-zk-multi-lost-ack-test.log](/tmp/hbase-replication-peer-zk-multi-lost-ack-test.log)
reports `BUILD SUCCESS`. The test asserts the `ReplicationException` and its
`NodeExistsException` cause directly; the output log only shows the injected
connection-loss retry because the expected exception is caught by JUnit.

`hbase-replication/src/test/resources/adhoc-coordination/replication-peer-zk-multi-lost-ack-add.smt2`
models commit, reply loss, replay, and the `NODEEXISTS`/fallback branch.
Z3 returned `sat` for committed multi plus lost reply and `unsat` for a
delivered reply or an uncommitted first attempt under the same target.

## Prior-issue check and scope

Targeted official ASF Jira searches found no exact report of a successful
peer-create multi replayed after reply loss. [HBASE-2611](https://issues.apache.org/jira/browse/HBASE-2611)
concerns region-server failure during replication queue transfer and merely
introduced use of ZK multi. [HBASE-27110](https://issues.apache.org/jira/browse/HBASE-27110)
introduced alternate peer storage and says ZooKeeper remains the default.
This is a provisional novelty check, not proof that no prior report exists.

The test targets the storage layer and proves the immediate exception/state
if it passes. The procedure stall is currently a source-level consequence,
not yet exercised by an end-to-end Master procedure test.
