# Two replayable AddPeer procedures contend for one sync peer lock

`AddPeerProcedure.releaseLatch` releases the Master-wide sync replication peer
semaphore while `ModifyPeerProcedure` is still executing its final
`POST_PEER_MODIFICATION` state. The ProcedureExecutor can persist the terminal
`SUCCESS` state only after that execution returns. During the interval, a
second sync peer procedure can acquire the semaphore and persist a noninitial
state. If the Master crashes before the first procedure's `SUCCESS` record,
both procedures are restored as noninitial. `AddPeerProcedure.afterReplay`
tries to acquire the single permit for each; the second throws
`IllegalStateException("Can not acquire sync replication peer lock ...")`.

The targeted [unit test](/u/vnr3ne/hbase/hbase-server/src/test/java/org/apache/hadoop/hbase/master/replication/TestAddPeerReplaySyncLockCollision.java:95) uses real `AddPeerProcedure` methods, `ReplicationLogCleanerBarrier`, semaphores, and the same protobuf procedure conversion used by the store. It asserts the named exception and a PRE-state control. [Surefire](/u/vnr3ne/hbase/hbase-server/target/surefire-reports/org.apache.hadoop.hbase.master.replication.TestAddPeerReplaySyncLockCollision.txt) reports 1 test, 0 failures, 0 errors. The test does not run a real ProcedureStore, restart a Master, or drive the full state machine scheduler; that crash window is established from `ModifyPeerProcedure` and `ProcedureExecutor` source. The [SMT model](/u/vnr3ne/hbase/hbase-server/src/test/resources/adhoc-coordination/add-peer-replay-sync-lock-collision.smt2) returns `sat` for two durable noninitial states and `unsat` when the second remains PRE.

Sources: `AddPeerProcedure.java:87-94,98-118,139-153`; `ModifyPeerProcedure.java:257-270`; `ProcedureExecutor.java:506-526`. Novelty remains provisional. Targeted Jira/GitHub searches found no exact replay overlap report. [HBASE-21389](https://issues.apache.org/jira/browse/HBASE-21389) revisited sync replication procedure locks generally; its accessible Jira page does not document this precise release-before-SUCCESS replay window. The related patch was not available during review.
