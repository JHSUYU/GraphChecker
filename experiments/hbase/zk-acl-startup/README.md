# ACL watcher initialization failure while RPC startup continues

`HMaster.java:591` and `HRegionServer.java:558` call their RPC service
`start`. `HBaseRpcServicesBase.internalStart` creates an authorization-enabled
`AccessChecker`, calls `ZKPermissionWatcher.start`, catches and logs
`KeeperException`, then calls `rpcServer.start()` unconditionally
(`HBaseRpcServicesBase.java:177-190`). During initial watcher start,
`ZKPermissionWatcher.java:74-101` registers a listener and calls
`ZKUtil.watchAndCheckExists`; if the ACL parent exists it fetches and installs
its child ACL data. A thrown `KeeperException` before that fetch leaves the
new `AuthManager.globalCache` empty (`AuthManager.java:89`).

For an ordinary, non-superuser caller with an existing ZooKeeper global ADMIN
grant, `AuthManager.authorizeUserGlobal` reads that empty local cache and
returns false (`AuthManager.java:211-229`).
`AccessChecker.requireGlobalPermission` throws `AccessDeniedException` at
`AccessChecker.java:138-153`. A Master administrative RPC reaches the same
check through `MasterRpcServices.rpcPreCheck` at `:541-547`; RegionServer
administrative RPCs use `RSRpcServices.rpcPreCheck` at `:578-584`. The test
uses the Master service to exercise the startup catch and actual checker. It
does not send a network RPC or run a real ZooKeeper server.

The deterministic test `TestZKPermissionWatcherStartupFailure` serializes a
normal global ADMIN grant and first proves it authorizes through a healthy
real `AccessChecker`. It injects one `ConnectionLossException` from
`ZKUtil.watchAndCheckExists` while starting `MasterRpcServices`, verifies the
mock RPC server's `start` call, and checks the service's real `AccessChecker`
rejects that same user. Loading the same ACL bytes into that live checker is
the healthy control. The bytes stand for already committed ZooKeeper ACL data;
the test does not exercise ZooKeeper persistence or notification delivery.

The [Surefire report](/u/vnr3ne/hbase/hbase-server/target/surefire-reports/org.apache.hadoop.hbase.master.TestZKPermissionWatcherStartupFailure.txt)
records one test, zero failures, and zero errors; the test explicitly asserts
the `AccessDeniedException`. `zk-acl-startup.smt2` composes the persisted ACL
input, watcher success/fail arms, local cache state read, RPC startup, and
exception branch. Z3 returns `sat` for failed initial watch and `unsat` for
the same exception when the watcher loads the grant. This is hand-composed,
not emitted by the GraphChecker Java 8 recorder.

Targeted searches of ASF Jira and apache/hbase GitHub found no exact report
of `HBaseRpcServicesBase.internalStart` swallowing the initial ACL watcher
failure and serving requests with missing grants. [HBASE-8213](https://issues.apache.org/jira/browse/HBASE-8213)
describes an older global cache overwritten by configuration after startup;
[HBASE-12402](https://issues.apache.org/jira/browse/HBASE-12402) describes
table ACL data overwritten by a startup ordering race. Novelty review is
provisional.
