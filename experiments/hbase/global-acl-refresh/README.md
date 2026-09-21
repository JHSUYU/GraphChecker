# Transient global ACL denial during refresh

`ZKPermissionWatcher.refreshNodes` calls `AuthManager.refreshTableCacheFromWritable`
for the global ACL znode. `AuthManager.updateGlobalCache` clears the live
`globalCache` before iterating over and inserting the new ACL entries. During
that interval `AccessChecker.requireGlobalPermission` can read the empty cache
and throw `AccessDeniedException` even if both the old and new ZooKeeper ACLs
grant the user the same action.

The unit test `TestGlobalPermissionRefreshCoordination` pauses the real
`updateGlobalCache` method immediately after `clear`, at its `keySet` read. It
checks the real `AccessChecker` before, during, and after refresh. The injected
pause stands for scheduler interleaving; it does not model a ZooKeeper failure.

Source chain: `AccessController.java:270-290` writes ACL table changes to the
ZooKeeper mirror; `ZKPermissionWatcher.java:159-177` receives a child data
change on its executor, then `:243-253` passes the global entry to
`AuthManager.refreshTableCacheFromWritable` at `AuthManager.java:112-120`.
`PermissionStorage.java:105-108` identifies the global entry. The cache is
cleared and repopulated at `AuthManager.java:156-169`; concurrent authorization
reads it at `:211-229`; `AccessChecker.java:138-153` throws
`AccessDeniedException` for the resulting denial. Initial watcher load and
children-change refresh also reach the same cache updater.

Surefire `hbase-server/target/surefire-reports/org.apache.hadoop.hbase.security.access.TestGlobalPermissionRefreshCoordination.txt`:
1 test, 1 intentional regression failure, 0 errors, 0 skipped. The failure at
test line 111 reports `Insufficient permissions for user 'coordination_user'
(global, action=ADMIN)` after the before/during/after checks. The test invokes
the actual private cache updater by reflection and tests the actual checker;
it does not run the ZooKeeper event path.

[HBASE-28984 / PR #6485](https://github.com/apache/hbase/pull/6485/files)
already fixed the same clear-while-reading mechanism for table and namespace
`PermissionCache` updates. Its diff leaves `updateGlobalCache` unchanged, so
this is an uncovered global scope of a known race mechanism, with provisional
novelty as a distinct affected scope. [HBASE-12402](https://issues.apache.org/jira/browse/HBASE-12402)
concerns watcher-startup ordering and stale table ACL data, a different route
to `AccessDeniedException`.

`global-acl-refresh.smt2` composes the ZooKeeper ACL, local cache transition,
RPC arrival order, and exception branch. The first query should be `sat` and
the completed-refresh control should be `unsat`.
