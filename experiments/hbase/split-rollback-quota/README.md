# Split rollback leaks namespace region quota (verified reproduction)

`SplitTableRegionProcedure.preSplitRegion` calls `MasterQuotaManager.onRegionSplit`,
which increments `NamespaceStateManager`'s cached count before daughter regions
exist. When a later rollback-supported split state fails, `rollbackState` has
no corresponding decrement. With a namespace maximum of two regions and one
real region, a failed split leaves the cache at two. A subsequent valid split
reaches `NamespaceAuditor.checkQuotaToSplitRegion` and explicitly throws
`QuotaExceededException` even though only one region exists in meta.
`MasterQuotaManager.onRegionSplitReverted` provides a decrement hook, but the
split rollback path never calls it.

The [mini-cluster test](/u/vnr3ne/hbase/hbase-server/src/test/java/org/apache/hadoop/hbase/master/assignment/TestSplitRollbackNamespaceQuotaCoordination.java:74) injects a one-shot failure in `preSplitRegionBeforeMETAAction`, after the quota increment and before meta update. It checks the first split actually reserved a slot, rolled back, and left one default replica. A second real split fails with the exact `QuotaExceededException`. Its final expected-count assertion deliberately fails at line 115 because the cache is 2 instead of 1. [Surefire](/u/vnr3ne/hbase/hbase-server/target/surefire-reports/org.apache.hadoop.hbase.master.assignment.TestSplitRollbackNamespaceQuotaCoordination.txt) reports 1 test, 1 deliberate failure, 0 errors. The [SMT model](/u/vnr3ne/hbase/hbase-server/src/test/resources/adhoc-coordination/split-rollback-namespace-quota.smt2) returns `sat/unsat` for the stale-count failure and its control.

[HBASE-28533](https://issues.apache.org/jira/browse/HBASE-28533) fixed an adjacent parent `SPLITTING` state left by split rollback; it did not describe or repair the quota count leak. Novelty is provisional under the ledger's targeted-search rule.
