# Mixed existing and missing table in `setRSGroup`

Status: verified reproduction; novelty provisional.

## Production path

- Public synchronous `Admin.setRSGroup` delegates to `AsyncAdmin.setRSGroup` via `AdminOverAsyncAdmin.java:1125-1126`.
- `RawAsyncHBaseAdmin.java:4538-4551` starts separate `tableExists` requests. A missing table's callback takes `if (!exist)` and completes the returned future with `TableNotFoundException`.
- Without waiting for those checks, `RawAsyncHBaseAdmin.java:4553-4573` requests descriptors and starts a `modifyTable` for each descriptor in the response.
- `HMaster.java:3883-3895` silently omits a missing requested table from the descriptor list, so a mixed set still returns the existing table and permits its modification.

The coordinated states are the Meta table-existence result for the missing member, the Master's descriptor list for the existing member, and the returned future's completion. The exception branch and table mutation can both execute for the same public call.

## Evidence and limits

- [Java regression](/u/vnr3ne/hbase/hbase-server/src/test/java/org/apache/hadoop/hbase/rsgroup/TestRSGroupSetMixedMissingTable.java) creates one real table and an RSGroup, then calls public `Admin.setRSGroup` with that table plus a missing one. The test confirms the exact `TableNotFoundException` and a changed descriptor, then deliberately ends with a failing safety assertion. [Surefire](/u/vnr3ne/hbase/hbase-server/target/surefire-reports/org.apache.hadoop.hbase.rsgroup.TestRSGroupSetMixedMissingTable.txt) and [Maven log](/tmp/hbase-rsgroup-set-mixed-missing-test.log) record 1 test, 1 deliberate final failure, 0 errors. The sole failure is Java line 81: expected `default`, actual `rsgroup_set_target`.
- [SMT-LIB2](/u/vnr3ne/hbase/hbase-server/src/test/resources/adhoc-coordination/rsgroup-set-mixed-missing-table.smt2) is a hand abstraction of the relevant source relations. `/tmp/hbase-z3/usr/bin/z3 -smt2` returns `sat / unsat / unsat` for the failure window, valid-input control, and joined-precheck control. It is a path-consistency aid, not an end-to-end GraphChecker execution of HBase bytecode.
- Existing `TestRSGroupsAdmin1` checks a single missing member (`testBogusArgs`, `testNonExistentTableMove`) and a two-existing-table success (`testMultiTableMove`). It does not check the mixed set.

## Novelty review

Targeted ASF Jira and `apache/hbase` GitHub searches on 2026-09-19 did not find an exact report of this asynchronous `tableExists`/descriptor fan-out. [HBASE-16430](https://issues.apache.org/jira/browse/HBASE-16430) fixed a historical multiple-table group-map update bug; it used a different storage representation and did not describe a missing-member exception paired with another member's successful mutation. Novelty remains provisional pending wider review.
