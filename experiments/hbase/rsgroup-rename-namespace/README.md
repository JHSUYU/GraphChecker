# Namespace reference left behind by successful RSGroup rename (verified reproduction)

`RSGroupInfoManagerImpl.renameRSGroup(oldName, newName)` commits the new group
map and updates table descriptors that explicitly name `oldName`. It never
updates namespace descriptors. Namespace descriptors can also inherit an
RSGroup through `RSGroupInfo.NAMESPACE_DESC_PROP_GROUP`; `removeRSGroup` checks
and rejects such references, whereas rename proceeds. After a successful
rename, a newly created table with no explicit group inherits the stale
namespace value. `CreateTableProcedure.prepareCreate` passes that value to
`MasterProcedureUtil.checkGroupExists`; its `if (group == null)` throws a
`ConstraintException` claiming the inherited group does not exist.

This is distinct from `rsgroup-rename-partial-failure`: the rename completes
successfully and no fault injection is needed. The SMT model has a reachable
exception and an unsatisfiable control when the namespace reference is updated.
The mini-cluster test ran through public `admin.renameRSGroup`: the targeted
[Surefire report](/u/vnr3ne/hbase/hbase-server/target/surefire-reports/org.apache.hadoop.hbase.rsgroup.TestRSGroupRenamePartialFailureCoordination.txt)
and [Maven log](/tmp/hbase-rsgroup-namespace-public-api.log) record 1 deliberate
red assertion at test line 161, 0 errors, with
`ConstraintException: Region server group rename_old for table
rename_inherited:t(inherit from namespace) does not exit`. The test first
asserts a successful rename, the unchanged namespace descriptor, and failure
of a real `admin.createTable`; it then calls the exact guard from
`CreateTableProcedure` to pin the exception class. The RPC failure is only
checked as an `IOException` mentioning the old group name.

Targeted Jira/GitHub searches found no exact report. [HBASE-24112](https://issues.apache.org/jira/browse/HBASE-24112) introduced
renaming, and [HBASE-24721](https://issues.apache.org/jira/browse/HBASE-24721) fixed destination overwrite. Novelty remains provisional and this case is
counted under the ledger's targeted-search rule.
