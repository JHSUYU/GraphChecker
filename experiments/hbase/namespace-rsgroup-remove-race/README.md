# Namespace creation overlaps RSGroup removal (candidate)

`CreateNamespaceProcedure.prepareCreate` checks that target group G exists and
has servers (`CreateNamespaceProcedure.java:190-192`,
`AbstractStateMachineNamespaceProcedure.java:124-130`). The procedure writes
the descriptor later in `CREATE_NAMESPACE_INSERT_INTO_NS_TABLE` (`:75-77`). If G
has one server, another operation can move that server out after prepare.
`RSGroupInfoManagerImpl.removeRSGroup` then sees zero servers and no namespace
descriptor referencing G, and removes G (`:370-399`). The original namespace
procedure subsequently commits a descriptor pointing to the now missing group.
An inherited table creation passes the old name through
`CreateTableProcedure.java:307-320`; `MasterProcedureUtil.java:225-233` throws
`ConstraintException` from `if (group == null)`.

The RSGroup manager's `synchronized` method does not hold the namespace
procedure's exclusive namespace lock. A [deterministic mini-cluster test](/u/vnr3ne/hbase/hbase-server/src/test/java/org/apache/hadoop/hbase/master/procedure/TestCreateNamespaceRSGroupRemovalCoordination.java:85)
reproduced the interleaving. It submits a real `CreateNamespaceProcedure`
subclass that pauses after the real PREPARE state, moves G's last server to
default, removes G through public Admin, lets namespace INSERT complete, then
checks the stale descriptor and actual `createTable` failure. It calls the
same group-existence guard used by `CreateTableProcedure` to pin the precise
`ConstraintException`. The public `admin.createTable` failure is asserted as
an `IOException` containing G; the direct production guard call pins the
precise exception class. The test does not restart the Master. Its
[Surefire report](/u/vnr3ne/hbase/hbase-server/target/surefire-reports/org.apache.hadoop.hbase.master.procedure.TestCreateNamespaceRSGroupRemovalCoordination.txt)
records 1 deliberate failure, 0 errors, at the final assertion expecting
no guard failure; every preceding assertion passed. It counts provisionally
in `findings.jsonl`. Existing
`TestRSGroupsAdmin1#testNamespaceConstraint` checks the sequential orders but
does not interleave them.

The [hand-built SMT model](namespace-rsgroup-remove-race.smt2) checks the
prepare→move→remove-scan→remove-commit→namespace-commit→table-check ordering;
Z3 returned `sat/unsat`. This is a path consistency aid, not an
end-to-end GraphChecker HBase execution. Targeted Jira/GitHub searches found
no exact report. [HBASE-25497](https://issues.apache.org/jira/browse/HBASE-25497)
concerns `move_namespaces_rsgroup` failing to update a namespace descriptor,
a different operation. Novelty remains provisional because the searches are
not exhaustive.
