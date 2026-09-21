# RSGroup rename partial failure (verified reproduction)

`RSGroupInfoManagerImpl.renameRSGroup` persists a renamed group with
`flushConfig(newGroupMap)` before invoking `setRSGroup(updateTables, newName)`.
The latter creates and waits for table modification procedures. A failure in
their pre-operation hook leaves the old group absent from the persisted group
map while the table descriptor still names it. A client retry of the same
rename reaches `getRSGroupInfo(oldName)` and explicitly throws
`ConstraintException("RSGroup oldName does not exist")`.

The deterministic mini-cluster test rejects one table descriptor update in a
Master coprocessor after the group map is committed. It then checks both
coordination states and the exact retry exception. The retained [combined Maven log](/tmp/hbase-rsgroup-quota-replay-test.log)
records a deliberate red assertion at test line 115 with the captured
`ConstraintException: RSGroup rename_old does not exist`. The SMT file returns
`sat/unsat` for the failure and no-failure control. The fault is injected by a
coprocessor, and the test stays within a live Master; it does not restart the
Master to read persisted group state back. A later namespace-only rerun overwrote
the shared Surefire report file, so the combined log is the retained evidence
for this method.

Novelty is provisional. HBASE-24112 introduced group renaming and HBASE-24721
fixed an unrelated destination-overwrite defect; no exact partial-failure
report was found in targeted Jira/GitHub searches. The exact-match search was
limited, so this finding counts provisionally.
