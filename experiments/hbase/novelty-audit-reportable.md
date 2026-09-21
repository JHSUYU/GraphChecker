# HBase ad hoc coordination: reportable exception failures

Audited 2026-09-19 against HBase commit `1790942bb2d46f41f1b4aed94db85e6f5bd18a1a`.

This is the conservative reporting set from the 55 existing ledger rows after
two audits: novelty and failure impact. These **36** findings each have a
reproduced ad hoc coordination-state mismatch that throws an exception causing
a meaningful public request or critical service operation to fail, or a
source-deterministic critical startup failure. No exact same-root predecessor
was found in the targeted ASF Jira and `apache/hbase` PR/commit review. This
bounded review cannot prove that no unpublished or unindexed report exists.
The entries are not all end-to-end distributed incidents; the companion audits
state the test boundaries. Historical `countedToward50` flags in
`findings.jsonl` are discovery bookkeeping and must not be read as this count.
Across all 55 rows, the exception-impact audit found 38 passing, 8 with
insufficient evidence, and 9 failing the requested criterion. Two of the 38
impact passes (#6 and #40) have known same-root predecessors, leaving 36 here.

| Ledger row | New finding | Reproduced effect |
| --- | --- | --- |
| 1 | Token-key roll lets a delayed issuer sign with an already expired key | A still-live token is rejected as `InvalidToken`. |
| 3 | A mixed-table synchronous replication batch inherits only the first entry's admission decision | With the blocked table first, `DoNotRetryIOException` rejects the healthy table's replication batch and stalls its WAL shipment. |
| 5 | A previously accepted CLOSED region report is retried after table deletion removes assignment state | The error response makes the RegionServer close handler throw and abort its server. |
| 7 | Interrupted filesystem peer removal leaves a disabled marker for a reused peer ID | Master and RegionServer peer states disagree; enabling throws. |
| 8 | Concurrent full backups can choose the same millisecond-based ID before taking the session lock | The second request fails at the existing snapshot directory. |
| 9 | An old descriptor scan overwrites a cache invalidation's visibility | Snapshot creation falsely reports a present table as absent. |
| 10 | Master serves RPCs after its first ZooKeeper ACL watch fails | A valid global grant remains invisible and authorization throws. |
| 11 | Specific-region reopen validates membership against the OPEN-only subset | A known CLOSED region is falsely reported as foreign to its table. |
| 12 | RSGroup rename commits the group map before a table descriptor write that can fail | The old name vanishes while the descriptor retains it; retry fails. |
| 13 | RSGroup rename omits namespace descriptors | A later table create using inherited placement fails on the stale group name. |
| 15 | RegionServer replication initialization reads peer IDs and configs at different moments | Ordinary peer removal between reads aborts initialization. |
| 16 | Split rollback leaves a namespace region-count reservation behind | A subsequent legal split is rejected by quota. |
| 17 | Backup repair ignores an exclusive lock acquired before its RUNNING history row | A crashed client leaves all later backups locked out. |
| 18 | Namespace creation validates an RSGroup before that group's removal becomes visible | A committed namespace retains a deleted group, blocking table creation. |
| 19 | Filesystem peer config's two-slot read races its rotation | A still-existing peer appears to have no config during replication init. |
| 20 | Backup deletion acquires the lock before a history scan outside its release `finally` | A scan error leaves the exclusive lock permanently set. |
| 22 | Peer IDs containing `/` are accepted but stored as nested paths | Peer enumeration loses the accepted peer; later state changes fail. |
| 23 | A backup merge contender that fails lock acquisition clears the actual owner's marker | The owner subsequently fails while its lock has been stolen. |
| 24 | Backup merge validates images before acquiring its lock while deletion can remove one | Merge dereferences missing metadata, leaks the lock, and fails the next exclusive operation. |
| 25 | Backup repair treats a live RUNNING session as abandoned | It clears that owner's lock, and the owner fails to release it. |
| 27 | A transient failed `.regioninfo` read during `refresh_meta` is treated as absence | Refresh deletes a live opening region; Master/RegionServer fail its open. |
| 28 | One caller's short timeout completes the shared region-locator future exceptionally | A concurrent caller without a timeout receives the other's timeout. |
| 29 | Restore does not hold the backup-delete isolation lock | Concurrent deletion removes its manifest and restore throws. |
| 30 | Snapshot procedure registration normalizes a key but status lookup uses the raw key | Public status throws `UnknownSnapshotException` for an active snapshot. |
| 32 | Clone quota counts an offline split parent from a snapshot manifest as an active region | A clone whose active daughters fit quota is rejected. |
| 34 | A long-lived Meta replica selector retains a removed replica after scale down | It pins the removed replica and public region-location lookup throws `RegionOfflineException`. |
| 36 | Quota chore publishes the observant snapshot before a table-enable action succeeds | A transient enable failure is never retried; the table stays disabled. |
| 37 | An unresolved region hostname reaches reverse DNS with a null address | MapReduce split planning throws a null-pointer exception. |
| 39 | A failed RSGroup persistence write leaves a mutated object in the published holder | Subsequent decisions use a group state that was never committed. |
| 44 | MOB cleanup combines successful family coverage with another family's failed scan | It archives a referenced MOB file and a later read fails. |
| 46 | Synchronous peer status interprets a literal peer ID as a regex | An existing peer ID containing regex syntax is reported missing. |
| 47 | REST scanner GET checks the generator while concurrent DELETE nulls its scanner | The in-flight GET throws a null-pointer exception. |
| 48 | MOB cleanup uses a split-parent directory name instead of its live reference set | It archives a still-referenced MOB file and a public read fails. |
| 50 | A non-force PITR backup batch lets two full images cover each other | Both are deleted, then the next continuous incremental backup fails. |
| 51 | Expired-MOB cleanup runs with an old descriptor after `minVersions` changes | It removes a value the new table policy must retain. |
| 55 | Legacy ZooKeeper peer sync-state repair races peer removal | Repair recreates an empty peer parent, then peer config lookup fails. |

Per-row source, regression, Surefire result, and prior-art comparisons:
[1–18](novelty-audit-01-18.md), [19–36](novelty-audit-19-36.md), and
[37–55](novelty-audit-37-55.md). The [cross-cutting audit](novelty-audit-crosscut.md)
records the held rows and duplicate-root checks. The stricter exception-impact
audit is in [1–18](coordination-impact-audit-01-18.md),
[19–36](coordination-impact-audit-19-36.md), and
[37–55](coordination-impact-audit-37-55.md). The five findings removed from
the prior 38-list were #21, #26, #33, #49, and #52; #5, #24, and #34 were
added after tracing their exception to the failed critical operation.
