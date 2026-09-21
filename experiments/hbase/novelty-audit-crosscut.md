# Cross-cutting audit of existing HBase findings (2026-09-19)

Scope: the 55 existing `findings.jsonl` rows at HBase commit
`1790942bb2d46f41f1b4aed94db85e6f5bd18a1a` (2026-09-18). This audit
adds no candidate. The previous count of 53 means *provisionally independent
reproductions*, not 53 proven first reports.

## Evidence inventory

- All 55 rows point to a present HBase test source file and a present targeted
  Surefire XML report. All 54 `verified` rows point to a present SMT file;
  the one candidate has no SMT. Eight older rows use paths relative to this
  experiments directory; those paths exist after correct resolution.
- The latest targeted Surefire XML files comprise 28 green and 27 red reports.
  The red reports usually fail a final desired-state assertion after the
  incident path is asserted. A red report is evidence of the trace only after
  its precise failure and preceding assertions are inspected; it is not a
  passing regression test.
- One row is already excluded from the independent count:
  `HBASE-REPLICATION-PEER-ZK-MULTI-LOST-ACK-ADD-001` shares the ambiguous
  ZooKeeper multi reply/replay root with RSGroup deletion. The duplicate-close
  row is still only a candidate. Neither should be presented as a newly
  verified independent bug.

## Conservative novelty flags under review

- [HBASE-18415](https://issues.apache.org/jira/browse/HBASE-18415) explicitly
  describes a request committing, a timeout, and an Admin retry with a
  different nonce that meets already-changed state. The existing backup
  snapshot lost-ACK row has a backup-specific outer retry with the same
  general non-idempotence mechanism. It may be a new affected caller but is
  not safely described as a wholly new coordination mechanism.
- The MapReduce unresolved-region-host row's `isUnresolved()` branch only
  logs; its eventual NPE comes from an implicit dereference in `reverseDNS`.
  It does not meet the earlier strict branch-local explicit-throw criterion.
  The REST scanner-close and disabled-registry-refresher NPE rows likewise
  need separate scrutiny under that criterion.
- Backup lock outcomes need root-cause clustering. The orphan-session,
  failed-history-scan, and precheck/delete paths all end at the same
  exclusive-lock CAS failure but arise at different cleanup sites. A rejected
  merge contender and a live-session repair both release another operation's
  lock; missing ownership enforcement is common to both even though the
  callers and triggers differ. The independent-bug count should reflect that
  distinction after auditing the source and prior issues.
- `ConnectionUtils.getOrFetch` expressly describes the possibility of a stale
  in-flight registry result after cache clearing and says a caller can retry
  later. The Meta-replica stale-fetch test shows one public lookup exception
  with a controlled registry, but not that the ordinary retried data path
  fails. Its bug status is weaker than its trace reproduction.
- `IncrementCoalescer.createIncCallable` deliberately throws `IOException`
  labelled `Auto-Fail rest of ICVs` after more than two failures and catches it
  to log `FAILED_ICV`. Its cross-table data loss under that branch is a real
  observed behavior, but whether it violates the documented optional
  coalescing semantics is unproved. Do not present it as a definite new bug.
- The equal-clock split collision is mechanically real under a manually
  injected clock, but the test does not show an ordinary production split
  reaching the exact equality boundary. [PR #8395](https://github.com/apache/hbase/pull/8395)
  already reports the same encoded-name collision guard for a different
  crafted input. Hold it from a strict new-production shortlist.
- [HBASE-28984 / PR #6485](https://github.com/apache/hbase/pull/6485/files)
  previously identified the clear-then-repopulate authorization-cache race
  for table/namespace permissions. The global cache remains vulnerable, but
  the coordination mechanism is known; calling it wholly new would mislead.
- The AddPeer replay semaphore test directly serializes two procedure
  instances into a replay state. Without an actual ProcedureStore crash/replay
  demonstrating both records coexist, its durable incident premise is still
  an inference.
- RSGroup `saveRSGroupMapToZK` has deliberately aborted Master for any
  `KeeperException` since its early implementation
  ([HBASE-6721 implementation commit](https://github.com/apache/hbase/commit/ca816f0780)).
  The lost-ACK test proves this fail-stop path can occur after a committed
  delete, but without a guarantee that Master must continue on ambiguous
  ZooKeeper outcomes it should not appear in the strongest new-bug list.
- `Table.batchCallback` publicly warns that it needs an extra region locate
  after the action. A successful Put followed by table deletion makes that
  lookup fail, as tested, but the method is deprecated and the warning makes
  its correctness promise uncertain. Hold that row from the strongest list.

Three companion per-row audits cover entries 1–18, 19–36, and 37–55. Only
cases with a convincing bug invariant, causally reproduced failure, and no
matching public predecessor should appear in a user-facing new-bug list.
