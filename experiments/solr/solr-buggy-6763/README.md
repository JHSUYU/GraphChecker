# SOLR-6763 at solr-adhoc-38: not reachable on today's code (no case run)

[SOLR-6763](https://issues.apache.org/jira/browse/SOLR-6763) (fix 5dbff1d1c1d, 2014): a ZooKeeper session expiry
while a shard leader election waits for its replicas (`ShardLeaderElectionContext.waitForReplicasToComeUp`) was
logged and looped over, so after the reconnect two elections ran for one core: the stale one registered as leader
(cluster state names the core leader) while the new one failed and cleared `CloudDescriptor.isLeader`, and every
update was refused by solr-adhoc-38's guard (`DistributedZkUpdateProcessor.java:1031`, "cluster state says we are
the leader, but locally we don't think so"). The fix throws on `SessionExpiredException` in that wait.

**Verdict: not reachable on graphchecker/solr-checks (12d23091d1, lucene-solr 8.11): masked by SOLR-7844
(442963d020, 2015, "Zookeeper session expiry during shard leader election can cause multiple leaders").** The fix's
lines are there verbatim (`ShardLeaderElectionContext.java:398-403`) and could be deleted, but SOLR-7844 closed the
same window twice more, so the deletion alone changes nothing the point can see:

1. `ShardLeaderElectionContext.java:128-133`: `if (isClosed) return;` right after `waitForReplicasToComeUp`
   returns. On `Expired`, `ConnectionManager.java:140-146` (solrj) runs the BeforeReconnect command before it opens
   the new session (`:152-161`), and ZkController's (`ZkController.java:457-467`) closes every outstanding election
   context (`closeOutstandingElections`, `:563-587`; `ShardLeaderElectionContext.close()` sets `isClosed`, `:67-71`).
   Without the bail-out the old wait loops on the dead session until that runs, leaves at `while (!isClosed ...)`
   (`:391`) and returns at `:128`.
2. `ShardLeaderElectionContextBase.java:128-143`: the leader registration is one multi, `Op.check(leaderSeqPath)` +
   `Op.create(leaderPath, EPHEMERAL)` + `Op.setData(parent)`, retried only on NodeExists; an election whose sequence
   node died with the expired session cannot write the leader node.

The study's chain (the old election survives, writes the leader node, the new one sets `isLeader=false`) needs both
gone, which is reverting most of SOLR-7844 (11 files): a backport to 2014 code, not a small change on today's (owner,
2026-10-26). Decision: the lead, 2026-10-26 (no case, no run). Notes:
`/bulk/analysis/buggy-detect-2026-10-26/6763-notes.md`.

On the fixed code the point is already SAT through a different fault world (STATUS "Solr checks", solr-adhoc-38,
SGF9: MARKER_FLIPPED, confirmed in the VM, native 0/10).
