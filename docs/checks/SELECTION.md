# The ad hoc check selection: the final table (owner 2026-10-21)

This is the one table every branch shares (owner 2026-10-21: "删除所有的旧的文档里数据，全局分支通用的就是这个最终的表"). It
replaces the narrowed selection of 2026-10-04 and its counts. Ids are study.txt's (hdfs-adhoc-NN, solr-adhoc-NN,
hbase-adhoc-NN, zk-adhoc-NN), each marked at its throw by `@CausynthExceptionTarget("<id>")`.

| system | heuristic YES points (study.txt) | selected ad hoc check points | with an integration test we run | causym executions |
| --- | ---: | ---: | ---: | ---: |
| HDFS | 53 | 38 | 36 | 46 |
| Solr | 40 | 21 | 13 | 20 |
| HBase | 38 | 25 | 19 | 22 |
| ZooKeeper | 13 | 19 | 16 | 16 |
| **total** | **144** | **103** | **84** | **104** |

**The columns:**
- **Heuristic YES points:** study.txt's binary rule over HDFS 3.4.3, Solr 8.11.4, HBase 2.6.6 and ZooKeeper 3.8.7.
- **Selected points:** the heuristic points kept after the low-quality ones are removed (each removal and its reason is
  below). For ZooKeeper the selection also counts the six bug points added for its checks (owner: "zookeeper选出来带上我们
  新加的"). Every selected point is real ad hoc coordination.
- **With an integration test we run:** a cluster integration test reaches the point's guard, and we run it: an
  existing test, or our modified `Causynth*` version of one.
- **Causym executions:** one per (point, integration test) we run, bug checks included. One point may carry several,
  e.g. HDFS-11 carries 9.

## HDFS: 38 selected, 36 with an integration test, 46 executions

**Selected and run (36):** 05 06 07 08 09 10 11 12 14 15 16 19 20 21 22 23 24 25 26 27 28 29 30 31 33 34 35 37 38 39
40 45 48 49 50 52 (`experiments/hadoop/hdfs-adhoc/checks.tsv`).

**Selected without a usable test (2):**
- 13 (BlockTokenSecretManager:432, NO_PATH: no cluster test);
- 18 (DatanodeDescriptor:537, WORKLOAD_UNCERTAIN: its test does not guarantee the second PROVIDED-storage update).

**Executions (46):**
- 36 study cases, one per run point;
- 10 bug checks:
  - on HDFS-11 (8): hdfs-11741, hdfs-17897, hdfs-17899-bug1/2/3, hdfs-17967-pathA/B/C;
  - on HDFS-52 (1): hdfs-17960;
  - on its own site (1): hdfs-bugs-slowdisk-zero (RoundRobinVolumeChoosingPolicy:84).

**Removed (15):**
- 01, 17, 43: the seed never reaches the target (client polling and IBR waits; every DataNode's first heartbeat after the
  NameNode restart; truncate recovery waits);
- 02, 03, 04: client-local stream state or an ack timeout;
- 32: the block pool's removal runs in an actor thread started before the window, so no explored world reaches it;
- 36: no test;
- 41, 42, 44: request validation or file policy;
- 46, 47: format, fsimage load;
- 51, 53: debug dumps.

## Solr: 21 selected, 13 with an integration test, 20 executions

**Selected and run (13):** 05 07 09 10 13 14 19 21 22 31 38 39 40 (`experiments/solr/solr-adhoc/checks.tsv`; 22 is run as
solr-18406, the same throw).

**Selected without a run (8):**
- 01, 15, 16, 36, 37: no cluster test reaches the guard (37, DistributedZkUpdateProcessor:1003: the sub-shard range
  inside the parent's, weak coordination, added 2026-10-21);
- 06, 18, 34: a test evaluates the guard, but no counterfactual kind can flip it (no writer publishes a PULL leader; one
  znode version feeds both alias copies; the local CREATE waits on the same reader).

**Executions (20):**
- 12 study cases;
- 8 bug checks:
  - solr-18406 (on SOLR-22);
  - on their own sites (7): solr-18413, solr-bugs-reindex-cleanup, solr-bugs-migrate-buffer-leak,
    solr-bugs-overseer-lock-leak, solr-bugs-snapshot-no-active, solr-bugs-restore-construction,
    solr-bugs-tra-start-overwrite.

**Removed (19):** 02 03 04 08 11 12 17 20 23 24 25 26 27 28 29 30 32 33 35: no coordination (request validation, start-up
configuration, test hooks, local invariants, operator input) or an unreachable failure branch.

## HBase: 25 selected, 19 with an integration test, 22 executions

**Selected and run (19):** 04 07 08 10 11 12 13 14 15 19 20 21 22 24 28 31 34 35 37 (`experiments/hbase/hbase-adhoc/checks.tsv`,
on HBase master).
- 04 = HBASE-30484 and 22 = HBASE-30483.
- 04, 07, 22, 34 run our `TestCausynth*` versions of their tests.

**Selected without a run (6):** 16 (TransitRegionStateProcedure "Failed to close region": its test returns at CLOSED
before the guard), 17, 18 (TransitRegionStateProcedure abnormal close; repeated failed opens), 23 (ZKProcedureCoordinator
reached-znode data), 32 (RegionReplicaFlushHandler: a secondary replica's flush after the primary's flush RPC, added
2026-10-21), 33 (AuthenticationTokenSecretManager with an aborted ZKWatcher): no cluster test reaches the guard.

**Executions (22):**
- 19 study cases;
- 3 bug checks on their own sites: hbase-bugs-master-active-time, hbase-bugs-backup-lock-reply-lost,
  hbase-bugs-ns-rsgroup-removal (`results/hbase/`).

**Removed (13):**
- 03 05 06 09 25 26 36 38: no path, no coordination;
- 01, 02: the site no longer exists on master;
- 29, 30: request validation that no cluster test reaches on master;
- 27: a stop while the ZooKeeper tracker is null (timing only).

## ZooKeeper: 19 selected, 16 with an integration test, 16 executions

**Selected with an integration test (16):**
- the study points 01 02 03 04 06 07 10 11 12 13;
- the six bug points:
  - zk-bugs-trunc-sync (ZOOKEEPER-5094, PR 2459);
  - zk-bugs-observer-master (ZOOKEEPER-5088, PR 2454);
  - zk-bugs-quota-init;
  - zk-bugs-election-offer;
  - zk-bugs-container-reuse;
  - zk-bugs-retry-seq-quota.
- The three NoNode bugs share one throw, and the two quorum bugs share ZKDatabase:341; each bug is its own point because
  each is its own coordination path.
- `docs/checks/ZOOKEEPER.md` §E has the rows.

**Selected without a run (3):**
- 08, 09 (LearnerSessionTracker): no path;
- 05 (Follower:103, the leader's epoch below the accepted one, added 2026-10-21): its throw is dead on master. Learner:522
  throws first, and no other thread writes the accepted epoch.

**Executions (16):** one per point with a test (`experiments/zookeeper/zookeeper-cases.tsv`).
- 2 have run: quota-init and election-offer.
- The other 14 wait for the work in TODO "ZooKeeper".

**Removed:** none.
