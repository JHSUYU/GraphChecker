# SOLR-6101 put back (solr-buggy-6101, point solr-adhoc-19)

## The bug

[SOLR-6101](https://issues.apache.org/jira/browse/SOLR-6101) (fix 75b9821eb42, 2014): shard splitting fails when
`legacyCloud=false` is set as a cluster property. The Overseer's split created each sub-shard's first core with a
direct core-admin CREATE that carried no `coreNodeName`. That is valid only in *legacy* mode, where the receiving
node assigns the `coreNodeName` itself; under the non-legacy contract the Overseer must assign it first (write the
replica into the cluster state, pass its name on the CREATE). So with `legacyCloud=false` every SPLITSHARD failed at
the node's check. The fix makes the split create the sub-shard replicas through ADDREPLICA, which under non-legacy
writes the replica into state and passes `coreNodeName`.

Point solr-adhoc-19 (`docs/checks/SOLR.md`) is that node-side check: `CoreContainer.create`,
`!Overseer.isLegacy(zkStateReader) && cd.getCloudDescriptor().getCoreNodeName() == null`, throw
`CoreContainer.java:1330` "non legacy mode coreNodeName missing". The study's row names this bug as the CONFIG
mechanism of the point: flip `legacyCloud` to non-legacy and the split's CREATE hits this guard.

## What was put back, on graphchecker/solr-bug-6101

The fork branch is `graphchecker/solr-checks` (12d23091d1, the Solr 8.11 tree every check runs) plus two commits:

- **The bug, by hand** (b0fffb0fcd): in `SplitShardCmd.split`'s `createSubSlicesAndLeadersInState` loop, the
  ADDREPLICA message and `ocmh.addReplica(...)` are replaced by a core-admin CREATE (name, collection, shard, the
  replica type, `addPropertyParams`) sent to the parent leader's node through one `asyncRequestTracker(asyncId)`,
  whose responses the block after the loop processes -- the pre-fix shape (`sendShardRequest` /
  `collectShardResponses`). The sub-shard's creation in the cluster state (CREATESHARD, `waitForNewShard`) and the
  extra sub-shard replicas (repFactor > 1) are unchanged: the fix's other hunks only routed those through ADDREPLICA
  too, and they are not needed to fire the point.
- **The workload and the target** (a4e7d3e0ba): `TestCausynthSplitShardLegacy`, and `solr-buggy-6101` added to the
  marker on `CoreContainer.create`'s throw (beside `solr-adhoc-19`). (ea10a5b0a7 made the collection the legacy way
  for the node-only world; reverted in 35e71c92f0, so the branch head is a4e7d3e0ba's content, the tree the case runs.)

## The workload

`org.apache.solr.cloud.TestCausynthSplitShardLegacy#splitUnderLegacyCloud` (one node, SplitShardTest#doTest's shape):
it sets the cluster property `legacyCloud=true`, waits until every node's `ZkStateReader` holds it, creates a 1x1
collection, indexes four documents, splits `shard1`, waits for `activeClusterShape(2, 3)`, and asserts the four
documents are in the sub-shards; it unsets `legacyCloud` at the end. In legacy mode the split's core-admin CREATE
without a `coreNodeName` is valid, so the split succeeds natively. Solr 8.11's default is non-legacy
(`Overseer.isLegacy` = `"true".equals(getClusterProperty(LEGACY_CLOUD, "false"))`), so the workload has to run with
`legacyCloud=true` for the put-back to pass natively; the bug is reached only in a world GraphChecker builds, where
the node reads `legacyCloud=false` at the sub-shard core's creation.

No workaround changes the fatal outcome; the bug is the upstream bug.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("solr-adhoc-19,solr-buggy-6101")` on `CoreContainer.create`'s throw, `CoreContainer.java:1330` |
| the occurrence | `target_occurrence` in `case.sh` | `auto0/node0#epoch0/region/REGION.05d95c18-...#2`: the first sub-shard leader's `CoreContainer.create` (the seed's #1 is the collection's own core, under OVERSEER_TASK#1; #2 and #3 the split's two sub-shard leaders, under OVERSEER_TASK#2) |
| the config root | the program text (`causynth/ConfigRoots`) | `CONFIG:legacyCloud==true`, a MARKER: the `Overseer.isLegacy` wrapper's return (`"true".equals(getClusterProperty("legacyCloud", "false"))`), one root for every read of it in the scope |
| scope | `case.sh` | `CoreContainer`, `SplitShardCmd`, and the other readers of `legacyCloud` on the workload's path: `CreateCollectionCmd`, `AddReplicaCmd`, `ReplicaMutator`, `ZkController` (exact) -- but not `Overseer` (see below) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` (as solr-adhoc-19) |
| mechanism | `experiments/accept/report.py` | `solr-buggy-6101`: `MARKER_FLIPPED`, root `CONFIG:legacyCloud==true` to `false` |

The run's budget is `solr-buggy-cases.tsv`'s 21600 s.

### Why this scope: the flip must be the whole cluster's (the bug's own world)

A configuration root is planted where it is minted, at every read of it a symbolic occurrence makes; a read outside
the analysed scope keeps its recorded value. The first scope (`CoreContainer` + `SplitShardCmd`, run S6101a) minted
`legacyCloud` at `CoreContainer.create` alone, so a world planting `false` moved the node while the Overseer stayed
legacy -- and in that world the collection's own CREATE (`CreateCollectionCmd`'s legacy path, no `coreNodeName`)
threw first, at node0's #1, so the split never ran (UNSAT_CLOSED: every path's fatal arm needs the root `false`,
every admitted path ran it `true`, and the one flip that ran it `false` never reached the declared occurrence). That
node-only world is also the fixed code's (its split's ADDREPLICA, legacy on the Overseer, sends no `coreNodeName`
either), so it could not tell the bug apart anyway. With the Overseer side's readers in the scope the root is one,
planted on both sides (seed S6101scope3: no concrete read; the plan carries it at `CoreContainer.create#u51`,
`ZkController.register#u21`, `checkStateInZk#u3`, ... and `CreateCollectionCmd.call#u95`): `legacyCloud=false`
for the whole cluster, where the fixed split assigns a `coreNodeName` through ADDREPLICA and passes and only the
bug's bare CREATE throws. `Overseer` itself stays out: with its class in the scope, `isLegacy`'s body is analysed,
the guard's value is traced inside it to `ZkStateReader.clusterProperties` (the parsed `/clusterprops.json`), no
site declares the configuration input, and the plans carry no `legacyCloud` root (runs S6101c/S6197c, stopped at
their plans). The only `isLegacy` reader outside this scope, `OverseerCollectionMessageHandler:645`
(MODIFYCOLLECTION), is not on the workload's path. (Tried and dropped on the way: making the collection the legacy
way, a core-admin CREATE naming its `coreNodeName`, so the node-only world survives #1 -- non-legacy mode refuses
such a self-registering core in the cluster-wide world, and the node-only world is the fixed code's too.)

## Native check of the bug's own world (scratch, not committed)

The workload with only its `legacyCloud=true` lines removed (`TestCausynthS2NoLegacySplit`, every read sees the
default, non-legacy -- the cluster-wide world), on the two trees (`/bulk/trees/s2scratch`): the fixed tree passes
(6.4 s); `solr-bug-6101` fails, the node logging `Error CREATEing SolrCore 'causynthSplitLegacy_shard1_0_replica_n3':
non legacy mode coreNodeName missing` (and `_shard1_1_replica_n4`) -- solr-adhoc-19's own throw at
`CoreContainer.java:1330`.

## Result

<!-- filled from the run S6101a -->
