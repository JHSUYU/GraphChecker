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
  marker on `CoreContainer.create`'s throw (beside `solr-adhoc-19`).

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
| the occurrence | `target_occurrence` in `case.sh` | `auto0/node0#epoch0/region/REGION.05d95c18-...#2`: the first sub-shard leader's `CoreContainer.create` (the seed's #1 is the collection's own core; #2 and #3 are the two sub-shard leaders) |
| the config root | the program text (`causynth/ConfigRoots`) | `CONFIG:legacyCloud==true`, a MARKER, minted at the `Overseer.isLegacy` wrapper's call in `CoreContainer.create` (`#u51`); flipping it to `false` makes the node non-legacy |
| scope | `case.sh` | `CoreContainer`, `SplitShardCmd` (Overseer out: its own `isLegacy` reads are a library body, read concretely) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` (as solr-adhoc-19) |
| mechanism | `experiments/accept/report.py` | `solr-buggy-6101`: `MARKER_FLIPPED`, root `CONFIG:legacyCloud==true` to `false` |

The run's budget is `solr-buggy-cases.tsv`'s 21600 s.

## Native check of the bug's own world (scratch, not committed)

`TestCausynthS2Scratch#splitWithoutLegacy` (the split with `legacyCloud` unset, i.e. non-legacy) on the two trees
(`/bulk/trees/s2scratch`): on the fixed tree the split succeeds; on `solr-bug-6101` it fails, and the node logs
`Error CREATEing SolrCore 's2split_shard1_0_replica_n3': non legacy mode coreNodeName missing` -- solr-adhoc-19's
own throw at `CoreContainer.java:1330`. So the bug fires the point's own throw in the non-legacy world.

## Result

<!-- filled from the run S6101a -->
