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
- **The collection made the legacy way** (ea10a5b0a7, the branch head and the tree the case runs): its one core is
  created by a core-admin CREATE naming its `coreNodeName`, so the first CREATE without one on node0 is the split's
  (below, "the first run").

## The workload

`org.apache.solr.cloud.TestCausynthSplitShardLegacy#splitUnderLegacyCloud` (one node, SplitShardTest#doTest's shape):
it sets the cluster property `legacyCloud=true` and waits until every node's `ZkStateReader` holds it; makes a 1x1
collection the legacy way (one core-admin CREATE of `causynthSplitLegacy_shard1_replica_n1` naming `core_node1`, which
the node registers into the cluster state); indexes four documents, splits `shard1`, waits for
`activeClusterShape(2, 3)`, asserts the four documents are in the sub-shards, and unsets `legacyCloud`. In legacy mode
the split's core-admin CREATE without a `coreNodeName` is valid, so the split succeeds natively (7.6 s). Solr 8.11's
default is non-legacy (`Overseer.isLegacy` = `"true".equals(getClusterProperty("legacyCloud", "false"))`), so the
workload runs legacy for the put-back to pass natively. No workaround touches the bug or the fatal.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("solr-adhoc-19,solr-buggy-6101")` on `CoreContainer.create`'s throw, `CoreContainer.java:1330` |
| the occurrence | `target_occurrence` in `case.sh` | `auto0/node0#epoch0/region/REGION.05d95c18-...#2`: the first sub-shard leader's `CoreContainer.create` (the seed's #1 is the collection's own core-admin create; #2 and #3 the split's two sub-shard leaders, under OVERSEER_TASK#1) |
| the config root | the program text (`causynth/ConfigRoots`) | `CONFIG:legacyCloud==true`, a MARKER, minted at the `Overseer.isLegacy` wrapper's return in `CoreContainer.create` (`#u51`; `Overseer` is outside the scope, so its return is the frontier) |
| scope | `case.sh` | `CoreContainer`, `SplitShardCmd` |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` (as solr-adhoc-19) |
| mechanism | `experiments/accept/report.py` | `solr-buggy-6101`: `MARKER_FLIPPED`, root `CONFIG:legacyCloud==true` to `false` |

The run's budget is `solr-buggy-cases.tsv`'s 21600 s.

## Result: SAT in the node-only world, confirmed in the VM (S6101e) -- with a caveat

Round S6101e (2026-10-26, snapshot `/bulk/gc-run/solr-b6101-3` = GraphChecker abc3e8ec9, tree set
`/bulk/trees/sb6101-2` = ea10a5b0a7, `/bulk/gc-out/solr-buggy/6101`): 519 s, `SAT_CANDIDATE` `FINAL_READY`,
`MARKER_FLIPPED` at valuation 1 moving `CONFIG:legacyCloud==true` to `false`, `polarityDecides` true, no gap, no
defect, nothing bounded, `cone.json` unbound empty; `report.py` **PASS**.

- **CONFIRM**: the selected session `a3537682e3d9e19d-50d8600e` is itself the run (every moved root at the model's
  value, the fatal observed at the declared anchor). In it the root is planted `false` at node0's two sub-shard
  creates; the split's bare core-admin CREATEs of `causynthSplitLegacy_shard1_0_replica_n3` and `_1_replica_n4` are
  refused, "non legacy mode coreNodeName missing" -- solr-adhoc-19's own throw at `CoreContainer.java:1330`.
- **The chain** (the selected path in `final/candidate.smt2`): `path_fatal__0` is `CFG = false` and the guard's
  `!isLegacy` arm, where `CFG` is the configuration cell (`M_Z_field_SRC.7ba8e801...`, the `isLegacy` return read at
  `CoreContainer.create#u51`); the guard's other conjunct, `cd.getCloudDescriptor().getCoreNodeName() == null`
  (`#u55`), is a concrete decision on this path: the CREATE comes from the put-back split, which sets no
  `coreNodeName`. With the root pinned at its recorded `true` the formula is unsat (`polarityDecides`).
- **REPRODUCE**: no native run -- `NATIVE_PLANT_UNSUPPORTED`: the root's mint row names its occurrence but no getter call
  site ("at [], called at []"), so the native planter cannot place this getter-returned configuration. Instead a
  scratch reproduction of the witness world (not committed; `/bulk/trees/s2scratch`, runner
  `/bulk/analysis/buggy-detect-2026-10-26/solr-logs/nodeonly/nodeonly.sh`): a scratch patch makes
  `CoreContainer.create` read non-legacy on one named node, set by the test right before SPLITSHARD
  (`TestCausynthS2NodeOnlySplit`, otherwise this workload), every other read staying legacy -- the world CONFIRM ran.
  On `solr-bug-6101`: **10/10** planted runs fail with `Error CREATEing SolrCore
  'causynthSplitLegacy_shard1_0_replica_n3'` (and `_shard1_1_replica_n4`) `: non legacy mode coreNodeName missing` at
  `CoreContainer.java:1330`; control (no plant) **0/3** (all pass).
- **Caveat: the fixed code also throws in this world.** It is the node-only world: the node reads `legacyCloud=false`
  while the Overseer keeps its recorded legacy reads (they are outside the scope). There the fixed split's ADDREPLICA,
  legacy on the Overseer, also sends no `coreNodeName`, and the node refuses it: the same scratch reproduction on the fixed tree
  fails **10/10** (`causynthSplitLegacy_shard1_0_replica_n3` refused at `:1330`), control 0/3 -- the
  same class as solr-adhoc-19's own node/Overseer disagreement, and as the accepted HDFS adhoc-11 and ZooKeeper cases
  where the fixed code reaches the throw in the witness world.
- **The bug's own world -- only the buggy tree throws** (native, scratch): the workload with its `legacyCloud=true`
  lines removed (`TestCausynthS2NoLegacySplit` on the Collections-API workload, every read non-legacy, the whole
  cluster): the fixed tree passes (6.4 s); `solr-bug-6101` fails, `Error CREATEing SolrCore
  'causynthSplitLegacy_shard1_0_replica_n3': non legacy mode coreNodeName missing` (and `_shard1_1_replica_n4`).

### The cluster-wide world: planned, not realized by today's runtime (S6101d)

To get the discriminating world inside GraphChecker, the readers of `legacyCloud` on both sides were put in the scope
(GraphChecker ddcf7acaa: `CreateCollectionCmd`, `AddReplicaCmd`, `ReplicaMutator`, `ZkController`, with the
Collections-API workload a4e7d3e0ba). The root stays one, with no concrete read, and the plan carries it SYMBOLIC on
node0's creates and on the Overseer's `CreateCollectionCmd.call` (`#u95`). S6101d (snapshot `solr-b6101-5`) ended
`RUN_DEFECT` (z3 did not decide the whole formula; two obligations `SOLVER_TIMEOUT` at 1800 s): in the legacyCloud=false
replay (forced flip `6d4b102b3889362b`, `rootAssignments {CONFIG:legacyCloud==true: false}`) the root was minted once,
at node0's first create, and never at `CreateCollectionCmd#u95`, so the Overseer read its recorded legacy value, the
collection's CREATE carried no `coreNodeName`, and node0 refused it before the split ran. A field-read configuration
is written at every read in every occurrence (`RootMint.configuration`); a getter-returned one is planted only where a
symbolic read mints, so the Overseer's read stays at the recording. With `Overseer` itself in the scope the root
disappears (its body is analysed and the value is traced into `ZkStateReader.clusterProperties`, the HELD JSON leaf
solr-adhoc-19 had): runs S6101c, stopped at their plans. An engine change to plant a getter config at every return
was considered and not made (lead, 2026-10-26).

### The first run (S6101a, UNSAT_CLOSED)

Same declaration, Collections-API workload (a4e7d3e0ba): `UNSAT_CLOSED` in 1219 s. Every path's fatal arm needs the
root `false`, every admitted path ran it `true`; the one replay that ran `false` (forced flip `6d4b102b3889362b`)
threw at node0's #1, the collection's own CREATE (`CreateCollectionCmd`'s legacy path, no `coreNodeName`, while the
node read non-legacy), so the declared occurrence was never reached. Hence the legacy-way collection (ea10a5b0a7).
