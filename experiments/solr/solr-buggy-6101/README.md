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

The fork branch is `graphchecker/solr-checks` (12d23091d1, the Solr 8.11 tree every check runs) plus:

- **The bug, by hand** (b0fffb0fcd): in `SplitShardCmd.split`'s `createSubSlicesAndLeadersInState` loop, the
  ADDREPLICA message and `ocmh.addReplica(...)` are replaced by a core-admin CREATE (name, collection, shard, the
  replica type, `addPropertyParams`) sent to the parent leader's node through one `asyncRequestTracker(asyncId)`,
  whose responses the block after the loop processes -- the pre-fix shape (`sendShardRequest` /
  `collectShardResponses`). The sub-shard's creation in the cluster state (CREATESHARD, `waitForNewShard`) and the
  extra sub-shard replicas (repFactor > 1) are unchanged: the fix's other hunks only routed those through ADDREPLICA
  too, and they are not needed to fire the point.
- **The workload and the target** (a4e7d3e0ba): `TestCausynthSplitShardLegacy`, and `solr-buggy-6101` added to the
  marker on `CoreContainer.create`'s throw (beside `solr-adhoc-19`).
- **The collection made the legacy way** (ea10a5b0a7): its one core created by a core-admin CREATE naming its
  `coreNodeName`, for the node-only world (S6101e below; there a Collections-API collection's own CREATE was refused
  first).
- **The workaround: legacyCloud field-backed** (fb0c5878b2, below): every read of `legacyCloud` through one field.
- **The collection through the Collections API again** (040ae6d4c6, the branch head and the tree S6101f runs):
  ea10a5b0a7 undone, the workload is a4e7d3e0ba's again. In the cluster-wide world `CreateCollectionCmd` takes its
  non-legacy branch and names the core's `coreNodeName`, so the first CREATE node0 refuses is the split's; a
  self-registering core-admin create would itself be refused there by non-legacy registration (`checkStateInZk`).

## The workaround: every read of `legacyCloud` through one field-backed value (fb0c5878b2)

`legacyCloud` was a getter-returned configuration: `Overseer.isLegacy` (`"true".equals(getClusterProperty("legacyCloud",
"false"))`) is a recognized wrapper, and a world moving it is planted only at a getter return that a *symbolic*
occurrence reads (`RootMint#materializePrimitive`): the node's `CoreContainer.create` read moved, the Overseer's reads
(`CreateCollectionCmd`, `AddReplicaCmd`, ...) kept the recording's legacy value (S6101d below). A configuration that a
*field* holds is different (SYMBOL-SCOPE §4.3): when every writer of an instance field stores one key's value in one
shape, the field's reads are declared (`EXACT_STATIC_CONFIG_READ_SITE_V1`), INSTRUMENT weaves
`ConcolicRegionRuntime.readConfiguration` before each, and `RootMint#configuration` writes the world's value into the
field at every read, in every thread, whatever occurrence runs it (a symbol is minted only where a symbolic occurrence
reads it; elsewhere the read is the world's value, concretely).

So the tree routes every read through one field (`// GraphChecker:` on each line):

- `org.apache.solr.cloud.CausynthLegacyCloud` (new): `isLegacy(ZkStateReader)` and `isLegacy(ClusterStateProvider)`
  each make a fresh holder, store `Overseer.isLegacy(...)` into its `boolean legacyCloud` and return that field.
- every caller of `Overseer.isLegacy` in solr-core calls it instead: on the node `CoreContainer.create` (the target
  guard at `:1328`; its `Overseer` import is swapped for this one, so no line of `CoreContainer` moves and the throw
  stays `:1330`) and `ZkController` (`register`, `publish`, `isPublishAsDownOnStartup`, `checkStateInZk`); on the
  Overseer `CreateCollectionCmd.call`, `AddReplicaCmd`, `OverseerCollectionMessageHandler.modifyCollection` and
  `ReplicaMutator.setState`.

Natively nothing changes: each call reads the cluster property exactly as before, at the same moment, and returns
that answer; the holder is local to the call (nothing shared, no lock, no ordering added). It is an instance field
because GraphChecker's configuration fields are instance fields only (`ConfigRoots#fieldValue` refuses a static one,
`CausynthPipeline#instrumentConfigurationRead` needs an `InstanceFieldRef`); none is needed for the cluster: the plant
is keyed by the field's signature, not by its owner, and a `MiniSolrCloudCluster` runs every node and the Overseer in
one JVM, so one world value reaches every read on every node. `Overseer` stays out of the scope, so `isLegacy` stays
the recognized wrapper whose return the field's two writers store (the getter call a writer stores is the field's own
read, never a concrete one), and the slice stops there (with `Overseer` in the scope it entered `isLegacy` and
`ZkStateReader.getClusterProperty`, an application class in every Solr case, and reached the parsed
`/clusterprops.json` map: S6101c).

The seed's scope map: `CONFIG_KEY CONFIG:legacyCloud==true`, `mintedAt <CausynthLegacyCloud: boolean legacyCloud>`,
`concreteReads []`; `root_demand.jsonl` chose the field (`CONFIG_FIELD`, distance 3); `CoreContainer.create`'s region
declares the field's read in `CausynthLegacyCloud.isLegacy` (and the two `isLegacy` methods are regions of their own,
the field's writers); the plan's three `CoreContainer.create` occurrences on node0 each carry five `legacyCloud`
read phases.

## The workload

`org.apache.solr.cloud.TestCausynthSplitShardLegacy#splitUnderLegacyCloud` (one node, SplitShardTest#doTest's shape):
it sets the cluster property `legacyCloud=true` and waits until every node's `ZkStateReader` holds it; creates a 1x1
collection through the Collections API, indexes four documents, splits `shard1`, waits for `activeClusterShape(2, 3)`,
asserts the four documents are in the sub-shards, and unsets `legacyCloud`. In legacy mode the split's core-admin
CREATE without a `coreNodeName` is valid, so the split succeeds natively (7.5 s on the tree set; 20/20 passes, below).
Solr 8.11's default is non-legacy (`Overseer.isLegacy` = `"true".equals(getClusterProperty("legacyCloud", "false"))`),
so the workload runs legacy for the put-back to pass natively. No workaround touches the bug or the fatal.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("solr-adhoc-19,solr-buggy-6101")` on `CoreContainer.create`'s throw, `CoreContainer.java:1330` |
| the occurrence | `target_occurrence` in `case.sh` | `auto0/node0#epoch0/region/REGION.05d95c18-...#2`: the first sub-shard leader's `CoreContainer.create` (#1, anchor `45db8fb77fc51b17`, is the collection's own core; #2 and #3 the split's two sub-shard leaders) |
| the config root | the program text (`causynth/ConfigRoots`) | `CONFIG:legacyCloud==true`, a MARKER, a configuration *field*: minted at the read of `CausynthLegacyCloud.legacyCloud`, whose writers store the `Overseer.isLegacy` wrapper's return; the world's value written at every read of the field |
| scope | `case.sh` | `CoreContainer`, `SplitShardCmd`, `CausynthLegacyCloud` (exact) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` (as solr-adhoc-19) |
| mechanism | `experiments/accept/report.py` | `solr-buggy-6101`: `MARKER_FLIPPED`, root `CONFIG:legacyCloud==true` to `false` (unchanged: the field's root has the wrapper's key and view) |

The Overseer-side callers (`CreateCollectionCmd`, `AddReplicaCmd`, ...) need not be in the scope for the world to
reach them: the plant is woven into `CausynthLegacyCloud`'s body, which they call. Left out, the formula is the
node-only runs' size (S6101d's larger scope ended in z3 timeouts); their reads are planted, concretely, never minted.
The run's budget is `solr-buggy-cases.tsv`'s 21600 s.

**Running it (liftlab):** START-HERE §3 (`CASES=solr-buggy-6101`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1`, the
snapshot `/u/vnr3ne/gc-run/bd-solr-1`, round B1: `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-solr-buggy-6101`). The
rounds below ran on CloudLab (2026-10-26); their `/bulk` paths were that cluster's and stay as the record. Liftlab:
B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 884 s (B1-solr-buggy-6101).

## Result: SAT in the bug's own cluster-wide world -- confirmed, reproduced natively 10/10, accepted (S6101g)

**Where it stands against the acceptance**: accepted -- CONFIRM yes, GraphChecker's native REPRODUCE **10/10** with
control **0/10**, `report.py` **PASS**, and the witness discriminates (cluster-wide). `configurationOnly` is a valid
world: `legacyCloud=false` is a value the cluster accepts (Solr 8.11's default), the bug report's own setting.

Round S6101g (2026-10-26, snapshot `/bulk/gc-run/solr-b6101-7` = GraphChecker 61e881776, tree set
`/bulk/trees/sb6101-3` = 040ae6d4c6, `/bulk/gc-out/solr-buggy/6101`): 1102 s, `SAT_CANDIDATE` `FINAL_READY`,
`MARKER_FLIPPED` at valuation 51 moving `CONFIG:legacyCloud==true` to `false`, `polarityDecides` true, no gap, no
defect, `cone.json` 0 unbound, BOUNDED by world depth 0 (876 task rounds cut, the declared bound), `configurationOnly`;
`report.py` **PASS**. FORCE: `FORCED_TARGET` at `create#u55#1`, ADMITTED.

- **CONFIRM**: the selected session `bdaacea3e6e80311-35ea79ae` is itself the run (every moved root at the model's
  value, the fatal observed at the declared anchor `944ad028333f2969`, node0 #2) -- the world S6101f confirmed (below):
  the Overseer's reads take the field's value too, the collection's CREATE carries `coreNodeName=core_node2`, and the
  split's bare core-admin CREATE is refused at `CoreContainer.java:1330`.
- **The chain** (`final/candidate.smt2`, two paths): the selected `path_fatal__0` is the door markers on the way
  unfired, `CFG = false` and the guard's `!isLegacy` arm (`CFG` = `M_Z_field_SRC.7ba8e801..._CausynthLegacyCloud`, the
  field read in `CausynthLegacyCloud.isLegacy` under `CoreContainer.create#u51`); `path_fatal__1` asks `CFG = true` and
  the same arm, a contradiction. `coreNodeName == null` is concrete (the put-back split's CREATE). Pinned at `true`:
  unsat (`polarityDecides`).
- **REPRODUCE: 10/10, control 0/10.** The plant (`final/reproduce/plant.jsonl`) is one ROOT row -- `CONFIG
  CONFIG:legacyCloud==true`, `field <org.apache.solr.cloud.CausynthLegacyCloud: boolean legacyCloud>`, `reads
  [<...CausynthLegacyCloud: boolean isLegacy(org.apache.solr.common.cloud.ZkStateReader)>#u5]`, `value false` -- and the
  TARGET row. The plant agent writes `false` into the field before the one GETFIELD of that planned method, at every
  execution in every thread (what `RootMint#configuration` does in the VM at the same plan site). In each planted run
  `PLANT_APPLIED` is stated first at the Overseer's read (`OVERSEER_TASK#1`, `CreateCollectionCmd`), the collection's
  CREATE carries `coreNodeName=core_node2`, and the split's bare CREATE of `causynthSplitLegacy_shard1_0_replica_n3`
  takes the fatal arm of `create#u55` at the declared anchor `944ad028333f2969` (`AT_ANCHOR`). The control runs plant
  nothing: every CREATE is legacy (no `coreNodeName`), all three cores are created and the workload passes.
- **Scope of the native plant, as in the VM**: the plan's only read site of the field is `isLegacy(ZkStateReader)#u5`;
  `isLegacy(ClusterStateProvider)` (called by `ReplicaMutator.setState`) is not a plan site, so it keeps its recorded
  value natively, as it did in CONFIRM (the VM weaves `readConfiguration` only at the plan's sites).
- **The engine support** (system/solr-buggy-detect only, reviewed): 61e881776 (ConfirmMain writes the field row from the
  plan's `configuredSourcePhases`; `RecordingPlant.fieldRead`; `PlantAgent` rewrites the planned GETFIELDs) and
  e5c894636 + ad3d08028 (review: a method is planted only when its GETFIELDs of the field are exactly its plan sites,
  else `PLANT_UNWRITTEN`; null owner; two roots on one field refused, and a root a getter also returns; the getter
  configSource lookup reverted). The g runs ran on a snapshot of 61e881776; their plant rows recomputed with
  e5c894636 and with ad3d08028 are byte-identical to what they planted, and the reviewed agent rewrites
  `CausynthLegacyCloud` the same way (fieldRead before the one GETFIELD of `isLegacy(ZkStateReader)`, nothing else), so
  the verdict stands under the reviewed engine.
- **It discriminates** (native, scratch, below): in this world the fixed split names its sub-shard replicas'
  `coreNodeName` and passes; only the put-back bare CREATE throws.

### Earlier: the same world before the native field plant (S6101f)

Round S6101f (2026-10-26, snapshot `/bulk/gc-run/solr-b6101-6` = GraphChecker 59ae37bfb, tree set
`/bulk/trees/sb6101-3` = 040ae6d4c6, `/bulk/gc-out/solr-buggy/6101`): 901 s, `SAT_CANDIDATE` `FINAL_READY`,
`MARKER_FLIPPED` at valuation 12 moving `CONFIG:legacyCloud==true` to `false`, `polarityDecides` true, no gap, no
defect, `cone.json` 0 unbound, BOUNDED by world depth 0 (57 task rounds cut, the declared bound), `configurationOnly`;
`report.py` **PASS**. FORCE: `FORCED_TARGET` at `create#u55#1`, and its forced flip `6d4b102b3889362b` -- the flip
S6101a and S6101d had NOT_ADMITTED ("the declared occurrence never reached") -- now **ADMITTED**.

- **CONFIRM**: the selected session `6d4b102b3889362b-17473dc2` is itself the run (every moved root at the model's
  value, the fatal observed at the declared anchor `944ad028333f2969`, node0 #2). The world is cluster-wide: the root
  is minted `false` at node0's three creates, and the Overseer's reads -- outside every planned occurrence ("fired under
  none": the field holds the world's value, concretely) -- read it too: `CreateCollectionCmd` took its non-legacy branch
  and the collection's CREATE carries `coreNodeName=core_node2` (the recording's carried none), so node0 accepts the
  collection's core (#1); then the split's bare core-admin CREATEs of `causynthSplitLegacy_shard1_0_replica_n3` and
  `_1_replica_n4` are refused, "non legacy mode coreNodeName missing" -- solr-adhoc-19's own throw at
  `CoreContainer.java:1330`.
- **The chain** (`final/candidate.smt2`, one path): `path_fatal__0` is the door markers on the way unfired, `CFG =
  false` and the guard's `!isLegacy` arm, where `CFG` (`M_Z_field_SRC.7ba8e801..._CausynthLegacyCloud`) is the
  configuration field read in `CausynthLegacyCloud.isLegacy` under `CoreContainer.create#u51`; `coreNodeName == null`
  (`#u55`) is concrete on the path (the CREATE comes from the put-back split). Pinned at its recorded `true`: unsat
  (`polarityDecides`).
- **It discriminates.** In this world the fixed split (ADDREPLICA, its Overseer read non-legacy too) names the
  sub-shard replicas' `coreNodeName` and passes; only the put-back bare CREATE throws (native, below). The node-only
  caveat of S6101e is gone.
- **REPRODUCE** (then): no native run -- `NATIVE_PLANT_UNSUPPORTED` ("minted at ... at [], called at []"): the native
  planter planted a configuration only at a getter call's return, and a root minted at a field's read has none
  (CHECKING trap 21); hence the engine support above and S6101g.

### Native checks outside the engine (scratch, `/bulk/trees/s6scratch`, runner `/bulk/analysis/buggy-detect-2026-10-26/solr-logs/s6/`)

Scratch worktrees of the committed trees (`bug6101` at 040ae6d4c6, `bug6197` at f5d86cbd8a, `fixed` at
`graphchecker/solr-checks` 12d23091d1 with the same `CausynthLegacyCloud` change applied uncommitted and both workloads
copied in); `run.sh`/`chain.sh` run each test by `ant test` with build.sh's flags; results in `s6/<tree>/results.txt`.

- **No behaviour change**: the workload on the buggy tree, legacyCloud=true, **20/20 PASS**, no refusal at `:1330`
  (the tree set's own build: PASSED 7.5 s).
- **The bug's world, legacyCloud=false as a cluster property** (`TestCausynthS6FalseSplit`: the workload with `"true"`
  set to `"false"`): `solr-bug-6101` **10/10 FAIL**, the split's `causynthSplitLegacy_shard1_0_replica_n3` /
  `_1_replica_n4` refused, "non legacy mode coreNodeName missing" (`CoreContainer.java:1330` in the cause); the fixed
  tree **10/10 PASS**.
- **GraphChecker's world, natively** (a scratch patch makes `CausynthLegacyCloud`'s field take
  `-Ds6.legacyCloud=false` at every read -- what `RootMint#configuration` does in the VM -- with the workload
  unchanged, legacyCloud=true set): `solr-bug-6101` **10/10 FAIL** at `:1330` (the same two cores); the fixed tree
  **10/10 PASS** (its collection's CREATE carries `core_node2`, the split's ADDREPLICAs `core_node5`/`core_node6`);
  control (no plant) the 20 runs above, **0/20**.

## Earlier: SAT in the node-only world, confirmed in the VM (S6101e) -- with a caveat

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

### The cluster-wide world with a getter-returned root: planned, not realized (S6101d; realized by the field, S6101f)

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
