# SOLR-6197 put back (solr-buggy-6197, point solr-adhoc-19)

## The bug

[SOLR-6197](https://issues.apache.org/jira/browse/SOLR-6197) (fix 54b11b3eba9, 2014): the MIGRATE collection API
fails when `legacyCloud=false`. The same mismatch as SOLR-6101, in the MIGRATE command: `migrateKey` created the
temporary collection's second replica (on the target shard leader's node) with a direct core-admin CREATE carrying
no `coreNodeName`, valid only in legacy mode. With `legacyCloud=false` the node requires the Overseer to assign the
name, so every MIGRATE failed at the node's check. The fix creates that replica through ADDREPLICA.

Point solr-adhoc-19 is the node-side check `CoreContainer.create`, `CoreContainer.java:1330` "non legacy mode
coreNodeName missing"; the study's row names this bug (and SOLR-6101) as the point's CONFIG mechanism.

## What was put back, on graphchecker/solr-bug-6197

`graphchecker/solr-checks` (12d23091d1) plus:

- **The bug, by hand** (cb3a5be4b2): in `MigrateCmd.migrateKey`, the ADDREPLICA message and
  `AddReplicaCmd.addReplica(...)` for the temporary collection's second replica are replaced by a core-admin CREATE
  (today's core name from `Assign.buildSolrCoreName`, the temp collection, its shard) sent to the target leader's
  node through `asyncRequestTracker(asyncId)`, responses processed with the same error message -- the pre-fix shape.
  The imports only that block used (`HashMap`, `ADDREPLICA`) are removed.
- **The workload and the target** (3b70166099): `TestCausynthMigrateLegacy`, and `solr-buggy-6197` added to the
  marker on `CoreContainer.create`'s throw.
- **The collections made the legacy way** (afa0476204): source and target each by one core-admin CREATE naming its
  `coreNodeName`, for the node-only world (S6197e below).
- **The workaround: legacyCloud field-backed** (da4cea38b8, the same change as solr-buggy-6101's fb0c5878b2, below).
- **The collections through the Collections API again** (f5d86cbd8a, the branch head and the tree S6197f runs):
  afa0476204 undone, the workload is 3b70166099's again. In the cluster-wide world `CreateCollectionCmd` names each
  core's `coreNodeName` (source, target, and MIGRATE's temporary collection's first core), so the first CREATE refused
  is MIGRATE's bare one on the target node.

## The workaround: every read of `legacyCloud` through one field-backed value (da4cea38b8)

`legacyCloud` was a getter-returned configuration: `Overseer.isLegacy` (`"true".equals(getClusterProperty("legacyCloud",
"false"))`) is a recognized wrapper, and a world moving it is planted only at a getter return that a *symbolic*
occurrence reads (`RootMint#materializePrimitive`): the node's `CoreContainer.create` read moved, the Overseer's reads
(`CreateCollectionCmd`, `AddReplicaCmd`, ...) kept the recording's legacy value (S6197d below). A configuration
that a *field* holds is different (SYMBOL-SCOPE §4.3): when every writer of an instance field stores one key's value in one
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
`/clusterprops.json` map: solr-buggy-6101's S6101c).

The seed's scope map: `CONFIG_KEY CONFIG:legacyCloud==true`, `mintedAt <CausynthLegacyCloud: boolean legacyCloud>`,
`concreteReads []`; `root_demand.jsonl` chose the field (`CONFIG_FIELD`, distance 3); `CoreContainer.create`'s region
declares the field's read in `CausynthLegacyCloud.isLegacy` (and the two `isLegacy` methods are regions of their own,
the field's writers); the plan's two `CoreContainer.create` occurrences on node1 carry the field's read phases.

## The workload

`org.apache.solr.cloud.TestCausynthMigrateLegacy#migrateUnderLegacyCloud` (two nodes, TestCausynthMigrateBufferLeak's
shape): it sets `legacyCloud=true` and waits until every node's reader holds it; creates the source collection on
node0 and the target on node1 through the Collections API (`createNodeSet`); indexes two documents of route key `a!`
into the source, migrates the key to the target, and asserts the two documents are on the target; it unsets
`legacyCloud` at the end. MIGRATE splits the key into a temporary collection on the source leader and creates that
collection's second replica on the target leader with the put-back core-admin CREATE; in legacy mode it is valid, so
the MIGRATE succeeds natively (9.3 s on the tree set; 20/20 passes, below).

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("solr-adhoc-19,solr-buggy-6197")` on `CoreContainer.create`'s throw, `CoreContainer.java:1330` |
| the occurrence | `target_occurrence` in `case.sh` | `auto0/node1#epoch0/region/REGION.05d95c18-...#2`: the temporary collection's second replica on the target leader (node1's #1, anchor `645b4104ac357824`, is the target collection's own core) |
| the config root | the program text | `CONFIG:legacyCloud==true`, a MARKER, a configuration *field*: minted at the read of `CausynthLegacyCloud.legacyCloud`, whose writers store the `Overseer.isLegacy` wrapper's return; the world's value written at every read of the field |
| scope | `case.sh` | `CoreContainer`, `MigrateCmd`, `CausynthLegacyCloud` (exact) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` |
| mechanism | `experiments/accept/report.py` | `solr-buggy-6197`: `MARKER_FLIPPED`, root `CONFIG:legacyCloud==true` to `false` |

The Overseer-side callers need not be in the scope for the world to reach them (the plant is woven into
`CausynthLegacyCloud`'s body, which they call); left out, the formula is the node-only runs' size. Budget 21600 s.

**Running it (liftlab):** START-HERE §3 (`CASES=solr-buggy-6197`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1`, the
snapshot `/u/vnr3ne/gc-run/bd-solr-1`, round B1: `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-solr-buggy-6197`). The
rounds below ran on CloudLab (2026-10-26); their `/bulk` paths were that cluster's and stay as the record. Liftlab:
B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 988 s (B1-solr-buggy-6197).

## Result: SAT in the bug's own cluster-wide world -- confirmed, reproduced natively 10/10, accepted (S6197g)

**Where it stands against the acceptance**: accepted -- CONFIRM yes, GraphChecker's native REPRODUCE **10/10** with
control **0/10**, `report.py` **PASS**, and the witness discriminates (cluster-wide). `configurationOnly` is a valid
world: `legacyCloud=false` is a value the cluster accepts (Solr 8.11's default), the bug report's own setting.

Round S6197g (2026-10-26, snapshot `/bulk/gc-run/solr-b6197-7` = GraphChecker 61e881776, tree set
`/bulk/trees/sb6197-3` = f5d86cbd8a, `/bulk/gc-out/solr-buggy/6197`): 754 s, `SAT_CANDIDATE` `FINAL_READY`,
`MARKER_FLIPPED` at valuation 24 moving `CONFIG:legacyCloud==true` to `false`, `polarityDecides` true, no gap, no
defect, `cone.json` 0 unbound, BOUNDED by world depth 0 (25 task rounds cut, the declared bound), `configurationOnly`;
`report.py` **PASS**.

- **CONFIRM**: the selected session `a5972cb95766e3f7-ad44c55a` is itself the run (the fatal at the declared anchor
  `14f38ae6f4a636b4`, node1 #2) -- the world S6197f confirmed (below): the Overseer's reads take the field's value, the
  three collections' CREATEs carry `coreNodeName=core_node2`, and MIGRATE's bare CREATE of
  `split_shard1_temp_shard1_shard1_replica_n3` on node1 is refused at `CoreContainer.java:1330`.
- **The chain** (`final/candidate.smt2`, one path): `path_fatal__0` is the door markers on the way unfired, `CFG =
  false` and the guard's `!isLegacy` arm (`CFG` the field read in `CausynthLegacyCloud.isLegacy` under node1's
  `CoreContainer.create#u51`); `coreNodeName == null` is concrete (the put-back MIGRATE's CREATE). Pinned at `true`:
  unsat.
- **REPRODUCE: 10/10, control 0/10.** The plant is one ROOT row -- `CONFIG CONFIG:legacyCloud==true`, `field
  <org.apache.solr.cloud.CausynthLegacyCloud: boolean legacyCloud>`, `reads [<...CausynthLegacyCloud: boolean
  isLegacy(org.apache.solr.common.cloud.ZkStateReader)>#u5]`, `value false` -- and the TARGET row. The plant agent
  writes `false` into the field before the one GETFIELD of that planned method, at every execution in every thread (as
  `RootMint#configuration` does in the VM at the same plan site). In each planted run `PLANT_APPLIED` is stated first at
  the Overseer's read (`OVERSEER_TASK#1`), the source's, the target's and the temporary collection's CREATEs carry
  `coreNodeName=core_node2`, and MIGRATE's bare CREATE of `split_shard1_temp_shard1_shard1_replica_n3` takes the fatal
  arm of `create#u55` at the declared anchor `14f38ae6f4a636b4` on node1 (`AT_ANCHOR`). The control runs plant nothing:
  every CREATE is legacy and the workload passes.
- **Scope of the native plant, as in the VM**: the plan's only read site of the field is `isLegacy(ZkStateReader)#u5`;
  `isLegacy(ClusterStateProvider)` (called by `ReplicaMutator.setState`) is not a plan site, so it keeps its recorded
  value natively, as it did in CONFIRM.
- **The engine support** (reviewed): 61e881776, e5c894636 and ad3d08028, as solr-buggy-6101 says. The run used a
  snapshot of 61e881776; its plant rows recomputed with e5c894636 and ad3d08028 are byte-identical to what it planted,
  and the reviewed agent rewrites `CausynthLegacyCloud` the same way, so the verdict stands under the reviewed engine.
- **It discriminates** (native, scratch, below): in this world the fixed MIGRATE (ADDREPLICA, non-legacy on the
  Overseer) names the replica's `coreNodeName` and passes; only the put-back bare CREATE throws.

### Earlier: the same world before the native field plant (S6197f)

Round S6197f (2026-10-26, snapshot `/bulk/gc-run/solr-b6197-6` = GraphChecker 59ae37bfb, tree set
`/bulk/trees/sb6197-3` = f5d86cbd8a, `/bulk/gc-out/solr-buggy/6197`): 724 s, `SAT_CANDIDATE` `FINAL_READY`,
`MARKER_FLIPPED` at valuation 27 moving `CONFIG:legacyCloud==true` to `false`, `polarityDecides` true, no gap, no
defect, `cone.json` 0 unbound, BOUNDED by world depth 0 (20 task rounds cut, the declared bound), `configurationOnly`;
`report.py` **PASS**.

- **CONFIRM**: the selected session `a5972cb95766e3f7-5be11088` is itself the run (the fatal at the declared anchor
  `14f38ae6f4a636b4`, node1 #2). The world is cluster-wide: the root is minted `false` at node1's two creates and the
  Overseer's reads, outside every planned occurrence, read it too -- `CreateCollectionCmd` took its non-legacy branch
  for all three collections, whose CREATEs carry `coreNodeName=core_node2` (the source's on node0, the target's on
  node1, MIGRATE's temporary collection's first core on node0; the recording's carried none), so every one is accepted;
  then MIGRATE's bare core-admin CREATE of `split_shard1_temp_shard1_shard1_replica_n3` on node1 is refused, "non
  legacy mode coreNodeName missing" -- solr-adhoc-19's own throw at `CoreContainer.java:1330`.
- **The chain** (`final/candidate.smt2`, one path): `path_fatal__0` is the door markers on the way unfired, `CFG =
  false` and the guard's `!isLegacy` arm (`CFG` the configuration field read in `CausynthLegacyCloud.isLegacy` under
  node1's `CoreContainer.create#u51`); `coreNodeName == null` is concrete (the CREATE comes from the put-back MIGRATE).
  Pinned at `true`: unsat.
- **It discriminates.** In this world the fixed MIGRATE (ADDREPLICA, non-legacy on the Overseer) names the replica's
  `coreNodeName` and passes; only the put-back bare CREATE throws (native, below). The node-only caveat of S6197e is
  gone.
- **REPRODUCE** (then): no native run -- `NATIVE_PLANT_UNSUPPORTED` (a root minted at a field's read had no native
  planter; CHECKING trap 21); hence the engine support above and S6197g.

### Native checks outside the engine (scratch, `/bulk/trees/s6scratch`, runner `/bulk/analysis/buggy-detect-2026-10-26/solr-logs/s6/`)

Scratch worktrees of the committed trees (`bug6101` at 040ae6d4c6, `bug6197` at f5d86cbd8a, `fixed` at
`graphchecker/solr-checks` 12d23091d1 with the same `CausynthLegacyCloud` change applied uncommitted and both workloads
copied in); `run.sh`/`chain.sh` run each test by `ant test` with build.sh's flags; results in `s6/<tree>/results.txt`.

- **No behaviour change**: the workload on the buggy tree, legacyCloud=true, **20/20 PASS**, no refusal at `:1330`
  (the tree set's own build: PASSED 9.3 s).
- **The bug's world, legacyCloud=false as a cluster property** (`TestCausynthS6FalseMigrate`): `solr-bug-6197` **10/10
  FAIL**, `split_shard1_temp_shard1_shard1_replica_n3` refused, "non legacy mode coreNodeName missing"
  (`CoreContainer.java:1330` in the cause); the fixed tree **10/10 PASS**.
- **GraphChecker's world, natively** (the scratch `-Ds6.legacyCloud=false` plant at every read of
  `CausynthLegacyCloud`'s field, workload unchanged): `solr-bug-6197` **10/10 FAIL** at `:1330`; the fixed tree
  **10/10 PASS**; control (no plant) the 20 runs above, **0/20**.

## Earlier: SAT in the node-only world, confirmed in the VM (S6197e) -- with a caveat

Round S6197e (2026-10-26, snapshot `/bulk/gc-run/solr-b6197-3` = GraphChecker abc3e8ec9, tree set
`/bulk/trees/sb6197-2` = afa0476204, `/bulk/gc-out/solr-buggy/6197`): 710 s, `SAT_CANDIDATE` `FINAL_READY`,
`MARKER_FLIPPED` at valuation 32 moving `CONFIG:legacyCloud==true` to `false`, `polarityDecides` true, no gap, no
defect, `cone.json` unbound empty, BOUNDED by world depth 0 (216 task rounds cut, the declared bound); `report.py`
**PASS**.

- **CONFIRM**: the selected session `9da6b55c62251bc4-107cab43` is itself the run. The root is planted `false` at node1's
  create only; the temporary collection's first core on node0 (legacy, unplanted) is created, then MIGRATE's bare
  core-admin CREATE of `split_shard1_temp_shard1_shard1_replica_n3` on node1 is refused, "non legacy mode coreNodeName
  missing" -- at the declared anchor.
- **The chain**: `path_fatal__0` is `CFG = false` and the guard's `!isLegacy` arm (the `isLegacy` return at
  `CoreContainer.create#u51` on node1); the `coreNodeName == null` conjunct is concrete on this path (the CREATE comes
  from the put-back MIGRATE). The other path ran legacy and is contradictory. Pinned at `true`: unsat.
- **REPRODUCE**: no native run (`NATIVE_PLANT_UNSUPPORTED`, as solr-buggy-6101: no getter call site on the mint row).
  Scratch reproduction of the witness world (`TestCausynthS2NodeOnlyMigrate`: non-legacy on node1 only, set right
  before MIGRATE): on `solr-bug-6197` **10/10** planted runs fail with `Error CREATEing SolrCore
  'split_shard1_temp_shard1_shard1_replica_n3': non legacy mode coreNodeName missing` at `CoreContainer.java:1330`;
  control **0/3** (all pass).
- **Caveat: the fixed code also throws in this world** (the Overseer stays legacy, so the fixed MIGRATE's ADDREPLICA
  sends no `coreNodeName` either): the same scratch reproduction on the fixed tree fails **10/10**
  (`split_shard1_temp_shard1_shard1_replica_n3` refused at `:1330`), control 0/3 -- the same class as the accepted HDFS
  adhoc-11 and ZooKeeper cases.
- **The bug's own world -- only the buggy tree throws** (native, scratch, `TestCausynthS2NoLegacyMigrate`, every read
  non-legacy): the fixed tree passes (5.3 s); `solr-bug-6197` fails, `Error CREATEing SolrCore
  'split_shard1_temp_shard1_shard1_replica_n3': non legacy mode coreNodeName missing`.

### The cluster-wide world with a getter-returned root: planned, not realized (S6197d; realized by the field, S6197f)

As solr-buggy-6101 (GraphChecker ddcf7acaa, Collections-API workload 3b70166099): S6197d (2471 s) ended `RUN_DEFECT`
(formula UNSAT_CLOSED plus one BLOCKING `ADMISSION_GAP`, an Overseer state-update create no session ran). The plan
carried the root on node1's creates, `ZkController.publish`, `MigrateCmd.call` and one `CreateCollectionCmd.call`
occurrence (the source's); in the legacyCloud=false replay (forced flip `a737b54a4004b1be`) the source's CREATE carried
`coreNodeName=core_node2` but the target collection's `CreateCollectionCmd` (not planned) stayed legacy, and node1
refused `causynthMigrateLegacy-target_shard1_replica_n1` before MIGRATE ran. A getter-returned configuration is planted
only where a symbolic read mints; no engine change was made (lead, 2026-10-26).

### The first run (S6197a, UNSAT_CLOSED)

Same declaration, Collections-API workload: `UNSAT_CLOSED` in 1256 s; the one replay running legacyCloud=false threw
at node1's #1, the target collection's own CREATE. Hence the legacy-way collections (afa0476204).
