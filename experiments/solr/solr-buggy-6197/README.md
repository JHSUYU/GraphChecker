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

`graphchecker/solr-checks` (12d23091d1) plus two commits:

- **The bug, by hand** (cb3a5be4b2): in `MigrateCmd.migrateKey`, the ADDREPLICA message and
  `AddReplicaCmd.addReplica(...)` for the temporary collection's second replica are replaced by a core-admin CREATE
  (today's core name from `Assign.buildSolrCoreName`, the temp collection, its shard) sent to the target leader's
  node through `asyncRequestTracker(asyncId)`, responses processed with the same error message -- the pre-fix shape.
  The imports only that block used (`HashMap`, `ADDREPLICA`) are removed.
- **The workload and the target** (3b70166099): `TestCausynthMigrateLegacy`, and `solr-buggy-6197` added to the
  marker on `CoreContainer.create`'s throw.
- **The collections made the legacy way** (afa0476204, the branch head and the tree the case runs): source and target
  each by one core-admin CREATE naming its `coreNodeName`, so the first CREATE without one on node1 is MIGRATE's.

## The workload

`org.apache.solr.cloud.TestCausynthMigrateLegacy#migrateUnderLegacyCloud` (two nodes, TestCausynthMigrateBufferLeak's
shape): it sets `legacyCloud=true` and waits until every node's reader holds it; makes the source collection on node0
and the target on node1 the legacy way (one core-admin CREATE each, naming `core_node1`); indexes two documents of
route key `a!` into the source, migrates the key to the target, and asserts the two documents are on the target; it
unsets `legacyCloud` at the end. MIGRATE splits the key into a temporary collection on the source leader and creates
that collection's second replica on the target leader with the put-back core-admin CREATE; in legacy mode it is valid,
so the MIGRATE succeeds natively (9.2 s).

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("solr-adhoc-19,solr-buggy-6197")` on `CoreContainer.create`'s throw, `CoreContainer.java:1330` |
| the occurrence | `target_occurrence` in `case.sh` | `auto0/node1#epoch0/region/REGION.05d95c18-...#2`: the temporary collection's second replica on the target leader (node1's #1 is the target's own core-admin create) |
| the config root | the program text | `CONFIG:legacyCloud==true`, a MARKER, minted at the `Overseer.isLegacy` return in `CoreContainer.create` (`#u51`) |
| scope | `case.sh` | `CoreContainer`, `MigrateCmd` |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` |
| mechanism | `experiments/accept/report.py` | `solr-buggy-6197`: `MARKER_FLIPPED`, root `CONFIG:legacyCloud==true` to `false` |

Budget 21600 s.

## Result: SAT in the node-only world, confirmed in the VM (S6197e) -- with a caveat

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

### The cluster-wide world: planned, not realized by today's runtime (S6197d)

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
