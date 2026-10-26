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
  marker on `CoreContainer.create`'s throw. (afa0476204 made the collections the legacy way for the node-only world;
  reverted in 0df157b070, so the branch head is 3b70166099's content, the tree the case runs.)

## The workload

`org.apache.solr.cloud.TestCausynthMigrateLegacy#migrateUnderLegacyCloud` (two nodes,
TestCausynthMigrateBufferLeak's shape): it sets `legacyCloud=true` and waits until every node's reader holds it,
creates the source collection alone on node0 and the target alone on node1, indexes two documents of route key `a!`
into the source, migrates the key to the target, and asserts the two documents are on the target; it unsets
`legacyCloud` at the end. MIGRATE splits the key into a temporary collection on the source leader and creates that
collection's second replica on the target leader with the core-admin CREATE. In legacy mode the CREATE without a
`coreNodeName` is valid, so the MIGRATE succeeds natively; the bug is reached only in a world where the target node
reads `legacyCloud=false` at that core's creation.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("solr-adhoc-19,solr-buggy-6197")` on `CoreContainer.create`'s throw, `CoreContainer.java:1330` |
| the occurrence | `target_occurrence` in `case.sh` | `auto0/node1#epoch0/region/REGION.05d95c18-...#2`: the temporary collection's second replica, on the target leader (node1's #2; node1's #1 is the target collection's own core) |
| the config root | the program text | `CONFIG:legacyCloud==true`, a MARKER, the `Overseer.isLegacy` wrapper's return, one root for every read of it in the scope |
| scope | `case.sh` | `CoreContainer`, `MigrateCmd`, and the other readers of `legacyCloud` on the workload's path: `CreateCollectionCmd` (also MIGRATE's temporary collection), `AddReplicaCmd`, `ReplicaMutator`, `ZkController` (exact); not `Overseer` |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` |
| mechanism | `experiments/accept/report.py` | `solr-buggy-6197`: `MARKER_FLIPPED`, root `CONFIG:legacyCloud==true` to `false` |

Budget 21600 s. Why this scope, and why `Overseer` stays out: as solr-buggy-6101's README (the first run, S6197a,
UNSAT_CLOSED for the same reason: in the node-only world the target collection's own CREATE threw first, at node1's
#1).

## Native check of the bug's own world (scratch, not committed)

The workload with only its `legacyCloud=true` lines removed (`TestCausynthS2NoLegacyMigrate`, the cluster-wide
world): the fixed tree passes (5.3 s); `solr-bug-6197` fails, `Error CREATEing SolrCore
'split_shard1_temp_shard1_shard1_replica_n3': non legacy mode coreNodeName missing` -- the temporary collection's
replica on the target leader, solr-adhoc-19's own throw at `CoreContainer.java:1330`.

## Result

<!-- filled from the run S6197a -->
