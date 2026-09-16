# WIP: PC4 — the last of the static-graph residue

Base commit: `492280b46` (the `r3/PC3` branch tip, two staging merges back).
Contents: 2 commits (`0001`, `0002`) + `uncommitted.patch` (5 files, one of
them a deletion) + `status.txt`.
This was never a branch on the remote.

**Status in main.** Both commits are MERGED (`Merge r3/PC4 @f5cd60449`) —
mandate items 1 and 2. `uncommitted.patch` is NOT applied — it was mid-edit
when round 3 stopped, and it holds mandate items 3 and 4. Apply it with
`git apply uncommitted.patch`.

## The mandate

1. **PLAN's region-scoping walk is fed by DECLARED PORTS**
   (`DECLARED_SITE` + `declaredSiteCaptures`, `ROOT_SITE`, declared
   communication captures, the target) and moves on the candidate graph plus
   the scope map's stored cells.
   *The planner's ruling:* **retention is a scope fact.** Keep all 15
   activations of `REGION.16ba41cf` and all 63 of `REGION.1f6914ec`; raise
   11741's `region_path_max_tasks` to 256. 17960's 45 → 16 is accepted only
   after a **writer-coverage check**: no dropped occurrence holds a
   `WRITE_SITE` of a cell a retained occurrence reads.
2. Delete finalizer clusters **B / C / E**,
   `DependencyRole.CONCRETE_STRUCTURE_CARRIER`, and the CONCRETE rows.
3. Delete `RuntimeRefinedGraphBuilder`, `RECORD_FIELD` +
   `instrumentFieldTrace`, `trace.fields`, `refined_dataflow_edges.jsonl.gz`
   and the `run_engine` readers.
4. `SymbolizeAction.matchesLocal` keys on **(method, unit index)**, not the
   Soot local name; local cells are named by the **program variable**
   (`jb` `use-original-names` with the suffix stripped) so the static graph is
   a pure function of the workload. Soot's `LocalSplitter` names clones in
   identity-hash order, which is why the current naming is unstable.

## What the two merged commits did

* `0001` **The demand walk is fed by declarations, not by discovery.**
  Cluster A's failure closure took its ports from the recording's field
  accesses (cluster B) and moved on the pairs cluster C made of them
  (`RUNTIME_FIELD_FLOW`). Both are discovery: a read the campaign never
  declared mints no symbol — `ConcolicScheduler.SymbolicInputSelection` is the
  one admission rule — so an occurrence retained because such a read paired
  with some recorded write bought the plan a task that can publish no arm.
  The walk now seeds from the fatal branch's own operand cells at every
  observed target plus the declared cells of every occurrence admitted by a
  declaration, and moves by one backward walk over the candidate graph inside
  the occurrence, crossing to another occurrence exactly where the map says a
  location is STORED (`StaticScopeMap.writeSitesByCell`, new).
  Deleted with the rule they implemented: `admitSharedLocationWriters`,
  `admitWritersOfDemands`, `transitiveSharedLocationDemand`,
  `caredSharedLocations`, `requestFlowPrefixInputs`, `fatalPrefixCutoff`,
  `addRegionPathInputs`, `causalRegionRetentionEdge`.
  Measured: 17960 45 → 16 tasks, symbolize byte-identical; 11741 86 → 133
  tasks, symbolize 26 → 46; `REGION.1f6914ec` 23 → 63 and `REGION.16ba41cf`
  5 → 15 — the map names the REGIONS whose text stores a location, never which
  activation of one wrote it. 11741's `schedule_max_jobs` 128 → 256 (that is
  the cap the scheduler refused on; `region_path_max_tasks` bounds EXPLORE's
  wave closure and stays at 128). The 17960 writer-coverage check passed: all
  76 read rows belong to retained regions and every recorded writer of each
  read location is a retained region too.
* `0002` **Delete the discovered ports, their pairing and their carrier role.**
  Clusters B (470 lines), C (419) and E (375), plus `filterPorts`,
  `trimFatalPrefixAccesses`, `retainRuntimeAccesses`, `stampEdgeOccurrences`,
  `canonicalizeRegionEdges`, the whole port half of `RegionDemandIndex`,
  `ClosureWalk`'s three unreachable sets, `Result.regionEdges` and every
  consumer, `plan/AutomaticRegionEdge`,
  `DependencyRole.CONCRETE_STRUCTURE_CARRIER`, `DependencyRole.merge` and the
  carrier stamps. Published `inputActions` are now 100% SYMBOLIC /
  VALUE_FRONTIER (17960 4, 11741 46). `RuntimeSelectedRegionFinalizer`
  3702 → 1634 lines. Readers of every deleted published member were checked
  with `git grep` on the staging tip `0e3c1ab39` and on the in-flight branches
  `r3/C3` and `r3/FIX1`; no caller in either `/opt/hadoop-*` tree.
  **A plan artifact written before this change states a `DependencyRole` this
  engine has no meaning for; `normalize` refuses it by name and it is not a
  supported input.**

## What the uncommitted diff holds (items 3 and 4, in progress)

`CausynthPipeline`, `CausynthTraceRecorder`, `RuntimeRegionPlanner`,
`CanonicalJson`, and the deletion of
`runtime/RuntimeRefinedGraphBuilder.java` (1100 lines) — item 3, partly.
Item 4 (the `matchesLocal` key and the program-variable cell naming) is NOT
started. Read the diff before trusting it; it was never built or run.

## Consequence of item 4 not being done

`candidate_dataflow_edges.jsonl.gz` is **not yet a pure function of the
workload**. The known instability is exactly Soot local renaming: on 17960 the
file moves between runs with `rows=8833` both, no id gained or lost, and 6
`guard_dependency` rows in one method (`INodesInPath.resolvePath`) differing by
the single transposition `$z5 <-> $z6`, the `(kind,siteId)` multiset identical.
Until item 4 lands, compare that artifact with that normalization, not by hash.

## Definition of done

Apply, finish items 3 and 4, re-run the offline gate over both kept corpora,
and show `candidate_dataflow_edges.jsonl.gz` byte-identical across two runs.
