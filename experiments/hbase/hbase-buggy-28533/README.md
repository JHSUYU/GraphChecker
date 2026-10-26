# HBASE-28533 put back (hbase-buggy-28533, point hbase-adhoc-15) -- stub: no case yet

## The bug

[HBASE-28533](https://issues.apache.org/jira/browse/HBASE-28533) (PR 5863, fix 8a2f3ef793, 2024):
`SplitTableRegionProcedure.prepareSplitRegion` sets the parent's `RegionStateNode` to SPLITTING; before the fix
`rollbackState(SPLIT_TABLE_REGION_PREPARE)` did nothing, so a split that failed in a later rollback-able step before it
closed the parent (the namespace region quota in SPLIT_TABLE_REGION_PRE_OPERATION, a coprocessor veto) left the master
believing an open parent was SPLITTING until a restart. The fix's `rollbackPrepareSplit` puts it back to OPEN.

Point hbase-adhoc-15: `MergeTableRegionsProcedure.prepareMergeRegion`'s `!state.isOpened()` for a parent ->
`MergeRegionException("Unable to merge regions that are NOT online")` (:507).

## What was put back, on graphchecker/hbase-bug-28533

de71623820 (from graphchecker/hbase-checks b5d5cc6a20): the PREPARE case is the empty `break; // nothing to do` again,
the fix's `rollbackPrepareSplit` (only that case called it) is deleted, and so is the fix's assertion (the parent OPEN
after the rollback) in `TestSplitTableRegionProcedure#testRollbackForSplitTableRegionWithReplica`. No workload yet.

## Finding: the study's chain does not reach :507 on the latest code

The study row (hbase.txt) reads: a split fails at its namespace quota, the pre-fix rollback leaves the parent SPLITTING,
"the next merge of that parent is refused at :507". On today's tree that merge is refused earlier, at another throw:

- `HMaster.mergeRegions` constructs the procedure inside its RPC handler's `NonceProcedureRunnable.run`
  (HMaster:2374, `new MergeTableRegionsProcedure(...)`).
- The constructor calls `checkRegionsToMerge` (MergeTableRegionsProcedure:106), which calls `checkOnline(env, ri)` for each
  parent (:149) -> `AbstractStateMachineTableProcedure.checkOnline` (:186-193) -> `RegionStateNode.checkOnline`:
  `if (s != State.OPEN) throw new DoNotRetryRegionException(... " is not OPEN; state=" + s)` (RegionStateNode:321-322),
  rethrown as a `MergeRegionException` (MergeTableRegionsProcedure:148-151).
- So a merge requested after the failed split fails in its constructor with "is not OPEN; state=SPLITTING": the same
  exception class as :507's, a different guarded throw, and no procedure is ever submitted, so `prepareMergeRegion`'s
  :507 does not run.
- The check came with HBASE-22777 (1b168cd6de, 2019-08-01). rel/2.6.6, the release the study read, has it too
  (`MergeTableRegionsProcedure.java` of tag rel/2.6.6 from GitHub: `checkRegionsToMerge(env, ...)` :107,
  `checkOnline(env, ri)` :150, `!state.isOpened()` :502).

:507 runs in the MERGE_TABLE_REGIONS_PREPARE step, under the merge's region locks (`waitRegions`, :406; `holdLock` true,
:426); the split holds the parent's lock for its whole life too (`waitRegions` :162, `holdLock` true in
AbstractStateMachineRegionProcedure:82). :507 therefore fires for this bug only when a merge is constructed while the
parent is still OPEN and is prepared after the split's rollback: built before the split's PREPARE sets SPLITTING
(SplitTableRegionProcedure:589 on this branch), queued behind the split's lock, prepared once the split has failed and
rolled back. With the fix the rollback restores OPEN and that merge goes through; with the bug it meets SPLITTING at
:507.

What a workload must then satisfy (to be decided after hbase-buggy-20642 and -15039, lead 2026-10-26):
- the split must not fail natively (the bug would be reached natively, its symptom the constructor refusal above), so
  its failure comes from a root;
- a merge constructed before a split that then succeeds is prepared on a SPLIT parent and also throws at :507, on the
  fixed code: point 15's own race, one re-pairing (the constructor's read before the SPLITTING write), not the bug. Any
  shape where the bug's world is reached from that one adds the split's failure as a second root, and EXPLORE meets the
  fixed-code witness first unless the split cannot succeed in any world.

## Result

None yet. If no workload keeps the bug necessary at :507 without being contrived, the case is recorded as: on the
latest code HBASE-28533 does not reach its point's own throw (the natural chain ends at the merge constructor's
checkOnline, RegionStateNode:322).
