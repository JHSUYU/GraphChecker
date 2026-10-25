# HDFS-15590

## The bug

[HDFS-15590](https://issues.apache.org/jira/browse/HDFS-15590), "namenode fails to start when ordered snapshot deletion
feature is disabled" (fix 368f2f637e8, PR 2326, 2020). With `dfs.namenode.snapshot.deletion.ordered` on, deleting a
snapshot that is not the earliest only marks it deleted (today it is also renamed `<name>#<id>`) and logs
`OP_DELETE_SNAPSHOT <name>`; once it is the earliest, its real deletion (the ordered-deletion GC daemon's) logs a second
`OP_DELETE_SNAPSHOT`, for its renamed name. A NameNode restarted with ordered deletion off replays the first record as a
real deletion (`SnapshotManager.deleteSnapshot` -> `DirectorySnapshottableFeature.removeSnapshot`), finds nothing for the
second, and `removeSnapshot` throws `SnapshotException("Cannot delete snapshot ...: the snapshot does not exist.")` out of
`FSEditLogLoader.applyEditLogOp`: the NameNode does not start. The issue's stack is exactly this chain. The fix returns
`null` there when ordered deletion is off and the image is still loading.

The point is hdfs-adhoc-52 (`FSImageFormatPBSnapshot` :467-468, marked `hdfs-17960`): the same configuration across the
same restart. Behind the fix, that tolerance's `null` is what HDFS-17960's counter decrement then miscounts (the image
save's throw); with the bug put back, the replay throws first, at a different site: this case's target.

## What was put back, and the workload

The tree is `$GC_TREES/hadoop-hdfs-bug-15590`, the fork's `graphchecker/hdfs-bug-15590` (`graphchecker/hdfs-checks`
899c200cc8e plus two commits):

- **d9bc07f51e1, HDFS-15590 put back:** in `DirectorySnapshottableFeature.removeSnapshot`, the fix's
  `if (!snapshotManager.isSnapshotDeletionOrdered() && !snapshotManager.isImageLoaded()) return null;` (and its comment)
  is removed, so a snapshot not found throws again, as before the fix. Nothing else of the fix is touched:
  `SnapshotManager#isImageLoaded` is used by `checkSnapshotLimit` today, and the limit message and `TestSnapshotCommands`
  edits are not the bug.
- **f64cc697489, target and workload:** the throw is marked `@CausynthExceptionTarget("hdfs-buggy-15590")`;
  `TestOrderedSnapshotDeletion#testOrderedDeletionWithRestart` (the fix's regression test, in the shape hdfs-17960
  gave it: request brackets, sources `hdfs-17960/client` and `hdfs-17960/nn0` registered in `setUp`, the NameNode's
  epoch 1 at the restart) records the issue's sequence with ordered deletion on: snapshots s0 and s1; s1 deleted
  (marked, renamed `s1#<id>`); s0 deleted; `s1#<id>` deleted, as the GC daemon would delete it once it is the earliest,
  here on the request thread; then the NameNode restarts with ordered deletion on (the recorded value). Its replay marks
  and renames s1 at the first record and deletes s0 and `s1#<id>` through `removeSnapshot` at the second and third, which
  finds both: the workload passes natively (8.5 s, 11 edits replayed) and the target's guard (`i < 0`) is observed
  healthy at the second and third records. hdfs-17960's checkpoint after the restart is dropped (its target, not this
  one's). Natively with ordered deletion off at the restart (a scratch copy of the sequence, outside the tree) the
  NameNode does not start: `Cannot delete snapshot s1#1 from path /TestOrderedSnapshotDeletion: the snapshot does not
  exist.` at `removeSnapshot` <- `INodeDirectory.removeSnapshot` <- `SnapshotManager.deleteSnapshot` <-
  `FSEditLogLoader.applyEditLogOp` <- ... <- `FSNamesystem.loadFromDisk`, the issue's stack.
- **Workaround (named):** `setUp` sets the ordered-deletion GC daemon's period to a day, so no timer thread deletes a
  marked snapshot (and logs its `OP_DELETE_SNAPSHOT`) as a slow replay's timing falls. It changes no outcome: the
  workload makes that deletion itself.

Why not hdfs-17960's workload as it is: there s1 is deleted twice and s0 never, so under ordered deletion the restart's
replay never calls `removeSnapshot`, and the engine needs the target's guard observed at the declared occurrence in the
recording (SEED's `FATAL_TARGET_OBSERVATION_GAP`).

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("hdfs-buggy-15590")` on `removeSnapshot`'s `throw new SnapshotException("Cannot delete snapshot ...")`; `run.sh` derives the spec from it |
| the occurrence | `target_occurrence` in `case.sh` | `hdfs-17960/nn0#epoch1/region/REGION.9492ec77-0f65-34ba-a3af-14753ac7347d#2`: `SnapshotManager.deleteSnapshot` (`STATE_WRITER_ENTRY`) on the restarted NameNode, the second of its occurrences there to evaluate the target's guard, i.e. the replay of the third record (`s1#<id>`; the first record takes the rename arm in the recording and evaluates no guard). Resolved: `.../ctx:Root:CLIENT/restart-namenode#1/idx:...deleteSnapshot(...)@2` |
| roots | the checkout's hook | `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED`, minted by hdfs-17960's `CausynthSymbolicSource.symbolize` hook in `SnapshotManager.isSnapshotDeletionOrdered()` on the restarted NameNode's cached `snapshotDeletionOrdered` (a hook site owns its field) |
| scope | `case.sh` | hdfs-17960's without the classes that enclose the edit-log replay (`FSNamesystem`, `FSImage`, `FSEditLogLoader`) and its image save (`FSImageFormatProtobuf`, `FSImageFormatPBSnapshot`): no scoped region encloses `SnapshotManager.deleteSnapshot` on the restart's path, so each replayed `OP_DELETE_SNAPSHOT` is an occurrence of its own. Why: the anchor is the target guard's FIRST evaluation in the target occurrence (`RuntimeRegionPlanner#branches` selects occurrence 1 of a site; the session's target row is `removeSnapshot#u8#1`). With 17960's scope the whole replay is one occurrence (`FSNamesystem.loadFSImage`), and in the world with ordered deletion off the guard's first evaluation is the first record's (s1 found) and the throw its third: round B15590a's replay threw the target, yet no session observed the fatal at the anchor (UNSAT_CLOSED, below) |
| loop bounds, workflow | `loop-bounds.jsonl`, `workflow.properties` | hdfs-17960's rows for the classes still in scope (4 at 16) and its workflow (no comments) |
| wire mappings | `../communication-mappings.jsonl` | none matters: the divergence is local to the restarted NameNode |

## Result

**SAT, confirmed, reproduced 10/10 natively, report.py PASS** (round B15590b, 2026-10-25: snapshot
`/bulk/gc-run/hb15590-2` = 723e0f7d4, tree set `/bulk/trees/b15590` = fork f64cc697489, `GC_OUT=/bulk/gc-out/hdfs-buggy/15590`;
600 s: SEED 164, INSTRUMENT 109, REPLAY 113, EXPLORE 152, REPRODUCE 26). round-verify: `SAT_CANDIDATE end=(WITNESSED) z3=sat
moved=1 polarityDecides=True leaves=1 confirmed`, 0 BOUNDED / UNBOUND / HOLD; claim `MARKER_FLIPPED` at valuation 1 moving
`HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` true -> false; cone: the root in the selected path's cone, no unbound handoff;
REPRODUCE: 10 runs planted, 10 fatal at the anchor, control 10 runs 0 fatal.

The chain, read against the tree: the restarted NameNode's `SnapshotManager.snapshotDeletionOrdered` (the hook in
`isSnapshotDeletionOrdered()`, `SnapshotManager.java:196`) is false -> each replayed `OP_DELETE_SNAPSHOT`
(`FSEditLogLoader.java:822`) takes `deleteSnapshot`'s unordered arm (`SnapshotManager.java:516` false -> `:551`
`srcRoot.removeSnapshot`) -> the first record removes s1 and the second s0 from `snapshotsByNames`
(`DirectorySnapshottableFeature.java:259`) -> at the third, `searchSnapshot("s1#1")` (`:245`) finds nothing and
`if (i < 0)` (`:246`) throws the marked `SnapshotException` (`:247`). EXPLORE's one admitted flip was `deleteSnapshot#u7`
in the second record's occurrence with the root false (PLAN plans the three records' occurrences, two `createSnapshot`
replays and `setSnapshotCounter`; the session mints the root once, false, in the first record's occurrence, and the field
holds it for the later records); its replay threw at the third record's anchor
(`observedFatal` true, phi `true`), and CONFIRM took that session as the run. The formula has two paths: the witness
(the root false at its decisions, the fatal observed) and the seed (the root true, the fatal arm the binary search's
index over `snapshotsByNames`' states, `container_dag__*`: s0 and s1 added, s1 renamed, s0 removed), which no valuation
satisfies. The root is necessary: the file with the root pinned true is unsat, pinned false sat.

**Round B15590a** (snapshot `hb15590-1` = eb50a4ac5, hdfs-17960's scope): UNSAT_CLOSED in 525 s, though its flip of the
same decision (root false) replayed into the very throw: the restart's replay was one occurrence, the anchor the guard's
first evaluation there (`removeSnapshot#u8#1`), which in that world is the first record's healthy one; the throw was the
third. `compose.log`: "0 fatal-observing explored session(s)". Hence the scope above.
