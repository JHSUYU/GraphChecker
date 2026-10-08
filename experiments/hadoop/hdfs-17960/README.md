# HDFS-17960

## The bug

[Hadoop PR #8672](https://github.com/apache/hadoop/pull/8672). `SnapshotManager.deleteSnapshot`
decrements `numSnapshots` unconditionally after calling
`DirectorySnapshottableFeature.removeSnapshot`, and that call does not always remove
a snapshot. The workload records duplicate snapshot-deletion edits with ordered deletion
enabled, restarts the NameNode with ordered deletion disabled, then checkpoints. On the
restarted NameNode the second deletion record finds no such snapshot; with ordered deletion
off and the image not yet loaded, `removeSnapshot` takes its tolerance path and returns
without removing anything, while the counter is decremented all the same. Counter and
snapshot list then disagree and `saveNamespace` reaches the declared snapshot-count check
in `FSImageFormatPBSnapshot.Saver.serializeSnapshotSection`. The recording takes the healthy
arm, so the fatal predicate is concrete on the recorded path: the witness has to come from a
flipped decision, which is what makes this case the worked example for the whole design.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("hdfs-17960")` on the `throw new` at line 468, in the nested `Saver.serializeSnapshotSection` (the tree spells its `Preconditions.checkState(i == sm.getNumSnapshots())` as that if/throw); `run.sh` derives the spec from it |
| the occurrence | `target_occurrence` in `case.sh` | `hdfs-17960/nn0#epoch1/region/REGION.5cf88831-22cf-3d39-88b2-258261af8fc8#1` — the checkpoint RPC handler on the restarted NameNode. The target site sits in `serializeSnapshotSection`, whose own region (`REGION.f0132fca`) is entered synchronously from inside that handler and therefore opens no occurrence of its own: its sites are events of the enclosing one. The selector carries no `@api` part, so it is read as region plus node, and `#1` names the first of the two observed instances |
| roots | the checkout's hook | the one root is `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED`, minted by a `CausynthSymbolicSource.symbolize` hook in the checkout's own `SnapshotManager`, on the `dfs.namenode.snapshot.deletion.ordered` value the restarted NameNode caches. A hook site owns its field (`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED`), so the field is not listed here. The engine recognizes the field as configuration too (`causynth.ConfigRoots`: its one writer, the constructor, stores `conf.getBoolean` of that key), but a field a hook mints is the hook's, so SEED declares none of its reads; once the tree drops the hook the root is `CONFIG:dfs.namenode.snapshot.deletion.ordered` (SYMBOL-SCOPE §4.3) |
| region input | the static scope map (`inputKind: READ`) | `SnapshotManager.getNumSnapshots()` reads its `AtomicInteger` through a JDK accessor no replay versions, and other regions store it, so the read is a placeholder the closure binds to those writers -- the value the fatal predicate compares |
| root domains | no `root-domains.jsonl` | a `MARKER` root is free over both of its values without a domain row; every other value stands at its recording |
| wire mappings | `../communication-mappings.jsonl` (every HDFS case's one declaration) | none of its flows matters here: the divergence is local to one node |
| loop bounds | `loop-bounds.jsonl`: 31 rows, every one `loopBodyBound: 16`; `causynth_loop_default_bound=8` | the retained fsimage scan and edit-log replay loops. The default of 8 does not reach the duplicate deletion, which is why every retained site is declared at 16 |

## Build and run

Hadoop checkout: the HDFS tree `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r7`, branch `gc/hdfs-study-r7` (on `system/hdfs`; it descends from `gc/hdfs-unified-dtx`, the unified tree `gc/hdfs-unified`, trunk 734dd8a67cd, inventory `/bigtemp/vnr3ne/analysis/unify/hdfs-inventory.md`, plus the DataTransfer op's envelope). HDFS-17960's fix (PR #8672) is not in trunk, so the base has the
bug; the workload (`TestOrderedSnapshotDeletion#testOrderedDeletionWithRestart`) is the one
first written on the branch-3.4 tree `gc/hdfs-17960`, ported onto trunk's JUnit 5 file. From
this directory:

```bash
../../lib/run.sh . "" build        # installs the current GraphChecker API, builds the tree,
                      # runs the concrete workload test, refuses unless it alone passes
../../lib/run.sh . "" validate     # required workflow fields
../../lib/run.sh . "" campaign     # the whole campaign
```

Use a fresh `CAUSYNTH_OUTPUT_DIR` per campaign; the answer lands under `schedule/final`. The in-tree acceptance harness runs the same campaign and then probes and
reports it (`experiments/accept/README.md`):

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
CASES=hdfs-17960 bash experiments/accept/accept.sh
```

## What the harness expects

`report.py` passes this case only on `claim` `SAT_CANDIDATE`, `finalStatus` `FINAL_READY`,
empty `blockers` and no open BLOCKING gap, `polarityDecides` true, `valuationOrdinal` >= 1,
non-empty `movedRoots`, and `findingKind` `MARKER_FLIPPED` moving
`HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` to `false`.

## Status

PASS by mandate on `system/hdfs` (round HL1, MARKER_FLIPPED: `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` true -> false); its `.smt` read against the code: `docs/STATUS.md` "HDFS checks".
