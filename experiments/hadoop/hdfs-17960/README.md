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
snapshot list then disagree and `saveNamespace` reaches the annotated snapshot-count check
in `FSImageFormatPBSnapshot.Saver.serializeSnapshotSection`. The recording takes the healthy
arm, so the fatal predicate is concrete on the recorded path: the witness has to come from a
flipped decision, which is what makes this case the worked example for the whole design.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | `@CausynthExceptionTarget` on the constructed exception in the Hadoop checkout; `target.yaml` | `exception_target_id: hdfs-17960-snapshot-count-mismatch` |
| the occurrence | `declared_target_occurrence` in `workflow.properties` | `hdfs-17960/nn0#epoch1/region/REGION.f0132fca-8c1f-3f7c-93e7-dc41bfc20f40#1` |
| roots | none in `symbolic-inputs.jsonl` | the one root is `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED`, minted by a `CausynthSymbolicSource.symbolize` hook in the checkout's own `SnapshotManager`, on the `dfs.namenode.snapshot.deletion.ordered` value the restarted NameNode caches. A hook site owns its field (`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED`), so the field is not listed here |
| region input | `symbolic-inputs.jsonl`, one row | at `FSImageFormatPBSnapshot$Saver.serializeSnapshotSection`, the cell `<SnapshotManager: int getNumSnapshots()>.return` — the read whose value the fatal predicate compares |
| root domains | no `root-domains.jsonl` | a `MARKER` root is free over both of its values without a domain row; every other value stands at its recording |
| wire mappings | none (`causynth_communication_mappings` unset) | the divergence is local to one node, so the seed session has no exports and no attaches |
| loop bounds | `loop-bounds.jsonl`: 31 rows, every one `loopBodyBound: 16`; `causynth_loop_default_bound=8` | the retained fsimage scan and edit-log replay loops. The default of 8 does not reach the duplicate deletion, which is why every retained site is declared at 16 |

## Build and run

Hadoop checkout `/opt/hadoop-hdfs-17960-jdk8`, branch `gc/hdfs-17960-snapshot-replay-jdk8`,
compiled with Java 8. From this directory:

```bash
./run.sh build        # installs the current GraphChecker API, builds the tree,
                      # runs the concrete workload test, refuses unless it alone passes
./run.sh validate     # required workflow fields
./run.sh campaign     # the whole campaign
```

Use a fresh `CAUSYNTH_OUTPUT_DIR` per campaign; the epoch's answer lands under
`schedule/final`. The in-tree acceptance harness runs the same campaign and then probes and
reports it (`experiments/hadoop/accept/README.md`):

```bash
export CAUSYNTH_CUSTOM_JDK_HOME=/absolute/path/to/j2sdk-image
CASES=hdfs-17960 bash experiments/hadoop/accept/accept.sh
```

## What the harness expects

`report.py` passes this case only on `claim` `SAT_CANDIDATE`, `finalStatus` `FINAL_READY`,
empty `blockers` and no open BLOCKING gap, `polarityDecides` true, `valuationOrdinal` >= 1,
non-empty `movedRoots`, and `findingKind` `MARKER_FLIPPED` moving
`HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` to `false`.

## Status

Passes end to end under the current design. The committed artifacts of that run are under
`artifacts/` beside this file: `result.json` states `MARKER_FLIPPED` at `valuationOrdinal` 1
with `movedRoots {HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED: false}`, `polarityDecides true`,
`finalStatus FINAL_READY` and `gapCount` 0 (247 diagnostic rows). `valuations` records
ordinal 0 (`= true`, the run as it happened) `unsat` and ordinal 1 (`= false`) `sat`.

Running plain `z3 candidate.smt2` on the published file answers **unsat**, and that is not a
verdict about the case: the composer pins its own recorded valuation into the file it
publishes — `artifacts/candidate.smt2` ends with `(assert (! (= M_Z_field_SRC…SnapshotManager
true) :named valuation__…))` under the comment `; valuation 0: the run as it happened` — so a
plain run answers about that one valuation. `experiments/hadoop/accept/probe.sh` is what asks
the published formula unpinned, at the accepted assignment and at the other polarity — a
question about the whole formula rather than about the slice the campaign solved. It is
reported, never gated on.
