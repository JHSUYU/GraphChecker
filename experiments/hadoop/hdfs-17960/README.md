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
| the occurrence | `declared_target_occurrence` in `workflow.properties` | `hdfs-17960/nn0#epoch1/region/REGION.5cf88831-22cf-3d39-88b2-258261af8fc8#1` — the checkpoint RPC handler on the restarted NameNode. The target site sits in `serializeSnapshotSection`, whose own region (`REGION.f0132fca`) is entered synchronously from inside that handler and therefore opens no occurrence of its own: its sites are events of the enclosing one. The selector carries no `@api` part, so it is read as region plus node, and `#1` names the first of the two observed instances |
| roots | the checkout's hook | the one root is `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED`, minted by a `CausynthSymbolicSource.symbolize` hook in the checkout's own `SnapshotManager`, on the `dfs.namenode.snapshot.deletion.ordered` value the restarted NameNode caches. A hook site owns its field (`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED`), so the field is not listed here. The engine recognizes the field as configuration too (`causynth.ConfigRoots`: its one writer, the constructor, stores `conf.getBoolean` of that key), but a field a hook mints is the hook's, so SEED declares none of its reads; once the tree drops the hook the root is `CONFIG:dfs.namenode.snapshot.deletion.ordered` (SYMBOL-SCOPE §4.3) |
| region input | the static scope map (`inputKind: READ`) | `SnapshotManager.getNumSnapshots()` reads its `AtomicInteger` through a JDK accessor no replay versions, and other regions store it, so the read is a placeholder the closure binds to those writers -- the value the fatal predicate compares |
| root domains | no `root-domains.jsonl` | a `MARKER` root is free over both of its values without a domain row; every other value stands at its recording |
| wire mappings | none (`causynth_communication_mappings` unset) | the divergence is local to one node, so the seed session has no exports and no attaches |
| loop bounds | `loop-bounds.jsonl`: 31 rows, every one `loopBodyBound: 16`; `causynth_loop_default_bound=8` | the retained fsimage scan and edit-log replay loops. The default of 8 does not reach the duplicate deletion, which is why every retained site is declared at 16 |

## Build and run

Hadoop checkout: the HDFS tree `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx`, branch `gc/hdfs-unified-dtx` (the unified tree `gc/hdfs-unified`, trunk 734dd8a67cd, inventory `/bigtemp/vnr3ne/analysis/unify/hdfs-inventory.md`, plus the DataTransfer op's envelope). HDFS-17960's fix (PR #8672) is not in trunk, so the base has the
bug; the workload (`TestOrderedSnapshotDeletion#testOrderedDeletionWithRestart`) is the one
first written on the branch-3.4 tree `gc/hdfs-17960`, ported onto trunk's JUnit 5 file.
`artifacts/` records that older tree's paths: they are a frozen run's own provenance and are
not rewritten. From this directory:

```bash
../../lib/run.sh . "" build        # installs the current GraphChecker API, builds the tree,
                      # runs the concrete workload test, refuses unless it alone passes
../../lib/run.sh . "" validate     # required workflow fields
../../lib/run.sh . "" campaign     # the whole campaign
```

Use a fresh `CAUSYNTH_OUTPUT_DIR` per campaign; the epoch's answer lands under
`schedule/final`. The in-tree acceptance harness runs the same campaign and then probes and
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

Passes end to end. Campaign of 2026-09-21, four hosts, 190 s: `MARKER_FLIPPED` at
`valuationOrdinal` 1 with `movedRoots {HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED: false}`,
`polarityDecides true`, `finalStatus FINAL_READY`, no blocking gap, six solver runs.
Valuation 0 (`= true`, the run as it happened) is `unsat` and valuation 1 (`= false`) is `sat`
on the one admitted session, which observed the fatal arm. Exploration converged in two waves
over seven obligations; the admitted one is the flip of `isSnapshotDeletionOrdered()` at the
first duplicate deletion record, and its replay printed the corrupted state the workload
predicts for ordered deletion off, `snapshotListing=1 numSnapshots=0`.

The other three wave-0 obligations are refused correctly and are worth reading as a check on
the exploration rather than as noise. Two ask for one deletion to see ordered mode while a
later one does not, which no execution can do because both read the same configuration field
once; the third is the fatal branch itself, unsatisfiable while no session in the corpus
carries a different counter.

Four engine defects stood between the anchor re-declaration and that result, all of them
found here and all general rather than specific to this case:

1. **A loop body was refused by the rule for region entries.** A declared region entered inside
   a running occurrence opens none of its own, and that rule was being asked at a
   `LOOP_BODY_ROOT`'s body. Here `FSEditLogLoader.loadEditRecords` folds between the loop root
   in `FSNamesystem.loadFSImage` and the body hook inside it, so the innermost marker at the
   body belonged to another region and every body was refused. The edit-log replay occurrence
   never ran symbolically, the `isSnapshotDeletionOrdered` hook fired under no occurrence, no
   root was minted, and the run reported the root as never executing.
2. **Three filters dropped selection candidates in silence**, so a loop that certainly ran was
   reported as never executing and the refusal named nothing. They state their reason now, and
   that silence is what proved defect 1: with refusals speaking the run still reported zero
   refused candidates, which meant selection was never asked at all.
3. **Every loop body was asked whether the occurrence had taken the flip yet.** All bodies of a
   loop-body root publish at one occurrence address, so bodies that finish before the flipped
   ordinal answered "not yet" and were abandoned. That abandonment sets a sticky flag the
   end-of-run verdict consults first, so the session reported `NOT_ADMITTED` with an empty
   reason after a later body did take the flip.
4. **A mint that planted a root stated what it had observed rather than what it ran at.** The
   observation is the recording's own value, read before the wave's assignment is written, so
   the corpus stated one replay's root twice and differently and the composition refused the
   only witness this case has. A clock is untouched: it is asked as a skew on the run's own
   instant, and its reading is what the flip query floors and ceilings the cell by.

The committed artifacts under `artifacts/` beside this file are from an earlier run on an
earlier design and are kept as that run's own provenance. They agree with the campaign above on
everything the harness gates: `MARKER_FLIPPED`, ordinal 1, the same root moved to `false`,
`polarityDecides true`.

Running plain `z3 candidate.smt2` on the published file answers **unsat**, and that is not a
verdict about the case: the composer pins its own recorded valuation into the file it
publishes — `artifacts/candidate.smt2` ends with `(assert (! (= M_Z_field_SRC…SnapshotManager
true) :named valuation__…))` under the comment `; valuation 0: the run as it happened` — so a
plain run answers about that one valuation. `experiments/accept/probe.sh` is what asks
the published formula unpinned, at the accepted assignment and at the other polarity — a
question about the whole formula rather than about the slice the campaign solved. It is
reported, never gated on.
