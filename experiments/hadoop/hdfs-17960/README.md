# HDFS-17960 campaign

This experiment detects the snapshot-count mismatch fixed by
[Hadoop PR #8672](https://github.com/apache/hadoop/pull/8672).
The workload creates the duplicate snapshot-deletion edit records through the
normal ordered-deletion path, restarts the NameNode, and then checkpoints the
namespace. The vulnerable implementation decrements `numSnapshots` even when
replay finds that the corresponding snapshot was already removed.

The workload follows the upstream reproduction: it records the deletion edits
with ordered deletion enabled, then restarts the NameNode with ordered deletion
disabled. The restarted NameNode caches that configuration value in
`SnapshotManager.snapshotDeletionOrdered`, and the production symbolic-source
hook publishes that boolean. Replay removes the same snapshot twice, leaving
the counter different from the actual snapshot list. `saveNamespace` then
reaches the annotated snapshot-count check in
`FSImageFormatPBSnapshot.Saver.serializeSnapshotSection`. The concolic summary
keeps the configuration value symbolic, and Z3 validates the `false` valuation
through the replay mutations to that target.

```text
ordered deletes -> duplicate edit records -> NameNode restart
                                            |
                                            +-> symbolic ordered=false
                                                -> duplicate removal
                                                -> count/list mismatch
                                                -> annotated check
```

No communication mapping is configured because the symbolic value and the
state divergence are local to the NameNode; request epochs and edit-log replay
remain represented by tracing. `symbolic-inputs.jsonl` explicitly selects the
target region's `AtomicInteger.value` read, allowing its recorded read-from
edge to bind the replay-produced counter value into the exception predicate.
`loop-bounds.jsonl` contains every exact loop site retained by the final
selected closure for this checkout, each with a bound of 16. In the baseline
trace the first deletion reaches replay iteration 8 and the duplicate deletion
reaches iteration 9, so the default bound of 8 cannot retain the complete state
transition.

The checked-in result contains the full causal witness. All five selected path
worklists are `CLOSED`; the final composition is `FINAL_READY` with zero gaps,
coverage gaps, telemetry gaps, and free symbols. Runtime exploration added 14
topology-delta rows with no divergence. Overlapping regions observed the same
physical configuration event, so the composer canonicalized their projections
to one Boolean root. Z3 reports `false` as SAT and `true` as UNSAT.

Edit-log operation dispatch is retained as an exact table-switch observation,
including the concrete case key and successor index. The two duplicate deletion
occurrences therefore remain distinct decisions in the path evidence instead
of collapsing to the same taken/not-taken bit.

For the SAT valuation, the selected replay case executes both duplicate
deletions. The two `AtomicInteger.getAndDecrement` versions carry the count
from 2 to 1 and then from 1 to 0. Exact read-from edges bind version 2 to the
target `getNumSnapshots()` read, while the snapshot-list enumeration remains
1. The final predicate is therefore `1 != 0`, which reaches the annotated
`IllegalStateException`. The explored `true` sibling case is closed, but it
does not produce the demanded second counter version and is consequently not
a valid causal witness for this target.

Hadoop checkout: `/opt/hadoop-hdfs-17960-jdk8`, branch
`gc/hdfs-17960-snapshot-replay-jdk8`, based on commit `6dd24f5815f25431e6eab58e7f16894d1446b708`
and compiled with Java 8. Run `./run.sh build`, `./run.sh validate`, and then
`./run.sh campaign` from this directory. Use a fresh
`CAUSYNTH_OUTPUT_DIR` for each campaign; final SMT and replay evidence are
written below `schedule/final`.

`artifacts/` preserves the successful campaign's `candidate.smt2`, compressed
composition manifest, path closures, topology deltas, final result, structured
Z3 result, and direct Z3 output. A plain `z3 artifacts/candidate.smt2` returns
`sat`.
