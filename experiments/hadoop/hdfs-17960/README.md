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
hook publishes that boolean. Replay removes the snapshot *once*: the second
deletion record finds no such snapshot, and because ordered deletion is now
off and the image is not yet loaded, `DirectorySnapshottableFeature.removeSnapshot`
takes its tolerance path and returns without removing anything instead of
throwing. `SnapshotManager.deleteSnapshot` decrements `numSnapshots`
unconditionally after that call, so the counter is decremented twice for one
removal and ends up different from the actual snapshot list. `saveNamespace` then
reaches the annotated snapshot-count check in
`FSImageFormatPBSnapshot.Saver.serializeSnapshotSection`. The concolic summary
keeps the configuration value symbolic, and Z3 validates the `false` valuation
through the replay mutations to that target.

```text
ordered deletes -> duplicate edit records -> NameNode restart
                                            |
                                            +-> symbolic ordered=false
                                                -> second removal tolerated,
                                                   counter still decremented
                                                -> count/list mismatch
                                                -> annotated check
```

No communication mapping is configured because the symbolic value and the
state divergence are local to the NameNode; request epochs and edit-log replay
remain represented by tracing. The production hook makes the ordered-deletion
configuration an explicit Boolean root, and it is the only root this case
varies: `symbolic-inputs.jsonl` names no root at all, which admits no
automatic candidate while leaving the hook's own field -- the one authority
an allowlist does not govern -- exactly where it is. Everything else stands
at its recorded value.

The target's `AtomicInteger.value` read receives a bounded GuardedRead over
the retained counter expressions from the custom JDK: its arms are the two
`getAndDecrement` writers, and which arm the witness takes is what the
configuration root decides. Its consumer anchor and write-candidate selectors
carry the chosen expression and its local path condition directly into the
exception predicate.

That family is the shared carrier's rather than a minted root's, but it does
not survive the read being concretized: a `CONCRETE` action is never
symbolized, so the VM publishes no candidates and there is nothing to admit.
A campaign on an allowlist that named nothing measured it -- 25 active
observed tasks became 1, 94 consumer-boundary families became 2, 46 guarded
reads became 0, and the composer emitted `configuredSourceMaterializations:
[]`, so the configuration root itself was missing from `candidate.smt2`. The
file therefore declares the counter as a **carrier**
(`carrierFieldSignatures`): the read stays symbolic so its candidates keep
being published, and it is never stamped a declared root, so it mints
nothing. One root, and it is the configuration's.
`loop-bounds.jsonl` contains every exact loop site retained by the final
selected closure for this checkout, each with a bound of 16. In the baseline
trace the first deletion reaches replay iteration 8 and the duplicate deletion
reaches iteration 9, so the default bound of 8 cannot retain the complete state
transition.

A successful fresh campaign publishes all observed region paths and
consumer-anchor families on one immutable global-wave snapshot. `FINAL_READY`
is a verdict about the emitted candidate formula, not about the witness being
tied to the root: unobserved sibling paths are coverage telemetry only while
the SOLVE stage reports no degeneracy. When it does -- and on this case
`BooleanReachConditionExtractor` still reports
`DEGENERATE_UNCONSTRAINED_ROOT_SPACE`, with both valuations SAT -- the sibling
cases are what the witness is escaping through, so `FINAL_READY` licenses no
claim about the root and the gap has to be closed first. Claiming closed UNSAT
additionally requires complete propagation, GuardedRead, path, and topology
coverage. The explicit source observations
give overlapping views of the physical configuration event one Boolean
identity. Z3 should report
`false` as SAT and `true` as UNSAT.

Edit-log operation dispatch is retained as an exact table-switch observation,
including the concrete case key and successor index. The two duplicate deletion
occurrences therefore remain distinct decisions in the path evidence instead
of collapsing to the same taken/not-taken bit.

For the SAT valuation, the selected replay case executes both duplicate
deletions. The two `AtomicInteger.getAndDecrement` versions carry the count
from 2 to 1 and then from 1 to 0. The target `getNumSnapshots()` GuardedRead has
an arm for version 2 and anchors that expression, while the snapshot-list
enumeration remains 1. The final predicate is therefore `1 != 0`, which reaches
the annotated `IllegalStateException`. The explored `true` sibling case is
closed, but it does not contain the required second counter version and is not
a valid causal witness for this target.

Hadoop checkout: `/opt/hadoop-hdfs-17960-jdk8`, branch
`gc/hdfs-17960-snapshot-replay-jdk8`, based on commit `6dd24f5815f25431e6eab58e7f16894d1446b708`
and compiled with Java 8. Run `./run.sh build`, `./run.sh validate`, and then
`./run.sh campaign` from this directory. Use a fresh
`CAUSYNTH_OUTPUT_DIR` for each campaign; final SMT and replay evidence are
written below `schedule/final`.

The campaign writes `candidate.smt2`, its composition manifest, path closures,
topology deltas, final result, and structured Z3 result below its fresh output
directory. A plain `z3 schedule/final/candidate.smt2` returns `sat`.
