# CLAUDE.md

Automatic bounded concolic pipeline that synthesises an SMT witness for a
distributed-systems fault from a passing workload, and checks it with Z3.
HDFS-11741 is the case it is developed against; the engine carries no
knowledge of it.

## Build

```bash
mvn -o package -DskipTests
```

**Never `mvn clean`.** Recordings used to live under `target/`; the work root
is now `experiments-output/`, but the habit is still worth keeping.

## Run

```bash
HADOOP_REPO=/opt/hadoop \
HDFS11741_REGION_JOBS=$(nproc) HDFS11741_PATH_JOBS=$(nproc) \
HDFS11741_CONCOLIC_HEAP=8g HDFS11741_ENGINE_WAIT_MS=1200000 \
  experiments/hdfs/hdfs-11741/run.sh candidates
```

**Run the campaigns and the flips wide.** Each is its own JVM, so they share
nothing that would contend: the single symbolic engine is contended *inside* a
JVM, between activations on different threads, and never across them. Measured
peak resident per concolic JVM is about 1 GB. Serialising them is a debugging
posture — useful when a failure has to be attributable, expensive once it is —
and leaving it on afterwards silently costs hours.

`HDFS11741_ENGINE_WAIT_MS` matters: one symbolic engine serves the JVM, and a
losing activation has to outlast the winner discovering it contradicts the
recording. 60s is not enough for this workload; 1200s is.

## Pipeline

```
record ──► refine/plan ──► seed campaigns ──► path closure ──► compose ──► Z3
(trace)    (closure)       (one JVM each)     (flip + replay)  (SMT)
```

| Stage | Produces | Invalidated by |
|---|---|---|
| record | `runtime/` trace (GB) | instrumentation changes |
| refine/plan | `analysis/`, `schedule/` | closure/planner changes |
| seed campaign | `seed-results`, `seed-summaries` | runtime capture changes |
| path closure | `path-state/`, `merged_summary` | merge/planner changes |
| compose | `candidates/**/candidate.smt2` | composer changes |

Invalidate the narrowest layer that the change touches, and **everything below
it** — a stale `path-iteration-*` makes the next replay refuse to overwrite its
own output, and a half-built campaign directory fails closed on reuse.

That last one bites on every retry: a campaign that failed leaves a directory
without `seed-results.jsonl`, and `prepare_seed_campaign` refuses it rather
than rebuilding. Rerunning without deleting those directories first prints
`invalid seed campaign preparation state` once each and **never runs those
campaigns at all** — a whole round that looks like it reproduced the failure
while having executed nothing. `rm -rf` the failed task directories under
`campaigns/auto-seeds/producer/`, after saving any `hs_err_pid*.log` worth
keeping.

## Core design

**Target-first demanded closure.** The fatal target's backward closure decides
what is analysed; nothing outside it is explored.

**Region template × owner is the logical unit.** One template activating twice
is *one* summary instantiated at two exact ports by alpha-renaming, never two
summaries. `logicalInstanceCount` and `summaryReuseKey` carry this.

**Replay identity is semantic, not ordinal.** A flip is matched by its path
seed — the vector of branch decisions (`RuntimeRegionPlanner.assignPathSeedKeys`)
— so a valuation solved in one JVM binds to the corresponding activation in
another where invocation counts differ. Recorded call ids are provenance only.
Mismatch fails closed (`PATH_SEED_MISMATCH`, `REPLAY_NOT_ADMITTED`); a near
match is never substituted, because a solution not bound to the path it was
solved for means nothing.

**Two ledgers, not one.** The unroll bound (8) is charged only to
symbolically-guarded loops, because only those explode the path space. Service
loops are charged to a separate replay resource cap. Confusing them either
cuts real paths or lets a replay run forever.

**Versions and selections are different indices.** One output boundary can
publish several versions of a port; each becomes one guarded relation case.
`outputOccurrence` answers "which mutation inside this definition invocation"
and restarts per invocation; `outputVersionOrdinal` answers "which version of
this port" and runs across the boundary. Neither is replay identity.

**Fail closed, and name the gap.** Anything unproven becomes an explicit gap,
never a silent assumption. But a gap is charged to *itself*: a flip that cannot
be explored is abandoned and recorded, it does not fail the run.

**Bounded means bounded in paths, not in cost.** A replay is bounded in which
paths it may walk; what those paths cost to keep resident is not bounded, so a
replay can end before publishing. That is an exploration gap.

**A bound must not become an event in the workload.** A cut at a symbolically
guarded loop was raised as an exception, escaped the region, and failed a live
RPC — so a queue the analysis was watching never drained, and a guard reading
that queue disagreed with the recording on five hundred consecutive
activations. The analysis had changed the run it was measuring, and the
symptom looked like an ordinary replay divergence. Whatever a cut does, the
program around it must proceed as though the analysis were not there.

**Every shadow states its ownership.** For each shadow the engine holds, it
must be decidable whether the engine *owns* it, *claims* it, or merely
*observed* it. The crashes that cost this project its longest rounds were all
confusions of these three: an array's shadow reinterpreted as an instance's
(identity), a slot aliasing an expression it never ref-counted (ownership),
and a frameless fast path that skipped interception entirely (observation
coverage). A new symbolic feature declares which of the three it does before
it touches a shadow.

**What needs no runtime evidence is checked at planning time.** A flip
contract contradicting its own seed, a demanded port kind with no capture
path — both are decidable from the plan alone, and both were discovered after
the replay they doom. The planning-time check admits when it cannot decide
and never replaces the late check; it exists so a doomed unit of work costs
seconds, not a campaign.

**Artifacts outgrow their readers.** A captured expression tree reaches
hundreds of MB nested past jq's tree-parser depth limit. Gates read the two
top-level fields they need off a stream (`jsonl_stream_field`) and address
rows by line. A tool that cannot read its own output reports a correct result
as a failure — the most expensive kind of bug here, because it is
indistinguishable from a semantic one.

## Acceptance

A bounded candidate witness is the deliverable. State it as *"within this
bounded model and these freedoms, the fatal branch is reachable"* — never as
proof the bug occurs. Both error directions exist and must be reported
together:

- freedoms too wide → **SAT may be false** (unconstrained producers)
- paths too few → **UNSAT may be false** (bounds are an under-approximation)

Degenerate SAT is not success, but neither field that once stated it means
what it looks like. `reachCondition.formula` disjoins over Boolean roots
alone, so with none of those it reads `"true"` by arity; `valuations[].values`
is one entry per Boolean root, so empty is arity again. Both are silent on
whether anything was constrained. The verdict lives in
`reachCondition.degeneracyCheck`, computed from the root space itself: a
space that refused a valuation is constrained, one enumerated whole and never
refused is degenerate, and an unenumerated one says so. Only the constrained
side is provable from one direction, so degeneracy is claimed only where the
space was really covered. Never accept the existential witness as evidence of
constraint — those values are the solver naming freedoms it was handed, so a
long list of them argues the opposite. `expiryDate` plausibility is **not**
checked at this stage.

A third degeneracy hides better than either, because every structural check
passes: the fatal condition is asserted, the formula is not `true`, the
regions are all present — and the value the condition turns on is a free
leaf. A witness that reads *"some integer is absent from this table"* names
no producer for that integer, so nothing else in the model has to hold. The
check is per-symbol, not per-artifact: **for the operands of the fatal
condition, find the assertion that binds each one.** A symbol whose only
assertion is its own type range is unconstrained, whatever else surrounds
it. A region inside the closure is not evidence that any value it computes
reached the query.

The audit for the dropped-evidence variant is mechanical: for each
unconstrained operand, search the validated runtime edges for a `CONFIRMED`
edge that could have bound it. Finding one is a named gap, never silence —
evidence that was proven and then dropped is worse than evidence never
found, because `gaps: 0` over it is a false report.

## Method vs case

**The method is general; the case is the yardstick.** Case knowledge lives in
the acceptance side only and never enters `src/`. For HDFS-11741 the oracle is:
the engine must rank `removeExpiredKeys()`'s removal guard as a flip candidate
*without being told what HDFS is*. It does. That check is cheap — it reads
`region_path_worklist.jsonl` before any concolic work — and should be run
before the expensive stages, not after Z3.

Note `causalEdge.mutatorDeclaredCallee` is the **demand** (which output
relation needs closing), not the flip target; the flip target is in
`replayContract.source.site`.

## The witness, stated once

HDFS-11741 is two readers of one rolling table disagreeing. The heartbeat
chain decides what the DN *has*; the getBlockKeys chain decides what the
Balancer *presents*; the fault is the Balancer presenting a key the DN has
already rolled away. A witness is meaningful exactly when both operands of
the fatal membership test are bound to the same producer timeline:

```
NN updateKeys()            S' = put(remove(S, expired), fresh), one writer lane
  ├─ shared field ─► getBlockKeys handler ── RPC ──► BlockKeyUpdater: addKeys
  │                                                    │ balancer's table        [cell 1 — dropped, see TODO 1]
  │                                                    ▼
  │                                     newDataEncryptionKey (on the SASL send path)
  │                                                    │ cached DataEncryptionKey [cell 2 — modeled]
  │                                                    ▼
  │                                     later handshakes ─► presented keyId
  └─ shared field ─► sendHeartbeat handler ─ RPC ──► BPServiceActor ─► DN allKeys
                                                       └─ DataXceiver: (assoc_has allKeys keyId), flipped
```

Readers choose cut points on the timeline independently; Balancer at roll i,
DN at roll j, i < j *is* the divergence. Cell 2 is why i lags j robustly:
the encryption key is generated once and reused, so the balancer's read is
pinned at the roll of its *first* handshake while the DN's table keeps
advancing — the cache is a cut point frozen by program structure, which the
timeline model expresses as a single write read by every later activation.
Every ingredient is engine vocabulary — single-writer timelines, declared
carrier projections, membership over one table. None of it is case
knowledge.

**This paragraph is a reading, never a specification.** The relations it
describes have to fall out of symbolic execution and merging — the lifetime
arithmetic in particular is whatever executing `updateKeys` produces, and
writing that formula down here instead of deriving it would skip the only
thing worth proving. Nothing in `src/` may encode a lag between readers, a
lifetime expression, or any ranking tuned to reach this story. Build the
model without it and ask whether the model admits such a solution at all.
UNSAT is data, not failure, and a different story than this one is a result
to report rather than a deviation to correct.

## TODO (remaining simplification)

**Current executable baseline.** The standard HDFS-11741 `run.sh candidates`
entry point completes the seven-region target-first workflow: every bounded
path set closes, composition has no named gaps, the fatal absence-mutation
witness is `PINNED`, and Z3 reports `SAT / REACHABLE`. Concolic seed replay
retains its 2400-second emergency budget; path flips use a separate 180-second
default and record a flip that publishes no selected result as
`REPLAY_PRODUCED_NO_RESULT`. Remaining work is simplification and cost
reduction, not a prerequisite for this result.

1. Project demanded scalar RPC leaves directly at the configured trace
   boundary, then retire `ARRAY_SNAPSHOT` and protobuf/container reconstruction
   paths.
2. Pre-project the few scheduler indices now obtained by repeatedly parsing the
   large runtime-region artifact, while retaining the evidence required by
   audits.
3. Replace remaining non-semantic artifact and closure fingerprints with
   canonical identities wherever a hash adds no correctness property. RPC
   value, argument, and payload fingerprints are already absent.
4. Continue the lean-code audit after every rebuild. Generated stress fixtures
   and case configs are rebuilt on demand rather than tracked; retain semantic
   binding, iterator-removal, false-SAT, and process-exit regression tests.

## Constraints

- No hand-written summaries or SMT, ever.
- No HDFS-specific special cases in `src/`.
- No over-design, no over-verification. Concise changes.
- Prefer fixing the whole class of a defect when one instance is found —
  fixing them one at a time costs a full pipeline run each.
