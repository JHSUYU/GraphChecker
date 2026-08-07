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
HDFS11741_REGION_JOBS=1 HDFS11741_PATH_JOBS=1 \
HDFS11741_CONCOLIC_HEAP=8g HDFS11741_ENGINE_WAIT_MS=1200000 \
  experiments/hdfs/hdfs-11741/run.sh candidates
```

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

Degenerate SAT (`reachCondition.formula == "true"`, empty `valuations[].values`)
is not success. `expiryDate` plausibility is **not** checked at this stage.

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

## TODO

**Ruling L — bring the NameNode regions into the closure.** Mandatory. The
recursion terminal condition is wrong: deserialization writes are transport
reconstruction, not value production, so the closure stops short of the real
producer. Fix that judgement generally; the NN regions follow as a consequence.
Until then `expiryDate` has no producer and its model value means nothing.

**T3+T4 — analysis-layer speedup and the selection rules.** One work package,
because they touch the same code and their acceptance criteria conflict if
split (T3 demands unchanged output; T4 deliberately changes it).

- **R1 symbolic leaves** (landed): a leaf is symbolic only where some explored
  guard reads it. A value that is only carried never buys a path, and
  everything computed from it becomes symbolic for nothing. Fails closed.
- **R2 flip targets**: the fatal guard is the *goal*, not the flip target.
  Flip targets are branches dominating a demanded state mutation.
- **R1 is blocked from where it would matter most, and the reason is
  measured.** The refined dataflow graph offers only two tiers. `value_flow`
  is too narrow — it does not cross a codec or a container lookup, so
  tightening to it cuts the very chain that decides the fatal branch. Full
  taint is too wide — one leaf reaches ~33k cells, so almost nothing is
  cuttable. Concretely, the key whose membership decides the failure and a
  neighbouring field carried in the same encoded string have *identical*
  reachable sets (symmetric difference zero), so **no name-free criterion can
  separate them today**. The missing tier is value-level dependence that
  survives encode/decode: "after being encoded and decoded, is this value
  still *compared*, or only *reconstructed*?" Until that exists, R1 only
  removes leaves nothing reads at all (a logging flag, on the target region).
  This is also why one captured expression reaches 138MB nested past 10,000
  levels: the carrier cannot be told from the value it carries.

**T5 — realizability refinement at the SMT layer.** Decoupled from everything
upstream: on an implausible SAT, assert the negation of *why* it is implausible
and re-solve. Block the reason, not the point — negating one assignment
eliminates one point in a vast space and never converges. The accumulated
constraints become a realizability spec. **Constrain the environment (clock
monotonicity, non-negative lifetimes); never constrain program causality** —
that is forging a summary. If blocking turns it UNSAT, that is a strong result:
every witness in the bounded model needed the implausible condition.

**Open**: a DN flip replay reproducibly ends under SIGKILL before publishing.
Measured peak RSS 961MB against 182GB available, so it is **not** memory
exhaustion — cause unknown. Currently recorded as
`PATH_FLIP_REPLAY_PRODUCED_NO_RESULT` and explored past.

**Open**: two composition gaps surfaced once the pipeline reached the composer
— `JAVA_STRING_REFERENCE_IDENTITY:==` (Java reference equality between strings
of different origin; string *content* semantics are implemented) and
`splitElement:CONCAT_RECEIVER_REQUIRED` (split is implemented only for a
receiver that flattens to a concat chain).

## Constraints

- No hand-written summaries or SMT, ever.
- No HDFS-specific special cases in `src/`.
- No over-design, no over-verification. Concise changes.
- Prefer fixing the whole class of a defect when one instance is found —
  fixing them one at a time costs a full pipeline run each.
