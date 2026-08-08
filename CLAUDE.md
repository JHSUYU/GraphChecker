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
  ├─ shared field ─► getBlockKeys handler ── RPC ──► KeyManager.addKeys
  │                                                    └─ shared field ─► Dispatcher ─► presented keyId
  └─ shared field ─► sendHeartbeat handler ─ RPC ──► BPServiceActor ─► DN allKeys
                                                       └─ DataXceiver: (assoc_has allKeys keyId), flipped
```

Readers choose cut points on the timeline independently; Balancer at roll i,
DN at roll j, i < j *is* the divergence. Every ingredient is engine
vocabulary — single-writer timelines, declared carrier projections,
membership over one table. None of it is case knowledge.

## TODO (ordered: first what falsifies the report, then what binds the query)

**1 — The silent drop (fail-open; ahead of everything).** The accepted
candidate composed all six regions of the seven-row plan and reported
`gaps: 0`, yet the four `CONFIRMED_RUNTIME_IDENTITY` field-flow edges
KeyManager→Dispatcher became zero channels in the query — every channel it
does contain is Dispatcher-to-itself — leaving the presented keyId bound by
nothing but its own int range. Find where composition dropped a confirmed
channel (demand walk, port selection, or `composable()`), and wire the
Acceptance audit in so a recurrence cannot be quiet. A fail-closed defect
costs a proof; this one manufactured one.

**2 — Rank targets by residual freedom, not producer count.** `TargetRank`
prefers `producerGoals` count, which chose the write-phase handshake (9)
over the balancer one (6) and dropped the presenting chain from the task
plan entirely. Rank by how few unconstrained operands the closure leaves on
the fatal condition — that is the acceptance criterion itself, so ranking
and witness strength cannot disagree. Producer count breaks ties.

**3 — Recorder: container member identity.** One recorder package closes
three named gaps: element-level carrier projection (measured: 8 rebuilt
keys against 9 producer definitions, 6 against 3 — order pairing has no
recorded positions to attach to; `observedContainerWidth` is always −1),
the map whose String keys are one nameless symbol (source of
`ABSENT_EXPRESSION`, `JAVA_STRING_REFERENCE_IDENTITY:==`, and
`splitElement:CONCAT_RECEIVER_REQUIRED`), and array-element demand below a
spine object (the fatal read sits on `allKeys[]` elements; the landed
projection reaches the singleton spine `currentKey` only). Invalidates the
recording and everything below it; both passes measured ≈3.5 min.

**4 — Shared state as bounded timelines.** Writers on one lane become a
chain S₀→…→S_N of the already-proven summary, alpha-renamed per step — a
**third ledger** (state-chain bound), distinct from the unroll bound
(paths) and the replay cap (runtime), and visible in the SMT so a witness
says "within N rolls". Readers select cut points, monotone along each
reader's program order, free across unordered readers — that freedom is the
fault. Only activation-boundary states are published, which is region
atomicity by construction. Multi-lane **mutation** writers fail closed
(captured snapshots bake in the recorded interleaving; reordering them is
unsound); multi-lane assignment writers keep the existing selection.
Zero campaign cost — the chain is composition-layer instantiation. It also
gives clock monotonicity its footing (`t_i ≤ t_{i+1}` along the chain),
which T5 measured as uninstantiable today (all clock reads are case-split
alternatives, not a sequence).

**5 — R1b, after paths close.** Post-closure the predicate set is complete
for the closed path set, so a leaf never read by any recorded predicate may
demote to concrete *for composition only* (exploration keeps it symbolic).
This is the missing tier between `value_flow` (cannot cross a codec) and
full taint (keyId and its co-carried neighbour have byte-identical
reachable sets — measured, symmetric difference zero); statically the tier
does not exist.

**In flight** — the contract-vs-seed conflict (`replay event conflicts with
task seed`) is a static check that today runs at import time, *after* the
replay it condemns (measured: 26 minutes of engine work discarded by it).
Being front-moved to planning with the import check kept; the same round
measures the true flip count (75 EXPLORE guards is policy, not candidates)
and the oracle rank.

**Open** — a DN flip replay reproducibly ends under SIGKILL before
publishing; peak RSS 961MB against 182GB available, so not memory. Skips
now carry their kind, so the next occurrence is attributable.

**Landed this round** — demand crosses RPC response edges
(`ProtocolCarrierReconstruction`; NN handler regions and the roll monitor
enter the task plan). Spine-object field projection under its own authority
(`TRUSTED_DECLARED_CARRIER_PROJECTION_V1`), value-checked against evidence
the rule never reads. Engine released on prefix contradiction; the
entry-state gate demoted from veto to ordering; skip records distinguish
losing the engine from an unwalkable path. Fan-out defaults to the host and
announces its width; long stages log beside their artifacts (the serial
campaign was launched with JOBS=1 — the posture CLAUDE.md warns about, and
nothing recorded it). T5 exists as a tool (`smt_realizability_refine.py` +
`environment-axioms.smt2`): point-blocking measured non-convergent; the
expired-case control (force `expiryDate > now` on the removal branch) is
UNSAT, which is the encoding-faithfulness check passing.

## Constraints

- No hand-written summaries or SMT, ever.
- No HDFS-specific special cases in `src/`.
- No over-design, no over-verification. Concise changes.
- Prefer fixing the whole class of a defect when one instance is found —
  fixing them one at a time costs a full pipeline run each.
