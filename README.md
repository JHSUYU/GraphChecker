# GraphChecker

> GraphChecker is an academic software-engineering and program-analysis
> project maintained by a University of Virginia PhD student. It studies
> distributed-system behavior with authorized, local, open-source unit-test
> workloads.

GraphChecker performs **failure-directed compositional symbolic reasoning**.
It does not symbolically execute an entire distributed system or enumerate all
thread schedules. Instead, it keeps the local behavior and cross-component
relations that can affect one target condition, then asks whether they admit a
consistent bounded execution:

```text
local symbolic transitions
  + symbolic value handoffs
  + read-from / RPC / partial-order constraints
  = bounded global candidate
```

The next architecture milestone is a workload-wide symbolic session in which
related threads share symbolic expressions and selected heap state. RPC and
shared-field values will then cross execution boundaries while the workload is
running, rather than being reconstructed only by post-processing. HDFS-11741 is
the first experiment for this design because it combines concurrent `while`
loops, shared state, RPC propagation, and a downstream target condition.

## Current status versus target architecture

| Area | Implemented baseline | Planned architecture |
|---|---|---|
| VM execution | one serialized concolic region and owner thread | one workload-wide symbolic session shared by participating threads |
| Thread state | activation-local stack, locals, heap shadows, and PC | thread-local stack/locals/PC inside a session-wide expression universe |
| Shared fields | runtime-confirmed edges composed after replay | live versioned symbolic heap and guarded read-from choices |
| RPC | configured boundary values joined by offline equality/order constraints | application-traced symbolic value handoff at send/receive |
| Ordering | program order plus per-channel/per-RPC constraints | one event ledger for program, field, RPC, async, and synchronization edges |
| SMT | composition of selected region summaries and observed edges | direct target slice of the symbolic expression/event graph, plus bounded merges |
| Result | bounded candidate over a selected causal graph | replay-checked candidate with explicit coverage gaps |

The current implementation already has source/epoch identity, occurrence-scoped
region plans, guarded local summaries, bounded choices among admitted writers,
and a causal-graph writer. The global multi-thread VM session, live RPC
expression handoff, session-wide heap, unified event order, and replay gates are
roadmap items; current artifacts must not be described as if those pieces were
already present.

## Target architecture

```text
target + unit-test workload
          |
          v
static target slice and hook selection
          |
          v
application tracing control plane
  source / region / async / RPC identity
          |
          v
per-JVM GlobalSymbolicSession
  + shared ExprArena
  + versioned symbolic heap
  + unified event ledger
  + one ThreadSymbolicState per JavaThread
          |
          +---- shared-field expression flow
          +---- symbolic RPC handoff
          +---- local region IN / PC / OUT
          |
          v
target-directed slice and symbolic merging
          |
          v
candidate.smt2 + result + causal graph + coverage gaps
          |
          v
sparse concolic replay validation
```

Static analysis remains useful for locating the target, selecting relevant
regions and fields, and bounding instrumentation. Application tracing provides
runtime identity and communication correlation. The VM owns symbolic value
semantics. The final composer should project and merge this recorded symbolic
graph; it should not guess RPC endpoints or pair fields by concrete-value
similarity.

An observed run cannot reveal a writer, RPC endpoint, or path that never
occurred. Unseen alternatives still require another replay or a statically
identified candidate. The design therefore reduces dependence on the original
causal skeleton for formula construction, but does not claim completeness over
all distributed executions.

Everything below through the HDFS-11741 acceptance plan describes the target
architecture unless a statement is explicitly labelled as implemented.

## Planned core runtime model

### One session, separate thread states

`GlobalSymbolicSession` will span the complete unit-test workload in one JVM.
Every traced cluster/application thread can attach to that same session; only
selected regions record PCs, while any selected symbolic carrier continues to
propagate. The session will own the expression arena, session-scoped object
identities, selected heap versions, and causal events. Each thread will retain
its own frames, shadow operand stack, symbolic locals, path condition, and
region stack. Threads will share expressions, never execution stacks or one
global path condition.

For multiple JVMs, one `runId` will federate one session per JVM. Raw VM
pointers will never cross a process boundary; portable expression DAGs will.
MiniDFSCluster runs its logical nodes as threads in one JVM, so HDFS-11741 will
exercise the same-JVM design first.

### Stable identity

The minimal identity model is:

- `sourceKey = kind / role / sourceId / epoch`: a NameNode, DataNode, client,
  or test driver incarnation;
- `occurrenceId`: one dynamic activation of a region on one source;
- `relationKey`: the reusable local transition contract;
- `exchangeId` and `attemptId`: one concrete RPC exchange and retry attempt;
- `eventId` and `fieldVersionId`: session-local runtime evidence.

A restart preserves the logical `sourceId` and advances `epoch`. Different
nodes and different epochs never merge implicitly. Dynamic object IDs, thread
IDs, owner IDs, call IDs, and event IDs may remain trace evidence, but they are
not cross-replay addresses or logical identity.

### Region and target semantics

A region occurrence will retain the existing local transition relation:

```text
T_r(IN, OUT) = OR_k (pathGuard_k(IN) AND OUT = expr_k(IN))
```

Compatible paths from repeated concolic runs are merged by `relationKey`, while
their source and occurrence evidence remains distinct. Multiple occurrences of
the target region are handled the same way as other regions; they are not
collapsed into one runtime event.

For a target replay, only the selected branch inside the target method is
flipped; its earlier reachability prefix is record-only. Producer regions may
still explore selected output-relevant branches in their own bounded
worklists. Reaching the target and capturing a valid target relation matters;
whether the enclosing JUnit method ultimately passes is not the acceptance
criterion.

## Planned RPC symbolic propagation

Application tracing will be the RPC control plane. It will identify the local
source, logical call, attempt, exchange, direction, endpoint, and serialized
leaf path. The VM will be the symbolic data plane: it will export an expression
at the sender and attach it to the deserialized value at the receiver.

For example:

```java
x = getRPC(a, b);
y = x + 1;
```

The intended flow is:

1. Before request serialization, tracing allocates an `exchangeId`; the VM
   exports the symbolic leaves of `a` and `b`.
2. At server deserialization or handler entry, tracing matches that exchange
   and the VM attaches the imported expressions to the server arguments.
3. The server executes normally and derives a response expression `E(a,b)`.
4. The response hook exports `E`; the client return hook attaches it to `x`.
5. The caller executes `x + 1`, and the VM directly builds `E(a,b) + 1`.

The client and server remain separate source-local region occurrences. Only
selected values and provenance continue across RPC; the sender's stack, heap
identity, source, and path condition do not.

The symbolic sidecar for one exchange needs only the run/session identity,
exchange and attempt IDs, direction, endpoint/schema mapping, and symbolic
leaves `(path, sort, shape, expression reference, concrete fingerprint)`.
Same-JVM RPC uses an expression reference through a session broker. Cross-JVM
RPC later uses a content-addressed portable DAG. Schema-aware Protobuf/Writable
adapters should discover symbolic leaves generically; explicit mappings are
reserved for real serialization transformations.

Retries, timeouts, cancellation, late responses, fan-out, and response
aggregation create distinct exchange events. A unique exchange propagates one
expression directly. Several compatible messages become a guarded message
choice; they are never merged solely because their concrete payloads match.
Missing metadata or incompatible shape produces an explicit RPC handoff gap
and a fresh/concrete fallback, not a silent guessed binding.

Protocol boundaries that transform values may provide a small semantic
adapter. The adapter still uses the same `exportExpression`/`attachExpression`
VM interface, but declares the real transformation instead of asking the VM to
symbolically execute a protocol library. HDFS-11741 needs one such adapter for
its SASL data-transfer handshake.

## Planned shared fields and concurrent writes

Selected field, static-field, array, container, volatile, and atomic writes
will publish a new expression version after the concrete write succeeds. A
read will capture its concrete value and compatible symbolic versions in the
same VM access hook.

For example:

```text
T1: W1(x) = A + 1     concrete 10
T2: W2(x) = B * 2     concrete 10
T3: R3(x)             concrete 10
```

One concrete execution still performs one real read. If synchronization or a
unique version proves its provenance, `R3` immediately receives that writer's
expression. If an ordinary concurrent read cannot distinguish equal-valued
writes, the VM must not guess. It attaches a bounded guarded expression:

```text
exactlyOne(rf1, rf2, rf_unknown)
R3 = ite(rf1, A + 1, ite(rf2, B * 2, Unknown_x))
```

Each candidate also carries its writer path guard and legal order constraints.
`rf_unknown` prevents an incomplete writer set from turning an under-approximate
UNSAT result into a global conclusion. Volatile, monitor-ordered, and modeled
atomic operations can provide stronger provenance. `AtomicInteger`/`AtomicLong`
RMW operations must publish one linearized relation such as
`new = old + delta`; CAS publishes only the concretely observed arm.

Shared-field propagation will be automatic for symbolic values in the
session-wide shadow heap. Static analysis will select the bounded carrier set
to control cost; it will not reconstruct a write/read equality afterward.

## Planned symbolic merging and SMT construction

Merging will happen at three different levels:

1. **Local path merge:** guarded cases from repeated executions form one local
   transition relation.
2. **Read/message merge:** compatible writer or RPC versions use exactly-one
   selectors plus value and order constraints.
3. **Global target slice:** the final formula contains only expression and event
   nodes that can reach the target predicate.

All causal channels will share one event-order domain. Program order, thread start
and join, executor handoff, RPC send/receive, monitor/volatile/atomic order,
read-from, restart, and persistence edges therefore participate in the same
cycle check. GraphChecker does not construct or enumerate a total schedule.

The target formula is conceptually:

```text
AND local region transitions
AND symbolic value handoffs
AND guarded read-from/message selections
AND failure-relevant partial order
AND target predicate
```

The causal graph and SMT are two views of this same selected model. The graph
keeps source/epoch, region occurrences, external API roots, key branches,
observed candidate edges, solver-selected edges, replay evidence, and gaps.

## Planned concolic replay policy

Replay will be best effort and start from a fresh unit-test cluster. The first
workload provides the observed loop unroll, read-from relations, RPC exchanges,
and array/container shape as an alignment reference, not a full deterministic
replay contract.

Hard admission will be limited to the correct source/region occurrence and a valid
target/output relation. A different worker thread, harmless loop-count change,
extra RPC attempt, or approximate compatible shape is accepted when the
selected symbolic flow remains valid; the deviation is recorded as a coverage
gap. Missing target flow retains every usable local relation but makes the
result partial.

When the solver selects a competing writer, replay will enforce only the sparse
read cut required by that model: the selected writer precedes the read, and
other writers occur before it or after the read. Gates will be placed before
the selected access or lifted outside an application lock. GraphChecker will
never park while holding an application lock, overwrite a program field, or
replace an RPC return value. The concrete read version and exchange must still
be observed.

SAT means the selected bounded model has a consistent assignment. UNSAT means
unreachability only within a closed selected model. UNSAT from a partial or
seed-only model is inconclusive. Every unsupported operation, unknown writer,
shape mismatch, unsafe gate, missing exchange, or import failure remains a
named gap.

## HDFS-11741 first experiment

The source of truth is the Hadoop checkout at `/opt/hadoop`. Its current branch
is `analysis/hdfs-11741-before-fix` at
`529147b5640fcb2a0d733385148be4e8b0b901ce`, built on the upstream pre-fix
baseline `ece33208b89a6a06c1b362d10fab31343fe5df13`. The two later tracing
commits are source candidates to re-audit, not specifications for the new
architecture. The old
HDFS-11741 workflow scripts, generated patches, and prior artifact trees are
not inputs to the new design and must not define its regions, bounds, or
acceptance checks. We will inspect and modify the Hadoop source directly, then
create one minimal source-driven test launcher after the new runtime APIs are
stable.

The starting workload is the existing source test:

```text
hadoop-hdfs-project/hadoop-hdfs/src/test/java/
  org/apache/hadoop/hdfs/server/balancer/
  TestBalancerWithEncryptedTransfer.testEncryptedBalancer1
```

The production source already exposes the end-to-end behavior to model:

1. `HeartbeatManager.Monitor.run()` loops while the NameNode is running and
   calls `BlockManager.shouldUpdateBlockKey()`. The master
   `BlockTokenSecretManager.updateKeys()` changes `currentKey`, `nextKey`, and
   `allKeys`; `removeExpiredKeys()` contains the relevant iterator loop.
2. `KeyManager.BlockKeyUpdater.run()` loops while the Balancer is active,
   invokes the NameNode `getBlockKeys()` RPC, and feeds the result to
   `BlockTokenSecretManager.addKeys()`. `KeyManager.newDataEncryptionKey()`
   caches the selected `DataEncryptionKey`.
3. `BPServiceActor.offerService()` loops on the DataNode heartbeat path.
   A key-update command reaches `BPOfferService`, which calls `addKeys()` on
   the DataNode's local table.
4. The Balancer then opens a data-transfer SASL handshake. The client encodes
   `DataEncryptionKey.keyId`, `blockPoolId`, and `nonce` into the SASL user
   name. The DataNode parses them, calls
   `BlockPoolTokenSecretManager.retrieveDataEncryptionKey(keyId,
   blockPoolId, nonce)` to select the block-pool manager, then delegates to
   `BlockTokenSecretManager.retrieveDataEncryptionKey(keyId, nonce)`.
5. The selected target is the `allKeys.get(keyId) == null` branch in the final
   method. `nonce` is consumed only after that lookup succeeds; `blockPoolId`
   selects the manager but is not an operand of the target branch.

MiniDFSCluster supplies distinct logical sources for the NameNode, each
DataNode, the Balancer/client, and the test driver, although they execute as
threads in one JVM. A fresh concrete source run will establish the initial
loop unroll and container/RPC shapes. The new harness will bound only the
target-relevant loops and will then vary at least one loop count to ensure that
replay follows symbolic flow rather than an exact historical unroll.

### HDFS SASL symbolic adapter

Hadoop IPC propagation alone is insufficient: the value selected by the
Balancer crosses a SASL transformation before the DataNode target. A dedicated
HDFS adapter is therefore allowed and required:

```text
Balancer DataEncryptionKey
  keyId, blockPoolId, nonce
          |
          | SASL_HANDSHAKE exchangeId
          v
DataNode parsed keyId, blockPoolId, nonce
          |
          +---- blockPoolId ---> select block-pool manager
          |
          +---- keyId ---------> allKeys.get(keyId) target
          |
          +---- nonce ---------> createPassword after lookup
```

This adapter will live in the Hadoop integration layer. GraphChecker's core
will see only a generic typed symbolic handoff.

At the client, the adapter will export expressions immediately before
`getUserNameFromEncryptionKey()`. At the server, it will correlate the
handshake attempt and attach the expressions after
`split`/`parseInt`/Base64 decode. `blockPoolId` will flow into manager
selection, while `keyId` and `nonce` will flow into the delegated manager
call. This preserves the actual mapping without requiring the VM to model the
entire SASL implementation. It will not propagate the sender stack or PC, or
attach fields absent from the handshake. A malformed three-component shape,
unmatched attempt, or inconsistent concrete fingerprint will become a named
SASL handoff gap.

The ablation sequence is:

1. rebuild the current offline region-composition baseline from the same
   Hadoop source workload, without reusing old artifacts;
2. global session with live communication handoff (Hadoop RPC plus SASL);
3. live RPC plus session-wide shared-field/atomic propagation;
4. unified event ledger and sparse read-cut replay;
5. the patched HDFS variant as a semantic control.

Acceptance requires:

- all selected HDFS threads attach to one same-JVM symbolic session without
  mixing thread-local path conditions;
- NameNode expressions reach the Balancer/DataNode receiver regions through
  the traced RPC exchanges without post-hoc concrete-value matching;
- the cached Balancer `DataEncryptionKey.keyId` expression crosses the SASL
  adapter and is the expression used by the DataNode target lookup;
- selected shared-state reads use an exact or explicit guarded writer choice;
- only the target replay flips the selected target-method branch; its prefix
  remains observed, while producer worklists remain independently bounded;
- the target-sliced SMT and causal graph agree on source, occurrence, value
  flow, order, selected branch, and coverage gaps;
- loop-count variation either preserves the selected flow or produces a named
  partial result; it never silently binds a different occurrence.

Report target reach, resolved value flows, gap classes, SMT size and solve time,
replay attempts, runtime, peak memory, and symbolic sidecar bytes for every
ablation. A SAT result is reported as a bounded candidate until the selected
flows are confirmed by replay.

There is intentionally no experiment command yet. The first implementation
deliverable is a new source-first launcher; the legacy HDFS-11741 scripts will
be retired rather than extended.

## Implementation TODO

### Phase 0 — Preserve and simplify the baseline

- [ ] Re-audit `/opt/hadoop` from the pre-fix source revision, keeping only
  source hooks that match the new session/handoff interfaces.
- [ ] Retire the old HDFS-11741 script/patch pipeline and create no compatibility
  path for its artifact schemas.
- [x] Use `sourceKey`, `occurrenceId`, `relationKey`, and contract hash in the
  public plan/task/summary path.
- [x] Keep local guarded transition summaries, bounded path worklists, current
  Composer behavior, and causal-graph output as the regression baseline.
- [ ] Finish removing logical dependence on owner ID, process-name inference,
  root call ID, representative occurrence, expanded occurrence catalogs,
  canonical/exact port bijections, root-bound output closures, and duplicate
  edge/goal/closure artifacts. Trace-only evidence may remain internal.
- [ ] Converge on one canonical causal-model artifact plus `.smt2`, result, and
  a generated graph view; do not add compatibility schemas.

### Phase 1 — Global VM session

- [ ] Split the current VM `ThreadContext` into session-owned state and
  thread-owned execution state.
- [ ] Replace the single-active-region mutex with attach/detach membership for
  relevant Java threads.
- [ ] Add session-wide atomic expression/object IDs and immutable expression
  lifetime; clean them only at session teardown.
- [ ] Preserve independent shadow stacks, locals, PCs, branch events, and
  region frames for every thread.
- [ ] Keep object identity stable across GC and prevent one thread/region exit
  from clearing another thread's symbolic state.

### Phase 2 — Shared field and synchronization propagation

- [ ] Add versioned hooks for selected instance/static fields and fixed-shape
  arrays/containers, pairing each symbolic update with the concrete access.
- [ ] Add global linearization records for volatile, monitor, thread lifecycle,
  `AtomicInteger`/`AtomicLong`, Unsafe, and VarHandle operations.
- [ ] Implement exact writer propagation when justified and guarded candidate
  expressions with an unknown fallback for ambiguous plain reads.
- [ ] Add one unified event-order ledger and reject cyclic candidate orders.

### Phase 3 — Application-traced RPC and async handoff

- [ ] Replace object-keyed/FIFO correlation with unique async handoff,
  logical-RPC, attempt, and exchange IDs.
- [ ] Add framework-level request/response hooks around serialization,
  deserialization, and handler entry/exit.
- [ ] Add `exportExpression`, same-JVM broker, `importExpression`, and
  `attachExpression` VM APIs.
- [ ] Implement generic Protobuf/Writable leaf discovery, shape validation,
  retries, timeouts, late responses, fan-out, and response aggregation.
- [ ] Implement the HDFS SASL adapter from `DataEncryptionKey` leaves to
  block-pool manager selection and the delegated `(keyId, nonce)` lookup, with
  one exchange ID per handshake attempt.
- [ ] Add portable, content-addressed expression envelopes for cross-JVM runs
  only after the same-JVM HDFS experiment is stable.

### Phase 4 — Merge, SMT, causal graph, and replay

- [ ] Build the target slice directly from the session expression/event graph.
- [ ] Reuse local relation merging, but replace offline RPC/field discovery with
  recorded expression identities and guarded version choices.
- [ ] Emit one order domain across field, RPC, async, synchronization, and
  region events.
- [ ] Compile a solver-selected read/message cut into lock-safe sparse gates;
  validate actual versions and exchanges without changing program values.
- [ ] Classify target, flow, shape, import, gate, and source-epoch divergence;
  retain partial relations and emit SMT with honest coverage state whenever
  the target relation remains usable.

### Phase 5 — Tests and HDFS-11741 evaluation

- [ ] Build a minimal launcher directly around the Hadoop source test; do not
  call the legacy HDFS-11741 workflow scripts.
- [ ] Unit-test simultaneous thread contexts and path-condition isolation.
- [ ] Test one writer, equal-valued competing writers, unknown writer,
  volatile/monitor ordering, atomic RMW/CAS, and lock-safe gates.
- [ ] Test synchronous RPC, retry/timeout, response flow, async executor
  handoff, shape drift, and source restart/epoch separation.
- [ ] Run the HDFS-11741 ablations, loop-count variation, and patched control.
- [ ] Compare the new graph/SMT against the preserved offline baseline and
  publish gaps and costs, not only SAT/UNSAT.

## Non-goals and invariants

- Do not enumerate all thread schedules, message orders, or system executions.
- Do not share operand stacks, locals, or one global PC between threads.
- Do not copy a sender's PC or source identity into an RPC receiver.
- Do not infer a plain-race writer from equal concrete values or event IDs.
- Do not treat a static candidate as an observed causal edge.
- Do not use transient trace IDs as replay identity.
- Do not hide unsupported semantics behind an unconstrained SAT result.
- Do not require exact replay of unrelated loop iterations or events.
- Do not introduce HDFS method names, formulas, or branch outcomes into the
  generic VM, runtime, merger, or SMT semantics.

## Build

GraphChecker's current Java baseline is built with:

```bash
mvn -q test
mvn -q -DskipTests package
```

The custom-JDK and experiment-specific instructions are documented under
[`docs/`](docs/). The HDFS-11741 instructions will be rewritten when the new
source-first launcher exists.
