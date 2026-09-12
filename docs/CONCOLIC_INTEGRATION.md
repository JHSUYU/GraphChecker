# Concolic integration contract

This document describes the boundary between instrumented Java code,
GraphChecker, and the custom JDK. The graph chooses what to observe and replay;
the custom JDK supplies the symbolic values used by the SMT query.

## Analysis and execution identity

Static analysis starts at the annotated target and finds a backward dependency
closure of region skeletons, communication sites, shared-state sites, explicit
symbolic sources, and retained loops. The first runtime trace resolves that
skeleton to concrete region occurrences, message exchanges, selected
shared-state reads, bounded writer snapshots, and topology. Those observations
refine the closure and instrumentation plan. They do not create
producer-to-consumer value equations.

A scheduled member names one region occurrence and one local path goal:

```json
{
  "taskId": "TASK.SEED.<sha256>",
  "goalId": "GOAL.REGION_PATH.<uuid>",
  "goalKind": "REGION_PATH_CLOSURE",
  "regionId": "REGION.<uuid>",
  "sourceKey": "node#epoch0",
  "occurrenceId": "node#epoch0/region/REGION.<uuid>#1",
  "rootSelector": {
    "method": "<Worker: int compute()>",
    "kind": "RECEIVER_CONTEXT",
    "causalAnchor": {"kind": "REGISTERED_SOURCE", "sourceKey": "node#epoch0"},
    "invocationOrdinal": 1
  }
}
```

A scheduled task id is `TASK.SEED.<sha256>` over the member's source
occurrence, relation content and exact port set; the replay task minted for a
solved flip is `TASK.REPLAY.<sha256>`. `goalId` is `GOAL.REGION_PATH.` or
`GOAL.TARGET_REACH.` followed by a UUID derived from the occurrence id, and
`goalKind` is correspondingly `REGION_PATH_CLOSURE` or `TARGET_REACH_CLOSURE`.

An occurrence id is a planned address,
`<sourceKey>/region/<regionId>#<ordinal>`, optionally followed by
`#a<ordinal>` naming the activation that ran it. One planned address may be
entered several times in one replay, so every compatible activation is
published as its own occurrence rather than one being answered and the rest
reported as an ambiguous address. Plan rows, relations and
target-reach queries carry the planned address; a summary row carries the
activation form and repeats its planned address in `plannedOccurrenceId` beside
`activationOrdinal`. A plan and a summary are matched on the planned address,
never on the activation.

A schedule is drawn from exactly one closure. `ConcolicScheduler
--closure-mode` is `candidate` (every occurrence the frozen region plan
declares), `seed-replay` (only the occurrences a seed activation can replay) or
`active-observed` (only the occurrences this iteration's summaries observed),
and the campaign states which one each stage uses.

All members in the selected causal closure form one linked replay bundle. They
execute in one workload JVM so native expression handles, shared-state
versions, and boundary identities remain valid across the whole causal chain.

## Explicit symbolic roots

There are two root authorities:

- a configured application source such as a NameNode configuration field;
- a planned manual symbolization action, including the public symbolization
  hooks used by the HDFS workloads.

Each successful mint records stable source identity, occurrence, Java type,
and solver term. A value with no explicit root or propagated expression is a
coverage gap. The runtime and composer do not manufacture an unconstrained
replacement symbol.

### Declaring which roots an experiment wants

Most roots are proposed automatically: any primitive return of a call the
analysis does not hold, reached backwards from an explored branch, becomes an
`EXTERNAL_CALL_RETURN` input port. For the HDFS block-key workloads that is
every `<org.apache.hadoop.util.Timer: long now()>` return. An experiment that
does not want the whole automatic set narrows it with
`causynth_symbolic_inputs=@config/symbolic-inputs.jsonl`.

The file is a **restrictive allowlist, not an addition**: with it present, any
input action the file does not name is scheduled `CONCRETE` and keeps whatever
expression the VM already propagated to it, so it mints nothing. A region the
file does not mention has all of its symbolic actions concretized. Without the
file every automatic candidate stays symbolic.

One JSONL row per region. `regionId` is required and must name a region the
runtime plan actually contains; the other three keys are optional sets of
names, any of which admits an action:

| key | matches the action's |
|---|---|
| `fieldSignatures` | `accessFieldSignature` or `declaredFieldSignature` |
| `portIds` | `portId` or `symbol` |
| `cells` | `cell` |

`cells` is how a call return is named, since it carries no field signature: an
`EXTERNAL_CALL_RETURN` action's cell is `<callee signature>.return`, identical
at every call site of that callee inside the region, so one entry declares
"this region's wall clock". Example, from
`experiments/hadoop/hdfs-17899/symbolic-inputs.jsonl`:

```json
{"regionId":"REGION.aaa1cfd7-...","fieldSignatures":["<org.apache.hadoop.security.token.delegation.DelegationKey: int keyId>"],"cells":["<org.apache.hadoop.util.Timer: long now()>.return"]}
```

A declared row does not only survive the narrowing: it **mints**. Once a
shared-state carrier is installed, every later read of a field arrives wrapped
in a `ReadFrom`, including a field only ever written from constants, and the
automatic rule reads that wrapper as "already propagated" and skips the mint --
so a declared field could stay concrete. A declared source of primitive type
asks the strict question instead (is anything symbolic actually inside the
tree?) and mints where the answer is no, recording the usual
`PLANNED_MANUAL_SYMBOLIZATION_V1` evidence. A declared read that a symbol has
already reached still flows, so declaring both a root and the values derived
from it does not fork the chain: on the HDFS block-key experiments
`BlockTokenSecretManager#serialNo` is the mint and `DelegationKey#keyId` /
`#expiryDate` flow from it and from the clock. Non-primitive declarations keep
the loose rule, since a container or reference has no root to mint.

Two things are exempt from the allowlist and stay symbolic without a row:

- a field owned by a `CausynthSymbolicSource.symbolize` hook site — the hook
  call is itself the declaration;
- an `EXPLICIT_SYMBOLIC_FAULT` port, i.e. a `Debug.makeSymbolicBoolean` marker
  the workload wrote into its own source.

Every candidate the file refuses is published, with its region, source kind,
site and cell, as `suppressedRootCandidates` in the scheduler's
`symbolic_root_policy.jsonl`, so a root that is missing downstream can be
traced to the declaration rather than to the mechanism that proposed it.

## Trace context and topology

The workload registers a stable node owner with `registerSource`, may bind
handler aliases to it, and starts each external operation with
`beginSourceRequest`. It closes the returned scope in `finally`.

At a message boundary:

```text
outboundExchange(...) -> strict trace-context header
inboundExchange(header, ...) -> scope token
endInboundExchange(scope token)
```

The header carries sender span, source identity, request flow, and the symbolic
message envelope. `recordExchange` records the SEND or RECEIVE leg and its
REQUEST or RESPONSE half. Correlation, attempt, endpoint, and instrumentation
site identifiers describe topology and locate the exact handoff. They are not
SMT variables and are never used to reconstruct a value.

## VM propagation and consumer anchors

A declared wire flow identifies one exact producer endpoint and one exact
consumer endpoint. Instrumentation invokes:

```text
exportCommunicationLeaf(portId, carrier, field, descriptor)
attachCommunicationLeaf(portId, carrier, field, descriptor)
```

A port id names one declared endpoint of one exchange site --
`<exchangeSiteKey>.req.<name>` or `<exchangeSiteKey>.resp.<name>` -- while a
site id, `<method>#u<unitIndex>`, names the bytecode unit a capture was
instrumented at. The plan's handoff row carries both, and the hook is addressed
by the port.

The export stores the live VM expression handle in the next message envelope.
The matching receive attaches that expression to the real consumer value. A VM
handle is valid only inside the workload JVM/session; linked regions therefore
replay together.

The custom JDK leaves a transparent `ConsumerBoundaryExpression` at every
successful RPC attach and shared-state read. The anchor records boundary kind,
event identity, Java type, and the already-propagated payload expression. Java
operations continue from that payload. For example:

```text
C produces x + 1
  -> RPC attach in B anchors x + 1
  -> B computes 2 * (x + 1)
  -> RPC attach in A anchors 2 * (x + 1)
  -> A branches on the same propagated expression
```

Shared fields and containers use the same rule. When several recorded writes
can supply a read, its propagated payload is a guarded choice over every writer
expression. Each arm retains its writer case and local path condition. The SMT
query requires exactly one arm and makes that arm imply its writer case and
local path condition. All candidates in the bounded write set remain available
to this choice. An incomplete set remains a coverage gap and cannot support a
closed final claim.

Requiring the selected arm's writer is necessary but not sufficient: on its own
it leaves every *later* writer to the same location free to run as well, so a
read could take a value its own program order has already overwritten. The
model therefore also says that the selected arm is the last write the read
could have seen. The order is the VM's own -- each candidate carries the
session-monotonic `fieldVersionId` of the version it names, and a read's
candidate list is the location's retained version list taken under the version
lock at the read, so every candidate was published before the read and the ids
order them exactly. For candidates `w_1 < ... < w_n`, selecting `w_k` implies
`w_k` is active and no `w_j` with `j > k` is, where "active" is the same
conjunction of writer case closure and local path condition the arm's writer
obligation already asserts. The earliest candidate is the location's `INITIAL`
version, so selecting it forbids every tracked writer. Each arm but the last
carries one named `guarded_read_order__` assertion. Version ids minted in
different symbolic sessions do not compare, so one stable read lowered from
several sessions keeps an order only where the sessions agree; a read whose
candidates admit no single order keeps the rest of its model and is reported as
`GUARDED_READ_ORDER_UNKNOWN` in the guarded-read model, which is telemetry and
not a refusal.

## Local path conditions and symbolic merging

Each region records the path condition it executed. RPC propagation does not
copy an upstream region's path condition into the receiver thread. Instead,
the importer keeps every region case with its own selector and local path
condition.

Offline closure groups consumer anchors by stable boundary family. Every
observed payload becomes one family arm selected by the exact producer case.
The selector implies that case's local path condition. Nested anchors are
resolved recursively, so a multi-hop dependency shares its intermediate merge
instead of enumerating the Cartesian product of all upstream paths.

For two independent dependencies with two cases each, the formula contains two
two-arm merges. It does not enumerate four whole executions. For a dependent
chain, the downstream payload already contains the upstream expression and the
family selectors add the matching local path conditions. Composition directly
lowers those propagated expressions and local conditions.

## Replay waves

One path-flip obligation chooses a primary region branch. Companion regions in
the same bundle receive the same solver assignment and replay normally, so
downstream branches, RPC handoffs, and GuardedRead candidate snapshots are
observed again. Different obligations run in separate workload JVMs and may
execute in parallel.

One planner JVM runs per wave. It reads the same immutable summary snapshot
and task plan for every member named on its `--members` roster, computes the
propagation closure once, and writes each member's own path manifest and
worklist into that member's own directory. The campaign waits for the wave,
imports its new cases, then publishes one larger snapshot for the next wave. A
region is closed only at this closure-wide fixed point. An obligation whose
flip query exhausts the solver budget is recorded as the `SOLVER_TIMEOUT`
exploration status and the `PATH_FLIP_SOLVER_TIMEOUT` path coverage gap: its
sibling path stays unexplored, which blocks `UNSAT_CLOSED` and never a
`SAT_CANDIDATE`. A topology change quarantines the complete replay bundle and
starts a new topology epoch; cases from different epochs are never merged.

Retained loops use their configured finite unroll as one region-local path.
Repeated transfers and shared-state accesses keep their loop/boundary ordinal
and candidate writer versions. Loop iterations do not become separate
symbolic-merge cases merely because they repeat.

## Result contract

Every imported region summary carries `schemaVersion`, `kind`, `goalId`,
`taskId`, `sourceKey`, `topologyEpoch`, `boundarySessionScope`, `regionId`,
`occurrenceId`, `activationOrdinal`,
`plannedOccurrenceId`, `relationKey`, `loopBound`, `goalKind`, `edgeBindings`,
`pathCondition`, `branchMappings`, `normalExit`, `boundedExit`,
`exceptionType`, `localCaseId`, `summaryId` and
`pathSetClosed`. Evidence the replay did not produce is absent rather than
empty: `symbolicSourceEvidence`, `manualSymbolicInputObservations`,
`recordedSharedState`, `vmHandoffEvents`, `pathLoopCounts`,
`pathLoopCountGaps`, `alignmentGaps`, `familySnapshotDigest`,
`replayGroupId` when the replay named a group, `sharedExpressionTable` when
some payload of the row refers to a hash-consed definition, and, for a
target-reach goal, `targetReached` and `targetReach`. The importer validates
that evidence and publishes local cases or named gaps; it writes every field
above except `pathSetClosed`, which the campaign stamps on once the exploration
waves settle, matching each worklist report on `plannedOccurrenceId`.
`sharedExpressionTable` holds the hash-consed expression definitions the row's
own payloads refer to.

The composer consumes the closure-wide cases and the target predicate. Its
manifest reports consumer-boundary families, case-to-PC dependencies,
GuardedRead choices, field versions and reads, propagation gaps, and
final-status refusals. `FINAL_READY` means the emitted formula has all
selectors, path conditions, and propagated values needed for a sound SAT
witness. `FINAL_READY` is stage-local: it states that the formula is complete,
not that the campaign proved anything. Open path, propagation, and
bounded-candidate coverage remains telemetry and prevents only a closed UNSAT
conclusion. The generated SMT therefore follows the recorded causal chain
directly from explicit roots through propagated consumer expressions to the
target condition.

## The claim

`ClaimPolicy` decides what a campaign proved, once, and publishes that
decision inside the reach-condition report as `campaignClaim`. The EMIT stage
of `run_engine.sh` copies `claim`, `claimReason`, `blockers` and
`whyNotAccepted` from it into `result.json` and refuses to publish a result
from a reach report that carries no decision; it derives no verdict of its
own. `ClaimPolicy` can be replayed on any published pair of artifacts:

```bash
java -cp GraphChecker.jar edu.uva.liftlab.graphchecker.concolic.ClaimPolicy \
  --manifest schedule/final/candidate_composition_manifest.json \
  --reach schedule/final/z3-result.json \
  --mappings experiments/hadoop/<case>/communication-mappings.jsonl
```

A claim is accepted only when no blocker is named. `SAT_CANDIDATE` needs a
`REACHABLE` solver result, `UNSAT_CLOSED` an `UNREACHABLE` one; everything
else is `INCONCLUSIVE_PARTIAL` and every reason is one row of `blockers`
(`code`, `subject`, `detail`) and one line of `whyNotAccepted`.

| Blocker | Named when |
| --- | --- |
| `COMPOSER_NOT_FINAL_READY` | the manifest's `finalStatus` is not `FINAL_READY` |
| `COMPOSITION_GAPS_UNRESOLVED` | a Composer refusal or a solver gap is open -- the same rows EMIT counts in `gaps.json` |
| `DEGENERATE_ROOT_SPACE` | `degeneracyCheck` is `DEGENERATE_*`: the target provably ignores every root |
| `UNDECIDED_ROOT_SPACE` | `degeneracyCheck` is `UNDECIDED_*`: the question was never decided, so it is not answered |
| `TARGET_UNCONSTRAINED_BY_ROOTS` | a `REACHABLE` result where no single root flip changes satisfiability and no existential perturbation was rejected |
| `DECLARED_WIRE_FLOWS_UNREALIZED` | `communication-mappings.jsonl` declares a `WIRE_FLOW` the composition realized neither side of; the blocker names those flows |
| `WITNESS_UNINFORMATIVE` | the existential witness is every-zero, or identical under every satisfying valuation, while no perturbation of it was rejected |
| `SOLVER_UNDECIDED_VALUATIONS` | the solver returned neither sat nor unsat on an enumerated valuation |
| `UNSAT_CLOSURE_INCOMPLETE` | an `UNREACHABLE` result without closed selected-path authority |
| `NO_EXACT_REACHABILITY` | the solver stage reached no exact reachability decision |

The root-space rule is the one the previous jq gate did not have. A witness is
evidence only if the target predicate depends on a symbolic root: two
enumerated valuations that differ in exactly one Boolean root and disagree on
satisfiability show that dependence, and so does a rejected existential
perturbation. Without either, the formula and the roots are disconnected and
the witness names nothing, whatever the formula satisfies. That check does not
apply to an `UNREACHABLE` result, which has no witness to tie to a root.

`UNSAT_CLOSURE_INCOMPLETE` is required for `UNSAT_CLOSED` and for nothing
else: one connected SAT witness stays valid while sibling paths are open.

### Realizing a declared wire flow

A declared `WIRE_FLOW` becomes real in a composition by either of two
mechanisms, and both count:

- **an exchange port pair.** The runtime plan binds the flow's
  `XCH.<exchangeSiteKey>.<req|resp>.<flow>` ports to regions, `side: "IN"` for
  the consumer and `side: "OUT"` for the producer. The flow is realized when
  the composition drew a case, a guarded read or a witness from a region on
  each side. This is the mechanism by which the hdfs-17899 SASL
  `data-encryption-key-id` flow is real.
- **a consumer boundary family.** The Composer publishes these as
  `casePathConditionDependencies` rows of kind
  `CONSUMER_BOUNDARY_CASE_DEPENDENCY`, whose `boundaryKind` says whether the
  family came from an `RPC_ATTACH` or a `FIELD_READ`. A declared flow whose
  ports no plan bound is realized when the composition realized any such
  family, because nothing else can single that flow out.

`ClaimPolicy` reports one row per declared flow in `rootSpace.wireFlows`
(`flow`, `realized`, `mechanism`, and whether each side was realized), and the
blocker's `subject` is the comma-joined names of the flows that were not
realized -- a count cannot be acted on. Counting consumer boundary families
alone called the realized SASL flow of hdfs-17899-bug3 unrealized, and reading
them from the retired `symbolicPropagation` array reported none at all.
