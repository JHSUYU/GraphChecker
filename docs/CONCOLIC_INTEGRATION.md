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
witness. Open path, propagation, and bounded-candidate coverage remains
telemetry and prevents only a closed UNSAT conclusion. The generated SMT
therefore follows the recorded causal chain directly from explicit roots
through propagated consumer expressions to the target condition.
