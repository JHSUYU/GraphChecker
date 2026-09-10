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
  "taskId": "TASK.<query>",
  "goalId": "GOAL.REGION_PATH.<occurrence>",
  "goalKind": "REGION_PATH_CLOSURE",
  "regionId": "REGION.3",
  "sourceKey": "node#epoch0",
  "occurrenceId": "node#epoch0/region/REGION.3#1",
  "rootSelector": {"method": "<Worker: int compute()>", "ordinal": 1}
}
```

`goalKind` is `REGION_PATH_CLOSURE` or `TARGET_REACH_CLOSURE`. All members in
the selected causal closure form one linked replay bundle. They execute in one
workload JVM so native expression handles, shared-state versions, and boundary
identities remain valid across the whole causal chain.

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
exportCommunicationLeaf(siteId, carrier, field, descriptor)
attachCommunicationLeaf(siteId, carrier, field, descriptor)
```

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

All planners in one global wave read the same immutable summary snapshot. The
campaign waits for the wave, imports its new cases, then publishes one larger
snapshot for the next wave. A region is closed only at this closure-wide fixed
point. A topology change quarantines the complete replay bundle and starts a
new topology epoch; cases from different epochs are never merged.

Retained loops use their configured finite unroll as one region-local path.
Repeated transfers and shared-state accesses keep their loop/boundary ordinal
and candidate writer versions. Loop iterations do not become separate
symbolic-merge cases merely because they repeat.

## Result contract

Each region result contains task and occurrence identity, exit kind, explicit
symbolic-root evidence, its local path condition, consumer-boundary handoffs,
shared-state GuardedRead candidate snapshots, retained-loop observations, and
topology observations. The importer validates that evidence and publishes
local cases or named gaps.

The composer consumes the closure-wide cases and the target predicate. Its
manifest reports consumer-boundary families, case-to-PC dependencies,
GuardedRead choices, field versions and reads, propagation gaps, and
final-status refusals. `FINAL_READY` means the emitted formula has all
selectors, path conditions, and propagated values needed for a sound SAT
witness. Open path, propagation, and bounded-candidate coverage remains
telemetry and prevents only a closed UNSAT conclusion. The generated SMT
therefore follows the recorded causal chain directly from explicit roots
through propagated consumer expressions to the target condition.
