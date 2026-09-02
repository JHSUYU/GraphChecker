# Concolic integration contract

This is the current boundary between instrumented Java code, GraphChecker
runtime, and the custom JDK. The main workflow is described in
[README.md](../README.md).

## Execution identity

A worker task names one region occurrence and one goal:

```json
{
  "taskId": "TASK.<query>",
  "goalId": "GOAL.OUTPUT_RELATION.<demand>",
  "goalKind": "OUTPUT_RELATION_CLOSURE",
  "regionId": "REGION.3",
  "sourceKey": "node#epoch0",
  "occurrenceId": "node#epoch0/region/REGION.3#1",
  "rootSelector": {"method": "<Producer: int compute()>", "ordinal": 1}
}
```

`goalKind` is `OUTPUT_RELATION_CLOSURE` or `TARGET_REACH_CLOSURE`. A
synchronous call does not split its caller into another region occurrence.

## Node and request context

The workload registers a stable node owner with `registerSource`, may bind
handler aliases to it, and starts each external operation with
`beginSourceRequest`. The returned request scope is ended in `finally`.

At a message boundary:

```text
outboundExchange(...) -> strict trace-context header
inboundExchange(header, ...) -> scope token
endInboundExchange(scope token)
```

The header carries the sender span, source identity, and request flow. The
receiver installs them only for the inbound scope. `recordExchange` records a
transport-neutral SEND or RECEIVE leg with REQUEST or RESPONSE half.
Correlation and attempt identifiers describe topology; they never recover
context or symbolic values.

## Declared wire values

A `WIRE_FLOW` has one producer, one consumer, one Java type, and one direction.
Each endpoint uses exactly one capture kind:

```text
METHOD_PARAMETER  method + parameter index
METHOD_RETURN     method return
CALL_ARGUMENT     method + exact call + argument index
CALL_RETURN       method + exact call return
```

The runtime plan lowers a producer to an OUT handoff and a consumer to an IN
handoff. Instrumentation has one operation per side:

```text
exportCommunicationLeaf(portId, carrier, field, descriptor)
attachCommunicationLeaf(portId, carrier, field, descriptor)
```

The producer stages `{portId, VM handle, producer task, producer occurrence}`
in the next symbolic message envelope. The concrete transport drains that
envelope into a header before sending and installs the exact header before the
receiver capture. An IN capture consumes only its declared port from the
installed message. Missing, duplicate, or malformed entries fail closed.

A VM handle is valid only inside its workload JVM/session. The envelope does
not turn it into a cross-process expression format. Request and response
messages otherwise use the same mechanism.

## Region runtime

`ExecutionTask.inputActions` is the sole input-materialization catalog. Runtime
object identity locates values only within the active task and never becomes a
cross-run query identity. Selected branches use exact VM events and condition
indices; predicates are read back by range. Runtime bookkeeping pauses path
condition collection so tracing code does not alter the program predicate.

Normal exits capture declared scalar, field, and container outputs. Exceptional
exits do not fabricate normal output captures. Container state is owned by the
custom VM; Java does not maintain a second symbolic container ledger.

## Result and isolation

Each task emits one `CONCOLIC_REGION_RESULT` containing task identity, exit
kind, unresolved/materialized inputs, branch mappings, output captures, root
output expression, VM handoff evidence, and engine summary. The importer owns
admission and publishes explicit diagnostics for missing inputs, invalid branch
events, unavailable expressions, or absent message leaves.

One custom-JDK worker owns one fresh workload session. Related region contexts
may share that session's symbolic heap, message broker, and event ledger across
threads. Independent obligations run in separate JVM workers and merge only
normalized cases and topology deltas, never heap state or raw event IDs.
