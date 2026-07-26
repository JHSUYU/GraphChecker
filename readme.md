# GraphChecker

GraphChecker determines whether a target exception is reachable under Java
semantics, observed cross-thread ordering, and the complete output relations of
all producer regions.

It combines three sources of evidence:

1. static backward data-flow analysis;
2. one concrete seed execution; and
3. per-region concolic replay.

Together, these sources define `region.in -> region.out` relations. GraphChecker
composes the relations along the dynamic read-from graph and emits an SMT
formula for Z3.

The current implementation targets fixed-order shared-field RPC workloads. Two
or more producers may run concurrently, and a consumer reads each shared field
once after the producers finish. Thread scheduling itself is not modeled as a
symbolic variable.

## Architecture

```text
annotated target exception
        |
        v
SeedBackwardStaticAnalyzer
  static_dataflow_edges.jsonl
        |
        v
SymbolicRegionPlanner
  symbolic_regions.jsonl
  symbolic_region_edges.jsonl
        |
        v
instrumented seed execution
  causynth-trace.jsonl
        |
        v
RuntimeRegionPlanner
  RegionInstancePlan
        |
        v
ConcolicScheduler
  ExecutionTask
        |
        v
parallel custom-JDK workers
  PathObservation
        |
        v
ConcolicSummaryImporter + RegionPathWorklist
  closed RelationSummary
        |
        v
ConcolicSmtComposer
  candidate.smt2
        |
        v
Z3: sat | unsat
```

JSON is used only at artifact boundaries. The production pipeline uses the
following typed carriers:

- `StaticRegion`: a region's methods, input and output ports, branches, and
  canonical edges.
- `OutputClosureContract`: the outputs required by a downstream demand and the
  backward slice for each output.
- `RegionInstancePlan`: one concrete region invocation and its execution goals.
- `ExecutionTask`: one executable replay for a goal.
- `PathObservation`: the path condition, branch occurrences, and region-end
  outputs produced by one task.
- `RelationSummary`: guarded output cases for a single producer invocation.

## Regions, Activations, and Goals

A `regionInstanceId` identifies one activation envelope: a single concrete
region invocation, not an individual branch or output.

```json
{
  "regionInstanceId": "REGION.3@producer#call2",
  "closureGoals": [
    {
      "goalId": "GOAL.OUTPUT_RELATION...",
      "kind": "OUTPUT_RELATION_CLOSURE"
    },
    {
      "goalId": "GOAL.TARGET_REACH...",
      "kind": "TARGET_REACH_CLOSURE"
    }
  ]
}
```

The pair `(regionInstanceId, goalId)` identifies a semantic exploration
campaign. A `taskId` identifies one custom-JDK execution within that campaign.
Branch flips are path-enumeration tasks inside an output campaign rather than
separate activations.

## Output Closure

For every output requested by a downstream consumer, the planner computes a
backward dependency closure:

```text
requested OUT
  -> input ports
  -> relevant branch sites
  -> methods
  -> causal edge IDs
  -> one region-end capture endpoint
```

Code that affects only unrelated branches, counters, or debug fields is excluded
from the output slice. The path worklist flips only branches that occur in the
dynamic or static slice of the requested output.

### Joint outputs

A downstream demand may request multiple output ports from the same producer
invocation:

```text
requested outputs = {outX, outY}
joint execution scope = slice(outX) union slice(outY)
```

Each output retains its own slice and capture endpoint, while all outputs share
one path-condition campaign. Every merged case contains the complete set of
outputs:

```text
case C0:
  guard = ...
  outX = ...
  outY = ...
```

The composer selects a complete case atomically. It never combines outputs from
different replays, input assignments, or producer instances. If any member of a
joint demand is incomplete, the entire demand fails closed.

## Region-End Output Semantics

A field output is not tied to a particular assignment site or to an occurrence
in the seed trace. At every normal region exit, the custom JDK reads the field's
current symbolic expression.

For example:

```java
if (condition) {
    b = x;
} else {
    b = y;
}
```

The two replay paths produce:

```text
condition   -> b_out = x
!condition  -> b_out = y
```

After merging:

```text
b_out = ite(condition, x, y)
```

If a path does not write `b`, the exit read yields `b_in`, which provides the
frame condition. If a path writes `b` multiple times, the exit read yields the
expression after the last dynamic write.

Normal return values are captured directly at the root exit. Exceptional paths
do not have ordinary outputs and are modeled separately from the normal output
relation.

## Symbolic Containers

Arrays, maps, lists, sets, queues, and collection views are modeled inside the
custom JDK. The planner does not enumerate container elements, entries, or
snapshots. Instead, each activation maintains an identity-based shadow state and
emits a single `ContainerRelation` expression DAG:

```text
Java object identity
      |
      v
activation-local shadow state
      |
      +-- READ / WRITE
      +-- SIZE / IS_EMPTY / CONTAINS
      +-- APPEND / INSERT / REMOVE / CLEAR
      +-- VIEW / ITERATOR / NEXT / KEY / VALUE
      |
      v
region-end ContainerRelation
      |
      v
shared ContainerSmtCodec
```

Both the path solver and the final composer use `ContainerSmtCodec`. This keeps
the SMT encoding of selection, storage, size, map presence and ordering, Java
booleans, strings, and integral widths consistent across both stages.

### Container IR

The VM-serialized expression is the canonical container IR:

```json
{
  "_type": "ContainerRelation",
  "shape": "ASSOCIATIVE",
  "operation": "PUT",
  "receiver": { "... previous state ..." },
  "arguments": [{ "... key ..." }, { "... value ..." }]
}
```

### State shapes

`IndexedState` represents arrays, lists, and queues:

```text
size: Int
elements: Array<Int, Value>
```

`AssocState` represents maps and sets:

```text
size: Int
present: Array<Value, Bool>
values: Array<Value, Value>
order: Array<Int, Value>
position: Array<Value, Int>
```

`Value` covers primitives, strings, and references. Java `int` and `long` widths
are preserved by `ContainerSmtCodec.Term`; arithmetic uses
`java_int_wrap` and `java_long_wrap` rather than unbounded mathematical integer
semantics.

### Initial state

Container state is constructed lazily instead of from a full snapshot:

- An existing array has its concrete runtime length.
- An array created as `new T[n]` inside a region carries symbolic length `n`.
- A successful indexed read, write, or iterator step adds
  `0 <= index < size`.
- Map, list, and set size, lookup, membership, iterator key, and iterator value
  constraints are added from the concrete execution as needed.
- Elements outside the current output closure are neither enumerated nor written
  to artifacts.

Containers may therefore undergo symbolic mutations that change their size
inside a region. Existing Java arrays retain their original length, while newly
allocated arrays may have a symbolic length.

### Supported operations

- Array: length, load, and store.
- List: `get`, `set`, `add`, insertion, removal by index, `contains`, `size`,
  `isEmpty`, `clear`, and iteration.
- Queue: `offer`, `poll`, `peek`, `element`, and `remove()`.
- Set: `add`, `remove`, `contains`, `size`, `isEmpty`, `clear`, and iteration.
- Map: `get`, `put`, removal by key, `containsKey`, `size`, `isEmpty`, and
  `clear`.
- Map views: `entrySet`, `keySet`, `values`, iteration, `next`, `getKey`, and
  `getValue`.

The following operations are currently unsupported and fail closed:

- `Map.putAll`, `putIfAbsent`, `replace`, `replaceAll`, `compute*`, and `merge`;
- `Map.remove(key, value)`;
- `List.remove(object)` and `listIterator(int)`;
- `Iterator.remove` and mutations through collection views;
- reflection, native container APIs, and direct or off-heap buffers;
- semantics that depend on HashMap buckets, TreeMap comparators, or other JVM
  implementation details.

### Container outputs

Primitive fields, ordinary object fields, and container fields use the same
region-end capture mechanism:

```text
read the exact field path at normal exit
  -> System.getSymbolicExpression(value)
  -> scalar expression or final ContainerRelation
```

The capture is independent of the last mutation or assignment site. A container
with no mutations yields its pre-state; a container with multiple mutations
yields its final shadow state.

## Parallel Concolic Exploration

Each custom-JDK process maintains a single symbolic context. Parallelism occurs
across isolated worker processes:

```text
shared concurrent worklist
  -> worker JVM 1: replay query A
  -> worker JVM 2: replay query B
  -> ...
  -> worker JVM N: replay query N
```

Every worker has an independent custom JDK, heap, path condition, and output
file. The coordinator deduplicates tasks with a canonical query key, merges new
paths in waves, and then generates the next set of branch flips. Only one result
for a given query is accepted.

Worker scheduling does not affect branch relevance, query identity, closure
membership, merged case identity, or the final SAT/UNSAT formula.

## Composition Invariants

The final SMT candidate preserves the semantic lineage needed to justify its
result:

- stable identity for the annotated target exception;
- the backward slice and causal edge IDs for every output;
- branch witnesses, exact path-condition events, and occurrences;
- `regionInstanceId`, `goalId`, `taskId`, and `queryKey` lineage;
- shared-field writer and reader order;
- receiver and value identities with read-from evidence;
- correlations between outputs in a joint case;
- relation completeness and any unresolved gaps; and
- a SHA-256 digest of the composed artifact.

An SMT candidate is ready only when every required relation is complete and no
composition gaps remain.
