# Causynth / concolic semantic boundary

Status: current V2 contract, 2026-07-26.

GraphChecker has two SMT consumers:

- `ConcolicConstraintSolver` solves one path-flip query and produces concrete
  replay assignments.
- `ConcolicSmtComposer` composes admitted region summaries and the consumer
  target condition.

Both consume the same custom-JDK expression IR. A missing semantic operation
adds a gap; it never becomes an unconstrained proof.

## Execution envelope

Dynamic capture is supported by the customized OpenJDK 8 Zero interpreter with
`-Xint`. C1/C2 compiled execution, reflection and native-call semantics are
outside the supported workload envelope.

One observed region invocation is a `RegionInstancePlan`. Its
`executionGoals` may contain output closure and target reach goals. Scheduler
projects goals into `ExecutionTask` rows identified by `taskId`.

## Scalars and control flow

Supported scalar relations include:

- boolean and Java integral primitives;
- exact Java `int`/`long` wrap for `+`, `-`, `*`, negation and `iinc`;
- binary32/binary64 arithmetic and comparisons represented with SMT FP;
- equality and ordered comparisons on compatible scalar sorts;
- reference null tests;
- supported String equality, contains, prefix, suffix, concatenation and
  emptiness;
- exact branch site, occurrence, concrete outcome and ordered condition-index
  ownership from the VM;
- fixed-bound `for`, `while`, and `do-while` control flow: at most eight body
  iterations, with a path cut immediately before a ninth body entry
  body can begin.

Unsupported operators or malformed width/type information produce a semantic
gap. In particular, a diagnostic term is not enough to make a candidate
complete.

## Output transformer

An output closure selects the inputs, branch sites and methods that can affect
one requested OUT. Every normal replay captures the value at region exit:

```text
path condition + final OUT expression
```

The VM does not preselect an assignment site. Multiple writes, branch-dependent
writes and no-write frame conditions therefore use the actual final value of
each replay. Normal-exit field capture reads the exact owner-field shadow:
an unchanged shadow preserves the pre-state expression, while a concrete
write produces the exact String/null/primitive constant for that path.
`RegionSummaryMerger` creates one guarded relation from the admitted path rows.

Demand-symbolized objects distinguish an absent field shadow from a field that
was concretely overwritten in the current activation. `putfield`/`putstatic`
leave an activation-local written marker when they clear a symbolic shadow;
ordinary and Zero fast `getfield` paths therefore cannot resurrect the old
pre-state expression after a concrete write.

Several requested ports belonging to one downstream demand are carried by one
joint goal and one shared path case. Independent summaries from different
producer paths are never combined as if they came from one invocation.

## ContainerRelation V2

Array and collection semantics are captured in the VM as one nested
`ContainerRelation` expression DAG. It is the only container IR and is lowered
by the shared `ContainerSmtCodec`.

Indexed state:

```text
STATE(receiver, length)
READ(state, index)
WRITE(state, index, value)
SIZE(state)
APPEND / INSERT / REMOVE / CLEAR
CONTAINS
ITERATOR / HAS_NEXT / NEXT
```

Associative state:

```text
STATE(receiver)
READ / PUT / REMOVE / REMOVE_AT / CLEAR
CONTAINS / SIZE / IS_EMPTY
ENTRY_VIEW / KEY_VIEW / VALUE_VIEW
ITERATOR / HAS_NEXT / NEXT / KEY / VALUE
```

Successful indexed access records its bounds. Concrete Map key/value results
record equality to the selected symbolic entry. Map insertion order and
position are part of `AssocState`, so removal compacts later iterator
positions.

Supported public operations are intentionally narrow:

- arrays: load, store and length;
- List: get, set, add/insert, remove by index, contains, size, isEmpty, clear,
  iterator/hasNext/next/remove;
- Queue: offer, poll, peek, element and no-argument remove;
- Set: add, remove, contains, size, isEmpty, clear, iterator;
- Map: get, put, remove by key, containsKey, size, isEmpty, clear and read-only
  entry/key/value iteration, iterator removal and backed-view clear.

Callback mutators (`compute*`, `merge`, `replaceAll`) and bulk mutation are not
modeled. Iterator `remove` and backed-view `clear` are the only supported
view mutations; other live-view mutations abort with one explicit reason.

There is no Java-side element ledger, engine array binding, Map-entry
projection or container-specific dynamic binding. Initial container state is
activation-local and relevance-first: only cells demanded by the failure slice
are retained, with a fixed capacity of eight unique cells per logical input
port. A ninth relevant cell is a materialization gap. A complete region-end
snapshot has no relevance proof, so a physical size above eight also fails
closed instead of truncating. Variable-length containers may still execute;
only their symbolic snapshot boundary is bounded.

## Replay admission

A SAT path-flip model is useful only when every controlled symbol has a real
materialization action. The worker then replays without forcing the branch and
admits the result only when the VM reports the intended:

```text
region + task + site + occurrence + ordered prefix + outcome
```

The importer performs one decoding/admission pass. It does not reconstruct
container snapshots or duplicate VM expression semantics.

## Final composition

Composer binds producer output ports to downstream input ports using proved
runtime read-from edges. It selects one joint producer case per region
instance, preserving correlations between outputs. A final candidate is
structurally ready only when:

- required output closures are complete;
- summaries are relationally complete;
- all required producer/read-from bindings resolve;
- expression lowering has no semantic gaps.

The final independent Z3 result remains a candidate analysis result; the
fixture gate checks its expected SAT/UNSAT profile.

## Engineering principle

Correctness is protected at the semantic boundaries above, not by duplicating
every field in multiple artifacts. Do not add compatibility fallbacks, mirror
booleans, repeated JSON validation or operation-specific Java binding schemas.
Prefer one canonical object, one decoder and one explicit unsupported boundary.
