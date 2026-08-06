# GraphChecker

GraphChecker starts from an annotated local failure, combines static analysis
with one concrete workload, and automatically constructs bounded concolic
tasks. Real custom-VM summaries are then composed into SMT and checked by Z3.

```text
annotated exception
  -> backward static candidate graph
  -> runtime activation binding
  -> runtime state/RPC evidence
  -> region templates, owners, inputs, outputs
  -> bounded ExecutionTask records
  -> custom-VM PathObservation records
  -> guarded RelationSummary records
  -> composed SMT
  -> Z3 sat | unsat
```

There is one production pipeline. Manual region lists, seed-variable lists,
single-instance selectors, handwritten summaries, and handwritten SMT are not
authorities.

## Static and runtime selection

Static analysis deliberately over-approximates from the failure predicate. It
finds candidate definitions, uses, calls, returns, field flow, control
dependence, and configured protocol boundaries. Runtime analysis then performs
two passes:

1. bind real execution-entry activation envelopes;
2. instrument only selected methods and record exact state, branch, owner/lane,
   and RPC lineage evidence.

The final dependency slice starts from a demanded output or target. It follows
the latest exact same-activation field write when one exists; otherwise the
field read becomes a region input. Static edges may cross an unobserved
alternate branch inside the runtime-selected method envelope. A branch operand
becomes symbolic only when its guard controls selected data flow.

This makes symbolization relevance-first. For `if (a > b)`, both operands are
symbolic when both are live dependencies; an unrelated operand remains
concrete. Container size and loop-continuation guards retain the observed seed
shape unless the failure slice itself depends on them. Element fields used by
semantic guards remain eligible symbolic inputs.

## Regions and occurrences

A region template is rooted at an execution-context authority such as
`main`, `Thread.run`, a task `run/call/execute`, or a configured server RPC
entry. Constructors and ordinary helpers are part of an owning region; they do
not become roots merely because they initialize a field.

One root activation is one region occurrence. Loop iterations inside it remain
inside that occurrence. The logical analysis unit is:

```text
region template x trace owner
```

Different owners are retained because they may represent different simulated
nodes. Repeated occurrences for the same owner share one logical VM summary;
composition instantiates that summary at exact occurrence ports by alpha
renaming. Transient JVM thread ids, object ids, ports, and root call ids are not
cross-execution identities.

`RuntimeTraceContext` propagates generic owner, lane, span, and RPC lineage from
thread creation and RPC boundaries. Protocol configuration declares which
client/server operations correspond. Once a configured RPC occurrence is
traced, GraphChecker does not require endpoint, payload, argument-value, or
object fingerprints to prove the same protocol edge.

## Bounded execution

Every `for`, `while`, and `do-while` in a task is governed by one CFG-loop
policy: at most eight loop-body iterations. A ninth body entry is cut; a loop
that exits at its guard after exactly eight bodies still returns normally.

Container materialization is also relevance-first. The current implementation
keeps up to thirty-two distinct failure-relevant cells per logical input port.
That number is a resource default, not a modeled collection length; if a real
slice needs more, the cap should be raised based on evidence. It was raised
from eight on exactly such evidence: the HDFS-11741 slice demands the
balancer's `DataEncryptionKey.encryptionKey`, a `byte[20]` whose bytes are
what the failure compares. Exceeding the cap fails closed instead of silently
discarding a relevant cell.

The custom VM owns scalar/container symbolic expressions and final region
outputs. Java planning code chooses what to execute and symbolize but does not
invent output relations. The VM records exact branch occurrences and region-end
expressions; the importer accepts only results matching the scheduled task and
bound contract.

## Shared state and interleaving

GraphChecker does not require a runtime happens-before or observed read-from
edge between different lanes. For a shared field:

- writes in one lane keep their program order;
- a same-lane writer precedes a later same-lane reader;
- writers from different lanes are placed in a bounded versioned channel;
- each consumer read chooses the initial version or one eligible preceding
  write;
- several writes to the same consumer input belong to one channel, not several
  independent choices.

This models bounded scheduling alternatives without symbolizing thread ids or
replaying every scheduler decision.

## Canonical artifacts

The main typed carriers are:

- `StaticRegion`: methods, ports, branches, and candidate edges;
- `OutputClosureContract`: demanded outputs and their backward slices;
- `RegionInstancePlan`: exact occurrences and closure goals;
- `ExecutionTask`: one bounded replay request;
- `PathObservation`: VM path condition, occurrences, and outputs;
- `RelationSummary`: guarded output cases;
- the composition manifest: exact summary/edge bindings and semantic gaps.

JSON is an artifact boundary, not a second semantic implementation. Unsupported
operators, ambiguous ports, incomplete output paths, a bound cut, or a missing
binding remain explicit gaps and prevent a trusted composition.

## Usage

The generic stage runner is documented in
[`experiments/generic/README.md`](experiments/generic/README.md). The HDFS-11741
automatic experiment is documented in
[`experiments/hdfs/hdfs-11741/README.md`](experiments/hdfs/hdfs-11741/README.md).

Build and run focused tests with:

```bash
mvn -q -DskipTests package
mvn -q test
experiments/generic/test_workflow.sh
```

## TODO

- Regenerate the HDFS-11741 target-first closure and run its real custom-VM
  concolic campaigns with region-level and path-level parallelism.
- Compose the resulting summaries, verify that `keyId` has no unconstrained
  producer gap, and confirm the bounded HDFS-11741 witness with Z3.
