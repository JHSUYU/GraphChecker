# Concolic Region Integration Contract

Status: the maintained generic workflow produces hash-bound, independently
Z3-checked candidate models for the six reference profiles. Natural replay
promotion remains the explicit final TODO.

This document defines the project-independent contract between GraphChecker's
static/runtime analysis, Soot instrumentation, the custom OpenJDK concolic
engine, producer scheduling, guarded merging, and SMT verification. The
top-level `readme.md` is the authoritative handoff and experiment-status file.

## 1. Research scope

This is academic software engineering and program analysis. The maintained
validation scope is the local three-thread RPC fixture matrix, executed with
the repository's custom OpenJDK and Z3. Application topology, target sites,
and semantics must come from program evidence and workflow configuration;
there is no domain-specific composition adapter.

## 2. Core invariants

1. Every analyzed unit is a `REGION.*`; no domain-specific region types exist.
2. A region has one of two capture goals: `TARGET_BRANCH` or `OUTPUT_CLOSURE`.
3. The target goal captures one exact branch observation and derives
   one immutable `BranchReplayContract` plus `SolverPathContext` for candidate
   composition. The maintained workflow does not replay the target.
4. An output goal is admitted only through real record/solve/replay/import
   evidence and is merged only after its bounded path worklist closes.
5. Input models may change real program inputs. Branch outcomes remain
   read-only runtime observations.
6. Static dataflow discovers work but does not establish runtime value
   semantics.
7. Cross-region equality requires a complete, invocation-matched runtime value
   fingerprint. Shared state requires a concrete write/read witness.
8. Manual transport mappings and domain semantic adapters are not inputs to
   the maintained workflow.
9. Any missing evidence, unsupported expression, bound, cycle, or incomplete
    admission remains an explicit gap.

`TARGET_BRANCH` and `OUTPUT_CLOSURE` are the only accepted capture goals. Old
goal aliases are rejected instead of being translated.

## 3. Static region IR

`symbolic_regions.jsonl` contains project-independent region schemas. A
representative row is:

```json
{
  "schemaVersion": 1,
  "regionId": "REGION.17",
  "rootMethod": "<owner.Type: Ret method(Arg)>",
  "methods": ["<owner.Type: Ret method(Arg)>"],
  "symbolicInputs": [
    {
      "portId": "REGION.17.in.0",
      "cell": "<owner.Type: int field>"
    }
  ],
  "outputs": [
    {
      "portId": "REGION.17.out.0",
      "cell": "<owner.Type: java.util.Map state>",
      "kind": "HEAP_STATE"
    }
  ],
  "outputSlices": [
    {
      "outputPort": "REGION.17.out.0",
      "inputPorts": ["REGION.17.in.0"],
      "methods": ["..."],
      "sites": ["<owner.Type: Ret method(Arg)>#u12"],
      "causalEdgeIds": ["EDGE.42"],
      "complete": true
    }
  ]
}
```

An output slice is a static over-approximation. `causalEdgeIds` refer to the
single canonical edge table in `static_dataflow_edges.jsonl`; a slice does not
embed another copy of those rows or persist derived edge/count aliases.
Runtime import still has to prove that every required input was actually
symbolized.

## 4. Runtime activation and value evidence

`concolic_activation_plan.jsonl` identifies a concrete region invocation and
its observed branches. Stable site identity is `method signature + #uN`; branch
occurrence disambiguates loops and repeated calls.

Value fingerprints are bounded canonical object-graph serializations. The
trace stores only SHA-256, completeness, node count, and failure reason. A
fingerprint-bound or reflection failure makes an equality non-composable. The
soundness assumption for digest equality is SHA-256 collision resistance.

`runtime_region_edge_validation.jsonl` schema 2 stores one runtime `state`
and one `bindings` array per canonical static endpoint:

```json
{
  "schemaVersion": 2,
  "kind": "RUNTIME_REGION_EDGE_EVIDENCE",
  "edgeId": "REGION_EDGE.4",
  "fromRegion": "REGION.17",
  "toRegion": "REGION.2",
  "transportKind": "SHARED_STATE",
  "fromPort": "REGION.17.out.0",
  "toPort": "REGION.2.in.1",
  "requiresOrder": true,
  "requiresObjectIdentity": true,
  "state": "CONFIRMED_READ_FROM",
  "bindings": [{
    "writeEvidenceKind": "FIELD_ASSIGNMENT",
    "writeEvidenceAuthority": "RUNTIME_EXACT_FIELD_WRITE_EVENT_V1",
    "orderAuthority": "GLOBAL_RECORDER_MONOTONIC_SEQUENCE_ORDER_V1",
    "orderConfirmed": true,
    "fieldReceiverIdentityConfirmed": true,
    "receiverObjectId": 41,
    "writerEventSeq": 120,
    "readerEventSeq": 137
  }]
}
```

Conditional static mapping/projection metadata may be retained when needed to
resolve a canonical output. Derived admission booleans, duplicate relation
fields, counts, and diagnostic copies of the same endpoint pair are not
persisted. The two composable states are:

```text
CONFIRMED_RUNTIME_VALUE_EQUALITY:
  matching concrete region instances
  complete endpoint fingerprints
  equal digest
  ordered endpoint evidence in each binding

CONFIRMED_READ_FROM:
  concrete field/container mutation
  concrete later read
  receiver identity
  write/read sequence and ordering
```

An observed call order without those witnesses is insufficient.
`AutomaticRegionEdge` derives the relation from the state and validates every
binding as the shared fail-closed gate.

`ConcolicScheduler` rebuilds a target activation's equality classes from only
the witness-bearing relations selected for that concrete region instance. A
global static equality class is never reused blindly for another invocation.

## 5. Capture goals

### 5.1 `TARGET_BRANCH`

The target activation is executed once without assignments or branch
overrides. The importer records that unforced observation, and the scheduler
derives one candidate query from its typed `BranchWitness`:

```text
ordered source BranchWitness prefix
AND the flipped source witness predicate
AND positioned SolverPathContext constraints
```

Only `VM_PC` witnesses may form a flip contract. An exact VM branch event with
no path condition remains observation-only and cannot be converted into a
synthetic condition or alternate certificate. In the maintained workflow the target
contract is consumed as the fatal candidate condition; it is not turned into
a target input model and is not replayed. Observing the annotated exception
naturally under a selected full-workload model remains the final TODO.

### 5.2 `OUTPUT_CLOSURE`

The scheduler resolves the requested output, loads its static backward slice,
and prepares executable materializations with the same definition index used
for target scheduling. The runtime activation's `symbolize` array is the input
declaration authority; the scheduler re-derives executable `materializations`
from those declarations, so pre-existing materializations cannot authorize
themselves. A seed capture contains no forced branch.

Every output activation must carry the canonical schema-v1 `outputClosure`.
Each demanded member owns its own slice and capture ledger; when capture is
required that member must declare both `captureBindingsRequired=true` and
`captureBindingsComplete=true`. A stale singular `requestedOutput*` template,
an incomplete member, or occurrence `0` cannot bypass that gate.
Failure leaves `schedulerReady=false` and `symbolicReady=false`.

The importer rejects relational completeness unless every slice input has a
runtime symbolization event. A structured symbol such as
`REGION.8.in.2.someField` may satisfy its parent port `REGION.8.in.2`; unrelated
symbols cannot.

## 6. Summary IR

An admitted path summary keeps the canonical relation data used downstream.
A representative witnessed branch row is:

```json
{
  "summaryId": "SUMMARY.REGION.17.<stable>",
  "regionId": "REGION.17",
  "activationId": "ACT.OUTPUT.<stable>",
  "captureGoal": {"kind": "OUTPUT_CLOSURE"},
  "outputClosure": {
    "schemaVersion": 1,
    "kind": "OUTPUT_CLOSURE_CONTRACT",
    "producer": {
      "regionId": "REGION.17",
      "regionInstanceId": "REGION.17@test#call7",
      "rootCallId": 7
    },
    "members": [{
      "output": {
        "portId": "REGION.17.out.0",
        "cell": "<example.Region: int value>",
        "kind": "SINK_STATE",
        "javaTypeDescriptor": "I",
        "selectionAuthority": "CONFIRMED_READ_FROM_EDGE"
      },
      "slice": {
        "inputPorts": ["REGION.17.in.0"],
        "sites": ["<example.Region: void run()>#u12"],
        "staticSites": ["<example.Region: void run()>#u12"],
        "methods": ["<example.Region: void run()>"],
        "causalEdgeIds": ["DF.17"],
        "captureBindingsRequired": true,
        "captureBindingsComplete": true,
        "captureBindings": [{
          "captureKind": "FIELD_ASSIGNMENT_RHS",
          "captureBindingId": "REGION.17.out.0.capture.0",
          "outputPort": "REGION.17.out.0",
          "outputCell": "<example.Region: int value>",
          "method": "<example.Region: void run()>",
          "siteId": "<example.Region: void run()>#u12",
          "unitIndex": 12,
          "occurrence": 1
        }]
      }
    }]
  },
  "pathCondition": [{"_type": "BinaryExpression"}],
  "branchMappings": [
    {
      "witness": {
        "schemaVersion": 1,
        "kind": "BINARY_BRANCH_WITNESS",
        "site": {
          "siteId": "<owner.Type: Ret method(Arg)>#u12",
          "method": "<owner.Type: Ret method(Arg)>",
          "unitIndex": 12,
          "occurrence": 1
        },
        "sourceTakenOutcome": true,
        "sourceSatisfiedPredicate": {"_type": "BinaryExpression"},
        "vmPcIndex": 0,
        "predicateNormalization": "IDENTITY"
      },
      "summaryPcIndex": 0,
      "policy": "EXPLORE"
    }
  ],
  "outputExpressions": {
    "REGION.17.out.0": {
      "_type": "ConstExpr",
      "_java_type": "I",
      "_exp": "Y_I_17"
    }
  },
  "heapStateInitializers": [],
  "heapEffects": [],
  "relationallyComplete": true
}
```

`SummaryBranchMapping` has exactly one authority: either
`{witness, summaryPcIndex, policy}` or
`{concreteObservation, policy}` for an exact VM-attested binary event that
added no path-condition entry. It does not duplicate site, outcome, condition,
override, or runtime-event aliases at the mapping root. Completeness details
remain importer diagnostics; the canonical summary persists the one aggregate
`relationallyComplete` gate instead of parallel validity,
materialization-admission, and heap-model completeness mirrors.

Map mutations are ordered state transitions such as `MAP_PUT`, `MAP_REMOVE`,
`MAP_CLEAR`, or `MAP_PUT_ALL`. Each effect has pre/post state IDs, ordinals,
input/output ports, and expression operands. A fresh empty map requires a
specific static allocation witness plus runtime receiver binding; it is not a
domain assumption.

Direct `Map.remove(key)` is normalized through its ordinary VM
`MethodExpression`. The maintained contract deliberately does not support an
`Iterator.remove()` mutation. Its exact static causal-edge `invoke` is
recognized, but the VM `HashMap.removeNode` evidence cannot prove the
corresponding application call and current entry. The importer reports
`INCOMPLETE_ITERATOR_REMOVE_APPLICATION_PROVENANCE`, emits no admitted
transformer, sets `relationallyComplete=false`, and never reconstructs the
mutation from an iterator side channel. Non-mutating iterator entry reads,
finite map snapshots, and nested value-field bindings remain supported.

## 7. Worklists

### 7.1 Upstream topology resolution

There is no persisted recursive region worklist and no summary cache.
Runtime-confirmed `READ_FROM`/`EQUALITY` bindings identify the bounded upstream
regions required by the fatal query. The composer resolves that graph directly
from static regions, runtime bindings, and complete merged producer summaries.
Missing, ambiguous, unobserved, cyclic, or out-of-bound dependencies become
composition gaps; no discovery activation or static fallback is synthesized.
Multiple confirmed writes to one read form guarded alternatives rather than an
arbitrary choice.

### 7.2 Producer path worklist

Only `relationallyComplete=true` output summaries are eligible. For each
output-relevant witnessed branch, latest first,
`BranchReplayContract.flip()` constructs:

```text
orderedPrefix := earlier BranchWitness values
source        := selected BranchWitness
required      := complement(source.sourceSatisfiedPredicate)
suffixPolicy  := DROP_SOURCE_SUFFIX
```

`SolverPathContext` separately retains positioned `_array_expr` and
`MethodExpression` constraints before the selected branch. Both values are
immutable typed JSON without a self-hash. The stable task key is computed from
their canonical content, the output demand key, the full closure fingerprint,
and semantic branch identity; it excludes dynamic activation IDs. Terminal
SAT/UNSAT/materialization records prevent duplicate work. Unwitnessed Boolean
conditions are gaps.

## 8. Producer constraint solve and replay

`ConcolicConstraintSolver` lowers the expression IR to SMT-LIB, invokes Z3, and
returns materializable assignments. The important result is the selected path
and symbolic relation, not a displayed concrete model.

For producer output closure, the replay activation carries assignments and the
same immutable replay contract. The runtime reports applied assignment count
and actual branch witnesses; branch outcomes are observations, not replay
inputs.

The importer is the only replay-admission call boundary. Its compact
`ReplayAdmission` checks:

```text
all assignments applied
expected branch prefix observed naturally
selected site/occurrence has the desired outcome
```

For dynamic Map.Entry and array/container assignments, the retained model
admission additionally checks fresh activation-local rebinding; object tokens
are never compared across executions. Only then may the importer append the
canonical summary and let the path worklist mark the task covered. The former
standalone path replay verifier and its scratch manifest no longer exist.

## 9. Guarded merging

`RegionSummaryMerger` groups path summaries by exact producer invocation,
canonical output demand, and closure fingerprint. Each case carries its own
path-condition guard, the complete demanded output-expression set, heap
initializers, and heap effects. The merge is complete only when the path
worklist itself is closed without gaps.

Unexplored or rejected paths are never treated as infeasible. An incomplete
merge may be emitted for diagnostics, but the composer marks it incomplete.

## 10. Maintained workload orchestration

The generic workload driver implements:

```text
resolve annotation target and static slice
collect runtime activations and edge evidence
capture one unforced target observation and candidate query
for each producer, in isolated processes:
  capture an unforced output seed
  repeat plan -> solve -> input-only replay -> import within bounds
  stop only at CLOSED with no gaps
  merge admitted paths into one guarded relation
compose producer relations with the target query
run Z3 and Boolean-root projection
write the five terminal candidate artifacts
```

The execution backend receives file locations and environment variables only.
The selected generic workflow performs activation-specific Soot
instrumentation, runs its configured local workload on the custom JDK, and
lets the importer normalize the result. The former all-purpose Java campaign
runner and its compatibility state machine are not part of this workflow.

After a successful non-debug producer campaign, the retained evidence is:

```text
observed_path_summaries.jsonl
raw_results.jsonl
path_exploration_records.jsonl
region_path_closure.json
merged_region_summaries.jsonl
```

Intermediate planner/runtime output lives in a single `current` scratch
directory and is deleted after each accepted step. Numbered
`iteration-NNNN` directories are retained only when
`GRAPH_CHECKER_DEBUG=true`; they are diagnostic history, not workflow inputs.
No cache directory or recursive-worklist artifact is produced.

## 11. SMT composition

`ConcolicSmtComposer` consumes only:

```text
canonical fatal BranchReplayContract and SolverPathContext
the observed target summary selected by that contract
complete/guarded region summaries
target-instance-selected equality/read-from bindings
common region/port schemas
```

It does not read an external semantic-contract registry. Legacy summaries
carrying `protocolModel` or embedded `explicitContracts` are rejected as
incomplete.

Structural composition succeeds only if there are no missing summaries,
incomplete relations, unsupported expressions, or unbound ports. The result is
still `CANDIDATE_ONLY`: promotion by a natural, injection-free target replay is
the explicit remaining TODO.

The composition manifest is the single cross-file artifact authority. It
fingerprints the actual CLI inputs and emitted SMT; after the relationship
catalog is written, the same manifest binds that artifact as well. It does not
require a second derived binding id or reciprocal field-by-field certificate.

Each `caseProjectionCatalog` row is also compact:

```json
{
  "caseId": "CASE.0123",
  "selectorTerm": "case_selector__...",
  "bindings": [
    {
      "portId": "REGION.17.in.0",
      "term": "sym__port__REGION_17_in_0__int",
      "bridgeAssertionName": "bridge__..."
    }
  ]
}
```

String bindings additionally carry `nullnessTerm`. Static port schemas recover
the sort; the row does not copy the full guard formula, assertion text/hash,
runtime binding object, source summary, or dynamic metadata.

The schema-2 relationship catalog has exactly four top-level fields:
`schemaVersion`, `kind`, `trustState=CANDIDATE_ONLY`, and `relationships`.
Each relationship is a candidate projection; there is no parallel eligibility
flag or duplicated composition binding. No solver result promotes a
relationship to trusted evidence. A future natural, injection-free target
replay may upgrade a candidate only after observing the annotated target under
the candidate model; that trust-promotion stage remains an explicit TODO.

The terminal workflow output is exactly:

```text
candidate.smt2
candidate_composition_manifest.json
symbolic_relationship_candidates.json
candidate_boolean_model.json
candidate_result_manifest.json
```

The three schema-2 reports use `state=CANDIDATE_READY` (or
`CANDIDATE_WITH_GAPS` before terminal admission),
`trustState=CANDIDATE_ONLY`, and the Boolean/result reports use
`reachability=REACHABLE|UNREACHABLE`. Old `status`, `complete`,
verification-eligibility, and natural-replay-implemented flags are not part of
the compact protocol.

## 12. Verification

```bash
mvn -q test
mvn -q package -DskipTests
experiments/generic/test_workflow.sh
```

A nonzero workflow/proof exit caused by explicit gaps is an expected
fail-closed state; the JSON manifest is authoritative.
