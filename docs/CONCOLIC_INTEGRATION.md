# Concolic Region Integration Contract

Status: the maintained generic workflow produces hash-bound, independently
Z3-checked candidate models for the six reference profiles. Natural replay
promotion remains the explicit final TODO.

This document defines the project-independent contract between GraphChecker's
static/runtime analysis, Soot instrumentation, the custom OpenJDK concolic
engine, recursive scheduling, guarded merging, and SMT verification. The
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
3. The target goal captures one exact branch, then replays a single immutable
   `BranchReplayContract`; it does not need comprehensive path enumeration.
4. An output goal is admitted only through real record/solve/replay/import
   evidence and is merged only after its bounded path worklist closes.
5. Input models may change real program inputs. Branch overrides never count as
   automatic concolic evidence.
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
      "complete": true
    }
  ]
}
```

An output slice is a static over-approximation. Runtime import still has to
prove that every required input was actually symbolized.

## 4. Runtime activation and value evidence

`concolic_activation_plan.jsonl` identifies a concrete region invocation and
its observed branches. Stable site identity is `method signature + #uN`; branch
occurrence disambiguates loops and repeated calls.

Value fingerprints are bounded canonical object-graph serializations. The
trace stores only SHA-256, completeness, node count, and failure reason. A
fingerprint-bound or reflection failure makes an equality non-composable. The
soundness assumption for digest equality is SHA-256 collision resistance.

Runtime edge validation has two authorities:

```text
EQUALITY:
  matching concrete region instances
  complete endpoint fingerprints
  equal digest
  valueEqualityObserved = true
  valueEqualityAuthority = RUNTIME_COMPLETE_VALUE_FINGERPRINT

READ_FROM:
  concrete field/container mutation
  concrete later read
  receiver identity
  write/read sequence and ordering
  status = CONFIRMED_READ_FROM
```

An observed call order without those witnesses is insufficient.
`AutomaticRegionEdge` is the shared fail-closed gate.

`ConcolicScheduler` rebuilds a target activation's equality classes from only
the witness-bearing relations selected for that concrete region instance. A
global static equality class is never reused blindly for another invocation.

## 5. Capture goals

### 5.1 `TARGET_BRANCH`

The scheduler selects an observed fatal branch and creates one
`BranchReplayContract`:

```text
ordered source BranchWitness prefix
AND the flipped source witness predicate
```

The solver output is converted to concrete materialization actions. A replay is
admitted only if:

```text
all expected actions were applied
no branch override was used
the concrete target site/occurrence reached the desired outcome
the expected exception appears in the exception chain
```

Only `VM_PC` witnesses are replayable. An exact VM branch event with no path
condition remains observation-only and cannot be converted into a synthetic
condition or alternate certificate. This goal deliberately stops after the
contract is validated.

### 5.2 `OUTPUT_CLOSURE`

The scheduler resolves the requested output, loads its static backward slice,
and prepares executable materializations with the same definition index used
for target scheduling. The runtime activation's `symbolize` array is the input
declaration authority; the scheduler re-derives executable `materializations`
from those declarations, so pre-existing materializations cannot authorize
themselves. A seed capture contains no forced branch.

Every output closure must explicitly carry
`requestedOutputCaptureComplete=true`. A legacy transition template,
occurrence `0`, or `TRANSITION_DISCOVERY_ONLY` goal cannot bypass that gate.
Failure leaves `schedulerReady=false` and `symbolicReady=false`.

The importer rejects relational completeness unless every slice input has a
runtime symbolization event. A structured symbol such as
`REGION.8.in.2.someField` may satisfy its parent port `REGION.8.in.2`; unrelated
symbols cannot.

## 6. Summary IR

An admitted path summary contains:

```json
{
  "summaryId": "SUMMARY.REGION.17.<stable>",
  "regionId": "REGION.17",
  "activationId": "ACT.OUTPUT.<stable>",
  "captureGoal": {"kind": "OUTPUT_CLOSURE"},
  "requestedOutput": {"portId": "REGION.17.out.0"},
  "pathCondition": [{"_type": "BinaryExpression"}],
  "branchMappings": [
    {
      "siteId": "<owner.Type: Ret method(Arg)>#u12",
      "occurrence": 1,
      "conditionIndex": 0,
      "outcome": true,
      "overrideApplied": false
    }
  ],
  "outputExpressions": {},
  "heapStateInitializers": [],
  "heapEffects": [],
  "inputMaterializationAdmission": {"complete": true},
  "heapEffectModel": {"complete": true},
  "relationallyComplete": true,
  "branchOverrideUsed": false,
  "valid": true
}
```

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
`INCOMPLETE_ITERATOR_REMOVE_APPLICATION_PROVENANCE`, sets
`heapEffectModel.complete=false` and `relationallyComplete=false`, and never
reconstructs the mutation from an iterator side channel. Non-mutating iterator
entry reads, finite map snapshots, and nested value-field bindings remain
supported.

## 7. Worklists

### 7.1 Recursive region worklist

The graph worklist starts at the fatal query's input ports and walks only
runtime-validated equality/read-from relations for automatic composition.
Mapping-only or otherwise unobserved transitions produce terminal gaps and
stop recursive expansion. `RegionTransitionDiscoveryWorklist` has been
deleted: no discovery capture is synthesized for such a transition, and no
static transition template fallback exists.

Its stable query key includes semantic region/output/relation context and
excludes activation IDs. Cache lookup is output-specific. Multiple confirmed
writes to one read form a guarded alternative group rather than an arbitrary
choice.

Bounds include depth, regions, activations per region, alternatives per read,
queries, paths, and wall-clock. Cycles and every bound event are manifest rows.

### 7.2 Region path worklist

Only `relationallyComplete=true` output summaries are eligible. For each
output-relevant branch, latest first:

```text
prefix := conditions before the selected branch
query  := prefix AND negate(selected condition)
suffix := dropped
```

The stable flip key includes the semantic prefix, output, site, occurrence, and
desired outcome, but excludes activation IDs. Terminal SAT/UNSAT/materialization
records prevent duplicate work after resume. Unmapped conditions are gaps.

## 8. Constraint solve and replay

`ConcolicConstraintSolver` lowers the expression IR to SMT-LIB, invokes Z3, and
returns materializable assignments. The important result is the selected path
and symbolic relation, not a displayed concrete model.

The replay activation carries assignments and the same immutable replay
contract. It must not contain `forcedBranches`, target-branch aliases, or replay
branch overrides. The runtime reports applied assignment count and actual
branch witnesses.

`ConcolicReplayValidator` checks:

```text
no branch override
all assignments applied
expected branch prefix observed naturally
selected site/occurrence has the desired outcome
```

Only then may the imported summary update the cache.

## 9. Guarded merging

`RegionSummaryMerger` groups path summaries by region and requested output.
Each case carries its own path-condition guard, output expressions, heap
initializers, and heap effects. The merge is complete only when the path
worklist itself is closed without gaps.

Unexplored or rejected paths are never treated as infeasible. An incomplete
merge may be emitted for diagnostics, but the composer marks it incomplete.

## 10. Maintained workload orchestration

The generic workload driver implements:

```text
load graph, summaries, path records, and resume activations
repeat within bounds:
  plan graph and region paths
  if a complete cached summary has a pending flip:
    solve, execute, validate, import, update path record
  else if an automatically eligible output is missing:
    prepare output capture with scheduler
    execute fixed test, import, update output-specific cache
  else:
    merge and evaluate closure
persist all state and manifest
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
fingerprints the actual CLI inputs, emitted SMT, and the complete relationship
catalog. The catalog itself contains only its schema, candidate array, and
verification eligibility; it does not mirror the manifest's target identity,
stage, artifact fingerprints, or a second derived binding id.

Relationship catalogs are deliberately candidate-only and always carry
`eligibleForAutomaticVerification=false`. No solver result promotes a
relationship to trusted evidence. A future natural, injection-free target
replay may upgrade a candidate only after observing the target under the
candidate model; that trust-promotion stage remains an explicit TODO.

## 12. Verification

```bash
mvn -q test
mvn -q package -DskipTests
experiments/generic/test_workflow.sh
```

A nonzero workflow/proof exit caused by explicit gaps is an expected
fail-closed state; the JSON manifest is authoritative.
