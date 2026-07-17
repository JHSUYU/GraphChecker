# Concolic Region Integration Contract

Status: implemented core; the hand-written one-DN runtime-bounded N=4
diagnostic is verified, while production automatic-composition gaps remain
tracked in the top-level `readme.md` (2026-07-17).

This document defines the project-independent contract between GraphChecker's
static/runtime analysis, Soot instrumentation, the custom OpenJDK concolic
engine, recursive scheduling, guarded merging, and SMT verification. The
top-level `readme.md` is the authoritative handoff and experiment-status file.

## 1. Research scope

This is academic software engineering and program analysis. The fixed
validation workload is the HDFS-owned local `MiniDFSCluster` test:

```text
repository: /Users/lizhenyu/Desktop/study/hadoop
commit:     ece33208b89a6a06c1b362d10fab31343fe5df13
test:       org.apache.hadoop.hdfs.server.balancer.
            TestBalancerWithEncryptedTransfer#testEncryptedBalancer1
boundary:   local test/custom OpenJDK only; no third-party systems
```

HDFS names such as SASL, token, key, or encrypted transfer describe ordinary
upstream source and test behavior. They do not broaden the work into attacks,
intrusion, exploitation, or access to external systems.

## 2. Core invariants

1. Every analyzed unit is a `REGION.*`; no domain-specific region types exist.
2. A region has one of two capture goals: `TARGET_BRANCH` or `OUTPUT_CLOSURE`.
3. The target goal performs one directed fatal-branch replay; it does not need
   comprehensive path enumeration.
4. An output goal is admitted only through real record/solve/replay/import
   evidence and is merged only after its bounded path worklist closes.
5. Input models may change real program inputs. Branch overrides never count as
   automatic concolic evidence.
6. Static mappings discover work but do not establish value semantics.
7. Cross-region equality requires a complete, invocation-matched runtime value
   fingerprint. Shared state requires a concrete write/read witness.
8. Domain adapters may map formats and ports only. They cannot add equations.
9. Human assumptions are `EXPLICIT_CONTRACT`, physically separate from and
   ineligible for automatic SMT composition.
10. Any missing evidence, unsupported expression, bound, cycle, or incomplete
    admission remains an explicit gap.

Legacy strings `RELATIONAL_PRODUCER` and `RELATIONAL_PROTOCOL` are accepted only
when reading old artifacts. New artifacts always emit `OUTPUT_CLOSURE`.

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

An observed call order or static RPC/serialization mapping without those
witnesses is mapping-only. `AutomaticRegionEdge` is the shared fail-closed gate.

`ConcolicScheduler` rebuilds a target activation's equality classes from only
the witness-bearing relations selected for that concrete region instance. A
global static equality class is never reused blindly for another invocation.

## 5. Capture goals

### 5.1 `TARGET_BRANCH`

The scheduler selects a final fatal branch and creates:

```text
old path prefix
AND negated final condition
```

The solver output is converted to concrete materialization actions. A replay is
admitted only if:

```text
all expected actions were applied
no branch override was used
the concrete target site/occurrence reached the desired outcome
the expected exception appears in the exception chain
```

This goal deliberately stops after the directed fatal condition is validated.

### 5.2 `OUTPUT_CLOSURE`

The scheduler resolves the requested output, loads its static backward slice,
and prepares executable materializations with the same definition index used
for target scheduling. A seed capture contains no forced branch.

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

## 7. Worklists

### 7.1 Recursive region worklist

The graph worklist starts at the fatal query's input ports and walks only
runtime-validated equality/read-from relations for automatic composition.
Mapping-only edges can identify a gap but stop recursive expansion.

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

The replay activation carries assignments and a validation-only target branch.
It must not contain `forcedBranches` or replay branch overrides. The runtime
reports applied assignment count and actual branch mappings.

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

## 10. Campaign state machine

`ConcolicCampaignRunner` implements:

```text
load graph, summaries, path records, and resume activations
repeat within bounds:
  plan graph and paths
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
The fixed HDFS script performs activation-specific Soot instrumentation, runs
the single local unit test on the custom JDK, and lets the campaign importer
normalize the result.

Persisted resume files are:

```text
campaign_activations.jsonl
campaign_summaries.jsonl
region_path_records.jsonl
merged_region_summaries.jsonl
concolic_campaign_manifest.json
```

## 11. SMT composition

`ConcolicSmtComposer` consumes only:

```text
validated fatal query and target replay summary
complete/guarded region summaries
target-instance-selected equality/read-from bindings
common region/port schemas
```

It does not read the HDFS explicit-contract registry. Legacy summaries carrying
`protocolModel` or embedded `explicitContracts` are rejected as incomplete.

The manifest is complete only if there are no missing summaries, incomplete
relations, unsupported expressions, unbound ports, or target replay gaps.
`domainSemanticAdapterUsed=false` and `explicitContractsIncluded=false` are
explicit output invariants.

`SymbolicRelationshipVerifier` may run an automatic proof only when the
candidate set says `eligibleForAutomaticVerification=true`. It first requires
the base formula to be SAT, then classifies a relationship as `DERIVED` only if:

```text
base constraints AND NOT(relationship) == UNSAT
```

This prevents vacuous proofs from an inconsistent base and blocks proof labels
when composition is incomplete.

## 12. HDFS-specific boundary

`HdfsRegionPortMapper` can locate HDFS-named ports and attach evidence paths. It
emits no semantic assertion and is ineligible as a summary or SMT input.

`HdfsExplicitContracts` separately records hypotheses such as codec round-trip,
cache policy, or expiry/membership. Every row is marked:

```text
kind = EXPLICIT_CONTRACT
eligibleForAutomaticDerivation = false
includedInSmt = false
mayBeReportedAsSymbolicExecutionResult = false
```

The proposed NameNode → Balancer → DataNode `keyId` path and NameNode → DataNode
`allKeys` path are navigation hints. Each actual equality, read-from, temporal,
or membership relation still requires runtime/concolic evidence.

No HDFS loop has currently been modified. A loop rewrite is permissible only
as a documented, minimal experiment in the fixed local source copy after a real
loop-specific blocker is demonstrated; it cannot silently change the modeled
semantics.

## 13. Verification

```bash
mvn -q test
mvn -q package -DskipTests
bash -n experiments/hdfs/run_hdfs.sh
```

The fixed HDFS commands and current artifact paths are documented in the
top-level `readme.md`. A nonzero campaign/proof exit caused by explicit gaps is
an expected fail-closed state; the JSON manifest is authoritative.
