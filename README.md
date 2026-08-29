# GraphChecker

GraphChecker is an academic program-analysis tool for bounded causal replay of
distributed systems. Starting from a workload and a target branch, it discovers
relevant regions, flips branches, preserves symbolic expressions across VM and
communication boundaries, composes the selected causal graph, and emits SMT.

The HDFS experiments model keys only as abstract coordination identifiers. They
do not recover credentials or secret bytes.

## HDFS-11741 status

The current bounded witness targets:

```text
workload: TestBalancerWithEncryptedTransfer#testEncryptedBalancer1
target:   BlockTokenSecretManager.allKeys.get(keyId) == null
```

The exported result is:

- [`candidate.smt2`](experiments/hdfs/hdfs-11741/result/candidate.smt2)
- [`candidate_composition_manifest.json`](experiments/hdfs/hdfs-11741/result/candidate_composition_manifest.json)

It was recomposed with the current GraphChecker JAR from cached analysis and
replay results. The Composer reports `FINAL_READY`, no selected gaps, no free
symbols, and no missing or ambiguous selected-input authority. Independent Z3
returns `sat`.

The satisfying model selects `TARGET_PATH.2`, the second recorded target-map
read. Its failure-relevant propagation is:

```text
K at NameNode
  -> getBlockKeys response
  -> Balancer cached BlockKey
  -> client materialized keyId
  -> later client reuse
  -> DataNode target keyId

rotation #a2 allKeys state
  -> heartbeat response
  -> DataNode allKeys installation
  -> target read 3356 selects recorded writer rf12
  -> lookup of K returns null
```

The SMT contains named equalities for every cross-boundary step, including
`exact_vm_handoff_port_*`, `exact_component_value_carrier_*`,
`exact_materialization_alias_*`, and the selected read-from assertions. The
model also selects `rf4` for heartbeat read 2521, which is the exact `#a2`
rotation occurrence, rather than an ordinal or first-activation fallback.

This is an existential bounded witness. `pathSetComplete=false` and
`recordedModelComplete=false` mean it is not an exhaustive-path or UNSAT
completeness result; they do not introduce a free input into the selected SAT
chain.

Validate the frozen artifact with:

```bash
cd /opt/GraphChecker

jq -e '
  .finalStatus == "FINAL_READY"
  and (.gaps | length) == 0
  and (.freeSymbols | length) == 0
  and (.finalStatusRefusals | length) == 0
  and .selectedInputLedgerAudit.missingOccurrences == 0
  and .selectedInputLedgerAudit.ambiguousOccurrences == 0
  and .selectedInputLedgerAudit.unknownArmAuthorities == 0
' experiments/hdfs/hdfs-11741/result/candidate_composition_manifest.json

z3 -smt2 experiments/hdfs/hdfs-11741/result/candidate.smt2
```

Expected first Z3 line: `sat`.

## Pipeline

The production flow is:

```text
static target slice and region planning
  -> instrumented workload trace
  -> bounded occurrence planning
  -> concolic branch-flip replay
  -> recorded read-from and VM handoff import
  -> causal composition
  -> SMT and Z3
```

HDFS-specific endpoints, symbolic hooks, and bounds stay under
`experiments/hdfs/hdfs-11741` and the Hadoop adapter. Core propagation and
composition remain field- and workload-agnostic.

The current loop declarations are in
[`loop-bounds.jsonl`](experiments/hdfs/hdfs-11741/loop-bounds.jsonl). A bound
counts selected causal bodies plus the loop exit. Polling iterations without a
selected causal anchor are stutter and do not consume a symbolic occurrence.
In particular, the NameNode monitor bound admits the third causal update after
restart, and `removeExpiredKeys` admits all selected live entries plus exit.

For a new full workload campaign, use a fresh output root:

```bash
cd /opt/GraphChecker
mvn -q -DskipTests package

export GRAPH_CHECKER_JAVA='<analysis JVM wrapper>'
export CAUSYNTH_CLASSPATH='<current Hadoop test classpath>'
export CAUSYNTH_OUTPUT_DIR='<new absent output directory>'

./run_engine.sh \
  --config experiments/hdfs/hdfs-11741/workflow.properties \
  campaign
```

Do not resume an old campaign directory. Cached immutable analysis/import
artifacts may be reused only when their source, config, VM, runtime plan, and
input digests still match.

## Current implementation

- Seed-analysis and summary-import outputs use content-addressed caches. Cache
  keys cover the JAR, source/config inputs, plans, bounds, and raw replay
  results; restored files are digest-checked and malformed entries fail closed.
  The HDFS workflow keeps this cache outside the result directory.
- SMT composition is a fixed ordered pipeline: recorded-session lowering,
  target-path lowering, causal passes, and final emission. There is no alternate
  compatibility composition path.
- Runtime plans, relation summaries, concolic result rows, configured source
  phases, and VM shared-state evidence accept only their current schemas. Old
  shapes and missing activation identities are rejected instead of synthesized.
- The scheduler now exports a compact symbolic-root mechanism catalog. An
  optional external LLM proposal is digest-bound, complete over that catalog,
  and deterministically validated before it can narrow materialization; it
  cannot alter workflow discovery or loop bounds. See
  [`docs/SYMBOLIC_ROOT_LLM.md`](docs/SYMBOLIC_ROOT_LLM.md).
- Output-capture aliases, obsolete reflective VM methods, and redundant
  Composer/fixture paths have been removed. `replayOccurrence` remains only on
  scheduler/runtime actions where it is part of current replay semantics.

## TODO

- After the symbolic-root workflow is stable across more bug cases, optimize
  and refactor this planning lane, then delete superseded/dead code and
  fixtures. Do not add fallback compatibility for retired schemas or paths.

## Minimal verification used for this result

```bash
bash -n run_engine.sh
bash src/test/shell/run_engine_campaign_helpers_test.sh
mvn -q test
mvn -q -DskipTests package
z3 -smt2 experiments/hdfs/hdfs-11741/result/candidate.smt2
git diff --check
```
