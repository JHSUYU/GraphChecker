# GraphChecker

GraphChecker is a research tool for failure-directed, bounded causal replay of
distributed systems. Given a workload and a target branch, it discovers a
target-relevant causal skeleton, explores selected branch alternatives,
propagates symbolic expressions across heap and communication boundaries, and
composes the retained relations into SMT.

The result is a bounded existential statement about the selected execution
model. GraphChecker is not a whole-program verifier, and an incomplete bounded
search is not evidence of global unreachability.

The HDFS experiments treat keys as abstract coordination identifiers. They do
not recover credentials or secret bytes.

## Design and authority

```text
workload + target
  -> static and seed-runtime discovery
  -> frozen causal skeleton
  -> symbolic-root mechanism catalog
  -> optional external LLM proposal
  -> deterministic proposal validation and scheduling
  -> bounded concolic replay
  -> VM expression and read-from import
  -> causal composition
  -> SMT and Z3
```

Each stage has a narrow authority boundary:

| Stage | Produces | Does not decide |
| --- | --- | --- |
| Static discovery | Target slice, region/endpoint catalogs, retained loops, source-declaration candidates | Runtime occurrences, read-from choices, reachability |
| Seed runtime | Observed activations, branches, field versions, reads, and RPC events | Which bounded causal model is accepted |
| Scheduler | Target-first tasks, occurrence identities, selected relations, frozen topology, mechanism cards | Symbolic expressions or solver reachability |
| External LLM | Semantic classifications of already cataloged root candidates | Topology, loop bounds, occurrences, read-from, replay, or SMT |
| Custom VM and importer | Path predicates, symbolic expressions, versioned writers, replay-local evidence | Final composition acceptance |
| Composer | Candidate formula, selected-closure audit, and `FINAL_READY` or refusal | Solver reachability or whole-run acceptance |
| Solver and extractor | `REACHABLE`, `UNREACHABLE`, or `UNKNOWN` for the composed formula | Composition closure or gaps outside that formula |
| Shell orchestrator | Frozen provenance, aggregate gap gate, and mechanical claim mapping | Re-deciding Composer or solver semantics |

A topology change never mutates a running iteration. It closes that immutable
iteration and causes the next iteration to rebuild the target frontier.
Content-addressed caches reuse analysis and import results only when their
relevant input digests match. The seed cache deliberately excludes only the
LLM proposal property so catalog and alternative proposals can share one seed
analysis; the proposal is still frozen and digest-bound in campaign provenance
and the schedule index.

## LLM-guided symbolic-root narrowing

GraphChecker does not call an LLM. The `catalog` command runs through the first
`PLAN` stage and writes a digest-bound
`symbolic_root_mechanism_cards.json`. An external LLM may classify those cards,
and the scheduler validates the returned JSON before it affects a campaign.

The LLM can propose only these decisions:

- `SELECT_ROOT`: symbolize an independently changeable origin already marked
  `symbolizable=true`.
- `RETAIN_CONTEXT`: preserve a carrier, selector, guard, or relation-bound
  value without minting a second independent symbol.
- `EXCLUDE_SYMBOLIZATION`: keep polling noise or an irrelevant mechanism
  concrete.
- `REVIEW`: mark insufficient evidence without guessing. It is not executable;
  the validator rejects the proposal until a human resolves every review item
  and resubmits it.

A proposal is complete over one exact catalog, cites catalog evidence IDs, and
is rejected on an unknown, duplicated, or missing candidate. A
`relationBound=true` value must remain context because its producer equality is
part of the causal chain. Only writer-anchored context remains symbolic so that
equality reaches the Composer; local context with no writer is materialized as
concrete. Fixed symbolic declarations remain separate from the proposal: they
are known instrumentation authority for a witness, not the complete bug ground
truth.

For HDFS-11741, `keyId` and `expiryDate` are current fixed roots. A semantic
proposal should still consider alternative mechanisms such as encryption-key
cache lifetime and reuse, key rotation and installation, time/expiry
configuration, map membership, and the selectors or guards that choose a
version. See [the proposal contract and prompt](docs/SYMBOLIC_ROOT_LLM.md).

## Loop bounds and shared state

Every retained condition-controlled loop declares its own `K_L` in the
workload configuration. `K_L` is the maximum number of retained loop-body
executions (and therefore published symbolic cases); the loop exit does not
consume a body slot. Declared values are independent per loop and must be in
the supported range `1..64`. The core default of eight is an executor ceiling,
not workload semantics, so the HDFS workflow refuses a missing declaration.

For an anchor-addressed polling loop, exact source-phase or response-exchange
anchors reserve capacity inside `K_L`. Ordinary prefix bodies may consume the
remaining capacity. Only excess bodies that satisfy no still-missing selected
anchor are released as stutter, leaving the reserved slots available. A
repeated occurrence of an already satisfied anchor does not consume another
reserved slot. The workload still executes those iterations concretely;
GraphChecker does not skip the program's polling. If a selected anchor never
occurs before shutdown, the campaign emits a named gap rather than claiming
closure. The current declarations are in
[loop-bounds.jsonl](experiments/hdfs/hdfs-11741/loop-bounds.jsonl).

Concurrent shared state is modeled as:

```text
VM-recorded writer versions
  -> runtime-observed candidate writers for a read
  -> SMT rf_selector__ arms, including rf_unknown
  -> solver-selected writer arm
  -> replay-local observation and confirmation
```

The current selected-read cut is `OBSERVE_AND_CONFIRM`: it does not wait for a
writer, rewrite a program field, or replace an RPC return. Consequently,
post-SMT deterministic schedule replay is not yet a completion guarantee.

## Toolchain and prerequisites

Use a stock JDK 8 for GraphChecker and discovery tracing. Use the customized
OpenJDK 8 Zero VM only for narrow concolic replay; do not set it as the global
`JAVA_HOME` for the whole workflow.

Required workflow tools are a stock JDK 8, Maven, Z3, `jq`, `python3`,
`sha256sum`, and a `protoc` whose version matches the selected Hadoop checkout.
Docker with `linux/amd64` support is required only when building the custom VM
from source. The HDFS source launcher reads `<protobuf.version>` from Hadoop
and refuses a mismatched `protoc`. Its Maven build is deliberately offline, so
the local Maven cache must already contain that Hadoop revision's dependencies.

Build GraphChecker and the custom VM from the tracked sources:

```bash
export JAVA_HOME=/absolute/path/to/stock-jdk8
export PATH="$JAVA_HOME/bin:$PATH"

mvn -q -DskipTests package

JOBS=4 \
  third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh

JDK_HOME="$PWD/third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image" \
  third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_smoke_test.sh
```

The repository does not contain the local `/opt/causynth-toolchain` binary
cache or a custom-JDK `build/` tree. For a faster public setup, publish a
versioned GitHub Release or OCI image with its source commit, platform, and
SHA-256 digest; keep machine-specific binaries outside Git history. See the
[custom VM build guide](third_party/OpenJDK-Concolic-Execution-Engine/README.md).

## Running HDFS-11741

The configured workload and target are:

```text
workload: TestBalancerWithEncryptedTransfer#testEncryptedBalancer1
target:   BlockTokenSecretManager.allKeys.get(keyId) == null
```

Fresh runs require the symbolic-propagation hooks in
[JHSUYU/hadoop](https://github.com/JHSUYU/hadoop). The documented baseline is
`a32f43e22ad71283b1921c134dbcde6b44775676`, which pins Protobuf compiler
2.5.0. Another revision is compatible only if it preserves the same hook
contract, and its different source digest will be frozen by the campaign.

Build that Hadoop checkout and capture its test classpath. Use absolute paths;
the example path names are not required:

```bash
export HADOOP_HOME_DIR=/absolute/path/to/hadoop
export HADOOP_PROTOC_PATH=/absolute/path/to/matching/protoc
export HDFS11741_BUILD_OUTPUT="$PWD/experiments-output/hdfs-11741-build"

LAUNCHER_OUTPUT="$HDFS11741_BUILD_OUTPUT" \
  experiments/hdfs/hdfs-11741/source-first-launcher.sh build

HADOOP_TEST_CP=$(<"$HDFS11741_BUILD_OUTPUT/hadoop-test-classpath.txt")
export CAUSYNTH_CLASSPATH="$HADOOP_HOME_DIR/hadoop-hdfs-project/hadoop-hdfs/target/test-classes:$HADOOP_HOME_DIR/hadoop-hdfs-project/hadoop-hdfs/target/classes:$HADOOP_HOME_DIR/hadoop-hdfs-project/hadoop-hdfs-client/target/classes:$HADOOP_HOME_DIR/hadoop-common-project/hadoop-common/target/test-classes:$HADOOP_HOME_DIR/hadoop-common-project/hadoop-common/target/classes:$HADOOP_TEST_CP"
```

GraphChecker's HDFS analysis needs a high-heap stock-JDK wrapper. For example,
save the following outside the repository as an executable file, adjusting the
heap to the host:

```bash
#!/usr/bin/env bash
exec /absolute/path/to/stock-jdk8/bin/java -Xmx32g "$@"
```

Then configure the two JVM roles and reusable cache:

```bash
export CAUSYNTH_REPO="$HADOOP_HOME_DIR"
export GRAPH_CHECKER_JAVA=/absolute/path/to/graphchecker-java-wrapper
export HDFS11741_TRACE_JDK="$JAVA_HOME"
export CAUSYNTH_CUSTOM_JDK_HOME="$PWD/third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image"
export CAUSYNTH_CACHE_DIR=/absolute/path/to/graphchecker-cache
```

For LLM narrowing, use two different, initially absent output roots and the
same cache. The catalog phase stops before replay:

```bash
export CAUSYNTH_OUTPUT_DIR=/absolute/absent/path/hdfs11741-catalog
unset CAUSYNTH_SYMBOLIC_ROOT_PROPOSAL

./run_engine.sh \
  --config experiments/hdfs/hdfs-11741/workflow.properties \
  catalog
```

Classify
`$CAUSYNTH_OUTPUT_DIR/schedule/iteration-0000/symbolic_root_mechanism_cards.json`
with the contract in `docs/SYMBOLIC_ROOT_LLM.md`, then run a fresh campaign:

```bash
export CAUSYNTH_OUTPUT_DIR=/absolute/absent/path/hdfs11741-selected
export CAUSYNTH_SYMBOLIC_ROOT_PROPOSAL=/absolute/path/to/proposal.json

./run_engine.sh \
  --config experiments/hdfs/hdfs-11741/workflow.properties \
  campaign
```

Do not resume or overwrite an old output root. A campaign freezes the
GraphChecker JAR, VM, configuration, target, protocol stubs, loop bounds,
symbolic declarations, optional proposal, Hadoop classes, classpath, and both
source checkouts before replay.

## Checked HDFS-11741 reference witness

The repository includes a pre-LLM reference formula and composition manifest:

- [candidate.smt2](experiments/hdfs/hdfs-11741/result/candidate.smt2)
- [candidate_composition_manifest.json](experiments/hdfs/hdfs-11741/result/candidate_composition_manifest.json)

Its selected causal propagation is, at a high level:

```text
NameNode block key
  -> getBlockKeys response
  -> Balancer cached key
  -> DataEncryptionKey/client key identifier
  -> DataNode target key identifier

NameNode key rotation
  -> heartbeat response
  -> DataNode allKeys installation
  -> selected target read-from
  -> missing map lookup
```

The manifest reports `FINAL_READY`, zero selected gaps, zero free symbols, and
no missing, ambiguous, undeclared, or unknown-arm selected-input authority.
Independent Z3 returns `sat`. This establishes one bounded existential witness;
`pathSetComplete=false` and `recordedModelComplete=false` explicitly prevent an
exhaustive-path or global-UNSAT claim. Because these files predate the LLM root
selector, they do not validate an LLM-selected campaign or post-SMT replay.

Verify the checked files from the repository root:

```bash
jq -e '
  .schemaVersion == 2
  and .kind == "CONCOLIC_COMPOSED_SMT"
  and .state == "CANDIDATE_READY"
  and .finalStatus == "FINAL_READY"
  and (.gaps | length) == 0
  and (.freeSymbols | length) == 0
  and (.finalStatusRefusals | length) == 0
  and .selectedInputLedgerAudit.missingOccurrences == 0
  and .selectedInputLedgerAudit.ambiguousOccurrences == 0
  and .selectedInputLedgerAudit.undeclaredPortOccurrences == 0
  and .selectedInputLedgerAudit.unknownArmAuthorities == 0
' experiments/hdfs/hdfs-11741/result/candidate_composition_manifest.json

z3 -smt2 experiments/hdfs/hdfs-11741/result/candidate.smt2
```

The expected first Z3 line is `sat`.

## Acceptance and development checks

The Composer and solver determine the semantic claim mechanically mapped into
`schedule/final/result.json`:

- `FINAL_READY` plus `REACHABLE` becomes `SAT_CANDIDATE`.
- `FINAL_READY` plus `UNREACHABLE` plus
  `unsatClosureComplete=true` becomes `UNSAT_CLOSED`.
- Every other combination is `INCONCLUSIVE_PARTIAL`.

A fresh run is accepted only when that claim is `SAT_CANDIDATE` or
`UNSAT_CLOSED`, the aggregate `schedule/final/gaps.json` has `gapCount == 0`,
and the same fresh run has its frozen provenance and run manifest. The shell
writes `result.json` before applying the aggregate gap gate, so its claim alone
is insufficient. A zero exit alone without the matching fresh artifacts is
also insufficient; neither an old SMT file, seed-level `sat`, nor
`CANDIDATE_READY` passes this gate.

Useful local checks are:

```bash
bash -n run_engine.sh
bash -n third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh
bash src/test/shell/run_engine_campaign_helpers_test.sh
bash src/test/shell/symbolic_variable_model_print_test.sh
mvn -q test
mvn -q -DskipTests package
z3 -smt2 experiments/hdfs/hdfs-11741/result/candidate.smt2
git diff --check
```

## Repository layout

- `src/main/java/.../causynth`: static discovery and target-directed planning.
- `src/main/java/.../concolic`: scheduling, replay import, composition, and
  reachability.
- `src/main/java/.../runtime`: runtime instrumentation and symbolic handoff.
- `run_engine.sh`: immutable campaign orchestration, caching, provenance, and
  final gap/claim gates.
- `src/main/java/.../contract`: current cross-stage artifact schemas.
- `experiments/hdfs/hdfs-11741`: workload-specific target, endpoints, loop
  bounds, launcher, and checked witness; HDFS hooks live in the Hadoop fork.
- `third_party/OpenJDK-Concolic-Execution-Engine`: custom VM source, Docker
  build entrypoint, and smoke tests.
- `docs/SYMBOLIC_ROOT_LLM.md`: external LLM context, prompt, and JSON contract.

## TODO

- Add a thin post-SMT witness replay that consumes the selected causal skeleton
  and model, then reports any schedule/read-from divergence explicitly.
- Evaluate LLM proposals across additional bugs against the unfiltered catalog:
  retained roots, replay jobs/time, missed mechanisms, and witness preservation.
- After this path is stable across cases, optimize and refactor the
  planner/scheduler lane and delete superseded code, dead code, and redundant
  fixtures. Do not add fallback compatibility for retired schemas or paths.
