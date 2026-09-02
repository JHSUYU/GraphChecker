# GraphChecker

GraphChecker builds bounded, failure-directed causal replays for distributed
Java workloads. From a workload and target it discovers the relevant program
slice, records concrete node and request flows, explores selected alternatives,
propagates symbolic values through heap and message boundaries, and composes an
SMT formula.

The result is about the selected bounded model. An incomplete search is not a
whole-program unreachability proof.

## Toolchain

```text
workload + target + wire flows + loop bounds
  -> static discovery
  -> seed trace and causal graph
  -> immutable target-first plan
  -> concolic replay and import
  -> causal composition
  -> SMT and Z3
```

The shell orchestrator freezes inputs and launches stages; it does not infer
causal edges or symbolic expressions. Static discovery owns capture sites, the
runtime owns observations, the custom VM owns symbolic expressions, and the
Composer owns formula closure.

Communication uses one transport-neutral model:

- A workload registers each stable node owner, then begins a request flow from
  that node.
- Every HTTP request and response carries the current trace context. Inbound
  handling installs the remote parent, source, and request flow for a scoped
  interval and restores the previous context on exit.
- Exchange correlation contributes topology only. It never reconstructs a
  context or symbolic value.
- A `WIRE_FLOW` declares one typed producer and consumer. Its capture kind is
  exactly one of `METHOD_PARAMETER`, `METHOD_RETURN`, `CALL_ARGUMENT`, or
  `CALL_RETURN`.
- OUT captures export a symbolic message leaf; IN captures attach that leaf.
  Request and response directions use the same mechanism.

Each campaign iteration is immutable. New topology closes the current
iteration and is planned in the next one. Content-addressed caches are reused
only when their relevant frozen inputs match.

## Requirements

- Stock JDK 8 and Maven for GraphChecker and seed tracing
- The customized OpenJDK 8 Zero VM for concolic replay
- Z3, `jq`, `python3`, and `sha256sum`
- Compiled workload production/test classes and their complete classpath

Build GraphChecker and, when needed, the custom VM:

```bash
export JAVA_HOME=/absolute/path/to/jdk8
export PATH="$JAVA_HOME/bin:$PATH"
mvn -q -DskipTests package

JOBS=4 \
  third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh
```

The custom VM build and smoke-test instructions are in
[third_party/OpenJDK-Concolic-Execution-Engine/README.md](third_party/OpenJDK-Concolic-Execution-Engine/README.md).

## Workflow configuration

`run_engine.sh` reads a small `key=value` workflow file. Paths may be absolute
or use `@config`, `@repo`, and `@project`. The corresponding
`GRAPH_CHECKER_*` and `CAUSYNTH_*` environment variables may override values;
the `config` command prints the result.

At minimum, configure the workload repository/module, production classes,
classpath, target, loop-bound declarations, workload command and test identity,
custom VM, scheduling/solver bounds, and fresh output/cache roots. Configure
`causynth_communication_mappings` when the target crosses a message boundary.
An empty loop-bound file explicitly means that the selected workload has no
retained condition-controlled loop requiring a bound.

Inspect and validate before running:

```bash
./run_engine.sh --config /absolute/path/workflow.properties config
./run_engine.sh --config /absolute/path/workflow.properties validate
```

Run either the symbolic-root catalog phase or the complete campaign:

```bash
./run_engine.sh --config /absolute/path/workflow.properties catalog
./run_engine.sh --config /absolute/path/workflow.properties campaign
```

The catalog command stops after writing
`schedule/iteration-0000/symbolic_root_mechanism_cards.json`. An optional
external proposal can narrow independent roots; its strict contract is in
[docs/SYMBOLIC_ROOT_LLM.md](docs/SYMBOLIC_ROOT_LLM.md). Use a different fresh
output root for the subsequent campaign.

## SOLR-18406

The current workload targets follower replication when the selected leader
commit expires between `filelist` and `filecontent`. It pauses the follower
after the file list, lets the reservation expire, commits a newer generation,
then resumes the download. The expected repaired behavior is to renegotiate and
install the newer generation.

The checked-in declarations are:

- [target.yaml](experiments/solr/solr-18406/target.yaml)
- [communication-mappings.jsonl](experiments/solr/solr-18406/communication-mappings.jsonl)
- [loop-bounds.jsonl](experiments/solr/solr-18406/loop-bounds.jsonl)

The mappings cover the generation carried by `indexversion`, `filelist`, and
`filecontent`, plus the HTTP status response. The instrumented Solr workload
registers leader/follower node owners and one outer follower fetch request flow;
its HTTP bridge carries trace and symbolic headers on both directions.

The same directory contains the complete workflow and replay adapter. After
building the instrumented checkout at `/opt/solr`, run the generic toolchain
against [workflow.properties](experiments/solr/solr-18406/workflow.properties):

```bash
./run_engine.sh --config experiments/solr/solr-18406/workflow.properties catalog
./run_engine.sh --config experiments/solr/solr-18406/workflow.properties campaign
```

## Results

The final directory contains the composed SMT, composition/reachability reports,
aggregate gaps, frozen provenance, and `result.json`. Accepted outcomes are:

- `SAT_CANDIDATE`: a bounded witness was found.
- `UNSAT_CLOSED`: the composed bounded model is closed and unsatisfiable.
- `INCONCLUSIVE_PARTIAL`: no accepted claim; inspect named gaps.

A successful claim also requires zero aggregate gaps and matching fresh
provenance. A zero process exit or an old SMT file is not sufficient.

## Development checks

```bash
bash -n run_engine.sh
bash src/test/shell/run_engine_campaign_helpers_test.sh
mvn -q test
git diff --check
```

Main code lives under `src/main/java/.../{causynth,runtime,concolic,contract}`;
the custom VM is under `third_party/OpenJDK-Concolic-Execution-Engine`.
