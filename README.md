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
  -> pass 1 skeleton trace
  -> pass 2 state trace and causal graph
  -> immutable linked region-path plan
  -> concolic replay and import
  -> causal composition
  -> SMT and Z3
```

The shell orchestrator freezes inputs and launches stages; it does not infer
causal edges or symbolic expressions. Static discovery owns capture sites, the
runtime owns observations, the custom VM owns symbolic expressions, and the
Composer owns formula closure.

Tracing runs the workload twice. Pass 1 instruments method activation
envelopes only and selects the candidate region skeletons the run activated;
each selected skeleton is the candidate's own row carrying the anchor names
that run observed. Pass 2 re-instruments only the selected region methods and
records calls, branches, arguments and direct declared-field accesses. The
region finalizer mints each occurrence identity exactly once over the pass-2
trace and stamps it onto the activation; the region planner and every later
stage read that identity instead of deriving one.

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

`solver_timeout_ms` is the per-query Z3 budget for every solver stage,
including each region path-flip query. A flip query that exhausts it is
recorded as the `SOLVER_TIMEOUT` exploration status and named as a
`PATH_FLIP_SOLVER_TIMEOUT` coverage gap: the campaign continues, and only a
closed UNSAT conclusion is withheld. Raise it when a host runs several
campaigns at once.

`region_path_max_waves` (default 12, override
`CAUSYNTH_REGION_PATH_MAX_WAVES`) bounds the EXPLORE closure loop. That loop
normally ends at its own fixed point, when every member's
`region_path_manifest.json` reports `state=CLOSED`. Two guards keep a closure
that is not converging from running forever:

- **No progress.** A wave that proposes exactly the obligations the previous
  wave proposed, over an exploration-record set whose verdict histogram is
  also unchanged, has learned nothing; the loop stops instead of re-solving
  and re-replaying the same set.
- **Wave budget.** Failing that, the loop stops after
  `region_path_max_waves` waves.

Either stop is recorded on every still-pending worklist as a
`REGION_PATH_CLOSURE_NO_PROGRESS` or `REGION_PATH_WAVE_BUDGET_REACHED`
coverage gap, never as a campaign failure. Like any coverage gap these are
telemetry: an unexplored sibling path withholds a closed UNSAT conclusion and
says nothing about a SAT candidate, so the campaign still publishes what it
established. Raise the budget for a workload whose closure legitimately needs
more waves than it has members.

Inspect and validate before running:

```bash
./run_engine.sh --config /absolute/path/workflow.properties config
./run_engine.sh --config /absolute/path/workflow.properties validate
```

Run the complete campaign:

```bash
./run_engine.sh --config /absolute/path/workflow.properties campaign
```

## HDFS experiments

All GraphChecker experiments run from `main`. The Hadoop workloads have separate
checkouts so that their source changes and compiled classes remain independent.

| Case | Hadoop checkout | Experiment entry point |
| --- | --- | --- |
| HDFS-11741 | `/opt/hadoop-hdfs-11741` | `experiments/hadoop/hdfs-11741/run.sh` |
| HDFS-17897 | `/opt/hadoop-hdfs-17897` | `experiments/hadoop/hdfs-17897/run.sh` |
| HDFS-17899 Balancer | `/opt/hadoop-hdfs-17899-bug1` | `experiments/hadoop/hdfs-17899/run.sh bug1` |
| HDFS-17899 SPS | `/opt/hadoop-hdfs-17899-bug2` | `experiments/hadoop/hdfs-17899/run.sh bug2` |
| HDFS-17899 DataNode | `/opt/hadoop-hdfs-17899-bug3` | `experiments/hadoop/hdfs-17899/run.sh bug3` |
| HDFS-17960 | `/opt/hadoop-hdfs-17960-jdk8` | `experiments/hadoop/hdfs-17960/run.sh` |

Append `build` to compile a workload and run its concrete test. Append `campaign`
to execute the full GraphChecker pipeline. For example:

```bash
experiments/hadoop/hdfs-17899/run.sh bug1 build
CAUSYNTH_OUTPUT_DIR=/tmp/hdfs-17899-bug1-fresh \
  experiments/hadoop/hdfs-17899/run.sh bug1 campaign
```

Use a fresh output directory for each campaign. Keep its workflow, mappings,
compiled classes and replay scripts unchanged until it finishes. The shared
build and classpath helpers ensure Hadoop compiles against the current
GraphChecker API and loads its own common/client classes, even when another
case has installed the same Hadoop SNAPSHOT coordinates in Maven's cache.

## Results

`schedule/final/` contains exactly seven files: `candidate.smt2`,
`candidate_composition_manifest.json`, `z3-result.json`, `path-closures.json`,
`gaps.json`, `result.json`, and `run-manifest.json`, which records the frozen
provenance digests, the per-iteration manifests, and the digest of every other
published artifact. The frozen inputs themselves are not in `final/`: the
private read-only copy of the tool the run executed is the `GraphChecker.jar`
in `schedule/frozen-inputs/`. Accepted outcomes are:

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

Main code lives under `src/main/java/.../` in the packages `annotation`,
`causynth`, `concolic`, `contract`, `option`, `runtime` and `transformer`; the
identity and artifact contracts shared across stages live in `contract`. The
custom VM is under `third_party/OpenJDK-Concolic-Execution-Engine`.
