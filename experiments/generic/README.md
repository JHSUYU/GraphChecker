# Generic config-driven workflow

`run_engine.sh` is a thin, application-independent orchestrator over the Java
entry points. Project layout, workload command, and artifact locations come
from the selected workflow configuration. The exception target itself comes
from the application classfile's `@CausynthExceptionTarget` marker; the
configuration may select its marker id but does not describe or search for a
throw site.

Start from `conf/workflow.example.properties` and invoke commands from the
GraphChecker checkout:

```bash
./run_engine.sh --config experiments/generic/conf/workflow.example.properties build
./run_engine.sh --config experiments/generic/conf/workflow.example.properties analyze
./run_engine.sh --config experiments/generic/conf/workflow.example.properties workload
./run_engine.sh --config experiments/generic/conf/workflow.example.properties schedule
./run_engine.sh --config experiments/generic/conf/workflow.example.properties import
./run_engine.sh --config experiments/generic/conf/workflow.example.properties compose
./run_engine.sh --config experiments/generic/conf/workflow.example.properties reach
```

Guarded relation construction belongs to the workload-specific producer
exploration loop: `RegionPathWorklist` atomically emits the guarded relation
only when the exact output closure reaches `CLOSED`. The generic runner
therefore consumes that relation at `compose` without a second detached merge
or validation pass.

`reach` calls `BooleanReachConditionExtractor` and asks the configured Z3
executable about every valuation of the automatically discovered Boolean root
inputs. It writes a machine-readable truth table and canonical DNF, then checks
that the composed SMT plus the Java Boolean domain implies that DNF. It does
not accept handwritten SMT or a caller-provided reachability condition.

The `reach` stage consumes four composition inputs:
`composed_smt`, `composition_manifest`, `refined_regions`, and
`relationship_candidates`. It verifies their path/size/SHA-256 bindings from
the composition manifest before extraction. Its output defaults to
`schedule/boolean_reach_condition.json`. `reach_max_inputs` (default `12`) and
`reach_max_valuations` (default `4096`) bound exhaustive enumeration; exceeding
either limit produces an incomplete report instead of silently sampling.

## Exception target annotation

The application marks the exact failing construction with the Java 8
type-use annotation shipped by GraphChecker:

```java
throw new @CausynthExceptionTarget("request-failure") RequestException();
```

The analyzer reads that marker from the class file and starts its backward
slice at the one matching Jimple throw. `target.yaml` may contain
`exception_target_id: request-failure` to select among multiple markers in one
input class tree. With no id there must be exactly one marker. The exception
type is taken from the annotated `NEW`; the removed exception-name,
`seed_variables`, and `seed_function` paths are rejected rather than searched
or inferred globally.

## Binary branch replay protocol

An observed, replayable binary decision is represented once by a typed
`BranchWitness`. It owns the exact site/occurrence, source outcome, canonical
satisfied predicate, VM path-condition index, and predicate normalization.
The witness JSON is the value itself; it does not carry a redundant self-hash.
`BranchReplayContract.flip()` is the sole polarity operation and produces the
ordered-prefix-plus-flipped-target request consumed unchanged by the worklist,
solver, instrumentation, runtime, importer, and verifier. A zero-PC VM branch
event is observation-only and cannot be promoted through an alternate
certificate. Retired target/prefix/negated-condition aliases are rejected.
Multiway switches use their own successor-aware records.

Producer path exploration executes that contract with input-only
materialization. The target stage derives the same typed contract and a
`SolverPathContext` as a candidate fatal query, but does not execute a target
replay. The three-thread reference runner stops at a hash-bound, independently
Z3-checked result with `state=CANDIDATE_READY`,
`trustState=CANDIDATE_ONLY`, and exact
`reachability=REACHABLE|UNREACHABLE`. Promoting that candidate to a trusted
result by an injection-free natural replay is intentionally the remaining
TODO.

The compact relationship catalog is schema 2 and has only
`schemaVersion`, `kind`, `trustState`, and `relationships`. The terminal
candidate result binds exactly five files: the SMT, composition manifest,
relationship catalog, Boolean model, and result manifest. No bootstrap result,
recursive worklist, summary cache, eligibility mirror, or
natural-replay-implemented flag is part of the maintained protocol.

## Paths and configuration

The generic config grammar is one `key=value` per line. It is parsed as data,
not sourced as shell code. Unknown keys remain visible to Java through `-C`
but cannot mutate shell variables.

Ordinary relative paths use `workflow_path_base`, which accepts `config`,
`project`/`graphchecker`, or `repo`. Explicit prefixes override that default:

- `@config/path` is relative to the config file.
- `@project/path` and `@graphchecker/path` are relative to GraphChecker.
- `@repo/path` is relative to the resolved analyzed-project repository.

Classpath and multi-summary values are colon-separated. Keep each setting on
one line. The normalized result can be inspected without running analysis:

```bash
./run_engine.sh --config path/to/workflow.properties config
./run_engine.sh --config path/to/workflow.properties validate
```

The principal environment overrides are:

| Config key | Environment override |
| --- | --- |
| `graphchecker_jar` | `GRAPH_CHECKER_JAR` |
| `java_bin` | `GRAPH_CHECKER_JAVA` |
| `maven_bin` | `GRAPH_CHECKER_MAVEN` |
| `graphchecker_work_dir` | `GRAPH_CHECKER_WORK_DIR` |
| `project_repo` | `CAUSYNTH_REPO` |
| `project_module_dir` | `CAUSYNTH_MODULE_DIR` |
| `project_classes_dir` | `CAUSYNTH_CLASSES_DIR` |
| `project_classpath` | `CAUSYNTH_CLASSPATH` |
| `causynth_output_dir` | `CAUSYNTH_OUTPUT_DIR` |
| `causynth_target_spec` | `CAUSYNTH_TARGET_SPEC` |
| `custom_jdk_home` | `CAUSYNTH_CUSTOM_JDK_HOME` |
| `z3_bin` | `CAUSYNTH_Z3` |
| `reach_report` | `CAUSYNTH_REACH_REPORT` |
| `reach_max_inputs` | `CAUSYNTH_REACH_MAX_INPUTS` |
| `reach_max_valuations` | `CAUSYNTH_REACH_MAX_VALUATIONS` |
| `workload_command` | `CAUSYNTH_WORKLOAD_COMMAND` |

Artifact-specific overrides use the same names shown by `config`, including
`CAUSYNTH_REGION_PLAN`, `CAUSYNTH_EDGE_VALIDATIONS`,
`CAUSYNTH_RAW_RESULTS`, `CAUSYNTH_COMPOSE_SUMMARIES`,
`CAUSYNTH_COMPOSED_SMT`, and
`CAUSYNTH_RELATIONSHIP_CANDIDATES`. The reachability output can be relocated
with `CAUSYNTH_REACH_REPORT`; solver timeout is configured through
`CAUSYNTH_SOLVER_TIMEOUT_MS`.

Use `--dry-run` or `GRAPH_CHECKER_DRY_RUN=true` to inspect constructed commands.
For small fixtures, `--debug` (or `GRAPH_CHECKER_DEBUG=true`) prints bounded
stage artifacts on stderr: analyze shows the static graph, symbolic regions,
and symbolic region edges; workload shows
`runtime_region_edge_validation.jsonl` and `concolic_region_plan.jsonl`;
`debug-stage merge` projects an existing guarded relation, and compose shows
the generated SMT. The item and byte caps are configurable through
`GRAPH_CHECKER_DEBUG_MAX_ITEMS` and `GRAPH_CHECKER_DEBUG_MAX_BYTES`.
Run the shell regression with:

```bash
experiments/generic/test_workflow.sh
```
