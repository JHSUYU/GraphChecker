# Generic config-driven workflow

`run_engine.sh` is a thin orchestrator over the existing Java entry points. It
does not contain HDFS source, Maven-module, Docker, test-name, or exception
semantics. `experiments/hdfs/run_hdfs.sh` remains the HDFS-specific adapter.

Start from `conf/workflow.example.properties` and invoke commands from the
GraphChecker checkout:

```bash
./run_engine.sh --config experiments/generic/conf/workflow.example.properties build
./run_engine.sh --config experiments/generic/conf/workflow.example.properties analyze
./run_engine.sh --config experiments/generic/conf/workflow.example.properties workload
./run_engine.sh --config experiments/generic/conf/workflow.example.properties schedule
./run_engine.sh --config experiments/generic/conf/workflow.example.properties import
./run_engine.sh --config experiments/generic/conf/workflow.example.properties merge
./run_engine.sh --config experiments/generic/conf/workflow.example.properties compose
./run_engine.sh --config experiments/generic/conf/workflow.example.properties solve
./run_engine.sh --config experiments/generic/conf/workflow.example.properties reach
```

`solve` calls `SymbolicRelationshipVerifier` for the generated relationship
obligations. `reach` calls `BooleanReachConditionExtractor` and asks the
configured Z3 executable about every valuation of the automatically discovered
Boolean root inputs. It writes a machine-readable truth table and canonical
DNF, then checks the composed SMT plus the Java Boolean domain implies that
DNF. Neither command accepts handwritten SMT or a caller-provided reachability
condition.

The `reach` stage consumes four authenticated composition artifacts:
`composed_smt`, `composition_manifest`, `static_regions`, and
`relationship_candidates`. Its output defaults to
`schedule/boolean_reach_condition.json`. `reach_max_inputs` (default `12`) and
`reach_max_valuations` (default `4096`) bound exhaustive enumeration; exceeding
either limit produces an incomplete report instead of silently sampling.

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
| `rpc_mapping_file` | `CAUSYNTH_RPC_MAPPING_FILE` |
| `runtime_region_instances` | `CAUSYNTH_RUNTIME_REGION_INSTANCES` |
| `workload_command` | `CAUSYNTH_WORKLOAD_COMMAND` |

Artifact-specific overrides use the same names shown by `config`, including
`CAUSYNTH_ACTIVATION_PLAN`, `CAUSYNTH_RUNTIME_REGION_INSTANCES`,
`CAUSYNTH_EDGE_VALIDATIONS`,
`CAUSYNTH_RAW_RESULTS`, `CAUSYNTH_MERGE_SUMMARIES`,
`CAUSYNTH_COMPOSE_SUMMARIES`, `CAUSYNTH_COMPOSED_SMT`, and
`CAUSYNTH_RELATIONSHIP_CANDIDATES`. The reachability output can be relocated
with `CAUSYNTH_REACH_REPORT`; solver timeout remains shared with relationship
verification through `CAUSYNTH_SOLVER_TIMEOUT_MS`.

`rpc_mapping_file` is intentionally not concatenated into runtime edge
validation automatically. A fixture adapter may translate its declared RPC
equalities into the scheduler's validated edge schema, but production
composition must retain its existing runtime-evidence gates.

Use `--dry-run` or `GRAPH_CHECKER_DRY_RUN=true` to inspect constructed commands.
For small fixtures, `--debug` (or `GRAPH_CHECKER_DEBUG=true`) prints bounded,
deterministic graph projections after analyze/workload/schedule, guarded
symbolic merges after merge, and the generated SMT after compose, all on
stderr. The item and byte caps are configurable through
`GRAPH_CHECKER_DEBUG_MAX_ITEMS` and `GRAPH_CHECKER_DEBUG_MAX_BYTES`.
The historical `run_engine.sh process <conf>` form is preserved for existing
HDFS-compatible shell configs.

Run the shell regression with:

```bash
experiments/generic/test_workflow.sh
```
