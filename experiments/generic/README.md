# Generic config-driven engine

`run_engine.sh` is the application-independent stage runner used by automatic
experiment drivers. Project layout, workload, protocol declarations, and
artifact paths come from a `key=value` workflow file. The exception target
comes from the application classfile's `@CausynthExceptionTarget` marker.

The maintained engine stages are:

```text
build -> analyze -> workload -> schedule -> import -> compose -> reach
```

`workload` performs both runtime passes: activation-envelope selection followed
by state/branch collection for the selected region methods. `schedule` only
emits bounded `ExecutionTask` records. Workload-specific automatic drivers run
the VM tasks, close producer path sets, and feed the imported summaries back to
`compose`; no shell stage fabricates a summary or SMT formula.

Direct stage invocation is intended for automatic drivers and diagnosis:

```bash
./run_engine.sh --config path/to/workflow.properties validate
./run_engine.sh --config path/to/workflow.properties analyze
./run_engine.sh --config path/to/workflow.properties workload
./run_engine.sh --config path/to/workflow.properties schedule
```

`config`, `validate`, and `debug-stage` are read-only. `--dry-run` prints the
constructed command. `--debug` prints bounded artifact projections to stderr.

## Configuration

The config file is parsed as data and is never sourced by the shell. Unknown
keys are passed to GraphChecker through `-C` but cannot mutate shell state.
Relative paths use `workflow_path_base`:

- `@config/path`: relative to the workflow file;
- `@project/path` or `@graphchecker/path`: relative to GraphChecker;
- `@repo/path`: relative to the analyzed repository.

Classpath and multi-summary settings are colon-separated. Environment
overrides use the documented `GRAPH_CHECKER_*` and `CAUSYNTH_*` names; run
`config` to inspect the normalized result.

## Target and replay contracts

The application marks the failing construction with the Java 8 type-use
annotation:

```java
throw new @CausynthExceptionTarget("request-failure") RequestException();
```

An observed binary decision is represented by one typed `BranchWitness` with
its exact site, occurrence, concrete outcome, VM path-condition index, and
canonical predicate. `BranchReplayContract.flip()` is the only polarity
operation. A zero-PC branch is observation-only. Multiway switches use their
own successor-aware records.

Producer exploration materializes inputs only. `RegionPathWorklist` publishes a
guarded relation only after the exact output closure is closed. `compose`
consumes imported VM relations and emits a manifest-bound SMT artifact; `reach`
checks it with the configured Z3 executable.

Run the shell contract test with:

```bash
experiments/generic/test_workflow.sh
```
