# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

GraphChecker is a Soot-based bytecode transformer that instruments distributed system bytecode to enable "dry-run" recovery execution with isolated I/O and state, allowing operators to test recovery strategies safely before performing real recovery.

The main component is the **Instrumentation Engine** (`src/`): a Soot-based bytecode transformer that rewrites target system classes to enable pilot execution.

## Build Commands

### Instrumentation Engine (root Maven project)
```bash
# Build (creates target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar)
mvn clean package -DskipTests

# Or via the engine script
./run_engine.sh build
```

### Running the Instrumentation Engine
```bash
./run_engine.sh transform <config-file>   # Transform target system bytecode
./run_engine.sh help                      # Print help
```

### Tests
```bash
mvn test    # JUnit 5 via Surefire
```

## Architecture

### Bytecode Transformation Pipeline (`GraphCheckerTransformer.instrument()`)

The engine processes target system classes through these ordered phases:

1. **IO Isolation** — Redirects all file I/O to `/opt/ShadowDirectory`
2. **HTTP Hook Injection** — Adds OpenTelemetry baggage to HTTP headers for context propagation
3. **Method Divergence** — For each method, creates `method$instrumentation()` (dry-run) and `method$original()` variants; the original method checks `isDryRun()` to dispatch
4. **State Redirection** — Redirects field reads/writes to `org.pilot.State` class for isolation
5. **Baggage Propagation** — Wraps context-passing constructs (Runnables, Futures, condition variables, executor submissions)
6. **Context Tracking** — Injects OpenTelemetry initialization into configured classes
7. **Sanitization** — Final validation and cleanup

### Key Source Packages (Engine — `src/main/java/edu/uva/liftlab/graphchecker/`)

| Package | Purpose |
|---------|---------|
| `transformer/` | Main orchestration: `GraphCheckerTransformer` drives the pipeline |
| `generator/` | `GraphCheckerMethodGenerator` creates diverged method variants |
| `isolation/IO/` | IO handler strategy classes (`FileOutputStreamHandler`, `FileChannelHandler`, `PathHandler`, etc.) |
| `isolation/stateredirection/` | `StateRedirection` + `ClassFilterHelper` for field-level state isolation |
| `distributedtracing/` | `BaggagePropagation`, `HTTPPropagator`, and parameter wrappers for cross-thread/cross-process context |
| `option/` | CLI parsing via Apache Commons CLI |
| `staticanalysis/` | Recovery pattern detection |

Entry point: `GraphCheckerMain.java` — initializes Soot, registers `GraphCheckerTransformer`, and runs the transformation.

### Configuration System

Target system behavior is controlled via `.properties` files (see `experiments/solr17515/conf/` for examples). Key sections parsed by `ClassFilterHelper`:

- `blacklist_pilotfunc_classes` / `whitelist_pilotfunc_classes` — Control method divergence scope
- `blacklist_state_classes` / `whitelist_state_classes` — Control state isolation scope
- `http_send_classes` / `http_recv_classes` — HTTP context propagation targets
- `io_classes` — I/O-intensive classes for isolation
- `seda_queue` / `seda_worker` — SEDA queue instrumentation
- `entry_classes` / `startpoint_methods` — Recovery entry points

## Technical Notes

- Java 8 source/target
- Uses **Soot 4.4.1** for bytecode analysis/transformation (Jimple IR)
- The `src/recipes/java` directory is included as an additional source root via build-helper-maven-plugin
- `org.pilot.*` references in the code are EXTERNAL runtime dependencies — do NOT rename these



