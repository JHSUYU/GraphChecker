# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

GraphChecker is a Soot-based bytecode transformer that injects **OpenTelemetry context propagation** at async boundaries in distributed system bytecode. It wraps async hand-off points (thread spawns, executor submissions, `CompletableFuture` chains, Guava `Futures`) with `Context.current().wrap(...)` so OTel context is preserved across threads.

## Build Commands

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

### Bytecode Transformation (`GraphCheckerTransformer.internalTransform()`)

The transformer iterates over all application classes and for each concrete method body scans statements for async boundary call sites. When found, it inserts two Jimple statements before the call:

1. `$ctx = staticinvoke Context.current()` — capture the current OTel context
2. `$wrapped = interfaceinvoke $ctx.wrap($arg)` — wrap the Runnable/Callable/Executor

The wrapped value replaces the original argument so OTel context flows across thread hand-offs.

**Covered async boundary patterns:**
- `Thread.<init>(Runnable)`
- `Executor.execute(Runnable)` / `ExecutorService.submit(Runnable|Callable)`
- `ScheduledExecutorService.schedule*(Runnable|Callable, ...)`
- `CompletableFuture.*Async(...)` — wraps trailing `Executor` arg
- Guava `Futures.addCallback` / `transformAsync` / `transform` — wraps trailing `Executor` arg

### Key Source Files (`src/main/java/edu/uva/liftlab/graphchecker/`)

| File/Package | Purpose |
|---|---|
| `transformer/GraphCheckerTransformer.java` | The single `SceneTransformer` — async boundary detection and `Context.wrap()` injection |
| `analysis/` | `AnalysisManager` and `PhaseInfo` — Soot phase registration |
| `option/` | CLI parsing via Apache Commons CLI (`OptionParser`, `GraphCheckerOptions`) |
| `util/ClassFilterHelper.java` | Config-driven class filtering (whitelist/blacklist) |
| `GraphCheckerMain.java` | Entry point — initializes Soot, registers the transformer, runs transformation |

### Configuration System

Controlled via `.properties` files (see `experiments/hdfs/conf/hdfs.properties`). Key options:

- `blacklist_pilotfunc_classes` / `whitelist_pilotfunc_classes` — Control which classes are instrumented
- `context_propagation_enabled` — Enable/disable OTel async boundary wrapping (default: true)
- `java_class_path` — JVM classpath for Soot resolution (must include all runtime deps of the target system)

## Technical Notes

- Java 8 source/target
- Uses **Soot 4.4.1** for bytecode analysis/transformation (Jimple IR)
- The `src/recipes/java` directory is included as an additional source root via build-helper-maven-plugin




