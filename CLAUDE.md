# CLAUDE.md

This repository is a minimal Soot-based bytecode processing skeleton.

## Build

```bash
mvn clean package -DskipTests
```

## Run

```bash
java -cp target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar \
  edu.uva.liftlab.graphchecker.GraphCheckerMain \
  -i /path/to/classes \
  -x /path/to/dependencies/* \
  -o /path/to/output
```

## Current Architecture

| Path | Purpose |
|---|---|
| `GraphCheckerMain.java` | Entry point; configures and runs Soot |
| `option/` | Minimal Apache Commons CLI parsing |
| `analysis/` | Soot phase metadata and registration |
| `transformer/GraphCheckerTransformer.java` | Empty transformer extension point |
| `util/` | Small helpers used by the Soot runner |

There is intentionally no active analysis or bytecode mutation logic. Future work should add it inside `GraphCheckerTransformer`.
