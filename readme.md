# GraphChecker

GraphChecker is now a minimal Soot-based bytecode processing skeleton.

The project keeps only the plumbing needed to:

- parse command-line input;
- configure Soot classpaths, input directories, input jars, and output;
- load target classes;
- run one registered whole-program Soot phase;
- leave an empty `GraphCheckerTransformer` for future analysis or transformation logic.

All previous grey-state, OpenTelemetry, context propagation, state tracing, and HDFS-specific analysis logic has been removed.

## Build

```bash
mvn clean package -DskipTests
```

This produces:

```text
target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
```

## Run

Process a directory of compiled classes:

```bash
java -cp target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar \
  edu.uva.liftlab.graphchecker.GraphCheckerMain \
  -i /path/to/classes \
  -x /path/to/dependencies/* \
  -o /path/to/output
```

Process a jar:

```bash
java -cp target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar \
  edu.uva.liftlab.graphchecker.GraphCheckerMain \
  -j /path/to/app.jar \
  -x /path/to/dependencies/* \
  -o /path/to/output
```

Disable output when only loading and visiting classes:

```bash
java -cp target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar \
  edu.uva.liftlab.graphchecker.GraphCheckerMain \
  -i /path/to/classes \
  -x /path/to/dependencies/* \
  --no_output
```

## Extension Point

Future work should start in:

```text
src/main/java/edu/uva/liftlab/graphchecker/transformer/GraphCheckerTransformer.java
```

The current transformer only visits application classes and counts concrete methods. It does not mutate bytecode.
