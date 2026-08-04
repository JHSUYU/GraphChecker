# HDFS-11741

This experiment targets the Hadoop source immediately before the HDFS-11741
fix:

```text
ece33208b89a6a06c1b362d10fab31343fe5df13
```

The checkout may be this commit or a descendant that leaves
`KeyManager.java` unchanged, such as the local commit that adds optional
Causynth RPC tracing. `run.sh` verifies ancestry and the null-only
`KeyManager.newDataEncryptionKey()` guard. It refuses a descendant containing
the HDFS-11741 expiry fix, including a cherry-pick with a different commit id.

The patch only adds GraphChecker's class-retained fatal-target marker to the
`InvalidEncryptionKeyException` construction in
`BlockTokenSecretManager.retrieveDataEncryptionKey`. It does not change Hadoop
runtime behavior or apply the upstream bug fix.

Apply it from the root of a clean Hadoop checkout:

```bash
git checkout ece33208b89a6a06c1b362d10fab31343fe5df13
git apply --check \
  /opt/GraphChecker/experiments/hdfs/hdfs-11741/patches/mark-fatal-target.patch
git apply \
  /opt/GraphChecker/experiments/hdfs/hdfs-11741/patches/mark-fatal-target.patch
```

## Baseline workload

The experiment uses the existing Hadoop JUnit method:

```text
org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer#testEncryptedBalancer1
```

Prepare the pre-fix checkout, compile its main and test classes, materialize
the complete test-scope classpath, and run only that method:

```bash
experiments/hdfs/hdfs-11741/run.sh prepare
```

The individual steps are also available as `patch`, `build`, `classpath`, and
`baseline`. The generated classpath is written to:

```text
target/hdfs-11741/project-classpath.txt
```

## Prepare concolic tasks automatically

After `prepare` and a GraphChecker build, run the complete pre-concolic
pipeline with one command:

```bash
experiments/hdfs/hdfs-11741/run.sh tasks
```

`tasks` performs static analysis, the activation-envelope runtime pass, the
selected-region state/runtime pass, and task scheduling. It validates each
stage's artifacts. The final task plan must contain executable typed tasks
with the canonical `CFG_BACKEDGE` loop-bound contract.

The command stops at:

```text
target/hdfs-11741/schedule/execution_task_plan.jsonl
target/hdfs-11741/schedule/branch_queries.jsonl
```

It never starts the custom concolic JVM and does not run import, composition,
or reachability solving. An empty `branch_queries.jsonl` is valid before any
concolic result has been captured.

For a clean checkout, the fully automated preparation is:

```bash
experiments/hdfs/hdfs-11741/run.sh full-auto
```

`full-auto` applies the marker, builds and tests Hadoop, materializes the
classpath, builds GraphChecker, and then runs `tasks`. It has the same
pre-concolic stopping point.

`workflow.properties`, `target.yaml`, and `protocol-stubs.jsonl` define the
next GraphChecker phase. The protocol stub file explicitly connects the
logical NameNode/DataNode RPC methods and the encrypted SASL handshake; static
analysis does not infer these bridges from `Protocol`/`PB` class names.

Run the configured static analysis with:

```bash
experiments/hdfs/hdfs-11741/run.sh analyze
```

After static analysis, run the two runtime-analysis passes with:

```bash
experiments/hdfs/hdfs-11741/run.sh workload
```

The first pass selects concrete region activations. The second pass records
direct field identities and configured RPC endpoints, then writes the refined
graph and runtime region plans. This command does not start concolic replay.
