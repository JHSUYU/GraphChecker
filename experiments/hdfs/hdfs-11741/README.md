# HDFS-11741

This experiment targets the Hadoop source immediately before the HDFS-11741
fix:

```text
ece33208b89a6a06c1b362d10fab31343fe5df13
```

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
