# HBase Java 8 Zero VM pressure run

This adapter runs one mini-cluster JUnit method in one JVM and records elapsed
time, peak RSS, a per-second Java RSS/thread sample, host available memory,
swap use, the full test log, and exit code. The default is the one-RegionServer
`TestMultiActionMetricsFromClient#testMultiMetrics` method. `--large` chooses
`TestClientClusterStatus#testNone`, whose setup starts three Masters, five
RegionServers, and five DataNodes.

Build the Java 8 HBase worktree first. Then run from this directory:

```bash
./run.sh
./run.sh --large --heap 16g --timeout 90m
```

The runner accepts any no-argument JUnit 4/5 `@Test` method with no-argument
lifecycle methods. `JUnitMethodRunner` invokes `@BeforeAll`, `@BeforeEach`, the selected method,
`@AfterEach`, and `@AfterAll` reflectively. It does not run Jupiter extensions,
parameterized tests, or parameter injection. In particular,
`TestResultSizeEstimation` has `@BeforeEach setUp(TestInfo)` and cannot be run
through this adapter without runner support.

For a stock Java 8 baseline, set `VM_HOME=/usr/lib/jvm/java-8-openjdk-amd64`
and pass the same `--test` and `--heap`. Use `--classpath-file FILE` to reuse a
Maven test-dependency classpath. Without it, the script generates one from the
**Java 8 worktree** with `dependency:build-classpath`; core HBase Maven jars are
replaced with this worktree's `target/classes` or `target/test-classes` and a
path into `/u/vnr3ne/hbase` is rejected. The requested test class must have
Java 8 bytecode.

Each run creates a fresh directory under `/tmp/graphchecker-hbase-jdk8-pressure`.
Its `jvm.log`, `time.txt`, `samples.csv`, `exit-code.txt`, `run-info.txt`, and
`classpath.txt` remain for comparison. `latest-run` names the newest run.

By default this measures **custom Zero VM execution**, with no symbolic task.
For one actual GraphChecker concolic task, additionally pass `--plan FILE
--task-id ID --classes DIR`. The instrumented classes precede the worktree
classes in the JVM classpath, and the run writes `concolic-results.jsonl` plus
session rows under its run directory.

For a full GraphChecker campaign with several worker JVMs, monitor the process
tree rooted at the campaign launcher's PID:

```bash
./sample_process_tree.py --root-pid "$campaign_pid" \
  --output "$run_dir/campaign-samples.csv" \
  --summary "$run_dir/campaign-summary.json"
```

The CSV records the number and PIDs of live Java descendants, their combined
RSS and threads, total process-tree RSS, host available memory, and swap used.
The JSON records observed peaks and minimum available memory. The sampler
follows surviving worker JVMs if their parent exits, and stops after the whole
observed tree exits or it receives SIGTERM.
