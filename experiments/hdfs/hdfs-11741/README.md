# HDFS-11741

This experiment runs the automatic bounded GraphChecker pipeline against the
Hadoop revision immediately before the HDFS-11741 fix:

```text
ece33208b89a6a06c1b362d10fab31343fe5df13
```

Start from that clean revision. The experiment applies one canonical runtime
patch (trace context, bounded workload knobs, and deterministic block-key
serials) plus the fatal-target marker. It rejects a checkout containing the
upstream expiry fix. The RPC hooks carry trace lineage only; endpoint, payload,
and value fingerprints are not part of the binding protocol.

The supported commands are:

```bash
# Patch/build Hadoop, construct its test classpath, and run the concrete test.
HADOOP_REPO=/opt/hadoop experiments/hdfs/hdfs-11741/run.sh prepare

# Automatic static analysis + two runtime passes + task generation.
HADOOP_REPO=/opt/hadoop experiments/hdfs/hdfs-11741/run.sh tasks

# Resume from an existing task plan: VM summaries, SMT, and Z3 only.
HADOOP_REPO=/opt/hadoop experiments/hdfs/hdfs-11741/run.sh candidates

# Complete pipeline: prepare, task discovery, VM summaries, SMT, and Z3.
HADOOP_REPO=/opt/hadoop experiments/hdfs/hdfs-11741/run.sh full
```

All experiment artifacts are rooted at `experiments-output/hdfs-11741`
(override with `HDFS11741_WORK_ROOT`), deliberately outside `target/` so
`mvn clean` cannot erase a recorded campaign. A tree recorded before this
change under `target/hdfs-11741` is still honored with a warning; migrate it
once with:

```bash
mv target/hdfs-11741 experiments-output/hdfs-11741
```

`config` and `validate` are read-only diagnostics. `traced-workload` is an
internal callback used by `workflow.properties`; it is not a separate workflow.
There is no public single-task, single-region, or single-target selector.

`tasks` stops before concolic execution and produces:

```text
experiments-output/hdfs-11741/analysis/symbolic_regions.jsonl
experiments-output/hdfs-11741/runtime/concolic_region_plan.jsonl
experiments-output/hdfs-11741/schedule/execution_task_plan.jsonl
experiments-output/hdfs-11741/schedule/branch_queries.jsonl
experiments-output/hdfs-11741/schedule/selected_target_binding.tsv
experiments-output/hdfs-11741/schedule/selected_closure_bindings.tsv
```

Scheduling is target-first. It takes the highest-ranked valid fatal target,
walks its trusted exact-port dependency closure, and schedules only that one
target goal plus the unique producer logical goals in the closure. Each goal
is selected with its region, runtime occurrence membership, and goal identity;
the occurrence is discovery evidence, while the emitted task retains the
logical replay identity. Per-goal scheduler outputs are isolated and then
merged deterministically by `taskId` and `queryKey`.

`full` does not hard-code thread ids, object ids, call ids, or HDFS region
names. Each selected task is instrumented and replayed by the custom VM; the
importer and composer consume those VM summaries directly. The SAT candidate
is retained at:

```text
experiments-output/hdfs-11741/candidates/<campaign>/candidate.smt2
experiments-output/hdfs-11741/candidates/<campaign>/z3-result.json
experiments-output/hdfs-11741/candidates/sat-result.json
```

Concolic execution keeps two bounded parallelism levels. Independent logical
region campaigns run in parallel (`HDFS11741_REGION_JOBS`, default 2), and one
campaign executes the sorted semantic path-seed/branch-flip frontier in
parallel (`HDFS11741_PATH_JOBS`, default 2). Every campaign and flip has a
private classes, test-data, log, result, and summary directory. Frontier
results are merged serially by canonical query key, and only the coordinator
performs partial-SAT probes, so concurrency does not change the composed
relation order.

All loops in a concolic task use the generic CFG-backedge limit of eight body
iterations; this applies to service loops without recognizing Hadoop method
names. The three HDFS workload activation knobs also default to eight so runtime
discovery cannot record an eighth or thirty-second occurrence that replay must
cut. `HDFS11741_NN_UPDATE_ITERATIONS`,
`HDFS11741_DATANODE_REFRESH_ITERATIONS`, and
`HDFS11741_BALANCER_REFRESH_ITERATIONS` may reduce that concrete evidence
window to 1--8; values above eight are rejected. Container materialization
currently retains up to eight failure-relevant cells per logical input port; this
is an independent exploration resource cap, not an assumption that an HDFS
container has length eight and never a way to increase loop execution.

The concrete workload is:

```text
org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer
  #testEncryptedBalancer1
```

The protocol mapping in `protocol-stubs.jsonl` declares the logical RPC pairs
and whether a server callback starts a new execution entry or remains nested in
its owning region. Runtime trace lineage chooses the actual occurrences; wire
payload equality is deliberately not revalidated.

The lightweight patch gate uses a temporary clean checkout and tests first and
idempotent second application:

```bash
experiments/hdfs/hdfs-11741/test_patch.sh
```
