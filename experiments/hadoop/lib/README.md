# The one harness every case runs through

A case directory under `experiments/hadoop/` holds DECLARATIONS only:

| file | what it declares |
| --- | --- |
| `case.sh` | per case id: the Hadoop worktree (`repo`), the workload (`test_class`, `test_method`), the declared target (`target_occurrence`), the analysis `scope`, and optionally `loop_bounds`, `target_spec`, `hadoop_javac` |
| `workflow.properties` | the campaign's budgets and inputs |
| `target.yaml`, `*.jsonl` | the target, communication mappings, symbolic inputs, root domains, loop bounds |

Everything executable is here, one copy for every case:

```bash
lib/run.sh <case dir> <case id> build|config|validate|campaign
```

| script | role |
| --- | --- |
| `case-env.sh` | sourced by every script: reads `case.sh` and derives paths; holds the block-key family's shared scope (`blockkey_scope`) |
| `run.sh` | the launcher: the case's declarations become the campaign environment, then `run_engine.sh` |
| `execute.sh` | one workload JVM: the recording, or a concolic replay |
| `prepare-analysis.sh` | copies the declared scope into the classes directory the weave reads |
| `classpath.sh`, `classpath.py` | the workload classpath, read off the case's own surefire report |
| `build.sh` | builds the case's Hadoop tree and runs its workload once natively |
| `java.sh` | the engine JVM |

The discovery hook is the same for every case: with
`CAUSYNTH_TARGET_OCCURRENCE_OVERRIDE=""` PLAN refuses with
`DECLARED_TARGET_OCCURRENCE_MISSING` and lists every observed target
occurrence.

The Hadoop side of a case calls the GraphChecker Hadoop shim
(`src/shim/java`, the `hadoop-shim` classifier jar): no tree carries its own
facade.  A workload registers every node through
`org.apache.hadoop.hdfs.server.datanode.CausynthCluster` before any traffic,
and opens the recorded window with it.  Daemons are not suppressed: the
schedule prefix reproduces them.  Two more rules keep the world the window
starts from the same in every run, because the prefix orders only the window
itself:

- the cluster's configuration goes through `CausynthCluster.configure`, so
  nothing set up before the window expires on the wall clock (the recording
  runs on a JIT, every replay on an interpreter many times slower);
- a per-node loop inside the window takes `CausynthCluster.dataNodes()`,
  which is in the order of the nodes' registered names, because which
  physical node plays which role is the cluster's random choice.
