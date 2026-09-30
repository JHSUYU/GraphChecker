# The one harness every case runs through

A case directory under `experiments/<system>/` holds DECLARATIONS only:

| file | what it declares |
| --- | --- |
| `case.sh` | per case id: the system's worktree (`repo`), the workload (`test_class`, `test_method`), the declared target (`target_occurrence`), the analysis `scope`, and optionally `loop_bounds`, `target_spec`, `classpath_test`, `workload_properties` (and Hadoop's `hadoop_javac`) |
| `workflow.properties` | the campaign's budgets and inputs |
| `target.yaml`, `*.jsonl` | the target (`exception_target: <name> <binary class name> <source line> [<thrown type>]`: no annotation, no tree rebuild), communication mappings, symbolic inputs, root domains, loop bounds |

Everything executable is here, one copy for every case:

```bash
lib/run.sh <case dir> <case id> build|config|validate|slice|campaign
```

`slice` runs SEED's static half alone (the case's scope copied in, the seed
analysis with the scope grown): the static artifacts an ad-hoc selection
scores (`tools/adhoc/slice.sh`, `score.py`), with no workload run.

| script | role |
| --- | --- |
| `case-env.sh` | sourced by every script: reads the system's `system.sh`, then `case.sh`, and derives paths |
| `run.sh` | the launcher: the case's declarations become the campaign environment, then `run_engine.sh` |
| `execute.sh` | one workload JVM: the recording, or a concolic replay |
| `prepare-analysis.sh` | copies the declared scope into the classes directory the weave reads |
| `classpath.sh` | the workload classpath, as the system's `system.sh` reads it off a test report (`experiments/<system>/classpath.py`) |
| `java.sh` | the engine JVM |

The discovery hook is the same for every case: with
`CAUSYNTH_TARGET_OCCURRENCE_OVERRIDE=""` PLAN refuses with
`DECLARED_TARGET_OCCURRENCE_MISSING` and lists every observed target
occurrence.

The Hadoop side of a case calls the GraphChecker Hadoop shim
(`src/shim/java`, the `hadoop-shim` classifier jar): no tree carries its own
facade.  A workload registers every node through
`org.apache.hadoop.hdfs.server.datanode.CausynthCluster` before any traffic,
and opens the recorded window with it.  Daemons are not suppressed (owner
ruling 2026-09-23: they take part in the coordination a case is about).  A
daemon's work that crosses a queue carries its scope across it -- the IPC
server's call queue, the DataNode actor's command processor -- so a key update
a daemon heartbeat took is still a recorded delivery with its IPC doors.  The
schedule reproduces daemons -- before a replay's cut event by event, and after
it in their timeouts, so a daemon turn the recording took after the
workload's own request is not taken before it just because the replay runs
many times slower than the recording did.  More rules keep the world the
window starts from the same in every run, because the schedule orders only
the window itself:

- the cluster's configuration goes through `CausynthCluster.configure`, so
  nothing set up before the window expires on the wall clock (the recording
  runs on a JIT, every replay on an interpreter many times slower);
- a per-node loop inside the window takes `CausynthCluster.dataNodes()`,
  which is in the order of the nodes' registered names, because which
  physical node plays which role is the cluster's random choice;
- the cluster is built with
  `.dataNodeConfOverlays(CausynthCluster.dataNodeOverlays(n))`, so each
  DataNode has IPC connections of its own, as a DataNode process does: in
  one JVM the DataNodes otherwise share one NameNode connection whose
  threads belong to whichever node opened it first;
- the block a case reads its roles off is written with
  `CausynthCluster.createOnNode(fs, path, holder)` and the workload asserts
  it landed on `holder`, because random replication-1 placement makes a
  different started node play each role in every run.  A case whose roles
  come from an erasure-coded group names its nodes by block index instead;
- every wait the workload makes inside its window for its own results is
  bounded by `CausynthCluster.WINDOW_WAIT_MS` (60 s): a replay that cannot
  hold its prefix stalls every thread for the watchdog's 15 s before it runs
  free, and a workload that gives up first fails for the engine's reason.
- a check inside the window of what a witness exists to change -- a key a
  node must still retain, the rotation gap, a cached key id -- is
  `CausynthCluster.recordingPrecondition(() -> ..., message)`: asserted in
  the recording and a native run, never evaluated in a replay, whose world
  the engine chose and where the check would end the witness before the
  anchor (hdfs-17967 path B lost all 22 of its admitted replays so).  Only
  reads go in the supplier: a call that acts, or that is itself a recorded
  occurrence, stays in every run and only its result is checked.

## The block-key window: the key flows the RPC's way

Every tree of the block-key family (hdfs-17899 bug1/2/3, hdfs-17897, hdfs-17967
A/B/C) carries 11741's expiry check, so a key goes stale there only through a
failed RPC (PIPELINE §12, the owner's ruling). A workload of the family is
therefore written so that the verifying node's key arrives over an RPC INSIDE
the window, and the consumer presents that key:

1. inside the window the master rotates (`updateKeys`, as a `KEY_MANAGER_TICK`
   of the request that owns the rotation);
2. every node that will verify a key takes the master's new keys over its OWN
   NameNode RPC inside the window — its heartbeat, whose answer carries the
   `KeyUpdateCommand` — through the IPC doors, whose fault points
   (`FAULT:HADOOP_IPC:REQUEST`, `FAULT:HADOOP_IPC:RESPONSE`) are the witness;
   the workload marks each node for a key update and sends one heartbeat
   per node; whichever heartbeat of the node reaches the NameNode first --
   the workload's or the node's own daemon -- delivers the keys, and its
   IPC doors are the witness;
3. the consumer (Balancer, SPS, a source DataNode, the client) then takes the
   master's CURRENT key — over its own in-window RPC where it has one — and
   presents it in the transfer the target check verifies.

The recording succeeds (a `recordingPrecondition` checks the verifier holds
the presented key); a world whose step-2 delivery failed has the verifier
without it, which is the fatal. No workload of the family relies on a key
expiring: the clocks stay at the recording in every accepted witness.
