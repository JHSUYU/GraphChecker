# Tree edits captured for hdfs-17899

Captured 2026-09-16 by the FINAL HANDOVER TASK A sweep (opus-impl, planner Fable 5.1).

## Why this directory exists

The mandate assumed these trees had no `.git`. They do: each is a **git worktree of
`/opt/hadoop`** (`.git` is a gitdir pointer file, e.g. `gitdir: /opt/hadoop/.git/worktrees/<tree>`),
each checked out on its own `gc/...` branch.

**All of these branches are now pushed** to `git@github.com:JHSUYU/hadoop.git`. The tree edits
listed below were committed onto each branch on 2026-09-16 and pushed, so the file copies in
this directory are **the same content as those commits** — not a separate or divergent version.

| tree | branch | pushed sha (contains these edits) |
|---|---|---|
| `hadoop-hdfs-11741` | `gc/hdfs-11741-current` | `eed1f3a1ad16871bda4ccd46329584fbff5116e5` |
| `hadoop-hdfs-17897` | `gc/hdfs-17897-striped-checksum` | `737b2c00a18a094d6427a976bd31ec5011431c01` |
| `hadoop-hdfs-17899-base` | `gc/hdfs-17899-wire-base` | `c92fdab813ed37a7ffa62e69c99005c1ce2fb807` |
| `hadoop-hdfs-17899-bug1` | `gc/hdfs-17899-bug1` | `5dcf40938953773e91c0f7eaea8ffc92bbdc6472` |
| `hadoop-hdfs-17899-bug2` | `gc/hdfs-17899-bug2` | `f1133eb328bf075174632c570b0f409215129b42` |
| `hadoop-hdfs-17899-bug3` | `gc/hdfs-17899-bug3` | `615f836ee5c21f8137bc3c4696cde5dc91498b94` |

The two sibling HDFS-17960 trees are ordinary clones (not worktrees) and were committed and
pushed the same day; they are listed here only for completeness and are **not** copied into
this directory:

| tree | branch | pushed sha |
|---|---|---|
| `hadoop-hdfs-17960` | `gc/hdfs-17960-snapshot-replay` | `8ad9132e3b50a9bf645526f34bf01c8863d6acf3` |
| `hadoop-hdfs-17960-jdk8` | `gc/hdfs-17960-snapshot-replay-jdk8` | `f1f863e984471d63fb0645c6d6b2fffa3dc6055e` |

The files are copied here verbatim so that **the GraphChecker repository is self-sufficient
once this host is reclaimed**: the case work can be read and re-applied without access to
`/opt/hadoop*` or to the Hadoop fork.

(Correction: an earlier draft of this file stated these branches had no `origin/` ref and were
unpushed. That was wrong — it was read off missing local `refs/remotes/origin/gc/*`
remote-tracking refs, which this repo never fetched; `git ls-remote` is the authority.)

## Upstream Hadoop revision

- Apache upstream base for every tree: **734dd8a67c** ("HADOOP-19863. Incorrect Vectored IO
  metrics from Local Filesystem. (#8447)"), the last non-GraphChecker commit under each branch.
- `hadoop-project/pom.xml` version: **3.6.0-SNAPSHOT**
- Repo remote: `git@github.com:JHSUYU/hadoop.git` (`origin/main` merge-base `ece33208b89a`)

## How the file set was chosen

The mandated "mtime newer than the tree's top-level `pom.xml`" criterion **degenerates** on
these trees: it selects ~3915 of 13209 source files, because a bulk pass re-stamped most of
the tree (11741: all 3915 land in the 2026-09-15 17:00-18:59 window) without changing content.
Every genuinely edited file is inside that set, so the set is a valid superset but useless as a
selector. The authoritative selector used here is `git status --porcelain` in the worktree,
unioned with the two other mandated criteria (files named in the known diffs; basename
matching `*Causynth*`). For every tree the diff-named and `*Causynth*` sets turned out to be
**subsets** of the git-status set, so nothing was selected on a weaker signal alone.
The `mtime>pom.xml` column below records the mandated criterion for audit.

Excluded: `target/`, `generated-sources/`, `.git/`, and all build output.

## Generated capture artifacts (per tree, under `<tree>/diffs/`)

- `generated-branch-commits.patch` - `git log -p 734dd8a67c..HEAD`, i.e. every GraphChecker
  commit on that unpushed branch.
- `generated-uncommitted.diff` - `git diff HEAD` as of capture, i.e. the tracked-file edits
  that were then committed as the branch's 2026-09-16 tip commit (see the table above).
  (Untracked files are copied whole; see the `git` column.)


## Tree `hadoop-hdfs-17899-base`

- path: `/opt/hadoop-hdfs-17899-base`
- branch: `gc/hdfs-17899-wire-base` (worktree of `/opt/hadoop`, pushed to origin)
- HEAD at capture: `824a7fafaa253f9ad8be5b4334755d90f7be32ef`
- HEAD after the 2026-09-16 commit of these edits (pushed): `c92fdab813ed37a7ffa62e69c99005c1ce2fb807`
- upstream base: `734dd8a67c`
- top-level `pom.xml` mtime (mandated pivot): 2026-09-02 22:58:08

### GraphChecker commits on this branch (734dd8a67c..HEAD)

- `824a7fafaa Expose SASL key id as a scalar wire endpoint`
- `ed2afa2c49 Add strict message-carried IPC and SASL propagation`

### Files copied

| file (relative to tree root) | git | mtime | mtime>pom.xml | known diff |
|---|---|---|---|---|
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/CausynthMessagePropagation.java` | modified | 2026-09-14 01:51:00 | yes | hadoop-hdfs-17899-base-call-carried-scope.diff |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/Client.java` | modified | 2026-09-14 01:51:00 | yes | hadoop-hdfs-17899-base-call-carried-scope.diff |

### Known diffs copied into `hadoop-hdfs-17899-base/diffs/`

- `hadoop-hdfs-17899-base-call-carried-scope.diff`
- `generated-branch-commits.patch` (generated)
- `generated-uncommitted.diff` (generated)

## Tree `hadoop-hdfs-17899-bug1`

- path: `/opt/hadoop-hdfs-17899-bug1`
- branch: `gc/hdfs-17899-bug1` (worktree of `/opt/hadoop`, pushed to origin)
- HEAD at capture: `a5aac692107dbf28b00b294902aeac688add4174`
- HEAD after the 2026-09-16 commit of these edits (pushed): `5dcf40938953773e91c0f7eaea8ffc92bbdc6472`
- upstream base: `734dd8a67c`
- top-level `pom.xml` mtime (mandated pivot): 2026-09-03 00:04:58

### GraphChecker commits on this branch (734dd8a67c..HEAD)

- `a5aac69210 Use real key propagation in the HDFS-17899 Balancer workload`
- `6bf1136d31 Complete HDFS-17899 Balancer causal workload`
- `efde1f22f9 Model multi-frame SASL as one causal exchange`
- `9a67a48cc8 Expose current block key as one wire scalar`
- `30857d4062 Build HDFS-17899 workloads for the concolic VM`
- `98b7ff1a94 Add HDFS-17899 Balancer causal workload`
- `2ac95d47dd Expose SASL key id as a scalar wire endpoint`
- `ed2afa2c49 Add strict message-carried IPC and SASL propagation`

### Files copied

| file (relative to tree root) | git | mtime | mtime>pom.xml | known diff |
|---|---|---|---|---|
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/CausynthMessagePropagation.java` | modified | 2026-09-14 19:46:04 | yes | d3-lineage-hdfs-17899-bug1.diff, hadoop-hdfs-17899-bug1-call-carried-scope.diff |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/CausynthSymbolicSource.java` | untracked | 2026-09-14 19:46:04 | yes | - |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/Client.java` | modified | 2026-09-14 19:46:04 | yes | hadoop-hdfs-17899-bug1-call-carried-scope.diff |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/Server.java` | modified | 2026-09-14 19:46:04 | yes | d3-lineage-hdfs-17899-bug1.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferServer.java` | modified | 2026-09-14 19:47:30 | yes | d3-lineage-hdfs-17899-bug1.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager.java` | modified | 2026-09-14 19:47:30 | yes | expiry-root-hdfs-17899-bug1.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/balancer/KeyManager.java` | modified | 2026-09-14 19:47:30 | yes | d3-lineage-hdfs-17899-bug1.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/blockmanagement/HeartbeatManager.java` | modified | 2026-09-14 19:47:30 | yes | d3-lineage-hdfs-17899-bug1.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/BPServiceActor.java` | modified | 2026-09-14 19:47:30 | yes | d3-lineage-hdfs-17899-bug1.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/BlockReceiver.java` | modified | 2026-09-14 19:47:30 | yes | - |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/DataXceiver.java` | modified | 2026-09-14 19:47:30 | yes | d3-lineage-hdfs-17899-bug1.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/test/java/org/apache/hadoop/hdfs/server/balancer/TestBalancer.java` | modified | 2026-09-14 19:48:09 | yes | d3-rotation-scope-hdfs-17899-bug1.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/test/java/org/apache/hadoop/hdfs/server/balancer/TestBalancerWithEncryptedTransfer.java` | modified | 2026-09-14 19:48:09 | yes | d3-rotation-scope-hdfs-17899-bug1.diff |

### Known diffs copied into `hadoop-hdfs-17899-bug1/diffs/`

- `d3-lineage-hdfs-17899-bug1.diff`
- `d3-rotation-scope-hdfs-17899-bug1.diff`
- `hadoop-hdfs-17899-bug1-call-carried-scope.diff`
- `expiry-root-hdfs-17899-bug1.diff`
- `loop-bounds-after-call-carried-scope.diff`
- `generated-branch-commits.patch` (generated)
- `generated-uncommitted.diff` (generated)

## Tree `hadoop-hdfs-17899-bug2`

- path: `/opt/hadoop-hdfs-17899-bug2`
- branch: `gc/hdfs-17899-bug2` (worktree of `/opt/hadoop`, pushed to origin)
- HEAD at capture: `a177d8daf9086b6165d2a9e2a5a85fc12dee5604`
- HEAD after the 2026-09-16 commit of these edits (pushed): `f1133eb328bf075174632c570b0f409215129b42`
- upstream base: `734dd8a67c`
- top-level `pom.xml` mtime (mandated pivot): 2026-09-03 00:05:12

### GraphChecker commits on this branch (734dd8a67c..HEAD)

- `a177d8daf9 Use real IPC key refresh in the HDFS-17899 SPS workload`
- `d72729d022 Complete HDFS-17899 SPS causal workload`
- `f9b017dda0 Model multi-frame SASL as one causal exchange`
- `4f79527b91 Expose current block key as one wire scalar`
- `431cd27fe6 Build HDFS-17899 workloads for the concolic VM`
- `082ac046c4 Add HDFS-17899 SPS causal workload`
- `2ac95d47dd Expose SASL key id as a scalar wire endpoint`
- `ed2afa2c49 Add strict message-carried IPC and SASL propagation`

### Files copied

| file (relative to tree root) | git | mtime | mtime>pom.xml | known diff |
|---|---|---|---|---|
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/CausynthMessagePropagation.java` | modified | 2026-09-14 19:46:04 | yes | d3-lineage-hdfs-17899-bug2.diff, hadoop-hdfs-17899-bug2-call-carried-scope.diff |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/CausynthSymbolicSource.java` | untracked | 2026-09-14 19:46:04 | yes | - |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/Client.java` | modified | 2026-09-14 19:46:04 | yes | hadoop-hdfs-17899-bug2-call-carried-scope.diff, bug2-marker-hoist.diff |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/Server.java` | modified | 2026-09-14 19:46:04 | yes | d3-lineage-hdfs-17899-bug2.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferServer.java` | modified | 2026-09-14 19:47:30 | yes | d3-lineage-hdfs-17899-bug2.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager.java` | modified | 2026-09-14 19:47:30 | yes | expiry-root-hdfs-17899-bug2.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/balancer/KeyManager.java` | modified | 2026-09-14 19:47:31 | yes | d3-lineage-hdfs-17899-bug2.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/blockmanagement/HeartbeatManager.java` | modified | 2026-09-14 19:47:31 | yes | d3-lineage-hdfs-17899-bug2.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/BPServiceActor.java` | modified | 2026-09-14 19:47:31 | yes | d3-lineage-hdfs-17899-bug2.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/BlockReceiver.java` | modified | 2026-09-14 19:47:31 | yes | - |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/DataXceiver.java` | modified | 2026-09-14 19:47:31 | yes | d3-lineage-hdfs-17899-bug2.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/test/java/org/apache/hadoop/hdfs/server/sps/TestExternalStoragePolicySatisfier.java` | modified | 2026-09-14 19:48:13 | yes | d3-rotation-scope-hdfs-17899-bug2.diff, hadoop-hdfs-17899-bug2-daemon-wait.diff |

### Known diffs copied into `hadoop-hdfs-17899-bug2/diffs/`

- `d3-lineage-hdfs-17899-bug2.diff`
- `d3-rotation-scope-hdfs-17899-bug2.diff`
- `hadoop-hdfs-17899-bug2-call-carried-scope.diff`
- `expiry-root-hdfs-17899-bug2.diff`
- `bug2-marker-hoist.diff`
- `hadoop-hdfs-17899-bug2-daemon-wait.diff`
- `loop-bounds-after-call-carried-scope.diff`
- `generated-branch-commits.patch` (generated)
- `generated-uncommitted.diff` (generated)

## Tree `hadoop-hdfs-17899-bug3`

- path: `/opt/hadoop-hdfs-17899-bug3`
- branch: `gc/hdfs-17899-bug3` (worktree of `/opt/hadoop`, pushed to origin)
- HEAD at capture: `fe90ac77ffd1c60b6f2e4795b30d077b531d0502`
- HEAD after the 2026-09-16 commit of these edits (pushed): `615f836ee5c21f8137bc3c4696cde5dc91498b94`
- upstream base: `734dd8a67c`
- top-level `pom.xml` mtime (mandated pivot): 2026-09-02 23:44:24

### GraphChecker commits on this branch (734dd8a67c..HEAD)

- `fe90ac77ff Use real IPC key refresh in the HDFS-17899 DataNode workload`
- `dfc554b582 Complete HDFS-17899 DataNode causal workload`
- `e73df61bf0 Keep stale DataNode key stable in HDFS-17899 workload`
- `7cb2e5f264 Model multi-frame SASL as one causal exchange`
- `7d703fd337 Expose current block key as one wire scalar`
- `8dc94162e4 Build HDFS-17899 workloads for the concolic VM`
- `9d975a4265 Add HDFS-17899 DataTransfer causal workload`
- `ea164ee9e1 Expose SASL key id as a scalar wire endpoint`
- `ed2afa2c49 Add strict message-carried IPC and SASL propagation`

### Files copied

| file (relative to tree root) | git | mtime | mtime>pom.xml | known diff |
|---|---|---|---|---|
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/CausynthMessagePropagation.java` | modified | 2026-09-14 19:41:26 | yes | d3-lineage-hdfs-17899-bug3.diff, hadoop-hdfs-17899-bug3-call-carried-scope.diff |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/CausynthSymbolicSource.java` | untracked | 2026-09-14 19:41:26 | yes | - |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/Client.java` | modified | 2026-09-14 19:41:26 | yes | hadoop-hdfs-17899-bug3-call-carried-scope.diff |
| `hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/Server.java` | modified | 2026-09-14 19:41:26 | yes | d3-lineage-hdfs-17899-bug3.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferServer.java` | modified | 2026-09-14 19:42:52 | yes | d3-lineage-hdfs-17899-bug3.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager.java` | modified | 2026-09-14 19:42:52 | yes | - |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/balancer/KeyManager.java` | modified | 2026-09-14 19:42:52 | yes | d3-lineage-hdfs-17899-bug3.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/blockmanagement/HeartbeatManager.java` | modified | 2026-09-14 19:42:53 | yes | d3-lineage-hdfs-17899-bug3.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/BPServiceActor.java` | modified | 2026-09-14 19:42:53 | yes | d3-lineage-hdfs-17899-bug3.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/BlockReceiver.java` | modified | 2026-09-14 19:42:53 | yes | - |
| `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/datanode/DataXceiver.java` | modified | 2026-09-14 19:42:53 | yes | d3-lineage-hdfs-17899-bug3.diff |
| `hadoop-hdfs-project/hadoop-hdfs/src/test/java/org/apache/hadoop/hdfs/server/datanode/TestCausynthDataTransferRpcFailure.java` | modified | 2026-09-14 19:43:33 | yes | d3-rotation-scope-hdfs-17899-bug3.diff |

### Known diffs copied into `hadoop-hdfs-17899-bug3/diffs/`

- `d3-lineage-hdfs-17899-bug3.diff`
- `d3-rotation-scope-hdfs-17899-bug3.diff`
- `hadoop-hdfs-17899-bug3-call-carried-scope.diff`
- `expiry-root-at-every-key-construction.diff`
- `loop-bounds-after-call-carried-scope.diff`
- `generated-branch-commits.patch` (generated)
- `generated-uncommitted.diff` (generated)
