# START HERE: the 16 ZooKeeper cases on CloudLab (system/zookeeper-cloudlab, 2026-10-25)

You take over GraphChecker's ZooKeeper group as it runs on a five-node CloudLab cluster. This file is self-contained:
the goal, what the branch holds, the cluster and its parallel strategy, the results, how to run a case and the whole
series, what is left, and the rules. The liftlab takeover file of the same group is
[zookeeper-START-HERE.md](zookeeper-START-HERE.md) (`system/zookeeper`, 2026-10-22); HBase's is
[hbase-START-HERE.md](hbase-START-HERE.md); HDFS on CloudLab is the branch `system/hdfs-cloudlab`.

- **Repo:** `git@github.com:JHSUYU/GraphChecker.git`, branch **`system/zookeeper-cloudlab`** (on the cluster:
  `/bulk/GraphChecker`, integration worktree `/bulk/wt/gc-zk-cloudlab`).
- **The tree:** the fork `https://github.com/JHSUYU/zookeeper.git`, branch `graphchecker/zookeeper-checks` (889f0e96:
  the liftlab head 51b21356 plus this branch's two workarounds; local `/bulk/zookeeper`, branch `gc/zk-cloudlab`).
  Tree sets (worktrees of `/bulk/zookeeper`, each with its Maven repository `/bulk/m2/zk<k>/zookeeper-checks`):
  `/bulk/trees/zk3` (889f0e96, the final rounds), `zk2` (7aa086bb), `zk1` (51b21356, natives only).
- **VM image:** `/bulk/vm/zookeeper/j2sdk-image` (this branch's VM sources, `tools/vm/build-image-docker.sh`).
- **From GitHub:** [../REPRODUCE.md](../REPRODUCE.md) §8 makes the cluster, the image and the tree and runs the series.

## 1. The goal and what was done

The owner (2026-10-25): "git clone我的zookeeper代码git@github.com:JHSUYU/zookeeper.git。请你把system/zookeeper分支也改造成
system/zookeeper-cloudlab zookeeper之前在别的服务器集群跑通了全部的adhoc check，现在，请你把多个node的利用也适配到我们这里的cloudlab。
请你思考这么一个问题，我们的cloudlab一般是5个节点，是大内存。这点和之前的liftlab不同。所以在system/hdfs-cloudlab和
system/zookeeper-cloudlab上，我们的并行策略要最大化cloudlab集群的使用。然后你优化好，让zookeeper的所有adho check检查也都能跑通".

What changed against `system/zookeeper` (git log has each commit):
- **CloudLab's layer** from `system/hdfs-cloudlab`: hosts node0-node4 and `/bulk` (`tools/lib/gc-env.sh`), the host
  ledger charging cores beside memory, every choice among hosts by free cores first, `tools/cloudlab/setup-nodes.sh`
  and `tools/vm/build-image-docker.sh`, OPERATIONS §11, LESSONS §11.
- **The parallel strategy for five big-memory nodes** ([PARALLEL.md](PARALLEL.md) §8, on both CloudLab branches): cores
  bind here, not memory (5 x 40 logical cores x 251 GB against liftlab's 14 x 48 x 30 GB), so
  - the ledger charges hundredths of a core and a replay its measured mean, not its 90th percentile rounded up;
  - a node's busy cores are the lesser of its charges and its load plus what its newest starts have yet to add to it
    (idle resident solvers keep their charges); a node's 40 logical cores are 20 physical ones, and admitting by idle
    logical CPUs instead was measured slower (Z5, P4) and reverted;
  - a round is one pool of every case (`tools/rounds/run-pool.sh`): longest expected first, a start whenever a tenth
    of the cluster's cores is free, its head on the node heading the fewest; no lanes and no alone reruns.
- **Two workarounds in the fork** (STATUS "Per-system surface", ZooKeeper column): `QuorumBase` starts its peers from
  the highest server id down (zk-adhoc-02's setUp elected two leaders in 4 of 9 native runs), and in a workload a
  wait of `CONNECTION_TIMEOUT` or more for a server to come up never times out (06's and 12's startup recordings
  came up past the test's 30 s in the replay).
- **results/zookeeper:** `final-stats.py` and `collect-results.sh` read CloudLab's run names (`accept-<round>-<case
  less its first word>`).

## 2. Results

The CloudLab rounds Z1-Z9 (2026-10-25, `/bulk/gc-out/zk-final`; every case's table row and reading:
`results/zookeeper/README.md` "On CloudLab"). Z4 (snapshot `/bulk/gc-run/zkF4` = 16ca5f402, tree set `/bulk/trees/zk3`,
16 cases at once beside the HDFS pool P3, 2.5 h) is the run of record of 15 cases (06's stays liftlab's):

| case | CloudLab (run, wall) | liftlab |
| --- | --- | --- |
| zk-bugs-quota-init | **PASS**: SAT MARKER_FLIPPED, native 10/10 (Z4, 863 s) | PASS 10/10 |
| zk-bugs-election-offer | **PASS**: SAT STATE_PAIRING_FLIPPED after 10 refuted claims, native 9/10 (Z4, 2971 s) | PASS 10/10 |
| zk-bugs-container-reuse | **PASS**: SAT STATE_PAIRING_FLIPPED, native 10/10 (Z4, 1699 s) | PASS 10/10 |
| zk-bugs-retry-seq-quota | **PASS**: SAT MARKER_FLIPPED, native 10/10 (Z4, 1659 s) | PASS 10/10 |
| zk-bugs-observer-master | **PASS**: SAT STATE_PAIRING_FLIPPED, native 7/10 (Z4, 1282 s) | PASS 4/10 |
| zk-bugs-trunc-sync | not detected: the formula UNSAT_CLOSED, as liftlab's; the run RUN_DEFECT by one BLOCKING gap, an inherited flip one session stated no decision for (Z4, 8247 s; Z9 alone, 4884 s, the same gap on the same obligation: TODO ZooKeeper on CloudLab 2) | not detected, UNSAT_CLOSED |
| zk-adhoc-01 | SAT_UNCONFIRMED: CONFIRM refused the claim (Z4, 3059 s) | the same |
| zk-adhoc-02 | SAT_UNCONFIRMED: every claim refuted by CONFIRM (Z4, 8946 s) | the same |
| zk-adhoc-03 | SAT CLOCK_SKEW, confirmed, native 4/10 (Z4, 1541 s) | the same, 4/10 |
| zk-adhoc-04 | UNSAT_CLOSED, substantive, 6 of 6 paths free (Z4, 1967 s) | substantive |
| zk-adhoc-06 | **not run through**: RUN_DEFECT at REPLAY in seven runs, its recorded election does not replay here (TODO ZooKeeper on CloudLab 1) | UNSAT substantive |
| zk-adhoc-07 | UNSAT_CLOSED, substantive (Z4, 2096 s) | substantive |
| zk-adhoc-10 | UNSAT_CLOSED, vacuous by construction (Z4, 1875 s) | vacuous, class C |
| zk-adhoc-11 | UNSAT_CLOSED, vacuous by construction, every fatal arm literal false (Z4, 8697 s) | vacuous, class C |
| zk-adhoc-12 | UNSAT_CLOSED, substantive (Z4, 2784 s) | substantive |
| zk-adhoc-13 | UNSAT_CLOSED, substantive (Z4, 534 s) | substantive |

So 15 of 16 cases reach their liftlab verdict on CloudLab; no new bug. The cluster: Z4 kept 54-59 % of the 200 logical
CPUs busy, the 20 physical cores of each node full; the HDFS named cases beside it ran 36 % faster summed than on the
first pool (P1 -> P3, PARALLEL §8.4). Per case the walls are 1.6-11.6x liftlab's (median about 2.6x: every case at
once here, liftlab's longer cases alone on 14 lifts); the serial seeding alone is 1.1-2.0x slower (older cores).

## 3. Read, in this order

1. This file, then `results/zookeeper/README.md` (the table and one reading per case).
2. [PARALLEL.md](PARALLEL.md) §8 and [OPERATIONS.md](OPERATIONS.md) §11: the cluster and the strategy.
3. [TODO.md](TODO.md) "ZooKeeper on CloudLab" and "ZooKeeper"; [LESSONS.md](LESSONS.md) §10 (ZooKeeper's traps), §11
   (CloudLab's).
4. `docs/checks/ZOOKEEPER.md` §E (the cases), STATUS "ZooKeeper checks" and "Per-system surface".
5. [RULES.md](RULES.md), [CHECKING.md](CHECKING.md), [AGENTS.md](AGENTS.md).

## 4. Running a case and the series

- **Snapshot:** `bash tools/lib/worktree-add.sh /bulk/gc-run/<name> <commit> --detach` (an explicit commit), then
  `ssh node2 'cd /bulk/gc-run/<name> && mvn -q -o package -DskipTests'`. Never rebuild a snapshot a run reads.
- **Tree set:** `git -C /bulk/zookeeper worktree add --detach /bulk/trees/zk<k>/zookeeper-checks <commit>`, copy a
  Maven repository to `/bulk/m2/zk<k>/zookeeper-checks`, then on a node `cd <worktree> && env
  PATH=/usr/lib/maven/bin:$PATH GC_TREES=/bulk/trees/zk<k> ZOOKEEPER_MAVEN_REPO=/bulk/m2/zk<k>/zookeeper-checks bash
  experiments/zookeeper/prepare-trees.sh` (16 PASSED lines, ~10-30 min). Never run natives on a tree a run reads.
- **One case:** `cd <snapshot> && env GC_OUT=/bulk/gc-out/zk-final GC_TREES=/bulk/trees/zk3
  CAUSYNTH_CUSTOM_JDK_HOME=/bulk/vm/zookeeper/j2sdk-image PRUNE=0 CASE_TIMEOUT_SECONDS=14400 tools/rounds/launch-run.sh
  <snapshot> <case> <ROUND>-<case less its first word>`.
- **The series:** from the snapshot, `(setsid nohup env GC_OUT=/bulk/gc-out/zk-final GC_TREES=/bulk/trees/zk3
  CAUSYNTH_CUSTOM_JDK_HOME=/bulk/vm/zookeeper/j2sdk-image PRUNE=0 POOL_EXPECTED=<case TAB seconds file>
  tools/rounds/run-pool.sh <ROUND> experiments/zookeeper/zookeeper-cases.tsv system/zookeeper=<snapshot> >
  /bulk/gc-out/zk-final/pool-<ROUND>.out 2>&1 < /dev/null &)`; `touch /bulk/gc-out/zk-final/series-<ROUND>.STOP` stops
  new starts, `tools/rounds/stop-run.sh <ROUND>-<case>` stops a case.
- **Reading:** `tools/rounds/round-status.sh <ROUND>`, `tools/analysis/vacuity.py --latest --detail <run>` on every
  UNSAT, `results/zookeeper/final-stats.py --order <rounds> --cases experiments/zookeeper/zookeeper-cases.tsv`,
  `results/zookeeper/collect-results.sh <rounds>`.

## 5. Rules you must keep

As [zookeeper-START-HERE.md](zookeeper-START-HERE.md) §5 and RULES.md: general fixes only; a workaround is small, makes
an order controllable or a value trackable, never switches the fatal outcome, and is named in STATUS "Per-system
surface"; the time model is handled by workarounds; the false-positive filter (CONFIRM/REPRODUCE) stays; at most 5
coding agents; kill only by explicit pid or process group (a `pgrep -f <pattern>` matches the shell that runs it);
never `git add -A`; commits as Zhenyu Li <zhl136@ucsd.edu> with the trailer `Co-Authored-By: Claude Opus 5.5
<noreply@anthropic.com>`. Parallelism serves throughput (owner 2026-10-06): judge a round by cases finished per hour
and by the CPUs' busy share, not by how many campaigns run.
