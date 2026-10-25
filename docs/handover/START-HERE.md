# START HERE: the 46 HDFS cases on HBase's engine, on CloudLab (system/hdfs-cloudlab, 2026-10-24)

You take over GraphChecker's HDFS group as it runs on HBase's final engine and on a five-node CloudLab cluster. This
file is self-contained: the goal, what the branch holds, the cluster, the results, how to run a case and the whole
series, what is left, and the rules. The takeover files of the other systems are [hbase-START-HERE.md](hbase-START-HERE.md)
(HBase, `system/hbase`) and STATE §0/§S (HDFS's earlier bodies and Solr).

- **Repo:** `git@github.com:JHSUYU/GraphChecker.git`, branch **`system/hdfs-cloudlab`** (on the cluster: `/bulk/GraphChecker`,
  integration worktree `/bulk/wt/gc-hdfs-cloudlab`).
- **The trees:** the Hadoop fork `https://github.com/JHSUYU/hadoop.git`: `graphchecker/hdfs-checks` (44 cases: every case
  but hdfs-adhoc-21 and hdfs-11741), `graphchecker/hdfs-checks-adhoc21` (21), `graphchecker/hdfs-11741` (11741);
  `experiments/hadoop/trees.tsv`. On the cluster the tree sets (worktrees of `/bulk/hadoop`, each with its Maven
  repository `/bulk/m2/f<k>`): `/bulk/trees/f1` (the fork as F1 started: 75cb90e9dfe, 9478e60313f, 6c86fca9a2b), `f3`
  (0d2b473db63), `f5` (57e091c8af6), `f6` (899c200cc8e, the branch head); a tree a run reads is never rebuilt, so a tree
  change during a series is a new set.
- **From GitHub:** [../REPRODUCE.md](../REPRODUCE.md) §9 makes the cluster, the VM image and the trees and runs the series.

## 1. The goal and what was done

The owner's goal (2026-10-24, verbatim in STATE §C): read GraphChecker (every branch's docs) and the Hadoop fork's
`graphchecker/*` branches; take `system/hbase` as the base ("system/hbase的整个流程优化和system/hdfs已经有很大不同。所以我建议你从
system/hbase作为基准，开始迁移") and rebuild `system/hdfs` + `system/hdfs1` on its pipeline as `system/hdfs-cloudlab`, which
runs every HDFS ad hoc check of those two branches to its `.smt`, validates every SAT as HBase does (CONFIRM in the VM,
native REPRODUCE), applies all of HBase's process (results/, vacuity, the final series), adapts the fork's
`graphchecker/hdfs-checks` branch, and brings liftlab's parallel scheduling to CloudLab's node0-node4 ("内存很充足").

What changed against `system/hbase` (git log has each commit; STATUS "Per-system surface" and LESSONS §10 the why):
- **The Hadoop shim and its door entry points are back** (eb4b370c5): `src/shim` (the `hadoop-shim` classifier jar) and
  `MessageDoors#captureScope`, `#handingOff`/`#handedOff` (with Identity's received-message hand-off), `#received`,
  `#startupStep`/`#startupDone`, `#replaying`, `#outboundNone`, public `#setAside`/`#putBack`: what `system/solr`'s LOC 2a/2b
  deleted "system/hdfs keeps them". The trees call them unchanged.
- **CloudLab's scheduling** (agent L): the host ledger charges cores beside memory, across campaigns (a charge
  `<mb>.<cores>.<host>...`, `CAUSYNTH_HOST_MAX_CORES_PCT`), and every choice among hosts orders by free cores first; gc-env
  for node0-4 (`GC_BULK=/bulk`, `GC_REPO`, `GC_CONTROL_HOST` empty: every node heads); `tools/cloudlab/setup-nodes.sh`,
  `tools/vm/build-image-docker.sh`. CloudLab binds on cores (old E5-2660 v2, 40 logical / 20 physical per node), not memory.
- **DECIDE** (agent D, reviewed twice): a handed-on delivery of the path's own run is the path's own (a two-hop handoff's
  inner arm no longer reads as a re-pairing), and the own-witness pass asks each fatal-observing explored path once in its
  own run, its world's clocks held, within a sixth of the decide budget. hdfs-17897's replayed heartbeat fault is claimed
  MARKER_FLIPPED, no longer a refuted STATE_PAIRING model first.
- **REPRODUCE** keeps a turn-counted ORDER row in a world that plants no root (c8d40a5d8): hdfs-bugs-slowdisk-zero 10/10.
- **The HBase process for HDFS's declarations:** world depth 0 for every case (RULES), 11741 at 2 (two clocks), 07 at its
  6; `seed_replay_time_factor=130` as Solr's and HBase's; `results/hdfs/` (final .smt, claim, table).
- **The fork** (`graphchecker/hdfs-checks` 899c200cc8e, every step a workaround named in STATUS "Per-system surface"):
  a quorum call's replies in its loggers' order for every QJM check (05-10; 07 no longer reads
  `graphchecker/hdfs-checks-adhoc07`); a block recovery's primary the live replica with the least DataNode UUID, not the
  most recently heartbeated one (28-30: the replay recovered on the other DataNode); a LightWeightGSet sized as for a
  64 MB heap (52: a 22 GB replay heap made a 33M-bucket INodeMap that every fsimage save walked); TestEncryptedTransfer's
  client without block-acquire retries (11: a race named dn0's second SASL connection a retry or the checksum).
  `graphchecker/hdfs-checks-adhoc21` (25b4f1e531f) is that plus 21's workload with its post-target skip loop trimmed.
- **Case declarations** (`experiments/hadoop/*/case.sh`, `hdfs-cases.tsv`): the ad hoc family's closures up to 128 tasks
  (14 at 256), 11 up to 24 waves, `replay_timeout_s=7200` for 24/26/37 (their whole workloads replay in ~1 h here).

## 2. Results

The final rounds F1-F8 (2026-10-24, `/bulk/gc-out/hdfs-final`; F1 the whole series in 8 lanes, then 5 more, on snapshot
`/bulk/gc-run/hcF1` = 9c1bbe157 and tree set `/bulk/trees/f1`; F2-F8 the reruns each declaration or workaround needed, on
their own snapshots and tree sets) are `results/hdfs/README.md`: the rounds, every case's claim, mechanism, native k/N,
time breakdown and closure, and one reading per case. STATUS "HDFS checks on CloudLab" has the summary and what each case
needed; STATUS "Per-system surface" each workaround with its evidence run.

## 3. Read, in this order

1. This file, then [STATE.md](STATE.md) §C (where everything is on the cluster) and `results/hdfs/README.md`.
2. [LESSONS.md](LESSONS.md) §10 (this port's traps), §9 (HBase's, which apply), the rest.
3. [OPERATIONS.md](OPERATIONS.md) §11 (CloudLab), [PARALLEL.md](PARALLEL.md), [RULES.md](RULES.md), [CHECKING.md](CHECKING.md),
   [AGENTS.md](AGENTS.md).
4. [TODO.md](TODO.md) "HDFS on CloudLab" (what is left), STATUS "HDFS checks" (the readings of system/hdfs and
   system/hdfs1, each case's chain against the HDFS code) and "HDFS checks on CloudLab".
5. `docs/design/PIPELINE.md` for the stage you touch (§7.7 the ledger, §8/§9 DECIDE, §10b REPRODUCE).

## 4. Running a case and the series

- **Snapshot:** `bash tools/lib/worktree-add.sh /bulk/gc-run/<name> <commit> --detach` (an explicit commit or the caller's
  HEAD), then `ssh node2 'cd /bulk/gc-run/<name> && mvn -q -o package -DskipTests'`.
- **One case:** `cd <snapshot> && env GC_OUT=<out> GC_TREES=/bulk/trees/f1 CAUSYNTH_CUSTOM_JDK_HOME=/bulk/vm/hbase/j2sdk-image
  CASES="<case ids>" CASE_TIMEOUT_SECONDS=14400 PRUNE=0 tools/rounds/launch-round.sh <snapshot> <ROUND>`.
- **The series:** `tools/rounds/run-pool.sh <ROUND> experiments/hadoop/hdfs-cases.tsv system/hdfs-cloudlab=<snapshot>`,
  run from the snapshot: one pool of every case over the five nodes, longest first, a start whenever a tenth of the
  cluster's cores is free (PARALLEL §8; F1 ran before it as lanes of `run-series.sh`,
  `/bulk/gc-out/hdfs-final/lanes/lane<k>.tsv`). Development rounds: `tools/adhoc/sweep.sh` (shared pool).
- **Reading:** `tools/rounds/round-verify.sh <ROUND>`, `tools/analysis/vacuity.py --latest --detail <run>` on every UNSAT,
  `tools/analysis/smt-legend.py --repo <tree> <run>/out/<case>` on every SAT, `results/hdfs/final-stats.py`,
  `results/hdfs/collect-results.sh`. A live watcher: `/bulk/analysis/hdfs-2026-10-24/watch.sh '<round glob>'`.

## 5. Rules you must keep (RULES.md, LESSONS.md)

- General fixes only; a workaround is small, never switches the fatal outcome, and is named in STATUS "Per-system
  surface"; the time model is handled by workarounds only. HDFS changes are judged by HDFS's cases.
- Completeness over precision: over-approximate in COMPOSE, CONFIRM stays strict. A review agent reads every
  COMPOSE/CONFIRM/schedule/identity batch before its merge.
- A SAT counts when confirmed in the VM, natively reproduced (or NATIVE_PLANT_UNSUPPORTED named) and its chain read; an
  UNSAT when at its fixed point, z3 unsat on the file, and not vacuous (or vacuous by construction with the reason).
- At most 5 coding agents, each on its own branch, worktree, snapshot and GC_OUT; briefs on disk
  (`/bulk/analysis/hdfs-2026-10-24/`); design gate for identity/schedule/symbolic/soundness changes.
- Shell and git: kill only by pid (`tools/rounds/stop-run.sh` alone on its line), never `git add -A`, never rebuild a
  snapshot or tree a run reads; commits as Zhenyu Li <zhl136@ucsd.edu> with the Claude trailer; push only what the owner asked.
