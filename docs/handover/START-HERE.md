# START HERE: THE HDFS branch (system/hdfs-liftlab, 2026-10-27)

You take over GraphChecker's HDFS group: every HDFS case on HBase's final engine, run on liftlab with the memory-ledger
scheduling of `system/hbase` and `system/solr`. This one branch replaces `system/hdfs` and `system/hdfs1` (the owner,
2026-10-26: "最终system/hdfs-liftlab一个分支就能彻底取代原先的system/hdfs和system/hdfs1了哈"). This file is self-contained: the
goal, what the branch holds, the cluster, the trees, the results, how to run a case and the whole series, what is left,
and the rules. The other systems' takeover files are their own branches' START-HERE (README "The branches"); HDFS's
earlier bodies are STATE §0. The old HDFS bugs put back by hand run on `system/hdfs-buggy-detect` (this branch plus those
cases; its START-HERE).

- **Repo:** `git@github.com:JHSUYU/GraphChecker.git`, branch **`system/hdfs-liftlab`** (local repository
  `/u/vnr3ne/GraphChecker`, `GC_REPO`; integration worktree `/bigtemp/vnr3ne/wt/gc-hdfs-liftlab`).
- **The trees:** the Hadoop fork `https://github.com/JHSUYU/hadoop.git`: `graphchecker/hdfs-checks` (899c200cc8e: every case
  but hdfs-adhoc-21 and hdfs-11741), `graphchecker/hdfs-checks-adhoc21` (25b4f1e531f: 21), `graphchecker/hdfs-11741`
  (6c86fca9a2b: 11741); `experiments/hadoop/trees.tsv`. The current tree set is `/bigtemp/vnr3ne/wt/hl-trees-1`
  (`hadoop-hdfs-study-r7`, `hadoop-hdfs-21`; Maven repositories under `/bigtemp/vnr3ne/m2/hl-1`); a tree a run reads is
  never rebuilt, so a tree change during a series is a new set.
- **The cluster:** liftlab, lift02-15 (48 cores and 30 GB each; `/bigtemp/vnr3ne` and the home over NFS). lift11 is the
  control host (`GC_CONTROL_HOST`: the lead's sessions, neither a worker nor a head); lift07 has been unreachable since the
  servers went down on 2026-10-23; lift02 and lift03 cannot reach lift15, so they are workers, never heads. The 12
  workers: lift02-06, lift08-10, lift12-15. Maven and Ant are only on lift02-06 and lift08-10 (builds go there).
- **The image:** `/bigtemp/vnr3ne/vm-force12/j2sdk-image` (this branch's VM sources are `system/hbase`'s).
- **From GitHub:** [../REPRODUCE.md](../REPRODUCE.md) §0-§5 clones the branch and the fork, builds the image and the
  trees, and runs one case or the series.

## 1. The goal and what the branch is

The owner's goal (2026-10-26, verbatim in STATE §L): run every HDFS ad hoc check but hdfs-11741 again, on the HDFS
port's code with liftlab's parallel scheduling ("你要把system./solr等的并行，弄到system/hdfs-liftlab"), and measure the 45
cases' time breakdown -- seeding, exploration, compose + solver -- each case alone on the cluster ("每个独占集群").

`system/hdfs-liftlab` is the HDFS port onto `system/hbase` (below; first run on CloudLab, whose head is the tag
`archive/system/hdfs-cloudlab`, 3411a49f8) with liftlab's scheduling (2acb6e9f7, 3a9b0a688, 76828e529, 3ed666321,
c3f820ed1 revert the CloudLab one) and e2a6aebf9, gc-env's liftlab defaults (`GC_BULK=/bigtemp/vnr3ne`,
`GC_REPO=~/GraphChecker`, z3 in `~/.local/bin`, `LIFTS` lift02-15 but lift11, `GC_CONTROL_HOST=lift11`), then four
general fixes of `system/solr` (43ac04c1e, b4c24f9e3, 6a1d5fd6a, f7c095f00). **Scheduling is `system/hbase`'s**:
`run_engine.sh` and its shell test equal `system/hbase`'s; every start is charged on the host ledger by its memory and
no host passes 70 %; every choice among hosts takes the most memory room (PIPELINE §7.7, PARALLEL).

What the HDFS port changed against `system/hbase` (git log has each commit; STATUS "Per-system surface" and LESSONS §10
the why), all kept here:
- **The Hadoop shim and its door entry points are back** (eb4b370c5): `src/shim` (the `hadoop-shim` classifier jar) and
  `MessageDoors#captureScope`, `#handingOff`/`#handedOff` (with Identity's received-message hand-off), `#received`,
  `#startupStep`/`#startupDone`, `#replaying`, `#outboundNone`, public `#setAside`/`#putBack`: what `system/solr`'s LOC 2a/2b
  deleted "system/hdfs keeps them". The trees call them unchanged.
- **DECIDE** (agent D, reviewed twice): a handed-on delivery of the path's own run is the path's own (a two-hop handoff's
  inner arm no longer reads as a re-pairing), and the own-witness pass asks each fatal-observing explored path once in its
  own run, its world's clocks held, within a sixth of the decide budget. hdfs-17897's replayed heartbeat fault is claimed
  MARKER_FLIPPED, no longer a refuted STATE_PAIRING model first.
- **REPRODUCE** keeps a turn-counted ORDER row in a world that plants no root (c8d40a5d8): hdfs-bugs-slowdisk-zero 10/10.
- **The HBase process for HDFS's declarations:** world depth 0 for every case (RULES) but 11741 at 2 (two clocks;
  07's former 6 dropped by 94fce7127); `seed_replay_time_factor=130` as Solr's and HBase's; `results/hdfs/` (final .smt, claim, table).
- **The fork** (`graphchecker/hdfs-checks` 899c200cc8e, every step a workaround named in STATUS "Per-system surface"):
  a quorum call's replies in its loggers' order for every QJM check (05-10; 07 no longer reads
  `graphchecker/hdfs-checks-adhoc07`); a block recovery's primary the live replica with the least DataNode UUID, not the
  most recently heartbeated one (28-30: the replay recovered on the other DataNode); a LightWeightGSet sized as for a
  64 MB heap (52: a 22 GB replay heap made a 33M-bucket INodeMap that every fsimage save walked); TestEncryptedTransfer's
  client without block-acquire retries (11: a race named dn0's second SASL connection a retry or the checksum).
  `graphchecker/hdfs-checks-adhoc21` (25b4f1e531f) is that plus 21's workload with its post-target skip loop trimmed.
- **Case declarations** (`experiments/hadoop/*/case.sh`, `hdfs-cases.tsv`, whose `branch` column is `system/hdfs-liftlab`
  for every case): the ad hoc family's closures up to 128 tasks (14 at 256), 11 up to 24 waves, `replay_timeout_s=7200`
  for 24/26/37 (their focused replays run the whole upgrade or rollback test).

## 2. Results

**The series H1** (2026-10-26 23:55 to 2026-10-27 17:34; STATE §L): the 45 cases of `experiments/hadoop/hdfs-cases.tsv`
but hdfs-11741, one at a time, each alone with the 12 lifts as workers (head lift10), snapshots `/u/vnr3ne/gc-run/hl-1`
(e2a6aebf9, the first 25) and `hl-2` (f7c095f00, the other 20), tree set `hl-trees-1`, image `vm-force12`; runs
`/bigtemp/vnr3ne/gc-out/hdfs-final/accept-H1-<case without hdfs->`. Each case's verdict, native k/N, time breakdown
(seeding / exploration / compose + solver) and closure: `results/hdfs/README.md`. The 45 alone in 62555 s (17.4 h): the 9
named bugs but 11741 PASS (native 10/10), 10 and 12 SAT, 52 a named bound (z3 undecided in its budget), 33 UNSAT_CLOSED;
no new bug. hdfs-11741 was not run on liftlab (owner): its row is the port's CloudLab run F7 (CLOCK_SKEW confirmed in the
VM, native 0/10: TODO "HDFS on liftlab" 12).

**The records it stands beside.** The former branches' readings, each case's chain against the HDFS code: STATUS "HDFS
checks"; their time breakdown, every case alone on ten lifts: series EX1, PERFORMANCE §6 and the `ex1_*` columns of
`hdfs-cases.tsv`. The port onto HBase's engine, per case: STATUS "HDFS checks on HBase's engine".

## 3. Read, in this order

1. This file, then [STATE.md](STATE.md) §L (where everything is) and `results/hdfs/README.md`.
2. [LESSONS.md](LESSONS.md) §10 (the port's traps), §9 (HBase's, which apply), the rest.
3. [OPERATIONS.md](OPERATIONS.md) §1 and §4 (liftlab, the ledger, rounds), [PARALLEL.md](PARALLEL.md), [RULES.md](RULES.md),
   [CHECKING.md](CHECKING.md), [AGENTS.md](AGENTS.md).
4. [TODO.md](TODO.md) "HDFS on liftlab" (what is left), STATUS "HDFS checks" and "HDFS checks on HBase's engine".
5. `docs/design/PIPELINE.md` for the stage you touch (§7.7 the work pool and the ledger, §8/§9 COMPOSE and DECIDE, §10b
   REPRODUCE).

## 4. Running a case and the series

Every command runs with `env -u BASH_ENV` (or `unset BASH_ENV` first), from a lift that reaches every worker (never lift02,
lift03 or lift11 as a head). Snapshot and tree set are shared read-only once a run reads them.
- **Snapshot:** `bash tools/lib/worktree-add.sh /u/vnr3ne/gc-run/<name> <commit> --detach` (sparse, no `third_party/`;
  `GC_REPO` names the repository), then `cd /u/vnr3ne/gc-run/<name> && tools/onlift.sh -h <host> -g 6 mvn -q -o package
  -DskipTests`, `<host>` one with Maven (lift02-06, lift08-10; the same for every build below).
- **A tree set:** `tools/onlift.sh -g 8 env GC_TREES=/bigtemp/vnr3ne/wt/<set> GC_M2=/bigtemp/vnr3ne/m2/<set>
  experiments/hadoop/prepare-trees.sh hadoop-hdfs-study-r7 hadoop-hdfs-21` from a built checkout (`onlift.sh` forwards no
  environment, so the variables go inside its command; add `hadoop-hdfs-11741-r6` for 11741): ~20 minutes, its log ends
  with a `PASSED`/`FAILED`/`MISSING` line per workload. Then every case's `validate`:
  `bash /bigtemp/vnr3ne/analysis/hdfs-2026-10-26/lead/validate.sh <snapshot> <tree set>`.
- **One case:** `GC_TREES=<tree set> bash /bigtemp/vnr3ne/analysis/hdfs-2026-10-26/lead/launch.sh <topic> <snapshot> <case>
  <TAG> [budget s]` (the 12 lifts as workers, `vm-force12`, into `/bigtemp/vnr3ne/gc-out/hdfs-<topic>/accept-<TAG>`; start it
  detached: `setsid nohup ... > <log> 2>&1 < /dev/null &`). With the branch's own tool: `cd <snapshot> && env
  GC_OUT=<out> GC_TREES=<tree set> CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force12/j2sdk-image
  CAUSYNTH_CAMPAIGN_WORKER_HOSTS="<the 12 lifts>" CASE_TIMEOUT_SECONDS=<budget_s> tools/rounds/launch-run.sh <snapshot>
  <case> <tag>` (it holds the shell until the case ends; the default workers are gc-env's `LIFTS`, which still names
  lift07: export `LIFTS` without it).
- **The series, each case alone:** H1's driver, `cd /bigtemp/vnr3ne/analysis/hdfs-2026-10-26/lead/final && SNAP=<snapshot>
  TREES=<tree set> WORKERS='<the 12 lifts>' HEADS='lift10' setsid nohup bash series.sh <round> 1 <case>... &` (started
  on the head with `ssh -f`; log `series-<round>.log`, START/END per case; `touch series-<round>.STOP` stops further
  starts; never edit a driver a running series reads: copy it). With the branch's own tool: `cd <snapshot> && env
  GC_OUT=<out> GC_TREES=<tree set> LIFTS='<the 12 lifts>' CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force12/j2sdk-image
  tools/rounds/run-series.sh <round> experiments/hadoop/hdfs-cases.tsv system/hdfs-liftlab=<snapshot> [case...]`
  ([../REPRODUCE.md](../REPRODUCE.md) §4). Development rounds of many cases at once: `tools/adhoc/sweep.sh` (shared pool).
- **Watching:** `lead-watch.sh` (one line per run end, stall, full host) and `watchdog.sh` (D-state processes, orphaned
  z3s, a host refusing ssh) in the same directory, each under a Monitor; the decision log `RUNS.txt`.
- **Reading:** `tools/rounds/round-verify.sh <ROUND>`, `tools/analysis/vacuity.py --latest --detail <run>` on every UNSAT,
  `tools/analysis/smt-legend.py --repo <tree> <run>/out/<case>` on every SAT, `tools/rounds/series-stats.py <ROUND>`,
  `results/hdfs/final-stats.py`, `results/hdfs/collect-results.sh`.

## 5. Rules you must keep (RULES.md, LESSONS.md)

- General fixes only; a workaround is small, never switches the fatal outcome, and is named in STATUS "Per-system
  surface"; the time model is handled by workarounds only. HDFS changes are judged by HDFS's cases.
- Completeness over precision: over-approximate in COMPOSE, CONFIRM stays strict. A review agent reads every
  COMPOSE/CONFIRM/schedule/identity batch before its merge.
- A SAT counts when confirmed in the VM, natively reproduced (or NATIVE_PLANT_UNSUPPORTED named) and its chain read; an
  UNSAT when at its fixed point, z3 unsat on the file, and not vacuous (or vacuous by construction with the reason).
- Memory is the limit on liftlab: every start goes through the host ledger, no host above 70 %; the control host lift11
  stays light (no builds, no polling there).
- At most 5 coding agents, each on its own branch, worktree, snapshot and GC_OUT; briefs on disk
  (`/bigtemp/vnr3ne/analysis/hdfs-2026-10-26/`); design gate for identity/schedule/symbolic/soundness changes.
- Shell and git: kill only by pid (`tools/rounds/stop-run.sh` alone on its line), never `git add -A`, never rebuild a
  snapshot or tree a run reads; commits as Zhenyu Li <zhl136@ucsd.edu> with the Claude trailer; push only what the owner asked.
