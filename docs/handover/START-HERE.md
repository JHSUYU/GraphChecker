# START HERE: system/hdfs-buggy-detect -- the old HDFS bugs, on THE HDFS branch (liftlab)

You take over `system/hdfs-buggy-detect`: `system/hdfs-liftlab` (THE HDFS branch: every HDFS ad hoc case on HBase's final
engine, run on liftlab with the memory-ledger scheduling of `system/hbase` and `system/solr`) plus seven old HDFS bugs
put back by hand, each making one of its ad hoc checks fail (§0). This file is self-contained: §0 is this branch's own
work; §1-§5 are `system/hdfs-liftlab`'s (the goal, what it holds, the cluster, the trees, the results, how to run a case
and the whole series, the rules), all of which hold here. The other systems' takeover files are their own branches'
START-HERE (README "The branches"); HDFS's earlier bodies are STATE §0.

## 0. The old HDFS bugs (this branch)

The owner's goal (2026-10-26): put back by hand, on today's trees, the old bugs that make an ad hoc check's OWN
declared throw fail, and detect each on the system's branch; a check truly beyond GraphChecker's capability is not
forced. The table of all four systems, the owner's decisions and the engine support: [BUGGY-DETECT.md](BUGGY-DETECT.md).
`system/hdfs-buggy-detect` is the CloudLab experiment's branch (2026-10-25..27, 01a320d58) with `system/hdfs-liftlab`
merged in (c9aece5af): liftlab's scheduling, the engine support for HDFS-14311 kept (STATE §B).

| case (`experiments/hadoop/`) | bug | point | tree = the fork `JHSUYU/hadoop` branch | CloudLab, 2026-10-26 | B1 (liftlab) |
| --- | --- | --- | --- | --- | --- |
| `hdfs-buggy-11741` | HDFS-11741 | hdfs-adhoc-11 | `graphchecker/hdfs-bug-11741` c0af4cbcfe5 | SAT, CLOCK_SKEW, native 10/10 | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 884 s (B1-buggy-11741) |
| `hdfs-buggy-17383` | HDFS-17383 | hdfs-adhoc-12 | `graphchecker/hdfs-bug-17383` 1e519fa598a | SAT, lost heartbeat reply, 10/10 | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 572 s (B1-buggy-17383) |
| `hdfs-buggy-12931` | HDFS-12931 | hdfs-adhoc-11 | `graphchecker/hdfs-bug-12931` d9fde9f9480 | SAT, lost key-update reply, 10/10 (caveat) | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 368 s (B1-buggy-12931) |
| `hdfs-buggy-5766` | HDFS-5766 | hdfs-adhoc-11 | `graphchecker/hdfs-bug-5766` a8f16edc154 | SAT, lost key-update request, 10/10 (caveat) | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 516 s (B1-buggy-5766) |
| `hdfs-buggy-10609` | HDFS-10609 | hdfs-adhoc-11 | `graphchecker/hdfs-bug-10609` bec4a7e0e52 | SAT, lost key-update request, 10/10 (caveat) | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 506 s (B1-buggy-10609) |
| `hdfs-buggy-14075` | HDFS-14075 | hdfs-adhoc-45 | `graphchecker/hdfs-bug-14075` 7e8681a724d | SAT, LOCAL_IO fault, 10/10 | B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 463 s (B1-buggy-14075) |
| `hdfs-buggy-14311` | HDFS-14311 | hdfs-adhoc-24 | `graphchecker/hdfs-bug-14311` be29cd3c074 | not detected: a capability limit | B1: not detected again (UNSAT_CLOSED, substantive: 9 paths, 8 free; 2333 s) |

Each tree is `graphchecker/hdfs-checks` 899c200cc8e with one bug put back (its own commit) and a workload for it; the
tree name is `hadoop-hdfs-bug-<jira>` (`experiments/hadoop/trees.tsv`), the list of cases
`experiments/hadoop/hdfs-buggy-cases.tsv` (budget 21600 s each), each case's README the bug, what was put back, the
workload, the declarations, the runs and the reading. `report.py` holds each case's expected mechanism
(`EXPECTED_MECHANISM`). `hdfs-buggy-15590` is a case the owner dropped (its witness fires another throw): it is in no
list and its tree branch was never pushed.

- **The tree set** (liftlab: `/bigtemp/vnr3ne/wt/bd-trees-1`, Maven repositories `/bigtemp/vnr3ne/m2/bd-1`; built
  2026-10-27/28, every workload PASSED: `/bigtemp/vnr3ne/analysis/buggy-detect-liftlab-2026-10-28/trees/`), from a built
  checkout of this branch, on a Maven host:
  `tools/onlift.sh -h <lift02-06 or lift08-10> -g 8 env GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1 GC_M2=/bigtemp/vnr3ne/m2/bd-1
  experiments/hadoop/prepare-trees.sh hadoop-hdfs-bug-11741 hadoop-hdfs-bug-17383 hadoop-hdfs-bug-12931
  hadoop-hdfs-bug-5766 hadoop-hdfs-bug-10609 hadoop-hdfs-bug-14075 hadoop-hdfs-bug-14311` (each tree cloned from the fork,
  built against the checkout's jar, its workload run once natively: its log line `PASSED`/`FAILED`/`MISSING`). The lead's
  wrapper: `/bigtemp/vnr3ne/analysis/buggy-detect-liftlab-2026-10-28/build-tree.sh <checkout> hadoop <tree...>`.
- **The snapshot:** `/u/vnr3ne/gc-run/bd-hdfs-1` (c9aece5af, built): `bash tools/lib/worktree-add.sh
  /u/vnr3ne/gc-run/<name> <commit> --detach`, then `tools/onlift.sh -h <a Maven host> -g 6 mvn -q -o package
  -DskipTests` in it.
- **One case, or all of them at once** (round B1 ran them together, the shared ledger spreading every replay over the
  workers): from the snapshot, `env GC_OUT=/bigtemp/vnr3ne/gc-out/buggy-detect GC_TREES=/bigtemp/vnr3ne/wt/bd-trees-1
  GC_M2=/bigtemp/vnr3ne/m2/bd-1 LIFTS="lift02 lift03 lift04 lift05 lift06 lift08 lift09 lift10 lift12 lift13 lift14"
  CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force12/j2sdk-image CASE_TIMEOUT_SECONDS=21600 PRUNE=0
  CASES="hdfs-buggy-11741 ..." tools/rounds/launch-round.sh /u/vnr3ne/gc-run/bd-hdfs-1 <ROUND>` (`DRY=1` prints the heads
  it would choose). Each case writes `$GC_OUT/accept-<ROUND>-buggy-<jira>`. The heads come from `LIFTS` by room and every
  head must reach every worker: lift02 and lift03 cannot reach lift15, so lift15 stays out of `LIFTS` (B1's first
  launches with it in failed PREFLIGHT on heads lift02/lift03: kept as `accept-B1STOP-*`, relaunched). The lead's wrapper:
  `/bigtemp/vnr3ne/analysis/buggy-detect-liftlab-2026-10-28/launch-b1.sh hdfs <case...>`; its log `RUNS.txt` beside it.
- **Reading a case:** `GC_OUT=... tools/rounds/round-verify.sh <ROUND>` (how EXPLORE ended, z3 on the file, gaps, moved
  roots, CONFIRM); the report `$run/report/<case>/report.md` (PASS = the expected mechanism, confirmed, reproduced
  natively; again by hand: `python3 experiments/accept/report.py <case> $run/out/<case> <work dir>`);
  `python3 tools/analysis/vacuity.py --latest --detail $run` on every UNSAT; `tools/analysis/smt-legend.py --repo
  <tree> $run/out/<case>` on every SAT, against the case README's chain; native k/N and control in
  `out/<case>/schedule/final/reproduce.json`.

What is left for the old bugs: [TODO.md](TODO.md) "Buggy-detect".

## The HDFS branch underneath (system/hdfs-liftlab)

- **Repo:** `git@github.com:JHSUYU/GraphChecker.git`, branches **`system/hdfs-buggy-detect`** (this one; worktree
  `/bigtemp/vnr3ne/wt/gc-hdfs-bd`) and **`system/hdfs-liftlab`** (integration worktree `/bigtemp/vnr3ne/wt/gc-hdfs-liftlab`);
  local repository `/u/vnr3ne/GraphChecker`, `GC_REPO`.
- **The trees:** the Hadoop fork `https://github.com/JHSUYU/hadoop.git`: `graphchecker/hdfs-checks` (899c200cc8e: every case
  but hdfs-adhoc-21 and hdfs-11741), `graphchecker/hdfs-checks-adhoc21` (25b4f1e531f: 21), `graphchecker/hdfs-11741`
  (6c86fca9a2b: 11741); `experiments/hadoop/trees.tsv`. The current tree set is `/bigtemp/vnr3ne/wt/hl-trees-1`
  (`hadoop-hdfs-study-r7`, `hadoop-hdfs-21`; Maven repositories under `/bigtemp/vnr3ne/m2/hl-1`); a tree a run reads is
  never rebuilt, so a tree change during a series is a new set.
- **The cluster:** liftlab, lift02-15 (48 cores and 30 GB each; `/bigtemp/vnr3ne` and the home over NFS). lift11 is the
  control host (`GC_CONTROL_HOST`: the lead's sessions, neither a worker nor a head); lift07 has been unreachable since the
  servers went down on 2026-10-23; lift02 and lift03 cannot reach lift15 (since 2026-10-28), so the workers are the 11
  of gc-env's default `LIFTS`: lift02-06, lift08-10, lift12-14. Maven and Ant are on PATH only on lift02-06 and
  lift08-10 (builds go there).
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
