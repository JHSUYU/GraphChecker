# Operations: servers, storage, tools, rounds, debugging (long-term)

Part of every agent's long-term memory ([RULES.md](RULES.md)). How the servers are shared, where
everything lives, how to build, test, run and read a campaign, and the traps the leads fell into.

## 1. Hosts and storage

| what | where / how |
| --- | --- |
| hosts | `lift06`…`lift15` (ten), 48 cores and 30 GB each. All ten are used for every fan-out (obligations, rounds, sweeps, builds). `lift11` is the owner's interactive machine: it is a **worker but never a campaign head** (`launch-round.sh` enforces it). Never blow up a host's memory: every start goes through the host ledger (below). |
| home | `/u/vnr3ne` is NFS-shared by all lifts, **100 GB quota** (it has been full twice). Keep bulk data off it. |
| bulk storage | `/bigtemp/vnr3ne` (NFS pool, automounted on every lift, owner-approved): round outputs `gc-out/`, VM images `vm-*/`, specs, analyses, gate outputs `ab/`, helper scripts `bin/`, agent worktrees `wt/`. `test -w` does not trigger the automount; `ls` it first. |
| local scratch | `/localtmp/$USER` on each lift (replay working directories go to `/localtmp/$USER/graphchecker/`). |
| stock JDK 8 | `/usr/lib/jvm/java-8-openjdk-amd64`. **Trap:** the owner's dotfiles export `JAVA_HOME=java-11`, which lift11–15 lack, and `bash -c` under ssh re-reads `~/.bashrc`. Do not edit the dotfiles; use `onlift.sh`, which unsets `SSH_CLIENT` and sets Java 8. |
| where things live | stated once in `tools/lib/gc-env.sh`: `GC_BULK` (`/bigtemp/vnr3ne`), `GC_OUT`, `GC_TREES` (the system trees, `$GC_BULK/wt`), `GC_M2` (their Maven repositories, `$GC_BULK/m2`), `Z3_BIN`, `LIFTS`, the ledger. Every case's `case.sh` names its tree under `GC_TREES`. From a fresh clone of the GitHub branches: [../REPRODUCE.md](../REPRODUCE.md) |
| z3 | `Z3_BIN` (`~/.local/bin/z3`, 4.14.1), what the engine, `accept.sh`'s probe and `round-verify.sh` run |
| concolic VM images | Both HDFS branches: **`/bigtemp/vnr3ne/vm-hg5/j2sdk-image`** (sources: branch `hdfs-vm-hg5` `742f13363`; its `SOURCE.txt` and `smoke.log` sit beside it): list/deque/HashSet iterators reach their tracked container, a read record states its observed version `{fieldVersionId, versionKind}` in envelope schema 2, outside mutations marked after they run. `main`'s: `vm-model-guards2`. Every other `vm-*` directory is superseded. Pass an image as `CAUSYNTH_CUSTOM_JDK_HOME` (a sweep: `VM_IMAGE`), never as `JAVA_HOME`. A new image from either HDFS branch's sources: `tools/vm/build-image.sh <new dir>` on a host with gcc-6 (lift15), a few minutes; a fresh clone's image (2026-10-08, `/bigtemp/vnr3ne/repro/vm`) passed the same smoke suite. A Java side that needs natives an image lacks refuses the replay by name (`ConcolicVmBroker#requireCurrentCapabilities`). |
| HDFS trees | `$GC_TREES/<name>`, one per row of `experiments/hadoop/trees.tsv`, each a branch of the Hadoop fork (`git@github.com:JHSUYU/hadoop.git`; on this cluster each is a worktree of `~/hadoop` on the local branch STATE §3 names): **`hadoop-hdfs-study-r7`** = **`graphchecker/hdfs-checks`** `bd72fcc1a13` (every HDFS case but 07, 21 and 11741: the 36 study checks' markers and workloads, the eight named block-key/snapshot cases, `hdfs-bugs-slowdisk-zero`, the time family's workarounds, HDFS-17897's fix reverted); **`hadoop-hdfs-study-r8`** = **`graphchecker/hdfs-checks-adhoc07`** `e3dab6266a7` (hdfs-adhoc-07 only: r7 + QJM's `AsyncLoggerSet`/`QuorumCall` reply maps in the loggers' order); **`hadoop-hdfs-21`** = **`graphchecker/hdfs-checks-adhoc21`** `c360d869629` (hdfs-adhoc-21 only: r7 + the DataNode handshake on its own joined thread); **`hadoop-hdfs-11741-r6`** = **`graphchecker/hdfs-11741`** `6c86fca9a2b` (hdfs-11741: trunk 734dd8a67cd with HDFS-11741's fix reverted, its own hook generation). `main`'s cases read `$GC_TREES/hadoop-hdfs-dtx` (local `gc/hdfs-unified-dtx`, Maven repo `/bigtemp/vnr3ne/wt/dtx/m2`). **Making a tree**: `experiments/hadoop/prepare-trees.sh <name>` from a built `system/hdfs1` checkout via `tools/onlift.sh -g 8`: clones the branch, installs the checkout's plain jar into the tree's own Maven repository `$GC_M2/<name>`, builds hadoop-hdfs and every module it needs (`experiments/hadoop/build.sh`, Java 8, `javac8-filter-crc32c.sh`), then runs every case's workload once natively, since a case's classpath is read off its workload's surefire report (a case whose workload never ran there fails validate, "missing test report"). After a rebuild, or for a check added to `checks.tsv`: `SKIP_TREE_BUILD=1 experiments/hadoop/build.sh <tree> '<Class>#<method>'` runs just the workload. The trees on this cluster today were made before that script (sparse worktrees of `~/hadoop` built module by module, Maven repositories `$GC_M2/hdfs-study-r7`, `hdfs-study-r8`, `hdfs-11741-r6`). **A per-case tree** (a workaround one case reads, owner 2026-10-06): a fork branch from r7's with the patch, a row in `trees.tsv`, `case.sh` overriding `repo=` for that case id only. A tree change that adds or removes a statement in a method shifts its Jimple unit ids: a case's `loop-bounds*.jsonl` rows naming them must follow. |
| Solr trees | `system/solr`'s 20 cases: **`lucene-solr-checks`** (`$GC_TREES/lucene-solr-checks`, branch `gc/solr-checks`, a worktree of `~/lucene-solr-8_11`; to be the fork's `graphchecker/solr-checks`, `experiments/solr/trees.tsv`): `gc/solr-bugs` plus every case's marker, the bug checks' workloads and the full-distributed tests' hook. **Making it** from the fork: `experiments/solr/prepare-trees.sh` via `tools/onlift.sh -g 8` (clone, Ant build against the checkout's jar, every case's workload once natively; after a tree change `SKIP_TREE_BUILD=1 experiments/solr/build.sh <tree> <seed> '<Class>#<method>'` runs one workload). `main`'s cases: one Solr 8.11 tree line, `~/lucene-solr-unified` (branch `gc/solr-unified`, a worktree of `~/lucene-solr-8_11`): the shared adapter, both cases' workloads and target markers, the two kept scaffold patches (inventory: `/bigtemp/vnr3ne/analysis/unify/solr-inventory.md`); solr-18406 and solr-18413 name its successor `gc/solr-unified-storing` (`/bigtemp/vnr3ne/wt/lucene-solr-storing`: the same plus SolrZkClient's `MessageDoors#storing` write brackets). The older per-case worktrees (`gc/solr`, `~/lucene-solr-18406`, `~/lucene-solr-18413`, `~/lucene-solr-8_11-adhoc`) serve only rounds started on them. Ant build; native Ant tests need `-Dtests.useSecurityManager=false`. `~/solr` is apache/solr main (blobless: never `git grep` a commit there). |
| ZooKeeper trees | `/bigtemp/vnr3ne/wt/zookeeper-hb` (`gc/zk-unified-hb`, + the RESPONSE door, for `hb-schedule`; Maven repo `/bigtemp/vnr3ne/m2/zookeeper-hb`). `/bigtemp/vnr3ne/wt/zookeeper-unified` (branch `gc/zk-unified` on `branch-3.9`, a worktree of `~/zookeeper`): the adapter (`CausynthZk`, `CausynthZkCluster`), the `zk-bugs` cases' target markers and the quota workload. Maven build into its own repository `/bigtemp/vnr3ne/m2/zookeeper` (`experiments/zookeeper/build.sh`, which installs the GraphChecker jar there; never `~/.m2`). Build a case's workload before its first run: `SKIP_GRAPHCHECKER_INSTALL=1 bash experiments/lib/run.sh experiments/zookeeper/zk-bugs <case> build`. Its only remote is apache/zookeeper: never push it. |
| HBase tree | `/bigtemp/vnr3ne/wt/hbase-unified` (`gc/hbase-unified`); clones `~/hbase`, `~/zookeeper`, `~/hadoop`, `~/lucene-solr-8_11`; private Maven repos `/bigtemp/vnr3ne/m2/<name>` |
| host ledger | `$CAUSYNTH_HOST_LEDGER` = `/bigtemp/vnr3ne/gc-out/hosts/<lift>/charges/<mb>.<host>.<pid>.<time>.<rand>`: a charge's mtime is its 120 s lease, renewed every 10 s by its holder; a lapsed lease no longer counts (it is deleted at ten leases); `explorations/` = the capped explorations running. `ls` the charges of a host to see what holds it |
| evidence and agent tools | `/bigtemp/vnr3ne/gc-out/solr-bugs/{evidence,agent-tools,scripts}` (jstacks of the ZkStateReader-race hangs, A2's `watch-sb.sh`/`watch-stall.sh` run watchers, the storing tree's `spelledAs-adapter.patch`); `/bigtemp/vnr3ne/readout-stream/` (A6's `measure-seed.sh`, `measure-obl.sh`, `compare.py` and the retained-heap tool `heap/tool/HeapRetained.java`: how replay memory was measured; 4.2 GB of data); `/bigtemp/vnr3ne/gc-out/hb-schedule/` (Z1–Z5 with their `run.sh` recipes); `/bigtemp/vnr3ne/ab/` (offline gates; jars in `ab/jars/`) |
| round outputs | `/bigtemp/vnr3ne/gc-out/hdfs-study/` (the HDFS group's rounds: `accept-<round>-<n>/`, `sweep-<round>-cases.tsv` maps n to the case, `rounds/<round>.cases`); `/bigtemp/vnr3ne/gc-out/hdfs-excl/` (series EX1, every case alone, PRUNE=0: the offline gate's corpora); `/bigtemp/vnr3ne/gc-out/<branch or agent>/` for agents' runs; `gc-out/accept-V25-*` `main`'s last round |
| owner's memory notes | `~/.claude/projects/-u-vnr3ne-GraphChecker/memory/` (one fact per file, index `MEMORY.md`) |

## 2. Helper commands

```bash
tools/onlift.sh [-g <min-free-GB>] [-h <host>] <command...>
    # run a command in the current directory on the least-loaded host of LIFTS (or <host>) with the
    # Java 8 + Maven toolchain; use it for mvn, the shell test, tree and VM builds, offline stages,
    # anything heavy. `onlift.sh -h` with no host hangs; always give a host or omit -h.
tools/pick-lift.sh [min-free-GB]   # prints the best host
```

Round tools (in the repo, `tools/rounds/`; `GC_OUT` names the output root): `round-status.sh <round>` (every started
case: age, stage, seed give-ups, or its verdict), `round-watch.sh <round> [<baseline>]` (one line per finished case, per seed
replay past 30/80 give-ups, and STALLS-REGRESSION when a seed replay passes twice the baseline round's give-ups of the
same case), `round-slow.sh <round> <baseline>` (a running case past 2x/4x its baseline time),
`round-verify.sh <round> [case...]` (how EXPLORE ended, z3 on the exported formula, BLOCKING gaps, moved roots,
CONFIRM, the formula's leaf symbols: NO-SYMBOL marks an UNSAT over nothing that moves, a scope hole to read before
it counts; `BOUNDED:<keys>`, a declared bound cut the search; `UNBOUND:<n>`, a broken causal chain per `cone.py`; the last
line counts both. What each column means for "done" and the traps behind them: [CHECKING.md](CHECKING.md)), `obl-times.py <case>/schedule` (EXPLORE: run time vs queue wait per verdict, concurrency, refusal
reasons). How to debug a slow case: [../design/PERFORMANCE.md](../design/PERFORMANCE.md) §4. Reading a `.smt` by hand:
`tools/analysis/smt-legend.py <out/case> --repo <tree>` names every leaf symbol of `final/candidate.smt2` (each root's
door or configuration and where it was minted, each read's node, region, method and field, each handoff's port and
producer), the starting point of every causal-chain check.

## 3. Build, test, commit

```bash
cd ~/GraphChecker
tools/onlift.sh -g 10 bash -c 'mvn -q -o package && bash src/test/shell/run_engine_campaign_helpers_test.sh'
```

Keep `-o` (offline): `~/.m2` is shared over NFS. `mvn package` also builds the `hadoop-shim`
classifier jar from `src/shim/java`, which the HDFS trees call. A snapshot needs all three jars in
`target/` (`-jar-with-dependencies`, `-hadoop-shim`, plain).

VM: `tools/vm/build-image.sh <new dir>` via `tools/onlift.sh -h lift15 -g 12` (the one lift with gcc-6): the
checkout's `third_party/` sources built on local disk as a full JDK, then the smoke suite (`<dir>/smoke.log`); a few
minutes. Never overwrite an image a round uses; build a new directory.

## 4. Rounds (live campaigns)

```bash
tools/lib/worktree-add.sh ~/gc-run/p<N> <commit> --detach   # no third_party/: seconds, not most of an hour
(cd ~/gc-run/p<N> && tools/onlift.sh -g 10 mvn -q -o package -DskipTests)
GC_OUT=/bigtemp/vnr3ne/gc-out/<dir> CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-hg5/j2sdk-image \
  CASES="hdfs-17960 hdfs-adhoc-20" tools/rounds/launch-round.sh ~/gc-run/p<N> <round>   # heads chosen by room
#   (CASES unset: launch-round.sh's own list of the named cases)
# tools/rounds/launch-run.sh <snapshot> <case> <suffix>: one run, its obligations also over all of LIFTS
DRY=1 ... tools/rounds/launch-round.sh ...                         # the heads it would choose
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/round-monitor.sh '<round>-*' | grep --line-buffered 'DONE '
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/stop-run.sh <round>-<case> ...
```

- Every tool takes `GC_OUT` from `tools/lib/gc-env.sh` (default `/bigtemp/vnr3ne/gc-out`).
- A launch must name its VM image (`CAUSYNTH_CUSTOM_JDK_HOME`; a sweep's `VM_IMAGE`): there is no
  default image.
- `launch-round.sh` chooses each case's head host at launch from the hosts' room in the ledger
  (`campaign_host_room`): the heaviest case first (its `engine_memory_mb`, `tools/lib/heads.sh`
  `case_engine_heap_mb`), each to the host with the most room among those heading the fewest
  cases, so no host heads two before every host heads one; `lift11` heads nothing. A head only drives its campaign: every
  engine JVM, the seed and CONFIRM replays and REPRODUCE's runs go wherever there is room, its own
  host first (PIPELINE §7.7).
- Every replay after a campaign's seed replay (obligations, GROW re-runs, CONFIRM) is charged the
  campaign's measured need (`run_engine.sh` `campaign_replay_need_mb`): the largest resident peak
  its replays stated so far (`workload_rss_mb` in each worker directory; the seed replay's first)
  times 1.5, at least 512 MB; the seed replay's heap is sized for seven times the recording's peak and it is charged twice that peak at its start
  (HDFS seed replays peak at 0.5-1.4 times their recording), growing past it while its host has real room; every
  replay at most half a host's ceiling at its start, growing past it while the host has real room.
  The replay logs say it: "the workload JVM's resident memory peaked at X MB; its host was charged Y
  MB", and the head's log "a replay peaked at X MB (...): every replay from now on needs N MB".
- A round's cases share nothing (`stream_shared_pool=false`): each keeps as many obligations in
  flight as the hosts admit, so one case alone may take the whole cluster. A sweep ("Run the bug
  checks") gives every case `CAUSYNTH_STREAM_SHARED_POOL=true`, so the cases it runs at once share
  the lifts: each exploration keeps its share in flight, the slots of its hosts at its measured
  replay charge (`campaign_pool_slots`: on each lift as many replays as fit under the 70 % ceiling
  at that charge, at most its cores) over the sharing explorations running now (their entries in
  `$CAUSYNTH_HOST_LEDGER/explorations/`), at least one, read again at every start
  (`campaign_stream_has_slot`).
  A sweep's head is admitted (`fanout.sh` `ADMIT_MB`, no lifelong charge: its campaign reserves the room) for the room it reserves on its host
  before it measured anything, what its planner or composer starts at (`tools/lib/heads.sh`
  `case_head_reserve_mb`, 8 GB), not its engine heap: a40's Solr heads asked for 16 GB and waited
  while one case's 27-32 replays filled the lifts. Once its engine JVMs have run, the room it holds
  is their measured peak times 1.25 (`run_engine.sh` `campaign_head_need_mb`). A lift holds the
  largest idle reservation of its heads, not their sum.
- A round name is written once (`accept-<round>-<case>` exists → refused). Names used so far:
  `v*`, `r1`–`r9`, `ra1`, `rb1`, `i1`–`i3`, `stream*`, `fast*`, `g1`, `F1`, `F1b`, `F2`, `K*`, `L*`, `N1`,
  `V1`–`V25`, `V4h`, `V5h`, `V7b`, `V16b`, `V18b`, `V22b`, `V22c`, `V24b`, `PP1`, `PP1b`, `M1`, `CF1`, `STO1`, agents' `a37f*`,
  `ee*`, `agent-*`, `w4-*`, `R5x*`, `r6s*`, `R7*`, `nr*`, `SB*`, `SBX*`, `SBR*`, `EO*`, `ZK*`, `SD*`, `HB*`, `HBA*`,
  `W6C*`, `Z*`, `G*` (in their own `GC_OUT`). Use a fresh name: the next `main` round is `V26`, the next HDFS group round `HG11` (used 2026-10-06/07 on the two HDFS branches: `HL1`, `HL1R-*`, `HF1`-`HF3`, `OK3`-`OK5`, `W21`, `CC*`, `EX1`; used 2026-10-05/06: `HG8*`, `HG9`, `HG9B`, `HG9L-<case>`, `SW1`, `SW1L-45`, `HG10V`; agents', each in its own `GC_OUT`: `TM*`, `CL*`, `AR*`, `AW*`, `DO*`, `FD*`, `CW*`, `SH55`, `NP*`, `WD*`, `SL*`) (HDFS-study names used: `HG1`-`HG5`, `HG5A`, `HG7`, `HS*`, `HN*`, `TD*`, `DS2`-`DS8`, `DC*`, `IOF*`, `HSS*`, `HSC*`, `HOA*`, `HDV*`, `HCS*`; agents' of 2026-10-05, each in its own `GC_OUT`: `RIH*`, `MCH*`, `WHF*`, `HCL*`, `PS*`, `AS*`, `HR*`, `DW*`, `D1`).
- Typical wall time: the 46 HDFS cases each alone on the ten lifts are [../design/PERFORMANCE.md](../design/PERFORMANCE.md)
  §6 (series EX1: most 10-40 min, 11741 ~1.5 h, 07 ~3 h). After the campaign, the acceptance report's `probe.sh` (z3
  per alternative path, 600 s each) can add up to 30 min before the summary row is written; it is reported, not a gate.

**The HDFS group (a sweep of the 46 cases), as the 2026-10-05 lead ran it (round HG7):**

```bash
tools/lib/worktree-add.sh ~/gc-run/<snap> system/hdfs1 --detach
(cd ~/gc-run/<snap> && tools/onlift.sh -g 6 mvn -q -o package -DskipTests)
out=/bigtemp/vnr3ne/gc-out/hdfs-study
cp $out/rounds/HG7.cases $out/rounds/<ROUND>.cases            # the 46 case ids, one per line
cd ~/gc-run/<snap> && (GC_OUT=$out VM_IMAGE=/bigtemp/vnr3ne/vm-hg5/j2sdk-image PRUNE=0 setsid nohup \
  bash tools/adhoc/sweep.sh ~/gc-run/<snap> <ROUND> $out/rounds/<ROUND>.cases 2 \
  > $out/sweep-<ROUND>.log 2>&1 < /dev/null &)
# under a Monitor (it expires after 30 min; the tools keep state in $out/.watch-<ROUND>, so a re-armed one
# does not repeat itself):
(GC_OUT=$out tools/rounds/round-watch.sh <ROUND> & GC_OUT=$out tools/rounds/round-slow.sh <ROUND> HG7 & wait) 2>&1 \
  | grep --line-buffered -E 'DONE|STALLS>=80|SLOW x4|rror'
GC_OUT=$out tools/rounds/round-status.sh <ROUND>     # every started case: age, stage, seed give-ups or its verdict
GC_OUT=$out tools/rounds/round-verify.sh <ROUND>     # every finished case: how EXPLORE ended, z3 on candidate.smt2,
                                                     # BLOCKING gaps, moved roots, CONFIRM
tools/rounds/obl-times.py $out/accept-<ROUND>-<n>/out/<case>/schedule   # EXPLORE's run time vs queue wait
```

- `2` is the number of heads per host. The sweep needs about 5 minutes on NFS before the first
  `accept-<ROUND>-<n>` appears; its first wave (20 heads at once) runs SEED ~3x slower than later starts.
- `PRUNE=0` keeps every artifact (the recordings the offline gate needs; ~1.5-6 GB per case, /bigtemp has room);
  `PRUNE=1` (the default) keeps what a verdict needs.
- A case at 80+ seed give-ups whose class is known (the start-up/clock family, handled by workarounds) is
  stopped, not waited out; mark it in `$out/.watch-<ROUND>/slow.<n>.{2,4}` so the slow watcher stops naming it.
- Stopping a sweep takes two steps:
  1. Kill its `fanout.sh` driver by pid, on the host you launched it from. Find it with
     `ps -eo pid,cmd | grep '[f]anout.sh'`.
  2. Write the run names (`accept-` suffixes) to a file and run `stop-run.sh` ALONE on its command line:
     `ls -d $out/accept-<ROUND>-* | sed 's#.*/accept-##' > /tmp/runs; cd <snap> && GC_OUT=$out xargs
     tools/rounds/stop-run.sh < /tmp/runs` (a command line that also names a run's directory gets killed too).
- A finished case has two lines in its `summary.tsv`; the header is there from the start.
- **The case budget under a full sweep**: `sweep.sh` defaults to `CASE_TIMEOUT_SECONDS=5400`; with 20 heads at once
  the replay slots are the bottleneck and HG9 (2026-10-06) cut six cases (11 12 26 33 37 05: EXPLORATION_CUT or
  MISSING). Launch the full round with `CASE_TIMEOUT_SECONDS=10800`, and hdfs-11741 with `14400` (HF2, 2026-10-06: PASS in
  5168 s; HF1's default 5400 would have cut it). To rerun one case of a sweep with another budget,
  copy its line from `$out/sweep-<ROUND>-jobs.txt`, change `CASE_TIMEOUT_SECONDS=` and the trailing suffix (e.g.
  `HG9L-11`), save it as `$out/<suffix>.job` and start it: `onlift.sh -g 12 bash -c "setsid nohup bash $out/<suffix>.job
  > $out/launch-<suffix>.log 2>&1 < /dev/null &"`. A sweep's driver reads its jobs file once: to change the budget of
  cases still queued, kill the `fanout.sh` driver by pid (its running cases go on) and start a new sweep of the queued
  ones (HG9 -> HG9B).
- **A check added to `checks.tsv`** (a swap) needs its workload's surefire report in the case's tree, or validate
  fails ("missing test report ... run build first"): run its test there once, `tools/onlift.sh -g 8 env
  SKIP_TREE_BUILD=1 MAVEN_REPO_LOCAL=<the tree's Maven repository> experiments/hadoop/build.sh <tree> '<Class>#<method>'`
  (`TestEditLog` for 45, 2026-10-06); it says whether the report names the test.
- **A deep closure alone on the cluster** (a case the sweep's time limit cut; the owner: a large closure must
  converge): `CASE_TIMEOUT_SECONDS=10800 GC_OUT=$out CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-hg5/j2sdk-image
  tools/rounds/launch-run.sh ~/gc-run/<snap> <case> <suffix>` with nothing else running: no shared pool, up to ~120
  replays in flight.

## 5. A snapshot for a branch that needs another tree

There is no override for a case's tree: each `experiments/<system>/<case>/case.sh` names its `repo=` (17899's and
17967's per sub-case, indented; `hdfs-adhoc`'s per check id). To validate a branch on another tree, edit those lines in
the **snapshot only**, uncommitted, never on a system branch, then build and test the snapshot
(`onlift.sh -g 10 bash -c 'mvn -q -o package && bash src/test/shell/run_engine_campaign_helpers_test.sh'`). A tree built
for one branch must not be installed into the shared `~/.m2` (use `MAVEN_REPO_LOCAL`, `experiments/hadoop/build.sh`), or
it changes the jars every other tree's build resolves. A Solr or ZooKeeper workload must be built in the tree the case
names before its first run: `bash experiments/lib/run.sh experiments/solr/<case dir> "<arg>" build` (the snapshot's jar
built first), `SKIP_GRAPHCHECKER_INSTALL=1 bash experiments/lib/run.sh experiments/zookeeper/<case> "<arg>" build` from
the snapshot.

## 6. The offline regression gate (merge gate)

```bash
AB_ACCEPT_ROOT=/bigtemp/vnr3ne/gc-out/hdfs-excl AB_OUT=/bigtemp/vnr3ne/ab/<name> [AB_STAGES="IMPORT EXPLORE.N COMPOSE"] \
  tools/regress/offline-ab.sh --round EX1 <baseline.jar> <candidate.jar> [case...]
```

Re-runs every stage that is a pure function of a recorded round (SEED.static, SEED.trace, PLAN,
EXPLORE.0, SOLVE.0, IMPORT, EXPLORE.N, COMPOSE, CONFIRM planning) with both jars and compares.
`AB_STAGES=EXPLORE.drift` replays the landing order to count re-keyed arms (a change to an arm's
key: `ObligationFactory#dependence`, `Corpus#inputShape`).
No replay: it cannot see VM, runtime or identity changes — those need a live round. Read the
header for `AB_HEAP_MB`, `AB_BASELINE_REPO` (when declarations differ between sides), `AB_HOSTS`.
Keep jars in `/bigtemp/vnr3ne/ab/jars/`.

- Start a gate through `onlift.sh` on a lift other than `lift11`, a few cases (one corpus set) at a time: each case's
  stages wait for ledger room in `ab_place`, and dozens of waiters jammed NFS on lift11 (2026-10-06).
- A corpus recorded before a row-contract change cannot feed the candidate side: gate against rounds recorded by
  this body (EX1, `PRUNE=0`, holds every case's recording and corpus; 07's run is `accept-EX1-adhoc-07e`).

## 7. Reading a campaign, and debugging

`summary.tsv` (verdict row) → `logs/<case>.log` (`[campaign:error] stage=… reason=…`) →
`report/<case>/report.md` (blocking gaps, witness findings, causal cone) → `out/<case>/schedule/final/`
(`claim.json`, `candidate.smt2`, `candidate_composition_manifest.json`, `confirm.json`, `gaps.json`)
→ how EXPLORE ended `iteration-0000/exploration.json` → per planner round
`iteration-0000/obligations-<NNNN>/<id>/` (`obligation_query.smt2`, `obligation_result.jsonl`,
`replay.log`) → sessions `iteration-0000/sessions/<id>/`
(`targets.jsonl` has `reachedAnchor` and `observedFatal`). `experiments/accept/cone.py` and
`probe.sh` re-check a published formula. `tools/analysis/timeline.py`
breaks a campaign's time down by stage.

**Debugging a case** (the method the leads used):
- **Start with the summary.** Its row gives the claim, the verdict and the reason. Then the log's
  `[campaign:error] stage=… reason=…`, then `report/<case>/report.md` and the `final/` artifacts.
  `final/candidate.smt2` is the full free-root formula; re-solve it with `$Z3_BIN` to check
  an UNSAT.
- **A seed replay that is slow or stalled.** Count its schedule give-ups:
  `grep -c 'did not happen' out/<case>/schedule/iteration-0000/seed-result/focused/replay.log`.
  - A few is normal; tens means the replay's order departs from the recording. Read which events did
    not happen and why (which thread, which slot).
  - Take a `jstack` of the replay JVM on its host (`ps -g $(cat <dir>/pgid)` on the head host finds
    the run).
  - Read `schedule.jsonl` and the recording's `ScheduleLog` events around the slot.
- **Time.** `tools/analysis/timeline.py <case dir>` splits a campaign's time by stage and job. Compare
  it with the same case in the previous round. A stage far over its history is a bug until shown
  otherwise.
- **EXPLORE.** `iteration-0000/exploration.json` says why exploration ended. Per round,
  `obligations-<NNNN>/<id>/obligation_result.jsonl` holds ADMITTED / NOT_ADMITTED / UNSAT /
  ADMISSION_GAP, with the reason. Counting refusal reasons across a round finds the dominant waste.
- **The host ledger** (`$CAUSYNTH_HOST_LEDGER/<lift>/charges/`). It tells you whether a step waits
  for memory ("waiting for memory for a head step"). A lapsed charge is a file older than 120 s.
- **Offline first.** A COMPOSE, EXPLORE or CONFIRM-planning change can be replayed on a recorded
  round with `offline-ab.sh` (§6) before any live run.

## 8. Traps the last leads fell into

- **pkill can kill your own shell.** `pkill -f <pattern>` matches every process whose command line
  contains the pattern, including the shell that runs it, and a heredoc counts as part of that command
  line. The lead session runs on `lift11`, which is also a worker. Use `[x]`-style patterns, kill by pid,
  or send the script to `ssh <lift> 'bash -s'` from a file written earlier. `stop-run.sh` is safe.
- **A head's command line does not carry its output path** (`run_engine.sh --config …`): `pgrep -f
  accept-<round>-<case>` finds the workers, not the head, and says "dead" for a live run. Tell a live run by
  `ps -g $(cat accept-<round>-<case>/pgid)` on its head host.
- **A starved head step looks like a hang:** a step that needs more than the ledger can ever free on a busy
  lift waits silently (`waiting for memory for a head step … on any host`). Main now holds the best host for a
  waiting step and starts GROW's planner at 2 GB; if a log goes quiet for many minutes, read the step's own
  stderr (`obligations-<NNNN>/grow-stderr.log`).
- **Never rebuild a tree that someone reads.** Check `pgrep -fc '[h]adoop-hdfs-study-r7'` (etc.) on every lift first;
  replays read the tree's `target/classes` directly.
- **Parallel coverage or test runs can corrupt a tree's `target/test-classes`** (a broken `ssl-client.xml`
  once failed every HDFS workload; the backup is in `/bigtemp/vnr3ne/analysis/corrupt-test-classes/`).
- **A monitor re-armed on `round-monitor.sh` re-reports every finished case;** filter out the ones you have.
- **One run is not a verdict on a flaky case.** 11741 (balancer dispatcher timing) and solr-18413 (ZooKeeper
  watch timing, Overseer queue) have real races; a CONFIRM refutation there can be the race, not the branch.
- **Composite changes hide their culprit.** When several branches are stacked in one snapshot and a case fails,
  run the case on plain main and on main + one branch before deciding.
- **Launch a canary through `launch-round.sh`** (or `launch-run.sh` from `3007804da` on): before that,
  `launch-run.sh` left a run's obligations on its head host alone (W6C2-W6C4 ran on lift11, 2-3 replays at a time).
- **Recordings run on stock HotSpot; only replays run on the concolic VM image.** A recording hang is never the
  image's fault.
- **The Solr trees carry a workaround for an upstream `ZkStateReader` race** (a stale fetch resurrects a deleted
  collection; a delete's `waitForState` then hangs forever under `CausynthBounds`). A new Solr tree needs the same
  per-collection refresh lock (`gc/solr-unified-storing` `04f8489`).
- **A `Monitor` expires after 30 minutes;** re-arm it for the cases still running and filter the ones you have.
- **Lapsed ledger charges are still files** until ten leases pass: judge a host by the charges whose mtime is
  younger than 120 s, not by `ls | wc -l`.
- **The home quota is 100 GB** and has filled twice: round outputs, VM images and worktrees of other trees go
  to `/bigtemp/vnr3ne`. Remove old snapshots with `tools/rounds/snapshot-gc.sh` (it refuses one in use).
- **`stop-run.sh` kills every process whose command line names the run's directory, your own shell included**: a
  command that ran `stop-run.sh HG5A-0` and, in the same line, grepped `accept-HG5A-0/...` killed the lead's shell
  (exit 144). Run it alone; feed many names through a file and `xargs`.
- **Kill by pid, never by pattern**: an agent's `kill` of `tools/regress/offline-ab.sh` by pattern hit another agent's
  gate on lift11.
- **`jstack` leaves `.attach_pid<pid>` in the target JVM's working directory**, which is a case tree for a workload:
  FREEZE's checkout digest once failed on it vanishing mid-hash (now tolerated, d8d26347e); jstack sparingly while a
  sweep freezes.
- **`onlift.sh` goes over ssh, which drops exported variables**: `onlift.sh -g 12 env MAVEN_REPO_LOCAL=... cmd`, never
  `MAVEN_REPO_LOCAL=... onlift.sh cmd` (a tree build then installs into the shared `~/.m2`).
- **A sweep's `PRUNE=1` deletes the recordings** (`runtime/`) the offline gate replays; HG5A could not feed any gate.
  Keep `PRUNE=0` for a round you will gate against.
- **A verdict row is not a verdict**: a `UNSAT_CLOSED` whose exploration ended `CAMPAIGN_BUDGET_REACHED` was cut
  (now EXPLORATION_CUT, a RUN_DEFECT); always check with `tools/rounds/round-verify.sh`.
- **A stopped run still writes its summary row** (`MISSING`, after the stop): do not read it as a failure of the case.
- **A wait that matches itself never ends**: `until ! pgrep -f '<string>'` matches its own shell when the string is in its
  command line (the lead's and an agent's waits ran for hours). Wait on a pid (`kill -0 <pid>`) or a file, with a
  `timeout`.
- **`git status` in a full (non-sparse) worktree on NFS takes minutes and holds `index.lock`**: a backgrounded one
  blocked the lead's merge commit. Use sparse worktrees (`tools/lib/worktree-add.sh`); never background a git status.
- **The ledger's memory reading under many waiters** (fixed b7c5dc99d): every waiter refreshed every host's reading
  over ssh and renamed it into one NFS directory every 5 s; 254 processes sat in D state on lift11. Now one shell per
  host refreshes (`<host>/refresh`) and the others use a reading up to 30 s old.
- **A Hadoop tree hook calls a shim method the jar must have**: a tree with A4's door calls throws NoSuchMethodError at
  the first IPC under any jar without `received`/`outboundResponse`; the shim entry goes into `system/hdfs` before the
  tree is built.
