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
| z3 | `~/.local/bin/z3` (4.14.1) |
| concolic VM images | `system/hdfs`'s VM: **`/bigtemp/vnr3ne/vm-hg5/j2sdk-image`** (vm-size-source + the container observation of scope batch 1: list/deque/HashSet iterators reach their tracked container, a read record states its observed version `{fieldVersionId, versionKind}` in envelope schema 2, outside mutations marked after they run; sources = branch `hdfs-vm-hg5` `742f13363`, merged into `system/hdfs`; its `SOURCE.txt` and `smoke.log` sit beside it). `vm-size-source` (an INDEXED size skips element sets) served HG2-HG4. `main`'s VM: `vm-model-guards2` (no model records a condition). Older: `vm-streams2`, `vm-w4h` (rounds before V19). Superseded, deletable: `vm-model-guards`, `vm-streams`, `vm-hdfs-scope-container`, `vm-hdfs-scope-rows`. Parked, unreviewed: `vm-w4i` (branch `perf-vm-readout`), `vm-nr41` (branch `vm-ref-compare`). Pass an image as `CAUSYNTH_CUSTOM_JDK_HOME` (a sweep: `VM_IMAGE`), never as `JAVA_HOME`. A Java side that needs natives an image lacks refuses the replay by name (`ConcolicVmBroker#requireCurrentCapabilities`); a jar after `hdfs-scope-rows` refuses a schema-1 image. |
| HDFS trees | **`/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r5`** (`gc/hdfs-study-r5`, a worktree of `~/hadoop`, Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-r5`): every HDFS case but 11741 on `system/hdfs` (the 36 study checks, the eight named block-key/snapshot cases, `hdfs-bugs-slowdisk-zero`); = r4 (r3 plus the IPC handler opening a call's exchange before `doAs`) plus the IPC request's start at the RPC engine's invoke point. A tree change that adds or removes a statement in a method shifts its Jimple unit ids: a case's `loop-bounds.jsonl` rows naming them must follow (r5: `Client#sendRpcRequest` `#u54`/`#u59` -> `#u53`/`#u58`). A case's classpath is read off its own workload's surefire report in the tree: a case whose workload never ran there fails validate ("missing test report"), so after a rebuild run every case's test once (`./mvnw -o -Dmaven.repo.local=<repo> ... -pl hadoop-hdfs-project/hadoop-hdfs surefire:test -Dtest=<Class#method,...>`). r3 (`/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r3`, superseded) = `gc/hdfs-study-next` (the 49 study markers, MiniJournalCluster hooks, node-startup brackets, startup window, weak adapter registries, the NameNode's heartbeat tick, the IPC door naming its verb) + `gc/hdfs-study-startup` (the NameNode's `registerDatanode` write lock is the startup step that fixes the DataNodes' order); Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-next`. hdfs-11741: `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-r5` (`gc/hdfs-11741-r5`, Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-r5`; superseded: `hadoop-hdfs-11741-r4`, `-verb`). A copied Maven repo may hold an older GraphChecker jar than the tree calls (r4's lacked `startupStep`): install the current one first (`mvn -o install:install-file -Dfile=<jar> -DpomFile=pom.xml -Dmaven.repo.local=<repo>`). `main`'s cases run `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` (`gc/hdfs-unified-dtx`, Maven repo `/bigtemp/vnr3ne/wt/dtx/m2`); its inventory `/bigtemp/vnr3ne/analysis/unify/hdfs-inventory.md`. Older trees (`gc/hdfs-study`, `gc/hdfs-bugs`, `~/hadoop-hdfs-11741`, the `-w6` trees of `wire-codec-p1`) serve only the runs and branches that name them. A server-side class compiled into a tree by hand (r3's `FSNamesystem`) used the snapshot's `GraphChecker-1.0-SNAPSHOT-hadoop-shim.jar` on the classpath: `javac -source 8 -target 8 -cp "$SHIM:target/classes:$(cat hdfs-cp.txt)" -d target/classes <file>`. |
| Solr trees | One Solr 8.11 tree line, `~/lucene-solr-unified` (branch `gc/solr-unified`, a worktree of `~/lucene-solr-8_11`): the shared adapter, both cases' workloads and target markers, the two kept scaffold patches (inventory: `/bigtemp/vnr3ne/analysis/unify/solr-inventory.md`); solr-18406 and solr-18413 name its successor `gc/solr-unified-storing` (`/bigtemp/vnr3ne/wt/lucene-solr-storing`: the same plus SolrZkClient's `MessageDoors#storing` write brackets). The older per-case worktrees (`gc/solr`, `~/lucene-solr-18406`, `~/lucene-solr-18413`, `~/lucene-solr-8_11-adhoc`) serve only rounds started on them. Ant build; native Ant tests need `-Dtests.useSecurityManager=false`. `~/solr` is apache/solr main (blobless: never `git grep` a commit there). |
| ZooKeeper trees | `/bigtemp/vnr3ne/wt/zookeeper-hb` (`gc/zk-unified-hb`, + the RESPONSE door, for `hb-schedule`; Maven repo `/bigtemp/vnr3ne/m2/zookeeper-hb`). `/bigtemp/vnr3ne/wt/zookeeper-unified` (branch `gc/zk-unified` on `branch-3.9`, a worktree of `~/zookeeper`): the adapter (`CausynthZk`, `CausynthZkCluster`), the `zk-bugs` cases' target markers and the quota workload. Maven build into its own repository `/bigtemp/vnr3ne/m2/zookeeper` (`experiments/zookeeper/build.sh`, which installs the GraphChecker jar there; never `~/.m2`). Build a case's workload before its first run: `SKIP_GRAPHCHECKER_INSTALL=1 bash experiments/lib/run.sh experiments/zookeeper/zk-bugs <case> build`. Its only remote is apache/zookeeper: never push it. |
| HBase and bug trees | `gc/hbase-unified`, `gc/solr-bugs`, `gc/hdfs-bugs`, `gc/hdfs-unified-dtx-w6`, `gc/hdfs-11741-w6` under `/bigtemp/vnr3ne/wt/` ([STATE.md](STATE.md) §5); clones `~/hbase`, `~/zookeeper`, `~/hadoop`, `~/lucene-solr-8_11`; private Maven repos `/bigtemp/vnr3ne/m2/<name>` |
| integration worktree | `/bigtemp/vnr3ne/wt/gc-hg4b` (branch `hg5`): where the 2026-10-04 lead merged each HDFS round's feature branches before snapshotting (`~/gc-run/hg<N>`). `/bigtemp/vnr3ne/wt/main-pw` is the 2026-10-03 lead's merge worktree for `main` rounds |
| host ledger | `$CAUSYNTH_HOST_LEDGER` = `/bigtemp/vnr3ne/gc-out/hosts/<lift>/charges/<mb>.<host>.<pid>.<time>.<rand>`: a charge's mtime is its 120 s lease, renewed every 10 s by its holder; a lapsed lease no longer counts (it is deleted at ten leases); `explorations/` = the capped explorations running. `ls` the charges of a host to see what holds it |
| evidence and agent tools | `/bigtemp/vnr3ne/gc-out/solr-bugs/{evidence,agent-tools,scripts}` (jstacks of the ZkStateReader-race hangs, A2's `watch-sb.sh`/`watch-stall.sh` run watchers, the storing tree's `spelledAs-adapter.patch`); `/bigtemp/vnr3ne/readout-stream/` (A6's `measure-seed.sh`, `measure-obl.sh`, `compare.py` and the retained-heap tool `heap/tool/HeapRetained.java`: how replay memory was measured; 4.2 GB of data); `/bigtemp/vnr3ne/gc-out/hb-schedule/` (Z1–Z5 with their `run.sh` recipes); `/bigtemp/vnr3ne/ab/` (offline gates; jars in `ab/jars/`) |
| round outputs | `/bigtemp/vnr3ne/gc-out/hdfs-study/` (the HDFS group: `accept-<round>-<n>/`, `sweep-<round>-cases.tsv` maps n to the case, `rounds/<round>.cases` and `rounds/<round>-review.md`); `/bigtemp/vnr3ne/gc-out/<branch or agent>/` for agents' runs; `gc-out/accept-V*` the `main` rounds |
| owner's memory notes | `~/.claude/projects/-u-vnr3ne-GraphChecker/memory/` (one fact per file, index `MEMORY.md`) |

## 2. Helper commands (outside the repo)

```bash
/bigtemp/vnr3ne/bin/onlift.sh [-g <min-free-GB>] [-h <host>] <command...>
    # run a command in the current directory on the least-loaded lift (or <host>) with the Java 8 +
    # Maven toolchain; use it for mvn, the shell test, VM builds, offline stages, anything heavy.
    # `onlift.sh -h` with no host hangs; always give a host or omit -h.
/bigtemp/vnr3ne/bin/pick-lift.sh [min-free-GB]   # prints the best lift
```

Round tools (in the repo, `tools/rounds/`; `GC_OUT` names the output root): `round-status.sh <round>` (every started
case: age, stage, seed give-ups, or its verdict), `round-watch.sh <round> [<baseline>]` (one line per finished case, per seed
replay past 30/80 give-ups, and STALLS-REGRESSION when a seed replay passes twice the baseline round's give-ups of the
same case), `round-slow.sh <round> <baseline>` (a running case past 2x/4x its baseline time),
`round-verify.sh <round> [case...]` (how EXPLORE ended, z3 on the exported formula, BLOCKING gaps, moved roots,
CONFIRM, and the formula's leaf symbols: NO-SYMBOL marks an UNSAT over nothing that moves, a scope hole to read before
it counts), `obl-times.py <case>/schedule` (EXPLORE: run time vs queue wait per verdict, concurrency, refusal
reasons). How to debug a slow case: [../design/PERFORMANCE.md](../design/PERFORMANCE.md) §4. Reading a `.smt` by hand:
`tools/analysis/smt-legend.py <out/case> --repo <tree>` names every leaf symbol of `final/candidate.smt2` (each root's
door or configuration and where it was minted, each read's node, region, method and field, each handoff's port and
producer), the starting point of every causal-chain check.

## 3. Build, test, commit

```bash
cd ~/GraphChecker
/bigtemp/vnr3ne/bin/onlift.sh -g 10 bash -c 'mvn -q -o package && bash src/test/shell/run_engine_campaign_helpers_test.sh'
```

Keep `-o` (offline): `~/.m2` is shared over NFS. `mvn package` also builds the `hadoop-shim`
classifier jar from `src/shim/java`, which the HDFS trees call. A snapshot needs all three jars in
`target/` (`-jar-with-dependencies`, `-hadoop-shim`, plain).

VM: build with `third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh`
(or the recipe under `/bigtemp/vnr3ne/vm-w1/work/`, see `docs/design/VM.md`), ~1 h for a full JDK,
via `onlift.sh -g 12`. Smoke tests: `scripts/causynth_smoke_test.sh` with `JDK_HOME` = the image.
Never overwrite an image a round uses; build a new directory.

## 4. Rounds (live campaigns)

```bash
git worktree add --detach ~/gc-run/p<N> <commit>
(cd ~/gc-run/p<N> && /bigtemp/vnr3ne/bin/onlift.sh -g 10 mvn -q -o package -DskipTests)
GC_OUT=/bigtemp/vnr3ne/gc-out CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-model-guards2/j2sdk-image \
  tools/rounds/launch-round.sh ~/gc-run/p<N> <round>              # all 11 cases, heads chosen by room
CASES="hdfs-17960 solr-18413" ... tools/rounds/launch-round.sh ... # a subset (or any case id); the 14 regression
#   cases: hdfs-11741 hdfs-17897 hdfs-17899-bug1 hdfs-17899-bug2 hdfs-17899-bug3 hdfs-17960 hdfs-17967-pathA
#   hdfs-17967-pathB hdfs-17967-pathC solr-18406 solr-18413 zk-bugs-quota-init zk-bugs-election-offer hdfs-bugs-slowdisk-zero
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
  times 1.5, at least 512 MB; the seed replay is charged seven times the recording's peak; every
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
  `W6C*`, `Z*`, `G*` (in their own `GC_OUT`). Use a fresh name: the next `main` round is `V26`, the next HDFS group round `HG8` (HDFS-study names used: `HG1`-`HG5`, `HG5A`, `HG7`, `HS*`, `HN*`, `TD*`, `DS2`-`DS8`, `DC*`, `IOF*`, `HSS*`, `HSC*`, `HOA*`, `HDV*`, `HCS*`; agents' of 2026-10-05, each in its own `GC_OUT`: `RIH*`, `MCH*`, `WHF*`, `HCL*`, `PS*`, `AS*`, `HR*`, `DW*`, `D1`).
- Typical wall time on main (round `V25`, cluster shared with agent runs): HDFS RPC cases 7–12 min (up to 30
  on a busy cluster), 17960 ~12 min, 11741 ~34 min, solr-18406 ~20 min, solr-18413 ~23 min, quota-init ~10 min,
  election-offer ~34 min, slowdisk-zero ~9 min. After the campaign, the acceptance report's
  `probe.sh` (z3 per alternative path, 600 s each) can add up to 30 min before the summary row is
  written; it is reported, not a gate.
- **How the last lead used the servers:** one round at a time, at most ~6–8 cases at once (batch 1
  = six cases, then the rest as cases finish); sweeps with 1 head per host
  (`sweep.sh … 1`); agents' verification runs in their own `GC_OUT`; every start through the ledger
  (≤ 70 % memory per lift); `lift11` (the owner's machine, where the lead session runs) works but
  never heads; builds with `onlift.sh -g 10`.

**The HDFS group (a sweep of the 46 cases), as the 2026-10-05 lead ran it (round HG7):**

```bash
git -C ~/GraphChecker worktree add --detach ~/gc-run/<snap> system/hdfs
(cd ~/gc-run/<snap> && /bigtemp/vnr3ne/bin/onlift.sh -g 6 mvn -q -o package -DskipTests)
out=/bigtemp/vnr3ne/gc-out/hdfs-study
cp $out/rounds/HG7.cases $out/rounds/<ROUND>.cases            # the 46 case ids, one per line
cd ~/gc-run/<snap> && (GC_OUT=$out VM_IMAGE=/bigtemp/vnr3ne/vm-hg5/j2sdk-image PRUNE=0 setsid nohup \
  bash tools/adhoc/sweep.sh ~/gc-run/<snap> <ROUND> $out/rounds/<ROUND>.cases 2 \
  > $out/sweep-<ROUND>.log 2>&1 < /dev/null &)
# under a Monitor (it expires after 30 min; the tools keep state in $out/.watch-<ROUND>, so a re-armed one
# does not repeat itself):
(tools/rounds/round-watch.sh <ROUND> & GC_OUT=$out tools/rounds/round-slow.sh <ROUND> HG7 & wait) 2>&1 \
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
- A case at 80+ seed give-ups whose class is known (the start-up/clock family, until the time model lands) is
  stopped, not waited out; mark it in `$out/.watch-<ROUND>/slow.<n>.{2,4}` so the slow watcher stops naming it.
- Stopping a sweep takes two steps:
  1. Kill its `fanout.sh` driver by pid, on the host you launched it from. Find it with
     `ps -eo pid,cmd | grep '[f]anout.sh'`.
  2. Write the run names (`accept-` suffixes) to a file and run `stop-run.sh` ALONE on its command line:
     `ls -d $out/accept-<ROUND>-* | sed 's#.*/accept-##' > /tmp/runs; cd <snap> && GC_OUT=$out xargs
     tools/rounds/stop-run.sh < /tmp/runs` (a command line that also names a run's directory gets killed too).
- A finished case has two lines in its `summary.tsv`; the header is there from the start.
- **A deep closure alone on the cluster** (a case the sweep's time limit cut; the owner: a large closure must
  converge): `CASE_TIMEOUT_SECONDS=10800 GC_OUT=$out CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-hg5/j2sdk-image
  tools/rounds/launch-run.sh ~/gc-run/<snap> <case> <suffix>` with nothing else running: no shared pool, up to ~120
  replays in flight.

## 5. A snapshot for a branch that needs another tree

There is no override for a case's tree: each `experiments/<system>/<case>/case.sh` names its `repo=`. To
validate a branch that needs a different tree (no branch does today; `pairing-port` needed
`/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` before its merge), edit those lines in the **snapshot only**, uncommitted,
never on main:

```bash
git worktree add -q --detach ~/gc-run/p<N> <main>
cd ~/gc-run/p<N> && git merge --no-ff -q <branch> -m "Validation merge: <branch>"     # resolve docs conflicts by keeping both sides
sed -i 's#repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx$#repo=<tree>#' \
  experiments/hadoop/hdfs-17967/case.sh experiments/hadoop/hdfs-17899/case.sh \
  experiments/hadoop/hdfs-17960/case.sh experiments/hadoop/hdfs-17897/case.sh
/bigtemp/vnr3ne/bin/onlift.sh -g 10 bash -c 'cd ~/gc-run/p<N> && mvn -q -o package && bash src/test/shell/run_engine_campaign_helpers_test.sh'
```

The `case.sh` files of 17899 and 17967 hold indented `repo=` lines (one per sub-case), hence no `^` there.
11741 keeps `~/hadoop-hdfs-11741`. A tree built for one branch must not be installed into the shared
`~/.m2` (use `MAVEN_REPO_LOCAL`, `experiments/hadoop/build.sh`), or it changes the jars every other tree's
build resolves. A Solr workload must be built in the Solr tree the case names before its first run:
`SKIP_GRAPHCHECKER_INSTALL=1 bash experiments/lib/run.sh experiments/solr/<case> "" build` from the snapshot.

## 6. The offline regression gate (merge gate)

```bash
AB_ACCEPT_ROOT=/bigtemp/vnr3ne/gc-out AB_OUT=/bigtemp/vnr3ne/ab/<name> [AB_STAGES="IMPORT EXPLORE.N COMPOSE"] \
  tools/regress/offline-ab.sh --round r8 --round r7 <baseline.jar> <candidate.jar> [case...]
```

Re-runs every stage that is a pure function of a recorded round (SEED.static, SEED.trace, PLAN,
EXPLORE.0, SOLVE.0, IMPORT, EXPLORE.N, COMPOSE, CONFIRM planning) with both jars and compares.
`AB_STAGES=EXPLORE.drift` replays the landing order to count re-keyed arms (a change to an arm's
key: `ObligationFactory#dependence`, `Corpus#inputShape`).
No replay: it cannot see VM, runtime or identity changes — those need a live round. Read the
header for `AB_HEAP_MB`, `AB_BASELINE_REPO` (when declarations differ between sides), `AB_HOSTS`.
Keep jars in `/bigtemp/vnr3ne/ab/jars/`.

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
  `final/candidate.smt2` is the full free-root formula; re-solve it with `~/.local/bin/z3` to check
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
- **Never rebuild a tree that someone reads.** Agents run checks on `/bigtemp/vnr3ne/wt/hadoop-hdfs-dtx` and the
  Solr trees too: check `pgrep -fc '[h]adoop-hdfs-dtx'` (etc.) on every lift first; replays read the tree's
  `target/classes` directly.
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
