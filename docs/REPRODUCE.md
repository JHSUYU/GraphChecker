# Reproducing the checks from GitHub: the 46 HDFS cases (§0-§5), Solr (§6), HBase (§7), ZooKeeper (§8)

Everything a run needs is on GitHub: GraphChecker's branch of the system (the engine, the case settings, the VM
sources) and the system's fork, whose `graphchecker/*` branch is the tree under test (the adapter, the target markers,
the workloads). Clone the two, check out those branches, and the section of the system runs its cases. Nothing on the
cluster's disks is assumed besides the operating system packages below (§0).

| repository | branch | what it holds |
| --- | --- | --- |
| `git@github.com:JHSUYU/GraphChecker.git` (private) | `system/hdfs` | the locked body: the engine that closed 39 cases (the named bugs but 11741, and 30 study checks) |
| | `system/hdfs1` | the newest body: the other 7 cases (07 11741 21 29 30 39 40), these tools, the VM sources |
| | `system/solr` | the 20 Solr cases (§6) |
| | `system/hbase` | the 22 HBase cases (§7), `results/hbase/` |
| | `system/zookeeper` | the 16 ZooKeeper cases (§8), `results/zookeeper/` |
| `https://github.com/JHSUYU/hadoop.git` (public fork) | `graphchecker/hdfs-checks` | the HDFS tree of 43 cases (tree `hadoop-hdfs-study-r7`) |
| | `graphchecker/hdfs-checks-adhoc07` | hdfs-adhoc-07's tree (`hadoop-hdfs-study-r8`) |
| | `graphchecker/hdfs-checks-adhoc21` | hdfs-adhoc-21's tree (`hadoop-hdfs-21`) |
| | `graphchecker/hdfs-11741` | hdfs-11741's tree (`hadoop-hdfs-11741-r6`): trunk with HDFS-11741's fix reverted |
| `https://github.com/JHSUYU/solr.git` (public fork) | `graphchecker/solr-checks` | the Solr tree (`lucene-solr-checks`) |
| `https://github.com/JHSUYU/hbase.git` (public fork) | `graphchecker/hbase-checks` | the HBase tree (`hbase-checks`) |
| `https://github.com/JHSUYU/zookeeper.git` (public fork) | `graphchecker/zookeeper-checks` | the ZooKeeper tree (`zookeeper-checks`) |

Which branch runs which case, with the case's budget and what series EX1 ended with, is
[`experiments/hadoop/hdfs-cases.tsv`](../experiments/hadoop/hdfs-cases.tsv); which fork branch each tree is,
[`experiments/hadoop/trees.tsv`](../experiments/hadoop/trees.tsv). The VM sources
(`third_party/OpenJDK-Concolic-Execution-Engine`) are the same on both GraphChecker branches, so one image serves both.

## 0. The machines

- Linux x86_64 hosts (Ubuntu 22.04 here: ten hosts `lift06`-`lift15`, 48 cores and 30 GB each). One host works; a case
  then takes several times longer (PERFORMANCE §6 was measured on ten).
- One filesystem mounted at the same path on every host (`GC_BULK`, here `/bigtemp/vnr3ne`), the home directory shared
  too, passwordless `ssh -o BatchMode=yes` between the hosts, and a local scratch directory `/localtmp/$USER` on each.
- Packages: `openjdk-8-jdk` (at `/usr/lib/jvm/java-8-openjdk-amd64`), `maven` (`/usr/lib/maven/bin`), `git`,
  `python3`, `rsync`. For the VM build, on one host: `gcc-6`/`g++-6` and `libffi-dev libfreetype6-dev libcups2-dev
  libasound2-dev libx11-dev libxext-dev libxt-dev libxrender-dev libxtst-dev zip unzip` (or Docker: step 2).
- z3 4.14.1: unpack `https://github.com/Z3Prover/z3/releases/download/z3-4.14.1/z3-4.14.1-x64-glibc-2.35.zip` and put
  `bin/z3` at `~/.local/bin/z3` (or name it as `Z3_BIN`).

Where things go is stated once, in [`tools/lib/gc-env.sh`](../tools/lib/gc-env.sh): `GC_BULK` (the shared storage),
`GC_OUT` (run outputs), `GC_TREES` (the system trees), `GC_M2` (their Maven repositories), `Z3_BIN`, `LIFTS` (the
hosts), `CAUSYNTH_HOST_MAX_USED_PCT` (70: no start may leave a host fuller) and `CAUSYNTH_HOST_MAX_CORES_PCT` (100: the
percent of a host's cores its live charges may keep busy). On another cluster, edit those
defaults in that file on both checkouts. A value exported in the shell that starts a run also works: every hop of the
run passes them on (`gc_env_words`); `tools/onlift.sh` does not, so give it `env NAME=value` in its command. The
commands from step 2 on use these variables: `source ~/GraphChecker-hdfs1/tools/lib/gc-env.sh` in the shell first.

## 1. GraphChecker, both branches

```bash
for b in hdfs1 hdfs; do
  git clone -q --no-checkout -b system/$b git@github.com:JHSUYU/GraphChecker.git ~/GraphChecker-$b
  git -C ~/GraphChecker-$b sparse-checkout set --no-cone '/*' '!/third_party/'
  git -C ~/GraphChecker-$b checkout -q system/$b
  (cd ~/GraphChecker-$b && ~/GraphChecker-hdfs1/tools/onlift.sh -g 6 mvn -q package -DskipTests)
done
```

The checkouts leave out `third_party/` (the VM's 47,000 source files, which no build or run reads; step 2 clones them
apart). `tools/onlift.sh` runs a command in the current directory on the host of `LIFTS` with the most room, with
Java 8 and Maven on its path; use it for every build. The first build downloads the dependencies into `~/.m2`. The jars
(`target/GraphChecker-1.0-SNAPSHOT{,-jar-with-dependencies}.jar`; on `system/hdfs` also `-hadoop-shim`) are what a run reads; leave a checkout
alone while a run uses it.

## 2. The concolic VM image

On a host with gcc-6, a full clone on its local disk:

```bash
ssh <host> 'git clone -q -b system/hdfs1 git@github.com:JHSUYU/GraphChecker.git /localtmp/$USER/gc-vm &&
  /localtmp/$USER/gc-vm/tools/vm/build-image.sh <GC_BULK>/vm/hdfs'
```

A full OpenJDK 8 (Zero, release, `-DENABLE_CONCOLIC`) built on the host's local disk, then the causynth smoke suite
on it: `$GC_BULK/vm/hdfs/j2sdk-image` is the image (`CAUSYNTH_CUSTOM_JDK_HOME`), `SOURCE.txt` the commit it was built
from, `smoke.log` the suite (`SMOKE_EXIT=0`, 24 `OK` lines). About 3 minutes at `JOBS=40` (lift15, 2026-10-08). A
host without gcc-6:
`FULL_JDK=true third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh` (Ubuntu 18.04
container), then copy its `build/linux-x86_64-normal-zero-release/images/j2sdk-image`.

## 3. The four HDFS trees

```bash
cd ~/GraphChecker-hdfs1
for t in hadoop-hdfs-study-r7 hadoop-hdfs-study-r8 hadoop-hdfs-21 hadoop-hdfs-11741-r6; do
  tools/onlift.sh -g 8 experiments/hadoop/prepare-trees.sh $t > $GC_BULK/prepare-$t.log 2>&1 &
done; wait
```

Each tree is cloned from the fork at `$GC_TREES/<name>` on its branch, built against `system/hdfs1`'s jar with a
Maven repository of its own (`$GC_M2/<name>`; hadoop-hdfs and every module it needs, Java 8), and then runs the
workload of every case that names it once natively: a case's classpath is read off its workload's surefire report, so
a case whose workload never ran in its tree fails validate ("missing test report"). The log ends with one line per
workload, `PASSED` or `FAILED` (a native failure still leaves the report the case needs) or `MISSING` (the script
fails). A native `FAILED` seen once: `TestDFSStartupVersions#testVersions` in the long combined run (a DataNode's
storage lock still held by the previous one in the same JVM); it passed when run again alone. Both GraphChecker
branches read these trees: a run puts its own jar ahead of the tree's classpath. 10-25 minutes a tree (clone over
NFS, build, workloads; r7 with its 43 workloads the longest; 2026-10-08), the four in parallel.

## 4. Running the cases

One case, from the checkout of its branch (the table's `branch` and `budget_s` columns):

```bash
cd ~/GraphChecker-hdfs1
export GC_OUT=$GC_BULK/gc-out/repro CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/hdfs/j2sdk-image
CASE_TIMEOUT_SECONDS=21600 tools/rounds/launch-run.sh ~/GraphChecker-hdfs1 hdfs-adhoc-29 R1-adhoc-29
```

The run is a session of its own (`setsid`) and holds the shell until the case ends (start it as `(setsid nohup ... >
<log> 2>&1 < /dev/null &)` to leave it running); it writes `$GC_OUT/accept-R1-adhoc-29/` and ends with the second
line of its `summary.tsv`. Its
obligations go to every host of `LIFTS`. `tools/rounds/stop-run.sh R1-adhoc-29` (with the same `GC_OUT`) stops it.

All 46, each alone on the cluster, as series EX1 ran them:

```bash
cd ~/GraphChecker-hdfs1
(setsid nohup tools/rounds/run-series.sh R1 experiments/hadoop/hdfs-cases.tsv system/hdfs=$HOME/GraphChecker-hdfs \
  system/hdfs1=$HOME/GraphChecker-hdfs1 > $GC_OUT/series-R1.out 2>&1 < /dev/null &)
```

Each case runs from the checkout of its branch with its budget; naming case ids after the checkouts runs only
those. The series took 15.2 h on the ten hosts (most cases 10-40 min, 11741 ~45 min, 07 ~3 h); a stopped series
resumes by the same command (finished cases are skipped); `touch $GC_OUT/series-R1.STOP` ends it before its next
case. Many cases at once instead: `tools/adhoc/sweep.sh` ([handover/OPERATIONS.md](handover/OPERATIONS.md) §4).

## 5. Reading the results

```bash
tools/rounds/round-verify.sh R1      # how each EXPLORE ended, z3 on the file, gaps, roots
tools/rounds/series-stats.py R1      # claim, time breakdown, closure regions per case
```

A case reproduces when its claim is the table's `ex1_claim`: SAT (`SAT_CANDIDATE`: confirmed by a replay, reproduced
natively) for the ten named bugs and hdfs-adhoc-10 and -12; UNSAT (`UNSAT_CLOSED`: z3 on the exported
`final/candidate.smt2` says unsat, EXPLORE at its fixed point) for the rest; hdfs-adhoc-21 `RUN_DEFECT` (its accepted
residue). The report's `PASS` also checks a named bug's declared mechanism; a study check declares none, so its report
says `FAIL` whatever its claim: the claim and round-verify decide, as [handover/CHECKING.md](handover/CHECKING.md) §1
says. What each `.smt` must contain (its causal chain, symbols and propagation, read by hand against the HDFS code)
is each case's row in [STATUS.md](STATUS.md) "HDFS checks"; `tools/analysis/smt-legend.py <run>/out/<case>` names every symbol of a formula.
Wall times vary run to run (replays race); the EX1 rows are in [design/PERFORMANCE.md](design/PERFORMANCE.md) §6.

## 6. The Solr cases

The 20 Solr cases ([`experiments/solr/solr-cases.tsv`](../experiments/solr/solr-cases.tsv): case, branch, budget) run
on GraphChecker's `system/solr` and one Solr 8.11 tree, the branch `graphchecker/solr-checks` of the public fork
`https://github.com/JHSUYU/solr.git` (tree `lucene-solr-checks`,
[`experiments/solr/trees.tsv`](../experiments/solr/trees.tsv)): Apache Lucene/Solr `branch_8_11` (8.11.4, `faca81b`)
with the adapter, every case's target marker and the bug checks' workloads.

1. **GraphChecker.** As §1, on the branch `system/solr`:

   ```bash
   git clone -q --no-checkout -b system/solr git@github.com:JHSUYU/GraphChecker.git ~/GraphChecker-solr
   git -C ~/GraphChecker-solr sparse-checkout set --no-cone '/*' '!/third_party/'
   git -C ~/GraphChecker-solr checkout -q system/solr
   (cd ~/GraphChecker-solr && tools/onlift.sh -g 6 mvn -q package -DskipTests)
   source ~/GraphChecker-solr/tools/lib/gc-env.sh
   ```

2. **The image.** As §2, from `system/solr` (its VM sources carry the forced replay's native,
   `System.forceNextConcolicBranch`, which the HDFS image lacks, and the one-channel read-out,
   `System.readOutTrackedLocations`: the runtime refuses an image without it by name -- a seed replay ends "Concolic task
   plan requires current custom VM broker capabilities: [readOutTrackedLocations]"; on the cluster the image is
   `/bigtemp/vnr3ne/vm-force10/j2sdk-image`, built from these sources):

   ```bash
   ssh <host> 'git clone -q -b system/solr git@github.com:JHSUYU/GraphChecker.git /localtmp/$USER/gc-vm-solr &&
     /localtmp/$USER/gc-vm-solr/tools/vm/build-image.sh <GC_BULK>/vm/solr'
   ```

   `$GC_BULK/vm/solr/j2sdk-image` is `CAUSYNTH_CUSTOM_JDK_HOME` for every Solr run.

3. **The tree.** Besides §0's packages it needs Apache Ant with Ivy (`ant ivy-bootstrap` once per host; Ant resolves
   the tree's libraries into `~/.ivy2`, the first build downloads them):

   ```bash
   cd ~/GraphChecker-solr
   tools/onlift.sh -g 8 experiments/solr/prepare-trees.sh > $GC_BULK/prepare-solr.log 2>&1
   ```

   `prepare-trees.sh` clones the fork's `graphchecker/solr-checks` into `$GC_TREES/lucene-solr-checks` (a directory
   already there is only built), builds solr-core and its tests (solrj, the test framework) with Ant on Java 8 against
   the checkout's jar (`experiments/solr/build.sh`), and runs every case's workload once natively under its seed
   (`experiments/solr/system.sh` `solr_seed`), one Ant run each: a case's classpath is read off its workload's junit4
   report. The log has one line per workload, `PASSED`, `FAILED` (natively; its report is still its classpath) or
   `MISSING` (the script fails). The tree's hooks call the engine's `MessageDoors` (the view publication:
   `publishing`, `refreshStarting`, `refreshEnded`) and `Sessions` (the expirer a planted
   SessionExpired calls, `CausynthSolrCluster#expire`), so it is built against, and runs on, the jar of the same
   `system/solr` checkout. On `gc/solr-zktrace2` (12d23091d1, 2026-10-16: `gc/solr-zktrace` 8fde6b812c -- final9 plus
   SolrZkClient's store-read door and the watcher's path and type -- plus the test client's live nodes in node order and
   an unbatched Overseer's queue removal in its message's own turn; engine system/solr 19ae623a7) all 17 workloads of the 20 cases passed (05 and 07
   share `AddReplicaTest#testAddMultipleReplicas`; 10, 39 and 40 `TimeRoutedAliasUpdateProcessorTest#test`), 3-62 s
   each, about 17 minutes for the workloads after the build, and `bash experiments/lib/run.sh
   experiments/solr/<case dir> <arg> validate` found every case's configuration valid. Checked again from a fresh clone on
   2026-10-19 (`system/solr` 980b76e80 from GitHub, the fork's branch into an empty `GC_TREES`;
   `/bigtemp/vnr3ne/analysis/solr-2026-10-18/final9/fork-check6.sh`, run through `tools/onlift.sh` -- a bare ssh shell
   has no `mvn` on its PATH): the build, 17 of 17 workloads PASSED, 20 of 20 cases valid, and solr-adhoc-38 ran from
   that clone through SEED, PLAN, INSTRUMENT, REPLAY and 64 rounds of EXPLORE (stopped after 45 min; its witness, a
   timing-dependent fatal, did not recur in that run). After a change to the tree, `SKIP_TREE_BUILD=1 experiments/solr/build.sh
   $GC_TREES/lucene-solr-checks F0993D5343E20BA4 '<Class>#<method>'` runs one workload; never build a tree a run
   reads.

4. **The 20 cases**, each alone on the cluster with its budget (05, 07 and 14 take the longest; the times of the last
   rounds are STATUS "Solr checks"):

   ```bash
   export GC_OUT=$GC_BULK/gc-out/repro-solr CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/solr/j2sdk-image
   (setsid nohup tools/rounds/run-series.sh S1 experiments/solr/solr-cases.tsv system/solr=$HOME/GraphChecker-solr \
     > $GC_OUT/series-S1.out 2>&1 < /dev/null &)
   ```

   One case alone: `CASE_TIMEOUT_SECONDS=14400 tools/rounds/launch-run.sh ~/GraphChecker-solr solr-18406 S1-18406`
   (the same `GC_OUT` and image). Many at once: `tools/adhoc/sweep.sh` with `CASE_TIMEOUT_SECONDS=21600`
   ([handover/OPERATIONS.md](handover/OPERATIONS.md) §4).

5. **Reading them**, as §5: `tools/rounds/round-verify.sh S1`. A bug check reproduces when it ends `SAT_CANDIDATE`
   (confirmed by a replay, reproduced natively: `final/reproduce.json`); a study check when its `.smt` is right, SAT
   confirmed or UNSAT at its fixed point with no `BOUNDED`/`UNBOUND` (each case's row: [STATUS.md](STATUS.md) "Solr
   checks"; the checking method and its traps: [handover/CHECKING.md](handover/CHECKING.md)).

## 7. The HBase cases

The 22 HBase cases ([`experiments/hbase/hbase-cases.tsv`](../experiments/hbase/hbase-cases.tsv): case, branch, budget;
each check's target, workload and state: [checks/HBASE.md](checks/HBASE.md) §E) run on GraphChecker's `system/hbase`
and one HBase tree, the branch `graphchecker/hbase-checks` of the public fork `https://github.com/JHSUYU/hbase.git`
(tree `hbase-checks`, [`experiments/hbase/trees.tsv`](../experiments/hbase/trees.tsv)): Apache HBase master
`1790942bb2` backported to Java 8, with the adapter, every case's target marker and the workloads of the tree's own.
Every HBase case explores at world depth 0 (`CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` in both `case.sh` files), as Solr's
final round did: a flip is asked from the recording's paths only (the engine's default, 3, re-asks the same arms in
every world: STATE §S of the Solr round, TODO "Solr: after SGF9" item 5). A case that needs k counterfactuals gets
depth k on its own `case.sh` line (RULES: several counterfactuals are fine): hbase-adhoc-34 runs at depth 1.
No HDFS: every workload's mini cluster runs on the local filesystem (STATUS "Per-system surface", HBase, "tree:
cluster and bounds").

1. **GraphChecker.** As §6.1, on the branch `system/hbase` (`~/GraphChecker-hbase`).

2. **The image.** Built as the Solr image (§6.2), from `system/hbase`'s VM sources (`system/solr`'s plus the held enum
   constant named of its class and no silent enum compare, VM.md §2/§4; the Solr image lacks them); on the cluster
   `/bigtemp/vnr3ne/vm-force12/j2sdk-image` (its `SOURCE.txt` and `smoke.log` beside it):

   ```bash
   ssh <host> 'git clone -q -b system/hbase git@github.com:JHSUYU/GraphChecker.git /localtmp/$USER/gc-vm-hbase &&
     /localtmp/$USER/gc-vm-hbase/tools/vm/build-image.sh <GC_BULK>/vm/hbase'
   ```

   `$GC_BULK/vm/hbase/j2sdk-image` is `CAUSYNTH_CUSTOM_JDK_HOME` for every HBase run.

3. **The tree.** Maven and JDK 8 (§0); the first build downloads the tree's dependencies into its own repository:

   ```bash
   cd ~/GraphChecker-hbase
   tools/onlift.sh -g 8 experiments/hbase/prepare-trees.sh > $GC_BULK/prepare-hbase.log 2>&1
   ```

   `prepare-trees.sh` clones the fork's `graphchecker/hbase-checks` into `$GC_TREES/hbase-checks` (a directory already
   there is only built), installs the checkout's plain jar into the tree's Maven repository (`HBASE_MAVEN_REPO`, by
   default one named by the tree's path under `$GC_M2`, e.g. `$GC_M2/hbase_bigtemp_vnr3ne_wt_hbase-checks`, so no two
   trees share one; `tools/onlift.sh` passes no environment, so give it inside the command, `env
   HBASE_MAVEN_REPO=...`); the tree compiles against GraphChecker's `MessageDoors` and `Sessions`, a provided dependency,
   so it runs on the jar of the same checkout), builds hbase-server and every module of a workload with what they
   depend on (`experiments/hbase/build.sh`), and runs every case's workload once natively by surefire, with
   `causynth.cluster.automatic` and the case's window: a case's classpath is read off its workload's surefire report.
   The log has one line per workload, `PASSED`, `FAILED` (natively; its report is still its classpath) or `MISSING`
   (the script fails). After a change to the tree, `SKIP_TREE_BUILD=1 experiments/hbase/build.sh
   $GC_TREES/hbase-checks '<Class>#<method>[@startup]'` runs one workload; never build a tree a run reads.

4. **The cases**, each alone on the cluster with its budget:

   ```bash
   export GC_OUT=$GC_BULK/gc-out/repro-hbase CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/hbase/j2sdk-image
   (setsid nohup tools/rounds/run-series.sh B1 experiments/hbase/hbase-cases.tsv system/hbase=$HOME/GraphChecker-hbase \
     > $GC_OUT/series-B1.out 2>&1 < /dev/null &)
   ```

   One case alone: `CASE_TIMEOUT_SECONDS=14400 tools/rounds/launch-run.sh ~/GraphChecker-hbase hbase-adhoc-15 B1-15`
   (the same `GC_OUT` and image).

5. **Reading them**, as §6.5: a bug check reproduces when it ends `SAT_CANDIDATE` (confirmed, reproduced natively); a
   study check when its `.smt` is right, SAT confirmed or UNSAT at its fixed point.

## 8. The ZooKeeper cases

The 16 ZooKeeper cases ([`experiments/zookeeper/zookeeper-cases.tsv`](../experiments/zookeeper/zookeeper-cases.tsv):
case, branch, budget; each check's target, workload and state: [checks/ZOOKEEPER.md](checks/ZOOKEEPER.md) §E; the
final series' `.smt`, claims and time table: [`results/zookeeper/`](../results/zookeeper/README.md)) need two branches:
- **the code:** GraphChecker's `system/zookeeper` (the engine, every case's settings, the VM sources);
- **the adapter:** the branch `graphchecker/zookeeper-checks` of the public fork `https://github.com/JHSUYU/zookeeper.git`
  (tree `zookeeper-checks`, [`experiments/zookeeper/trees.tsv`](../experiments/zookeeper/trees.tsv)): Apache ZooKeeper
  master `eab165995` on Java 8, with ZOOKEEPER-5094 and ZOOKEEPER-5088 unfixed (their fixes, PR 2459 and PR 2454, are
  the fork's branches `fix-trunc-sync-shutdown-state` and `fix/observer-master-pending-proposals`), plus the adapter
  (the automatic ClientBase and quorum cluster `CausynthZkCluster`, client requests and replies and the quorum's
  packets as messages `CausynthZk`, the named workarounds of STATUS "Per-system surface", ZooKeeper column), every
  case's target marker and the workloads of the tree's own.

1. **GraphChecker.** As §6.1, on the branch `system/zookeeper`:

   ```bash
   git clone -q --no-checkout -b system/zookeeper git@github.com:JHSUYU/GraphChecker.git ~/GraphChecker-zookeeper
   git -C ~/GraphChecker-zookeeper sparse-checkout set --no-cone '/*' '!/third_party/'
   git -C ~/GraphChecker-zookeeper checkout -q system/zookeeper
   (cd ~/GraphChecker-zookeeper && tools/onlift.sh -g 6 mvn -q package -DskipTests)
   source ~/GraphChecker-zookeeper/tools/lib/gc-env.sh
   ```

2. **The image.** Built as the Solr image (§6.2), from `system/zookeeper`'s VM sources (`system/hbase`'s plus a
   compare-and-swap's concrete expected value being the word its caller passed, 3d1c9a7b0; the HBase image lacks it); on
   the cluster `/bigtemp/vnr3ne/vm-force13/j2sdk-image`:

   ```bash
   ssh <host> 'git clone -q -b system/zookeeper git@github.com:JHSUYU/GraphChecker.git /localtmp/$USER/gc-vm-zk &&
     /localtmp/$USER/gc-vm-zk/tools/vm/build-image.sh <GC_BULK>/vm/zookeeper'
   ```

   `$GC_BULK/vm/zookeeper/j2sdk-image` is `CAUSYNTH_CUSTOM_JDK_HOME` for every ZooKeeper run.

3. **The tree.** Maven and JDK 8 (§0); the first build downloads the tree's dependencies into its own repository:

   ```bash
   cd ~/GraphChecker-zookeeper
   tools/onlift.sh -g 8 experiments/zookeeper/prepare-trees.sh > $GC_BULK/prepare-zookeeper.log 2>&1
   ```

   `prepare-trees.sh` clones the fork's `graphchecker/zookeeper-checks` into `$GC_TREES/zookeeper-checks` (a directory
   already there is only built), installs the checkout's jar into the tree's Maven repository (`ZOOKEEPER_MAVEN_REPO`,
   by default `$GC_M2/zookeeper<the tree's path, / as _>`; `tools/onlift.sh` passes no environment, so give it inside
   the command, `env ZOOKEEPER_MAVEN_REPO=...`): the tree compiles against GraphChecker's `MessageDoors` and
   `Sessions`, so it runs on the jar of the same checkout. Then it installs each workload's module with what it needs
   and runs every case's workload once natively by surefire as an automatic cluster (`causynth.cluster.automatic`): a
   case's classpath is read off its workload's surefire report. The log has one line per case, `PASSED` or `FAILED`
   (the script then fails). After a change to the tree, `SKIP_GRAPHCHECKER_INSTALL=1 SKIP_TREE_INSTALL=1
   MAVEN_REPO_LOCAL=<repo> experiments/zookeeper/build.sh $GC_TREES/zookeeper-checks <module> <class> <method>` runs
   one workload; never build a tree a run reads. Checked from a fresh clone on 2026-10-22 (`system/zookeeper` 6cff2496c
   from GitHub, the fork's branch into an empty `GC_TREES` and an empty Maven repository;
   `/bigtemp/vnr3ne/analysis/zookeeper-2026-10-21/lead/fresh/fresh-check.sh`, run through `tools/onlift.sh` -- a bare
   ssh shell has no `mvn` on its PATH): the build, 16 of 16 workloads PASSED (20-156 s each, 10 minutes with the
   downloads), 16 of 16 cases valid (`bash experiments/lib/run.sh <case dir> <case> validate`); the image built from
   the same branch (step 2: 3.5 minutes on lift15, smoke suite passed); and three cases ran from that clone and image to
   the final series' verdicts: quota-init SAT, 10/10 natively, 261 s; observer-master SAT, 5/10 natively, 544 s;
   zk-adhoc-13 UNSAT_CLOSED, 231 s (`/bigtemp/vnr3ne/gc-out/zookeeper-fresh`).

4. **The cases**, each alone on the cluster with its budget:

   ```bash
   export GC_OUT=$GC_BULK/gc-out/repro-zookeeper CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/zookeeper/j2sdk-image
   mkdir -p $GC_OUT
   (setsid nohup tools/rounds/run-series.sh Z1 experiments/zookeeper/zookeeper-cases.tsv \
     system/zookeeper=$HOME/GraphChecker-zookeeper > $GC_OUT/series-Z1.out 2>&1 < /dev/null &)
   ```

   One case alone: `CASE_TIMEOUT_SECONDS=14400 tools/rounds/launch-run.sh ~/GraphChecker-zookeeper zk-bugs-quota-init
   Z1-bugs-quota-init` (the same `GC_OUT` and image). Our final series kept a concurrent run when it took under 30 minutes
   and ran every longer case again alone on 14 hosts: 4.8 h in all, 4-60 min a case (`results/zookeeper/README.md`).

5. **Reading them**, as §5: `tools/rounds/round-verify.sh Z1` and `tools/rounds/series-stats.py Z1` (claim, time
   breakdown, closure regions per case). The final series' verdicts (`results/zookeeper/index.tsv`, one reading per case
   in its README): `SAT_CANDIDATE` (confirmed by a replay, reproduced natively: `final/reproduce.json`) for quota-init,
   election-offer, container-reuse, retry-seq-quota, observer-master (ZOOKEEPER-5088) and zk-adhoc-03;
   `SAT_UNCONFIRMED` for zk-adhoc-01 and -02 (every claim refuted by CONFIRM: the false-positive filter);
   `UNSAT_CLOSED` for trunc-sync (ZOOKEEPER-5094, not detected) and zk-adhoc-04, -06, -07, -10, -11, -12, -13 (10 and 11
   vacuous by construction: `tools/analysis/vacuity.py --latest --detail <run>`). A run's
   `out/<case>/schedule/final/candidate.smt2` compares with `results/zookeeper/<case>.smt2.gz`;
   `tools/analysis/smt-legend.py <run>/out/<case>` names every symbol. Replays race, so wall times vary run to run, and
   a native reproduction is a count (observer-master and 03 reproduced 4 of 10 natively, the others 10 of 10).

6. **On CloudLab** (branch `system/zookeeper-cloudlab`, five nodes, OPERATIONS §11). Make the cluster with
   `BULK_SUBNET=10.10.1.0/24 tools/cloudlab/setup-nodes.sh` (packages, disks, NFS `/bulk`, JDK 8, `~/.m2`, z3), then:

   ```bash
   git clone -q git@github.com:JHSUYU/GraphChecker.git /bulk/GraphChecker
   git -C /bulk/GraphChecker worktree add /bulk/wt/gc-zk-cloudlab system/zookeeper-cloudlab   # full: the VM sources
   (cd /bulk/wt/gc-zk-cloudlab && mvn -q package -DskipTests)
   ssh node4 'cd /bulk/wt/gc-zk-cloudlab && tools/vm/build-image-docker.sh /bulk/vm/zookeeper'   # ~4 min, smoke suite
   git clone -q -b graphchecker/zookeeper-checks git@github.com:JHSUYU/zookeeper.git /bulk/zookeeper
   git -C /bulk/zookeeper worktree add --detach /bulk/trees/zk3/zookeeper-checks graphchecker/zookeeper-checks
   ssh node2 'cd /bulk/wt/gc-zk-cloudlab && env PATH=/usr/lib/maven/bin:$PATH GC_TREES=/bulk/trees/zk3 \
     ZOOKEEPER_MAVEN_REPO=/bulk/m2/zk3/zookeeper-checks bash experiments/zookeeper/prepare-trees.sh'   # 16 PASSED
   bash /bulk/wt/gc-zk-cloudlab/tools/lib/worktree-add.sh /bulk/gc-run/zk $(git -C /bulk/wt/gc-zk-cloudlab rev-parse HEAD) --detach
   ssh node1 'cd /bulk/gc-run/zk && mvn -q -o package -DskipTests'
   cd /bulk/gc-run/zk && (setsid nohup env GC_OUT=/bulk/gc-out/zk GC_TREES=/bulk/trees/zk3 \
     CAUSYNTH_CUSTOM_JDK_HOME=/bulk/vm/zookeeper/j2sdk-image PRUNE=0 tools/rounds/run-pool.sh Z1 \
     experiments/zookeeper/zookeeper-cases.tsv system/zookeeper=/bulk/gc-run/zk > /bulk/gc-out/zk-pool.out 2>&1 < /dev/null &)
   ```

   `run-pool.sh` runs every case at once over the five nodes as their cores allow (PARALLEL §8); read the round with
   `results/zookeeper/final-stats.py --order Z1 --cases experiments/zookeeper/zookeeper-cases.tsv --out /bulk/gc-out/zk`.
   The final CloudLab rounds and their table are `results/zookeeper/README.md`.
