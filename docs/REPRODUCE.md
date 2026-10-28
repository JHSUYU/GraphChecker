# Reproducing the checks from GitHub: HBase (§7) and Solr (§6); HDFS and ZooKeeper on their own branches

Everything a run needs is on GitHub: GraphChecker's branch of the system (the engine, the case settings, the VM
sources) and the system's fork, whose `graphchecker/*` branch is the tree under test (the adapter, the target markers,
the workloads). Clone the two, check out those branches, and the section of the system runs its cases. Nothing on the
cluster's disks is assumed besides the operating system packages below (§0).

| repository | branch | what it holds |
| --- | --- | --- |
| `git@github.com:JHSUYU/GraphChecker.git` (private) | `system/hbase` | the 22 HBase cases (§7), `results/hbase/` |
| | `system/solr` | the 20 Solr cases (§6), `results/solr/` |
| | `system/hdfs-liftlab` | the HDFS cases (its own REPRODUCE §0-§5), `results/hdfs/` |
| | `system/zookeeper` | the 16 ZooKeeper cases (its own REPRODUCE §8), `results/zookeeper/` |
| | `system/<x>-buggy-detect` (x = hdfs, hbase, zookeeper, solr) | `system/<x>` (HDFS: `system/hdfs-liftlab`) plus the old bugs put back on today's tree, each a case `experiments/<sys>/<sys>-buggy-<jira>/` (that branch's REPRODUCE) |
| `https://github.com/JHSUYU/hbase.git` (public fork) | `graphchecker/hbase-checks` | the HBase tree (`hbase-checks`) |
| | `graphchecker/hbase-bug-<jira>` | `graphchecker/hbase-checks` with one old bug put back (`system/hbase-buggy-detect`) |
| `https://github.com/JHSUYU/solr.git` (public fork) | `graphchecker/solr-checks` | the Solr tree (`lucene-solr-checks`) |
| `https://github.com/JHSUYU/hadoop.git`, `zookeeper.git` (public forks) | `graphchecker/*` | the HDFS and ZooKeeper trees (their branches' REPRODUCE) |

`system/hdfs` and `system/hdfs1`, the former HDFS bodies on which series EX1 ran the 46 cases, stay on the remote as
history; `system/hdfs-liftlab` replaces them. The CloudLab runs of 2026-10-24..28 are kept only as the tags
`archive/system/<x>-cloudlab`.

## 0. The machines

- Linux x86_64 hosts (Ubuntu 22.04 here: liftlab, `lift02`-`lift15`, 48 cores and 30 GB each; `lift11` is the control
  host where the sessions run, out of the workers; `lift07` does not answer since 2026-10-23, so a run's workers are the
  other twelve: `LIFTS="lift02 lift03 lift04 lift05 lift06 lift08 lift09 lift10 lift12 lift13 lift14 lift15"`; lift02
  and lift03 cannot reach lift15 over ssh, so a run they head with lift15 among its workers is refused in PREFLIGHT:
  `launch-round.sh` heads cases on any host of `LIFTS` but lift11, so give it `LIFTS` without lift15, or without lift02
  and lift03). One host works; a case then takes several times longer.
- One filesystem mounted at the same path on every host (`GC_BULK`, here `/bigtemp/vnr3ne`), the home directory shared
  too, passwordless `ssh -o BatchMode=yes` between the hosts, and a local scratch directory `/localtmp/$USER` on each.
- Packages: `openjdk-8-jdk` (at `/usr/lib/jvm/java-8-openjdk-amd64`), `maven` (`/usr/lib/maven/bin`), `git`,
  `python3`, `rsync`; Apache Ant for the Solr tree (§6). For the VM build, on one host: `gcc-6`/`g++-6` and
  `libffi-dev libfreetype6-dev libcups2-dev libasound2-dev libx11-dev libxext-dev libxt-dev libxrender-dev libxtst-dev
  zip unzip` (or Docker: §2).
- z3 4.14.1: unpack `https://github.com/Z3Prover/z3/releases/download/z3-4.14.1/z3-4.14.1-x64-glibc-2.35.zip` and put
  `bin/z3` at `~/.local/bin/z3` (or name it as `Z3_BIN`).

Where things go is stated once, in [`tools/lib/gc-env.sh`](../tools/lib/gc-env.sh): `GC_BULK` (the shared storage),
`GC_OUT` (run outputs), `GC_TREES` (the system trees), `GC_M2` (their Maven repositories), `Z3_BIN`, `LIFTS` (the
hosts; its default lists all of lift02-15, so export the workers) and `CAUSYNTH_HOST_MAX_USED_PCT` (70: no start may
leave a host fuller). On another cluster, edit those defaults in that file on the checkout. A value exported in the
shell that starts a run also works: every hop of the run passes them on (`gc_env_words`); `tools/onlift.sh` does not,
so give it `env NAME=value` in its command. The commands from §2 on use these variables: `source
<checkout>/tools/lib/gc-env.sh` in the shell first.

## 1. GraphChecker

A sparse clone of the system's branch (§6.1, §7.1 give the commands): the checkout leaves out `third_party/` (the VM's
47,000 source files, which no build or run reads; §2 clones them apart). `tools/onlift.sh` runs a command in the
current directory on the host of `LIFTS` with the most room, with Java 8 and Maven on its path; use it for every build.
The first build downloads the dependencies into `~/.m2`. The jars (`target/GraphChecker-1.0-SNAPSHOT{,-jar-with-dependencies}.jar`)
are what a run reads; leave a checkout alone while a run uses it.

## 2. The concolic VM image

On a host with gcc-6, a full clone of the branch on its local disk (§6.2, §7.2 give the commands):
`tools/vm/build-image.sh <GC_BULK>/vm/<system>` builds a full OpenJDK 8 (Zero, release, `-DENABLE_CONCOLIC`) on the
host's local disk, then the causynth smoke suite on it: `$GC_BULK/vm/<system>/j2sdk-image` is the image
(`CAUSYNTH_CUSTOM_JDK_HOME`), `SOURCE.txt` the commit it was built from, `smoke.log` the suite (`SMOKE_EXIT=0`, 24 `OK`
lines). About 3 minutes at `JOBS=40`. A host without gcc-6:
`FULL_JDK=true third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh` (Ubuntu 18.04
container), then copy its `build/linux-x86_64-normal-zero-release/images/j2sdk-image`.

## 3. The HDFS cases

On `system/hdfs-liftlab` with the Hadoop fork's `graphchecker/hdfs-checks` (and `-adhoc21`, `hdfs-11741`): that branch's
REPRODUCE §0-§5 builds its trees and runs them (`experiments/hadoop/hdfs-cases.tsv` there).

## 4. Running the cases

One case, from a checkout of its branch: `tools/rounds/launch-run.sh <checkout> <case> <tag>` with `GC_OUT` and
`CAUSYNTH_CUSTOM_JDK_HOME` exported and `CASE_TIMEOUT_SECONDS` the case's budget (its system's `*-cases.tsv`). The run
is a session of its own (`setsid`) and holds the shell until the case ends (start it as `(setsid nohup ... > <log> 2>&1
< /dev/null &)` to leave it running); it writes `$GC_OUT/accept-<tag>/` and ends with the second line of its
`summary.tsv`. Its obligations go to every host of `LIFTS`. `tools/rounds/stop-run.sh <tag>` (with the same `GC_OUT`)
stops it.

Every case of a system, each alone on the cluster: `tools/rounds/run-series.sh <ROUND> <cases.tsv> <branch>=<checkout>`
runs each case from the checkout of its branch with its budget; naming case ids after the checkouts runs only those. A
stopped series resumes by the same command (finished cases are skipped); `touch $GC_OUT/series-<ROUND>.STOP` ends it
before its next case. Many cases at once instead: `tools/adhoc/sweep.sh` or `tools/rounds/launch-round.sh`
([handover/OPERATIONS.md](handover/OPERATIONS.md) §4).

## 5. Reading the results

```bash
tools/rounds/round-verify.sh <ROUND>      # how each EXPLORE ended, z3 on the file, gaps, roots
tools/rounds/series-stats.py <ROUND>      # claim, time breakdown, closure regions per case
```

The report's `PASS` checks a named bug's declared mechanism (`experiments/accept/report.py` `EXPECTED_MECHANISM`); a
study check declares none, so its report says `FAIL` whatever its claim: the claim and round-verify decide, as
[handover/CHECKING.md](handover/CHECKING.md) §1 says. `tools/analysis/smt-legend.py <run>/out/<case>` names every symbol
of a formula; `tools/analysis/vacuity.py --latest --detail <run>` says whether an UNSAT is vacuous. Wall times vary run
to run (replays race), and a native reproduction is a count.

## 6. The Solr cases

The 20 Solr cases ([`experiments/solr/solr-cases.tsv`](../experiments/solr/solr-cases.tsv): case, branch, budget) run
on GraphChecker's `system/solr` and one Solr 8.11 tree, the branch `graphchecker/solr-checks` of the public fork
`https://github.com/JHSUYU/solr.git` (tree `lucene-solr-checks`,
[`experiments/solr/trees.tsv`](../experiments/solr/trees.tsv)): Apache Lucene/Solr `branch_8_11` (8.11.4, `faca81b`)
with the adapter, every case's target marker and the bug checks' workloads.

1. **GraphChecker.** On the branch `system/solr` (§1):

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

3. **The tree.** Besides Maven it needs Apache Ant with Ivy (`ant ivy-bootstrap` once per host; Ant resolves
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
every world: Solr's final round SGF9 measured it). A case that needs k counterfactuals gets
depth k on its own `case.sh` line (RULES: several counterfactuals are fine): hbase-adhoc-34 runs at depth 1.
No HDFS: every workload's mini cluster runs on the local filesystem (STATUS "Per-system surface", HBase, "tree:
cluster and bounds").

1. **GraphChecker.** As §6.1, on the branch `system/hbase`:

   ```bash
   git clone -q --no-checkout -b system/hbase git@github.com:JHSUYU/GraphChecker.git ~/GraphChecker-hbase
   git -C ~/GraphChecker-hbase sparse-checkout set --no-cone '/*' '!/third_party/'
   git -C ~/GraphChecker-hbase checkout -q system/hbase
   (cd ~/GraphChecker-hbase && tools/onlift.sh -g 6 mvn -q package -DskipTests)
   source ~/GraphChecker-hbase/tools/lib/gc-env.sh
   ```

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
   $GC_TREES/hbase-checks '<Class>#<method>[@startup]'` runs one workload; never build a tree a run reads. Checked from
   a fresh clone on 2026-10-22 (`system/hbase` 789fcd66d from GitHub, the fork's branch into an empty `GC_TREES` and an
   empty Maven repository; `/bigtemp/vnr3ne/analysis/hbase-2026-10-20/fresh/fresh-check.sh`, run through
   `tools/onlift.sh` -- a bare ssh shell has no `mvn` on its PATH): the build, 18 of 18 workloads PASSED (the 22 cases
   share them; 17 minutes with the downloads), 22 of 22 cases valid (`bash experiments/lib/run.sh <case dir> <case>
   validate`), and hbase-bugs-backup-lock-reply-lost ran from that clone to its final verdict: SAT, 10/10 natively,
   control 0/10, 575 s (`/bigtemp/vnr3ne/gc-out/hbase-fresh`; the image was vm-force12, built from the same VM
   sources).

4. **The cases**, each alone on the cluster with its budget:

   ```bash
   export GC_OUT=$GC_BULK/gc-out/repro-hbase CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/hbase/j2sdk-image
   mkdir -p $GC_OUT
   (setsid nohup tools/rounds/run-series.sh B1 experiments/hbase/hbase-cases.tsv system/hbase=$HOME/GraphChecker-hbase \
     > $GC_OUT/series-B1.out 2>&1 < /dev/null &)
   ```

   One case alone: `CASE_TIMEOUT_SECONDS=14400 tools/rounds/launch-run.sh ~/GraphChecker-hbase hbase-adhoc-15 B1-15`
   (the same `GC_OUT` and image). Our final series kept a concurrent run when it took under 30 minutes and ran every
   longer case again alone on 14 hosts: 15.0 h in all, 11-211 min a case (`results/hbase/README.md`).

5. **Reading them**, as §6.5: `tools/rounds/round-verify.sh B1` and `tools/rounds/series-stats.py B1`. A bug check
   reproduces when it ends `SAT_CANDIDATE` (confirmed, reproduced natively); a study check when its `.smt` is right, SAT
   confirmed or UNSAT at its fixed point. The final series' verdicts (`results/hbase/index.tsv`, one reading per case in
   its README): `SAT_CANDIDATE` for the owner's five bugs (hbase-adhoc-04 = HBASE-30484, hbase-adhoc-22 = HBASE-30483,
   backup-lock-reply-lost, ns-rsgroup-removal: 10/10 natively; master-active-time 8/10) and the study checks 34 (9/10)
   and 24 (confirmed in the VM, no native plant); `SAT_UNCONFIRMED` for 07, 08, 10, 11, 12, 14, 15 (every claim refuted
   by CONFIRM: the named bound, TODO HBase 15); `UNSAT_CLOSED` for 19, 20, 21, 28, 35, 37 (all but 21 vacuous by
   construction: `tools/analysis/vacuity.py --latest --detail <run>`); `RUN_DEFECT` for 13 (its formula vacuous, TODO
   HBase 19) and 31 (vacuous; its RUN_DEFECT was stale generation gaps, fixed after the run). A run's
   `out/<case>/schedule/final/candidate.smt2` compares with `results/hbase/<case>.smt2.gz`; replays race, so wall times
   vary run to run and a native reproduction is a count.
