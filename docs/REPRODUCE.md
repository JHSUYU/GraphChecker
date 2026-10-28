# Reproducing the Solr checks from GitHub (`system/solr`)

Everything a run of the 20 Solr cases needs is on GitHub: this branch (the engine, the case settings, the VM sources)
and the Solr fork's `graphchecker/solr-checks` (the tree under test). Nothing on the cluster's disks is assumed besides
the operating system packages below (§0).

| repository | branch | what it holds |
| --- | --- | --- |
| `git@github.com:JHSUYU/GraphChecker.git` (private) | `system/solr` | the engine, the 20 cases ([`experiments/solr/solr-cases.tsv`](../experiments/solr/solr-cases.tsv): case, branch, budget), the VM sources, every case's final `.smt` and time row ([`results/solr/`](../results/solr/README.md)) |
| `https://github.com/JHSUYU/solr.git` (public fork) | `graphchecker/solr-checks` | the Solr 8.11 tree of every case (`lucene-solr-checks`, [`experiments/solr/trees.tsv`](../experiments/solr/trees.tsv)): Apache Lucene/Solr `branch_8_11` (8.11.4, `faca81b`) with the adapter, every case's target marker and the bug checks' workloads |

The other systems reproduce from their own branches' `docs/REPRODUCE.md` (README "Branches"): HDFS from
`system/hdfs-liftlab`, HBase from `system/hbase`, ZooKeeper from `system/zookeeper`, the old Solr bugs put back by hand
from `system/solr-buggy-detect`. The HDFS cases this branch carries from `system/hdfs1` are reproduced by
`system/hdfs-liftlab`.

## 0. The machines

- Linux x86_64 hosts (Ubuntu 22.04 here: liftlab, `lift02`-`lift15`, 48 cores and 30 GB each; lift11 is the control host
  where the sessions run, never a worker; lift07 does not answer since 2026-10-23, so a run's workers are the other 12).
  One host works; a case then takes several times longer.
- One filesystem mounted at the same path on every host (`GC_BULK`, here `/bigtemp/vnr3ne`), the home directory shared
  too, passwordless `ssh -o BatchMode=yes` between the hosts, and a local scratch directory `/localtmp/$USER` on each.
- Packages: `openjdk-8-jdk` (at `/usr/lib/jvm/java-8-openjdk-amd64`), `maven` (`/usr/lib/maven/bin`), Apache Ant with Ivy
  (`ant ivy-bootstrap` once per host), `git`, `python3`, `rsync` (Maven and Ant here only on lift02-06 and lift08-10:
  build there). For the VM build, on one host: `gcc-6`/`g++-6` and `libffi-dev libfreetype6-dev libcups2-dev
  libasound2-dev libx11-dev libxext-dev libxt-dev libxrender-dev libxtst-dev zip unzip` (here lift15; or Docker: §2).
- z3 4.14.1: unpack `https://github.com/Z3Prover/z3/releases/download/z3-4.14.1/z3-4.14.1-x64-glibc-2.35.zip` and put
  `bin/z3` at `~/.local/bin/z3` (or name it as `Z3_BIN`).

Where things go is stated once, in [`tools/lib/gc-env.sh`](../tools/lib/gc-env.sh): `GC_BULK` (the shared storage),
`GC_OUT` (run outputs), `GC_TREES` (the system trees), `GC_M2` (their Maven repositories), `Z3_BIN`, `LIFTS` (the
hosts; its default names every lift) and `CAUSYNTH_HOST_MAX_USED_PCT` (70: no start may leave a host's memory fuller).
On another cluster, edit those defaults in that file. A value exported in the shell that starts a run also works: every
hop of the run passes them on (`gc_env_words`); `tools/onlift.sh` does not, so give it `env NAME=value` in its command.
The commands from §2 on use these variables: `source ~/GraphChecker-solr/tools/lib/gc-env.sh` in the shell first, and
export `LIFTS` without the control host and any host that does not answer (here: `export LIFTS="lift02 lift03 lift04
lift05 lift06 lift08 lift09 lift10 lift12 lift13 lift14 lift15"`). `tools/onlift.sh` runs a command in the current
directory on the host of `LIFTS` with the most room, with Java 8 and Maven on its path; give it the hosts with Maven and
Ant (`LIFTS="lift04 lift05 lift06 lift08 lift09 lift10" tools/onlift.sh ...`) for every build.

## 1. GraphChecker

```bash
git clone -q --no-checkout -b system/solr git@github.com:JHSUYU/GraphChecker.git ~/GraphChecker-solr
git -C ~/GraphChecker-solr sparse-checkout set --no-cone '/*' '!/third_party/'
git -C ~/GraphChecker-solr checkout -q system/solr
(cd ~/GraphChecker-solr && tools/onlift.sh -g 6 mvn -q package -DskipTests)
source ~/GraphChecker-solr/tools/lib/gc-env.sh
```

The checkout leaves out `third_party/` (the VM's 47,000 source files, which no build or run reads; §2 clones them
apart). The first build downloads the dependencies into `~/.m2`. The jars
(`target/GraphChecker-1.0-SNAPSHOT{,-jar-with-dependencies}.jar`) are what a run reads; leave a checkout alone while a
run uses it.

## 2. The concolic VM image

The image is built from `system/solr`'s own VM sources, on a host with gcc-6, from a full clone on its local disk. They
carry the forced replay's native, `System.forceNextConcolicBranch`, and the one-channel read-out,
`System.readOutTrackedLocations`: the runtime refuses an image without it by name -- a seed replay ends "Concolic task
plan requires current custom VM broker capabilities: [readOutTrackedLocations]". On liftlab the image is
`/bigtemp/vnr3ne/vm-force10/j2sdk-image`, built from these sources.

```bash
ssh <host> 'git clone -q -b system/solr git@github.com:JHSUYU/GraphChecker.git /localtmp/$USER/gc-vm-solr &&
  /localtmp/$USER/gc-vm-solr/tools/vm/build-image.sh <GC_BULK>/vm/solr'
```

`$GC_BULK/vm/solr/j2sdk-image` is `CAUSYNTH_CUSTOM_JDK_HOME` for every Solr run: a full OpenJDK 8 (Zero, release, `-DENABLE_CONCOLIC`) built on the host's local disk, then the causynth smoke suite on
it: `SOURCE.txt` beside the image is the commit it was built from, `smoke.log` the suite (`SMOKE_EXIT=0`, 24 `OK`
lines); a few minutes. A host without gcc-6: `FULL_JDK=true
third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh` (Ubuntu 18.04 container), then copy
its `build/linux-x86_64-normal-zero-release/images/j2sdk-image`.

## 3. The Solr tree

Ant resolves the tree's libraries into `~/.ivy2` (the first build downloads them):

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

## 4. Running the cases

The 20 cases, each alone on the cluster with its budget (05, 07 and 14 take the longest; each case's time is its row in
`results/solr/README.md`):

```bash
export GC_OUT=$GC_BULK/gc-out/repro-solr CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/solr/j2sdk-image
(setsid nohup tools/rounds/run-series.sh S1 experiments/solr/solr-cases.tsv system/solr=$HOME/GraphChecker-solr \
  > $GC_OUT/series-S1.out 2>&1 < /dev/null &)
```

One case alone: `CASE_TIMEOUT_SECONDS=14400 tools/rounds/launch-run.sh ~/GraphChecker-solr solr-18406 S1-18406`
(the same `GC_OUT` and image; it holds the shell until the case ends, writes `$GC_OUT/accept-S1-18406/` and ends with
the second line of its `summary.tsv`; `tools/rounds/stop-run.sh S1-18406` stops it). A stopped series resumes by the same
command (finished cases are skipped); `touch $GC_OUT/series-S1.STOP` ends it before its next case. Run Solr cases one at
a time for their time, at most 3 at once otherwise: a head step wants ~23 GB, and eight at once starved them (STATE §S).
Many at once: `tools/adhoc/sweep.sh` with `CASE_TIMEOUT_SECONDS=21600` ([handover/OPERATIONS.md](handover/OPERATIONS.md)
§4).

## 5. Reading the results

`tools/rounds/round-verify.sh S1` (how each EXPLORE ended, z3 on the file, gaps, roots) and
`tools/rounds/series-stats.py S1` (claim, time breakdown, closure regions per case); each case's final verdict, `.smt`,
time and regions to compare with are [`results/solr/`](../results/solr/README.md) (each UNSAT read with
`tools/analysis/vacuity.py --latest --detail <run>`). A bug check reproduces when it ends `SAT_CANDIDATE`
(confirmed by a replay, reproduced natively: `final/reproduce.json`); a study check when its `.smt` is right, SAT
confirmed or UNSAT at its fixed point with no `BOUNDED`/`UNBOUND` (each case's row: [STATUS.md](STATUS.md) "Solr
checks"; the checking method and its traps: [handover/CHECKING.md](handover/CHECKING.md)).
