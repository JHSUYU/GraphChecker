# Reproducing the 46 HDFS checks from GitHub

Everything a run of the 46 HDFS cases needs is in two GitHub repositories. Nothing on the cluster's disks is assumed
besides the operating system packages below.

| repository | branch | what it holds |
| --- | --- | --- |
| `git@github.com:JHSUYU/GraphChecker.git` (private) | `system/hdfs` | the locked body: the engine that closed 39 cases (the named bugs but 11741, and 30 study checks) |
| | `system/hdfs1` | the newest body: the other 7 cases (07 11741 21 29 30 39 40), these tools, the VM sources |
| `https://github.com/JHSUYU/hadoop.git` (public fork) | `graphchecker/hdfs-checks` | the HDFS tree of 43 cases (tree `hadoop-hdfs-study-r7`) |
| | `graphchecker/hdfs-checks-adhoc07` | hdfs-adhoc-07's tree (`hadoop-hdfs-study-r8`) |
| | `graphchecker/hdfs-checks-adhoc21` | hdfs-adhoc-21's tree (`hadoop-hdfs-21`) |
| | `graphchecker/hdfs-11741` | hdfs-11741's tree (`hadoop-hdfs-11741-r6`): trunk with HDFS-11741's fix reverted |

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
`GC_OUT` (run outputs), `GC_TREES` (the HDFS trees), `GC_M2` (their Maven repositories), `Z3_BIN`, `LIFTS` (the
hosts) and `CAUSYNTH_HOST_MAX_USED_PCT` (70: no start may leave a host fuller). On another cluster, edit those
defaults in that file on both branches' checkouts: commands reached over ssh read the file, not your shell.

## 1. GraphChecker, both branches

```bash
git clone -b system/hdfs1 git@github.com:JHSUYU/GraphChecker.git ~/GraphChecker-hdfs1
git clone -b system/hdfs  git@github.com:JHSUYU/GraphChecker.git ~/GraphChecker-hdfs
for b in hdfs1 hdfs; do (cd ~/GraphChecker-$b && tools/onlift.sh -g 6 mvn -q package -DskipTests); done
```

`tools/onlift.sh` runs a command in the current directory on the host of `LIFTS` with the most room, with Java 8 and
Maven on its path; use it for every build. The first build downloads the dependencies into `~/.m2`. The three jars
(`target/GraphChecker-1.0-SNAPSHOT{,-jar-with-dependencies,-hadoop-shim}.jar`) are what a run reads; leave a checkout
alone while a run uses it.

## 2. The concolic VM image

```bash
cd ~/GraphChecker-hdfs1 && tools/onlift.sh -h <a host with gcc-6> -g 12 tools/vm/build-image.sh $GC_BULK/vm/hdfs
```

A full OpenJDK 8 (Zero, release, `-DENABLE_CONCOLIC`) built on the host's local disk, then the causynth smoke suite
on it: `$GC_BULK/vm/hdfs/j2sdk-image` is the image (`CAUSYNTH_CUSTOM_JDK_HOME`), `SOURCE.txt` the commit it was built
from, `smoke.log` the suite (`SMOKE_EXIT=0`, 24 `OK` lines). A few minutes at `JOBS=40`. A host without gcc-6:
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
fails). Both GraphChecker branches read these trees: a run puts its own jar ahead of the tree's classpath.

## 4. Running the cases

One case, from the checkout of its branch (the table's `branch` and `budget_s` columns):

```bash
cd ~/GraphChecker-hdfs1
GC_OUT=$GC_BULK/gc-out/repro CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/hdfs/j2sdk-image CASE_TIMEOUT_SECONDS=14400 \
  tools/rounds/launch-run.sh ~/GraphChecker-hdfs1 hdfs-adhoc-29 R1-adhoc-29
```

The run detaches; it writes `$GC_OUT/accept-R1-adhoc-29/` and ends with the second line of its `summary.tsv`. Its
obligations go to every host of `LIFTS`. `tools/rounds/stop-run.sh R1-adhoc-29` stops it.

All 46, each alone on the cluster, as series EX1 ran them:

```bash
cd ~/GraphChecker-hdfs1
(GC_OUT=$GC_BULK/gc-out/repro CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/hdfs/j2sdk-image setsid nohup \
  tools/rounds/run-series.sh R1 ~/GraphChecker-hdfs ~/GraphChecker-hdfs1 > $GC_BULK/series-R1.out 2>&1 < /dev/null &)
```

Each case runs from the checkout of its branch with its budget; naming case ids after the two checkouts runs only
those. The series took 15.2 h on the ten hosts (most cases 10-40 min, 11741 ~45 min, 07 ~3 h); a stopped series
resumes by the same command (finished cases are skipped); `touch $GC_OUT/series-R1.STOP` ends it before its next
case. Many cases at once instead: `tools/adhoc/sweep.sh` ([handover/OPERATIONS.md](handover/OPERATIONS.md) §4).

## 5. Reading the results

```bash
GC_OUT=$GC_BULK/gc-out/repro tools/rounds/round-verify.sh R1      # how each EXPLORE ended, z3 on the file, gaps, roots
GC_OUT=$GC_BULK/gc-out/repro tools/rounds/series-stats.py R1      # claim, time breakdown, closure regions per case
```

A case reproduces when its claim is the table's `ex1_claim`: SAT (`SAT_CANDIDATE`: confirmed by a replay, reproduced
natively) for the ten named bugs and hdfs-adhoc-10 and -12; UNSAT (`UNSAT_CLOSED`: z3 on the exported
`final/candidate.smt2` says unsat, EXPLORE at its fixed point) for the rest; hdfs-adhoc-21 `RUN_DEFECT` (its accepted
residue). The report's `PASS` also checks a named bug's declared mechanism; a study check declares none, so its report
says `FAIL` whatever its claim: the claim and round-verify decide, as [handover/CHECKING.md](handover/CHECKING.md) §1
says. What each `.smt` must contain (its causal
chain, symbols and propagation, read by hand against the HDFS code) is each case's row in
[STATUS.md](STATUS.md) "HDFS checks"; `tools/analysis/smt-legend.py <run>/out/<case>` names every symbol of a formula.
Wall times vary run to run (replays race); the EX1 rows are in [design/PERFORMANCE.md](design/PERFORMANCE.md) §6.
