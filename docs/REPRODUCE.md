# Reproducing the HDFS checks from GitHub (`system/hdfs-liftlab`, §0-§5); the other systems (§6); the old HDFS bugs (§7, `system/hdfs-buggy-detect`)

Everything a run needs is on GitHub: GraphChecker's branch of the system (the engine, the case settings, the VM
sources) and the system's fork, whose `graphchecker/*` branch is the tree under test (the adapter, the target markers,
the workloads). Clone the two, check out those branches, and §1-§5 run the HDFS cases; every other system's recipe is
its own branch's REPRODUCE (§6). Nothing on the cluster's disks is assumed besides the operating system packages below
(§0).

| repository | branch | what it holds |
| --- | --- | --- |
| `git@github.com:JHSUYU/GraphChecker.git` (private) | `system/hdfs-liftlab` | **THE HDFS branch**: every HDFS case on HBase's engine with liftlab's scheduling (§0-§5), `results/hdfs/` |
| | `system/hdfs-buggy-detect` | `system/hdfs-liftlab` plus the old HDFS bugs put back by hand (§7) |
| | `system/solr`, `system/hbase`, `system/zookeeper` | the other systems' cases, each with its `-buggy-detect` branch (§6) |
| `https://github.com/JHSUYU/hadoop.git` (public fork) | `graphchecker/hdfs-checks` | the HDFS tree of every case but hdfs-adhoc-21 and hdfs-11741 (tree `hadoop-hdfs-study-r7`) |
| | `graphchecker/hdfs-checks-adhoc21` | hdfs-adhoc-21's tree (`hadoop-hdfs-21`) |
| | `graphchecker/hdfs-11741` | hdfs-11741's tree (`hadoop-hdfs-11741-r6`): trunk with HDFS-11741's fix reverted |
| | `graphchecker/hdfs-bug-<jira>` | the old-bug trees of `system/hdfs-buggy-detect` (`hadoop-hdfs-bug-<jira>`, §7) |

`system/hdfs-liftlab` replaces the two former HDFS branches, `system/hdfs` (the locked body, 39 cases) and `system/hdfs1`
(the other 7), which stay on the remote for history: their checkouts ran the 46 cases as series EX1 (each case's
`ex1_*` columns in the table below), and the fork's `graphchecker/hdfs-checks-adhoc07` is read only by `system/hdfs1`'s 07.
Every case's branch (`system/hdfs-liftlab`), budget and EX1 result are
[`experiments/hadoop/hdfs-cases.tsv`](../experiments/hadoop/hdfs-cases.tsv); which fork branch each tree is,
[`experiments/hadoop/trees.tsv`](../experiments/hadoop/trees.tsv). The VM sources
(`third_party/OpenJDK-Concolic-Execution-Engine`) are `system/hbase`'s, so the HBase image serves the HDFS cases too.
Every case explores at world depth 0 but hdfs-11741 (2: its witness moves two clocks), as HBase's process has it (each
`case.sh`; hdfs-adhoc-07's former depth 6 was dropped by 94fce7127).

## 0. The machines

- Linux x86_64 hosts (Ubuntu 22.04 here: liftlab, `lift02`-`lift15`, 48 cores and 30 GB each; lift11 is the control host
  where the sessions run, out of the workers; on 2026-10-27 lift07 does not answer, so a run's workers are the other 12).
  One host works; a case then takes several times longer (PERFORMANCE §6 was measured on ten).
- One filesystem mounted at the same path on every host (`GC_BULK`, here `/bigtemp/vnr3ne`), the home directory shared
  too, passwordless `ssh -o BatchMode=yes` between the hosts, and a local scratch directory `/localtmp/$USER` on each.
- Packages: `openjdk-8-jdk` (at `/usr/lib/jvm/java-8-openjdk-amd64`), `maven` (`/usr/lib/maven/bin`), `git`,
  `python3`, `rsync`. For the VM build, on one host: `gcc-6`/`g++-6` and `libffi-dev libfreetype6-dev libcups2-dev
  libasound2-dev libx11-dev libxext-dev libxt-dev libxrender-dev libxtst-dev zip unzip`. On liftlab Maven is only on
  lift02-06 and lift08-10: give `tools/onlift.sh` those hosts (`LIFTS="lift02 lift03 lift04 lift05 lift06 lift08 lift09
  lift10" tools/onlift.sh ...`, or `-h <host>`) for every build below.
- z3 4.14.1: unpack `https://github.com/Z3Prover/z3/releases/download/z3-4.14.1/z3-4.14.1-x64-glibc-2.35.zip` and put
  `bin/z3` at `~/.local/bin/z3` (or name it as `Z3_BIN`).

Where things go is stated once, in [`tools/lib/gc-env.sh`](../tools/lib/gc-env.sh): `GC_BULK` (the shared storage),
`GC_REPO` (the repository `tools/lib/worktree-add.sh` adds snapshots to, `~/GraphChecker`), `GC_OUT` (run outputs),
`GC_TREES` (the system trees), `GC_M2` (their Maven repositories), `Z3_BIN`, `LIFTS` (the worker hosts: lift02-15 but
lift11), `GC_CONTROL_HOST` (lift11: never a head) and `CAUSYNTH_HOST_MAX_USED_PCT` (70: no start may leave a host's
memory fuller; the host ledger charges memory alone, PIPELINE §7.7). On another cluster, edit those defaults in that file.
A value exported in the shell that starts a run also works: every hop of
the run passes them on (`gc_env_words`); `tools/onlift.sh` does not, so give it `env NAME=value` in its command. The
commands from step 2 on use these variables: `source ~/GraphChecker-hdfs-liftlab/tools/lib/gc-env.sh` in the shell first,
and while a host of `LIFTS` does not answer, export `LIFTS` without it (here: `export LIFTS="lift02 lift03 lift04 lift05
lift06 lift08 lift09 lift10 lift12 lift13 lift14 lift15"`).

## 1. GraphChecker

```bash
git clone -q --no-checkout -b system/hdfs-liftlab git@github.com:JHSUYU/GraphChecker.git ~/GraphChecker-hdfs-liftlab
git -C ~/GraphChecker-hdfs-liftlab sparse-checkout set --no-cone '/*' '!/third_party/'
git -C ~/GraphChecker-hdfs-liftlab checkout -q system/hdfs-liftlab
(cd ~/GraphChecker-hdfs-liftlab && tools/onlift.sh -g 6 mvn -q package -DskipTests)
source ~/GraphChecker-hdfs-liftlab/tools/lib/gc-env.sh
```

The checkout leaves out `third_party/` (the VM's 47,000 source files, which no build or run reads; step 2 clones them
apart). `tools/onlift.sh` runs a command in the current directory on the host of `LIFTS` with the most room, with
Java 8 and Maven on its path; use it for every build. The first build downloads the dependencies into `~/.m2`. The jars
(`target/GraphChecker-1.0-SNAPSHOT{,-jar-with-dependencies,-hadoop-shim}.jar`) are what a run reads; leave a checkout
alone while a run uses it (a series runs from a frozen snapshot: `tools/lib/worktree-add.sh <dir> <commit> --detach`,
then the same build in it).

## 2. The concolic VM image

On a host with gcc-6, a full clone on its local disk:

```bash
ssh <host> 'git clone -q -b system/hdfs-liftlab git@github.com:JHSUYU/GraphChecker.git /localtmp/$USER/gc-vm-hdfs &&
  /localtmp/$USER/gc-vm-hdfs/tools/vm/build-image.sh <GC_BULK>/vm/hdfs-liftlab'
```

A full OpenJDK 8 (Zero, release, `-DENABLE_CONCOLIC`) built on the host's local disk, then the causynth smoke suite
on it: `$GC_BULK/vm/hdfs-liftlab/j2sdk-image` is the image (`CAUSYNTH_CUSTOM_JDK_HOME`), `SOURCE.txt` the commit it was
built from, `smoke.log` the suite (`SMOKE_EXIT=0`). The VM sources are `system/hbase`'s (the same `third_party/` tree), so
`system/hbase`'s image serves too; on liftlab it is `/bigtemp/vnr3ne/vm-force12/j2sdk-image`, which series H1 ran on.

## 3. The HDFS trees

```bash
cd ~/GraphChecker-hdfs-liftlab
tools/onlift.sh -g 8 env GC_TREES=$GC_TREES GC_M2=$GC_M2 \
  experiments/hadoop/prepare-trees.sh hadoop-hdfs-study-r7 hadoop-hdfs-21 hadoop-hdfs-11741-r6 > $GC_BULK/prepare-hdfs.log 2>&1
```

Each tree is cloned from the fork at `$GC_TREES/<name>` on its branch (a directory already there is only built), built
against this checkout's jar with a Maven repository of its own (`$GC_M2/<name>`; hadoop-hdfs and every module it needs,
Java 8), and then runs the workload of every case that names it once natively: a case's classpath is read off its
workload's surefire report, so a case whose workload never ran in its tree fails validate ("missing test report"). The
log ends each tree with one line per workload, `PASSED` or `FAILED` (a native failure still leaves the report the case
needs) or `MISSING` (the script fails): r7's 29 workloads, 21's and 11741's one each. Series H1's tree set
(`GC_TREES=/bigtemp/vnr3ne/wt/hl-trees-1`, `GC_M2=/bigtemp/vnr3ne/m2/hl-1`, r7 and 21 only, since H1 leaves 11741 out)
took ~20 minutes on lift12, 30 of 30 workloads PASSED (2026-10-26). Build the trees one after another, or run `./mvnw -v`
in one first: concurrent first builds race on the shared Maven wrapper's download. Never rebuild a tree a run reads: a tree
changed during a series is a new tree set (a new `GC_TREES` and `GC_M2`). Each case is then valid when
`bash experiments/lib/run.sh <case dir> <case arg> validate` passes (H1: 45 of 45).

## 4. Running the cases

One case, with its budget (the table's `budget_s` column):

```bash
cd ~/GraphChecker-hdfs-liftlab
export GC_OUT=$GC_BULK/gc-out/repro-hdfs CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/hdfs-liftlab/j2sdk-image
mkdir -p $GC_OUT
CASE_TIMEOUT_SECONDS=14400 tools/rounds/launch-run.sh ~/GraphChecker-hdfs-liftlab hdfs-17960 R1-17960
```

Start it on a host that reaches every host of `LIFTS` (never the control host; on liftlab never lift02 or lift03, which
cannot reach lift15): that host is the run's head. The run is a session of its own (`setsid`) and holds the shell until
the case ends (start it as `(setsid nohup ... > <log> 2>&1 < /dev/null &)` to leave it running); it writes
`$GC_OUT/accept-R1-17960/` and ends with the second line of its `summary.tsv`. Its obligations go to every host of
`LIFTS` (`CAUSYNTH_CAMPAIGN_WORKER_HOSTS`). `tools/rounds/stop-run.sh R1-17960` (with the same `GC_OUT`) stops it.

All of them, each alone on the cluster, as series H1 (and EX1 before it) ran them:

```bash
cd ~/GraphChecker-hdfs-liftlab
(setsid nohup tools/rounds/run-series.sh R1 experiments/hadoop/hdfs-cases.tsv system/hdfs-liftlab=$HOME/GraphChecker-hdfs-liftlab \
  > $GC_OUT/series-R1.out 2>&1 < /dev/null &)
```

Each case runs from the checkout its `branch` column names (every case: `system/hdfs-liftlab`) with its budget, one at a
time; naming case ids after the checkout runs only those (H1's 45, every case but hdfs-11741: `$(awk -F'\t' '$1 !~ /^#/ &&
NF && $1 != "hdfs-11741" {print $1}' experiments/hadoop/hdfs-cases.tsv)`). A stopped series resumes by the same command
(finished cases are skipped); `touch $GC_OUT/series-R1.STOP` ends it before its next case. Series H1 ran the same way with
the lead's driver (`/bigtemp/vnr3ne/analysis/hdfs-2026-10-26/lead/final/series.sh`, concurrency 1, every case's head on
lift10, the 12 answering lifts as workers): H1 (`results/hdfs/`: 62555 s for the 45, each alone) has its time per case. Many cases at once instead:
`tools/adhoc/sweep.sh` ([handover/OPERATIONS.md](handover/OPERATIONS.md) §4).

## 5. Reading the results

```bash
tools/rounds/round-verify.sh R1      # how each EXPLORE ended, z3 on the file, gaps, roots
tools/rounds/series-stats.py R1      # claim, time breakdown (seeding, exploration, compose + solver), closure regions per case
tools/analysis/vacuity.py --latest --detail $GC_OUT/accept-R1-<case>   # on every UNSAT
```

A case reproduces when its claim is its final run's in `results/hdfs/index.tsv` (each case's `.smt`, claim and reading
in `results/hdfs/`: H1; 11741's row is the port's CloudLab run F7): SAT (`SAT_CANDIDATE`:
confirmed by a replay, reproduced natively) for the named bugs and hdfs-adhoc-10 and -12; UNSAT (`UNSAT_CLOSED`: z3 on the
exported `final/candidate.smt2` says unsat, EXPLORE at its fixed point) for the study checks, each substantive or vacuous
by construction as its reading says. The report's `PASS` also checks a named bug's declared mechanism; a study check
declares none, so its report says `FAIL` whatever its claim: the claim and round-verify decide, as
[handover/CHECKING.md](handover/CHECKING.md) §1 says. A run's `out/<case>/schedule/final/candidate.smt2` compares with
`results/hdfs/<case>.smt2.gz`; `tools/analysis/smt-legend.py --repo <tree> <run>/out/<case>` names every symbol of a
formula. What each `.smt` must contain (its causal chain, symbols and propagation, read by hand against the HDFS code) is
each case's row in [STATUS.md](STATUS.md) "HDFS checks" (the former bodies' readings). Wall times vary run to run
(replays race); the EX1 rows of the former bodies are in [design/PERFORMANCE.md](design/PERFORMANCE.md) §6.

## 6. The other systems

Each system's cases run from its own GraphChecker branch and its fork's tree, by that branch's `docs/REPRODUCE.md`:
`system/solr` (the fork `JHSUYU/solr`, `graphchecker/solr-checks`), `system/hbase` (`JHSUYU/hbase`,
`graphchecker/hbase-checks`), `system/zookeeper` (`JHSUYU/zookeeper`, `graphchecker/zookeeper-checks`); the old bugs put
back by hand run from each `system/<x>-buggy-detect` and the fork's `graphchecker/<x>-bug-<jira>` branches (zookeeper:
`graphchecker/zk-bug-<jira>`, with `-control` beside each), HDFS's from `system/hdfs-buggy-detect`. The CloudLab record of
the HDFS port is the tag `archive/system/hdfs-cloudlab`.

## 7. The old HDFS bugs put back by hand (`system/hdfs-buggy-detect`)

Seven cases, `experiments/hadoop/hdfs-buggy-<jira>` (HDFS-11741, -17383, -12931, -5766, -10609, -14075, -14311; list and
budgets `experiments/hadoop/hdfs-buggy-cases.tsv`), each on its own tree `hadoop-hdfs-bug-<jira>` = the fork's
`graphchecker/hdfs-bug-<jira>` (`experiments/hadoop/trees.tsv`: `graphchecker/hdfs-checks` with that one bug put back by
hand and its workload). One branch holds everything, on liftlab as §0-§5:

1. **GraphChecker** as §1, on the branch `system/hdfs-buggy-detect`:

   ```bash
   git clone -q --no-checkout -b system/hdfs-buggy-detect git@github.com:JHSUYU/GraphChecker.git ~/GraphChecker-hdfs-bd
   git -C ~/GraphChecker-hdfs-bd sparse-checkout set --no-cone '/*' '!/third_party/'
   git -C ~/GraphChecker-hdfs-bd checkout -q system/hdfs-buggy-detect
   (cd ~/GraphChecker-hdfs-bd && tools/onlift.sh -h <a Maven host> -g 6 mvn -q package -DskipTests)
   source ~/GraphChecker-hdfs-bd/tools/lib/gc-env.sh
   ```

2. **The image** as §2 (the VM sources are `system/hbase`'s; on liftlab `/bigtemp/vnr3ne/vm-force12/j2sdk-image`).

3. **The trees**, into a tree set of their own:

   ```bash
   cd ~/GraphChecker-hdfs-bd
   tools/onlift.sh -h <a Maven host> -g 8 env GC_TREES=$GC_BULK/wt/bd-trees GC_M2=$GC_BULK/m2/bd \
     experiments/hadoop/prepare-trees.sh hadoop-hdfs-bug-11741 hadoop-hdfs-bug-17383 hadoop-hdfs-bug-12931 \
     hadoop-hdfs-bug-5766 hadoop-hdfs-bug-10609 hadoop-hdfs-bug-14075 hadoop-hdfs-bug-14311 > $GC_BULK/prepare-hdfs-bd.log 2>&1
   ```

   As §3: each tree cloned from the fork, built against this checkout's jar, its workload run once natively (one
   `PASSED`/`FAILED`/`MISSING` line each). On liftlab the set is `/bigtemp/vnr3ne/wt/bd-trees-1` (`GC_M2=/bigtemp/vnr3ne/m2/bd-1`),
   every workload PASSED (2026-10-28).

4. **The cases**, all at once (the shared ledger spreads every replay over `LIFTS`), from a frozen snapshot
   (`tools/lib/worktree-add.sh <dir> <commit> --detach`, built as in step 1):

   ```bash
   export GC_OUT=$GC_BULK/gc-out/repro-hdfs-bd GC_TREES=$GC_BULK/wt/bd-trees GC_M2=$GC_BULK/m2/bd \
     CAUSYNTH_CUSTOM_JDK_HOME=$GC_BULK/vm/hdfs-liftlab/j2sdk-image CASE_TIMEOUT_SECONDS=21600 PRUNE=0
   mkdir -p $GC_OUT
   CASES="$(awk -F'\t' '$1 !~ /^#/ && NF {print $1}' experiments/hadoop/hdfs-buggy-cases.tsv | tr '\n' ' ')" \
     tools/rounds/launch-round.sh <snapshot> R1
   ```

   Each case writes `$GC_OUT/accept-R1-buggy-<jira>/` (`DRY=1` first prints the head each would get). Every head must reach
   every host of `LIFTS`: on liftlab lift02 and lift03 cannot reach lift15, so leave lift15 out of `LIFTS` for this round. One case: `CASES=hdfs-buggy-17383`, or
   `tools/rounds/launch-run.sh <snapshot> hdfs-buggy-17383 R1-buggy-17383` as §4.

5. **Reading them**, as §5: `tools/rounds/round-verify.sh R1`; each run's `report/<case>/report.md` (PASS: the case's
   expected mechanism in `experiments/accept/report.py`, confirmed in the VM, reproduced natively with control 0/N);
   `tools/analysis/vacuity.py --latest --detail <run>` on an UNSAT; `tools/analysis/smt-legend.py --repo <tree>
   <run>/out/<case>` against the chain in the case's README. The verdicts to compare with are
   [handover/BUGGY-DETECT.md](handover/BUGGY-DETECT.md) (six SAT, HDFS-14311 not detected).
