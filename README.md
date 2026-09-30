# GraphChecker

GraphChecker is an academic research tool in software engineering. It studies how open-source
distributed Java systems (HDFS, Solr) fail under fault, clock and ordering counterfactuals.

It starts from one recorded run of a system's own cluster test that does **not** fail, plus one
annotated failure site (a `throw`). It then asks whether a small change could have made that
run fail at that site, and it answers with a witness. The changes it considers are a transport
fault, a skewed clock, a flipped configuration value, or a different pairing of a message or of
shared state.

A witness is a quantifier-free SMT formula (`candidate.smt2`), a claim naming what moved
(`claim.json`), and one replay confirming that the program agrees (`confirm.json`). Replays run
on a concolic OpenJDK 8 (Zero) that keeps a symbolic expression under every value. The formula
is composed from many focused replays, and the solver picks the nearest world. What the rows do
not state is refused by name, never defaulted.

What works today and what does not is in [docs/STATUS.md](docs/STATUS.md). The design is in
[docs/design/](docs/design/README.md).

## The pipeline

One campaign per case, driven by `run_engine.sh`: one `campaign_<stage>` shell function per
stage, which calls Java mains in the jar.

```
SEED        static fatal slice + scope map (Soot), one recording on stock JDK 8
PLAN        the occurrences to replay, the declared target resolved, the roots to mint
INSTRUMENT  weave hooks into the scoped classes, verify the woven bytecode
REPLAY      seed replay on the concolic VM -> the seed session (one file per row kind)
IMPORT      row-contract gate over every session (contract/RowInvariants)
EXPLORE     waves: plan flip obligations (explore/ExploreMain), solve each, replay it
            focused on its world (runtime/FocusedReplay), grow the woven regions (GROW)
COMPOSE     merge all sessions into one disjunction over the anchor, solve it per
            valuation with z3, decide the claim (compose/ComposeMain: Composer, ClaimPolicy)
SOLVE/DECIDE  check and print the solver verdict and the claim COMPOSE published
CONFIRM     re-run the witness world, check its edges (explore/ConfirmMain)
EMIT        final/result.json, gaps.json, run-manifest.json
```

The stages, their gates and the claim kinds are specified in
[docs/design/PIPELINE.md](docs/design/PIPELINE.md).

## Hosts and inputs

| what | where |
| --- | --- |
| hosts | `lift06`…`lift15`: 48 cores and 30 GB each. The home directory is shared over NFS with a 100 GB quota. Each host has local scratch at `/localtmp/$USER`. Bulky data goes under `/bigtemp/vnr3ne`. |
| stock JDK 8 | `/usr/lib/jvm/java-8-openjdk-amd64`. Maven, the engine, the SEED recording and the ad-hoc coverage runs all use it. |
| concolic VM | Build it with `third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh`; the image lands in `build/linux-x86_64-normal-zero-release/images/j2sdk-image`. Frozen copies live in `~/gc-out/vm-f<N>/j2sdk-image`. Pass the image as `CAUSYNTH_CUSTOM_JDK_HOME`; it is never `JAVA_HOME`. |
| z3 | `~/.local/bin/z3` (4.14.1) |
| HDFS trees | `~/hadoop-hdfs-<case>`, each a worktree of `~/hadoop` on branch `gc/<case>`. The ad-hoc HDFS checks run on `~/hadoop-hdfs-17967-c`. |
| Solr trees | Solr 8.11 worktrees of `~/lucene-solr-8_11`: `gc/solr` (the shared adapter), `~/lucene-solr-18406`, `~/lucene-solr-18413`, `~/lucene-solr-8_11-adhoc` |

## Build and test

```bash
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64 PATH=/usr/lib/jvm/java-8-openjdk-amd64/bin:$PATH
mvn -q -o package -DskipTests      # target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
mvn -q -o test
bash src/test/shell/run_engine_campaign_helpers_test.sh   # the harness test; run it and mvn test before a commit
```

Keep `-o` (offline): `~/.m2` is shared over NFS. `mvn package` also builds the `hadoop-shim`
classifier jar from `src/shim/java`, which the HDFS trees call.

The VM's own smoke tests are separate:
`third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_smoke_test.sh`, with `JDK_HOME`
set to the image.

## Run one case

A case directory holds declarations only. `experiments/<system>/<case>/` contains:

- `case.sh`: the tree, the workload test, the target occurrence and the analysis scope;
- `workflow.properties`: budgets and inputs. `run_engine.sh` accepts only the keys it knows, so
  an unknown key is refused;
- `target.yaml`;
- optionally `communication-mappings.jsonl` (`DOOR` and `WIRE_FLOW` rows),
  `root-domains.jsonl` and `loop-bounds*.jsonl`.

Everything executable is in `experiments/lib/`; its README gives the workload rules. Per-system
parts are in `experiments/<system>/{system.sh,build.sh,classpath.py}`.

```bash
experiments/lib/run.sh experiments/hadoop/hdfs-17960 "" build      # build the tree, run the workload once
export CAUSYNTH_CUSTOM_JDK_HOME=$PWD/third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image
CASES=hdfs-17960 bash experiments/accept/accept.sh                  # campaign + probe + report
```

A case id names its experiment by its longest prefix, for example `hdfs-17899-bug1`,
`solr-18413`, `adhoc-<check>.<workload>` or `solr-adhoc-<check>.<workload>`.

`accept.sh` runs the campaign, a z3 probe and `report.py`. `experiments/accept/README.md` says
what PASS means: the claim, no BLOCKING gap, the case's expected mechanism, `polarityDecides`,
a confirmation, and every moved root inside the causal cone (`cone.py`). `report.py`'s table
names the nine HDFS cases and the two Solr cases; a case it does not name cannot pass. Before
each case `accept.sh` waits for `MIN_FREE_GB` free where `OUT` is written (a refused write there,
such as a full quota, counts as none).

To run from a frozen snapshot (a round) instead of the working tree:

```bash
git worktree add ~/gc-run/p<N> HEAD && (cd ~/gc-run/p<N> && mvn -q -o package -DskipTests)
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/launch-run.sh ~/gc-run/p<N> hdfs-17960 v<R>-17960
GC_OUT=/bigtemp/vnr3ne/gc-out tools/rounds/launch-round.sh ~/gc-run/p<N> v<R>   # the nine HDFS + two Solr cases
tools/rounds/round-monitor.sh 'v<R>-*' | grep --line-buffered 'DONE '
tools/rounds/stop-run.sh v<R>-17960                      # stops a run by its output dir, on every lift
```

Obligations of a campaign fan out over the hosts in `CAUSYNTH_CAMPAIGN_WORKER_HOSTS`. On each
host, a per-host memory gate in `run_engine.sh` admits a start only when `MemAvailable` covers
three things: the case's `obligation_memory_mb`, a 3072 MB reserve, and every start made there
in the last 60 s. The ledger is `~/gc-out/hosts/<host>/`. Rules:

- Never rebuild a tree, or edit a snapshot, while a campaign runs on it.
- Never remove a `~/gc-run/p<N>` that a running sweep uses.

## Run an ad-hoc sweep

An ad-hoc check is a guarded `throw` that a system's existing cluster test reaches and passes.
Each case is one check × one workload (`<check>.<workload>`). The experiments are
`experiments/hadoop/adhoc` and `experiments/solr/solr-adhoc`; each holds `checks.tsv`,
`occurrences.tsv` and `targets/`. Their ad-hoc trees are listed above.

The steps, in order (`tools/adhoc/`; each script's header documents its arguments):

1. `sites.py <system-dir> <repo>`: every guarded `throw new` in the system's sources.
2. `coverage.sh`, fanned out by `fanout.sh`: one JaCoCo run per workload test, which writes
   `<w>.lines` and a `.node` marker and exits with the test's own status. You supply the list of
   workload tests (`workloads.tsv`).
3. `reach.py <sites.jsonl> <coverage-dir>`: checks whose guard ran and whose throw did not.
4. `select.py <system-dir> <sweep-dir> <experiment> <N> [per-check] [tree]`: rank and choose
   checks. It appends them to `checks.tsv` and prints the case ids. A workload whose test failed
   under coverage, or that starts no node, is skipped and named on stderr.
5. `annotate.py <experiment> <tree>`: put `@CausynthExceptionTarget("adhoc-<check>")` on each
   chosen throw and write `targets/`. Then rebuild the tree and commit it (a manual step).
6. `sweep.sh <snapshot> <round> <cases-file> [heads-per-host]`: one campaign per case over all
   ten lifts, with `PRUNE=1` and a 5400 s case budget. Head starts are gated on memory by
   `fanout.sh`.
7. `triage.py <round> [gc-out]`: one row per case with its outcome class (CONFIRMED, REFUTED,
   NO_WITNESS, STOPPED, DEAD, RUNNING, PENDING), finding, stage and reason.

Set `GC_OUT=/bigtemp/vnr3ne/gc-out` for sweeps. The scripts default to `/u/vnr3ne/gc-out`,
which is on the quota-limited home.

## Outputs

`accept.sh` and the round and sweep tools write `$GC_OUT/accept-<suffix>/`:

| path | holds |
| --- | --- |
| `summary.tsv`, `logs/<case>.log`, `report/<case>/{report.md,row.tsv,status}` | the verdict row, the campaign log, the readable report |
| `out/<case>/` | SEED's static artifacts: `static_scope_map.jsonl`, `scope_frontier.jsonl`, `region_skeletons.jsonl.gz`, `candidate_dataflow_edges.jsonl.gz`, and the recording under `runtime/` |
| `out/<case>/schedule/stage_metrics.tsv` | time per stage |
| `out/<case>/schedule/iteration-0000/` | `execution_task_plan.jsonl`, `concolic_region_plan.jsonl`, `recorded_schedule.jsonl`, `sessions/<id>/`, `obligations-<NNNN>/` (per wave: one worker directory per obligation), `obligation_results.jsonl` |
| `…/sessions/<id>/` | one replay's rows: `activations`, `decisions`, `reads`, `writes`, `exports`, `attaches`, `roots`, `targets`, `gaps`, `schedule` (`.jsonl`), `expressions.jsonl`, `manifest.json` |
| `out/<case>/schedule/final/` | `result.json`, `claim.json`, `gaps.json`, `candidate.smt2`, `candidate_composition_manifest.json`, `confirm.json`, `run-manifest.json` |

To read a failed run, work down this list:

1. `summary.tsv`, and `[campaign:error] stage=… reason=…` in the log.
2. `final/gaps.json`: the BLOCKING rows, by stage and code.
3. The per-wave `obligation_results.jsonl` verdicts: `ADMITTED`, `UNSAT`, `NOT_ADMITTED`.
4. A session's `targets.jsonl`, which has `reachedAnchor` and `observedFatal`.

A flip query can be re-solved by hand with `z3 -smt2 obligation_query.smt2`.

Replay working directories go under `/localtmp/$USER/graphchecker/` on each host. A sweep can
fill the home quota. Keep round outputs on `/bigtemp`, and keep at most a couple of snapshots
built.

## Repository map

```
run_engine.sh                     the campaign driver (every stage)
src/main/java/edu/uva/liftlab/graphchecker/
  causynth/    Soot pass: fatal slice, root catalog, door weave, weaving and its verification,
               region finalization, wire-flow catalog
  plan/        static scope map, scope growth, task plan, declared sites, lineage scan,
               work-start and timed-wait shapes
  runtime/     recording and replay hooks, identity and attribution, schedule (ScheduleLog),
               mints, message and store doors (MessageDoors), focused replay, confirmation,
               VM broker
  explore/     corpus, closure, frontier, flip queries, obligations, wave graph, ExploreMain,
               ConfirmMain
  compose/     Composer, families, SMT lowering, container codec, ClaimPolicy, ComposeMain
  contract/    row kinds, identity types, gap registry, session layout, IMPORT gate
  smt/         expression IR, arms and families, z3 driver
  annotation/  @CausynthExceptionTarget, Debug.makeSymbolicBoolean
src/shim/java/                    the Hadoop shim (org.apache.hadoop.ipc.*) the HDFS trees call
src/test/                         unit tests; shell/run_engine_campaign_helpers_test.sh
third_party/OpenJDK-Concolic-Execution-Engine/   the concolic VM (hotspot/src/share/vm/concolic,
                                  interpreter/bytecodeInterpreter.cpp) and its smoke tests
experiments/lib/                  the one harness every case runs through
experiments/accept/               accept.sh, report.py, cone.py, probe.sh
experiments/hadoop/, experiments/solr/   per-system scripts, cases, ad-hoc experiments
experiments/hbase/                HBase reading notes and sketches (not a runnable case)
tools/rounds/                     launch, monitor and stop campaigns on the lifts
tools/adhoc/                      ad-hoc check discovery, selection, sweeps, triage
tools/regress/                    offline-ab.sh: a candidate jar against a baseline on a recorded round, no replay (merge gate)
tools/analysis/                   one-off analyses (chain check, graph diff, pairing probe)
tools/case_onepager.py            one page per case from a campaign's artifacts
tools/linecount_reconcile.sh      per-package line counts of two checkouts
docs/STATUS.md                    done / partial / not done, per requirement; open defects
docs/design/                      the design (index: docs/design/README.md)
docs/reports/                     dated experiment reports
```
