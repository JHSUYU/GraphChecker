# GraphChecker

GraphChecker is an academic research tool in software engineering. It studies how open-source
distributed Java systems (HDFS, Solr, HBase, ZooKeeper) fail under fault, clock and ordering counterfactuals.

It starts from one recorded run of a system's own cluster test that does **not** fail, plus one
declared failure site (a `throw`, named by its class and source line). From that run it explores
systematically: it flips the symbolic branches on the failure's slice and the roots that decide
them (transport faults at the woven doors, local IO faults on the traced flow, clocks,
configuration values, the pairing of a message or of a shared-state read with its writer), replays
each flipped world on a concolic OpenJDK 8 (Zero) that keeps a symbolic expression under every
value, and grows the closure (the woven regions and the rows they state) from what each replay
newly reaches, round after round. Every admitted replay is fused into one free-root formula,
`candidate.smt2`, and z3 on that file decides: SAT or UNSAT.

A SAT comes with a claim naming the roots that moved (`claim.json`) and one replay confirming that
the program agrees (`confirm.json`). What the rows do not state is named, never silently
defaulted.

## Taking over: read these, in order

The README is an index. The handover documents hold the state, the plan and the rules. Every agent
that works on this project takes [RULES.md](docs/handover/RULES.md),
[AGENTS.md](docs/handover/AGENTS.md), [OPERATIONS.md](docs/handover/OPERATIONS.md) and
[PARALLEL.md](docs/handover/PARALLEL.md) as its own long-term memory.

| # | document | what it holds |
| --- | --- | --- |
| 1 | [docs/handover/STATE.md](docs/handover/STATE.md) | Where the work stands at the 2026-10-05 handover: the goals (verbatim); every GraphChecker branch with its head, worktree and state; every system tree (Hadoop, Solr, ZooKeeper, HBase) with its branch and what must change; VM images and snapshots; the rounds (HG4, HG5A, HG7, the agents') and the state of each HDFS check; where the evidence lives. |
| 2 | [docs/handover/TODO.md](docs/handover/TODO.md) | The plan, per system in the owner's order (HDFS, Solr, HBase, ZooKeeper): for HDFS the WIP to land, the r4 trees, the time model, 11741's binding, the open checks, speed, the next round and the end of HDFS, the cleanup still owed. |
| 3 | [docs/handover/RULES.md](docs/handover/RULES.md) | The owner's standing rules, long-term, quoted: what a finished check is (only SAT or UNSAT, a right `.smt`), symbolic scope first, general fixes only, no fallback code, a large closure converges (a bound is a rare last resort), workarounds with measure, system by system, git and safety. |
| 4 | [docs/handover/AGENTS.md](docs/handover/AGENTS.md) | How to work with agents: at most 4 coding agents, reviews at key complex places, briefs, design gates, worktrees, merges, stopping; how each lead ran them and the lessons. |
| 5 | [docs/handover/OPERATIONS.md](docs/handover/OPERATIONS.md) | Servers (ten lifts, the 70 % memory ledger), storage, trees, VM images, helper commands and round tools, build and test, rounds, sweeps and exclusive runs, the offline gate, reading and debugging a campaign, traps. |
| 6 | [docs/handover/PARALLEL.md](docs/handover/PARALLEL.md) | How development keeps all ten lifts full: the three levels of parallelism (inside a case, across cases, across agents), isolation and sharing over NFS, the loop in which nothing waits in series, what does not parallelize and how it gets faster. |
| 7 | [docs/checks/README.md](docs/checks/README.md) | Every ad hoc coordination check of the four systems (HDFS, Solr, HBase, ZooKeeper) and every bug check: site, guard, workload and live state; the per-system point tables and the owner's selection. |
| 8 | [docs/design/README.md](docs/design/README.md) | The design at a glance, stage by stage, and the index of the design specs (PIPELINE, SYMBOL-SCOPE, IDENTITY, CONTRACT-SPEC, VM, PERFORMANCE). |
| 9 | [docs/design/PERFORMANCE.md](docs/design/PERFORMANCE.md) | Where a campaign's time goes, how ten lifts run many campaigns at once, why cases were slow, how to debug a slow case, the open speed items. |
| 10 | [docs/STATUS.md](docs/STATUS.md) | Every capability: done / partial / not done, with code pointers and the per-system surface (adapters, workarounds). |

The sections below are the user-level reference: the pipeline, running one case, running the bug
checks, outputs, and the repository map.

---------------------------------------------------------------------------------------------------


## The pipeline

One campaign per case, driven by `run_engine.sh`: one `campaign_<stage>` shell function per
stage, which calls Java mains in the jar.

```
SEED        static fatal slice + scope map (Soot), one recording on stock JDK 8
PLAN        the occurrences to replay, the declared target resolved, the roots to mint
INSTRUMENT  weave hooks into the scoped classes, verify the woven bytecode
REPLAY      seed replay on the concolic VM -> the seed session (one file per row kind)
IMPORT      row-contract gate over every session (contract/RowInvariants)
EXPLORE     one streaming pool: plan flip obligations in rounds (explore/ExploreMain), solve
            each, replay it focused on its world (runtime/FocusedReplay), land each session
            as it returns, grow the woven regions (GROW); end at the first witness COMPOSE
            accepts
COMPOSE     merge all sessions into one disjunction over the anchor, solve it per
            valuation with z3, decide the claim (compose/ComposeMain: Composer, ClaimPolicy)
SOLVE/DECIDE  check and print the solver verdict and the claim COMPOSE published
CONFIRM     re-run the witness world, check its edges (explore/ConfirmMain)
EMIT        final/result.json, gaps.json, run-manifest.json
REPRODUCE   after the verdict: run a confirmed witness natively, N runs at once over
            the lifts, the recording weave on the stock JDK planting CONFIRM's world
            (fault markers, tree hook roots, the model's order), each ending at the
            fatal at its anchor (runtime/RecordingPlant)
```

The stages, their gates and the claim kinds are specified in
[docs/design/PIPELINE.md](docs/design/PIPELINE.md).

## Run one case

A case directory holds declarations only. `experiments/<system>/<case>/` contains:

- `case.sh`: the tree, the workload test, the target occurrence and the analysis scope; the test
  is a class and a method `m`, or one invocation of a parameterized test or class, `m[k]` (`m[i][j]`
  when both are: the class's, then the method's), k from 1 in the argument sources' order, as JUnit
  numbers them (`runtime/JUnitInvocation`);
- `workflow.properties`: budgets and inputs. `run_engine.sh` accepts only the keys it knows, so
  an unknown key is refused;
- `target.yaml`: `exception_target: <name> <binary class name> <source line> [<thrown type>]`.
  The engine finds the one `throw new` at that line of the class or of a class nested in it (a
  lambda body, an anonymous class) in the compiled classes; the tree is not rebuilt. The thrown
  type is needed only when the line holds two throws. A known bug's case keeps no `target.yaml`:
  its tree marks the bug's target throw with `@CausynthExceptionTarget("<case id>[,<case
  id>...]")` (the case id is `<case dir>-<case arg>`, e.g. `hdfs-17899-bug1`), and `run.sh`
  derives the spec from the marker (`tools/lib/annotated.py <system dir> <tree> <case id>`, into
  `$CAUSYNTH_OUTPUT_DIR/declared-target.yaml`). A bug check is such a case ("Run the bug
  checks");
- optionally `communication-mappings.jsonl` (`WIRE_FLOW` rows, one per system where they are the
  system's protocol: HDFS's is `experiments/hadoop/communication-mappings.jsonl`, used by every HDFS case; the fault doors are the engine's
  library catalog, `docs/design/SYMBOL-SCOPE.md` §4.2), `root-domains.jsonl` and
  `loop-bounds*.jsonl`.

Everything executable is in `experiments/lib/`; its README gives the workload rules. Per-system
parts are in `experiments/<system>/{system.sh,build.sh,classpath.py}`.

```bash
experiments/lib/run.sh experiments/hadoop/hdfs-17960 "" build      # build the tree, run the workload once
export CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-hg5/j2sdk-image     # system/hdfs's image
CASES=hdfs-17960 bash experiments/accept/accept.sh                  # campaign + probe + report
```

A case id names its experiment by its longest prefix, for example `hdfs-17899-bug1` or
`solr-18413`.

`accept.sh` runs the campaign, a z3 probe and `report.py`. `experiments/accept/README.md` says
what PASS means for a known bug (its expected mechanism); a study check (`<sys>-adhoc-NN`) declares no
mechanism, so its result is read by its claim: SAT_CANDIDATE (confirmed), UNSAT_CLOSED, or RUN_DEFECT. Before each case `accept.sh` waits for `MIN_FREE_GB` free where `OUT`
is written.

`tools/lib/gc-env.sh` states, once for every tool and for `run_engine.sh`, the output root
`GC_OUT` (default `/bigtemp/vnr3ne/gc-out`), the host ledger `CAUSYNTH_HOST_LEDGER` (default
`/bigtemp/vnr3ne/gc-out/hosts`, one for the cluster whatever `GC_OUT` a run writes) and the hosts
`LIFTS` (lift06–15).

Obligations of a campaign (each a solve, then its replay when the solver answers SAT, two starts),
and GROW's re-runs, fan out over the hosts in
`CAUSYNTH_CAMPAIGN_WORKER_HOSTS`, round-robin, as many on a host as its ledger admits, up to its
cores. A head's own steps go to its host when it has room, else to the pool's host with the most
room (`campaign_head_charged`, run there through `run_engine.sh --run-placed`). Every start on a
host is charged to the ledger first, at its measured need, for as long as it runs: the seed replay
(seven times the recording's measured peak), an obligation's solve (what a solver starts at), then
every obligation's, re-run's and CONFIRM's replay
(the campaign's measured replay need: the largest peak its replays stated so far, the seed's first,
times 1.5, at least 512 MB; `campaign_replay_need_mb`), each replay at most half a host's ceiling at
its start, a host's solver of the exploration (its start's need; PIPELINE §7.5), a campaign head's
engine JVM (its main's measured need, else `engine_memory_mb`, and once more at `engine_memory_mb`
if it runs out; PIPELINE §7.7), REPRODUCE's runs (the recording's peak), an offline gate's JVM (its
heap) and a `fanout.sh` job (its `NEED_MB`). A sweep's cases share the hosts
(`stream_shared_pool`): each keeps in flight its share of the slots its hosts hold at its measured
replay charge (PIPELINE §7.7). A start goes only when both the host's live charges and its real use
(`MemTotal` less `MemAvailable`), each with the start and a head's held room (its engine JVMs'
measured peak times 1.25, the largest idle head's of the host), stay within
`CAUSYNTH_HOST_MAX_USED_PCT` (70) percent of `MemTotal`; a charge lives by a lease its holder renews
(`$CAUSYNTH_HOST_LEDGER/<host>/charges/`, 120 s), so a killed run's charges lapse, and is released
the moment what it ran returns. A running workload JVM that outgrows its
charge is granted the excess, charged on the ledger, unless the host's real use (`MemTotal` less
`MemAvailable`) would pass that ceiling with it; only then is it ended (`campaign_watch_workload`,
`campaign_host_try_grow`): what the ledger promised other starts is no reason to end it. A head's "waiting for memory for a head step" line goes to stderr
(its stdout is often an artifact).

## Run the bug checks

A bug check is a real historical bug declared like a named case: a case directory (above) without
a `target.yaml`, whose tree marks the bug's throw with `@CausynthExceptionTarget("<case id>")`, run
as one campaign. A list of case ids, one per line, runs through `tools/adhoc/sweep.sh`: one
campaign per case, at most `heads-per-host` heads on each lift and every case's obligations on all
of them, every start through `fanout.sh` and the host ledger ([OPERATIONS.md](docs/handover/OPERATIONS.md) §4); each case gets
`CASE_TIMEOUT_SECONDS` (5400 s by default) and `PRUNE=1` (`PRUNE=0` keeps every artifact, for a measurement sweep, e.g. `CAUSYNTH_CAMPAIGN_STOP_AFTER=SEED`, which reaches each head on its job's command line), and a sweep started again resumes. Give
a sweep its own `GC_OUT`, so that `findings.py` reads that sweep's cases only (the host ledger
stays the cluster's one):

```bash
cd ~/gc-run/p<N>        # a built snapshot (OPERATIONS.md §4; a case on another tree, §5)
out=/bigtemp/vnr3ne/gc-out/checks-<round>
GC_OUT=${out} VM_IMAGE=/bigtemp/vnr3ne/vm-hg5/j2sdk-image setsid nohup \
  bash tools/adhoc/sweep.sh ~/gc-run/p<N> <round> <cases-file> 1 > ${out}-sweep.log 2>&1 < /dev/null &
GC_OUT=${out} tools/rounds/round-monitor.sh '<round>-*' | grep --line-buffered 'DONE '
GC_OUT=${out} python3 tools/adhoc/triage.py <round>         # class, stage, reason per case
python3 tools/adhoc/findings.py ${out} --ledger /bigtemp/vnr3ne/gc-out/findings/ledger.jsonl \
  --annotated experiments/<system> <tree>                    # confirmed witnesses by mechanism
```

Case `n` of the file writes `$GC_OUT/accept-<round>-<n>` (`sweep-<round>-cases.tsv` maps n to the
id); the sweep waits for head room by itself (a quiet log at the start is the ledger, not a hang).
`triage.py` classes each case: CONFIRMED, CONFIG_ONLY (confirmed, every moved root a
configuration), REFUTED (a real false positive: keep it), UNSAT, RUN_DEFECT (a defect of the run
or the engine to fix: no verdict), STOPPED (stage and reason), DEAD, RUNNING, PENDING. `findings.py` writes `findings.tsv`, one row per mechanism among
the confirmed witnesses (the target site, the finding kind and each moved root's kind, site, node
role and context), weighted by kind and native reproduction (REPRODUCE), the configuration-only
ones last; the ledger marks each new, known or dismissed (`dismissed.tsv` beside it), and
`--annotated` names the known bug whose marked throw a witness's campaign declared: a check that
found its own bug again. Hand-check every CONFIRMED witness against the code.

## Outputs

`accept.sh` and the round and sweep tools write `$GC_OUT/accept-<suffix>/`:

| path | holds |
| --- | --- |
| `summary.tsv`, `logs/<case>.log`, `report/<case>/{report.md,row.tsv,status}` | the verdict row, the campaign log, the readable report |
| `out/<case>/` | SEED's static artifacts: `static_scope_map.jsonl`, `scope_frontier.jsonl`, `region_skeletons.jsonl.gz`, `candidate_dataflow_edges.jsonl.gz`, and the recording under `runtime/` |
| `out/<case>/schedule/stage_metrics.tsv` | time per stage |
| `out/<case>/schedule/iteration-0000/` | `execution_task_plan.jsonl`, `concolic_region_plan.jsonl`, `recorded_schedule.jsonl`, `sessions/<id>/`, `obligations-<NNNN>/` (per planner round: one worker directory per obligation), `obligation_results.jsonl`, `exploration.json`, `witness-attempts/` |
| `…/sessions/<id>/` | one replay's rows: `activations`, `decisions`, `reads`, `writes`, `exports`, `attaches`, `roots`, `targets`, `gaps`, `schedule` (`.jsonl`), `expressions.jsonl`, `manifest.json` |
| `out/<case>/schedule/final/` | `result.json`, `claim.json`, `gaps.json`, `candidate.smt2`, `candidate_composition_manifest.json`, `confirm.json`, `reproduce.json`, `run-manifest.json` |

A flip query can be re-solved by hand with `z3 -smt2 obligation_query.smt2`.

## Repository map

```
run_engine.sh                     the campaign driver (every stage)
src/main/java/edu/uva/liftlab/graphchecker/
  causynth/    Soot pass: fatal slice, root catalog, door weave, weaving and its verification,
               region finalization, wire-flow catalog, declared-target line resolver
  plan/        static scope map, scope growth, task plan, declared sites, lineage scan,
               work-start and timed-wait shapes
  runtime/     recording and replay hooks, identity and attribution, schedule (ScheduleLog),
               mints, message and store doors (MessageDoors), focused replay, confirmation,
               VM broker
  explore/     corpus, closure, branches, frontier, flip queries, obligations, wave graph, ExploreMain,
               ConfirmMain
  compose/     Composer, families, SMT lowering, container codec, string identities, ClaimPolicy,
               ComposeMain
  contract/    row kinds, identity types, gap registry, session layout, IMPORT gate, row pool
  smt/         expression IR, arms and families, z3 driver
  annotation/  Debug.makeSymbolicBoolean; @CausynthExceptionTarget (the trees' compile ABI only)
src/shim/java/                    the Hadoop shim (org.apache.hadoop.ipc.*) the HDFS trees call
src/test/                         unit tests; shell/run_engine_campaign_helpers_test.sh
third_party/OpenJDK-Concolic-Execution-Engine/   the concolic VM (hotspot/src/share/vm/concolic,
                                  interpreter/bytecodeInterpreter.cpp) and its smoke tests
experiments/lib/                  the one harness every case runs through
experiments/accept/               accept.sh, report.py, cone.py, probe.sh
experiments/{hadoop,solr,zookeeper}/  per-system scripts and cases (hadoop/hdfs-adhoc: the 36 HDFS study
                                  checks, checks.tsv; hadoop/hdfs-bugs, zookeeper/zk-bugs: the bug_study
                                  checks; HBase's harness is on branch hbase-startup)
tools/lib/                        gc-env.sh (GC_OUT, host ledger, LIFTS for every tool), alive.sh
                                  (which runs a process on any lift still names), heads.sh (a
                                  case's configuration, its head's weight and
                                  room, and which host heads it)
tools/rounds/                     launch, monitor and stop campaigns on the lifts (launch-round.sh, launch-run.sh,
                                  stop-run.sh, round-status.sh, round-watch.sh, round-slow.sh, round-verify.sh,
                                  obl-times.py); snapshot-gc.sh
tools/adhoc/                      sweep.sh (a list of cases over the lifts), fanout.sh, triage.py,
                                  findings.py
tools/regress/                    offline-ab.sh: the offline merge gate
tools/analysis/                   timeline.py (where a campaign's wall time went), rootcov.py (roots
                                  and symbolic predicates per campaign), smt-legend.py (a formula's
                                  symbols named in the system's code, for checking a chain by hand)
docs/STATUS.md                    done / partial / not done, per requirement; open defects
docs/design/                      the design (index and design at a glance: docs/design/README.md; speed and the
                                  cluster: PERFORMANCE.md)
docs/checks/                      every ad hoc coordination check of HDFS, Solr, HBase and ZooKeeper, with its live state
docs/handover/                    STATE, TODO, RULES, AGENTS, OPERATIONS: the handover (start here)
```
