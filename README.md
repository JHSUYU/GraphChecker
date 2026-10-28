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

## The branches (github.com/JHSUYU/GraphChecker)

[docs/handover/HANDOVER-2026-10-28.md](docs/handover/HANDOVER-2026-10-28.md) is the map of everything on liftlab:
every GraphChecker branch and fork branch (and the archive tags), the tree sets, snapshots, images, the runs of
record, the buggy-detect results and how to run a case. The same file is on all eight `system/*` branches.

Every system has two branches, both run on liftlab (the lifts below); nothing goes to `main` (the 2026-10-03 body):

| system | ad hoc checks | old bugs put back (their `docs/handover/BUGGY-DETECT.md`) |
| --- | --- | --- |
| HDFS | `system/hdfs-liftlab` (replaces `system/hdfs` and `system/hdfs1`, which stay on origin as history) | `system/hdfs-buggy-detect` |
| HBase | `system/hbase` | `system/hbase-buggy-detect` |
| ZooKeeper | `system/zookeeper` | `system/zookeeper-buggy-detect` (this branch) |
| Solr | `system/solr` | `system/solr-buggy-detect` |

Each `system/<x>-buggy-detect` is `system/<x>` plus the old-bug cases (`experiments/{hadoop,hbase,zookeeper,solr}/*-buggy-<jira>/`) and
the engine support they needed. The CloudLab record (2026-10-24..28) is the tags `archive/system/<x>-cloudlab`.

The code under test is each system's fork, `github.com/JHSUYU/{hadoop,hbase,zookeeper,solr}` (never apache):
`graphchecker/<x>-checks` is the ad hoc tree (hadoop also `graphchecker/hdfs-checks-adhoc07`, `-adhoc21` and
`graphchecker/hdfs-11741`; zookeeper's final series ran on the tag `graphchecker/zookeeper-checks-liftlab`, 51b213562,
since the branch moved on to the buggy-detect trees' base), `graphchecker/<x>-bug-<jira>` one old bug put back on it (hadoop `hdfs-bug-*`, hbase
`hbase-bug-*`, zookeeper `zk-bug-*` with the fixed-code controls `zk-bug-*-control`, solr `solr-bug-*`); each
`experiments/*/trees.tsv` names the branches its system's cases read.

- **HDFS.** `system/hdfs-liftlab`: the 46 HDFS cases (36 study checks, 10 named bugs); its `docs/REPRODUCE.md`
  runs them. `system/hdfs-buggy-detect`: HDFS-11741, -17383, -12931, -5766, -10609, -14075, -14311 put back.
- **HBase** (finished 2026-10-21). `system/hbase`: the 22 HBase cases, `results/hbase/`, REPRODUCE §7.
  `system/hbase-buggy-detect`: HBASE-15039, -20642, -28533.
- **ZooKeeper** (finished 2026-10-22). `system/zookeeper`: the 16 ZooKeeper cases, `results/zookeeper/`, REPRODUCE §8
  (its takeover file is [docs/handover/zookeeper-START-HERE.md](docs/handover/zookeeper-START-HERE.md) here).
  `system/zookeeper-buggy-detect` (this branch): those 16 plus ZOOKEEPER-710 and -2886 put back, REPRODUCE §9;
  [docs/handover/START-HERE.md](docs/handover/START-HERE.md) is where a new lead starts, STATE §Z what the branch holds,
  TODO "ZooKeeper: the buggy-detect line" and "ZooKeeper" what is open, LESSONS §10 what ZooKeeper taught us.
- **Solr** (finished 2026-10-19). `system/solr`: the 20 Solr cases, REPRODUCE §6. `system/solr-buggy-detect`:
  SOLR-9440, -6101, -6197 (SOLR-6763 not reachable).

This branch descends from `system/zookeeper` (from `system/hbase`, `system/solr`, `system/hdfs1`), so its documents also carry the
earlier systems' state (STATE §H, §S, §0; STATUS per system); each system's own branch is its authority.

## The cluster: use every lift, in parallel -- mandatory for whoever takes over

The owner (long-term, 2026-10-05): "一定要最大化利用10个server。这10个server配有nfs,你只要做好代码隔离等。可以大大加速的。这是你的
长期记忆"; "我们一个case内oblication当然可以分配到多机"; "我们不必强行要求独占". The hosts are `lift02`-`lift15`, 48 cores and
30 GB each, NFS between them; `lift11` is the control host (the sessions run there; not a worker, no Maven), `lift07`
has been unreachable since 2026-10-23 (set `LIFTS` without it and without `lift11`; `tools/lib/gc-env.sh`'s default
names both), and Maven and Ant are only on `lift02`-`lift06` and `lift08`-`lift10` (build trees and snapshots there).
**A lead or agent that takes over keeps the workers full at all times; nothing waits in series except on a real
dependency.** How the last leads did it (details and lessons: [docs/handover/PARALLEL.md](docs/handover/PARALLEL.md)):

1. **Inside one case:** every obligation (a solve, then a replay), GROW re-run, CONFIRM and native reproduction is a
   separate start on whichever lift has room (`CAUSYNTH_CAMPAIGN_WORKER_HOSTS` = every worker); one case alone can keep
   ~100 replays in flight.
2. **Across cases:** a round is many cases at once (`tools/rounds/launch-round.sh` with `CASES=...`, or
   `tools/adhoc/sweep.sh <snapshot> <ROUND> <cases> 2`: 2 heads per lift, the cases sharing the replay slots). Give a
   full sweep `CASE_TIMEOUT_SECONDS=10800` (hdfs-11741 `14400`): under 20 heads the 90-min default cut six cases that
   closed at 3 h.
3. **Across development:** up to 5 coding agents (owner 2026-10-18), each on its own branch, sparse worktree, frozen snapshot and
   `GC_OUT`, each running its offline gates and at most 2 live validation runs, beside the lead's rounds; review and
   diagnosis agents read only. A landed fix is validated at once on the cases it touches, never by waiting for a round.
4. **Isolation over NFS is what makes this safe:** worktrees and snapshots without `third_party/`
   (`tools/lib/worktree-add.sh`, seconds instead of most of an hour); system trees, VM images and recorded corpora are
   shared read-only; never rebuild a tree or snapshot a run reads; kill by pid only.
5. **The one limit is memory:** every start is charged on the host ledger and no lift passes 70 %. Shared services must
   not be flooded: offline gates go through `onlift.sh`, a few cases at a time. **The control host stays light:**
   `unset BASH_ENV` in every session (a wedged `/sw` stalled every bash there), no polling or builds there. The whole
   recipe as run on 2026-10-12, with commands: [PARALLEL.md](docs/handover/PARALLEL.md) §6.
6. **At every lull, look at the lifts** (memory and load on each) and fill them with whatever does not wait on a fix.
7. **Parallelism serves throughput, never itself** (owner 2026-10-06: "你也不要过分并行哈。合理的并行"; "并行你要记住是让吞吐提升。
   而不是单单为了并行"): at ~18 live campaigns every case ran 3-5x slower. Keep about 8-10 live campaigns in all, the
   critical path first, and judge by cases finished per hour against each case's solo time, not by how full the lifts
   look.

## Taking over: read these, in order

The README is an index. The handover documents hold the state, the plan and the rules. Every agent
that works on this project takes [RULES.md](docs/handover/RULES.md),
[AGENTS.md](docs/handover/AGENTS.md), [OPERATIONS.md](docs/handover/OPERATIONS.md),
[PARALLEL.md](docs/handover/PARALLEL.md), [CHECKING.md](docs/handover/CHECKING.md) and [LESSONS.md](docs/handover/LESSONS.md) as its own long-term memory.

| # | document | what it holds |
| --- | --- | --- |
| 0 | [docs/handover/START-HERE.md](docs/handover/START-HERE.md) | A new lead starts here: ZooKeeper's old bugs put back (ZOOKEEPER-710, -2886), their verdicts, how to build their trees, run them on liftlab and read the result, what is left, the rules; [zookeeper-START-HERE.md](docs/handover/zookeeper-START-HERE.md) is the 16 ad hoc cases' (ZooKeeper finished 2026-10-22) and [BUGGY-DETECT.md](docs/handover/BUGGY-DETECT.md) the four systems' old-bug table |
| 1 | [docs/handover/STATE.md](docs/handover/STATE.md) | Where the work stands: ZooKeeper (§Z: what `system/zookeeper` and the ZooKeeper fork's tree hold, snapshots, images, runs, evidence); HBase (§H); Solr after its final round SGF9 (§S); the HDFS group (§0-§5): its branches, the goals (verbatim), the remote and the parked local branches, every system tree with its branch, VM images and snapshots, the rounds that closed each case, where the evidence lives. |
| 2 | [docs/handover/TODO.md](docs/handover/TODO.md) | What is left, per system in the owner's order (HDFS, Solr, HBase, ZooKeeper), each item parked with its evidence, then the cross-cutting engine items. |
| 3 | [docs/handover/RULES.md](docs/handover/RULES.md) | The owner's standing rules, long-term, quoted: what a finished check is (only SAT or UNSAT, a right `.smt`), symbolic scope first, general fixes only, no fallback code, a large closure converges (a bound is a rare last resort), workarounds with measure, system by system, git and safety. |
| 3b | [docs/handover/CHECKING.md](docs/handover/CHECKING.md) | How every verdict and `.smt` is checked before it counts (round-verify's columns, the hand check with the legend) and the twenty-one traps the leads fell into (cut searches, unbound handoffs, bounded rounds, constant fatal arms, unreached arms, one-value domains, HELD values, the let-binding trap, NO-SYMBOL, a sweep's default budget, run-to-run open arms, read-order divergence, residue that cannot move a constant phi, ...). |
| 4 | [docs/handover/AGENTS.md](docs/handover/AGENTS.md) | How to work with agents: at most 5 coding agents, reviews at key complex places, briefs, design gates, worktrees, merges, stopping; how each lead ran them and the lessons. |
| 5 | [docs/handover/OPERATIONS.md](docs/handover/OPERATIONS.md) | Servers (the lifts, the 70 % memory ledger), storage, trees, VM images, helper commands and round tools, build and test, rounds, sweeps and exclusive runs, the offline gate, reading and debugging a campaign, traps. |
| 6 | [docs/handover/PARALLEL.md](docs/handover/PARALLEL.md) | How development keeps every lift full: the three levels of parallelism (inside a case, across cases, across agents), isolation and sharing over NFS, the loop in which nothing waits in series, what does not parallelize and how it gets faster. |
| 6b | [docs/handover/OPTIMIZATIONS.md](docs/handover/OPTIMIZATIONS.md) | Every optimization so far -- parallelism and memory, the schedule, exploration rules, ZooKeeper -- with its measured effect and commit, and the ones designed but not done, ranked. |
| 6c | [docs/handover/LESSONS.md](docs/handover/LESSONS.md) | The traps we fell into and how we work around them: shell, zombie processes, NFS, heaps, Java 8 concurrency; how to measure performance and how to debug and verify |
| 7 | [docs/checks/README.md](docs/checks/README.md) | Every ad hoc coordination check of the four systems (HDFS, Solr, HBase, ZooKeeper) and every bug check: site, guard, workload and live state; the per-system point tables and the owner's selection. |
| 8 | [docs/design/README.md](docs/design/README.md) | The design at a glance, stage by stage, and the index of the design specs (PIPELINE, SYMBOL-SCOPE, IDENTITY, CONTRACT-SPEC, VM, PERFORMANCE). |
| 9 | [docs/design/PERFORMANCE.md](docs/design/PERFORMANCE.md) | Where a campaign's time goes, how the lifts run many campaigns at once, why cases were slow, how to debug a slow case, the open speed items. |
| 10 | [docs/STATUS.md](docs/STATUS.md) | Every capability: done / partial / not done, with code pointers and the per-system surface (adapters, workarounds); every case's verdict and its `.smt` read by hand, per system; the open defects. |
| 11 | [docs/REPRODUCE.md](docs/REPRODUCE.md) | From the GitHub branches alone: the machines, the GraphChecker checkout of each system, its VM image, its fork's trees, running one case or all of them, reading the results: HDFS (§0-§5), Solr (§6), HBase (§7), ZooKeeper (§8), ZooKeeper's old bugs (§9). |

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
            (fault markers, hook roots, clocks, configurations, accessor reads,
            call-return answers, the model's order), each ending at the fatal at
            its anchor (runtime/RecordingPlant, the plant agent runtime/PlantAgent)
```

The stages, their gates and the claim kinds are specified in
[docs/design/PIPELINE.md](docs/design/PIPELINE.md).

## Run one case

A case directory holds declarations only. `experiments/<system>/<case>/` contains:

- `case.sh`: the tree, the workload test, the target occurrence and the analysis scope; the test
  is a class and a method `m` (marked `@Test`, or a public `test*()` where the class's randomizedtesting runner takes
  JUnit 3 style methods, as Lucene's and Solr's `LuceneTestCase` does), or one invocation of a parameterized test or class, `m[k]` (`m[i][j]`
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
`LIFTS` (its default is the 11 reachable workers: lift02-15 without lift07, lift11 and lift15).

Obligations of a campaign (each a solve, then its replay when the solver answers SAT, two starts),
and GROW's re-runs, fan out over the hosts in
`CAUSYNTH_CAMPAIGN_WORKER_HOSTS`, each to the host with the most room, as many on a host as its ledger admits, up to its
cores. A head's own steps go to its host when it has room, else to the pool's host with the most
room (`campaign_head_charged`, run there through `run_engine.sh --run-placed`). Every start on a
host is charged to the ledger first, at its measured need, for as long as it runs: the seed replay
(twice the recording's measured peak at its start, its heap sized for seven times it, growing while its host has room), an obligation's solve (what a solver starts at), then
every obligation's, re-run's and CONFIRM's replay
(the campaign's measured replay need: the largest peak its replays stated so far, the seed's first, then
once eight more returned their peaks' 90th percentile, times 1.5, at least 512 MB; `campaign_replay_need_mb`),
each replay at most half a host's ceiling at
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
`CASE_TIMEOUT_SECONDS` (5400 s by default; give a full sweep 10800) and `PRUNE=1` (`PRUNE=0` keeps every artifact, for a measurement sweep, e.g. `CAUSYNTH_CAMPAIGN_STOP_AFTER=SEED`, which reaches each head on its job's command line), and a sweep started again resumes. Give
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
| `…/sessions/<id>/` | one replay's rows: `activations`, `decisions`, `reads`, `writes`, `exports`, `attaches`, `roots`, `targets`, `gaps`, `schedule`, `expressions` (`.jsonl.gz`, gzip: `zcat`), `manifest.json` |
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
src/test/                         unit tests; shell/run_engine_campaign_helpers_test.sh
third_party/OpenJDK-Concolic-Execution-Engine/   the concolic VM (hotspot/src/share/vm/concolic,
                                  interpreter/bytecodeInterpreter.cpp) and its smoke tests
experiments/lib/                  the one harness every case runs through
experiments/accept/               accept.sh, report.py, cone.py, probe.sh
experiments/hadoop/               trees.tsv (the HDFS trees: fork branches), prepare-trees.sh + build.sh (make one),
                                  hdfs-cases.tsv (the 46 cases: branch, budget, EX1's result)
experiments/{hadoop,solr,hbase,zookeeper}/  per-system scripts and cases (<sys>-adhoc: the study checks,
                                  checks.tsv; hadoop/hdfs-bugs, hbase/hbase-bugs, solr/solr-bugs,
                                  zookeeper/zk-bugs: the bug checks; the named cases; <x>-cases.tsv)
tools/onlift.sh, pick-lift.sh     run a command on the host of LIFTS with the most room (Java 8 + Maven)
tools/vm/build-image.sh           the concolic VM image from third_party/, then its smoke suite
tools/lib/                        gc-env.sh (where things live: GC_BULK, GC_OUT, GC_TREES, GC_M2, Z3_BIN, the
                                  host ledger, LIFTS; for every tool and case), worktree-add.sh (a
                                  worktree or snapshot without third_party/), alive.sh
                                  (which runs a process on any lift still names), heads.sh (a
                                  case's configuration, its head's weight and
                                  room, and which host heads it)
tools/rounds/                     launch, monitor and stop campaigns on the lifts (launch-round.sh, launch-run.sh,
                                  stop-run.sh, round-status.sh, round-watch.sh, round-slow.sh, round-verify.sh,
                                  obl-times.py); run-series.sh + series-stats.py (cases one at a time, each alone,
                                  and their time breakdown); snapshot-gc.sh
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
docs/handover/                    STATE, TODO, RULES, CHECKING, AGENTS, OPERATIONS, PARALLEL: the handover (start here)
```
