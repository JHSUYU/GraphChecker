# PIPELINE — the stages as the code runs them

One campaign answers one question: can the case's declared occurrence of the declared target site
(the *anchor*) reach its fatal arm, and by which mechanism. `./run_engine.sh --config
<workflow.properties> campaign` runs `do_campaign`, which calls these stages in order through
`campaign_stage` (each stage's wall time goes to `stage_metrics.tsv`; a failing stage ends the run
through `campaign_fail`, which prints `stage`, `component`, `artifact`, `reason` and exits 1):

| stage | code (`run_engine.sh` function; Java main) | writes | fails the campaign when |
| --- | --- | --- | --- |
| PREFLIGHT | `campaign_preflight` | — | the config does not validate; a worker host is unreachable |
| FREEZE_TOOL | `campaign_freeze_graphchecker_jar` | `frozen-inputs/GraphChecker.jar` | the jar changed while copied |
| SETUP (optional) | `campaign_setup` | whatever `campaign_setup_command` does | the command fails |
| FREEZE | `campaign_freeze` | the provenance (published by EMIT) | an input cannot be digested |
| SEED | `campaign_seed`; `GraphCheckerMain`, `plan.ScopeGrowth`, `plan.LineageScan`, `runtime.CausynthTraceRecorder` | static artifacts, the recording, `seed-skeletons/` | the workload exits nonzero; an artifact is missing or stale |
| PLAN | `campaign_plan`; `plan.ConcolicScheduler` | `iteration-0000/execution_task_plan.jsonl`, `runtime_workflow_schedule_index.json`, `plan.log` | the scheduler refuses (its deepest throwable is the reason: not even the target's demand depth fits `schedule_max_jobs`, no declared occurrence, no target); the index does not commit the frozen plan |
| INSTRUMENT | `campaign_instrument`; `GraphCheckerMain`, `causynth.VerifyWovenClasses` | `iteration-0000/instrumented-classes/`, `instrument.log` | the weave refuses (its deepest throwable is the reason); no class woven; a woven class does not verify |
| REPLAY | `campaign_session_replay`; the adapter (`runtime.*` in the workload JVM) | `iteration-0000/sessions/<seed>/` | killed on its bound (`seed_replay_time_factor`); no activation; no target row of the target method |
| IMPORT | `campaign_import_session`; `contract.ImportGateMain` | `session_census.jsonl`, `import_gate.list`, `import_gate.json`, `import_gated/`, `campaign_gaps.jsonl` | a session file is missing; a BLOCKING row invariant |
| ZKKEYS | `campaign_zk_keys`; `compose.ZkKeysMain` (only where PLAN wrote a ZooKeeper chain) | `zk_chain.jsonl` and `execution_task_plan.jsonl` rekeyed, `zk-keys.log` | ZkKeysMain exits nonzero |
| EXPLORE | `campaign_explore` (the streaming loop), `campaign_stream_grow`; `explore.ExploreMain`, `explore.ObligationSolverMain`, `plan.ExposedRegionPlanMain` | `obligations-NNNN/` (`planning-NNNN/` until taken), `steps/NNNN/`, `obligation_results.jsonl`, focused sessions, `exploration.json` | a round's planner fails (one out of the most heap a head JVM is given ends the exploration instead, §7.9); a host's memory or cores cannot be read; a GROW re-run does not finish; a landed session's BLOCKING row invariant (as IMPORT) |
| — | `campaign_publish_iteration_manifest` | `iteration_manifest.json` | — |
| COMPOSE | `campaign_compose`; `compose.ComposeMain` | `final/candidate.smt2`, `candidate_composition_manifest.json`, `claim.json`, `compose_inputs.sha256` | ComposeMain exits nonzero, its deepest throwable the reason (every refusal is a claim, not an exit) |
| SOLVE, DECIDE | `campaign_solve`, `campaign_decide` (read the manifest) | log lines | the manifest states no solver verdict or no valuation rows |
| CONFIRM | `campaign_confirm`; `explore.ConfirmMain`, one replay, `ConfirmMain --sessions` (the decision) | `final/confirm/`, `final/confirm.json`; a refuted claim's row in `refuted_claims.jsonl` | never (a failure is "unconfirmed"; after a refutation, while the budget has room, COMPOSE..CONFIRM run again for the next claim, the refuted one in `final/refuted/NNNN/`, §10) |
| REPRODUCE | `campaign_reproduce` after each confirmed claim, before EMIT; `explore.ConfirmMain --plant`, `reproduce_runs` native runs with the plant over the worker pool; `campaign_unreproduced`, `campaign_fallback` | `final/reproduce/`, `final/reproduce.json`; `final/unreproduced/NNNN/`, `final/fallback.json` | never (a claim reproduced in 0 runs is kept as the fallback and the next claim composed, §10b) |
| EMIT | `campaign_emit` | `final/gaps.json`, `result.json`, `run-manifest.json` | a frozen input changed |
| — | `campaign_exit_verdict` (reads `result.json`) | — | exit 2 = no `SAT_CANDIDATE`/`UNSAT_CLOSED`, exit 3 = BLOCKING gaps |

There is one iteration (`iteration-0000`); what a replay learns past the recording is taken up by GROW
inside EXPLORE. `campaign_stop_after=IMPORT` returns successfully after IMPORT, `SEED` after SEED (a
measurement run: the slice, the recording and its region plan).
The campaign root is `schedule_output_dir` = `<causynth_output_dir>/schedule`; `do_campaign` refuses a
root that already holds an iteration or `final/`, and claims it with `mkdir frozen-inputs`. Every
directory a stage writes is written once.

The row contract every stage reads is [CONTRACT-SPEC.md](CONTRACT-SPEC.md); occurrence identity and
the schedule are [IDENTITY.md](IDENTITY.md); what becomes symbolic is [SYMBOL-SCOPE.md](SYMBOL-SCOPE.md);
the concolic VM is [VM.md](VM.md).

**How the stages divide the work.**

- *A replay collects one arm.* An obligation replay makes one occurrence (or one state-connected
  factor) symbolic, plants the world it is asked about (root values, clock skews, answered
  handoffs, inherited flips), holds the schedule prefix of the session it was cut from, and asks
  that occurrence to take the other arm of one decision. It confirms nothing by itself.
- *Edges are joined in the SMT, not by execution.* Each replay publishes its own path condition
  and expressions; COMPOSE merges them into one disjunction, and a message or shared-state edge is
  a family of arms over the variable the consumer minted, each arm guarded by the world it was
  collected in. No replay has to realize a cross-node chain end to end.
- *The asked world is the one nearest the recording.* A flip query minimizes
  `Σ|x − recorded(x)|` over the integral roots and clocks it bounds, and every root or answered
  handoff of any sort the flipped predicate does not name is planted at its recorded value wherever
  the query stays sat, so a model is the smallest move that still takes the other arm (with a
  one-minute margin where the arm rests on a clock).
- *Demand, not exhaustion.* Exploration starts at the anchor's fatal predicate and guards and grows
  only along boundary inputs of demanded values and the doors of messages a demanded occurrence
  served; an arm is owed once across the corpus. Propagation alone cannot replace it: a root that
  acts only through control dependence (a store the healthy arm skips) leaves the recorded path's
  fatal predicate a literal, so the arm has to be collected by a replay. Focused replays cost the
  sum of the occurrences' path counts where one run holding them all symbolic would cost the product.
- *Fail closed, by name.* Every refusal is a `GapRow` of a closed `GapKind`, classed BLOCKING or
  DIAGNOSTIC by the stage that raises it.

## 0. Configuration

`workflow_config_keys` in `run_engine.sh` is the one table of keys a `workflow.properties` may set
(`k` loadable, `r` reset per run, `p` printed by `config`); an environment variable of the listed
name (e.g. `CAUSYNTH_SOLVER_TIMEOUT_MS`) overrides the file. `validate_config` refuses a run
missing `project_repo, project_module_dir, project_classes_dir, project_classpath,
causynth_output_dir, causynth_target_spec, custom_jdk_home, z3_bin, workload_command, trace_test,
causynth_loop_bounds, causynth_loop_default_bound`, or without a positive integer for each bound
marked * below.

| key | meaning |
| --- | --- |
| `workload_command`, `concolic_replay_command`, `campaign_setup_command` | the recording, the replay adapter (both `experiments/lib/execute.sh` for the committed cases, set by `experiments/lib/run.sh`), an optional setup step |
| `project_*`, `trace_test`, `custom_jdk_home`, `z3_bin`, `java_bin`, `graphchecker_jar` | the workload tree, its test, the concolic VM, z3, the engine |
| `causynth_output_dir` | where every artifact goes; the campaign root is its `schedule/` |
| `causynth_target_spec`, `causynth_communication_mappings`, `causynth_loop_bounds`, `causynth_loop_default_bound`*, `causynth_lineage_roots`, `causynth_scope_growth_budget` (24), `causynth_root_domains` | the case's declarations: target, wire flows and doors, per-loop bounds, lineage scope, scope growth budget, root domains |
| `declared_target_occurrence` | the anchor (§3) |
| `schedule_max_jobs`* | the most tasks PLAN may schedule |
| `solver_timeout_ms`* | one z3 run, in a flip query and in COMPOSE |
| `replay_timeout_s`* (2400) | the wall clock of one obligation replay |
| `seed_replay_time_factor`* (40) | the seed replay's wall clock, as a multiple of the recorded workload's (§5) |
| `recording_max_trace_mb`* (4096) | the most trace the recording may write; past it the workload is ended and SEED fails `RECORDING_BOUND` (§2) |
| `region_path_max_waves`* (12), `region_path_max_tasks`, `region_path_max_paths_per_region`, `region_path_max_flips_per_path`, `region_path_max_world_depth` | EXPLORE's bounds (§7.4, §7.9) |
| `compose_max_valuations`* (16) | the valuations COMPOSE enumerates |
| `campaign_worker_hosts`, `engine_memory_mb`, `stream_shared_pool` (false) | the pool's hosts, the most heap a head JVM is given and a solver asked again, whether the exploration shares its hosts' replay slots with the other sharing explorations (§7.7; a sweep's cases) |
| `campaign_stop_after` | empty, `SEED` or `IMPORT` |
| `reproduce_runs`* (10), `reproduce_time_factor`* (3), `reproduce_min_s`* (300), `reproduce_charge_pct`* (130) | how many native reproduction runs, each one's wall clock as a multiple of the recording's workload, at least `reproduce_min_s`, and each one's memory charge in percent of the recording's peak (§10b) |

Defaults in parentheses; `solver_timeout_ms` and `schedule_max_jobs` have none.

## 1. PREFLIGHT, FREEZE_TOOL, SETUP, FREEZE

- PREFLIGHT: `validate_config`, a replay command is required, `jq` and `sha256sum` exist, and every
  remote host of `campaign_worker_hosts` answers `ssh` in batch mode and sees `run_engine.sh` on the
  shared home.
- FREEZE_TOOL copies the jar into `frozen-inputs/`, digesting before, after and the copy; a jar that
  changed while it was copied fails the stage. Every later stage, and every remote worker, runs the
  frozen copy (`--run-obligation` refuses a jar whose sha256 is not the frozen one).
- SETUP, for the committed cases (`experiments/lib/prepare-analysis.sh`), copies the case's declared
  scope into `<causynth_output_dir>/declared-classes/`, the run's `project_classes_dir`: on the
  shared filesystem, so a static pass placed on any host (§7.7) reads the same classes, and the
  run's own (`experiments/lib/case-env.sh`).
- FREEZE digests the twelve inputs (jar, VM binary, `rt.jar`, `libjava.so`, `libjvm.so`, config,
  target spec, communication mappings, loop bounds, production classes tree, test classes tree,
  classpath string) and both checkouts' state (`campaign_checkout_state`: HEAD, branch, digest of the
  dirty files). SEED adds the static catalog and the region plan to this provenance. EMIT re-digests
  the inputs (`campaign_verify_frozen_inputs`) and fails if any changed.

## 2. SEED

`campaign_seed` runs the static pass and the recording:

1. `campaign_analyze_grown_scope`: `do_analyze` (`GraphCheckerMain` → `causynth.CausynthPipeline`, Soot
   over `project_classes_dir`, target from `causynth_target_spec`, per-loop bounds from
   `causynth_loop_bounds`, wire flows from `causynth_communication_mappings`) writes under
   `causynth_output_dir`: `candidate_dataflow_edges.jsonl.gz`, `region_skeletons.jsonl.gz`,
   `communication_gaps.jsonl.gz`, `static_scope_map.jsonl`, `scope_frontier.jsonl`,
   `root_demand.jsonl` (`causynth.CausynthArtifactWriter`) and `io_doors.jsonl` (the demanded local file
   doors, `causynth.DemandedDoors`; every pass weaves them, `-Dcausynth.io.doors`). A pass that chose
   more of those doors runs again over them, outside the growth budget. While `causynth_scope_growth_budget > 0` and
   `causynth_lineage_roots` is set, `plan.ScopeGrowth` adds classes where the slice stops at the scope
   into `scope-classes/` and the pass runs again, until it adds nothing ([SYMBOL-SCOPE.md](SYMBOL-SCOPE.md)).
   The pass's JVM runs on GraphChecker's jar alone; Soot reads `project_classpath` (`-x`) through
   `IndexedSourceLocator`, which lists the folder of each name it looks up in a class directory once per JVM
   and asks Soot's own lookup only for a name the listing holds (one pass of hdfs-adhoc-19: ~197K failed NFS
   `stat`s before, ~7K after).
   The target spec holds one line, `exception_target: <name> <binary class name> <source line>
   [<thrown type>]`; `causynth.ExceptionTargetLineResolver` finds the one `throw new` javac compiled at
   that line of the class or a class nested in it (a lambda body, an anonymous class), by the
   LineNumberTable of the analysis inputs, and refuses `TARGET_LINE_UNRESOLVED` or
   `TARGET_LINE_AMBIGUOUS` (state the type) otherwise. Its identity is the method, the thrown type and
   the `NEW`'s ordinal among the method's `NEW`s of that type, which the analyzer matches on Jimple.
   A spec of more than one line is refused (`MULTI_TARGET_UNSUPPORTED`).
   The scope map is [SYMBOL-SCOPE.md §3](SYMBOL-SCOPE.md); its `TARGET_SITE` rows state the
   target's `guards` with their fatal arms, the helper branch arms deciding a guard on a helper's
   constant return, each with its verdict or open, nested (`guardDeciders`,
   `causynth.BooleanReturns`) and the `chain` of guards before them; `StaticScopeMap.Site.pathSites`
   = guards + chain + the chain's deciders at every depth; a reached anchor flips its guards and
   the one decision each target row's open decider arm names (`TargetRow.OpenArm`); and `force`,
   the forcing table (each of those ifs with the arm that leads to the throw, a switch never,
   `plan.ForcingTable`; a guard or chain if each of whose arms reaches the throw -- or, in a caller,
   one of its calls into the throw's method -- within one iteration (the branch and every backedge,
   an edge into the loop's header, are barriers: an arm that comes back only in the next turn of a
   loop leaves the way in this one) is stated `passable` and never forced,
   `SiteControlDependence.MethodGuards#passable`: an `assert`'s `$assertionsDisabled` test, a guard
   on its skip arm while its other arm reaches the throw through the assert's own test; the first
   test of `if (a || b) throw`, whose healthy arm reaches it through `b` (a FORCE run that takes that
   arm goes on to `b`, §7.10); a caller's guard choosing which of its calls into the method runs;
   likewise a decider neither of whose arms leaves the way, each running to a return of the verdict
   its guard wants or on to an open value), one per TARGET_SITE row, which PLAN copies -- the task's own target's
   (`StaticScopeMap#ownTarget`) -- onto the declared task's `targetBranch.force` for the
   forced replay (§7.10), less a caller's chain guard where the recording's occurrence entered the
   throw's method (`ForcingTable#forOccurrence`: it reaches the method by some call, and forcing another
   call's guard would only divert it). The same table is COMPOSE's one statement of the arm toward
   the throw (§8, `RestsOn#wayGuard`). Loop-bound
   rows are keyed by Jimple unit id (`<method signature>#uNN`, field `loopSiteId`); the ids the
   pass uses are the skeletons' `loopControlSiteIds`, and any edit to an instrumented method moves
   the ids after it, so a case's loop-bound file is re-read from the skeletons after a tree edit.
   A loop's `K_L` (its row, else `causynth_loop_default_bound`) bounds the path space it offers:
   the iterations of one call that decided on a symbol (§5).
2. `do_workload`: one weave in trace mode `region-state` (lineage classes from `plan.LineageScan`
   included), then the workload itself (`workload_command`; a nonzero exit fails SEED; its wall
   time in seconds is kept as `campaign_recorded_workload_s`, the base of the seed replay's
   bound, §5; the recording itself runs under no wall-clock bound). The weave writes only the rows
   the aggregation reads (`causynth/TracedRows`): call rows at a declared site, a field-accessing
   call, a configured-source hook site, a store site that mutates through a call or a port's
   capture, argument rows at such a store site and where a port captures them, normal-exit rows
   only where a port captures them; every hook is still called, so each row keeps its number. The
   weave leaves the digest of the rule it traced by (`TracedRows#RULE`) and the three static
   artifacts it decided the rows on (scope map, candidate graph, candidate skeletons:
   `TracedRows#inputsDigest`) beside the woven classes; the recorder states it in the trace's
   manifest (schema 2, `tracedRows`), and the aggregation refuses a pruned trace over other
   artifacts, or traced by another rule, by name (`TRACED_ROWS_MISMATCH`: a site or port they add
   would find no rows; a recording made before the storing calls' argument rows lacks the holder
   edges the recorded heap reads -- record again); a schema-1 trace wrote every row. A frame
   writes one decision at one site at most twice (`CausynthTraceRecorder#emitDecision`: readers
   take a frame's decisions as a set, its first, or "more than once" for a loop). A method or
   field row is written only while its thread stands in an opened occurrence
   (`CausynthTraceRecorder#written`, `Identity#inOccurrence`: an activation, a fold into one,
   unnamed work inside one): method and field events count only there, so a row outside every
   occurrence could become no closure task and no row a claim uses (solr-bugs-reindex-cleanup MB2:
   1.78 of a 2.0 GB trace, a shared method run per document on request threads); exchange, gap
   and source rows are always written, and the rows left out are counted and said when the
   recording ends. Its trace is
   bounded: past `recording_max_trace_mb` its watcher (`campaign_watch_workload`) ends the
   workload (`RECORDING_BOUND`: a trace cut short is never aggregated), and so it does once the
   workload wrote nothing -- no trace row, no output, its sockets aside -- for
   `campaign_unbounded_stall_s` (600 s; `RECORDING_STALLED`, its threads first dumped on its
   output): the trees' `CausynthBounds` lift every wait's timeout, so a cluster test waiting for a
   notification it lost would wait out its 6 h bound (solr-bugs-reindex-cleanup SB16: an Overseer
   command's `waitForState` after its source's deletion, an hour without a byte). Either end leaves
   `runtime/RECORDING_ENDED`, the reason first, and SEED fails by that reason. Then
   `runtime.CausynthTraceRecorder` aggregates the trace into `runtime/concolic_region_plan.jsonl`
   (the runtime region plan) and `runtime/region_skeletons.jsonl`; the recording's
   `runtime/schedule.jsonl` sits beside them.
3. Both skeleton views are copied to `<campaign root>/seed-skeletons/`.

Every static pass and weave (`do_analyze`: SEED's passes and recording weave, INSTRUMENT's union
weave, GROW's) runs through `campaign_analyze`: its output is shown and kept (`static-pass.log`,
`runtime/weave.log`, `instrument.log`), and a pass that throws fails its stage with the deepest
throwable it printed as the reason (`campaign_thrown`), never as a bare stack trace.

## 3. PLAN

`campaign_plan` freezes the region plan as `iteration-0000/concolic_region_plan.jsonl`, copies the
recording's schedule to `recorded_schedule.jsonl`, and runs `plan.ConcolicScheduler`
(`scheduleTargetFirst`). `RuntimeWorkflowDiscovery.workflow` schedules the declared target first, then
every other occurrence the plan states is replayable, in recorded order; no slice is applied here
(the closure is EXPLORE's). The declaration is `declared_target_occurrence`: a resolved address, a
selector (`node#epochN/region/REGION.x[@api]#k`, the k-th match in recorded order), or `first` (none stated:
SEED resolves `first` and PLAN refuses, `DECLARED_TARGET_OCCURRENCE_MISSING`). SEED's aggregation resolves it once against the recording's target occurrences
whose chain the window holds back to its root (`RuntimeWorkflowDiscovery#declaredOccurrence`; none:
`DECLARED_TARGET_BEFORE_WINDOW`, IDENTITY.md §9) and marks that row `declaredOccurrence`; PLAN takes
the marked row as the target (no row or two: `DECLARED_TARGET_OCCURRENCE_UNPINNED`), and the shell
uses the address PLAN's index states for every later stage, whatever form the declaration had
(`campaign_plan`). The seed's closure already plans one occurrence per class of equivalent deciders
(SYMBOL-SCOPE.md §4.4, `deciderClass` on its row: `members`, `first`, `last`), and PLAN's log line
and cut summary name the classes (`ConcolicScheduler#deciderClasses`). The writers a reader that never
touched a field did not cross to, every object they wrote it on unreachable from it over the
recorded heap and, with its recorded holders, mentioned under one causal context not the reader's
(SYMBOL-SCOPE.md §4.4), and those crossed to only for a mention, are counted on the reader's row
(`confinedWriters`, `escapedWriters`); PLAN prints them as `CONFINED` and `ESCAPED`, by owner class
and field, and states them in the index. Each drop
is a DIAGNOSTIC `CLOSURE_CONFINED` row of the region plan's gaps, one per reader and field
(count, owner class, first writers), which EMIT carries into the campaign's gaps and result.json
`confinedWriters` (the recorded heap is partial: CHECKING trap 22). When the closure still holds
more occurrences than
`schedule_max_jobs`, PLAN keeps the target and the nearest demand depths that fit whole (the
seed's `demandDepth`, SYMBOL-SCOPE.md §4.4; never part of a depth, whose occurrences are equally
near) and states the rest in the index (`closureCut`: `keptDepth`, `occurrences`, `byDepth`;
`RuntimeWorkflowDiscovery.Workflow#nearest`); `campaign_stream_truncation` names it as a
`PLAN_CLOSURE_CUT` row, DIAGNOSTIC when an accepted witness ended the exploration and BLOCKING
otherwise. Only a target depth that does not fit fails the stage. Outputs: `execution_task_plan.jsonl` (every row stamped with one
`replayGroupId` = `REPLAY.GROUP.<sha256 of the rows>`) and `runtime_workflow_schedule_index.json`
(members TARGET/DEPENDENCY; the shell checks it commits the frozen region plan's sha256 and size and
decodes the membership once into `campaign_member_rows`). The seed replay's plan and every worker's
plan are hard links of the one task plan file, so a row GROW appends reaches all of them.

A door marker mints where its occurrence is planned (`ConcolicScheduler#declaredPorts`), but a store
read's door (a `DATA_FLOW` door, SYMBOL-SCOPE.md §4.2) only at the captures the seed's closure states
on the occurrence's row (`storeFetches`: the fetch whose decode registered what the target read --
an object the target read a slice field on, a provenance site's receiver or a declared read's
(`StaticScopeMap#receiverCells`: hbase-adhoc-34 reads `AuthenticationKey.id` on the key its own
`refreshKeys` decoded from `/hbase/tokenauth/keys/1`) --, and the other fetches, on its node, of a
location what it read was decoded from; each such occurrence is admitted, `STORE_FETCH_V1`,
`RuntimeSelectedRegionFinalizer#askFetches`; the ZooKeeper chain is seeded with the versions of the
same objects); its other captures are
woven but never asked, and the seed's log line counts them (`data-flow doors: N store read(s) in the
M planned occurrence(s), A asked {LOCATION=.., PROVENANCE=..}, R woven but never asked; F fetching
occurrence(s), K admitted only as such`).

A control producer (`CONTROL_PRODUCER_V1`, run paused but for its doors) is admitted where it read
a fault: a door of the message that started a demanded occurrence, and a reply leg of a request it
sent (`RecordedMessages#replyLegsOf`), the reply's readers and, in turn, what they sent. A request
sent by a recorded occurrence standing under the demanded one counts as its own: same node and
context, the demanded occurrence's index a proper prefix of its index (`OccurrenceAddress#standsUnder`),
such as a continuation it registered. EXPLORE applies the same rule (§7.2).

## 4. INSTRUMENT

`campaign_instrument` clears `iteration-0000/instrumented-classes/` and runs `do_analyze` with
`CAUSYNTH_CONCOLIC_TASK_PLAN`/`_TASK_ID` set to the whole plan: one union weave of every task. The
tree must hold a class file, and `causynth.VerifyWovenClasses` must verify every woven class against
the replay's class path, or the stage fails naming the class; a woven class that fails as the class the
class path holds fails unwoven (the same throwable and message, or both a `NoClassDefFoundError` for types
no entry holds: Jetty, for ZooKeeper's admin server under a recipe's workload) is listed `UNLINKED` and does
not fail it, since the workload cannot link it either way. Beside the tree the stage states its
plan's WEAVE KEY (`weave_key`, `causynth.WeaveKey`, `ConcolicInstrumentationSelections#weaveKeyFromEnvironment`):
a digest of every task's instrumentation values (`InstrumentationPlan`, each field by name), in plan
order, a value a later task repeats counted once -- what the weave reads of a plan, parsed as the weave
parses it, and nothing per occurrence; every reader of those values unions them (sets, maps whose first
entry wins, `LoopBoundPolicy#union`), and the weave's other inputs are SEED's, so two plans of one key
weave one tree. GROW re-runs this stage's function where a generation's key is not its tree's (§7.8).
The union weave opens ONE region entry per root hook group (`plan.ExecutionTask#rootHookGroup`: the
region and its root method, and a loop-body root's loop) and one enclosing entry per loop root
(`#loopRootHookGroup`), however many planned occurrences share it; a replay's entry offers each
invocation to every task of its group (`runtime.ConcolicTaskPlan#select`), and two rows of one group
that would place its entry apart are refused (`ROOT_HOOK_GROUP_DISAGREES`).
A loop-body root's controls are the branches leaving its loop, as the catalog's guards are
(`CfgLoopControl#retainedLoops`): an `if`, or a switch with a case that leaves (a `default` that
throws); its frame opens on the outermost control edge into the body whose target dominates the
demanded unit, and closes on every backedge and every exit of a control
(`CausynthPipeline#loopBodyEntry`, `#loopBodyClosingEdges`).
The wire's captures (SYMBOL-SCOPE §6.3): each attach a planned occurrence declares, and every export
of the program -- each OUT port of every region skeleton, its method woven as a planned
region's are (`CausynthPipeline#instrumentConcolicCommunicationHandoffs`,
`runtime.RuntimeRegionPlanner#exportSites`). A protobuf message's field is captured with its message (codec capture,
SYMBOL-SCOPE §6.3): exported at the builder's setter and bound to the builder, handed to the message by its `build()`;
the IPC, HBase RPC and DataTransfer doors walk the message they carry (`MessageCodec`, `WireExport`), staging each bound element
for the receiver, whose getter attaches it after the parse; the engine's plumbing and generated messages are never
state (`EnginePlumbing`, `RowRuntime#ownCode`). Its known limits are STATUS open defects 52-56.
Each conditional of a woven method gets the VM's decision marker just before it and, on every
arm it can take, one observation of the arm taken (`ConcolicRegionRuntime#resolveBranch`,
`#resolveSwitchBranch`; a switch gets one entry per case label), which never steers the run: the
woven body grows with the labels, not their square (ZooKeeper's `FinalRequestProcessor` switches
on 120, which a dispatch per label and successor took past the JVM's 64 KB method limit).

## 5. REPLAY

`campaign_replay` runs `concolic_replay_command` (the adapter) with the plan, task ids, class tree,
sessions directory, worker directory and `CAUSYNTH_SCHEDULE_PREFIX`; the seed replay is held to the
recording's schedule (`recorded_schedule.jsonl`); a timed wait held to it takes its `WAKE` slot when the
slot is due and returns no sooner than its own deadline, since a `WAKE` is a timeout the recording's wait
ran in full (`TimedWaits#outlast`, IDENTITY.md §8). A store's reads and writes take their turns at
their location (`READ`, `WRITE`, IDENTITY.md §7.2), so what a store read finds is the recording's
in the seed and in any replay's prefix. An event of a timed-wait loop's turn (`Root:WAKE/<wait>#k`: k
counts the loop's wakes, which the replay's timing moves) takes its slot by the turn's family, the number left out
and no occurrence named (`ScheduleLog#turnFamily`), so the replay's loop takes the recorded turns' slots in order
whatever turn it is at; one at a slot not yet due waits held, as a poll past its
recorded count does, so it never bounds a give-up of the slots before it; let go, it takes that slot, a `WRITE` still
behind an earlier held write to its location (IDENTITY.md §8). A `WAKE` no occurrence names whose context holds an open
slot between its key's last taken slot and the key's next one polls past its loop's recorded count: it takes no slot, so a
wait that polls longer than recorded never waits at a later loop's slot of the same site, nor passes or gives up what
lies between (`ScheduleLog#pastItsLoopLocked`; hbase-adhoc-13 NP18 gave up 918 slots so before it).
Where the model re-pairs a store read with another version
(a world's planted pairings, §7.5; CONFIRM's `ORDER` rows, §10; a reproduction's plant) the model's
order supersedes the recorded placement: the prefix ends before the first event the pairings
reorder, and past the cut such a run's reads take no slot (`ScheduleLog#readsHeld`), so a `READ`
yields to a planted `ORDER` -- a flipped world that reads before the newer write is never held
back to the recorded place -- while the writes keep their turns behind one another. A `READ` slot
never blocks the frontier, and both its waits are bounded by the stall rule's grace: the read behind
the earlier write is let go a grace into a stall (the write keeps its slot), and the next write
behind a read that does not come gives that read up a grace into one. A replay publishes one session under
`iteration-0000/sessions/<sessionId>/` (layout in [CONTRACT-SPEC.md §2](CONTRACT-SPEC.md)); with no
focus row its `manifest.json` states role `SEED`. The seed replay runs under a wall clock of
`seed_replay_time_factor` × `campaign_recorded_workload_s` seconds (§2), never less than
`replay_timeout_s`. It is `required`: a replay killed on that bound or otherwise (the failure
names what killed it; for the bound, the rule and its numbers, `campaign_adapter_timeout_rule`), a
session set with no `activations.jsonl.gz` that decodes to a row, or no `targets.jsonl.gz` row whose `anchorSiteId`
is in the target method (from the scope map's `TARGET_SITE` row) fails REPLAY; the last names why
the declared task went unanswered, its `TASK_UNANSWERED` row (`campaign_target_unanswered`: the
nearest activations and how each differed -- another node, an anchor the run never minted -- or that
its root never ran). The workload's exit
code is not the gate (a target that throws exits nonzero by design). Everything the engine prints in
a workload JVM -- the schedule's lines, a publication's failure, the workload's terminating
exception -- goes to the standard error the JVM started with (`runtime.EngineConsole`), never through
the `System.err` a test may have captured and asserts on (a40h2 FSImage-851: its seed replay failed
`TestDFSAdminWithHA#verifyUpgradeQueryOutput` on the schedule's own lines, before the declared
occurrence ran).

Loop bounds (`runtime.LoopAccounting`, per loop per method activation). A backedge traversal counts
toward the loop's `K_L` only when the iteration it closes recorded a decision with a term (the
first counts; `ActiveRegion#termedDecisions`): `K_L` bounds the flips a loop offers, and an
iteration that decided only on concrete values offers none; an iteration whose symbolic decisions a nested
planned region records (another occurrence's activation) counts as concrete here, so only the work cap bounds
it (accepted: its flips are that occurrence's). In a FORCE run's armed occurrence (§7.10) `K_L` does not
apply, only the work cap: `K_L` bounds the path space a loop offers to flips, and the forced run has one path,
which ends at its target (`ForcedArms#armedOn`; solr-adhoc-05 F2V4 diverged at `K_L` 8 in
`SolrCore.createInstances`'s symbolic loop). Every traversal, and every body of a fixed-count loop, is
charged to one work cap, `LoopBoundPolicy#workCap` (`MAX_REPLAY_PATH_LOOP_BODIES` = 32, or the loop's
declared `K_L` above it; body 33 is cut, for both kinds, `LoopBackedgeBudget#overWorkCap`); before, only
fixed-count (array-indexed) loops had it, and a
condition-bounded loop -- an iterator, a `while` -- was cut at `K_L` bodies whatever it decided on
(solr-adhoc-05/07/19/21: `CloudDescriptor.<init>`'s loop over a core's properties, every decision
concrete, cut the CREATE at its 9th body before its throw, in the seed and every replay). Either cut
ends the activation `CUT`, publishes its prefix and files a `BOUND_INSUFFICIENT` row naming the loop and its
reason (`LoopAccounting#endAtCut`; `LoopBoundPolicy#K_L_REACHED`, `#WORK_CAP_REACHED`; any other reason --
`INSTRUMENTATION_POLICY_MISMATCH`, `BOUND_HOOK_FAILURE:*` -- is the accounting's own failure); a path at the
anchor that a bound cut on the way to the throw is counted as the case's `loop_body_bound` (§8, result.json
`bounded`).

A replay JVM draws its RSA key pairs from a fixed pool (`runtime.ReplayKeys`, a JCA provider put
first by `JUnitMethodRunner`; four pairs of exponent 65537 per size of 1024-4096 bits, in the jar's
`replay-rsa-keys.txt`, one after another per size): the concolic VM has none of HotSpot's
`BigInteger` intrinsics, so one 2048-bit prime search takes it 40-70 s, and a Solr node makes one as
it starts (four nodes spent 220 s of a 470 s seed replay there). A key pair is `SecureRandom` bits no
stage reads. Another size or exponent is the JDK's own search; the replay log names either once per
size. The recording searches as always. The scope map is read once, when the workload session
opens (`GuardedStoreSites#install`, which hands its rows to `ClockLoops`).

A run ends before its JVM does, in one end for every workload JVM -- the recording, a focused or
CONFIRM replay, a native reproduction -- whether its workload ended or an early end came first
(`runtime.JUnitMethodRunner#exit`): admission ends (`ConcolicRegionRuntime#endAdmission`: no region
starts after it), live activations settle, the run totals close the session's rows (a closed
`SessionPublisher` writes nothing more) and then state the replay's verdict to its worker
(`RowRuntime#writeWorkerVerdicts`, last, whole by one rename), the schedule states how its order went,
the recording's trace is flushed and closed (`CausynthTraceRecorder#closeTrace`, its manifest
`CLOSED`), and the JVM HALTS (`Runtime.halt`; the log's last engine line `Causynth <UTC instant>: the run's
end halts its JVM (status <n>)`): the engine has no shutdown hook, and no cluster's
teardown or shutdown hook runs after the end (PV7-adhoc-38: 35 decided replays, verdicts written,
hung in Jetty's shutdown hook until their bound killed them and recorded `REPLAY_BOUNDED`). The VM
session is never closed; the halt frees it. A JVM told to end before its run did -- a signal (the
worker's bound) or the workload's own `System.exit`; the JDK refuses a new shutdown hook from then
on, before any hook runs (`#shutdownBegun`) -- states nothing and halts: a verdict is only ever a
decided end's. The settle
(`ConcolicResultPublisher#awaitSelectedResultPublications`) is bounded by progress: it gives up once
nothing has moved for 30 s (`#Grace`: no loop body charged, no activation settled, no publication
finished, no CPU on the publication thread or the decoding threads -- the page decoder and its
record decoders -- and no garbage collection while one of them computes -- a collection while all
wait is the cluster's, which runs on through the settle), so
a publication that computes is never cut and one blocked is: every activation still live is then stranded, and the
publication left running and every one queued behind it (the one publication thread reaches none)
are each a `TASK_UNANSWERED` `RESULT_PUBLICATION_UNSETTLED`, a seed's or a confirmation's session
included, which holds every obligation of the replay `NOT_ADMITTED`
(`FocusedReplay#noteUnsettledPublication`: its rows may be partial or missing). A stranded
activation is finished, abandoned and moved aside in one step (`ConcolicRegionRuntime#strand`,
under the lock its terminal takes); its VM region is its thread's, so the terminal that thread still
reaches closes it (`#closeStranded`) and publishes nothing. The end runs once: a
second thread ending the same run (an early end meeting the workload's own) waits for the first's
halt, so no end halts another's close half-done. Cluster threads outlive the test, and a region they
start while the end settles and closes the rows would be an occurrence no row states.

A concolic replay -- the seed's, a focused, FORCE or CONFIRM one -- ENDS AT ITS WINDOW'S CLOSE
(`CausynthTraceRecorder#stopRecording` -> `JUnitMethodRunner#endAtWindowClose`; Solr: `SolrCloudTestCase`'s
`@After`, before the class's cluster shutdown): the test's thread closing its window goes no further, and the
end runs on a thread of its own as at the workload's own end -- the activations still live settle on the
settle's bound while the cluster stays up, every verdict as at the workload's end (`FocusedReplay#windowClosed`:
a faithful world never entered is still `WORLD_REFUTED`, its (d) naming the close, its exception the test
method's own failure where the engine's lifecycle ran the method, `JUnitLifecycle#methodFailure`, printed on the
log; a test its own JUnit runner runs -- Solr's RandomizedRunner -- reports its failure only after its `@After`,
so none is known at the close); the log says `the replay ends at its window's close`. A close that comes after
the run concluded (a witness, a forced target, a refusal or a stall) changes no verdict. The test's thread
waits for the halt holding whatever its `@After` holds (Solr: `CausynthSolrCluster`'s class monitor, which no
cluster thread takes). The recording and a native reproduction run their teardown (natively, seconds;
neither records after the close). Nothing after the close is needed: no occurrence is admitted outside the
window (`ConcolicTaskPlan#select`, `#addressLoopRootInvocation`, `#selectNamed`), the recording states nothing
after it (`CausynthTraceRecorder#tracing`), the order is settled there (`ScheduleLog#windowClosed`) and the
window's duration measured there (`RecordingWindow#close`). What a teardown published were doors' rows of the
cluster's shutdown -- store and view writes, content exports and their watchers' attaches of the nodes' `down`
states (SGF8-adhoc-07: ~310 rows a session past the schedule's last event; 13: ~12) -- and the shutdown paths of
activations live at the close. Their readers: PLAN/EXPLORE's closure walk took them as WIRE and STATE edges and
slots (13 r10 offline over its sessions cut at the close: the same 1154 closure nodes, 79 WIRE edges of the
shutdown's `state.json` writes gone, so the slots and the arm keys that named them), COMPOSE as more versions of
a location to choose from, GROW as producers or door invocations no task planned, the gap ledger and EMIT as
gaps the shutdown filed, the import gate and the ledger as more rows of a session. Each pairs a window read with
a version made after the test ended, or names work no replay of the question runs (admission ends at the close,
and the replay now stops there): none needs them. CONFIRM's and REPRODUCE's questions are the window's.
A workload's second window would find its order already settled at the first close (every Solr recording opens
one). Run, the teardown cost a replay minutes after its close (07 reproductions, close to statement: the SGF8 jar
259-354 s, solr-int 142 s for 0298); ended at the close, 0298 105 s, and 18-156 s in four replays whose stall ended 3-4 s
before it -- what is left is the settle's publications decoding their pages. Their sessions import (no BLOCKING row)
and plan as before (07's seed plus 0298's session: 740 obligations against 741). While the end settles the cluster
runs on, so a door still states rows of ambient occurrences (07: the followers' replication polls, ~8 rows a second)
until the session closes, as it did after an early end's cut before.

A focused replay ends early, once, for one of six reasons (`ConcolicResultPublisher#conclude`):

- `AT_WITNESS`: the focus row's declared occurrence publishes a target row that observed the fatal
  (`#concludeAtWitness`); its schedule states the run cut there (`ScheduleLog#witnessed`: a replay
  held to it holds a `WAKE` it never made to the order's end, IDENTITY.md §8).
- `AT_REFUSAL`: a refusal decided every obligation the replay carries (`#concludeAtRefusal`,
  `FocusedReplay#refusedAt`, §7.6), a FORCE run's divergence among them (§7.10).
- `AT_MISMATCH`: a CONFIRM run took an edge its model did not choose -- a WIRE paired with another
  producer, an ORDER past its timeout, a VIEW_HOLD given way or overridden (`#concludeAtMismatch`,
  `Confirmation#mismatched`) -- which refutes the claim whatever follows; its session stands with the
  mismatch, which CONFIRM decides by. Run on, each ORDER the model chose that never came stood its
  full timeout (SGF7-bugs-snapshot-no-active: a confirmation refuted on a WIRE pairing ran 23 min at
  13 % CPU). A native reproduction and an obligation replay never end so.
- `AT_FORCED_TARGET`: a FORCE run's declared occurrence published its forced target row
  (`#concludeAtForcedTarget`, §7.10), read whole up to there as a witness's session is.
- `AT_NO_PROGRESS`: nothing new for 300 s in a replay asked a flip, before any flip it carries
  was taken, which decided every obligation (`#watchProgress`, `FocusedReplay#noProgress`, §7.6).
- `STALLED_AFTER_FLIP`: the same stall after a flip was taken: the session stands as the run made
  it up to there, read whole as a witness's session is, the flips taken keep their verdicts, the
  questions still open are `NOT_ADMITTED` (§7.6).

Either way admission ends, `Causynth <UTC instant>: the replay ends <reason>` goes to the replay log,
every activation still live is stranded at once, before the settle waits for anything
(`TASK_UNANSWERED` with the reason; after the workload's own end, one live while nothing progressed
for the grace is `TERMINAL_NEVER_REACHED`), and a publication not yet started is withheld (the
reason again): at the witness, a forced target or a stall after a flip, one submitted after it (the
session is read whole up to there, and its schedule states the run cut there); at a refusal or a
stall before any flip, every one (the session is withdrawn, and draining the queue into it cost a
Solr replay two to five minutes past the test's end). So the settle waits only for the publications
the session owes and the mints of the ones after the end: a stranded activation's terminal reads
nothing out (`ConcolicRegionRuntime#closeStranded`); a read-out still reading at the end reads no
more pages (`ConcolicResultPublisher#awaitDecodeRoom`), and a page of a read-out the session
withholds -- not submitted by the end, or submitted after -- files nothing (`#withholds`); its
table is still imported, since the session's pages are one channel and a later page may name a node
only it defined (VM.md §8). Waited for as live, the activations kept closing behind the end, each reading
out pages the one decoding thread decoded for no publication, and each reset the grace: SGF8-adhoc-07,
43 of 72 replays that stalled ran on, 38 to the test's own end (+209 s p50, +572 s p90) and 5 into
`replay_timeout_s`, which lost their verdicts and sessions. A stranded or late activation's path
is withheld and its mints are published, as an abandoned one's are: other activations' rows already
name its symbols (IMPORT invariant 11). The run then ends through `JUnitMethodRunner#exit`, whose halt
ends the in-process cluster (its threads and ports) with the JVM.

A read-out repeats what an earlier one stated (every close reads out every location touched since its
entry), and each event is one row, published by the first activation whose publication walks it
(`RowRuntime#claimEvent`). A location envelope read out again unchanged is filed as the record its
first reading decoded, shared by every activation that read it (`SharedStateCapture.Filed`, VM.md
§8), and a publication does not walk a record an earlier publication walked whole
(`Filed#walked`): every row and gap it can state is claimed once per session, the event index and
the stores outside every region keep what they hold, and what else it reads only grows before the
record exists (a mint's label is filed before its store, the READ_SITE methods at session open, a
performer at its region entry). The record stays the activation's, for its mint stores and its
referents (`RowPlaceholderMint#mintStores`, `RowPublication#unrowedReferent`). The walk rule this rests
on is named at `RowPublication#writes`: an effect that depends on the publishing activation, or is made
without a claim, goes in a loop of its own over every record, walked or not, never inside the walks
the skip drops.

Every logged version a region stored is a write row (`RowPublication#writes`; a store outside
every region has no performer, a declared input is a mint), the location's INITIAL among them,
flagged (`WriteRow#initial`): what the location held before every write its log names -- a
scalar's word, a container's members -- at the access that started the log, spelled as its own
site kind there (`Endpoint#initialSite`). A read of it joins it like any version.

A write of a reference states the state of the container it stored (`runtime.SharedStateCapture`
admits the VM's `referentState`/`referentStateRefused` on a WRITE or RMW of a field or an element
only, and `RowPublication` carries it onto the `WriteRow`); a read of a reference states the
identity it returned, which a read no write row states is pinned to; an exact read
(`observedExact`) the VM left unstated returned its version's leaf -- null, a constant or a named
object, a reference cell's INITIAL null among them (`ReadRow#returned`). A referent's version is a
write row or the write refuses it by name (`RowPublication#unrowedReferent`): the read-out refused
the container's log (its fault, e.g. `CONTAINER_BASE_UNSTATED` for a class the VM walks no base of,
a truncated envelope), or holds the version as no row (`VERSION_NOT_ROWED`) or no longer
(`VERSION_NOT_RETAINED`).

A decision row is a marked branch's own conditions (`runtime.VmBranchAttestation`, by the indices
its event names); a region's summary states no other condition. A container model's choices and
observations reach no row of their own: a choice is the guard of the mutation it stored, and what
the run observed is the `concreteValue` of the query node (VM.md §6, the pin/guard discipline),
which COMPOSE pins (§8, *A query's stated answer*).

A target occurrence publishes its target row whether or not it reached the throw
(`runtime.RowPublication`; a FORCE run's, reached forced, states the forced path condition, §7.10): `phiTerm` is the VM's satisfied predicate of the target branch put in
the fatal polarity (`RowRuntime.fatalTerm`); when the target branch tests what a helper returned,
its condition from the decision that chose the return (`RowPublication#decided`: the latest decision
in the helper's method before the target, when it is one of its `guardDeciders` branches, as
`ite(that decision as it held, the arm it took, the other arm)`, an arm its verdict or, open and
taken, the target's own condition; a concrete one there takes its condition from its nested helper's
deciders in turn; where the other arm is open and never ran, the target's own condition, and the row
names the arm and the decision whose flip runs it, `openArm`) in the fatal polarity
(`RowPublication#phi`), the target standing at the earliest decision it rests on; for a target with several guards (`a || b`), the OR of the fatal arms of the tests this
evaluation decided, from the test it reached the target at, with `observedFatal` = one
test took its fatal arm. A decision that states no predicate (the VM decided it concretely) is the
constant of the arm it took: `true` on the fatal arm, `false` on the healthy one, so a concrete
test that took its fatal arm is the whole disjunction and no arm at all is `false`; a reached anchor
never states an empty phi, an unreached one states none. A reached target whose decision has no
VM event id is a BLOCKING `UNSTATED_VALUE` (no position to cut the prefix at).

## 6. IMPORT

`campaign_import_session` requires every session to hold `activations, decisions, exports, attaches,
writes, reads, roots, targets, gaps, schedule` `.jsonl.gz` and a non-empty `expressions.jsonl.gz`, and
writes one `SESSION_CENSUS` row per (session, kind) to `session_census.jsonl` (its rows counted as they
decode, `campaign_rows`). `campaign_import_gate` then runs
`contract.ImportGateMain`, which appends every `contract.RowInvariants` violation (invariants 1-12,
[CONTRACT-SPEC.md §2.6](CONTRACT-SPEC.md)) to `campaign_gaps.jsonl` and prints a summary; one BLOCKING
violation fails IMPORT naming the first subject. The same gate runs on every session EXPLORE gates
before it lands (§7.9).

`campaign_import_gate <iteration> <epoch> <summary> <list>` judges each session once: the sessions
`<list>` names, one per line -- a session's directory WHEREVER IT STANDS (the corpus at IMPORT, where
the seed's is listed in `import_gate.list`; during EXPLORE the worker that replayed it, before it
lands) and, each a tab after it, the obligation workers whose answers name it, whose focus rows
are the ask it ran under and the flips it owes -- each recorded in the ledger `import_gated/`, one
record per session (`<id>.json`: whether it states SEED and the roots it mints, each id with the
first symbol its rows mint it under; `<id>.named.json.gz`: every symbol it names with one citation;
`ImportGateMain#record`); a session the ledger holds is not judged again. Every rule but two is one
session's. The two over the set are judged against the sessions the ledger holds that are still in
the epoch -- every one but those GROW's swaps withdrew (`withdrawn.txt`) and those the sessions gated now
replace (`--replaced`: a re-run's exposing session, gated before its swap) -- BY THEIR RECORDS, never
by reading them again (`RowInvariants.Gated`): exactly one SEED (1), and the epoch's roots (11) -- a
new session against every root of the epoch, a gated one again only for a root (id, symbol) a new
session brings, by what its record names and mints; the epoch in session id order, whichever
sessions it was gated in, so the first session to mint a root names its symbol. So gating the corpus
a wave, or a session, at a time files exactly the rows one gate over all of it would, each once,
and a gate's cost is its own sessions': SGF8-adhoc-07's gates read every admitted session's
manifest and roots (8-10 s for one session) and all ~300 of them whole when one brought a root (332
s for one, 463 s for 26). One caller at a time (the head). The gate holds one session at a time, so
its heap and its charge on the host it is placed on (§7.7) are 512 MB plus four times the largest
listed session's text (`campaign_import_gate_heap_mb`, `campaign_rows_bytes`: a session's rows as
they decode, not their gzip), not `engine_memory_mb`, which is sized for a JVM holding the whole
corpus (SOLR-18406 i1: charged 16 GB, IMPORT waited 7 min for room on the head and a wave's gate 30
min; the gate itself ran seconds). `tools/regress/offline-ab.sh`'s IMPORT stage lists every session
of a recorded corpus beside its workers and gates them at once with no ledger.

ZKKEYS (`campaign_zk_keys`, `compose.ZkKeysMain`; SYMBOL-SCOPE §6.4), where PLAN wrote a ZooKeeper
chain (`zk_chain.jsonl`, copied into the iteration by PLAN): the seed's own composition to the anchor,
and the decisions of every occurrence the anchor's values came from, name the store leaves the
question rests on; the iteration's chain is rekeyed with them, each plan row stating `contentKeys`
takes its occurrence's keys of it, and the plan is linked again as the seed's, so every replay after
the seed crosses only those leaves symbolically. A seed that composes no path keeps PLAN's keys.

## 7. EXPLORE

EXPLORE collects the arms the seed lacks: it flips decisions the anchor's failure can depend on, one
focused replay per flip, in planner rounds over one streaming pool (§7.9), and never decides a
witness (only COMPOSE and z3 do).

### 7.1 One round: `explore.ExploreMain`

ONE planner JVM serves an exploration's rounds (`ExploreMain --serve <dir> --sessions
<iteration>/sessions --static-scope-map ... --target-occurrence <declared>` plus the root domains and
bounds; each round one question naming its `round`, the inputs the campaign froze as the round
started -- its `corpus` (`<round>/corpus.txt`: the sessions it reads, one per line, every one landed
and gated), its `results` (`<round>/answers.jsonl`: the answers landed) and its `inFlight`
(`<round>/in_flight.jsonl`) -- and its `outputDir` (`planning-NNNN`, `obligations-NNNN` once taken),
asked through `explore.Service`, the protocol the host solvers speak, §7.5; the driver's side is §7.9:
the campaign lands sessions while a round plans, and the round reads none of them,
`SessionDir#named`; a named session the iteration does not hold fails the round; the obligation
workers' own files it reads as they stand, §7.9). What it read
for a round it keeps for the next: the sessions' rows (`Corpus#read(Path, Path, Corpus, Collection)`:
a landed session's rows never change, so only the sessions new to the round's corpus are parsed, and
one that left -- a GROW swap, after-witness trimming -- is dropped; of a session's gap rows, every one
read and only the kinds a corpus reads held, `SessionReader#gaps(GapKind)`: ADDRESS_UNSTABLE,
BOUND_INSUFFICIENT, UNPLANNED_INPUT, UNSTATED_VALUE -- EMIT reads the gap files themselves, §11 -- in every
JVM that reads a corpus) with what was derived from each
session's rows
alone (`Corpus.Derived`: its state join, its schedule's facts, read once, its rows by what they name --
the first activation and the decisions of each occurrence, the attach, root and read minting each symbol, a
forced session's own messages by interaction and producer -- and the walks of its expressions: symbols,
leaves, read locations and events, state reads), the static map while its
file reads the same (by digest), and the slot table it changed (step 4). WHAT A CORPUS HOLDS IS HELD
COMPACT, in every JVM that reads one, with no change to what any stage computes or writes: a session's
rows are keyed by what they name inside its `Derived`, never by a key spelled of the session and the name,
and its state join by a location's key and a version (`contract.VersionMap`, `SmtLowering#joinOf`, which also
answers a write by its version, `SessionJoin#write`: the corpus keeps no index of its own of writes); a
read's endpoints, locations, occurrences, index frames and strings are held once per read of a corpus
(`contract.RowPool`; the slot table's once per its read, `SlotTable#read`), a location's key spelled once
(`LocationId#key`) and an expression node's interned (`SmtLowering#locationKey(JsonObject)`); a set made once
and only read is a `contract.FrozenSet` (one array, its order kept: what a delivery rests on,
`RestsOn#named`; an expression's symbols, read locations and events, `Corpus#expressionSymbols`,
`#readLocations`, `#readEvents`; the join's read symbols; a member's reads by location and object,
`ClosurePlanner.MemberReads`), indexed for `contains` only the first time it is asked, a set the walk only
adds to and asks is a `contract.OpenSet` (`ClosurePlanner.Named`'s symbols and kept symbols, which no order is
read of) or, of rows, a `contract.IdentitySet` (a walk's decisions); a demand's expanded reads are bits over its
group's reads, by each read's place there (`ClosurePlanner.GroupReads#readAt`: a demand's walks have the one group
of its occurrence); a handoff the walk paired is a pair of references in a `contract.PairSet`, never a
`session|symbol` string, and every other key of several names is their list, never one string spelled of them
(the walk's once-said gaps, a member's reads by session and location or object, a location's write sites by site
and Java type, `Corpus#writeSitesOf`). A list an
index holds for good is cut to its size (`contract.Held`); every location key in a JVM is one string
(`LocationId#key`, interned), and so is every name a corpus derives from a session's schedule and leaf sets
(`Corpus#NAMES`: its facts' ids, stances and renders, `HeldLeaves`); the slot table is keyed by its
interactions' parts and world (`SlotTable.Key`), never their digested id spelled with the world; a round
takes what its manifest states of the reconciliation at once (`ExploreMain#skeleton`), its gaps written; an
expression table drops a node's reference once the collector let the node go (`ExpressionTable.Live`).
Within a round, what a
round asks again of the same corpus is answered once: an arm's dependence per task and decision
(`Corpus#dependence`: the frontier and the candidates key the same arms) and a task's feeders, and
the closure's walks of a demand that grew reuse its group, its members' reads and each read's
eligible writes (`ClosurePlanner.Walk#group`, `Corpus#eligibleWrites`). A member's reads are indexed once
per walk, and a group reads its members' indexes in group order (`ClosurePlanner.GroupReads`): the groups
of a closure overlap, and indexed per group, solr-adhoc-39 PV7 round 6's walk held each member's reads once
per group it is in, past 14 GB. Outside the closure walk a round's independent work takes every core of
its host (`contract.Parallel`; a planner is a head step, one JVM alone on its host, and its main says so,
`Parallel#width`; every other engine JVM -- a host solver, a composition, a confirmation -- computes on one
core beside the work the ledger booked the rest for): the dependences of
the arms the frontier keys (`ObligationFactory#dependences`: one session's arms in their order on one
thread -- a key asks its session's lowering, leaf sets and names, which remember the order they were
asked in -- the sessions side by side, after the literals every integral configuration is compared
with, which lower every session's decisions, `Corpus#configurationLiterals`, asked the same way; what a
session's keys named and lowered goes with its last one, `Corpus#keysDone`: held for every session to
the round's end, the lowerings' memos filled SGF8-adhoc-40 planning-7's 21504 MB heap), what each task's path
offers before the ledger is asked (`ObligationFactory#candidates`, by session as the keys), each new
session's derived rows and row ids (`Parallel#READS` at a time), each admitted session's graph nodes
and edges (`WaveGraph#of`) and store writes past the chain (`ZkEdges#of`), and every obligation
worker's files (`ExploreMain#answersByFlip`, `ObligationDir#workersIn`); a JSONL file is read in
blocks of whole lines and written in runs of rows, each parsed or rendered on a core
(`RowCodec#readAll`, `#readEach`, `#writeAll`, `Parallel#stream`; the slot table folds a round's
changes as they are parsed, `SlotTable#read`), and the round's two largest files, its slot changes
(whole once the skeleton is reconciled) and its graph, are written beside the rest of the round,
and its manifest, the round's end (`campaign_last_round_millis`), once they are (`Parallel#beside`; a
round that failed leaves none written over the next one's). Every result is taken in its items' order, so a round's files are byte for byte a
one-thread round's. Every index across sessions
is built anew each round, the lowerings with it, so each round's files are the ones a planner of its own, reading the
iteration then, writes (`ExploreMain --round N --results ... --output-dir ...`, the offline stages' entry over the
same code, reading every session its iteration holds; gated by `offline-ab.sh` `EXPLORE.serve`, whose served side
names each round's corpus as the run's head does). A late hdfs-adhoc-07 round, rebuilt whole by a
JVM of its own, was ~15 min: 2.5 min reading 653 sessions' rows and 4 min reading and rewriting a
1.9 GB slot table (PERFORMANCE §5). A round reads the corpus (`explore.Corpus.read`: every session its
corpus names, each worker's focus row as that session's world, the verdicts, the recorded schedule) and:

1. Names planned tasks answered at two addresses (`ADDRESS_UNSTABLE`, DIAGNOSTIC).
2. Resolves the declaration against the seed session's activations (`plan.SelectorResolution`);
   no single SEED session, an unresolved selector, or an address the seed never activated is a
   BLOCKING gap and leaves the round with no root.
3. Stops the branches that cannot answer the question (`explore.Branches`, §7.4) and plans the
   anchor's closure (§7.2). Every occurrence the rows connect (a recorded writer or producer, a
   control producer, the anchor) is planned as the walk finds it and never counts against the task
   bound; static candidate writers and producers wait until none is left and are then planned
   round-robin over their (node, region, context shape) class, at most `--max-tasks`
   (`region_path_max_tasks`, default 64) of them (`ClosurePlanner.Candidates`). solr-adhoc-07 IB1:
   59 of its 64 tasks were `CoreContainer.getCore` candidates while two recorded `create` writers were
   cut; its row-connected closure is 252 occurrences, planned whole. The runaway guard: past
   `ClosurePlanner.CLOSURE_CEILING` (1024) occurrences the rows connect are cut too, and so is every
   static candidate (one planned before leaves the plan: a recorded writer is never cut while a static
   candidate is kept; a candidate the rows later reach, as a member or a control producer, is no
   static candidate any more, `ClosurePlanner.Demand#absorb`), counted in the manifest's
   `ceilingCut` and named in result.json `bounded`
   (`region_path_closure_ceiling`). A
   truncated closure is the round's DIAGNOSTIC `ADMISSION_GAP` (`REGION_PATH_CLOSURE_TRUNCATED: ...`; `PLAN_CLOSURE_CUT` is PLAN's cut at `schedule_max_jobs`, §3) and its
   manifest's `truncated` (the occurrences not planned); whether it blocks a claim is the
   exploration's end's to say (§7.9).
4. Reconciles the slot table (`explore.SlotTable`): one slot per
   (interaction, world) inside the closure; a WIRE consumer paired with another producer in the same
   world is a replacement, and a read whose observed write the run orders after it (the two rows'
   seqs, the VM's one event clock, whatever threads ran them; never the anchor chain, which orders
   occurrences, not their events) contradicts the order (both `TOPOLOGY_DIVERGENCE`, BLOCKING when
   the session is admitted, else DIAGNOSTIC); another
   world's pairing is a new slot. A closure member's code point (node, region, index) that a
   session ran only under contexts of another shape (`Corpus#contextShape`, the rule of §7.4 and
   IDENTITY §9: per anchor hop the RPC site and sending node, then the root's role and api, without
   the per-site counts) is a `TOPOLOGY_DIVERGENCE` as well, BLOCKING when the session is admitted
   and in a world where the member ran, else DIAGNOSTIC (a new occurrence); under the member's shape
   it ran the member, whatever it counted (a poll's k-th wake is another k in every run), and under
   that shape and another too it grew. A member the session ran under its own shape (no `Lost`
   context), at its region and index, on another node MOVED -- the world placed the work there, and
   what runs at its code point is other work (solr-bugs-snapshot-no-active Z2K: a setData fault made
   node1 the Overseer, the client's update ran on node0, node1's autoscaling write stood at
   setData's code point) -- an `ADDRESS_UNSTABLE` DIAGNOSTIC row naming the node, never a
   replacement. A slot stands on the session that opened it: the slots of a
   session no longer in the corpus (one a GROW swap withdrew, §7.8) are dropped first, here and
   where COMPOSE reads the table, and the session in its place opens them again. An occurrence a
   replay answered by its shape (IDENTITY §9, its `ADDRESS_UNSTABLE` row) stands at the planned
   address under another chain, so its pairings are that chain's: they open slots beside the
   planned occurrence's and replace none, whichever session lands first, since each slot is
   indexed by whether its opening session answered its consumer's occurrence; only another
   answered pairing fills such a slot. On disk the table is its rounds' changes: each round writes,
   beside the rest of its work once reconciled, `obligations-NNNN/slots.jsonl.gz`, the slots it opened or replaced (`SLOT`,
   the row the slot holds now) and those it dropped (`SLOT_DROPPED`), in order; the table is those
   files folded in round order, after an iteration's whole `slots.jsonl.gz` where a run recorded before
   the per-round files has one (`SlotTable#read`). A round's planner folds the rounds before its own
   (the served one keeps the table it changed), so a round planned again starts from the same table
   and a round directory that goes takes its changes with it; COMPOSE folds them all.
5. Builds the ledger (§7.3), takes the arms in flight (`--in-flight`: the obligation rows the
   campaign has queued or running), builds the candidates (§7.4) -- the FORCE run first while it is owed, the
   forced flips next, then every other flip, none of which waits for them (§7.10) -- and opens the round:
   `obligations.jsonl`, nothing settled and nothing in flight.
6. Names the WITNESSES: every admitted focused session whose target row at the anchor observed the
   fatal (`ExploreMain#witnesses`), and states the anchor as a target row spells its occurrence
   (`anchorOccurrences`), by which the campaign tells a witness as it lands (§7.9).
7. States the round's WAVE, a generation of worlds: one past the deepest wave whose obligation
   published a landed session, 0 over the seed alone. It deepens only as sessions land.
8. Writes `graph.jsonl.gz` (`WaveGraph`: NODE per activated occurrence of admitted sessions, EDGE per
   WIRE pairing and STATE join, each with the world digests it was seen in, and a FRONTIER row with
   the counts new since the previous round), `growth.jsonl` (§7.8), `tasks.jsonl.gz`, `gaps.jsonl.gz`
   (the round's large files, and `slots.jsonl.gz`, gzip: `RowCodec#writeAll` deflates each run of
   1024 rows on the core that rendered it, one gzip member each, CONTRACT-SPEC §2.2; the gaps are
   written as the round says them, the closure walk's among them: `explore.RoundGaps` renders,
   deduplicates (by the line's 128-bit murmur3 digest) and deflates each run of 1024 distinct rows on a
   thread of its own and holds no row, `RowCodec.Runs`, the file written whole at the round's end, byte
   for byte the one `writeAll` wrote of their distinct list) and
   `explore_manifest.json` (anchors, round, wave, witnesses, tasks with their `why`,
   proposed/answered/in-flight counts and the candidates held in flight, the branches stopped,
   verdict histogram, gap counts, `force` (§7.10), state `OBLIGATIONS_PROPOSED` | `AWAITING` (nothing new, arms in
   flight) | `FIXED_POINT`, `concreteAnchors`, `openArms` and `boundedFlips`, §7.6). What only the seed ran is BLOCKING at the fixed
   point alone: nothing proposed, exposed or in flight, and no witness. A concrete anchor (§7.2) is
   information, never a gap: its decision is a constant of the formula (§8, a `false` phi), and each
   round's manifest states it in `concreteAnchors` (`ExploreMain#concreteRow`: its admitted paths,
   how many decided it on the way to the throw, the reads its closure demands and their locations,
   the earlier reads off the cone), which EMIT publishes in `result.json` `concrete[]`. So are the
   open decider arms the anchor's reached, admitted runs left phi without (`TargetRow.OpenArm`) and
   no run took (`ExploreMain#openArms`: per arm the state of its flip on each path that left it --
   UNSAT, UNANSWERED (a flip that came to no verdict, a replay that never reached the decision and
   refuted nothing), PENDING (asked, a flip asked again without a refuted world among them),
   BOUNDED (asked no more past `ObligationFactory#MAX_REFUTED_WORLDS` = 8 refuted worlds, the named
   valve for a clock or a wide integral that offers one world per value: `result.json` `bounded`
   `open_arm_max_refuted_worlds`), NOT_ASKED, NOT_FLIPPABLE -- an arm a path took is not listed -- and
   `refutedWorlds`, each world a replay of its flip refuted, §7.6; `unrunWorlds`, the asked-once-more
   replays that refuted nothing), judged at EMIT (§11). A path that asked its own flip is judged by
   that flip's answers, a refuted world answering nothing; a path that never asked shares the
   verdict of the obligation its id names (one arm per dependence, STATUS 58).

### 7.2 The closure: `explore.ClosurePlanner.plan`

Demand starts at the anchor: its flip sites are the target sites' guards
(`StaticScopeMap.Site.guards`) when some run reached the anchor, else the sites of the target's path
chain (`pathSites`). The demanded symbols of an occurrence are those its demanded values reach,
asked of their expressions' shared nodes, never of their lowered text (`Corpus#termSymbols`,
`#expressionSymbols`: the symbol leaves, through each joinable read to the value its version holds,
a container read's state rows by the v_C rule, a read no write answers as its mint; each expression
walked once per session): the anchor's `phiTerm` (a concrete fatal condition's constant names nothing), its own decisions at its flip sites (a factor
member deciding the same site decides it on its own objects), and the values it contributed (the
exports a demanded attach paired with, the write a demanded read could observe), and WHAT COMPOSE
KEEPS of each (`compose.RestsOn`, the one notion of what a delivery rests on, COMPOSE's path and arm
closures included): for each path COMPOSE admits at the anchor (`RestsOn#admitted`, COMPOSE's own
admission: a replay that refused its obligation is no path) -- its closure unseeded, as COMPOSE's --
and for each session the occurrence contributed in up to its last contribution's seq -- seeded by the
writes its contributed expressions read (`RestsOn#seedWrites`) -- the decisions of every occurrence
the row joins from its prefix reach (§8 P3) and the reads of those occurrences that rest on what
moves (`Independence`: a root, a clock, a value the session received), the anchor's own prefix
decisions among them, and no root the session minted that nothing kept reads; a handoff those name
is resolved to its attach row whoever received it, however many joins away (`ClosurePlanner
#step`), and its producer planned (hdfs-11741: the balancer's KeyManager, reached by the SASL
producer's closure, decides on the expiry dates of nn0's `updateBlockKeys@1` response, whose handler
no session ran until it was demanded so); closed over the reads those name and the writes they could
observe. Each (kind, session, occurrence, cutoff, terms) is asked once per walk. CONFIRM's ORDER
reads the same closure (`RestsOn#closure`), the anchor's reads cut where its path decided. The occurrence and its state-connected
factor are
one symbolic unit: every member's attaches and reads are asked whether a demanded value rests on them,
and a member joins the closure only through them, as a writer or a producer below, never for touching
what the occurrence touches (two readers of one location pass each other nothing).

The walk takes its demands in queue order while their steps run AHEAD on the planner host's cores
(`ClosurePlanner.CORES`, `Walk#ahead`, `#launch`, `#take`): the steps of the demands at the head of the
queue, two a core, start in queue order as cores free -- while the steps held weigh under a quarter of
the heap the old generation left free (`Walk#budget`, `Step#weight`), never one that a step before it
names as a successor (`Says#successors`: taking that one grows it) -- each against its demand's state as
it starts (`Step` holds that state: what the walk changes of a running step's demand it copies first,
`Demand#launched`; what only the demand's own take changes -- its naming, the handoffs it paired, the
reads it expanded -- the step reads in place, as the walk takes a demand only once its running step
ended), each a walk that mutates nothing it shares and says, in its order, what the
one-at-a-time walk changes there (a successor, a gap, a gap or fault-less door said once per key, the
occurrences offered once per key, a store version's earlier versions); the walk waits only for the step
it takes, starting others as steps end, and takes it while it is the walk of its demand's state then
(`Demand#version`), else walks the demand again itself -- so the plan is the one-at-a-time walk's, byte
for byte, however many cores ran it, and on one core no step runs ahead. What the walk decides in its
order and a running step reads to leave out what was said already (the gaps and keys said once, the
occurrences offered, the store versions expanded, the demands and the writes they absorbed) is held in
concurrent sets that only grow; a step reads its group's index, built on the planner's thread
(`Walk#reads`, each key's members an array replaced whole); one that threw ahead is walked again in
the order, so what the walk throws is what the one-at-a-time walk throws (an Error a step of the
demand's state now threw ends the walk). Inside one step, what
COMPOSE keeps of each path and delivery, the folds of its decisions, contributed values and fixed
point, and its expansions run in parts on the cores too, taken in order (`Walk#asked`, `#each`); once
the row-connected demand runs dry, the steps of the static candidates the bound still plans start
ahead, in the turns `Candidates#next` would give them (`Candidates#upcoming`, `Walk#prepare`), each
taken when its candidate is planned while it is still the walk of its state. Every memo a step reads holds a
function of its key, but one: a read row's leaves are held by its seq, which read rows share (a store
read and its view's), the first row asked giving the set (STATUS open defect 70); a step claims such a
seq where no one asked it yet (`Corpus#readLeaves`, `Corpus.Claims`), and its claims are taken in the
order (`Corpus#take`) -- one that claimed a seq taken by another row is walked again in the order.

A CONCRETE anchor (R1-ROOTS D0, `ClosurePlanner#concrete`) demands what it read before it decided.
An admitted path (the seed, or a focused session admitted whole) decided the anchor where it took
its arm: a reached anchor at its target row, on its phi; an unreached one on its decisions at the
flip sites (the way to the throw), the last of them where it left (none: it decided nothing on that
way). The anchor is concrete when some admitted path is at it, none observed the fatal, and none
decided it on a recorded symbol: every path COMPOSE takes is refused (§8, "decided concretely on
its healthy arm" or never reached) and nothing above names a value. An unreached path with a
symbolic decision on the way is not concrete, since flipping it is how a replay reaches the throw
(SOLR-18413's leader leaves at a concrete test of the boolean its clock-decided `isExpired`
returned). Its predicate reads are then the read rows its deciding predicate names, by read event
(`Corpus#readEvents` of phi or of the flip-site decisions' terms: a compound guard's phi stands at its
first test, and the reads of its later tests come after it -- hdfs-adhoc-26's cTime reads), and the
read rows the anchor made, in each admitted path,
before that path's deciding event, of the reads the root demand found on the throw's path guards
(SYMBOL-SCOPE §4.6; `StaticScopeMap#demandedAt`: a READ_SITE or READ placeholder stating its
`demandDistance`, joined on the method, the location kind and the type as `#carriersAt` joins; a
STORE read at a `PROVENANCE_SITE`, by its site, SYMBOL-SCOPE §5.7). Every anchor, concrete or not,
also demands the STORE reads it made at its provenance sites before it decided
(`ClosurePlanner#storeReads`): a store version's content is no value a term names, so a symbolic
predicate's demand never reaches it.
A later read cannot reach a decision already taken; an earlier one off the guards' cone reaches it
only through a read on it, whose writers the closure then asks. Their symbols are demanded like
those a symbolic phi names, so their writers become tasks flipped at their own guards and fault
sites. The demand tracks the cone's nearest reads however many flows from a branch (a String, a
reference, a container too), so they have read rows; a cell no region stores has no writer to ask
(the anchor then "read no shared state its path guards depend on"). The earlier reads off the cone
are counted, never dropped silently: `concreteAnchors` states how many
(`ClosurePlanner.Concrete#offCone`). A non-concrete anchor plans as before. Each demanded boundary input grows the closure:

- an attach whose symbol is demanded: its paired producer occurrence (reason `CLOSURE_MEMBER`, flip
  sites = the guards of the port's static export sites, contributed = its exports), and every activated
  occurrence holding a static export site of the port on the paired producer's node
  (`STATIC_CANDIDATE_PRODUCER`); an unpaired attach is `LINEAGE_LOST` (DIAGNOSTIC) and its static
  candidates are taken on every node;
- a read whose symbol is demanded: the writers `Corpus.eligibleWrites` names (the write of the observed
  version, and every other the one eligibility rule `Arms#eligible` admits: a write of the same
  session the read could have run right after -- its occurrence HB-concurrent, `Arms.concurrent`: not
  the same thread key, neither an anchor-chain ancestor of the other, both chains reaching a Root,
  neither Lost; every write between the two an HB-concurrent occurrence's; none of them under
  construction, a constructor or class initializer anywhere on its frame chain; no version between
  them a read observed and no row states -- or the location's INITIAL by the same test, whose
  expression's symbols are demanded and which is no task: no occurrence wrote it), and every activated occurrence on the reader's node holding a static write site of the
  location's carrier -- on any node when the reader or the holder is a client, a node the session's manifest
  names in `clientNodes` (PLAN's rule, `RuntimeSelectedRegionFinalizer#pairs`, `explore.Corpus#client`) --, unless the read's session states it holding other objects only
  (`STATIC_CANDIDATE_WRITER`; a heap location is one object's, and a store reaches only an object its
  occurrence holds: an occurrence whose recorded reads and writes name owners, none of them the
  location's, is no candidate; a static field, an owner that names no one object, an occurrence
  with no recorded access, or one that ran for its doors alone in that session (its rows state its
  doors, never what it touched) is, `ClosurePlanner.Walk#holdsOthersOnly`; PLAN's reachability and
  confinement filter, §3, is not applied here; `StaticScopeMap#carriersAt`: a
  recorded write joins a carrier in its method whose site stores its location's kind, `#stores` — a
  field store or an atomic's value a field, another mutator call a container's state, a read its
  field or a container field's state, no site an array element — and whose declared type may hold
  the row's: the same
  class, the bare sort, or, with no hierarchy at hand, value sorts that agree; a declared class no
  sort names holds any reference, and a runtime class no sort names may be a container, never a
  String or a box);
  a store of a reference among those writes that states a `referentState` adds the writers of each
  state of that container the read could have seen through it (`Corpus#referentStates`, COMPOSE's
  `SmtLowering#statesOf`);
- a STORE read (a guard's read of an object a store's fetch was parsed into, IDENTITY §7.2): the
  eligible row writers by the same rule, on any node (a one-JVM cluster's nodes are one session),
  and the writers of every earlier version of its location (`ClosurePlanner#storeWriters`,
  `#earlierVersions`: each write modifies the document before it, `RestsOn#closure`'s rule); each
  writer then names the doors of the queue item it took in (below); no static candidate; and the
  fetches of its location on the reader's node that PLAN stated on the target's data flow (the
  frozen plan's `storeFetches`, `StaticScopeMap#withPlan`, `ClosurePlanner#storeFetches`: a lost
  reply there registers no watch, so the node reads an older version), `STORE_FETCH`, contributing
  no value and not followed, flipped at their fault decisions as every task is;
- state reads a contributed expression makes (no ReadRow names them), and those of the anchor's own
  decision and fatal terms (`ClosurePlanner#anchorReads`, each term once): the same writer rule, through
  `Corpus.expressionStateReads`, each read's carriers named by its own VM site
  and type as a read row's are (`Corpus.StateRead#site`, `#javaType`): a read of a version no row
  wrote -- its writer ran paused, for its doors alone -- has no recorded write to name its carrier,
  and only its site makes the writer a static candidate, so a value demand that GROW unpauses
  (hbase-bugs-master-active-time HZ5: master0's activation wrote `HMaster.masterActiveTime` paused,
  `RemoteOperation`'s constructor read it at INITIAL inside the export of
  `OpenRegionRequest.initiating_master_active_time`, and the planner named the carrier of that read
  nowhere: T0 crossed as a constant, every world re-asked `throwOnOldMaster` under a key of its own
  host clock, and CONFIRM refuted the claims on that leaf);
- the doors of the message a demanded occurrence served (sender and receiver of its causal anchor's
  producer endpoint; every occurrence of the turn that sent it, on any of its threads and whatever
  its recorded place, a fault of which can stop the turn short of the send -- RestoreCmd's
  RESTORECORE requests before its ACTIVE offer; and every occurrence of a turn that took it in at
  its root, no occurrence open; `Corpus#doorsOf`, IDENTITY §7.2), each where a session recorded a
  fault decision of it (its fault
  point decides whether the message exists; the doors PLAN's `CONTROL_PRODUCER_V1` admits):
  `CONTROL_PRODUCER`, contributing no value. Any other door -- run under no planned task, a role,
  or one that decided no fault (hdfs-adhoc-28/29's heartbeat tick in a scope with no IPC client
  door, HG3: it waited as "only the seed replay ran this occurrence" and blocked the fixed point) --
  is one DIAGNOSTIC `ADMISSION_GAP` row and never waited for. Its reply legs too: the readers of the
  reply to every request a demanded occurrence sent, and, in turn, of the replies to what those
  readers sent (`Corpus#replyLegsOf`; a reply is a `<transport>#RESPONSE` message sent under the
  request's anchor, its readers the occurrences anchored on it), each that decided a fault
  (`CONTROL_PRODUCER`): a reply door decides whether the sender sees the reply wherever the reply is
  read. A synchronous client reads it in the sender itself (Hadoop IPC's `Client#getRpcResponse`,
  Solr's `HttpSolrClient#executeMethod`) or in the sender's own work anchored on the reply; an
  asynchronous one on its event loop, whose callbacks send the next request of the chain
  (HBase's `RpcConnection#finishCall`; Solr's `Http2SolrClient` listener;
  hbase-bugs-backup-lock-reply-lost: the lock's checkAndMutate goes out of the reply to its location
  lookup, and its own reply's door is the bug's fault).
  - A request counts as the demanded occurrence's own when it is sent by a recorded occurrence
    standing under it (`OccurrenceAddress#standsUnder`): the same node and causal context, the
    demanded occurrence's index a proper prefix of its index by frames. This is the work it
    registered or started that stands apart from it, chiefly a `CompletableFuture` continuation
    (IDENTITY §6), which never folds into the registrant's occurrence. PLAN takes these from the
    recorded activations of the occurrence's stance (`RecordedMessages#replyLegsOf`), EXPLORE from
    the corpus's occurrences of it (`Corpus#replyLegsOf`). A leg is still admitted only where it
    decided a fault.
  - Why: since continuations stood apart (0e146608a), the backup lock's checkAndMutate was sent by
    `AsyncSingleRequestRpcRetryingCaller#doCall`'s `addListener` continuation from a callMethod
    occurrence of its own at the registrant's address. PLAN planned the target alone, and the case
    fell from PASS to UNSAT_CLOSED (X214/X216-bak; the bisect is TODO HBase 11).
  - Measured on PLAN (planned tasks, before and after, IMPORT-only runs): backup-lock-reply-lost
    1 to 3, ns-rsgroup-removal 15 to 26, hbase-adhoc-04 61 to 69, hbase-adhoc-10 299 to 340,
    hbase-adhoc-22 123 to 115 (recording variance).
  Its own turn's earlier doors too: every
  occurrence standing where it stands (its node and causal context: the turn the message that
  started it began) that ran before it -- PLAN by the recording's root calls (an occurrence's first
  before the demanded one's last), EXPLORE by the rows of the first session that ran both
  (`Corpus#doorsOf`'s `earlier`) -- and decided a fault (`CONTROL_PRODUCER`): a fault there can end
  the turn before it (hbase-bugs-ns-rsgroup-removal: the master's hbase:meta Mutate in
  CREATE_NAMESPACE_INSERT_INTO_NS_TABLE precedes `TableNamespaceManager#cached`, the writer of the
  count the removal reads, in the same procedure turn). This only widens what is offered -- no
  recorded order removes a candidate --: the own turn's occurrences after it (or that ran in no
  session beside it) stay cut, as before, and both counts are DIAGNOSTIC `ADMISSION_GAP` rows
  ("earlier in turn", "own turn"). A control producer contributes no
  value, so the doors of the message that started it are not asked in turn (solr-18413 round Z7:
  six hops of request and queue-item doors behind the store writers' items doubled the plan).
  One door is a value: the SENDER of a message that started the writer of a store version a demand
  read, or of an earlier version of its location that one rests on (`ClosurePlanner#STORE_ITEM_PRODUCER`,
  `#writer`; PLAN's `STORE_ITEM_PRODUCER_V1`, `RuntimeSelectedRegionFinalizer#crossStore`, every writer
  up to the version a target read, `RecordedMessages#sendersOf`): the writer applied its item, so the
  version rests on the item's content, a key it removed as much as a value it set, which no content
  leaf carries to the reader (solr-bugs-overseer-lock-leak: the async MODIFYCOLLECTION's
  `readOnly=""` removes the property from state.json v6); so the doors of the message that started
  the sender are asked in turn -- the Overseer queue turn that took the task in, whose
  markTaskAsRunning door decides whether the task's Runner runs -- once: the sender's cells are not
  demanded, and those doors are control producers. A demand reached both as a door and as a sender
  is the sender (`Demand#absorb`: a connected value reason outranks a door's).

An attach or read no demanded value rests on is a DIAGNOSTIC gap, once per endpoint; so are the
diagnostics every replay repeats over objects of its own run -- a read whose carrier no write site names
(once per reader and field, an object's rid dropped), an unpaired attach, a recorded pairing its
consumer's anchor contradicts (once per consumer endpoint and producer) -- each as the first session
states it (solr-adhoc-39 PV7 round 5 said the no-carrier gap 75,333 times, a rendered address each). A region holds a
static site when the map's method set of the region contains the site's method or one of its callers;
with no method set, region-id equality. "Activated" means an instrumented activation row: an ambient
row (a port event outside every admitted activation, `RowRuntime#ambientActivation`) names where the
event ran, not a region that ran the site, so it makes no static candidate
(`ClosurePlanner#activated`); an ambient occurrence joins the closure only through the rows that name
it, or as the writer of a version no row wrote: a demanded read (a row's or a term's) that observed a
version no recorded write states -- its INITIAL, or one no row has -- was written by an occurrence that
ran unplanned, so every occurrence on the reader's node that ran with no instrumented activation and
whose region holds a static write site of the read's carrier is demanded as a value
(`UNRECORDED_WRITER`, `ClosurePlanner#unrecorded`, `Walk#holders`), unbounded like a member -- it has
no seed, so it is exposed to GROW, and one only the seed ran grows the plan alone (an `EXPOSED_REGION`
row in the seed's name and no obligation: no replay is re-run for it, §7.8) -- but for an occurrence entered in one of the system's
view classes (§3.4: a view's content is its store's, the chain's) and for a carrier a view class
declares; its rows state its doors only, so it is never judged to hold other objects only
(`Walk#holdsOthersOnly`). hbase-bugs-ns-rsgroup-removal HC9: the namespace procedure's group lookup
read `RSGroupInfoHolder.groupName2Group` at INITIAL, written by `moveServers`, which PLAN left
unplanned (the ZooKeeper chain's off-chain writers); offline its four occurrences are exposed
(Z3S-18413: 2 more exposures, tasks and proposals unchanged). For each session that read a version
no row wrote, the occurrences holding a write site of the read's carrier are kept
(`Plan#unrecordedWriters`); where the session is the seed or a FORCE replay and some of them are
planned now and ran unplanned there, the anchor's path in it is re-run
(`PathReruns`, an obligation ahead of the round's flips as FORCE is, one per path in flight, for
the writers no landed re-run of the path ran whole -- every round's growth proposed another, HC15-nsrg
15 in 20 rounds --, a DIAGNOSTIC `RERUN <obligation>` row naming them): the seed's as a `rerun` obligation on
its own world -- no query, the path's schedule cut, judged ADMITTED where the anchor's decision
(the target row's guard ordinal, else the path's last) takes its recorded arm again
(`ObligationSolverMain#rerun`), its focus row marked `rerun` so that arm is no flip of its world
(`ExploreCodec#readWorld`: the session stands in the path's world, at its depth) -- and a FORCE path as a FORCE obligation of its own id; its session
joins the corpus as any admitted session, and the next round flips on rows that name the writers
(hbase-adhoc-34 HZ12: the anchor's read of `allKeys` at INITIAL in the seed and the FORCE path, its
writer the region server's `start()` that only a flip leaving the anchor had re-run whole). A static site no session activated is a DIAGNOSTIC gap ("the retained set would have to grow"),
not a task. A decider the seed's closure left out for its class's planned first member (§3) runs
unplanned in every replay: no activation row names it, so it is no static candidate, and its class is
asked through the planned member. One anchor's walk scans one site's holders on one node once and offers an occurrence
once per (reason, site, guard set, node), whichever read or attach asks for it: asked again it is the
same demand, and folding it changes nothing (`ClosurePlanner#candidates`); the walk says each gap
once. Each demanded occurrence becomes a `Task` (id =
`digest("task|" + occurrence id)`, focused occurrence, state-connected factor, planned from the seed if
the seed captured it, else the first admitted session that did); its flip sites are its demanded sites
plus every fault site (`Corpus.faultSites`: a decision whose term reaches a root of the `FAULT`
category, by the same walk; a boolean configuration, hook source or READ placeholder is a MARKER
and no fault). A
demanded occurrence no session captured (ran, but no planned task admitted it) is: skipped if it is a
role (`ROLE.*`, `LINEAGE_LOST` when lost); skipped when its chain began at a daemon tick later than the
recording's last tick of that role on that node (`Corpus.tickPastRecording`, DIAGNOSTIC); *exposed*
(grown, §7.8) when an admitted focused session names it; *waiting* when only the seed names it
(DIAGNOSTIC, BLOCKING at the fixed point); BLOCKING when no session names it. An address already in
the plan that no replay ran again is a DIAGNOSTIC gap and neither grown nor waited for.

### 7.3 Obligation identity and the ledger: `explore.Frontier`

An obligation id is `ObligationFactory.obligationId` = digest of task id, site, ordinal, flipped
outcome and `dependence`, the arm's effect at the task: the task's own earlier decisions on the path
that share a variable with the guard, directly or through the task's own reads
(`compose.Independence.ofGuard`), each by its occurrence, site and outcome with how many different
conditions it decided there (`Corpus#decisionShape`: the stated term, reads by location; a poll
deciding the same condition again is one, a loop's iterations over another bound are not; never the
ordinal, which shifts with every earlier poll), plus the input shape (`Corpus.inputShape`). The inherited flips'
prefixes are no part of it (`FlipQuery` still asserts them): a prefix only adds conjuncts, so a
world's arm whose own path and input shape equal another's -- the input shape stating what each
member wrote at the guard's locations as the guard reads it -- is UNSAT where that one is
(solr-adhoc-07 IB1: a fault later in the task's own occurrence kept 13 decisions after the arm and
re-asked 979 seed arms); a reduced world's faithful NOT_ADMITTED (`WORLD_RAN:`) stands for the
parent world's arm too (STATUS open defect 59; an open decider arm whose every ask came back so ends
`OPEN_ARM_UNANSWERED`). The input shape:
whether the task's occurrence ran, its handoff sites and producers, and each factor member that
writes state it reads, named by its class (node, region, `Corpus#contextShape`; a producer too, never
an address's anchor hashes or counts), by what it delivered in this session: its handoff sites and
producers, its writes at the locations the guard reads (per site, each with what it wrote as the
flip query reads it, `Corpus#written` -- the rule: the key names everything the query depends on at
the task, modulo the run's own names. The written term canonical and digested: operators,
constants, roots by id, container subterms by their canonical bodies kept; an object handle's minted
digest numbered (below) and a read's event, version and owner dropped; a handoff by what binds it in the query (its
own run's wire arms the query states, `FlipQuery#arm`: each producer's class, export site, canonical
term, the path-condition predicates it states and roots' guard; with none, pinned to its arrival); a
read by its location's kind and slot and every writer the query offers it (`Arms#stateArms`: each
writer's class, write site and what `FlipQuery#delivered` takes from it -- its canonical term, a
free choice `?` (with the observed value where it is the observed writer) where the term states
nothing in particular, no choice `/` where it is a value of another sort; nothing bound: pinned to
its observed value). A term states nothing where it does not lower or names what the query cannot
declare (`FlipQuery#undeclared`), and nothing in particular where it holds an unsupported subterm;
a written term of either kind by the values the task's own reads of its version observed, the only
reads the query pins to a value through it (`FlipQuery#stated`), `?` where none did (an alternative
the query takes no value from; what another occurrence's read observed is no input of the query). A name a node has only in the
session's run (a host and port, a store session's id: the manifest's `runSpellings`) is named by the
node wherever the program spelled it (an observed value, a term's constants; never an engine-built
name), so a URL at another port names one node; a run's handle for an object -- an identity hash
(`<Class>@<hex>`, `RunSpellings#IDENTITY`), an object the VM named (`M_L'<class>'_<rid>`,
`VmRows#objectHandle`), a name the lowering minted from one (`identity__`, by its object) -- by its
class or kind and the order the key first meets it (`Corpus#handle`, `#numbered`), so objects
aliased alike fold and objects aliased otherwise name apart. No depth bound, and each naming
unit (a term, a container subterm) expanded once per session (`Corpus#step`, Tarjan's walk): a unit
no cycle runs through is its text; the units of one cycle (writers whose terms read what the others
wrote) are named when it closes (`Corpus#close`), each by the cycle's texts as it meets them, numbered
by first appearance from it (`cycleN`), so a name is the session's whichever unit a walk entered first
and two cycles name alike only as alike graphs (solr-adhoc-09 SC7: naming a cycle anew from every
entry was exponential in its depth, the planner 55 min on one round); a handoff's and a read's name
is held as a digest with its handles' marks (`Corpus#tokenName`), as a term's is: held whole, a chain
whose levels read the one before twice grew 3^n long (solr-adhoc-40 SL1, an 8 GB heap). A cycle whose texts times its
size pass `Corpus#NAMING_BUDGET` names each unit by its own reference -- no world folds through
it, its arms are asked again -- and the round names it (DIAGNOSTIC `ARM_KEY_NAMING_CUT`). A member flip that writes another
value there, a producer sending another term, a pinned payload of another value, or a term reading a
location another writer of another class may have written is another world; the same canonical
term written again folds) -- never delivered values, and a function of the session alone: semantic
counts only, the members, each one's writes and each one's producers as sets (replies to one call
arrive in any order; a poll, a request or a watch callback that wrote the same value k or k' times,
or under renumbered ids, delivered one world), a member's handoffs its distinct (attach site,
producer) pairs (`Corpus#handoffs`: hdfs-11741's distinct exports stay apart, the same field re-read
four or three times is one world; a ZK sequential node's ten-digit counter is numbered by first
appearance, `Corpus#sequences`, so `qn-0000000000` and `qn-0000000001` name alike), each a MESSAGE:
what a member or the task itself read of a store (a content port, `contract/ContentPort`) is a read, named wherever it
reaches the query, and a member with neither a message handoff nor a write at the guard's locations
is no line (solr-adhoc-19 SC6: members that read cluster state and wrote nothing the guard reads,
present in some worlds only, 32 ids of one arm; hdfs-11741's addKeys, fed keys by messages, stays a
line though the guard rests on none of its writes: the arm consumes them after the flip). The
handoffs the query states -- the guard's in its order, its kept conditions' as a set -- are named
by what binds them (`Corpus#handoffName`), so a member delivering the task another value there
re-keys with no line. A member that only wrote state the region reads
elsewhere is no conjunct of the query, and a world that changed it is reached by nesting from the
answer's session (§7.5), as an inherited prefix is (solr-adhoc-21 RX4: such lines -- a state watcher
or a client STATUS that ran in one replay only -- re-keyed half the re-asks). Known limits (STATUS
open defect 64): a member's write the recording states at no write site re-keys no arm, nor does
a member's store read that reaches the query by no read or handoff it states; the
downstream of a schedule variant (a member that ran in one replay of a world only) is not asked
again: schedules are not worlds. Never the session. An arm is
settled when some session recorded it under the same dependence, or an earlier round answered it
`ADMITTED`, `UNSAT` or a faithful `NOT_ADMITTED` (`ObligationResult#settlesArm`: its replay ran its
world as asked, `WORLD_RAN:`, or its query was refused at the arm, `ARM_REFUSED:` -- the flipped
predicate or the versions it read that no row wrote, all of which the key names, so every world
under it is refused alike; any other NOT_ADMITTED -- its world not run, or its query refused for what
the world holds (an inherited flip, a writer choice, the query's closure) -- settles only its own
flip, once a second one of it lands; `SAT_MODEL_READY` is no answer; an arm refused at the arm that
no run took stays an open arm, its refusal named on its row and its `OPEN_ARM_UNANSWERED`); an
`ADMITTED` replay also
settles its flip (`ObligationFactory#flip`) under whatever id the arm has since: a replay of that flip
of that path already took the arm in the path's world, and only the sessions landed since moved its
key (`Frontier#settled(Candidate)`; solr-adhoc-07 IB1: 59 answered flips re-keyed, 25 of them
ADMITTED). An UNSAT or NOT_ADMITTED answer settles its own id only. An arm in flight is not
proposed again, by its id or by its flip (`ObligationFactory#flip`: task, path, site, ordinal,
flipped outcome), since its id may move while it flies: sessions landing since its round grow the
dependence.
The ledger is rebuilt every round from the corpus, `obligation_results.jsonl` and the arms in
flight.

An id drifts as sessions land (the factor, and so the input shape, grows), so one flip is proposed
again under new ids (SOLR-18413 r5: 185 questions asked 717 times, 118 of the 166 re-asked with
byte-identical queries). Its **question** (`ObligationFactory#question`) does not drift while what its
answer rests on reads the same: `<flip>:<content>`, the flip (`#flip`: task, path, site, ordinal,
flipped outcome), then a digest of its query -- the sha256 of the text as its solver is asked
it (or the refusal that leaves none) -- and all its replay is given -- the world it plants (the path's world: roots, clock skews,
answers, inherited flips), the focused occurrence, the factor (a set) and the seed session of the focus row
(the schedule cut is the path's session cut at the focus and factor), the declared occurrence, and
the plan generation (a digest of the iteration's task plan, which GROW appends to and re-weaves
from). The solver builds it and looks it up in the questions this iteration's workers settled
(`ObligationDir#answered`); a settled one's answer is its answer, with no z3 and no replay (verdict
and detail name the obligation that settled it; an `ADMITTED` names no session, the session stays
that obligation's). A question is settled (`question.txt`) by a solver's own verdict or reused one
(`UNSAT`, a decided `NOT_ADMITTED`), or, for a SAT model (`question.asked`), by its replay's verdict
once the worker has it; never by a reuse (the obligation it reused settles it), a solver timeout or
an undecided solver (the held re-ask included), a replay killed on its bound, a replay that ended
without a publication (`RowRuntime#closeSession` withdraws the question), a solver that died, or a
worker that did not finish. A settled question stands only while its worker holds it and, for an
`ADMITTED` one, while its session is in the corpus (`ObligationDir#answered`).

**The solver key** (`explore/Solved`): what z3 decides of a query -- unsat, or sat and a model's
values -- is a fact of the query's text up to the names it declares, whatever obligation, world, task,
focus or plan generation built it. Its key (`Solved.Key`) is the sha256 of the text's CANONICAL form
(`SmtNames#canonical`): comments dropped (the task, path, session and symbol meanings a query states),
each run of whitespace one space, and every name a top-level `declare-fun`, `declare-const`, `define-fun`
or `define-fun-rec` of the text declares -- a root's, read's or handoff's variable, a writer choice, an
object's `identity__`, a `container_dag__`, a `view_leaf__`, each of which names a run's handles --
renamed by its first occurrence (`#0`, `#1`, ...; no name of a text begins with `#`), the fixed
vocabulary (`SmtNames.BUILTIN`, the preamble's names) and every literal as written: a string, a number, a
port, a clock reading stays as the run spelled it. Two texts of one canonical form are one formula under a
bijective renaming of their declared names (each declared name is renamed at every occurrence, and the
positions not renamed are equal token by token), so they are equisatisfiable and a model of one, renamed,
is a model of the other (KLEE's independent-slice cache, keyed by the lowered cone, §7.5's `FlipQuery#cone`).
The answer is kept under the key in the iteration (`solved/<key>.json`, its values under the canonical
names) once z3 decided it; every later ask of a text with that key (the first ask, the held re-ask, the
pinned asks of the nearest world, the hard lane's: `HardAsk#solvedKey` carries the key and the canonical
names of the model symbols) is answered with it, its values renamed onto the ask's own names, and runs no
z3: an UNSAT so answered settles its obligation with no z3 and no replay, as one z3 decided does; a SAT
answer is the model the ask plants, and its replay is still owed (the world differs after the flip, the
hdfs-11741 trap). A model value naming one of the text's declared names is not kept (`Solved#namesNone`:
its renaming would be the text's own). The answer is mapped for
each ask as z3's own is (`ObligationFactory#settled`, the model planted and checked for that
candidate), so a kept answer writes what a z3 run deciding the same writes, and settles its
question as that run would; the question stays its own replay key (the exact text's sha256). A kept
model is one model of the text, as a run gives one (each run races two engines). ONLY A WHOLE ANSWER IS
KEPT, OR ANSWERS AN ASK (`Solved#whole`): unsat, or sat with a value of every symbol the text asks the
model of -- a sat whose separate model run timed out, hit its cap or said unknown (`Z3#ask` keeps the
verdict) answers its own ask only, never later ones, which would read an empty model, plant nothing and
be refused for good; a timeout, a memout, unknown, an error or disagreeing engines say nothing of the
text, and the next ask runs z3 at its own budget and room. Keeping and reading are best effort: a store
that cannot be written or read (NFS) leaves the ask to z3. An entry is written whole (moved into place);
an ask that does not see it yet asks z3. Measured offline over the gen-1 study's Solr corpora, every arm
of a planned round at world depth 1 built as the solver builds it (`analysis/hbase-2026-10-19/reask/`):
Z3S-18413 round 2, 4103 queries, every text distinct (no hit by the text), 1470 canonical keys: 2633
asks answered from the store, 2054 of them UNSAT (settled, no z3), 579 SAT (the model handed on, the
replay owed); 299 of them solved again on their own text agreed, the 10 SAT models satisfied their own
texts renamed; solr-adhoc-39 round 5, 5526 texts, 4110 keys, 1416 asks from the store (1310 UNSAT), 164 re-solved
both ways agreed; hbase-bugs-master-active-time's 92 asks of depth 0 were 92 texts and 6 keys. z3 decided Z3S's
1470 keys in 38 s and 39's 4110 in 1363 s (the hits 37 s), and a worker that UNSAT settles takes ~2 s against minutes
for a replay, so what the store saves is z3 time: whether a re-ask is dispatched at all is the ledger's (its
dependence, above), and a SAT re-ask in another world is a pair world, whose replay depth > 0 asks for.

A WORLD IS REPLAYED ONCE (`DUPLICATE_WORLD`). A SAT model's focus row states its world, `world`: the whole-world
digest `ObligationFactory#wholeWorldDigest` of what the replay plants and is asked -- the root assignments (each
planted at the seed's mint of its root, a function of the root), clock deltas, answered handoffs, planted pairings,
the inherited flips and the flip itself (its focused occurrence, site, ordinal and arm), `ExploreCodec#readWorld`
over the row (`ObligationSolverMain`; a FORCE and a path re-run carry none: a FORCE forces an arm, a re-run replays
its path's world as more instrumentation asks). The head keeps the worlds it queued (`run_engine.sh`
`stream_worlds`): a SAT whose world a queued, running or landed replay already plants is not replayed; its result
is `DUPLICATE_WORLD`, naming that obligation (`campaign_stream_duplicate`; `exploration.json` `duplicateWorlds`,
`<obligation>:<the one replaying its world>`), an answered arm (`ObligationResult#settlesArm`) whose question is
answered too, and that replay's session is its answer. A replay that lands anything but ADMITTED (bounded,
refused, a path withdrawn, or run and not taking the arm, which the frontier asks again by its own rule, §7.3)
gives its world back, so the next ask of it replays: offline over NR1STOP-10, NP6-15, NC7-nsrg and NC5-22, no
world an ADMITTED replay reached is lost (NP6-15 976 replays -> 224, NC7-nsrg 192 -> 38, NR1STOP-10's 466 models
-> 188 replays). Sound in two parts: a replay is what it plants, and
the path a model was asked from sets only the schedule prefix the replay is held to, which is timing, no
counterfactual dimension (the owner's rule: worlds are planted values, never interleavings); and what the
instrumentation planned since the first replay adds is the closure's, which re-runs that session as for any
session (GROW, §7.8). hbase-adhoc-10 NR1STOP-10: the anchor path's two re-runs in the seed's world re-ran every
one of the 70 client doors, so each door fault was asked again from each re-run's path (412 asks, 140 worlds);
445 SAT models were 157 worlds, and 279 of the 315 fault replays queued at the stop repeated one.

### 7.4 Candidates: `ObligationFactory.candidates`

Paths of the task's occurrence, smallest world first, cut only from sessions that may parent an
obligation (`explore.Branches#parents`): the seed, or an admitted focused session whose branch did
not stop. The question is one declared occurrence `(r,c,i)`, and a focused replay whose run holds
no activation of the declared region `r` under the declared context `c` -- at any index `i`, which a
flip may shift (a fault's retry, a loop that runs once more) -- ran it under another chain or not at
all (`TASK_UNANSWERED`, `OCCURRENCE_ANCHOR_UNMATCHED`; a chain of the question's shape whose counts
alone differ, at an address the recording did not open, answers the declared occurrence at its address,
IDENTITY.md §9): its BRANCH STOPS. Its world is never
inherited, its paths are never flipped, and nothing it exposes is grown (§7.2's `uncaptured`: one
named only by stopped branches is DIAGNOSTIC); it stays in the corpus as evidence (its rows still
attest arms, §7.3). Contexts compare by `contract/ContextShape` (`Corpus#contextShape`, the rule
PLAN picks its walk origins by): per anchor hop the RPC site and the sending node, then the root's
role and api, without the per-site invocation counts; a sender no row names is unknown, never a
difference. Each stop is a DIAGNOSTIC `BRANCH_STOPPED` gap and counts in
the manifest's `branchesStopped`. COMPOSE and the claim stay on the exact declared address. A flip
candidate is a decision with a term (`FlipQuery.flippable`) at one of the task's flip sites, fault
decisions first; where the iteration has a ZooKeeper chain, a decision is one only where it rests on
a root, a message's field, a heap read or a chain read (`explore.ZkKeys`, SYMBOL-SCOPE §6.4) -- store
values off `zk_chain.jsonl` and decoded containers decide none --, the rest
counted in a DIAGNOSTIC `zk-keys` row; an arm's dependence names the reads its guard rests on that
observed a version no row wrote (`ObligationFactory#keyed`, `ClosurePlanner#unrecorded`), so the
arm over a path whose writers ran unplanned and the same arm over a re-run that recorded them are
two questions (hbase-adhoc-34 HZ14: the seed's refused #u79 settled the re-run's, which then held
the writers' rows); a term that names nothing classified is no off-chain decision
and is offered (`FlipQuery` decides it: hbase-adhoc-34's anchor guard read a map no row wrote, and
its arm was dropped as "off the chain" though no store value was in it). Bounds (`ExploreMain` options, defaults in `ObligationFactory`/`ClosurePlanner`):
`--max-tasks` 64 (static candidates; occurrences the rows connect are never counted, up to the
closure ceiling of 1024), `--max-paths-per-region` 32 paths per task, `--max-flips-per-path` 32 owed
arms per path, `--max-world-depth` 3 (flips a cut path's world may already hold). Every path is
keyed, and the path bound counts only the paths that offer an OWED arm -- one no ledger settles, no
round has in flight and no path before it offers: a path whose arms are all settled, in flight or
already offered is no path to cut from and is skipped uncounted, so the bound cuts new work, never
repetition (hdfs-adhoc-08 HG8F: of 15995 paths past the bound, 15670 offered nothing owed; the 325
others held 86 owed arms). It DEFERS, never drops: every round reads the task's paths again, and
once the paths before them are answered or in flight the deferred ones are the first that count, so
a fixed point defers nothing; EMIT names the bound only where the last round deferred
(`campaign_bounds`). Every
bound that drops work files a DIAGNOSTIC gap; settled candidates are filed as DIAGNOSTIC gaps too,
each arm once per task round. The planner builds no query;
an arm in flight is held by its flip (`ObligationFactory#flip`, §7.3), the first half of its
question.

**The pairing flip** (`explore.PairingFlip`, SYMBOL-SCOPE §6.4): a read of a node's VIEW of a
store location takes an older decode of that node. A node decides on whichever decode its view held,
and what a stale view changes is often no value a term names (a key an older document lacks, a
replica a loop skips), so no decision's flip reaches it. A task offers pairing flips where its
occurrence writes a STORE version or is the declared anchor's: for each view its occurrence read, or
its node read under its causal context in role work before it opened -- before its first row on the
session's one order, a tie at one seq included (a routed alias captures its view in the request's
role work and writes it in a store door's region, often with no VM event between) --, its earliest read is
offered each older version the node decoded before it in the session (on the session's one order,
`contract.RowOrder`: a decode and a read stated with no VM event between them in the order the engine
stated them; the view's INITIAL -- what the node held when the window opened, a decode before it,
stated at the view's first row in the window, seq 0 -- before every read), newest first, none older than
a decode the reader's own work (its node and causal context) made before the read -- the hold never
defers that work's own publications, so its view is at least that one's --, at most
`PairingFlip#PER_READ` (8); past them a `pairing-bound` gap, counted in result.json `bounded`
(`pairing_flip_per_read`). Its site is `PAIRING:<reader>` (`Obligation#PAIRING`, the read as CONFIRM
names its endpoint), its ordinal the version plus one (an ordinal is 1-based), its outcome taken, its
dependence constant; it counts
as a flip of the world (depth) and among a path's owed arms. No query is asked: the path is the one
its session ran, up to the read, and the world is that session's with the read paired to the decode
of the asked version (a view's writer is its version, `Confirmation#viewWriter`), held by CONFIRM's
rows (`ConfirmMain#holding`). The replay takes it where the read observed that version
(`FocusedReplay#pairedRead`); another version is `PAIRING_UNTAKEN` naming the one it saw -- and why, where its hold knows: overridden by whom, or given way at VIEW_HOLD_MAX (`Confirmation#untakenBecause`) --, and a read
that never ran leaves its occurrence unflipped (the prefix abandoned). A child inherits the pairing
as a pairing of its world, never as a decision to take.
A plain STORE read is offered the same way, only later: its earliest read of each location in the
occurrence (or its role prefix) is offered each tombstone of that location the session wrote after
it (`MessageDoors.TOMBSTONE`, a delete's write, IDENTITY §7.2; `PairingFlip#tombstones`, dependence
`STORE`) -- a znode's absence, which no term names (hbase-adhoc-24: `data == null` where the
barrier's read finds no node). Its writer is named by its version, `Confirmation#storeWriter`
(`STORE@<version>`): a store location has one tombstone per life, and the run that takes the
pairing may delete on another path than the session did (a timeout's finally block is another copy
of the call). The world holds the read past the tombstone: a `STORE_HOLD` row (§7.6), the prefix
cut before the read. A pairing of a store read with a version the session wrote before the one it
read is refused (`PAIRING_UNHELD`): no hold defers a store write.

### 7.5 One obligation: `explore.ObligationSolverMain`

The obligations of an exploration that run on one host are answered by ONE solver JVM there
(`campaign_solve_obligation`; `ObligationSolverMain --serve`, `explore.Service`, the one protocol of
a JVM that answers an exploration's questions in turn over state it keeps, the planner's too, §7.1:
questions on the serving host's own disk, oldest first, an answer `{exit, error}` whose error is the
deepest throwable): the first
question starts it if its host has room for a start's worth now (`campaign_start_solver`:
`campaign_solve_obligation` never waits for memory to start one), charged at the host ledger the
footprint of the heap it needs now (`campaign_solver_need_mb`, `campaign_jvm_footprint_mb`) for as long as it runs (it
holds the charge itself, `campaign_host_keep`, past the obligation that started it) and what its
resident memory grows past that as it grows, by a running JVM's rule (`campaign_watch_workload`:
refused only when the host's real use would pass the ceiling, and then the JVM is ended). Its heap,
and that of a question's own JVM, is its corpus's (`campaign_solver_heap_mb`): the corpus's session files as
they decode (`campaign_corpus_mb`: `campaign_session_bytes`, each gzip stream's trailer count, kept per
session beside the corpus -- a landed session never changes, so only a new one is read -- and stated for 60 s;
the solver's own retire check, `ObligationSolverMain#bytes`, counts the same) times `campaign_solver_live_pct`
(50 %: with the expression tables compact, the live set after a full collection was 35 % of them on
solr-adhoc-39 PV7, 3493 MB over 9974 MB, 46 % on solr-18413, 32 % on snapshot-no-active; 65-84 % as gson
trees) at `campaign_solver_gc_pct` (150 %) for the collector, at least 2 GB (`campaign_solver_now_mb`), and room for the corpus to double, up to the engine heap; it is charged the
footprint of what it needs now (`campaign_solver_need_mb`) and grows as watched. A solver that ran out of a
heap anyway (`-XX:+ExitOnOutOfMemoryError`, exit 3) states it beside the corpus (`campaign_solver_outgrown`,
`solver_outgrown_mb`), and every later one needs at least that. Started at a fixed 2 GB, 39's host solvers
died 20 times of "GC overhead limit exceeded" at 2, 4 and 8 GB (45 solver JVMs on 13 hosts, each a 1-4 min
corpus read), each death losing every question it held to a JVM of its own. A host's solver ANSWERS
SEVERAL QUESTIONS AT ONCE (`--seats`, `campaign_solver_seats`, eight; `explore.Service`: each on a seat
of its own, oldest first, beside the others only while its old generation was under three quarters
full after its last collection, `Service#BESIDE`, so a heap that fills answers one at a time; an
`Outgrown` question is given back, the service takes no more and retires once its other seats are
answered): one at a time, a solver answered about a question in 7 s (SGF8-adhoc-07: round 0's 400
solves on 12 hosts' solvers, ~1060 obligation-minutes queued). Each question solves over the corpus
it read or found read -- a read, one question at a time under the answerer's lock, builds a new
corpus from the one before and changes nothing of it -- IN A STATE OF ITS OWN over it
(`Corpus#asking`): each session's lowering fresh, as `Corpus#read` built it, made as the question first
lowers through it, and the literals a root's domain compares found through them (`Corpus#comparedLiterals`;
shared across questions, the first asker's lowerings took their side effects and the later ones'
did not); the arms a query refused are its thread's (`Arms#drainRefusals`); every other memo of a
corpus is a function of its rows and concurrent. So a question's files are the ones a JVM of its own,
reading that corpus, writes, whichever questions ran before or beside it. Its z3s run in the room
the solver holds for its seats (`smt.Z3.Rooms`, `campaign_solver_z3_mb`: `campaign_solver_races`, two,
questions' rooms), each run in slots of half a question's room (`campaign_question_mb`) as alone --
the cap and what a run at it answers are the question's -- waiting only for its turn at the room,
its budget counted from its start. A host holds no more of a campaign's solves at once than its
solver's seats (`campaign_stream_has_seat`), and a host where no solver of the campaign serves yet
only one -- that solve starts its solver -- so no question is admitted to wait behind a starting
solver: more add no answer, only their question
charges while they wait in the solver's queue (EX1-adhoc-07c: 13-18 per lift, 512 MB each, held 7-9 GB
of every lift's ledger), and past the solver's patience they became solver JVMs of their own
(PV7-adhoc-39: 113, "busy past 30s", each reading the corpus again); the rest wait uncharged in the
pool's queue (§7.7). Charged that at its start, a solver waited for room it did not use, and every question of
its corpus waited behind the start (round x1, eleven cases at once: 50-75 minutes). It takes the
questions in the order they came, each from the corpus as it read it: read again only when the
question's round was planned over a session the read did not hold (the round's `corpus.txt`, of the
sessions still standing; `ObligationSolverMain#round`, `#stale`), or a session it held has left (a
round's question needs no session that landed after it was planned, and the head lands sessions every
few seconds; a re-read of 39's 208 sessions takes 10-16 s), each session the read before already holds
taken from it unread (`Corpus#read(Path, Path, Corpus)`: a landed session's rows never change, and
reading them is the read's whole cost, 45 s over hdfs-11741 i1's 175 sessions), else the corpus as read
(`Corpus#freshLowerings`) -- so each obligation's files are the ones any solver, reading that
corpus, writes -- into a directory on the host's disk, named by the corpus, that the asking worker moves
into its worker directory. A read past what its heap holds (`campaign_solver_retire_mb`, its
`--retire-past-mb`; none at the engine heap) is not made: the solver gives the question back untaken and
ends (`Service.Outgrown`, `Service#retireOutgrown`, naming itself in `retired`), and the question's asker
starts the next one, sized anew. It ends once none has
come for `campaign_solver_idle_s` (300) and none waits; a question still `.taken` then was taken by a
solver that died (it retires only while none of its seats answers), its asker's to fail, and never keeps it (`Service#retire`: a
run stopped mid-answer left one, and the next run of that corpus path kept its solver and charge 2 h past
its end). Its log is `solver-<host>.log` beside the corpus. A
question still waiting when its solver ended starts the next one. A question that waits for its
solver says so after a minute and every ten minutes after (`campaign_solver_wait_said`). A cold
host's question is charged a solver's start (§7.7), and the solver it starts takes that charge over
whole (`campaign_start_solver <dir> <sessions> <charge>`: the ledger row renamed, held by the solver,
so the start's release drops nothing): the host is charged one solver, never two -- charged a second
beside the first, no cold host of SGF7-adhoc-39 (21 GB of sessions) had room, and 24 questions read the
corpus in JVMs of their own, 14-21 min each, their hosts never warm. A SOLVER IS SIZED BY WHAT SOLVERS MEASURED: after each corpus read a
solver states its live set after a full collection beside the corpus (`<iteration>/solver_live/`,
`ObligationSolverMain#stateLive`), and later solvers of the corpus take the share of its text the read of the
largest corpus held (`campaign_solver_measured_pct`; 11-15 % after compaction, 50 % before any measure, and
for a composer always).

**NO QUESTION IS ANSWERED IN A CORPUS JVM OF ITS OWN.** A question whose host had no room to start its
solver now (`campaign_solve_obligation` 3), or that its solver took and ended on or failed (1), is no
answer: its worker asks it again (`campaign_obligation_again`: `solve_again`, why, no answer) and
returns, and the head queues it again as an OBLIGATION (`campaign_stream_solve_again`,
`OBLIGATION <round> <id> again`), uncharged while it waits, its host cold, the obligation in flight. A
question asked again whose solver ends on it or fails again fails the worker by name (`asked_again`,
§7.7) -- but a SOLVER THAT ENDED FOR MEMORY (out of heap below the most heap a solver is given, the next
starting at twice it; or ended by its watcher for its host's room, 137) fails none of the questions it
held, eight at once (`campaign_solve_obligation` 4, `campaign_solver_ended_for_memory`, its end stated
in `<solver dir>/ended.<pid>`): each is asked again uncounted, at most `campaign_solver_memory_asks` (4)
times, then counted (`asked_again_memory`). Only a solver no host of the pool can ever hold -- its start's charge
(`campaign_solver_need_mb`) past every host's ceiling less the largest head reservation standing there,
idle or busy (`campaign_pool_can_hold`, `campaign_host_head_reserved`; a waiting step's hold, which comes
back, is none) -- is an answer, the named bound: NOT_ADMITTED "no host of the pool can hold its solver
of N MB", with an `OBLIGATION_UNFINISHED` gap row; there is no time bound, which would drop a starved
solve again (SGF5, 2026-10-14: a solve that placed itself from inside its start waited at most 600 s,
and on a pool charged past its real use its obligation was answered NOT_ADMITTED for good -- 4 to 69 per
case, 18413's witness among them). The ask is written before any row it left is removed, and a head
that still sees such a row reads the ask (`campaign_await_remote_result`). None settles a question
(`question.txt`/`question.asked` are removed).

**The solve's two lanes.** Every question is first asked at `campaign_solver_first_ms`
(`campaign_solver_first_tier_ms`, 60 s, never past `solver_timeout_ms`): the host's solver is started
with that budget. A question undecided at the first budget (`SOLVER_TIMEOUT after <first> ms`) -- or at
its z3s' cap (`SOLVER_MEMOUT at <cap> MB`, whatever the budgets) -- lands nothing: its ask left its
record beside its query (`obligation_ask.json`, `explore.HardAsk`: the question, the gaps its build
stated, what an UNSAT says, the model's constants, the query's sha256), and the head moves its answer
aside (`obligation_result.first.jsonl`), keeps the obligation in flight, and queues its HARD-LANE ask
(`campaign_stream_hard`, `stream_hard`, `HARD <round> <id>`), which `campaign_stream_dispatch` starts only
once no other start waits: z3 ALONE over that query
at the full `solver_timeout_ms` and the hard lane's z3 room (`campaign_hard_z3_room_mb`, 4096 MB), in a
JVM that reads no corpus (`campaign_obligation_decide`, `ObligationSolverMain --decide <worker>`, a
512 MB heap, `hard-host.txt`), charged that and the room (`campaign_decide_need_mb`, 5024 MB), as many at
once on a host as its cores and ledger room hold (§7.7). It answers as the corpus's ask maps an answer
(`ObligationFactory#settled`, the one mapping): UNSAT with the record's detail and gaps, settling its
question; undecided NOT_ADMITTED by name; a sat answer leaves its model (`obligation_model.json`,
`HardAsk.Model`, the budget and room it was asked at) and asks the obligation again of a host's
solver (its diagnostics `again-host.txt`, `again-std*.log` beside the first ask's), which builds the
query again and finishes the flip with the model where the query's sha256 is the record's (the planted
world, the held re-ask at the hard lane's budget and room, the focus row: the code after z3); a query
the corpus moved is refused by name (`HARD_MODEL_STALE`), with no replay and no re-ask (owner
2026-10-15: whatever spares a solve or a replay is kept, as long as the case gets its `.smt`), a
world-only answer as any refusal of its world. A record over another query or obligation is refused by
name with no z3 run (`HARD_ASK_MISMATCH`). Since the
obligation stays in flight, no fixed point is declared before its hard ask, nor does a stop end the
exploration with it unasked (`campaign_stream_idle` counts the hard lane). One undecided there lands
NOT_ADMITTED (settled, never asked again) and is named in `solver_timeouts.jsonl`; EMIT makes each a
`SOLVER_TIMEOUT` or `SOLVER_MEMOUT` ADMISSION_GAP row (`campaign_solver_timeouts`), BLOCKING under any
claim but a SAT_CANDIDATE: a RUN_DEFECT, counted in `defects[]`. Why the two lanes (SP4-10,
2026-10-12): the answered questions took a median 1 s, p90 4 s, but 12 READ-door and routed-alias flips
ran their z3 races 1000-1180 s of the 1810 s budget inside their hosts' solvers, and the 292 questions
queued behind them waited up to 1135 s. Why z3 alone (SGF7-adhoc-39, 2026-10-15): each hard ask was a
corpus JVM of its own, 18-21 GB charged, one per host, reading 21 GB of sessions for 15-20 min before its
z3 started.

`ObligationFactory.locate` finds the published obligation's path in the corpus under its round's id
(a path gone from the corpus is `NOT_ADMITTED`). `FlipQuery.build` asserts the path as its replay ran
it up to the flipped decision, the flipped decision negated, and every inherited flip's prefix through
its flipped decision (`Arms.conjunct`/`Arms.pathCondition` apply the recorded polarity; terms are
lowered by the one lowering, `compose.SmtLowering`). The query states exactly the declarations, facts
and preamble lines its texts reach in each lowered session's lowering (`FlipQueryText#statedDeclarations`,
`FlipQuery.Builder#unbound`, `#stateFacts`): its texts are read once per ask (`SmtNames.Named`) and
each lowering walks from the names it holds (`SmtLowering#reachedBy(Named)`), the preamble reached
once per distinct preamble -- read again per lowered session, solr-adhoc-39's 20 MB query took
220-283 s to build and its z3 run 1.3 s (PV7), now 8 s, the query byte-identical. A fact stands where
every name it states is reached or is a shared term (a long text named once, `term_dag__`/
`defined_dag__`) whose body's names stand (`SmtLowering#facts`, `#stands`): a term's definedness past
2048 characters is such a shared name, which no text of the query names, so it was dropped -- an
`Enum.valueOf` over a case conversion (`Slice.State.getState`) lost "the name is one of the constants",
and z3 chose states "", "l" or "MP" (SGF8B2H-adhoc-14: 31 answers-only flips at `DocCollection.<init>#u102`,
none admitted; offline over its round-0 corpus, all 7 re-asked now name a constant). Each symbol it
names gets one rule:

- ROOT: a declared MARKER is a free Bool; a CLOCK is one variable per (root, session) with domain
  `[host reading, host reading + 30 days]` in its own ticks (`RootMintRow#hostReading`: the mint's
  instant less the skew its node's clock ran at there; `JavaPrimitiveSmtSemantics.clockDomain`/
  `clockSkewCeiling`; no reading: `[0, Long.MAX]`; declared clock bounds are not read here), and its
  nearest world is the instant the session ran it at; within one session, a cell is no earlier
  than the cell before it (by seq) on the same clock of the same node, giving way where the session
  read the two the other way round (`FlipQuery#clockOrder`, COMPOSE's `clock_order__`), so no model
  jumps a clock forward and back, which a replay would plant as asked and no composed world is
  (hdfs-11741 L1: `be888ea2` +10 h, the next cell at the host's reading); any other root takes its domain from
  `root-domains.jsonl` (or the mint's), else is pinned to its recorded value.
- HANDOFF: an attach of the focused occurrence (a *control*) is bound per slot by
  `OR(pi_q ∧ guard_q ∧ v_H = e_q)` over `Arms.wireArms` (nested slots closed); a paired control whose
  every arm is dropped refuses the query (`UNPRODUCIBLE_ANSWER`); an unpaired one is free and listed
  `unproducible`. Every other attach (no answer is planted there) is bound by the arms of its own
  run only, nested slots closed the same way, so it moves only with the roots and clocks the replay
  plants (SOLR-18413: the leader parses a routing rule's expiry in its state watcher, and the expiry
  is the Overseer's clock plus the timeout); with no such arm it is pinned to its recorded arrival.
  Another run's arrival never binds it.
- READ: the eligible writers (`Arms.stateArms`, the location's INITIAL among them, the writer at
  version 0) become one Bool selector each (`wchoice_*`, exactly one), one choice per (reader
  occurrence, location) binding every read of it, so a writer's choice is the run only where every
  read saw that writer's one write; where the reads saw several writes, or a version no row wrote,
  one more selector, the run's own (`wchoice_*_run`, `FlipQuery#choices`), holds each read to the
  value it read (its observed write's delivery, else its row's `concreteValue`; neither refuses
  `UNSTATED_VALUE`) and is the recorded pairing, as COMPOSE's observed arm is (§8): a model taking it
  plants nothing, `heldToRecording` asserts it, and the writer choices stay beside it, less those a
  read of another version could not have seen (`Arms#eligible`); by COMPOSE's gate, only where a
  writer left is HB-concurrent with the reader, else the block is no choice and each read is held
  to the value it read; a writer
  whose write lowers to another sort than the read delivers nothing it could be and is no choice
  (`ARM_SORT_MISMATCH`, the recorded one excepted); no writer:
  pinned to the row's `concreteValue`; neither: refused `UNSTATED_VALUE`. A scalar read of a field or array cell
  of the flipped occurrence (not a container's state or a query of one) with more than one
  eligible writer is its own symbol, as COMPOSE keeps the anchor's
  (`FlipQuery#movableReads`, `SmtLowering#rowSymbol`): inlined, the VM's guarded read is the
  written value, a constant no selector moves (hdfs-bugs-slowdisk-zero: the detector turn's
  `maxSlowDisksToExclude <= 0` over the reconfiguration's 0 and its INITIAL 1). A read of a node's
  VIEW (SYMBOL-SCOPE §6.4) with more than one eligible decode is marked movable too
  (`SmtLowering#movable`), so a content leaf the path read through it lowers as the leaf of
  whichever decode its selectors pick (`SmtLowering#throughView`): a flip on such a leaf moves the
  view's pairing, which a model plants as any writer choice.
  Only reads the text names are variables: a container state behind a guard is inlined by its join
  (the closure demands its writers, §7.2), so the query declares nothing for it — a variable bound
  to each writer's state would constrain nothing, and its equalities over states built by removals
  (lambdas) are outside what z3 decides (`unknown`, "incomplete (theory array)").

An undeclared name in the flipped conjunct refuses the query (`DECLARATION_MISSING`); in a prefix
conjunct it drops the conjunct (DIAGNOSTIC); a malformed lowered term likewise. A name is declared
when the query declares it, a `let` binds it, the fixed preamble states it, or it is a theory
operator of `compose.SmtNames.BUILTIN`, the one vocabulary every stage reads with, which lists every
operator the lowering writes (the string operators `str.substr`, `str.indexof`, `str.at`,
`str.from_code`, `str.to_code`, `str.in_re`, `re.*`, `re.range` of `String.trim`, `re.union` and `re.++`
of `equalsIgnoreCase` against a literal among them, the
preamble's `java_ascii_lower`/`java_ascii_upper` of `String.toLowerCase`/`toUpperCase` (VM.md, String row),
the floating-point operators, `to_fp`, `int2bv`, `bv2int`
and the `Array` sort); COMPOSE refuses a path on the same test. The preamble states z3's alphabet as
Java's, `(set-option :encoding bmp)` (`VmTermLowering#JAVA_CHARS`: every character a UTF-16 code
unit), so a `charAt` is a char wherever its definedness (`0 <= i < length`, on its path) holds and no
query bounds the characters it reads (an unguarded range per `charAt` held every index below its
string's length on every path: solr-bugs-snapshot-no-active Z2K, 13,188 lines, 44 of 46 MB,
undecided; with the alphabet, sat in 1.8 s). A lowered text past 2048 characters -- a value's of
any sort but Bool (whose atoms the clock margin reads), a definedness, a String's nullness -- is a
`define-fun` the query states once and every use names (`SmtLowering#compact`, as container
subterms and view leaves are): an operation writes its operand's text by value, a substring its
receiver's four times, so a chain of them grew fourfold per level (solr-adhoc-10 SL2: a parse of a
handoff's string, texts of 2.6-9.6 GB). A symbol no rule binds
refuses (`UNPRODUCIBLE_ANSWER`); a query whose flipped predicate reaches no variable of its own --
none it names, none a definition it rests on names (`FlipQuery#flipCone`) -- is not asked, whatever
variables a prefix decision binds: by the owner's ruling (only SAT or UNSAT; a concrete value is a
constant) its other arm is UNSAT on that path, named `NOT_FLIPPABLE` (`FlipQuery#NOT_FLIPPABLE`,
`ObligationFactory#solve`), unless its occurrence read a version no row of the corpus wrote and no
placeholder read of its session mints (held at what it read, its producer unstated,
`FlipQuery#heldReads`; a version a mint states is its root's, as invariant 7 and the lowering's read
binding take it -- ZA8-cont's six Prep flips were refused only for the program's own
`Long.longValue()` read of a clock mint's box): that refusal stays (`ADMISSION_GAP`,
DIAGNOSTIC), the scope hole being real; one that reaches only leaves a frame's
write was freed to (`SmtLowering#framedLeaves`: the writer computed on an arrival it refused, so no
plant reaches them) is refused before it is solved (`UNPRODUCIBLE_ANSWER`, DIAGNOSTIC, named). A construct the
lowering refuses inside a stated term becomes a fresh `unsupported__*` constant of its sort and stays
in the query. Demanded conjuncts (the flip and the inherited flips) get a one-minute clock margin on
each comparison atom over a clock whose polarity `not`/`and`/`or` resolve (`explore.ClockMargin`;
an atom it cannot strengthen is a DIAGNOSTIC gap). The objective is the nearest world:
`minimize Σ|x − recorded(x)|` over bounded Int roots and clocks (`FlipQueryText`). For every other
sort the nearest world is taken after the answer (`explore.NearestWorld`): each root and each control
handoff the model plants that the flipped predicate does not name (`FlipQuery.Built#flipVariables`,
its own text and the definitions it reaches) is pinned to the value its path's run had
(`Built#recorded`: the root's `Corpus#rootValue`, the attach's `VmTermLowering#received`) and the
query asked again; if it is sat that model is the one planted, else each is
pinned in turn and kept where the query stays sat (a hard lane's model tries all at once only), so a
leaf the flip needs keeps the solver's value. Pins only add conjuncts: a model under them is a model
of the query. solr-adhoc-14's 31 `DocCollection.<init>#u102` flips planted `""` for the other slice's
state and its ranges, and every replay failed at `Slice.<init>`; they now plant 573 leaves at their
recording and move only the flipped slice's state (`analysis/solr-2026-10-18/explore/nearest/`).
THE QUERY IS THE FLIP'S CONE (KLEE's constraint independence, `FlipQuery#cone`): what it asserts --
prefix decisions, inherited flips, writer choices, root and clock domains, stated facts -- is split
into top-level conjuncts (`and`, `not not`, `not or`; `FlipQuery#conjuncts`), and only those that
share a name with the flipped conjunct, closed to a fixed point, are stated: a variable of the query,
or a declaration it states, which shares every name its definition reaches (a conjunct naming a
container shares what the container is built from, never what is only built from it); a preamble
function (`assoc_*`, `string_ref`) shares nothing, and a conjunct naming neither (constants alone) is
kept. A dropped conjunct shares no name with the cone and holds at the recording's values (a prefix
decision as run, a writer choice's exactly-one at the run's choice, a domain or pin at what was read,
an inherited flip as the session's world ran it, a stated fact as recorded), so the cone UNSAT is the
whole query UNSAT and a model of the cone, every dropped name at its recorded value, is a model of
the whole: only the cone's variables are declared, minimized and read back, and no dropped root,
clock, handoff or writer choice is planted. The hard lane asks the same text. SOLR-18413's witness
flip (`RoutingRule#isExpired`): 8 of 245 conjuncts, SAT at once with MigrateCmd's clock +243 s,
where the whole query, ZkStateReader's map bookkeeping sharing nothing with the flip, was "unknown
(incomplete (theory array))"; on its corpus the four flips undecided that way decided, ten decided
ones answered alike, queries 474 KB -> 7 KB.

z3 runs with `solver_timeout_ms`, which its driver (`smt.Z3`) enforces; a JVM that ends takes its
running z3 processes with it (a shutdown hook), every z3 is started under `setpriv --pdeathsig
KILL` (`Z3#DIES_WITH_ITS_DRIVER`), so the kernel kills it when the JVM thread that started it is
gone however the JVM ended (a KILL runs no hook), and each z3 also carries its own hard timeout ten
seconds past that budget (`-T`, `Z3#hardTimeout`), for a driver that hangs. EVERY z3 RUNS UNDER A
MEMORY CAP its JVM's charge covers: a JVM that starts z3 is told its z3 room R (`--z3-room-mb`,
required; `smt.Z3.Room`) and charged its footprint and R; each of its z3s holds a slot of R and starts
under z3's own `memory_max_size` at the slot less 64 MB (`Z3#MISSED_MB`: what z3's accounting does not
count; on 4.14.1 a capped z3 stayed within its cap at 1-2 GB and 12-20 MB past it at caps of tens of
MB, and stops printing `(error "out of memory")`, exit 101), and a run starts only while its two
slots fit in what R has free, in the order the runs asked (`Room#take`; a run alone always fits).
A z3 at its cap answers nothing: a run whose output holds the cap's line is `memout` unless its
verdict AND the payload its command asked for (a model's values, a core) were printed before it
(`Z3#decided`), so a core cut by the cap is unknown, never empty, and a model cut by it loses the race
to the other engine's. A model or core run at its cap in a slot shared with other asks, after a verdict
that fit, is that run once more alone, in half of R an engine (`Z3#payload`: a verdict with no model
selects no path); a verdict at its slot's cap is `memout` there (`Answer#memOut`): undecided by name,
as a timeout is, never sat or unsat and no error of the query (an error voids a composition's claim),
its reason the cap it hit. A host's solver's R is the room its seats share (`campaign_solver_z3_mb`:
two questions', each question's runs in slots of half a question's `campaign_question_mb`, 1152 MB --
its two engines 512 MB each -- as alone, `smt.Z3.Rooms`), in the hard lane `campaign_hard_z3_room_mb` (4096: 2 GB each); an obligation at
its cap is NOT_ADMITTED `SOLVER_MEMOUT` (a DIAGNOSTIC row of that kind) and asked again in the hard
lane whatever the budgets, and one at the hard lane's cap is named as a hard-lane timeout is
(`solver_timeouts.jsonl`, EMIT's `SOLVER_MEMOUT` row, `campaign_solver_timeouts`). Every run, here and in COMPOSE, is two z3 processes, one per arithmetic engine
(`smt.arith.solver` 2, the one the query states, and 6; `Z3#ARITHMETIC`), and answers with the
first that decides, killing the other; the stated engine's answer wins when it decides within as
long again as the other took (at least a second), so what it alone decides promptly answers as it
did alone, and an undecided pair is undecided (`Z3#run`). Each engine's z3 is told its engine
first and reads the query through `Z3.EngineWriter`, which replaces the option the query states as
the text streams (the later one would win); the query is never copied per engine. z3's time on one query swings by orders
of magnitude with the engine: SOLR-18413 r9's composed query ran past 30 minutes under 2 and is
sat in a second under 6. Timeout (`SOLVER_TIMEOUT` gap), `unknown` or error →
`NOT_ADMITTED`; unsat → `UNSAT`. On sat (`ObligationFactory.solve`): roots the assertions reach are
read back by root id, the flipped path's clocks as skews (`model − host reading`; one outside a Java
long refuses), controls as answers keyed by attach endpoint id (`ObligationFactory#answer`: a String
control as its JSON string literal, which the replay plants verbatim; one whose model value is no
string literal refuses, `NOT_ADMITTED`). Every recorded value a query pins
(an arrival, a read's `concreteValue`, a root) is a literal of the sort its variable is declared at
by COMPOSE's one rule (`SmtText#literal` → `VmTermLowering#smtLiteral`); an attach's value is read
as COMPOSE reads it (`VmTermLowering#received`: the answered value, else the arrival, a String's
text whatever it begins with), so a String handoff no arm states is pinned to its arrival. A writer choice the
model sets away from the writer the recording's reads observed, the location's INITIAL among them,
is a **planted pairing**, counted like an answered handoff (`ObligationFactory#planted`: reader →
writer, each as CONFIRM names them, `Confirmation#writer`; one of a read another session made refuses,
`PAIRING_UNPLANTABLE`). A pairing is planted only where the recorded ones take no flip: a model
that moves one is asked again with every writer choice held to the recorded writer
(`ObligationFactory#heldToRecording`, under the nearest world's pins; a container state follows its
writer's, and a refused term
`unsupported__*` has no recorded value and stays free), and a model that then plants something is
the one issued. An open decider arm's flip -- the decision a run that left the arm open asks,
flipped TOWARD the arm, away from what that run took (`Corpus#openArmFlip`; the same decision
flipped the other way is an ordinary flip) -- is asked without each world a replay of it refuted
(`Corpus#refutedWorlds`, by the flip's `ObligationFactory#flip`): one `(not (and ...))` per world,
exactly the world it ran -- every writer choice at the selector the world moved it to, else at the
recording's; every root at the world's value, else at the reading its path's session ran; every
clock at the instant its skew put it at, else at its host reading; every answered handoff
(`ObligationFactory#excluded`; a choice the query cannot state is left out) -- and its UNSAT says it
rests on them. A model whose whole world (`ObligationFactory#wholeWorldDigest`) is one already
refuted is never run again, and past `MAX_REFUTED_WORLDS` refuted worlds the flip is refused
(`OPEN_ARM_MAX_REFUTED_WORLDS`, the arm BOUNDED, §7.1); its focus row carries `openArm`, and a
refuted world's question is never reused. A model that plants nothing its path's session did not run -- no moved clock, no
answer, no pairing, and every assigned root at the value that session minted -- would have its
replay run that session's world again, and is refused before any replay (`NOT_ADMITTED`, a
DIAGNOSTIC `ADMISSION_GAP` under `EXPLORATION`). Assigning roots, all at their recorded values, it
names the polarity or binding fault that implies; assigning none (`EMPTY_WORLD`), it names the
symbols it sets that no replay plants (container states `st__*`, refused terms `unsupported__*`).
The parent world is overlaid (model wins: roots, skews, answers, pairings) and its flips inherited.
Every assigned root must have a mint in the seed session (else `ASSIGNMENT_UNMINTABLE`,
`NOT_ADMITTED`). The world's pairings are held by CONFIRM's rows over the session the path was cut
from (`ConfirmMain#holding`, §10: a `STATE` row per paired read, `ORDER` rows that realize it --
for an INITIAL every writer of the location after the read; a writer the read must precede waits for
the reader's occurrence to close, since the choice binds every read it makes of the location and
the flipped world may read it again, CONFIRM's for the read's activation; for a plain STORE read
held at a tombstone -- paired with a later one of its location (§7.4), or a read of a world that
took the pairing, which CONFIRM replays from the recording's schedule, where it reads the version
before (X104-24: two claims refuted, the run read v0) --, one `STORE_HOLD {reader, readerOccurrence,
location, version}` row: the reader's first `READ` turn of that location in that occurrence
(`MessageDoors#reading`, before the store's call) waits until this run has written that version
(`Confirmation#storeReading`), at most the order timeout (300 s), past which the read goes on, the
hold is unrealized by name (a CONFIRM mismatch) and the read, which then finds another version, is
`PAIRING_UNTAKEN` ("was never written"), so a run that never deletes refutes the pairing and never
waits for ever; the read is then compared by version, its STATE row's writer `STORE@<version>`; no
schedule slot is held (a watch callback's work takes none), and REPRODUCE plants no `STORE_HOLD`
natively (TODO HBase 10); for a node's VIEW, whose
decodes run in work no activation hook holds -- watch deliveries, request handlers --, one
`VIEW_HOLD` row instead: the node's PUBLICATIONS of the view past the paired version are deferred,
not its threads (`MessageDoors#publishing`, at Solr's `ZkStateReader#updateWatchedCollection`,
`ZkStateReader.StateWatcher#refreshAndWatchChildren` and `AliasesManager#setIfNewer`, a per-system patch;
`Confirmation#publishing`): on a thread delivering a store's notification -- the whole callback, after
it read its cause too -- the thread goes on, every reader on the node keeps the version it had, as
behind a slow callback, and once one publication of the view is deferred every later one of it
follows it, a removal, a same-version per-replica-state update and a recreated path's (the queue is
per path, not per store life, `Confirmation#queueKey`) too; the node's one publisher
applies them in the order they came, each once the holds it waits for end, under the notification's
scope and the locks the system's own publication takes. Nothing holds the thread's next notification:
Solr runs each watch callback on a cached pool, so a slow callback delays no other event, and a thread
waiting for its own deferred publication re-created the blocked hold's deadlock (round Z2Y). A
synchronous publication -- the system's own refresh, Solr's `forceUpdateCollection`, a lazy
collection's fetch, and the refreshes a caller reads right after on its own thread, even inside a
callback (`ZkStateReader.StateWatcher#refreshAndWatch()` with no event, `AliasesManager#update`), each
inside `MessageDoors#refreshStarting`; one on a thread delivering no notification; or the reader's own
work's (its node and causal context) -- is never deferred: it read the store after the
deferred ones, so it drops the deferred removals and what came before them (`Confirmation#published`),
and the rest publish nothing older over it, by the system's own compare (the znode version, the
per-replica cversion); one that publishes a version past the paired one leaves the pairing untaken.
The schedule cut stops before the first decode past the version before the read (`RowOrder`) (a decode
on a thread no registered node owns re-points no view; a view's writer is its version, its INITIAL's
too). Only a view the system publishes through the hook is held, one its doors file names
(`PUBLISHED_VIEW` rows, `LibraryCatalog#publishedView`: Solr's collection `state.json` and aliases): a
pairing of any other (Solr's legacy `clusterstate.json`, a snapshot's metadata) is never offered
(`PairingFlip`, a named `ADMISSION_GAP`), never composed -- its read offers COMPOSE no version
choice and stays at the version it observed, a named `ADMISSION_GAP` (`ComposedFamilies#heldView`) --
and refused at CONFIRM (`PAIRING_UNHELD`), never left to give way; at the version its read observed in
the selected session (a snapshot's metadata its own fetch decoded) CONFIRM holds nothing and compares
the read exactly, a STATE row (`ConfirmMain#stateEdges`). A view's STATE row is taken only where the run
read that version of that location (`Confirmation#taken`): a view's writer `VIEW@v` names no location,
and ZooKeeper's versions restart at every path and every life of one. A hold ends when the reader's work is done -- the reader's occurrence exits, or, for a read in
role work which no hook closes, the first region that work closes after the read in the run as it
goes, a named region's exit or a hop's close (`Confirmation#regionClosed`: a routed alias captures its
view in the request's role work and writes it in a store door's region) -- and is realistic for at most
VIEW_HOLD_MAX, counted from the first publication that hold deferred: `view_hold_max_ms`, 3000 ms of
recorded time, above Solr's own 2000 ms queue poll, times the VM's measured slowdown over the
recording, the seed replay's window over the recording's (`run_engine.sh campaign_view_hold_max`,
which fails the campaign by name when either window stated no duration; `RecordingWindow#measured`
states a run's at its end when it ends inside the window, marked cut, and the campaign names a cut
window in its log and in result.json `viewHoldMax.cutWindow`). Past it the hold
gives way by name, the configured bound in its row, a CONFIRM mismatch and `PAIRING_UNTAKEN`, and
`view_hold_max` in `bounded` whichever replay it gave way in (an obligation's, a witness's CONFIRM or
the final one). The system's own throw in a deferred apply is the system's failure, named; an apply
blocked past VIEW_HOLD_MAX is named, the node's later publications waiting behind it; one superseded
while it applies is named (it may land after the synchronous publication), one superseded before it
began is never applied; an interrupt never ends the publisher. A version the system puts in force at once past a hold still standing before its read -- a publication no hold defers (a request that carried a newer view, Solr's `ZkStateReader#compareStateVersions`; a refresh it asked for) or a refresh's decode its reader reads as it is (a lazy collection's live fetch, `MessageDoors#decode`) -- overrides it, named once per hold: `PAIRING_OVERRIDDEN` (DIAGNOSTIC), a CONFIRM mismatch, and the read's `PAIRING_UNTAKEN` says who (`Confirmation#overridden`; snapshot-no-active, rounds Z3E/Z3F: the client's `/update` refreshed the Overseer's node past the paired version, silently until then); nothing is held or released by it, and the reader's own work's publication, which the hold exempts, overrides nothing. An `ORDER` row waits at most the order's timeout (300 s), past which the
writer goes on and the order is unrealized by name, a CONFIRM mismatch and `PAIRING_UNTAKEN`; a
native reproduction holds the same rows, each stated held, waited or unheld); a pairing that session
states no read or write of refuses (`PAIRING_UNSTATED`). A pairing no term of a path names is claimed
from the session that took it as that session's whole world (§11 rule 3): its own run with the plants
in place of the recording's pairing at each planted location (`Composition#worldRun`; the own run
alone holds there "any arm but the plant"), only where the paired read lies on the fatal path at the
occurrence level (`Composition#onFatalPath`: its symbol in the cone, or its occurrence the anchor's or
the writer of a version a read in the cone, or a read of the anchor's own occurrence, observed -- a role
read counting as the read of each occurrence it is the role prefix of, the rule the pairing flip was
offered by, `Corpus#rolePrefix`).
The worker writes `obligation_result.jsonl`
(`SAT_MODEL_READY`), `obligation.jsonl`, `obligation_query.smt2.gz`, `gaps.jsonl.gz`,
`focused_task.jsonl` (the focus row, [CONTRACT-SPEC.md §3](CONTRACT-SPEC.md)), the pairings'
`expected_edges.jsonl` and the schedule cut (`SchedulePrefix.write`, held): the source session's
schedule up to the first event or mark of the flip occurrence, the focused occurrence, a factor
member, or an occurrence an `ORDER` moves after another's that the session ran first (the
prefix is followed only up to the first event the pairings reorder), and before the first event made
at or after a decode a `VIEW_HOLD` reorders (`Holding#cutBefore`; each schedule event states where it
was made among the VM's events, `ScheduleEvent#vmEvent`, on the scale a decode's view write states
its seq on, after every VM event so far (`Identity#afterLastEvent`): a decode in a
watcher's or the Overseer's role work, which runs on, is cut before itself and not before its
occurrence's first event) goes to `schedule_prefix.jsonl.gz`, the rest to `schedule_suffix.jsonl.gz` (gzip).

### 7.6 The obligation replay

`campaign_obligation_replay` links the seed plan into the worker directory and runs the adapter under
`replay_timeout_s`. The replay runs the workload to its end, its witness or its deciding refusal
(below); the focused set (focused occurrence, factor,
each assigned root's mint occurrence, inherited flips' occurrences) runs symbolically
(`runtime.FocusedReplay`). A clock skew is planted at its mint (the host's reading plus the skew)
and is a jump of that node's clock (`runtime.NodeClocks`): a declared clock reading no skew is asked
of reads the host plus the skew of the jump on its clock latest at or before it in the RECORDING's
order (its place is the event the recording read it at, `SymbolizeAction#eventSeq`, the seq its mint
row states), never this replay's order, so two threads that plant either way round run one clock.
One clock is one node, one JVM clock and one tick (`contract.Clock#same`, COMPOSE's rule too: the
source is the plan's `clockSource`, read off the wrapper's body, never a reading's value; a node's
wall clock and monotonic clock are two, and a clock stating no source is on no order). A value carrying an expression is
computed from a reading and is never moved again; an unattributed mint is on no node's clock and
reads the host (`MINT_UNATTRIBUTED`). A clock's mint row states the instant the run used and, as
`clockSkew`, how far its clock ran off the host there; skews stay relative to the host's reading. The replay owns the verdict: `RowRuntime.closeSession` writes the session's
`obligations.jsonl` and states the same rows to the worker's `replay_verdict.jsonl`. The worker is
the one writer of the obligation's answer, `obligation_result.jsonl`, and writes it once the
replay's process group is gone (`run_under_wall_clock_bound` ends it: whatever of it outlives the
launcher gets TERM, the kill grace, then KILL), so no replay JVM writes after it (solr-18406 ra1:
five JVMs past their bound rewrote the answer ADMITTED during their shutdown hooks, naming sessions
the worker had withdrawn, and the head waited for them until the campaign failed). The statement is
the answer whenever the replay made one, even when the bound killed its JVM after it: it is the
run's last write, after the session it names is closed (or, naming none, withdrawn), whole by one
rename, and a JVM told to end before its run did states nothing (§5). `ADMITTED` = the flipped
decision took the other arm, the focused prefix was not abandoned, the session published a mint row
for every assigned root and clock skew, every inherited flip held, and every edge of its
`expected_edges.jsonl` was taken (`runtime.Confirmation`, the world's pairings: a read that did
not observe its paired writer's version, or an order that stalled, is `PAIRING_UNTAKEN`);
anything else is `NOT_ADMITTED` naming why. **A refuted world** (`WORLD_REFUTED`,
`FocusedReplay#refuted`, an open decider arm's flip only, never CONFIRM's): a replay that never
entered the flip's occurrence and ran its world faithfully -- (a) every assigned root and skew
minted and planted at its value, no prefix abandoned, and every flip it inherited reached and
taken; (b) no order hold gave way (`Confirmation#held`: none waited out its timeout, no paired read
or placeholder (MINT edge) observed another writer, its edges were readable) and a hold in force at
the end -- still waiting, or until an interrupt of the run's own end (a cluster's shutdown) let it
go and its activation did nothing tracked after -- waits only on that occurrence; (c) the world
ACTED in the window -- a plant that moved a value off what the run read, a skew that moved a clock,
an answer that moved an arrival, a hold that waited (`FocusedReplay#worldActed`; a plant at the
recorded value, a zero skew or a configuration planted at a startup read before the window is no
act) -- and no slot was given up (`ScheduleLog#giveUpLocked`) before it first did; (d) the
workload ended by itself (`JUnitMethodRunner#main`, not a bound, a witness or a refusal) -- is
NOT_ADMITTED with a `refutation` (the conditions, the workload's exception, where it was thrown and
the test frame it passed). It answers nothing of the arm (`Frontier#consume` leaves it owed), so the
next round asks the flip again without that world (§7.5). A mint that ran without planting its assignment is a BLOCKING
`ASSIGNMENT_UNPLANTED` gap of the session. A replay ends once the focus row's `declaredTarget`
publishes a target row that reached the anchor and observed the fatal (`AT_WITNESS`, §5).

**The early end at a refusal** (`FocusedReplay#refusedAt`). A replay is *decided* at the first
refusal after which every obligation it carries is `NOT_ADMITTED` whatever the run does next: the
prefix of an obligation's own occurrence is abandoned (`REPLAY_PREFIX_UNMATCHED`: the flip site took
the recorded arm, or the occurrence closed without reaching it), which holds every flipped
obligation of the replay `NOT_ADMITTED` too, or a flip the replay inherited took the other arm. It
ends there (`AT_REFUSAL`, §5). A flipped obligation is never decided before its replay ends: its
session is a corpus session, cut from by later rounds and read whole by the closure and COMPOSE (the
anchor, the fatal and writers after the anchor among them), so only the witness, or a stall
(below), ends it early. A
decided replay **publishes no session**: its verdict rows state the refusal and that the replay
ended there, the worker's row names no session, and the replay withdraws the directory it opened
to `<worker>/refused-sessions/` at its close, in one rename (`RowRuntime#closeSession`,
`SessionPublisher#withdrawTo`); `campaign_obligation_replay`, on the host that ran the replay,
withdraws one a failed move left listed. A `NOT_ADMITTED` replay ran no world (§7.4 cuts no path from one),
and rows cut at the refusal are a prefix of a run no stage could tell from a whole one. Its gap rows
stay EMIT's (§11). A worker's replay stages its session in `<worker>/sessions/`, from where the
head lands it (§7.9); the head, reading a peer's row, waits until its own listing of that directory
holds the session the row names, or none naming the obligation when it names none
(`campaign_await_remote_result`), so it never lands one a cached listing kept.

**The early end at a stall** (`ConcolicResultPublisher#watchProgress`). A replay asked a flip --
never the seed's (no obligation) nor a confirmation's (its verdict rules stand; a stuck one ends at
its bound) -- is watched every 10 s from its recording window's opening on (before it the cluster
starts). What counts as progress (`#watched`), every count but the first bounded, so a loop busy
doing again what it did moves none of them:
- what is new (`ScheduleLog#newKeys`, `#madeKey`, counted only in a watched replay,
  `ScheduleLog#countNewEvents`): an event of a kind, site, node and context shape the run had not made
  before -- the shape as the question compares contexts (`ScheduleLog#shape`, `ContextShape`: per
  anchor hop the RPC site and the sender's node, then the root's role and api; no invocation count,
  anchor hash or handoff), every name the run minted for itself taken out of the site
  (`RunSpellings#strip`: a sequential znode's counter, a session id, a host and port, an identity
  hash). A poll, a retry or a watch made again makes no new key; other code, another store location,
  another request handler or another node does. A view's `PUBLISH` names the version it put in force,
  so a loop publishing new versions still makes new keys: the safe direction, a cut missed;
- the window's opening (at its close the replay ends, §5);
- the question's own moves (`FocusedReplay#questionMoved`): focused occurrences entered (the
  obligations', the assigned roots' mints', the inherited flips'), flips taken, own and inherited,
  roots planted, the world's first act;
- the order's slots taken or given up (`ScheduleLog#settledSlots`), and a model's order holds begun and
  ended (`Confirmation#holdMoves`: each may wait up to 300 s on purpose);
- a focused activation computing (`#FocusedComputing`): its thread, while it is live, used with the
  collectors half a look's span, the schedule's measure (`ScheduleLog#lookLocked`) asked of the
  question's own occurrences only.

Once nothing has moved for 300 s (`#NO_NEW_EVENT_MILLIS`; 600 s until 2026-10-16, when a stalled replay was each round's tail) the replay ends (`#stall`). Inside its
window every question still open is
`NOT_ADMITTED` by name, which says whether a schedule hold was live then (`FocusedReplay#noProgress`:
`REPLAY_NO_PROGRESS: nothing new for N s (...); no schedule hold was live` or `; a schedule hold
was live: <ScheduleLog#holding: the threads held for a turn, the longest's slot and wait, how many
with no slot or behind a held write>`), so a stall the engine's own hold made reads apart from one
the workload made. Before any flip it carries was
taken the stall decides the replay (`...; the replay ended there and published no session (until
then: <what it had settled>)`) and it ends as a refused replay does (`AT_NO_PROGRESS`, §5): no
session, its question settled. After one was taken the flips taken keep their verdicts, never
rewritten, the others are `NOT_ADMITTED` by the stall, and the session stands as the run made it up
to there (`STALLED_AFTER_FLIP`, §5): published as at a witness, every occurrence completed before
it. Either way its threads are dumped on the replay log; at its window's close the replay ends (§5), so no
stall comes after it. A workload
that ended settles on the settle's own bound instead. The bound: of 1,077 Solr
replays that ended by themselves or at their witness (PV7-38, PV7-39, nine SGF6 cases), the longest
span with no new kind of log line was 230 s (p99 162 s, p50 16 s); of their 567 teardowns 558 took
under a minute and 9 took 600-620 s, each standing on an Overseer response until a ZooKeeper session
expired (all ADMITTED; a replay now ends at its window's close, before its teardown); every replay PV7-38 lost to `replay_timeout_s` made
nothing new for more than 2,100 s before it (PULL replicas polling a leader left down, inside the
window; a failed test's teardown waiting on an Overseer response that never came), while the old
measure -- any schedule step, activation, loop body or thread CPU -- saw the polls move. Each watched
replay states its own count at exit (`Causynth schedule: <n> distinct event(s), at most <s> s between
two new ones, the last <s> s ago; ...`, `ScheduleLog#progress`), the measure the bound is checked
against. `replay_timeout_s` stays the last resort: only a run that keeps moving, or a JVM that
does not end, reaches it.

A replay killed on its bound before it stated its verdict (one that stated it is answered by its
statement, above): its session is withdrawn to `<worker>/timed-out-sessions/` and the
answer is `NOT_ADMITTED` naming the bound, its detail opening `REPLAY_BOUNDED:`
(`ObligationResult#replayBounded`; a replay killed inside its bound, by its memory reservation or a
signal, too): it answered nothing, of the arm or of its world, so it settles nothing and counts toward
no world-only answer (`explore.Frontier#consume`). Its flip is asked once more; a flip whose replays were
killed twice and that nothing else answered (a FORCE run's too, §7.10) is held unproposed, open, never settled -- an
`ADMISSION_GAP` row says so -- and named in the round manifest's `boundedFlips` (task, path, site,
ordinal, the outcome asked, each killed obligation and its detail), which EMIT names as the bound
`replay_timeout_s` (`campaign_bounds`): an UNSAT over such flips publishes as bounded, never as a clean
close (solr-adhoc-38 EXZ1: 24 flips killed twice at 2400 s, the expected witness among them, settled as
world-only answers, and the run ended `UNSAT_CLOSED` at `FIXED_POINT`). A question no solver could answer (§7.5), and a replay
that states no verdict, fail their worker, which is then that obligation's `NOT_ADMITTED` and an
`OBLIGATION_UNFINISHED` gap (§7.7); in a GROW re-run a replay with no verdict fails EXPLORE, and in
CONFIRM it is a confirmation that did not confirm.

### 7.7 The work pool

One pool for the whole exploration. An obligation is two starts: its SOLVE
(`campaign_obligation_worker`: its question answered by its host's solver, §7.5) and, when the
solver answers `SAT_MODEL_READY`, its REPLAY (`campaign_obligation_replay` in the obligation's
worker directory, on the model's focus row the solve left there), which the head queues the
moment the solve returns (`campaign_stream_ended`; between two starts of a dispatch too,
`campaign_stream_collect_jobs`), not at the next step -- the queue by kind
(`campaign_stream_enqueue`): a witness's `CONFIRM` and GROW's `RERUN`s lead it (hdfs-11741 AR1: 473
replays of later solves started ahead of the witness's confirmation, four hours), the solves follow
(seconds each, and each decides whether a replay is owed: solr-adhoc-21 RX4 left 1075 of 1158 in
flight as solves never started behind replays), the REPLAYs last, the newest first; dispatch starts
the first entry a host admits, and an entry queued past `campaign_stream_wait_bound_s` goes first
and alone, but for a witness's `CONFIRM` and GROW's `RERUN`s, which never wait behind it (a witness's
confirmation behind a 10 GB solver of its own) -- on the class tree and
plan the solve started on (carried by its queue entry, even when a GROW wove a newer generation
since). Until its REPLAY lands, the obligation is in flight (`stream_flying`, the planner's
`--in-flight`): solving, queued as a REPLAY or replaying, it is never proposed again; only the
replay's verdict lands, and an UNSAT, NOT_ADMITTED or reused ADMITTED answer of the solve lands as
the obligation's. The replay's answer replaces the solver's row as a new inode
(`campaign_write_whole`), never in place: written on another host than the row it replaces, an
NFS client holding the old row cached rewrote it past a truncate it lost (MCH1: the replay's row,
then the tail of the solver's, and the planner failed on the line). The head starts each queued solve, REPLAY, GROW re-run (§7.8) and confirmation,
first first -- a confirmation or GROW re-run queued at the front, a solve or a REPLAY ahead of every queued REPLAY,
except the REPLAY of a fault flip (its solver's focus row states `faultFlip`: the flipped decision reaches a `FAULT`
root, `Corpus#fault`; a pairing flip flips no decision and is never one), which waits behind every other entry, so a door fault at each of many client calls queues
behind the flips of the target's own guards (`campaign_stream_enqueue`; hbase-adhoc-10's R17-10 queued 210 of its 233
REPLAYs as client door faults ahead of them); nothing is dropped, and the wait bound still starts the entry waiting
longest -- while the exploration runs fewer than its share of a shared pool (below; a REPLAY
counts like any start), on the host of `campaign_worker_hosts` (empty: this machine, no
ssh) WITH THE MOST ROOM (`campaign_stream_admit_host`, `campaign_stream_by_room`: the ceiling less
the room heads hold there and the larger of its live charges and its real use, as the head's view
of its ledger holds them, the pool's order breaking ties, so a burst of equal starts goes one to
each host in turn and every start after it to the host its charges left the most room; one
round-robin cursor for every kind sat, after each solve the one warm solver took, on the host after
it, and every replay's scan started there: SGF8-adhoc-07 rounds 7-11 put 17 of 19 replays on lift04,
16 at once, 14.6 GB in use against 3-4 GB on the other lifts, 12 of them ended at its 70 % guard), a solve
first on a host where one returned answered within the solver's idle time (`campaign_stream_warm`,
set when a solve returns answered there, cleared when one returns asking again: that host's
solver of its corpus serves, so the question needs no solver started and no corpus read), and on
a host whose solver it would start only when one more is due (`campaign_stream_solver_due`: none
serves or starts yet, or the questions queued would take the seats of the solvers serving or starting
longer to answer, at the campaign's mean seat per question answered on a warm solver, first-lane
timeouts included, than a new solver takes to read the corpus, or THE OLDEST QUESTION QUEUED HAS
ALREADY WAITED LONGER THAN THAT READ -- a solver restarting or reading again holds every question
queued for it: SGF8-adhoc-07 round 12, 19 solves ~1100 s behind a 575 s restart and a 170 s read,
while the mean seat said none was due -- `campaign_corpus_mb` at the rate the first
question a solver started for measured, its MB over its seconds -- both measured as questions return,
`campaign_stream_seated_returned`, the seat from four on, 2 s and 160 MB/s until then (gzip rows), SGF7-adhoc-39's
first lane holding a seat 12 s per question on average, 102 of about 570 the whole 60 s) -- else it
waits for a serving solver's seat and the other hosts keep their room for replays (SGF7-adhoc-39: a
solver of its 21 GB corpus held 18.4 GB of a lift's 22.1 GB, one replay beside it, and the
round-robin warmed one on all 13 lifts for questions answered in about a second); a REPLAY on whichever host admits it (its worker is on the
shared home). A REPLAY, a re-run or a confirmation THE WATCHER ENDED FOR MEMORY (its host could not
take its growth, `campaign_watch_workload`: it states what it reached, `workload_refused_mb`) before
it stated anything decided nothing and is no answer: its run -- log, measures, the session it opened
-- goes aside under its worker (`<worker>/ended-<n>/`, `campaign_replay_set_aside`), its question
stays asked, and the head, reading `<worker>/replay_again` -- on another host's job too, once its
worker shows it (`campaign_await_remote_result`: a remote REPLAY's worker holding only its solve's
SAT_MODEL_READY row has no answer of the replay yet) -- takes its peak into the measured need and
queues its entry again unchanged (the REPLAY on the tree its solve started on, the RERUN, the CONFIRM;
in flight, owed or under confirmation as it was) at ITS FULL NEED, charged whole with no end's room
beside it (`campaign_stream_replay_again`, the entry's `stream_entry_need`); only one whose full need,
at most half a host's ceiling, is no more than it reached would end again, and is answered
`REPLAY_BOUNDED` as a replay past its bound is (`campaign_replay_bounded`); its full need is at least what
its own peak needs (`campaign_need_of_peak_mb` of what it reached), the campaign's need being the 90th
percentile's. SGF8-adhoc-07: 33 replays
ended so, 240 replay-minutes, each landed REPLAY_BOUNDED and 31 asked again by later rounds. A replay OUT
OF HEAP ends with 3 before it states anything -- the JVM's own OutOfMemoryError
(`-XX:+ExitOnOutOfMemoryError`, `experiments/lib/execute.sh`, a replay-context JVM only) or a heap that only
collects (`contract.HeapWatch`, started by `JUnitMethodRunner#main`); caught by the workload (a Solr node
catches Throwable) an OutOfMemoryError had let the replay run on without that thread's work. Its worker
names the heap it ran at (`workload_out_of_heap_mb`, `campaign_replay`) and sets its run aside the same way,
`replay_again` naming that heap; the head queues it again once at its kind's charge, and every replay from
then on -- that one first -- starts at twice that heap, at most half a host's ceiling
(`campaign_replay_heap_raised`, `campaign_replay_heap_floor_mb`: the heap basis a start hands on is at least
twice it and at least the charge it was admitted at, `campaign_replay_basis_mb`, `campaign_stream_start`; the
charge stays the measured need's, the replay VM's Serial collector growing its resident memory only as its
live set does); out of heap twice, or once at that most, it is `REPLAY_BOUNDED`. The seed replay and the final
CONFIRM run once more in place (`campaign_session_replay`, `campaign_confirm_claim`): out of heap at twice the
heap, the CONFIRM ended for memory at its full need (`campaign_replay_full_need_mb`); a second end fails the
seed's REPLAY and bounds the CONFIRM by name (`campaign_replay_bounded`: its confirmation refuted as
`REPLAY_BOUNDED: the confirmation replay ...`, never decided over no replay). A remote REPLAY whose worker
ends with no answer of its own at 255 (its ssh lost: an ssh client ended by a signal exits so, and the peer's
watchdog then ends the payload) or past 128 (a signal) was killed by infrastructure, not by its question: its run
goes aside under `<worker>/killed-<n>/` with the session it opened, and its entry is queued again unchanged, at
most twice (`campaign_stream_killed_again`, `campaign_killed_attempts`); a third such end, or any other failure,
is the worker's unfinished answer `NOT_ADMITTED` as before (`campaign_obligation_unfinished`). HZ14-mat: 24 replays
on lift06/07 ended at once at 20:40:14 when the head's ssh clients on lift11 were ended, each answered
`NOT_ADMITTED` before this. Checked live on vm-force10 with
the replay's heap overridden to 256 MB (`CAUSYNTH_WORKLOAD_JAVA_OPTS`): `Terminating due to
java.lang.OutOfMemoryError`, exit 3, the run set aside under `ended-1`, `replay_again` naming the heap. A replay's heap is half its basis, at least 4 GB (`campaign_replay_heap_mb`).
THE CONTROL PLANE IS RECORDED (`campaign_stream_event`, `<iteration>/stream_events.tsv`): each admission with the head's
time in it (the ledger's lock, the hosts' readings, the choice), each kind no host admitted in a pass,
and each job's end as the head takes it; a peer states its start time (`campaign_peer_enter`'s "peer <host>
at <epoch>" line, in the job's logs); `analysis/solr-2026-10-18/stream2/ctlplane.py` reads them with the
workers' files (a replay's JVM exit, `workload_cores_x100`). A host is taken for a start of a
kind (`campaign_stream_try_host`) while the cores the campaign's starts keep busy there leave the
start's own (read once, `campaign_host_cores`; `campaign_stream_kind_cores`: a solve or a `HARD` two,
its z3 race's two engines, a REPLAY, a re-run or a confirmation the cores replays measurably keep busy,
`campaign_replay_cores`: the seed replay's alone, then at least the 90th percentile of the replays after it
once eight returned, from the watcher's `workload_cores_x100`, its CPU time over its wall time -- solr-adhoc-05's
replays kept 2.2-3.7 cores busy each, and counted one they held 8 of 13 hosts at 96-100 % CPU; each start gives
back the cores it was admitted at, `stream_job_cores`; a host running
none takes one whatever its count; `campaign_stream_host_count` counts each start in and out), a
question the host's resident solver answers (`campaign_stream_seated`: a solve) only on a free seat
of that solver (`campaign_stream_has_seat`, §7.5: a warm host's seats, a cold host's one), and its
memory ledger admits the start at its kind's charge (below) -- so each kind runs on a host as many
at once as its cores and its room at that kind's measured charge hold, with no fixed count beside
them (two solves and one hard-lane ask per host kept PV7-adhoc-39 alone on the pool far below its
room); none admitting, the head waits for a return, its step's end or the poll interval
(`campaign_host_poll_s`). A START TAKES MILLISECONDS: the pool admits by the head's VIEW of each host's
ledger (`campaign_stream_view`, `campaign_stream_try_charge`) -- its live charges, the room heads hold there
and its real use, read again once older than the poll interval, and between, the charges as the head's
own starts found them under the host's lock and less what it released -- so a start the view has no room
for takes no lock and reads nothing, and one it has room for is decided by the ledger's rule
(`campaign_host_fits`, `campaign_host_admit`, as below) with the head room read as it stands and the live
charges under the lock; each host's MemAvailable is kept fresh beside the loop by a reader of its own
(`campaign_stream_read_hosts`, every poll interval, the ledger's one-refresher rule), so no start waits for
an ssh; what a pass reads once -- each kind's charge and cores, the solver's seats -- it reads once
(`campaign_stream_memo`, emptied as a return is collected); and the queue is scanned for an entry past the
wait bound only once its oldest is (dispatch-rate, 2026-10-17, lift04, 13 lifts, the ledger on NFS:
200 REPLAYs started at 2.0 a second and a round 0's 513 starts behind 500 queued solves at 1.4, each
start reading its host over ssh, ~350 ms, once its reading was older than the poll, through some thirty
forks; after, 61 and 28 a second, a start one lock, one listing of the charges, its row and its holder). A start runs locally in
a background subshell, or remotely through `ssh`: a solve as `run_engine.sh --run-obligation`
with the frozen jar and its sha256, a REPLAY or a re-run as a placed step (below)
(`campaign_stream_job`; a REPLAY's logs `replay-stdout.log`, `replay-stderr.log` and
`replay-host.txt` beside its solve's); each other start takes the class tree and plan of the
generation current when it starts (§7.8). The memory gate
(`campaign_host_try_start <host> <need>`) is a ledger shared by all campaigns, gates and
`tools/adhoc/fanout.sh` under `$CAUSYNTH_HOST_LEDGER/<host>/` (`tools/lib/gc-env.sh`, handed to every
peer with the ceiling): one file per live charge, `charges/<mb>.<id>`, and a start is allowed when
both `Σ live charges + held + need ≤ L` and `MemTotal − MemAvailable + held + need ≤ L`, where `L`
is `CAUSYNTH_HOST_MAX_USED_PCT` (70) percent of `MemTotal` and `held` the room a head holds there
(below): no start leaves a host more than 70 % charged or used. A charge holds for the whole life
of what it started: a JVM below its charge grows into it later, so its unused charge is room no
other start may take (counted only for a 60 s ramp, the Solr replays of rounds SB11 and SB13,
growing for minutes toward their 6000 MB, filled lift12-15 and lift06 to 29-30 GB). It lives by a
lease, the file's mtime (`campaign_host_lease_s`, 120 s, beyond NFS's attribute cache), renewed
every `campaign_host_renew_s` (10 s) by a process of its own while the shell that took it lives
(`campaign_host_hold`; `campaign_host_keep` for one handed on, the host's solver), and is removed
when what it ran returns (`campaign_host_release`); a killed run's charges lapse, and one ten
leases old is deleted. Every start states its measured need, with no default. A solve on a host
where its campaign's solver serves (`campaign_stream_warm`) is charged nothing: its z3s run in the room
that solver holds for its seats, charged with its JVM (§7.5; HI1/HI2's z3 runs: median 1 MB, p90 369 MB,
at most 1.8 GB; charged a question's 1152 MB each, eight seats would hold 9 GB of a host's ledger), on a
cold host what a solver JVM of its corpus needs (`campaign_solver_need_mb`, its footprint and the z3
room its seats share: the solver its question starts takes that charge over, §7.5), a hard-lane ask its corpus-free
JVM's footprint and the hard lane's z3 room (`campaign_decide_need_mb`, 5024 MB), each growing as its
JVM does, never a replay's (HG5A-11, hdfs-adhoc-19: its eight obligations waited 12 of EXPLORE's 13
minutes for room for a 2500 MB replay each, and their solver refused all eight: none replayed). A REPLAY, a re-run
or a confirmation needs its replay's: the campaign's MEASURED REPLAY NEED (`campaign_replay_need_mb`), the largest resident peak its replays
stated so far -- the seed replay's first (HEAD STEPS below), then every obligation's, re-run's and
CONFIRM replay's as it returns (`campaign_replay_measured`, read in `campaign_stream_ended`) -- until eight
replays after the seed's returned, then the 90th percentile of their peaks (`campaign_replay_peak_p90_mb`:
SGF8-adhoc-07's largest of 538 peaks, 6476 MB, had raised every replay's heap basis and full charge to 9728 MB;
their 90th percentile, 3547 MB, gives 5376), times 1.5, rounded up to 128 MB, at least 512 MB, and charged at
most half a host's ceiling
(`campaign_replay_charge_mb`). The need sizes a replay's heap; until eight replays after the seed's
returned, a replay of the stream is CHARGED a quarter more than the seed replay's life's mean, with room for
four ends that reach the largest peak so far (charged 1.5 times the seed's peak, SGF8POOL-adhoc-05's round 0 of 600
obligations held every host at seven replays of 200-300 MB, 12-38 % of its memory in use, for the round); once
eight returned, the 90th percentile of their lives' mean resident memory
(at most the need, `campaign_replay_typical`, the watcher's `workload_rss_mean_mb`), its end's growth as
it grows, and a host admits one only with room for four ends of their peaks' 90th percentile less that
charge (`campaign_replay_spike_mb`): a replay peaks in its last read, publishing its session (lift07,
SGF7B-adhoc-10: 19 replays, peaks 680-1557 MB, lives' medians 413-834 MB); charged at the largest peak, the lifts' ledgers held 21-22 GB over 8-11 GB
of real use and admitted nothing more (solr-adhoc-21 RX4: peaks p50 918, p90 1242, max 2234 MB). An obligation replay peaks near its own seed replay (round HG4:
hdfs-11741 674 / 662-715 MB, hdfs-17897 552 / 540-555), while the static 2500 MB per obligation
and seven times the recording per CONFIRM held the lifts' ledger at 11-22 GB over 3-7 GB of real
use (HG5A); one that outgrows the need grows its charge as below, and before eight returned raises the
need of every start after it (hdfs-adhoc-15: seed 514 MB, obligations 939-2003). The charge is taken at the
start (`campaign_stream_admit_host`, `stream_admitted_mb`, handed to the job); the head holds it,
the job releases it as soon as its work returned, before the head waits to see what a peer wrote,
and the head again once it collected or reaped the job (`campaign_stream_release`). A replay JVM
is handed what its host was charged for it (`CAUSYNTH_CHARGED_MB`) and its heap basis
(`CAUSYNTH_HEAP_BASIS_MB`, `campaign_replay_basis_mb`): its heap is half of it (4 GB at least), and
`experiments/lib/execute.sh` watches it until it ends (`campaign_watch_workload`): one whose
resident memory grows past its charge asks its host's ledger for the excess, as one more charge,
granted unless the host's real use would pass `L` with it -- once its run's end began (the replay JVM marks
it, `<worker>/workload_ending`, `JUnitMethodRunner#exit`: the settle's read-outs and publications, its end
peak), unless it would pass 85 % (`campaign_host_end_used_pct`, owner 2026-10-18; starts stay at `L`) -- and
holds what it was granted, released when it ends; one the host cannot take is ended, saying so (of the
end-peak kills the not-admitted study counted, those after the test's end, where this rule now applies:
14 B2H 25 of 36, 23 of them within 85 %; 14 OOM 10 of 47, 7 within; 07 0 of 18 and 13 1 of 21, the rest
mid-window at a host's 70 % of real use); each states its peak at its end and
writes it to `workload_rss_mb` in its worker directory, where the head reads it.

THE SHARED POOL. With `stream_shared_pool=true` (a sweep's cases, `tools/adhoc/sweep.sh`) the
explorations running at once share their hosts (`campaign_stream_has_slot`, the one dispatch
point): each starts one more only while it runs fewer than its share, the slots its hosts hold at
its measured replay charge (`campaign_pool_slots`: on each host as many starts as fit under the
ceiling above at that charge, at most its cores) over the sharing explorations whose entry in
`$CAUSYNTH_HOST_LEDGER/explorations/` is fresh (written when the loop starts, kept fresh by the
head's heartbeat like its room, `campaign_head_reservation_stale_s`, removed when it ends), at
least one, read again at every start; it says once for each share it waits at. So the share
follows the measured need, grows as others end and shrinks as others begin (what already runs past
it runs out), and one exploration alone keeps all of it. `false`, the default and a named
acceptance run's, shares nothing: the hosts' memory and cores alone decide. A sweep admits each
head for the room it reserves on its host (HEAD ROOM below; `tools/lib/heads.sh`
`case_head_reserve_mb`). Round a40 without sharing: one Solr case kept 27-32 replays in flight on
all ten lifts, the other cases' heads waited for room, and 20 Solr checks would have taken over
15 h; with a static per-case charge, adhoc-07's 151 replays of ~93 s each waited a median 35 min
for a slot (HG4).

HEAD STEPS. Every heavy step of a head (`do_campaign`) goes where there is room through one rule
(`campaign_head_charged`, `campaign_head_place`): the head's own host when it fits there (its own
room is not held against it), else the pool's host with the most room under the ceiling
(`campaign_host_room`), charged there while it runs and released when it returns; none having room,
it waits, saying so once -- but A STEP NO HOST CAN EVER HOLD never waits: past the most a pool host holds
with no charge standing (its ceiling less what it uses beside the ledger, at most the system's own 2048 MB, `campaign_head_most_mb`), an
engine JVM whose heap is only a bound (no measured need) runs at the largest heap that fits it, and any
other step fails at once, named (`engine_java`, `campaign_head_place`). A step on a peer runs through the remote worker script as
`run_engine.sh --run-placed` (`campaign_run_placed`) in the head's working directory, with the
head's exported `CAUSYNTH_`/`GRAPH_CHECKER_` variables, its output passed back as its own: a
program, or a `run_engine.sh` function whose arguments are all it reads of the head. The steps are
every engine JVM of every stage -- SEED's static passes, scope growth and trace aggregation, PLAN,
INSTRUMENT and its verifier, the import gate, the planner (one service held for the exploration,
§7.9), COMPOSE, CONFIRM's and REPRODUCE's `ConfirmMain`, GROW's planner and weave -- each charged
while it runs at the heap
it starts at (`engine_java`, `campaign_engine_start_mb`): its main's measured need
(`campaign_engine_need_mb`: the static pass and the composer 4 GB, the planner 8 GB, the trace
aggregation, scheduler, lineage scan, scope growth, woven-class verifier, CONFIRM, GROW's
`ExposedRegionPlanMain` (0.13 GB measured) and weave key `WeaveKey` (0.34 GB) 2 GB; the import gate its own, §6), or `engine_memory_mb` (else 8192) for a main with none; a JVM
that runs out of its heap (exit 3 under
`-XX:+ExitOnOutOfMemoryError`) runs again at twice it, up to `engine_memory_mb`, charged so, saying
so each time, and later starts of that main begin at the larger heap (`campaign_engine_outgrown`;
a head step's discovery is the head's, §7.9): a 2 GB trace aggregation or scheduler that asked for
the 16 GB engine heap at once found no lift of a running sweep with it free and waited 75-85 min
(a40s); every run ends
at its first out-of-heap error, at `engine_memory_mb` too (exit 3: the most heap a head JVM is given,
told apart from a crash) -- the seed
replay (`campaign_session_replay`), before any replay of the campaign was measured, needing seven
times the recording's measured peak (`workload_rss_mb`; a concolic replay outgrows its native
recording, up to 6.94 times in round x1; a recording that measured none, or a seed replay that
states no peak, fails REPLAY by name; it is charged only `campaign_seed_charge_factor` (2) times the
recording's peak at its start: HDFS seed replays peaked at 0.5-1.4 times their recording, HG9/HI2), and the final
CONFIRM replay (`campaign_confirm_claim`),
needing the measured replay need (above), each charged at most half a host's ceiling at its start
(`campaign_replay_charge_mb`: a charge only an idle host can hold waited 75 minutes in round HG1;
past its charge the replay grows while its host has room) and its heap sized by the whole need
(`CAUSYNTH_HEAP_BASIS_MB`), and REPRODUCE's native runs (§10b). A running JVM that outgrows its
charge is ended only when the host's real use would pass the ceiling with it
(`campaign_host_try_grow`). They read and write only the run's
shared directories -- the case's scope copy among them (§1) -- so each runs alike on any host. What
a head runs uncharged stays on its host: the setup adapter's copy and the recording, whose need is
what it measures. HEAD ROOM: a head
runs its engine JVMs on its own host first, between the obligations every campaign keeps starting
there, so it reserves room for the next one -- its measured step need (`campaign_head_need_mb`:
the largest peak any of its engine JVMs reached, each watched where its step runs and folded into
`<campaign>/engine_peak_mb` by `campaign_engine_jvm`, times 1.25, at least 1 GB, at most the engine
heap's JVM footprint, read again at every heartbeat; before any was measured, the footprint of what
its planner or composer starts at), never the case's engine heap; an engine JVM at a heap of H MB is
charged, held and watched at its footprint, H + H/16 + 384 MB (`campaign_jvm_footprint_mb`: the
JVM's own memory beside its heap; charged at H alone, solr-adhoc-07's served planner reached 8375 MB
at an 8192 MB heap on a host near the ceiling and was ended); a step its room does not cover is placed by its own charge, as
every head step is -- (`campaign_head_reserve`,
`<host>/heads/<id>` stating its need, fresh while the head lives, idle unless one of its JVMs
runs): a start that is no head's own counts the largest idle fresh
reservation of the host as used, a head's own start counts none (heads take turns and never
block each other), and the head gives its room up when it exits. A head step that waits for room
holds its need on the pool's host with the most room when it began to wait (`campaign_head_hold`,
`<host>/heads/<id>.hold`, fresh while the head lives, given up once the step is placed, the head
exits, or the exploration's end ends the step that waits -- a round dropped at a witness, §7.9 --
by the pid the hold names, `campaign_stream_reap`; `campaign_head_hold_room`): every start but the head's own counts it as a reservation, so
that host drains as its starts return instead of being taken again one obligation at a time
(a40h2's 14 GB seed replay waited 70 min, V5-11741's 16 GB GROW step 40 min and more, while the
pool kept every lift busy).
An obligation whose worker does not finish (a nonzero exit, local or remote, or a result the head
cannot see) is its own answer (`campaign_obligation_unfinished`): every process on its host whose
command line names its worker directory is ended (a peer's replay JVM is in a process group the
remote wrapper's watchdog does not reach), what it staged moves to `<worker>/unfinished-sessions/`,
and its row is `NOT_ADMITTED` naming the host, the exit and the last error of the start that failed,
on its own stderr (`campaign_stream_logs`: a solve's `stderr.log`, a `HARD`'s
`hard-`, a REPLAY's `replay-`; an engine failure's `die` or `campaign_fail` line names its cause, so a
reading tells a defect from a named bound). An engine failure stays loud: each such obligation files a
DIAGNOSTIC `ADMISSION_GAP` `OBLIGATION_UNFINISHED` in `campaign_gaps.jsonl`, which EMIT carries,
and `iteration_manifest.json` counts them (`unfinishedObligations`). A host whose memory or cores
cannot be read for `campaign_ssh_patience_s` fails the campaign at EXPLORE; a head that fails mid-exploration
ends everything it started first (an EXIT trap: each job's process tree, and every peer's workers).

### 7.8 GROW

When a round's `growth.jsonl` holds `EXPOSED_REGION` rows (occurrence, region, node, exposing session
and its obligation; none where only the seed ran it: that row grows the plan alone, no replay is
re-run for it, and the anchor's path re-runs once it is planned, §7.7), `UNPLANNED_INPUT` rows or `ZK_EDGE` rows (below), the head grows (`campaign_stream_grow`) and queues the round's proposals behind
GROW's re-runs, as what was queued before them stays queued: they start at once, in flight from the
round on, so no later round asks them again (solr-bugs-reindex-cleanup
Z10: dropped and re-asked, four growing rounds in a row re-proposed a backlog of 951 of round 5's 980
obligations, and the witness flip a non-growing round 1 queued in Z9 waited from round 1 to round 5,
unanswered when the exploration ended). One GROW is one GENERATION of the plan
and the class tree, under `generations/g<k>/`, BUILT BESIDE THE LOOP (`campaign_stream_grow_build`,
GROW's lane, §7.9; one at a time, from the plan and the tree current when it started):
`plan.ExposedRegionPlanMain` writes the generation's plan, the one before it plus one task row per
exposed address (admission basis `EXPOSED_BY:`, static inputs only, the plan's `replayGroupId`) and
each grown invocation (below), as a new file, and INSTRUMENT weaves that plan
(`campaign_instrument`'s plan argument) into the generation's own tree where its weave key (§4) is
not the key of the tree it stands on; the head meanwhile goes on starting, collecting, landing and
planning (SGF8-adhoc-07 minutes 2-11: a GROW in the head's hands, its planner and weave 386 s with no
start and no collection; solr-18413 Z3S: 8 min of a round's take), and a start meanwhile takes the
generation current then. The built generation is TAKEN between two head steps
(`campaign_stream_grow_take`): it is current from then on -- kept beside the round
(`grown_plan.jsonl`), the iteration's plan, its chain and the seed plan its hard links, each name
replaced whole by one rename (`campaign_link_whole`: rounds plan and hosts' solvers read the plan
meanwhile), the generation before keeping its own inode for whatever runs on it -- and its re-runs
are queued; no round is taken while a GROW builds or waits to be taken, so each round's growth is
judged against every re-run queued before it (`campaign_stream_growth_new`), and a GROW building or
built counts among GROW's owed work (`stream_hold`: a budget's end finds a round due, an open chain's
witnesses wait for it). An end that finds a GROW building or not taken drops it (its generation to
`explore-reaped/`, a round due). More planned occurrences of regions whose hooks that tree holds, a grown input at a hook
it holds and a dropped doors-only mark weave that tree again, so the generation keeps it
(SGF8-adhoc-19: 8 of its 11 generations were woven byte-identical to the tree before them, 62 s each
of the head's; the key is 0.8 s). At the take, each exposing obligation's replay is queued first, to re-run on whichever host of the pool
admits it (§7.7) in
`<worker>/grow-<round>/<obligation>/` (the worker's focus row and schedule cut linked in), `<worker>` the
ask whose answer names the exposing session (`campaign_obligation_worker_dir`, by the growth row's session,
kept for the re-run and its swap, `stream_reruns`): an obligation asked again under its id
has a worker in each round that asked it, and either may be the exposing one (SGF3-adhoc-21: the first
ask's worker found no host for its solver, the re-ask in `obligations-0004` exposed a region).

GROW HOLDS NOTHING (2026-10-17): no round, solve or swap waits for its slowest re-run. Before, no round was
planned until every re-run had returned and swapped, no solve started from the last re-run's return to the
swap, the swaps waited for every running solve, and ran one by one: SGF8-adhoc-05's round 4 -> 5 took 56.2 min
(weave 2.6, re-runs 37.2 -- 62 re-runs, p50 609 s, the slowest six 27-37 min -- swaps 10.2, ~9.6 s each, gate
6.2) while the pool ran ~32 replays of ~200. Now each re-run SWAPS in (`campaign_stream_swap`) between two
head steps once it returned -- its session gated where it staged it first, as any session is (§7.9) -- once
no reader of the session it withdraws runs (`campaign_stream_swap_due`). The
readers of a session's files, from the code: a witness's confirmation queued, running or undecided
(`stream_confirming`) whose attempt composed it (its `corpus.txt`): it confirms against that corpus
(solr-bugs-tra-start-overwrite Z2M, Z2N: the witness was the exposing session), so a confirmed one ends
the exploration with the swap dropped, its directory to `explore-reaped/` and the corpus exactly the
attempt's; a witness owed an attempt -- gated and not attempted (`stream_witnesses`: a confirmation owed
holds the attempt, not the landing) or deferred until a confirmation's verdict (`stream_deferred`) --
withdrawn first, the attempt would compose without it and a re-run that did not take the flip would lose
it (Z2M's class; an open chain's witnesses wait for exactly these swaps, under the confirmation's hold, and
are attempted again once the chain's GROW swapped in); the round planning, while its `corpus.txt` names it and its planner has not stated
`<round>/corpus_read` (`ExploreMain#CORPUS_READ`): a round reads session files only in its corpus read
(`Corpus#read`, rows and schedules), and fails on a session its corpus names that is gone. Nothing else:
a head step never runs beside a swap; a REPLAY, a re-run, a CONFIRM replay and a hard-lane ask read no
session; and a host's solver reads the corpus as it stands without what GROW withdrew -- the iteration's
`withdrawn.txt`, made empty as the exploration starts (before any solver serves) and appended before each
withdrawn session leaves -- and reads again when one left under its read (`ObligationSolverMain#standing`,
`#readWhole`, each read again said in the solver's log; a session leaves once and never returns, so one the
journal does not name after the read stood whole while it was read; the journal, not the listing, says what
left, and it is opened, never looked up first: a peer's NFS listing or lookup may be a minute old, while an
open reads the file as the head closed it). So solves run on through swaps (SGF7-adhoc-09: holding them
cost 51 min over six GROWs). WORKER FILES a swap sets to the re-run's are read as they stand, each renamed
over whole: a round's wave is taken from the workers its corpus read found (`Corpus#landedIn`), its answers
and bounds by flip (`ExploreMain#answersByFlip`, `#boundedFlips`) are a worker's flip's either way, and a
solver's settled questions (`ObligationDir#answered`) name the plan generation they were asked under, which
the GROW changed before any of its swaps, so a question asked since is another one (and one whose plan read
the same would be settled as it was before the swap). A replay owed on
the path of a session a swap withdrew (its focus row's `pathSessionId`, the solver's) is dropped
(`campaign_stream_replay_drop`): queued at the swap, or returned SAT from a solve that read the corpus
before it -- no replay, out of flight, so a later round may ask its arm again of the re-run's session;
one that runs finishes as usual. A kept obligation cut from an exposing session is answered by its
solver by name (`NOT_ADMITTED`, "no session of this corpus still states path ...") and a later round
asks it again of the re-run's session. ROUNDS PLAN WHILE RE-RUNS RUN, over their frozen corpus with the
exposing sessions in it (§7.9): such a round, or one taken after a re-run swapped in, sees what the
re-runs capture uncaptured still (`ClosurePlanner#uncaptured` names a demanded occurrence no session of
its corpus runs as a task, whatever the plan holds), so its growth rows are IN FLIGHT and not grown
again (`campaign_stream_growth_new`) where the exposing session has a re-run owed or was withdrawn by
one, or the subject (an occurrence, a task's `<symbol>#<k>`) was grown with the re-run of a session the
round's corpus names (`stream_growing`: planned before that re-run's session landed); the round after
the swap sees what a round always saw after it. A re-run that did not finish (failed, stalled, past its
bound) is dropped: not swapped in, the exposing session stays (what it would have captured is no longer
in flight), and its obligation is never re-run again (`<worker>/grow-dropped`; before 2026-10-15 it
failed the campaign).

EVERY RE-RUN HOLDS THE FIXED POINT, whatever its world's depth (`campaign_stream_idle`): the exploration
is at its fixed point only once no re-run is queued, running, swapping or owed its gate, and a growth that
queued re-runs owes no round until they land (`campaign_stream_grow_take`; one that queued none owes one at
once), each landing marking the corpus changed (`campaign_stream_swap`, `campaign_stream_move`), so a round
plans over the re-runs' sessions before the fixed point can hold. The world-depth bound
(`ObligationFactory.Bounds#maxWorldDepth`) only keeps a re-run's session from parenting an obligation
(`ObligationFactory#candidates`); the closure (`ClosurePlanner#plan`) reads every session, and a re-run under
a grown generation is the only session with rows in the regions it wove, so the grown tasks -- and the
obligations cut on them from the seed's paths -- exist only once it landed (SGF8-adhoc-39 at depth 0: the
round after its re-runs landed held 44 new tasks and 77 obligations, 48 of them composed paths; a fixed point
declared beside the re-runs, OPTIMIZATIONS 1.37, reverted, composed 8 paths of 57 in SGF9). A SESSION WHOSE
RE-RUN DID NOT LAND -- dropped at a stop, never run (a GROW dropped at the end), or not finished -- and
that is still in the corpus is named in `uncaptured_sessions.txt` (`campaign_stream_uncaptured`,
`contract.SessionDir#UNCAPTURED`; none after a witness, whose claim is the accepted attempt's): it ran
the grown regions uninstrumented, so COMPOSE frees what its reads saw that no write states
(`Composer#statedReads`, `SmtLowering#freedUncaptured`, FREE and named) rather than holding it
(over-approximated: an UNSAT stays sound, a false SAT is CONFIRM's), and `CompositionInputs` digests
the file.

One swap: the exposing session (that session alone: another ask's session of the obligation stays),
named in `withdrawn.txt` first, moves to `<worker>/before-<round>/` with a copy of the worker's previous
files, the re-run's files are renamed over the worker's (one it lacks is removed, so no peer's NFS client
opens an old inode through a name it cached), its session, gated where the re-run staged it (one the
gate's ledger, `import_gated/`, does not hold fails EXPLORE by name: no session lands ungated), lands,
and its verdict replaces the exposing ask's row in `obligation_results.jsonl` (another ask's row
of the obligation stays). The swaps due at a step go in ONE PASS: the exposing session is the one the
re-run's entry names, all their manifests read by one jq, each worker's files moved in a subshell of its
own (`campaign_stream_swap_jobs`, 16, waited by pid), the ledger rewritten once, the queue scanned in the
head's maps (`stream_rests`, `stream_withdrawn`). The queue stays first and in flight: the next round
gets it as `--in-flight` and proposes only what none of it asks, its new obligations queued behind it
(hdfs-11741 HG3: 342 queued obligations dropped and re-proposed put the witness obligation at 81 of
409). The withdrawn session's slots go with it (§7.1 step 4): under the grown plan
the region's events stand in new occurrences, so its endpoints have new ids, and a slot of the old
run would read the re-run and every later session of its world as a replacement (hdfs-11741 V4:
two BLOCKING rows withheld the witness's composition). Once nothing runs, the last generation's tree is the iteration's
`instrumented-classes`, with its weave key (CONFIRM, REPRODUCE). An exposure no obligation names (seed exposure) fails
EXPLORE.

A replay may also run past the plan's ZooKeeper chain (`zk_chain.jsonl`, SYMBOL-SCOPE §6.4), which is
a finite set of (znode, field) and grows by its own fields only: a replay's write of a chain path's
version by an occurrence off the chain (a STORE write, a decode's VIEW write) is a `ZK_EDGE` growth row
of the round (`explore.ZkEdges`) where a chain occurrence of the same session consumed that version (a
STORE read or a chain decode of it, a VIEW read of that node's view) and the occurrence's own leaves of
the path (its content ports) lie under a key the chain holds of it. Not an edge: another node's decode,
a version no chain occurrence consumed, a write or decode touching no chain field, a chain path the chain
keys no field of, a read of a path off the chain (a poll), and work under no region, which no task can
hold (solr-18413 SGF7, growing every such one: 52, 92 and 1099 rows in rounds 0-2, round 2's over 541
occurrences; by this rule 2, 0 and 50 over 36). A row states transport, location (the row's slot),
version, occurrence, the chain's keys it carries (`pointers`), and the first admitted focused replay
that showed it with its obligation -- or none (`sessionId` "") where only the seed or unadmitted
replays did, which no re-run follows. GROW's planner writes the generation's chain beside its plan
(`generations/g<k>/zk_chain.jsonl`, the iteration's `zk_chain.jsonl` its link from then on): the one
before it with each edge's occurrence and its keys appended (`contract.ZkChain#grown`), so the chain
never shrinks, a seed's edge as well; the edge's
occurrence loses its doors-only mark (`campaign_unpauses`), or, where no task holds it and its region
is a candidate skeleton, is planned `EXPOSED_BY` (work under no candidate region runs as recorded, its
path on the chain), each such row stating the keys (`contentKeys`); a generation whose weave key
changes is woven. Its exposing replay is re-run as an exposure's is.

A flipped world may also call a planned fault marker of a demanded door more often in its
occurrence than the recording did (solr-adhoc-09: the first `waitForState` timed out, so the
DeleteReplica task waited a second time, a call the recording never made). Its input action plans
one invocation (`replayOccurrence` k), so the replay runs the k-th call concretely and states an
`UNPLANNED_INPUT` row, subject `<taskId> <symbol>#<k>` (`runtime.RootMint#unplanned`); any other
input's later call keeps its rule and is no exposure: a clock read again is a later instant of
its one root, a configuration one root per key. A round's `growth.jsonl` holds one
`UNPLANNED_INPUT` row (task, input, k, exposing session and obligation) per invocation an
admitted session that may parent states (`ClosurePlanner#unplanned`), once: one its plan already
holds grows nothing, and one past `unplanned-input-max` (4) is a DIAGNOSTIC row of the round and
a declared bound of the case (`campaign_bounds`, `bounded` `unplanned_input_max`). GROW's
planner (`ExposedRegionPlanMain`) writes the generation's whole plan: the one before it, each
grown invocation added to its own task's row as the input `<symbol>#<k>` (port alike,
`replayOccurrence` k, observed in no recording) -- a second row of the occurrence would compete
for its claim -- then the exposed regions' rows. The exposing replay re-runs under it in its
world, the new input mints the k-th call, and a later round flips it there (one flip deeper,
`max_world_depth`).

### 7.9 The loop

`campaign_explore` is one streaming loop on the head, with no wave barrier. It starts queued
obligations wherever a host admits one (§7.7) and collects each as it returns
(`campaign_stream_wait`). Its own JVM work runs in the background in THREE LANES, so the pool goes on
starting and collecting while any waits for memory or runs, and none waits for another.
HEAD STEPS, one at a time (`campaign_stream_step`, in `steps/NNNN/`): an import gate with the
confirmation verdicts owed, or an attempt at witnesses. ROUNDS, one at a time (`campaign_stream_round`,
in `planning-NNNN/`): the exploration's planner (§7.1). GROW, one generation at a time
(`campaign_stream_grow`, §7.8): its planner, weave key and weave. Their JVMs -- the gate, the planner,
an attempt's composer, GROW's planner and weave -- are head steps (§7.7): each goes wherever there is
room, a planner and a composer at once each by its own charge (the served planner's is held for its
life anyway). AN ANSWER LANDS AS IT IS COLLECTED (`campaign_stream_collected`), never at the next
head step (SGF8-adhoc-07: an answer reached the next round's planner a median 329 s, p90 611 s, after
it returned, 2774 obligation-minutes, the head 71 % busy in import gates and planning in minutes
17-81): an answer that names no session -- a solve's UNSAT or NOT_ADMITTED, a hard-lane ask's, a
worker that did not finish (answered first by why, `campaign_obligation_unfinished`) -- is appended
to `obligation_results.jsonl` at once (`campaign_stream_land`: no head step reads the ledger, the
head is its one writer), out of flight; one that names a session, staged in its worker, is OWED THE
IMPORT GATE THERE (`stream_gate_owed`) and lands, session and verdict together, as the step that gated
it returns (`campaign_stream_land_gated`) -- so the corpus holds only gated sessions, an answer
naming a session stays in flight until its session is in the corpus, and no round waits for a gate;
a GROW re-run naming a session is gated the same way before its swap. Between two head steps, in the
head's hands, in this order:
1. a GROW whose generation was built is TAKEN (`campaign_stream_grow_take`, §7.8): the generation
   current, its re-runs queued first; then a round that returned is TAKEN (`campaign_stream_round_take`)
   while no GROW builds or waits to be taken: its directory becomes `obligations-NNNN/`, and the head
   takes its round (`campaign_stream_take_round`: the wave budget, GROW started for its exposures, and
   its proposals into the queue, where they start at once, on the generation current then, as anything
   queued before a GROW always could);
2. the round owed STARTS when none plans (`campaign_stream_round_start`) -- owed once a session has
   landed, or once nothing is queued, running or returned unlanded but confirmations and the hard lane's
   asks running (z3 alone at the full budget, up to 30 min: SGF8-adhoc-40 round 6 idled the 13 lifts
   12 min behind two; their obligations stay in flight and their verdicts land in whichever round is open
   when they return) and an answer came since the last round started (`campaign_stream_plan_due`;
   GROW's re-runs hold none: a re-run is a question left to wait for, which lands a session, and the
   round plans over the exposing sessions it stands in for, §7.8) --
   over inputs frozen now, written into `planning-NNNN/` beside its files:
   `corpus.txt`, the sessions landed (every one gated before it landed); `answers.jsonl`, the answers
   landed (`obligation_results.jsonl` as it stands); `in_flight.jsonl`, the obligation rows queued or
   running (§7.3). It plans in the background, the campaign landing meanwhile, and no session or
   answer that lands meanwhile is the round's (§7.1). The obligation workers' own files -- each one's
   answer, focus row and question, read for the worlds, the answers by flip and the killed replays
   (`Corpus#indexWorlds`, `ExploreMain#answersByFlip`, `#boundedFlips`) -- it reads as they stand when
   it reads them, as a round always did: a worker writes its own answer as its replay ends, a
   landing writes an unfinished one's (`campaign_obligation_unfinished`), a swap a re-run's (§7.8);
   its sessions' files it reads in its corpus read alone, and says so (`corpus_read`), from which on a
   swap may withdraw one of them;
3. GROW's returned re-runs, gated, swap in (`campaign_stream_step_start`), each one no reader of its
   exposing session holds (§7.8), their sessions moving into the corpus (`campaign_stream_move`); the
   next head step then takes in what returned owed its gate: ONE IMPORT gate (§6) over exactly them,
   each where its worker staged it (the list `gate`, its summary `import_gate.json`; one BLOCKING
   violation fails the campaign at IMPORT), and the confirmations' verdicts; as it returns, what it
   gated lands, and the round owed starts over it.

A round may also start while an attempt or a verdict step runs, every landed session gated before it
landed. Until a round is taken no reader of the rounds sees it -- its name matches no `obligations-*`
(the slot table, the workers, an attempt's COMPOSE) -- so an attempt composes only taken rounds
(solr-18413 Z3S, one lane: a witness that returned three seconds after a step began, which gated six
sessions and planned round 2 -- its planner out of 8 GB, then 1437 s waiting for 17.8 GB -- was
attempted 69 minutes after its replay ended). AN ATTEMPT'S SLOT TABLE IS ONE ROUND BEHIND ITS
SESSIONS, an over-approximation: the sessions landed since the last taken round started, the witness
among them, have no slots of their own until a round reconciles them (§7.1 step 4) -- the round that
does may plan while the attempt composes -- so COMPOSE checks their pairings only against the slots
earlier rounds opened (`SlotTable#replacements`: one that contradicts a slot of its own world is a
replacement, one no slot holds is growth). A spurious SAT is possible, and CONFIRM filters it (§10);
the next attempt reads the slots the round opened. After a witness the final COMPOSE reads the
accepted attempt's corpus (the sessions landed after it leave, WITNESSED below) with the slot table of
every round taken by then -- rounds taken between the attempt and its confirmation's verdict among
them -- so its claim may differ from the attempt's: `campaign_confirm` reuses the attempt's
confirmation for the same model only, and replays CONFIRM for any other. THE PLANNER SERVICE (`campaign_stream_plan`): the
round's lane starts it when none lives, as a head step -- placed by the usual rule (`campaign_head_place`) at
its need for the round, its charge held for its life by the shell that holds it (`campaign_host_keep`, as a
host solver's), grown as a watched JVM (`campaign_watch_workload`), the head's room marked busy while it runs
on the head's host -- and asks
the round of it on its host (`campaign_planner_ask`, through the remote worker script when it runs on
a peer: its questions wait on that host's disk, `campaign_planner_dir`). Its state is
`iteration-0000/planner/`, its log `planner.log`. One that ran out of a heap below `engine_memory_mb`
(exit 3) is started again at twice it and the round asked again; out of the engine heap it is
PLANNER_HEAP_EXCEEDED (below). IT RUNS AT THE ENGINE HEAP (`campaign_stream_plan`): one started lower outgrew its
heap mid-exploration and read the whole corpus again at the next (05: 11.6 GB, ~10 min of an idle pool) after
collecting to its end (~17 min each). ITS HOST IS CHARGED ITS HEAP'S FOOTPRINT for its life (`campaign_jvm_footprint_mb`), and its host runs no replay
beside it: a JDK 8 parallel collector grows the resident set toward the heap whatever the live set (SGF9-adhoc-31:
6.4 GB live at 20.2 GB resident), so a charge of its measured need let replays take the room its growth then
needed, and its watcher ended it at the head ceiling (the case lost). A ROUND IT CANNOT HOLD IT DOES NOT READ: before a round it judges its room by
its own measure (`contract.HeapWatch#outgrown`)
-- its old generation's live set at its highest since the last round (what it held after a full collection, as
`HeapWatch` reads it every 5 s, `#takePeakSwept`) with `HeapWatch#ROWS_PER_FILE_BYTE` (0.35) of the files of the
sessions new to it (`ExploreMain#toRead`), past `HeapWatch#FULL` (90 %) of its old generation -- and a round past
it is answered out of heap unread (`Service.OutOfHeap`, exit 3), the planner serving on; the round is
PLANNER_HEAP_EXCEEDED, its `heap-predicted` the planner's words (`campaign_planner_ask`). The rows are a steady
third of their files (0.32-0.37 over six SGF8 rounds of 05, 07, 10, 14, 40), what a round adds to them comes and
goes (peaks of 0.57 to over 1.09 times the files, in `Frontier.<init>` in three of the six), so no rule over the
files alone tells a corpus a planner holds from one it does not: 40 ran out over 16.2 GB of files, 05 lived at
~14.5 GB live of its 21.5 GB heap over 20.4 GB (shard-study FINDINGS §3, §7). A planner or a composer is a HEAD
STEP, one JVM alone on its host: placed, grown and given its z3 room under the head steps' ceiling
(`campaign_head_max_used_pct`, 88 %; the replays' and solvers' stays `CAUSYNTH_HOST_MAX_USED_PCT`, 70 %), so the
Solr study checks' engine heap is 24576 MB, a solver's at most 16384 (`campaign_solver_max_heap_mb`); every engine
JVM runs at `-XX:NewRatio=4`, its old generation four fifths of its heap (its live set is its corpus); any other end fails EXPLORE with its deepest throwable -- never a
silent start of another. The exploration's end stops it (`campaign_planner_stop`), and so does the
head's EXIT trap. A head step after which witnesses wait is followed by an
attempt at them (`witnesses`, below), a step of its own. A head JVM that outgrew its need in a step
or a round (§7.7) is the head's from then on (`outgrown`, joined per main at the larger heap: the
lanes run at once, so none's replaces another's). The corpus changes only between two head steps,
so a head step reads it as a landed whole (the answer ledger, which no step reads, takes each answer
as it is collected); the busier the head, the more returns one step gates. The exploration has five ends, each stated in
`exploration.json` (stop, rounds, steps (head steps), generations, answers, attempts, every
obligation cancelled or reaped, by id, and `roundDropped`, a round never taken):

- **WITNESSED.** A landed session whose replay was ADMITTED and whose target row at the declared
  occurrence (the last round's `anchorOccurrences`) observed the fatal -- the rule of §7.1 step 6 --
  is a witness: once the head step that took it in has gated it, the next head step -- whatever a
  round plans meanwhile -- is an attempt at every
  witness gated and not yet attempted, one COMPOSE over the corpus as it stands -- `do_compose`, the
  stage's own entry, into `witness-attempts/NNNN/` -- since an observed fatal is not yet a
  composable witness: COMPOSE's families may need sessions later obligations would add
  (`campaign_stream_attempt`; the sessions it composed are its `corpus.txt`). Obligations keep
  starting while it runs; nothing lands, so it reads the corpus as it stood, and what returns
  meanwhile, a witness too, lands after it: one attempt at a time, the witnesses that come during
  one coalesced into the next. Each attempt is a row of `witness_attempts.jsonl` once its outcome is
  known (attempt, step, witnesses, claim, finding kind, polarity, confirmed, its reason, accepted,
  how long its COMPOSE and its CONFIRM took, and `supersededBy`, below); `exploration.json` lists
  them by attempt. An attempt that publishes `SAT_CANDIDATE` with `polarityDecides` is confirmed
  (§10): its task is planned in the step (`campaign_confirm_plan`, its verdict
  `witness-attempts/NNNN/confirm.json`, its replay in `<campaign>/witness-confirm/NNNN/`, out of the
  iteration), a verdict known at once (a refusal, the selected session itself the run) decided there;
  otherwise its replay is a job of the pool (`CONFIRM`, queued first and kept first, no solve's REPLAY
  queued ahead of it, charged as the seed replay is,
  on the class tree and plan of the generation current when it starts), so landing, planning and
  later attempts go on while it runs (hdfs-17967-pathB HG3: a refuted attempt held the head's only
  step for 31 min while the witness obligation waited, unlanded). Its return lands like any job's,
  and the next step decides it (`campaign_stream_decide`, a returned confirmation's verdict going
  before a new attempt); of the confirmations decided together, the earliest attempt confirmed is
  the witness, by attempt order and not by finish time, and a later one confirmed states it
  (`supersededBy`). An attempt whose model is under confirmation is not confirmed twice: its
  witnesses wait and are attempted again once a verdict lands that does not end the exploration.
  Confirmed, the attempt ends the exploration at once: the queue is cancelled, every running job is
  reaped (its process tree here, its workers on every peer) -- an obligation's worker directory moves
  to `<campaign>/explore-reaped/`, as does every one that returned after the step began or whose
  REPLAY is still queued, and a
  confirmation still owed is its attempt's row; a round still planning, or returned and not taken,
  is dropped, its planner stopped first (`campaign_stream_round_drop`: its `planning-NNNN/` to
  `explore-reaped/`, `roundDropped`, owed as `roundDue`) -- and the sessions that landed after the accepted
  attempt composed leave the corpus for `<campaign>/explore-reaped/after-witness/`
  (`exploration.json` `afterWitness`), so the corpus COMPOSE reads next is exactly the one the
  attempt read (its slot table may hold rounds taken since, above); a DIAGNOSTIC `WITNESSED` row goes to `campaign_gaps.jsonl`. Refuted (its replay did
  not reach the fatal at the anchor: a false positive, §10), its model is excluded from every later
  composition and the exploration goes on, as after any other claim; one CONFIRM gave no verdict on
  (a task it refused by name, a decision that failed: a defect of the engine) is excluded from
  nothing. With no room
  left in the campaign's budget
  for a confirmation (`campaign_claim_room`, below), the claim is accepted unconfirmed and the
  final CONFIRM decides.
  A witness whose OWN chain is open is confirmed first and its chain grown meanwhile (owner
  2026-10-06 grew it first; 2026-10-15, best effort and performance first: CONFIRM decides): an
  attempt whose COMPOSE names an open chain (`ComposeMain#campaignClaim` `openChain`: each value the
  claimed path's fatal condition rests on that no attested producer made -- the set
  `experiments/accept/cone.py` reads off the formula, `compose.Cone`) goes to CONFIRM at once, and
  the producers those values' arrivals name that were not grown yet go to the head
  (`campaign_stream_open_chain`), which cancels the queued obligations and grows them
  (`campaign_stream_open`): each later round grows only its exposures of them, each producer once,
  and queues none of its obligations (`campaign_stream_chain_round`); the GROW's swap is held while
  the confirmation is owed, so a confirmed witness ends the exploration with the GROW dropped, and a
  refuted claim (excluded, the false-positive rule) has its witnesses still in the corpus attempted
  again once the GROW swaps in, a re-run landing as a witness of its own
  (`campaign_stream_chain_reattempt`). Growing first held SGF7-18413's real witness (isExpired's
  CLOCK_SKEW, open on node1's view of state.json leaves the Overseer's state-update ticks #30/#31
  wrote unplanned in its world) behind a GROW, its re-runs and a second COMPOSE over a corpus twice
  the size, ~30 min, and parked with nothing to grow it was never attempted again. A fixed point
  ends a chain no exposure reaches; the final claim names each open value (`WITNESS_CHAIN_OPEN`,
  EMIT's `defects[]`). hdfs-adhoc-12 AW2: the HA status txid's export at
  nn0 was exposed by the witness's own session, which ended the exploration before GROW.
  This is every campaign's rule: the question is one declared occurrence (owner 2026-09-28). Once
  the exploration has stopped otherwise, no attempt is made.
- **CAMPAIGN_BUDGET_REACHED.** Between two head steps, whatever a round plans or an earlier stop still lets land (that stop
  named in its detail: SGF7-adhoc-40's planner ran out of heap, and its replays and hard-lane asks drained until the case
  timeout killed the campaign before COMPOSE), the campaign's budget (`campaign_budget_s` from
  the campaign's start; `accept.sh` passes what is left of the case's `CASE_TIMEOUT_SECONDS`) has
  less left than the stages after the exploration are owed (`campaign_claim_room`): its reserve,
  `campaign_reserve`, COMPOSE and EMIT each as long as the longest COMPOSE the campaign measured
  (its stage metrics and its witness attempts; the last planner round, which reads the same corpus,
  standing for a COMPOSE not yet run: its `in_flight.jsonl`, copied as the planner starts, to its
  `explore_manifest.json`, `campaign_last_round_millis`), CONFIRM as long as the longest CONFIRM
  (the seed's REPLAY standing for a CONFIRM not yet run), REPRODUCE its own bound
  (`campaign_reproduce_bound`: `reproduce_time_factor` times the recorded workload, at least
  `reproduce_min_s`) twice -- its native runs go out at once and its control runs queue behind
  them, two waves where the pool holds one --, never less than
  `campaign_reserve_s` (600; a budget not above it is refused by
  `validate_config`). The exploration ends as at a witness (queue cancelled, what runs or returned
  unlanded reaped, a round planning or untaken dropped), and the stop is a DIAGNOSTIC row stating
  what it left owed. A REAP ENDS WHOLE TREES (`campaign_stream_reap`, `campaign_frozen_tree`): each
  process is stopped as it is listed and the tree listed again until no new one appears, before
  TERM, the kill grace and KILL, so nothing a job starts while it is listed outlives the end
  reparented to init (a job forking every 10 ms: 19 of 47 of its processes outlived the old reap, 0
  now).
- **REGION_PATH_WAVE_BUDGET_REACHED.** A round of wave `≥ region_path_max_waves` that still owes
  work is not dispatched (its proposals are named cancelled): the queued solves are cancelled, what
  runs lands -- a solved obligation's REPLAY too -- and the stop is a DIAGNOSTIC row. The wave bound is
  declared and generous: a last-resort valve (RULES, the owner's bound rule), named in `result.json`
  `bounded` like every declared bound that cut the search (§11), never read as the closure's own end.
- **TARGET_FATAL_IN_RECORDING.** The frozen region plan's header names the declared occurrence a BLOCKING
  `TARGET_FATAL_IN_RECORDING` (§9: the recording took the fatal arm there, so no counterfactual is asked of it and
  no claim can stand): the exploration starts no round and ends at once (`campaign_plan_blocker`), the stop a
  DIAGNOSTIC row naming the occurrence; COMPOSE then composes the seed's corpus and names the blocker, and EMIT
  publishes the `RUN_DEFECT` (hbase-adhoc-11 NR5-11: PLAN named it at 14 s, EXPLORE still ran 2 h 4 min before this
  stop existed).
- **FIXED_POINT.** Nothing queued, running or unlanded -- a GROW re-run included, whatever its
  world's depth (§7.8) --, no head step running, no round planning, untaken or owed, and the last
  round, over every answer, proposed and exposed nothing.
- **PLANNER_HEAP_EXCEEDED.** The planner ran out of the most heap a head JVM is given
  (`engine_memory_mb`, exit 3, §7.7): the corpus outgrew what the head can hold, so that round is
  not planned (its `planning-NNNN/`, with its logs, leaves for `explore-reaped/`, `roundDropped`),
  what runs lands, and the stop is a
  DIAGNOSTIC row naming the round, the corpus's size as it decodes and the planner's error, or the
  planner's measure of the round it could not hold, unread (§7.9) -- rounds were still owed. Any other planner failure fails EXPLORE, its deepest throwable the reason.

**THE END IS JUDGED ONCE, AT EMIT** (`campaign_exploration_cut`, the one place; owner 2026-10-04,
only SAT or UNSAT): `exploration.json` states what the end left owed -- queued obligations
cancelled, unlanded jobs and confirmations reaped, GROW re-runs dropped -- queued, or returned
and not swapped in (the exposing round's growth and obligations with them) -- a round due when the exploration stopped
(answers landed since the last round started, re-runs and swaps owed, or a round dropped untaken) -- and an end that owed work
(CAMPAIGN_BUDGET_REACHED or WITNESSED with any of it, PLANNER_HEAP_EXCEEDED always) under a claim
that is no `SAT_CANDIDATE` is one BLOCKING `EXPLORATION_CUT` row: an UNSAT over a corpus missing
those arms says nothing about them, so EMIT publishes it as a `RUN_DEFECT`. A SAT the corpus holds
stands, as CONFIRM validates it (the row DIAGNOSTIC); a WITNESSED end whose witness CONFIRM then
refuted owes it all, since the next claim is composed over the trimmed corpus with no new EXPLORE
(`campaign_next_claim`). FIXED_POINT and the declared wave bound owe nothing here; the bound is
named in `bounded` instead (§11) (HG5A: hdfs-adhoc-17 cancelled 151 queued obligations with none answered, 24 reaped 3
jobs, QJM 07/08/09 cancelled 1215/157/108 and reaped 2/16/25, and each but 07 had published
UNSAT_CLOSED).

A round never proposes an arm answered or in flight (§7.3), so the same obligations cannot be
proposed twice; the wave budget is what bounds the derivation. A case whose corpus outgrows the
8 GB start gives its planner more, and a composer past 8 GB more (`engine_memory_mb`, hdfs-11741's 16 GB): the 70
sessions (5.7 GB on disk) of round a40h2's check DataStreamer-638 ran its round-4 planner out of
8 GB. An end other than WITNESSED on a
last round whose closure was truncated (its `truncated`) is one BLOCKING
`REGION_PATH_CLOSURE_TRUNCATED` row naming that round (`campaign_stream_truncation`): a claim over
that closure misses arms. An accepted witness asks nothing past it, so its rounds' truncations stay
DIAGNOSTIC. COMPOSE, CONFIRM and EMIT then run on the corpus EXPLORE left, as after any end.

`campaign_publish_iteration_manifest` then writes `iteration_manifest.json`: provenance, digests of the
task plan, schedule index, census and obligation results, the members and their obligation digests.

### 7.10 The forced replay: FORCE

Every campaign whose scope map states a forcing table (§2, `plan.ForcingTable`) asks, in its first round and
ahead of every flip, ONE FORCE run of the declared anchor's task (`explore.ForcedFlip`, `Obligation#forcing`):
the recording's world -- no plant, no flip -- held to the seed session's schedule up to the anchor, its focus
row `flip: null` and `force: true` (`ExploreCodec#writeFocusFile`, which states the null). Its worker asks no
solver (`ObligationSolverMain#force`): the answer is SAT_MODEL_READY and the replay runs. In it
(`runtime.ForcedArms`) the declared occurrence, and only it -- on its thread, from its entry until its target
decision -- records from its entry and takes the arms that lead to the throw: at the woven prefix of each
branch of its table (`BranchObservation#prepare`) the runtime asks the VM to force the branch the next marker
marks (`System.forceNextConcolicBranch`, VM.md §2), every evaluation of it (a loop's turns, a recursion's
calls: each forced arm reaches the throw by post-dominance), a decider only inside a call of its helper from
the table row's `via` method (`Identity#callerFrame`, past javac's synthetic `access$NNN` and `lambda$` hops); a
nested planned region, another occurrence or thread is
never forced, nor a switch (the forced world takes its selector's case), nor a `passable` branch (§2: either
arm leads on to the forced guards, and forcing it against its concrete arm would state `false`:
solr-adhoc-07's two `assert`s in `ZkController.register`). A forcing the VM refuses (a negative
status, the call failing) leaves the branch to its operands and decides the run FORCE_DIVERGED at once. The
VM's event states the concrete answer it overrode; the decision row states it
(`DecisionRow#forced`, `concreteOutcome`), and the first decision forced against its concrete arm opens the
forced world. The target row, reached there on its fatal arm, stands at that decision and states as phi the
forced path condition: every decision of the occurrence from it up to the target's, as taken (forced or not;
a concrete one forced against its arm `false`), and the target's own phi (`RowPublication#forced`); it is
marked `forced` and observed no fatal (`TargetRow#forced`), so it is never a witness. The run ends once that
row is published (`AT_FORCED_TARGET`, §5) and its verdict is ADMITTED, `FORCED_TARGET` and how the occurrence
then ended (the target's throw, or a handler that caught it). A `passable` test of the target taken on its
healthy arm decides nothing: its healthy arm runs on to the target's next test, which is forced, and its reach
is not the target row's, which stands at the forced test and states the forced path condition up to it
(`ForcedArms#reachedTarget`; solr-18406 F2V3, `getAndSaveCommitPoint#u11`, the first test of `a || b`; SC1: a
row left at u11, before the forced world opened at u12, stated the plain disjunction, and that forced path made
every witness composition satisfiable at the recorded roots). An
occurrence that closes first, or takes any other test of its target on its healthy arm (a branch no marker of
its frame let the VM force), decides the run there
(`FORCE_DIVERGED`, naming the first exception the forced world threw and its frame, or the loop
bound that cut it, §5); one that never closed
(blocked, its activation stranded at the run's end) is decided at the session's close
(`RowRuntime#closeSession`, `ForcedArms#unreached`). Each way the session is withdrawn, the verdict
NOT_ADMITTED, and the exploration goes on as it would without one: a FORCED session publishes only at its
forced target, and the corpus reads one without a forced target row as no session. A FORCE replay killed
past its bound (`REPLAY_BOUNDED:`, §7.6) decided nothing: the FORCE run is read by its flip as a flip is
(`ForcedFlip#flip`, its row's flip, which its question names and a killed worker, its question withdrawn, is
read by), so it is asked again, and killed twice with no forced session landed it is held unasked, its state
`BOUNDED` and its flip named in the round's `boundedFlips` (a row marked `force`, listed as `FORCE`), which
EMIT names as `replay_timeout_s`: no UNSAT rests unnamed on a forced replay that ran nothing. `result.json`
`force` states the last round's view (state -- `PROPOSED`, `IN_FLIGHT`, the replay's verdict or `BOUNDED` --,
verdict detail, the forced flip and its verdict, read by the flip it asks -- `ExploreMain#answersByFlip`: its
id moves as sessions land -- and `seedFlipsAfterForcedFlip`, the seed path's flips at a site of the forcing
table asked after it was answered).

The session lands with role `FORCED` and is held apart (`explore.Corpus#forcedPaths`): every row of it is
indexed under its session, so its forced path composes and is asked in its own scope, and none in a
corpus-wide view (sessions, rows of an occurrence across sessions, a location's writers and sites, the
schedule's senders), so no other path, arm, slot, closure member, witness or settled arm reads a forced world;
its messages from before the forced world are its own path's arms alone (`Corpus#ownAttachesOf`,
`#ownExportsOf`, `Arms#armsAt`'s scope, the asking path's session), so its handoffs move with their producers
(FlipQuery binds a handoff by its own run's arms: solr-18413 FA2's expiry, a wire value of the Overseer's clock,
was otherwise pinned and the forced flip UNSAT) and no other path pairs with them; `SessionReader#admitted` is
false for it, no write from its forced world on is an alternative writer arm (`Arms#eligible`), nor an
arrival whose producer the closure plans, nor its forced world's mints a root reading (`Corpus#roots`, which
places clocks). Its path, `P_F`, is:
- EXPLORE's forced flip (`ObligationFactory#forced`, `FlipQuery#buildForced`): its decisions before the first
  one forced against its concrete arm as run, and its forced path condition as the demanded conjunct (clock
  margins too), every symbol rule a flip's; the ledger's flip is that decision at its forced arm, keyed apart
  from the seed path's flip of it (another question). Its replay is unforced and cut from `P_F`'s session;
  ADMITTED when that decision takes the arm, a witness when the fatal follows. It is queued ahead of the
  round's other flips, and no flip waits for it or for the FORCE run: the seed path's flips at a site of the
  forcing table go out beside them (solr-18413, round FA4: held behind the FORCE run and the forced flip, two
  replays in a row, its expiry flip's witness came 590 s after round 0, not 251 s).
- one more of COMPOSE's admitted paths (`RestsOn#admitted`, §8): pi its decisions before the forced world,
  phi the forced path condition, composed in its own session's scope -- roots by their corpus-wide names, clock
  cells on the recording's timeline, `v_H` by message families over the corpus's other sessions' exports,
  reads by its own writes. A claim on it is the run as recorded when it moves nothing (§10), never Realized
  (its target observed no fatal), and accepted only once CONFIRM, unforced and on the recording's schedule (not
  the forced run's, `ConfirmMain#write`), confirms it.

## 8. COMPOSE: `compose.ComposeMain` → `compose.Composer`

A merge, not a reconstruction: every value was propagated inside some replay. The anchor is the
declaration resolved against the seed (`ComposeMain.anchorOf`). The formula (`Composer.run`):

```
exactly-one(path_selector_p)  and  or(path_selector_p)               over admitted paths p
path_fatal__p:  selector_p => pi_p ∧ phi_p ∧ reads/joins_p ∧ valuation_p ∧ closure_p
message_family__p_*, writer_family__p_*, observed_family__p_*, state_family__p_*:  selector_p => ...
root_domain__*, clock_domain__*, clock_order__*, identities_distinct__*
refuted_claim__*:  not(selector_p ∧ its arms ∧ its valuation)       per model CONFIRM refuted (§10)
```

BEST EFFORT (owner 2026-10-15): COMPOSE never withholds the `.smt` for a part it can leave out. A
session not read whole (`SESSION_INCOMPLETE`) or whose own verdict disagrees with its worker's result
row is left out (its paths not composed), a path a row refuses is left out (`refusedPaths`), an
unreadable slot table or refuted-claims file is composed without, one solver name for two roots, at
two sorts or for two identities is named, and a path whose own question z3 answers with an error is
left out and the rest composed and decided once more (`ClaimPolicy#REFUSED_PATH`, `ComposeMain#run`)
-- each a DIAGNOSTIC row. Only a total absence blocks: no session states role SEED, no path reached
the anchor, the declared occurrence never ran; and a seed that observed the fatal itself
(SEED_OBSERVED_FATAL: a claim on it would be the recording). Sessions that replace a slot (§7.1) give
no arms.

**Admission** (`admit`, `settled`): one path per admitted session whose target row at the anchor reached
it (beside one, a target row that did not reach it is a DIAGNOSTIC gap); whether the anchor was reached
is asked of admitted sessions alone, once (`RestsOn#reached`, which EXPLORE's flip sites read too,
`ClosurePlanner#plan`): a replay its own rows do not admit is no disjunct and drops no path, even where
it reached the anchor and threw (a DIAGNOSTIC row names it; solr-adhoc-19 F2V4: such a replay made
COMPOSE drop 63 unreached paths); where none reached it, one per admitted
session that ran the occurrence and left the way to the throw at a guard (`RestsOn#wayGuard`: the
last decision at a path site of the anchor's OWN target -- the TARGET_SITE its target row's site
guards, `StaticScopeMap#ownTarget`, never pooled over every throw -- that took an arm off the way,
scanned back past the decisions that kept it -- the arm its forcing table names toward the throw, or a
`passable` branch, §2 -- and past a decider decided in a call from elsewhere than its row's `via`
(the decision row states its caller there, `DecisionRow#via`, `ForcedArms#statesCaller`; a row that
states none, from a corpus recorded before, is taken as the way's); the anchor's own target is found
by the target row's site, its label without the occurrence ordinal (`TargetRow#site`); a site the
table names no arm for, a switch or a fault call, is taken as left; a path that left at G and later
kept the way before a normal return left at G), its prefix the decisions before that guard: at a
SYMBOLIC guard its fatal arm is the guard's other arm, the way to the throw (a witness turns it,
CONFIRM judges the rest), at a concrete one the constant healthy decision (`false`), the guard named
in `concrete[]` as WAY with what its term rests on (hdfs-adhoc-07, 48). A session none of whose way
decisions left the way stopped on the way (a loop bound's cut, an exception, a return): no arm toward
the throw is stated, its fatal is `false`, its WAY row names the anchor and how it stopped. Wherever a
loop bound cut a non-reaching session's occurrence -- before it left the way or after (a later turn of
a loop, in its method or a caller's, may have come back), and whether or not another session reached
the anchor -- a DIAGNOSTIC row
`<anchor> loop-body-bound=<N>` makes the case `bounded` (`loop_body_bound`), so its UNSAT is not done
(CHECKING §1); a cut that names the accounting's own failure (§5) is a BLOCKING `BOUND_INSUFFICIENT`
row, an engine defect (RUN_DEFECT), never a bound (`RestsOn#cut`). Before, such a path's last way decision was composed at its other
arm: solr-adhoc-19 SG2b's u9 (`!inFlightCreations.add`, taken toward the throw before the cut) became
the CONFLICT throw "Already creating", and 19's and 21's UNSATs rested on that wrong arm. The seed
always, a focused session only when all its own verdicts are
`ADMITTED`; an obligation its manifest names with no verdict is BLOCKING, and so is a verdict the row of the
worker that landed the session states differently (`Corpus#waveVerdict`, by session: an obligation asked again
under its id has a session per ask, SGF3-bugs-snapshot-no-active's first NOT_ADMITTED, its re-ask's ADMITTED,
each its own). No target row at all --
the declared occurrence never ran -- is BLOCKING `DECLARATION_MISSING`; no disjunct is BLOCKING
`ADMISSION_GAP` naming the first refusal. Beside them, each forced path (§7.10) is admitted, in its own scope;
its forced path condition is asserted on its own path alone, never on another's, since its constants are the
forced world's and asserting them in another world could make a real witness UNSAT (completeness first).

**One path** (`compose(path, ordinal)`), in its own session's scope:

- P3 closure (`closure`): the occurrences the path's joins reach, each with the seq its prefix runs to,
  including earlier versions of every reached write's location; a refusal is its frame's
  (`frames`, `SmtLowering.RefusalFrame`, `SessionJoin#frame`, `#frameOfWrite`, indexed once per
  session): an `UNSTATED_VALUE` row the session filed on a reached occurrence (a VM-refused attach,
  an attach that minted no `v_H`) is an arrival its run computed on as a constant; its producer is
  the export the refused attach's VM handle names in the session (`ExportRow#handle`), and by the
  one rule below every write of the frame a read joins is FREE over what that export rests on that
  moves (`SmtLowering#frameMovers`: `#movers`, the one predicate every pin asks, through a read to
  its write and a family's re-paired reads; named FREE in `concrete[]` with them), else the frame's
  constants hold, named HELD (its producer unstated where no export states the handle);
- constraint independence (`compose.Independence.of`), by what MOVES: a root of the session, what a
  family binds (an anchor handoff's symbol, a location a STATE family may re-pair), a read whose value
  (its observed write's, walked, and the construction guards of its referent) rests on one. A
  condition stays exactly when one of its variables moves; what phi or a kept condition names is
  bound (the read stating it stays, and what its value names); a condition that only shares a value
  that does not move stays out, since it holds at its recorded values in every world (SOLR-18413
  r9: closed over sharing, the cluster-state map and a serializer's position counter kept 3479
  conditions and reads of one path, a tlog write among them that did not lower); a field
  projection's variables are what its lowering reads (`ContainerSmtCodec#fieldOperands`: the cell,
  and the owner only as a boxed payload), never the owner's `concreteOwner` chain. An obligation's
  key closes over sharing (`Independence.ofGuard`): a question's identity, not a formula;
- the valuation this session ran each non-clock root at (`valuationOf`; `Corpus.rootValue`: the
  focus row's assignment where the replay planted it, else the mint's reading, else the reading
  its manifest states where it read the root at the occurrence of the corpus's mint and minted
  none -- an occurrence run concretely, a mint refused or failed, `concreteReadings`,
  `Corpus#ranRoot`): a declared root minted with no value, or a mint whose `recordedValue` differs
  from the assignment ("stated twice and differently"), is a BLOCKING refusal; a root the sessions
  ran at different values (`Corpus#varied`, readings included) is pinned to this session's value,
  or bounded by its declared window around it; a root this session read and minted none is pinned
  to its reading whether varied or not -- its rows there may hold literals computed from it,
  through state no row tracks, and no term says how they move with it (hdfs-17967-pathA F2b: a
  path whose key-id arm came from a replay that ran the serial concretely, unguarded, was claimed
  at a serial it never ran, and CONFIRM refuted it under every jar; restricting the pin to arms
  whose row-level closure reached the read brought that claim back: DataNodes exported the
  data-encryption key's id from instrumented occurrences with no read row); a DERIVED root -- one
  some session found carrying another input's expression where it read it, a clock-derived expiry
  say (`derivedRoots`, `Corpus#derived`) -- has no reading of its own, and none pins anything; a
  declared root this session neither minted nor read refuses the path only when the path's terms
  name it;
- anchor handoffs, by the one arrival rule (`Composer#arrival`, a path's and an arm's alike):
  bound only by the message family, answered or not (an obligation's answer is
  what its replay planted at the consumer, not what a run delivered, so it is never a literal) --
  a family only where some run attests a delivery AT the attach's slot (`Arms#attestedDeliveries`:
  a run whose own pairing named this consumer ran its producer instrumented, its session not one a
  GROW re-run replaces -- the selection the slot's arms are made by, `Arms#pairings`, one rule for
  both; the family then sets aside the anchor's work past the path, by name); an attested
  producer's export no run paired with this consumer answers nothing here (PV6-18413: one replay ran
  the Overseer's state-update tick w12 instrumented while its own read of the target collection was
  delivered by tick w13; taken as a family no session could send, the leaf refused qn-14's producer
  arms, the state.json@9 family and both witness paths, NO_SUPPORTED_WITNESS; held, the corpus
  composes SAT CLOCK_SKEW). Still family-only, so an arrival only they leave without a sender is
  refused rather than settled (TODO): the anchor's work past the path, an arm naming a root its
  session minted no row for, and a message no one run sends at every leaf. An attach with no such
  run (or with no producer named) has a producer no row states, named for which case it is ("no
  session ran its producer instrumented", or "ran instrumented in N run(s), none of which paired it
  with this consumer"): HELD at the value its row states it received, conjoined with the path (inside an arm: with
  the arm's body) and named (`Composer.Concrete` HELD, "producer unstated", its `arm` the arm whose
  body holds it, none on the path's own) -- a String arrival held at its text (`Composer#arrived`)
  --, except a store content leaf (`contract.ContentPort`) whose producer no session attests at its
  port (`Composer#refusedByRule`): a role, which no weave captures (`ROLE`); a daemon tick past the
  recording's last, `Corpus#tickPastRecording` (`TICK_BOUND`); or a region no run ran instrumented
  and paired with this consumer where it wrote that port (`UNATTESTED`: which tick of a periodic writer writes a document's key is
  timing -- solr-18413 SG3C's Overseer state update that wrote the routing rule's `expireAt` ran
  instrumented 21 times, never writing it): that producer's own export at the port in the leaf's run
  (`Composer#delivery`) settles it. An expression binds it, the leaf stated as the
  export (several: one of them) with what its lowering requires and each handoff it names taken by
  this same rule -- the producer's path condition is not stated, an over-approximation CONFIRM
  filters -- named `EXPORTED`; a constant expression holds it at its received value, named
  `CONSTANT` (a role, or unattested), and `BOUNDED` past the tick bound, a named bound the case rests on (a
  DIAGNOSTIC `<producer> daemon-tick-bound=<last>` row, `run_engine.sh campaign_bounds`:
  `daemon_tick_bound`; the same row names a message no session sends whole whose unanswered leaf
  that producer wrote, `ComposedFamilies#nameTickBound`, since the arm handed it is refused for that
  bound). These three are no open link of a chain (`SmtLowering#settled`, `Cone`;
  `cone.py`'s `exportedByRefusedProducer`, `constantByRefusedProducer`, `boundedByTick`), one
  DIAGNOSTIC per producer, rule and kind counts the leaves on the paths kept. No export that lowers
  leaves it HELD and open, as a leaf with no producer; one whose producer is attested and no
  export of it lowers, or whose row states a value the lowering places nowhere, is FREE, named:
  nothing pins it, and a path is never dropped for it;
- THE ONE RULE for a value COMPOSE cannot bind (`SmtLowering#unbound`): FREE, named with what it
  rests on, where its stated producer rests on what can move; HELD at its recorded value, named
  "producer unstated", where no row states its producer; never free by default, never a silent
  pin. Every `concrete[]` row names the path it was composed on (`pathId`) and why (`reason`);
- the read rule (`statedReads`, `stateJoins`, through `SmtLowering.bind`, the guarded read's rule
  too): JOIN to the observed version's write expression if it lowers with no refusal, else the MINT
  of that version (a placeholder), else -- where what the refused write rests on can move (a root, a
  clock cell, a handoff, an anchor location a STATE family may re-pair: `SmtLowering#movers`, the one
  walk every pin asks, a method return's and a container answer's too, and EXPLORE's flip query
  alike, where a read of any location with write rows moves, `SmtLowering#forSession`) -- FREE, the
  read unconstrained and named with what it rests on (`SmtLowering#unbound`, a `Composer.Concrete`
  FREE in `concrete[]`), since a pin would hold it while a witness moves that; else, a version no
  write row states (a store outside every activation, `UNATTRIBUTED_STORE`) of a location a writer
  choice re-pairs (`SessionJoin#repaired`: in a flip query any location with write rows), OWN -- the
  read's own symbol, which the writer choice binds beside the run's arm holding it to what it read,
  as a read whose writer is known (`SmtLowering#bind`; hdfs-adhoc-39 OA4's `BlockInfo.uc` read of
  the completion); else PIN to the value the row states (a version no write row states: HELD, named
  "producer unstated"), else FREE all the same, named (`UNSTATED_VALUE`, DIAGNOSTIC: havoc, owner
  2026-10-15; SGF8-adhoc-21 had dropped 10 paths on map reads whose write did not lower); a write of a frame whose producer moves is FREE before any join; dropped, the
  join raises nothing (no refusal, side condition or gap); what a read
  row's binding required
  (container membership and cell tags, recorded readings) is stated with its join, so only where
  the conjunction asks about the read (`Composer#statedJoins`, `SmtLowering#ownConditions`); an
  object the VM named (`M_L'<class>'_<rid>`, an array `A<type>_<rid>-<version>`) is the reference it is, whatever its class, where a
  whole value is asked
  (`SmtLowering#whole`: a join, a published expression, a stated value) or a reference is (a
  comparison asks a named operand at the other's sort, on either side, `#binary`); an operator
  asks for its own operands, and a named container there is its state, at its class's sort
  (`Host#state`: that object's own state root, `container__`);
- `pi_p`: the anchor's decisions strictly before the target row's seq, and each reached occurrence's
  decisions before its cutoff;
- `phi_p`: the published `phiTerm` (fatal polarity); a concrete fatal condition's `true` is the
  fatal resting on `pi_p`, the path condition that reached the anchor, and its `false` the constant
  healthy decision: the path is a disjunct no valuation satisfies (symbolic stays symbolic, concrete
  is a constant), so a corpus whose paths all decided concretely closes UNSAT, its formula stating
  the decisions the path took up to the target, the anchor's own included, or for a path that never
  reached the anchor up to the guard it left the way at (`Composer#healthyDecisions`: each pi_p does
  not state, as a proposition named for it at the arm it took, `decided__`, its term in `concrete[]`
  as DECISION; a term over nothing that moves adds no answer, and lowered it contradicted the run
  where the lowering is less precise, hdfs-adhoc-07), never a bare constant; a row stating no phi refuses the path (invariant 9), as the composer never invents one;
- every other handoff the conjunction reaches, by the same rules; a handoff variable the corpus
  states of another session and this one minted no attach for refuses the path by name
  (`UNSTATED_VALUE`), so no path names a boundary variable its families do not bind.

A value the lowering has no semantics for (`SmtLowering#refuse`: a model it lacks, e.g.
`Long.parseLong(s, 16)`, `MODEL_SEMANTICS_MISSING:...:RADIX_NOT_10`) does not drop the path: the value is a
fresh constant, free, and the path stands on it over-approximated, named by a DIAGNOSTIC `UNSTATED_VALUE`
(havoc, owner 2026-10-15; CONFIRM filters a false witness: every path of SGF8-adhoc-14 rested on one such
parse of a shard's hash range, and the composition kept none). Any other refusal drops the path and is filed
with its own class; a dropped path is never silent: the claim names every admitted path
COMPOSE refused, with its first refusal (`Composition#refusedPaths`, `result.json` `refusedPaths`),
and an UNSAT says nothing about them.

A FATAL ARM THE RECORDING DID NOT TAKE IS HELD TO ITS RECORDING WHERE NOTHING IT RESTS ON MOVED
(`Composer#hold`, `Composer.Hold#held`). Where a path's fatal arm -- the published phi of a target row whose
run did not throw (`observedFatal` false), or the other arm of the symbolic guard it left the way at -- names
a free leaf of that kind (`SmtLowering#havocLeaves`, through the shared terms), the arm becomes
`(and fatal (not H))`, H the conjunction over every mover of the arm's published expression
(`SmtLowering#movers`, the walk every pin asks) at its recorded value: a root at its mint's value in the
path's session, an attach at its arrival, a re-paired read at its stated join in this path (the read takes
its observed write: the `joins` entry of each read symbol of that location and version); with no mover the arm
is `false`. Sound in two parts. (a) In the program the arm's expression is a function of its movers: the
unmodeled operation computes on operands the expression states, so with every mover at its recorded value
the expression has its recorded value, the healthy one. (b) CONFIRM plants only movers (roots, clock skews,
answers, pairings), so a world where every mover is at its recorded value replays the recording and cannot
be confirmed: excluding it loses no confirmable claim. A read the path states nowhere adds nothing to H by
(b): the formula never moves it. Three movers have no recorded value H can state, and leave the arm free,
named (`UNSTATED_VALUE` DIAGNOSTIC on the phi, "not held to its recording"): a clock (or a symbol no mint or
attach of the session states), a view leaf (it moves with its view's pairing too), and a frame's leaf (it moves
with the frame's producer, which the walk does not reach). A fatal the recording took is never held. Before,
the free leaf let `ClaimPolicy#closed` take the run as recorded for a witness: hbase-adhoc-15 HP8-15's seed path,
whose phi `"OPEN".equals(state)` (an enum read the lowering stated at REF) was a leaf nothing pinned, was
claimed `FORMULA_SAT` moving nothing, and CONFIRM refuted it.

THE COMPOSER'S HEAP BOUNDS ITS PATHS (`Composer#HEAP_SHARE`, 0.8): once its old generation is past that
share after a sweep (`HeapWatch#oldGenerationSwept`), the admitted paths not yet composed are left out, each
named `COMPOSE_HEAP_BOUND` (DIAGNOSTIC, in `refusedPaths`, so a witness among the composed ones still goes to
CONFIRM), the first path always composed; the campaign names the bound once, BLOCKING (`campaign_compose_bounded`,
stage COMPOSE), so EMIT labels the run RUN_DEFECT beside the formula's claim, as a truncated closure. Between
paths the composer drops every subterm its lowering minted that no statement reaches, and its mint
(`SmtLowering#path`): a join no conjunction asks about, an arm left out, a refused path; one a later box reads
back through a cell is kept. A subterm is named by its prefix and its identity's digest, so lowered again it has
the name it had, and the body is byte for byte the one a composer dropping nothing writes. What a path still
leaves is its statements, the declarations of the names its lowering touched (`declared` decides domains, pins
and refutations) and its manifest rows (SGF8OOM-adhoc-14 at 20 GB: about 110 MB a path over an 8.5 GB corpus,
against 400 MB before, so 27 of its 353 paths composed before the bound, against 6); its progress line every
minute says how full the old generation is. A composition whose paths all fit the bound can still run out of the engine heap
building the body (SGF8-adhoc-05: 332 of 332 paths at 73 %); `do_compose` then composes again with half the
paths the composer said it composed (`ComposeMain --max-paths`, the rest named `COMPOSE_HEAP_BOUND` as above),
until one composition ends or one path is all it had.

THE COMPOSER HOLDS WHAT THE PATH IT COMPOSES ASKS FOR, AS FAR AS ITS HEAP HAS ROOM (`Corpus#holding`,
`contract.RowHold`, `RowHold#SHARE` 0.6). Its corpus is read `Parallel#READS` sessions at a time, the next ones
read while these are indexed, as a corpus holding every row indexes it (each session in read order, the forced
ones after), and of each session's rows its reads and writes -- with what the corpus builds of them alone: its
state join (its writes by version and by location among what it answers), its reads by symbol, its rows by
occurrence, the answers that hold rows (`Corpus.StateRows`) -- are held apart: every one while the composer's old
generation after its last sweep (`HeapWatch#oldGenerationSwept`) stays under 60 % of it; each sweep past that
halves the decoded text the hold may hold from then on (said in the log: `hold: the old generation N % full after
a sweep: ...`), the sessions asked for least recently let go of first and read again from their files when next
asked, value for value (a landed session's files never change; reads and writes side by side). Held, the rows
take a small part of their text (pooled): SGF9-adhoc-40's 8442 MB of reads' and writes' text held whole cost
~450 MB more of the old generation than 2293 MB of it. Its paths ask a wide, recurring set: 1-156 sessions'
reads and writes a path (median 4, mean 21), 150 sessions (4.4 GB of text) asked by 10 paths or more,
consecutive paths sharing a median of none -- so the bound this replaced, 0.15 of the heap counted in text, let
each go before its next ask (`analysis/solr-2026-10-18/hold/`: an LRU replay of 40's asks misses 3968 times at
2293 MB, 461 at 5000, none at 8442). Held whole, 40 composes in 396 s against 1426 (3859 sessions read again,
110 GB), the old generation's peak 29 % against 27 %, the formula byte for byte the same (OPTIMIZATIONS 1.51).
Every held row is let go of before the body is lowered (`Corpus#letGo`, `RowHold#letGo`; read again from its
files if a path is composed again): SGF9-adhoc-05's 340 paths composed with all 427 sessions held, and its
16384 MB composer ran out of heap building the 1083 MB body (11.1 of 13.4 GB of old generation live after its
last full collection); let go of first, the body is lowered in 44 s and COMPOSE ends in 1391 s.
Every other row of every session stays held --
decisions, activations, attaches, exports, roots, targets, expressions, the gap kinds a corpus reads -- since a path's families ask most sessions for them: SGF8-adhoc-39's paths asked 52-71 of its 71
sessions for the decisions, activations, exports and expressions of their arms (every sender's pi and export),
and 1-8 for their reads and writes (the path's own session and the producers whose arms it closes); the final
phase asks every session once. Before the rows were pooled, reads and writes were most of a held corpus: SGF8-adhoc-13's 201 sessions held
1260 MB with them, 516 without; SGF8-adhoc-07's 358 (28.4 GB of rows, 14.6 GB of them reads and writes, 1.9 GB
gaps) filled 85 % of its composer's old generation, and 1 of its 309 paths was composed. Nothing else the
composer keeps holds a row it let go of: an index across sessions keeps an endpoint's occurrence, never the
endpoint (`Corpus#occurrenceOf`); `Arms#constructs` remembers a write by its endpoint's id; the slot table is
read for the sessions that replace a slot and the WIRE consumers it opened, then let go of (`Composer#unopened`;
07's 1.58 M slots held their own endpoints and frames); and a root's domain asks for the literals recorded
decisions compare it with only where they widen it (`RootDomain#widened`: an integral configuration the case
declares nothing for), each root's a walk of every session's decisions reaching it, lowered with that session's
reads and writes (07's 367 fault markers were each asked). The formula, its manifest rows and gaps are byte for
byte a whole corpus's (13, 39, 21, 10 at the composer's hold and at none; every composer test composes over a
corpus whose every sweep is past the share, so it holds next to nothing). 07 at 21504 MB, held at 0.15 of the
heap's text: 309 of 309 paths composed, 2.9 GB live after the read, the old generation 54 % after the last path.

Then **message families** (`ComposedFamilies.closeFamilies`): attaches grouped by correlation id,
one message under one selector; the eligible senders are the
sessions with an attested arm at every leaf of the message whose world's flip set contains or is
contained in the path's, and that ran none of the roots their arms are guarded by at another value
than the path's own session ran it at -- both judged against the PATH's session at every depth
(`ComposedFamilies#compatible`): the path carries its own run's valuation (`Composer#valuationOf`),
so an arm pinning another is never chosen, and, the one arm left, it made the path unsat with its
own run (solr-adhoc-39 SP6-39: the seed's delivery, admitted because its flips, none, are a subset
of the faulted session's, pinned that session's fault at the seed's reading); pins alone admit
incomparable worlds, whose deliveries contradicted 51 of SP6-39's 56 paths;
one `message_arm__` selector per sender (identical arm bodies share one),
exactly one, each arm guarded by its replay's value of every root it holds under (`Arms#arm`:
those its expression names, every varied root, every root its replay read and minted none -- the
valuation its path would carry, never a clock nor a derived root; a guard symbol no row has
declared yet is declared at its root's sort) and closed like a path in its own session (producer prefix before the delivery, its
P3 closure, nested families to depth 16). Every handoff the arm's conjunction names, its delivery's
and those its closure's conditions and joins read (`ComposedFamilies#handedOn`), goes by the path's
own arrival rule in the arm's session (`Composer#reachedHandoffs`): an attested arrival -- a run
attested at its slot (`Arms#attestedDeliveries`) -- is a nested family; one no run attests there is
HELD at the value its row received, conjoined inside the arm and named in `concrete[]` with the arm;
one whose attested deliveries do not lower is FREE, named; only one its session minted no attach for refuses the arm. So an arm is never refused
for a handoff its closure merely reads (hdfs-11741 PS1-PS3: the SASL sender's arms read, through the
balancer's key-updater tick, the expiry dates of a refresh whose NameNode handler no session
instrumented; refused, they took the key id's binding with them). A path closes each message once (one family,
one name), under what rests on it: the path's own messages under the path selector; a message a
delivery was itself handed under every arm (message or writer) whose conjunction names its
handoffs, asserted once the path's arms are all known as `(=> <path> (=> (or <those arms>) F))`
(`ComposedFamilies.Closed`, `#commit`), so an arm not chosen imposes nothing and a chosen one's
nested message holds as it was closed (hdfs-11741 m1: another run's six-key export, nested under
the path, contradicted the five-key export of the path's own run in 234 of 235 paths). Its arms
are chosen only with one of those (`(=> (or <its arms>) (or <those arms>))`), so the model's true
arm selectors are the chain its path took. A level's messages are closed before any of their arms
closes its own; an arm resting on a message the path closed already is one more thing resting on
it. A copy per arm instead is a family per arm per level: hdfs-11741 i1's body ran an 8 GB heap
out. A refused arm, or one whose body equals an earlier arm's (it rests on the same messages),
takes back what it stated (`ComposedFamilies#rollback`), its `concrete[]` rows included
(`SmtLowering#unboundRollback`): a row is the arm's only while the arm is in the formula, one per
value and arm. A message no session can send drops the path.
THE PATH ENDS AT ITS THROW (`Composer#leftPath`, a WIRE arm at every depth and a STATE arm alike):
the path's anchor occurrence runs the path's decisions up to its fatal decision -- the target
decision, or the guard it leaves the way at -- and no further, so an arm whose producer is the anchor
occurrence is no producer for the path where it was delivered, in its own session, after the
anchor's last decision at a site and turn the path also decided (`site#ordinal`) when that decision
took another arm than the path's or is the path's fatal decision; in the path's own session, after
its fatal decision. Each such arm is named (`ADMISSION_GAP` DIAGNOSTIC, subject `<slot> of
<session>`), never dropped silently; what was handed only such work -- solr-18413 SG3G/SG3H: the
seed's Overseer write after REMOVEROUTINGRULE, which the anchor offers on the branch the path's fatal
arm rules out (DistributedZkUpdateProcessor:950-960 against :925 -> :934) -- has a nested message no
session can send, so its arm is refused by the rule above. Only the anchor's own rows are ordered,
by program order against its own decisions: no producer of another occurrence is excluded by where
its rows stand (a writer on another thread keeps its arm whatever its seq), and a run that decided
nothing the path decided before the delivery says nothing: the arm stays.
WHAT THE VIEW HOLDS AT ANOTHER VERSION RESTS ON THAT CHOICE (`SmtLowering#viewGuarded`,
`ComposedFamilies#closeViewVersions`): a content leaf read through its node's view is the leaf of
whichever decode the view holds, `(ite (= V v) leaf_v ...)` over every version the node decoded, later
ones included (`SmtLowering#throughView`); what the path lowered only in another version's case rests
on that version's choice `(= V v)`, so that version's messages are closed under the choice, as a
nested message under its arm, never under the path alone, and their arms are chosen only with it. In
nested views a symbol rests on its innermost case's choice alone (the inner view's read is the outer
case's own: where the outer version is not held the inner choice is free; joined, a symbol took one
conjunction per path through the nesting), and the frame of a memoized lowering carries what it
lowered inside a case, so every hit records it (`SmtLowering.Raised#viewLowered`). A
version none of whose content the path names can be sent -- no session sends its message, or one of
its leaves no producer the corpus attests made -- is no version the read is paired to: the path holds
`(not (= V v))`, named (`UNPRODUCIBLE_ANSWER` DIAGNOSTIC, subject `version v of <view>`), its leaves
`UNPAIRED` in `concrete[]` (a settled kind: no open link, cone.json's `unpairedVersion`), and the path
stands. solr-18413 SG3G/SG3H: the path read node1's view at v9; the decode of v10 after its fatal
decision, sendable only by the seed's write after the anchor's REMOVEROUTINGRULE, forced that write's
arm on the claim (CONFIRM refuted it), and with the path-end rule dropped the path; now the claim
stands on the path's own arms at v9.
Each leaf an arm binds (a declared port's delivery) is noted with the occurrence it was delivered
into and whether its value rests on
a clock (`ComposedFamilies.BoundLeaf`: a CLOCK root the delivered value reaches, or a nested
delivery that does), for CONFIRM. A path's
families (message and state) are all or nothing: their named assertions, arm choices and families
are stated as they are made and taken back with a refused path (`ComposedFamilies#discard`,
`SmtLowering#retract`), so the next path, composed at the ordinal a refused one left free, names
nothing twice.

**State families** (`stateFamilies`), for the joined reads the stage re-pairs (`SessionJoin#repaired`,
one rule, one entry point, `Composer#repairing`): the anchor's up to its cutoff and every read its phi
names by read event (a target a helper decision decided stands at that decision), and every read the
selected session's world planted a pairing on (`Corpus.World#pairings`, each with every read its
occurrence made of the location, as the replay held them), each block of one occurrence's reads of
one location by the same test -- a named owner, and a read of it that could have seen a writer
besides the one it did -- and both less the owners `Composer#pinnedOwners` keeps; away from the anchor, its occurrence reached by the closure
(hdfs-bugs-slowdisk-zero: the detector turn's read of the exclusion bound, whose guard and store
the anchor's read of the published list rests on); of a static field or of a heap
location whose owner is an object rid (`Arms.namedOwner`; a class-name owner gets no alternatives):
one `writer_arm__` selector per writer occurrence of the same session (`Arms.stateArms`: the
observed writer's arm is the write the read observed, any other writer's its last write of the
location, and only attested ones the read could have run right after, `Arms#eligible`), one for the
location's INITIAL, the writer at version 0, where the read observed it or the same rule admits it
(its arm binds the reads to what the location held and rests on nothing a run
decided, `ComposedFamilies#initialBody`), plus an `observed_arm__` holding each read to its
own join or pin wherever the run is no one writer's arm -- the reads saw several writes (a nested
region of the reader's own thread wrote between two of its reads: hdfs-adhoc-23's
`StorageInfo.layoutVersion`), or a version one of them observed has no writing row, or -- THE
RUN AS RECORDED IS A WORLD -- the one writer every read observed is no arm of the run because its
selector binds its whole block (every location its arm states here) and the run read another
location of that block from another writer (hdfs-adhoc-16 HG5A: a `Block` constructor wrote
`blockId`, `genStamp` and `numBytes`, and the run read the last two from later writers; one pass is
the fixed point); the writer
arms stay beside it, each binding every read, and where the reads saw several versions only a
write each of them could have seen (`Arms#eligible` for every version; hdfs-adhoc-16: the first
read's own later write is none); exactly one per location that has two arms or more, one of them
an HB-concurrent writer's, else the reads keep their own joins, which are the run. The read
rule's "a location a STATE family may
re-pair" (`Composer#repairing`) is the same alternative: a read of it could have seen a writer
occurrence besides the one it did (`Corpus#eligibleWrites`; a version no row wrote has none of its
own). A hot field the reader's own occurrence alone writes, whose earliest versions the VM's
64-version bound dropped, is none (hdfs-17960 e1c: the checkpoint saver's configuration parse,
whose `Hashtable` entries' hashes, a `String.hashCode` no lowering models, are pinned). The arm the
run took (the observed arm, else the one writer every read observed) is part of the path's recorded
pairing -- at a location the world planted, the recording's pairing, any arm but the plant and the
observed arm, which holds the reads to what the plant gave them (`(not (or <plant> <observed>))`),
so a witness that needs either names it as the arm it re-paired (`repairedArms`) and the recording
decides it (STATE_PAIRING_FLIPPED). The run is always a world of the formula: where the one writer
every read observed has no selector -- its write is no arm here (`StateLocation#unoffered`) or its
body did not lower (SGF3-bugs-snapshot-no-active: a StateWatcher decode was handed a version of
`state.json` whose content an unplanned second `setData` of the Overseer's state update wrote,
uninstrumented, so no session attests that message whole, `UNPRODUCIBLE_ANSWER`) -- the location is
held by its observed arm (`StateFamilies#holdUnstatedRuns`), as a broken block is, beside its other
writers' arms. The reads keep their joins; that writer's closure and store-state choices are not offered
there: one DIAGNOSTIC
`UNSTATED_VALUE` row per hold names the path, the location, the writer and what refused it.

**A store content's leaf through a node's view** (`SmtLowering#throughView`, SYMBOL-SCOPE §6.4). A
guard that decides on a node's view of a store location -- Solr's `ZkStateReader.clusterState`,
re-pointed by each decode -- reads the leaf of the decode the view held. The field read of the view
reference cannot carry that leaf: the VM states the leaf's value where the decode's construction
stored it (a `Replica`'s state, four containers below the `ClusterState`, by value), so no
projection through an owner (below, one level from the movable read) reaches it, and the field is
re-pointed by every collection's decode, mixing locations. The family is over the PROVENANCE read's
VIEW instead (`LocationKind.VIEW`, the reading node and the store path), whose writers are that
node's decodes: where a read of it a family may re-pair stands in the path, a content leaf's attach
symbol of that view lowers as `(ite (= view v_1) leaf_1 ... leaf)`, the leaf of each decode of the
node that took it in, defined only where the view is one of them (`#perCandidate`); with no such read
it is its own. Each case is the plain leaf of that version's decode, what its writer's export binds:
a leaf of the view being cased is never cased again through the read that observed its version
(another reader's choice, not part of what the decode produced; solr-adhoc-40 SL1, one view read at
ten versions, was cased through every order of them), while two reads of one view, each a guard's,
each choose their own case; a view's answer is kept per leaf once per memo.

**A field through a re-pointable owner** (`SmtLowering#projection`, reached from the codec's
`Host.projection`). A field projection whose pair (`concreteOwner`/`concreteValue`) is stated
lowers to the run's cell, except through an owner that is a read `stateJoins` joined at the anchor
at a location a STATE family re-pairs (`SmtLowering#movable`: the family may bind it to another
writer's object; that read alone, by its event (`SmtLowering#readKey`), so another occurrence's read
of the location at the same version -- a writer's own lookup -- keeps the run's object). There it is the
field of the object the owner is, by the one rule for what is asked through such an owner
(`perCandidate`, R3-REFCONT's "answer per candidate identity"):
`(ite (= owner id_run) cell_run (ite (= owner id_k) cell_k ...))`, conjoined with "the owner is one
of these, and that case is defined". The run's object is the owner of the cell `concreteValue`
read, else `concreteOwner` when it spells an object; a pair naming neither refuses the path
(`UNSTATED_VALUE:OwnerCandidates:<location>`). The other candidates (`candidates`, C(r)) are the
objects of the projection's class that this session's writes of the owner's location reach, through
the reads in them. A candidate's cell (`fieldOf`) is the one write of it in the session, made
before the location first stored the object, or, never written, the one value every read of it
states at one version. A candidate with no such cell is no case, so the arms delivering it are
refused, and it is named DIAGNOSTIC `CANDIDATE_UNANSWERED:<cell>@<session>`, the refusals of a
write that did not lower in its detail. A candidate's write whose lowering reaches the very node
asking for it (`b.numBytes = f(owner.numBytes)` where the owner may be `b`) was read before it was
written: the memo refuses a node reached inside its own lowering (`LoweringCycle`,
`SmtLowering#memoized`), so that candidate answers nothing there (a40h2's FsDatasetImpl-1092 and
-1424 recursed until an 8 GB heap was full). EXPLORE lowers through
the same rule; its owners are never movable (a joined reference read is inlined), so a projection
there is the run's cell.

**A container queried through a re-pointable owner** (`SmtLowering#query`, reached from the codec's
`Host.query` for a relation stating `owner` whose answer is no state; a state is never selected,
since an array-valued choice over lambda terms is outside what z3 decides). Through a movable owner
(`#movableOwner`, the projection's own test) the query is asked of the object the owner is, by
`perCandidate`, for the object the owner read returned (its joined write's identity, else the one
its row states) and each other object a write of the owner's location stored (`candidates`, any
class): the same relation over each state of that object the reader could have seen through a store
of it (`#answerOf`), its receiver beneath views and iterators replaced by the state's chain
(`#asOf`). Through one store, those states are its `referentState` and the later versions the reader
could have seen (`#statesOf`, R3-REFCONT §1.4, the one rule EXPLORE also demands by): the version
live at the read in session order (the store's own when every one came later), and each later one
whose writer is HB-concurrent with the reader (`SessionJoin#concurrent`, `Arms#concurrent`). Each
state is chosen by a nested selector `nest__<digest>`, one per (read, object, version), so every
query through the read sees the object at one version; a family arm delivering one store holds them
to the states seen through that store (`#storeChoice`, conjoined by `ComposedFamilies#producerBody`).
Another object's answer holds exactly one of its selectors (a state a query has no answer at is none
of its options). The run's own object answers as the run saw it through the store the read observed,
and through any other store of it (a re-store publishes a later state) the states seen from that
store's referent on: at most one of those selectors holds, none being the run's answer. A read is
movable only in the path whose anchor joined it (`SmtLowering#path` clears the set when a path
begins), so a message arm lowered in another session's scope asks the run's answer there. Every
selector the path minted holds only under an arm of it that delivers a store its state was seen
through (`nest_family__<N>__<digest>`, `ComposedFamilies#stateFamilies`), so with the observed
store's arm, the pins' or no family, the run's object is the run's answer. A state rests on what
made it: under its selector, the arm conjoins the decisions of the closure its write adds to the
store producer's (`ComposedFamilies#stateClosure`, `RestsOn#closure` seeded with that write, the
writers EXPLORE demands), each before its cutoff, and joins the reads they name; a state whose added
closure the recording does not state is no option (`(not nest__…)`, its refusals named
DIAGNOSTIC). An answer holds only where the
owner is its object, so what its lowering requires is its case's precondition, never the path's. A
store that states no state (`referentStateRefused`, none, a version no write row states
(`UNPUBLISHED`), or no version lowers) delivers no case,
named DIAGNOSTIC `REFERENT_STATE_UNSTATED:<reason>:<object>@<session>`. A container query's read
names no object, so a location a family re-pairs whose query reads a field or a query is asked
through keeps the run's pairing (`OWNER_PINNED_BY_CONTAINER_READ`, below); a re-paired reference
whose write and row name no object refuses the path (`UNSTATED_VALUE:OwnerCandidates:<location>`).
`ENTRY` is a view to walk through; as a value no
`Value` spells it, and it is refused by name.

**A container read the family re-pairs** (`SmtLowering#movedQuery`). The anchor's read of a container
location a STATE family re-pairs (`SessionJoin#repaired`, per read event: the anchor's reads up to its
cutoff, `Composer#repairing`) asks its query of the read's own symbol, the state its join states at
the container's sort and each writer arm binds to that writer's state -- the INITIAL's arm to what the
location held before every write (`ComposedFamilies#initialBody`) --, not of the run's chain, which
inlined is the run's answer no family moves (zk-bugs-election-offer: the getData's lookup of an offer
in ZooKeeper's node map). The base a query requires of its chain (`requireStatedContainerBase`) is the
observed version's: every version of one location descends from it. A query through a view keeps the
run's chain (its positions are the chain's).

**What a state arm states for CONFIRM** (`SmtLowering#stateChoices`, `ComposedFamilies.ArmChoice#states`).
A query's reads are the container reads (MAP location) of the owner's reader whose joined value was
being lowered when it was asked (`#askedThrough`, the reads `#answering` holds). A writer arm carries,
for each store it delivers, each state a query through the read may have seen with its selector, the
write of that version and those reads; the claim keeps the ones the model chose (`ArmChoice#taking`,
the nested selectors asked beside the arm selectors, `Composition#stateSelectors`) and publishes them
per read as the selected arm's `referentStates` (`{selector, reader, writer, location, version}`,
`ComposeMain#referentStates`; a query no read answered is one row with an empty `reader`).

**New map operations** (`ContainerSmtCodec`). `READ_OR_DEFAULT` (`getOrDefault`) is a read whose
absent key answers the default. `PUT_ALL` (`putAll(m)`) puts, in the order m's chain put them, each
key m's chain names above its exact empty base, where m holds it (`assoc_put_if`, the guard inside
each component as `assoc_remove_if`'s); a source whose chain bounds no keys is refused by name
(`ContainerRelation:ASSOCIATIVE:PUT_ALL:source-keys-unstated`), and a view over the result counts
the source's keys. `MATCHES [k, e]` (the test a conditional mutator made) is whether the cell at
`k`, the null cell where `k` is absent, is `e`'s, tag included (`(= cell e)`): it guards the
`PUT_IF`/`REMOVE_IF` of `putIfAbsent`, `compute*`, `merge`, `replace(k, e, u)` and `remove(k, e)`,
and `CONTAINS` that of `replace(k, v)` and a set's `add`. An `UNKNOWN` cell -- what a callback the
run never ran would have stored -- is the MINT of a free `Value`, `unknown__` for its session and
`answer` id (`SmtLowering#unknown`, DIAGNOSTIC `ContainerCellUnknown@<session>`). A read at a
literal key passes guarded mutations at other literal keys as it passes plain ones. A queue's `PEEK` is its head, the null
cell where it is empty and no member required; `POLL` is the queue without its head, a shift at 0
where its size is a stated nonzero literal, itself where it is 0, and refused by name over no
stated size (`ContainerRelation:INDEXED:POLL:unstated-size`). A String a map
answers is its cell's `valueString`, null where the cell is the null cell `(VRef nullRef)`
(`ContainerStateModel#unboxValue`, `ContainerSmtCodec.Term#nullness`). A cell a map answers where a
reference is asked (the one unboxing at REF) is an object's reference, the null cell, or a String --
one stored in an Object-valued map, and an enum constant, which the VM states by its name (a
`ConStringSymbolExp` of type String: the put side cannot tell the two, `SmtLowering#boxed` boxes by
sort) --, whose reference is its `string_ref`: one per String (its inverse `ref_string` is stated for
each String the query names, quantifier-free), never null. A String compared with a reference (an enum
constant against a map's answer) takes the same reference, and a reference read out of a cell boxes
back to that very cell (`SmtLowering#cellOf`: `commandMap.get(action)` after `actions.get(op)` finds
the name it was keyed by). solr-bugs-reindex-cleanup SGF: CollectionAction's actions map, read
through SC's `toLowerCase` as a VRef, contradicted every path through `CollectionAction.get`.
A value the lowering hands
the codec keeps what it stated (`SmtLowering#codecTerm`): a String its nullness (a recorded String is
not null; hdfs ad-hoc `FinalizeCommand.blockPoolId` read off the command list reached `equals` as of
unknown nullness), and an answer per candidate object is null where its case's is, of unknown
nullness only where a case states none (`#perCandidateTerm`), which an operation dereferencing it
still refuses by name. A cell holds what Java stores: an object, a container included, is boxed as
its reference (`Host#box`; hdfs ad-hoc `bpStorageDirMap.put(bpid, dirs)` was cut `CannotBox`). An
object reference is an opaque identity: one the VM named (`M_L'c'_rid`, or an array's `A<type>_<rid>-<v>`, one identity at every version) is non-null and distinct
from its session's other named objects, one it placed unnamed (`P_L'c'_`, made only for a non-null
object) is non-null (`SmtLowering#opaque`), and either is that identity wherever it is asked as a
reference. The objects a session placed unnamed of one class share one identity, an
over-approximation (two such objects may compare equal) CONFIRM filters. A view's positions are
stated linearly in its chain's puts: each position below the size names a present key held at that
position, and each put key present is held at a position below the size. A position is the run's
iteration count, so the chain's order is the positions' only where it is the order the map's class
iterates in (`ContainerSmtCodec#unordered`): the snapshot's members follow its base in that order
(`order`, `members`); an `INSERTION` map iterates in its chain's order after them (a `putAll` in
its source's); a `HASH` map keeps it through removals and updates of a key it holds, while a put of
another key may rebin or resize its table. Past such a put, or over a base stating no order (a
recording before it), the same facts are stated through `assoc_view_key` and
`assoc_view_position` (`ContainerSmtCodec.ViewOrder.FREE`): the positions are a bijection with the
keys in no order, so a view read as a set keeps every key and no position is tied to a key the run
may not have had there. A free order is a function of the state's TERM -- an Int of its text's digest
(`ContainerSmtCodec#tag`) and its size, which names the state for a flip query's cone -- never of the
state's value: a removal's renumbering is a lambda over arrays, and z3 builds no model of an
uninterpreted function applied to a value holding one (SOLR-18413's witness attempt: valuation 0's own
run over ZkStateReader's map of collections, iterated after puts and a removal, "incomplete (theory
array)" for 600 s; sat in 1 s by the term). Two terms of one state may take two orders, more freedom
than the run had, which CONFIRM filters. Each such map is named DIAGNOSTIC
`ASSOC_VIEW_UNORDERED:<why>:<map symbol (class), or the location its state was read from>@<session>`
(`SmtLowering#diagnostics`). A view walks the state each step of its chain stands for (`Host#chain`: a
read's joined version), so a map's `values()` a region iterates through a read of it is bounded by
that version's keys. A query reads a map's order only through `assoc_key_at` or `assoc_position_of`
(`ContainerStateModel.ORDER_READERS`; a free view reads none); one that reaches none gets maps whose puts and removals keep no order (`ContainerStateModel#unordered`, chosen by
`SmtNames#reachedPreamble`), the same question with no lambda: a removal's renumbering is a lambda
over arrays, and z3 answered such queries "incomplete (theory array)" or not at all (hdfs-11741 L1:
valuation 0 undecided on two fatal-observing paths, each sat in seconds without it). Every
array-valued choice of a put is a `store` of a chosen element, never an `ite` over arrays.

**A query's stated answer** (`ContainerSmtCodec#term`, `SmtLowering#answered`). A container query
the VM states the answer of (`concreteValue`, with its `answer` id: a member of an opaque root, the
test a muted body made, an element of an array whose elements are the heap's) is its chain's where
the chain stands on a stated base -- a `SNAPSHOT_BASE` or a `CLEAR` under every relation, each state
the one it stands for (`Host#chain`), remembered per conjunction (`Host#statedBase`). Over any other
base it is the PIN of the read rule, as a method return's: a name `answer__` for its session and id,
equal to the stated value by an assertion named `pinned_answer__...` for an unsat core (DIAGNOSTIC
`ContainerAnswerPinned:<shape>:<operation>@<session>`), only where nothing it rests on moves
(`#moves`: its keys, positions, owner and chain -- a read the stage may re-pair moves); else its
relation stands, free over the opaque
base, and a `READ` there is refused `CONTAINER_BASE_UNSTATED` as before. A pin is never stated where
a witness may move it -- `READ(s, k) == v` under a moving `k` would cut the witness -- and no model
choice is a hard constraint: it is the guard its node states. The answer is the run's object's
alone: a query asked of another object a family may re-point its owner to (`SmtLowering#asOf`)
states none.

**Stream results** (VM.md §4, `SymStream`). A collected list is an `INDEXED` chain from an exact empty
`SNAPSHOT_BASE`: `APPEND_IF [v]` with a `guard` is `indexed_append_if`, the guard inside the store
(with it false the state is the receiver's); a collected set's `PUT_IF [k, v]` is `assoc_put_if`. A
`PIN` (no arguments, a `guard`, either shape) is its receiver's state with the guard required
wherever it is lowered (`ContainerSmtCodec#pinned`): what the run decided that no relation states. A
count is the `SIZE` and a match the `IS_EMPTY` of such a chain on a base no object holds.
`CONTAINS [x]` on a list is a disjunction over the positions its chain can fill -- the appends and
insertions above an exact base within `VIEW_CHAIN_LIMIT` (`ContainerSmtCodec#indexedBound`), each
below the size -- and is refused by name otherwise (`ContainerRelation:INDEXED:CONTAINS:unbounded-chain`).

**Construction guards** (`RestsOn#constructionGuards`, R3-REFCONT §1.6, D5). A write that stored a
container states its `referentState`; its referent rests on every decision its occurrence took
before it at the guard sites of the mutations its method made on a container it then published
(`StaticScopeMap#constructionGuards`, the scope map's `publishedFrom` write sites, the carriers the
store's recorded type may be held by, `StaticScopeMap#carriersAt`), those that skipped a mutation included. `Independence` keeps them: a kept
read brings the guards of the write it observed, and an arm (`ComposedFamilies#producerBody`) seeds
the guards of the writes it delivers (`Arms.Arm#write`); the closure then conjoins them in the
polarity they took, and the reads they name are joined in turn. A decision whose condition guards a
conditional mutation of the referent's chain (`REMOVE_IF`, `PUT_IF`, `APPEND_IF`), or that guard's
complement, stays free. `ComposeMain`
reads the epoch's scope map (`--static-scope-map`, required; `run_engine.sh do_compose` passes it).

**An owner kept to the run's pairing** (`Composer#pinnedOwners`): a location a STATE family may
re-pair keeps the run's pairing (no family, no movable owner), named DIAGNOSTIC, only where a read the
family moves -- the anchor's up to its cutoff and the world's planted ones (`Composer#repairing`) --
would leave something
unnamed; a reached writer's own read of the location keeps the run's pairing, so what is asked
through it names the run's object and pins nothing (zk-bugs-election-offer: each create and delete
looks up its parent in the node map the anchor's getData re-pairs). So when a reached occurrence's
container version is a mutation naming as its `owner` a moved read
(`OWNER_PINNED_BY_MUTATION:<location>@<session>`, R3-REFCONT C-4: another pairing would mutate an
object no row records the mutation of), or when a store of it states or refuses a referent while
the object it stored has no container log of its own in the session, a `Collections` wrapper or a
view (`OWNER_PINNED_BY_WRAPPER:<location>@<session>`: a query through a wrapper reaches its map
through a field no row records and names no owner, so it would be the run's map's answer whichever
object the family delivered), or when the anchor or a reached occurrence asks a field or a query
through a moved container query read of it (`OWNER_PINNED_BY_CONTAINER_READ:<location>@<session>`,
the read names no object, `Composer#containerOwners`).

**Roots and clocks.** `domains`: a declared MARKER is free; a root the sessions recorded differently is
stated per path; a domain from `root-domains.jsonl` (absolute or `±k` from the recording) or the mint
is a window; otherwise the root is pinned. `placeClocks`, before any path composes, puts every
clock cell of the corpus on the recording's timeline -- the seed's reading, or, for a cell the seed
never read (a region woven after it, an occurrence a replay moved: hdfs-17897 NP3, dn0's `addKeys`
run under the command queue's anchor instead of the heartbeat's), the seed's reading of the nearest
cell (by seq) of the same JVM clock (`contract.Clock#same`) that a session reading it also read --
on the same node where that session read one, else on any of its nodes (`Composer#nearestAnchor`: a
session is one JVM, and a mint's host reading is that JVM's clock with the node's skew taken off, so
placing translates one timeline onto the other and moves nothing; HZ17-mat: master0's activation
cell, read only by re-runs whose other cells were master1's and client0's, was unplaced, so 112 of
114 paths were refused and the two left named it free through a message arm) -- plus the time that
session's host read between the two; every seed reading anchors, whatever the formula names. A
cell no session can place refuses each path whose own terms name it, by name (`DECLARATION_MISSING`,
DIAGNOSTIC, in `refusedPaths`: no claim could say whether a witness moved it), and each message arm
whose closure names it (`ComposedFamilies.ArmBody#end`: an arm delivering it would leave it free,
outside every domain and every claim's moved roots), beside
`unstatedRoots` at step (1b); every other path composes, and only when every path is refused does the
ADMISSION_GAP close the composition. `clocks`: every clock cell the formula names gets its reading
(one still in the formula with none is named, DIAGNOSTIC, and has no domain) and a domain, floor =
the reading, ceiling = reading +
30 days (in its ticks), unless the case declares bounds. On one node, each cell is no earlier than
the nearest earlier cell by seq (the recording's event, the order a replay runs a plant on in) of the
same clock (`contract.Clock#same`: the JVM clock its row states and the same tick; a cell stating
none is on no order, DIAGNOSTIC) (`clock_order__`); where the recording read the two the other way round, the link gives way by that
much (`(<= (- earlier later) d)`), so the recording always satisfies it. The cells are listed in seq
order (`Composition#clockCells`), each with its reading and the cell before it (`clockBefore`).
Every session's instants are on that one timeline too: a replay runs on its own host's clock, started
later (a plant is a skew off that host, `runtime.NodeClocks`), so an instant it computed outside every
clock root -- a key's expiry from a startup reading -- is a constant on its own clock. A session's
base at a cell is how far its host read the cell later than the recording (at the cell where the
recording read it, else at the nearest cell both read, chosen as a placement's anchor is;
`Composer#clockBases`),
and an integral constant compared with an instant of that cell (the cell, or the cell plus or minus a
constant span) in that session's terms is lowered that much earlier (`SmtLowering#clockBases`,
`#onTimeline`); the recording's own constants stay. hdfs-11741 L1: dn1's first expiry check compared
each replay's startup keys, 9 to 11 minutes late on the recording's timeline, with the one dn1 clock.

**Valuations** (`valuations`): ordinal 0 = every declared root at its recorded value; then the
worlds explored replays ran to the fatal (`Composer#exploredWorlds`: each fatal-observing path's
session but the seed's, in session-id order, its planted declared roots that differ from the
recording, each distinct world once, at most `EXPLORED_WORLDS` = 16, the rest named in
`compose.log`; an enumerated move equal to one is not asked again; ClaimPolicy ranks them as any
valuation, its own-run rule first: hbase-bugs-master-active-time NZ11-mat's path was satisfiable only
at the skew its own replay ran, -2001, which no anchor or nearby value names, so its claim was the
free model's FORMULA_SAT); then single
moves -- a marker's flip and an integral's domain-end anchors (`Composer#anchors`: each bound and its
two inward neighbours, where the domain's outermost comparisons flip, however far from the
recording) before its other values, each by distance, and at equal distance a configuration-only
move after any other (`Composer#configurationOnly`) --, then pairs of moves, cut at
`compose_max_valuations` (a MARKER's move is its other polarity; an INTEGRAL's values come from its
window, its end anchors nearest first, then outward from its recorded value, nearest first; clocks
are not enumerated).

ComposeMain writes three files. `candidate.smt2`: the body, then valuation 0 as named pins
`(assert (! (= <root symbol> <value>) :named valuation__<symbol>))` (so the file as published asks
about the recorded valuation; every other valuation differs only in these pins), then the pins
ClaimPolicy held outcome 0 under (clock pins `clock_pinned__*`, recorded pairings), `(assert false)`
with the blocker named when the claim is blocked or there is no path, and `(check-sat)`.
`candidate_composition_manifest.json`: the `CompositionManifest` fields plus `finalStatus`
(`FINAL_READY` | `FINAL_REFUSED`), `finalStatusRefusals`, `gaps` and `solver` (§9). `claim.json`:
`{kind CLAIM, anchor, claim, solverRuns, seedSessionId, valuations, gaps}`, what CONFIRM reads; each
selected arm states `texts`, consumer endpoint id -> the model's value of each leaf CONFIRM holds
(`ComposedFamilies.BoundLeaf#held`: a delivery into the anchor) as the text that
arrives (an integral's decimal, a boolean's `true`/`false`, a String's characters; none for a char
or a floating value), for every such leaf whose value rests on no clock through the valuation's
selected arms (`ComposedFamilies#texts`; a replay reads its clocks afresh). CONFIRM compares it with each
name a node had only in one run named by the node on both sides -- the arm's run's (`ConfirmMain#named`), the confirming
run's (`Confirmation#attached`, `RunNames#name`) -- and exactly after that: a node's address differs by its run's port
(NC3-reindex attempt 0000 was refuted on `127.0.0.1:41564_solr` against `127.0.0.1:33130_solr`, both `auto0/node1`).

**The same inputs, the same composition** (`compose.CompositionInputs`). Last, a composition states
the SHA-256 of everything it read, `compose_inputs.sha256`: its arguments (anchor, root domains,
static scope map, valuation bound, solver budget, z3 -- not the z3 room, a resource), the JVM's
`causynth.*` properties and the file one names, each session (id, its files' names and sizes, its
manifest), `recorded_schedule.jsonl`, `refuted_claims.jsonl`, the slot tables, and the result and
focus rows of each worker whose session is one of them; taken before the corpus is read and again once
the claim is written, it is stated only where the two agree. The final COMPOSE is handed the
exploration's accepted witness attempt (`campaign_compose`, `ComposeMain --reuse`): where that attempt
states the digest of what the final would read -- its corpus is the one EXPLORE ended on (§7.9) -- its
four files are copied byte for byte and nothing is composed or solved: the same composition but for
z3's free choices, and the claim the same model, whose confirmation CONFIRM takes (§10). Anything
else (a refuted claim recorded, a session landed) composes anew. SGF7 (2026-10-15): both final
COMPOSEs made the attempt's `.smt2` again byte for byte (57 and 14 min of stage time), and 18413's claim,
another model of it in one Long value and 7 message arms, was replayed again (CONFIRM 4.6 min).

**Cost.** COMPOSE reads the whole corpus -- every session (`SessionReader#readAll`) and every
obligation worker's answer with, once it published a session, its focus row (`ObligationDir#workersIn`),
8 directories at a time (`contract.Parallel#READS`: on NFS a read is its latency; each file's blocks of
whole lines parsed on every core, `RowCodec#readAll`) -- composes each
admitted path and decides (§9). Where each top-level command of the body ends, the path selector
guarding it and whether it asserts a refuted claim (its name closes it, so only its last 64
characters are read) are found once, as the composition is built (`Composition#commandEnds`,
`#commandGuards`, `#commandRefuted`); what every path's question shares and each path's own scope,
the self-check's without its fatal arm included (`#sharedQuery`, `#scopeQuery`,
`#scopeWithoutFatalArm`), are written from the one body by them, never by searching it again: a search per command and path to the end of the body kept hdfs-adhoc-07's
self-check (HR1: 556 sessions, 248 paths, a 26 MB body) past the 5400 s case limit; offline it now
takes 2-3 minutes: the corpus read 73-130 s (NFS), composing 27-45 s, deciding 13 s over 744 z3 runs
(`/bigtemp/vnr3ne/ab/hdfs-refactor-compose/c07`).
ComposeMain says how far it is on stderr (`final/compose.log`, a witness attempt's `compose.log`):
the corpus read, every 25 paths, the composition (paths, body size, valuations), each z3 run (its
command, its answer and its wall, the wait for room included) and the decision. Before a COMPOSE is
measured, the campaign's reserve stands the last planner round for it (§7.9).

## 9. SOLVE and DECIDE: `compose.ClaimPolicy.decide`

The shell stages only check and print what ComposeMain decided (`solver.state`, valuations, claim).
`ClaimPolicy`:

1. No disjunct: `NO_SUPPORTED_WITNESS`.
2. Each path is first asked alone with every root free (60 s, `Disjunction#selfCheck`): an unsat
   path is refuted for every question. Its verdict alone, no core, unless the body asserts a refuted
   claim: asked under no pin, its core can name only that (`#refutedBySelfCheck`), so it answers
   every later ask without one, those that want a core too (SGF6-bugs-snapshot-no-active 0001: 141
   paths' core runs, 26 of 48 at their cap, each then asked again alone, held the decide for hours).
   The self-check has a third of the decide budget (`ClaimPolicy#SELF_CHECK_SHARE`,
   `Z3Incremental#until`): past it no path is self-checked and the one running ends, each
   undecided -- left in the disjunction, never refuted on it -- and the cap is named (DIAGNOSTIC
   `self-check cap`), so the recorded valuation, which decides the polarity, and the other
   valuations are asked in the rest (snapshot 0001: about 28 of 141 paths satisfiable after 20-90 s
   each, a self-check of 21 of the 30 minutes). When the composed formula is unsat (4), every path is asked
   once more with its fatal arm left out (`ClaimPolicy#contradictions`, `Disjunction#withoutFatalArms`,
   `Composition#scopeWithoutFatalArm`: its `path_fatal__` implication without phi), what its own run
   satisfied: a path unsat there (or undecided), or one that observed the fatal arm, contradicts its
   run -- `PATH_SELF_CONTRADICTORY` DIAGNOSTIC, and BLOCKING for the composition, since the UNSAT rests
   on it; refuted by phi alone everywhere, no root of the corpus turns any path to the fatal arm,
   which is the claim's own answer (b20h BlockTokenSecretManager-511, a40s
   BackupCmd-343: the null-checked read is pinned to the object the run read). Then every valuation is asked (4 at
   once; each question is written to its z3s from the one body the composition holds, never copied
   per ask or per arithmetic engine, `Composition#query`/`#scopeQuery`, `Z3#ask`) for the path
   selectors, arm selectors, the nested state selectors a state arm's stores are chosen among (§8),
   clock cells and the held leaves the arms bind (`Composition#heldSymbols`); a selected state arm
   keeps the states whose selector the model set. An undecided valuation is named DIAGNOSTIC: it
   names no witness, and the verdict is the formula's own answer (4).
   Every such ask (and each re-ask below) is `compose.Disjunction#ask`: the disjunction whole, its
   verdict within 60 s (`WHOLE_BUDGET_MS`; its model and core runs keep the full budget), until a
   whole ask of the composition runs past that budget; from then on, every ask is path by path, the
   same disjunction under more pins (hdfs-11741 i1: 24 of its 31 whole asks ran their 60 s
   out). Whole, z3 decides in seconds where it decides at all, but can spend any budget searching
   every path's conjunction at once (hdfs-11741 r3: 47 paths undecided in 30 min whole, about a
   second each alone); one that stops at its memory cap goes path by path too, at the slot it was
   asked in -- never asked again alone first (`Z3#ask`): each path is a smaller question.
   Every path question -- the self-check, the one without its fatal arm, a path in its own run, free,
   under its own pins -- is one SCOPE of a long-lived z3 (`smt.Z3Incremental`): one z3 per arithmetic
   engine reads what every path shares once (`Composition#sharedQuery`: the commands no selector
   guards and no refuted claim) and asks each path as `(push 1) (set-option :timeout B)` its own
   commands (`#scopeQuery`: the refuted claims, its guarded commands, its selector, its pins)
   `(check-sat)`, its model or core read off that check, then `(pop 1)`, every answer read up to an
   `(echo ...)` mark; the pop takes back all the scope asserted, named or declared, so no question
   sees another's (SGF6-bugs-snapshot-no-active 0001: 65 of each path's 69 MB shared, read again by
   every path's own z3 before, about 4 of its 5.5-8 s). z3 answers a scope with its incremental
   core, far slower on some questions (that corpus: a sat path 73 s scoped, 8 s alone), so after 1 s
   it falls back to its tactic solver (`combined_solver.solver2_timeout`, `SOLVER2_TIMEOUT_MS`): that
   path 4 s, unsat ones 0.3-3 s. The engines race as a run's do, the preferred one's decided answer
   winning within its grace where a model or a core is asked -- a verdict alone is the first decided
   engine's at once, the same whichever gives it (`Z3#PREFERRED_GRACE_MILLIS`, one-shot runs alike:
   snapshot 0001, a path engine 6 satisfied in 22 s while engine 2 ran 120 s undecided, answered at
   44 s before); the other engine's check still running is cancelled by SIGINT, on which
   z3 ends a `check-sat` and reads on (anywhere else SIGINT ends it: started afresh). Undecided is
   never a verdict -- a timeout (z3's `:timeout`, or silent 10 s past it: that z3 ended), an
   `unknown`, a z3 at its cap -- and a z3 that ends mid-question answers it nothing: the questions
   after it go to a fresh one. A question is asked once more where its z3 ended before reaching it,
   ran out of memory after answering others, or had a SIGINT meant for an earlier check still to land
   (sent as that check ended, it cancels the next check -- "interrupted from keyboard", z3 4.14.1 --
   or, outside a check, ends z3); a cancelled check that shows no verdict within 10 s ends its z3,
   and a question's silence counts from its send, on a fresh z3 from the end of the shared part's
   read (which never counts: a large shared part is no timeout of every question).
   Two decided answers to one question that differ -- its engines' in one run or race, or its verdict's
   and its model's or core's -- are an error (`Z3#DISAGREE`, the claim refused by name) and the
   question undecided. A sat whose model its cap cut is undecided, an unsat whose core it cut stands
   with its core unknown. A question that wants a core is asked whole of a pair started tracking --
   its verdict, model and core of one check (`Z3#CORE_TRACKING` slows every question, so the rest go
   to pairs that track nothing); asked untracked and then again tracked, the recorded valuation's core
   questions moved a 2269 MB room between the two pairs 14 times on snapshot 0001, each move a fresh z3
   reading 65 MB. The paths' questions are put as many at a time as the rooms place plain pairs, at
   least 8 (`Disjunction#LEAST_PATH_ASKS`), each kind in its lane, and asked by as many plain pairs as
   the composer's z3 room holds beside the tracking one at 1024 MB a z3 (`Z3Incremental#PAIR_SLOT_MB`:
   snapshot 0001's held 420-560 MB, 843 MB at peak); a room that holds no two pairs runs one at a
   time, each holding the whole room, half each engine. The final COMPOSE has the pool to itself, so
   its plain pairs run on every other pool host too (`ComposeMain --z3-hosts`, `run_engine.sh`
   `campaign_z3_hosts_grant`: each host charged whole 2048 MB pairs of what its ledger admits, at most
   16 GB, while the composer runs): a remote z3 is started over ssh, prints its pid first, reads the
   shared part from one file written beside the query (the lifts' links are 1 Gb/s), and is signalled
   and ended over ssh; one that has not read the shared part within 120 s gives its questions back
   to the other pairs (SGF7-adhoc-10: one pair beside its 16 GB composer ran 315 z3 runs in the
   30 min decide budget and left questions undecided). Their ssh connections open IN WAVES: at most
   `Z3Incremental#SSH_STARTS_PER_HOST` (4) a host until each shell prints its pid (the slot given back
   by the z3's reader as that line comes or its output ends, never by its pair's driver), so sshd's
   MaxStartups refuses none (48 at once to one lift: 12 refused; 4 at a time: none); one refused
   before its shell ran is started again, at most `SSH_ATTEMPTS` (3) times, a second apart more each
   time, then its pair asks no more (SGF8-adhoc-39: 15 of 102 pairs lost to the burst).
   An engine starts at 1024 MB on another host and at its share of the room here; one that runs out
   of memory -- reading the shared part or on a question -- is no answer while a host holds twice its
   slot: every pair runs at twice that slot from then on (`Z3Incremental#outgrownMb`), stops its
   engines, gives back its slots, takes the larger ones and starts afresh, and the question is asked
   again (SGF9-adhoc-05: its shared part, 255 MB of text, needs 2662 MB a z3; at 1024 MB every remote
   pair was lost reading it within a minute and the one here answered 124 of 124 questions memout).
   A host's pairs never hold more than its room: a pair takes its slots before it starts its engines
   (`Z3.Room#tryTake`) and, where they do not fit beside the others, waits and asks nothing; only a
   pair whose lane has no other pair holding slots waits in the room's line (`Room#take`), so lanes and
   one-shot asks still take turns. A pair whose host's whole room is less than the slot asks no more
   while another pair of its lane could hold it; else it asks at its whole room, and an engine out of
   memory there answers memout. A pair holds its slots while it lives and gives them back to whoever
   waits in the room's line once it has no question, or between questions after 30 s of them
   (`YIELD_AFTER_MS`), so pairs and one-shot asks take turns where the room holds no more. The valuations, asked up
   to four at a time (`PARALLEL_ASKS`, at most as many as there are), ask their whole disjunctions in
   slots of the room shared that many ways (`Disjunction#asking`, `Z3#shared`), and a lone one-shot
   ask -- the formula's -- in half of it each engine; a model or core run at a shared slot's cap is
   that run once more alone, never the verdict again (`Z3#payload`): a core cut there too leaves the
   verdict unsat, its core unknown.
   A composer's room is what its host admits beside it when its step runs: it is placed with one
   pair's 2048 MB (`campaign_z3_room_mb`; less where its footprint and that would not fit under the
   host's ceiling, at least 256 MB, said when it is; charged with it, `campaign_jvm_charge_mb`; the
   head's held room counts it, `campaign_head_need_mb`), and on the host its step lands on it is given
   whatever that host's ledger admits beside it then, under the 70 % ceiling, up to 18432 MB, eight
   plain pairs and the tracking one (`campaign_z3_room_grant`, `campaign_head_charged --room`: charged
   with the step, released with it, told as `--z3-room-mb`; offline A/B alike, `tools/regress/
   offline-ab.sh`). A fixed 3072 MB held one pair on any host however much of a lift stood idle; a
   6144 MB room in every charge, 15.2 GB that every head held too, kept five bug checks of round SGF4
   waiting 30 min and more for a host, which a room taken only where the step lands never asks. The
   paths answer
   in their order: the first sat path's answer (the asks
   after it stopped, a check still running cancelled), else undecided if any path was, else unsat with the union of
   the paths' cores. A path is asked in its own run first (`Disjunction#pathAsk`,
   `Composition#ownRun`): its own session's arm of each message the path received and each state
   read's observed writer, selectors only (never the values its handoffs carried, which are on its
   own clock), within 10 minutes at most; a model there is a model of the question, and only where
   its own run is refuted or undecided is the path asked free (hdfs-11741 L1: two fatal-observing
   paths sat in about 100 s in their own runs, undecided after 30 minutes free). A path unsat under some assertions is unsat under every set containing them,
   so it is not asked again there: its refutation answers, core and all, one asked without a core
   only an ask that wants none, unless it was asked under no assertion at all where the body asserts
   no refuted claim (the self-check: its core can name no pin). hdfs-11741 i1: 155 of 157 paths
   refute themselves, so every pinned re-ask of its witness asks two paths. A valuation pins every
   declared root; a path's question names few of them (`Composition#rootsOf`: the roots its own
   commands name, closed over the commands every path shares that name one of them and another,
   read off the body once). Each path -- free and in its own run -- is asked first under the pins of
   those alone (`Disjunction#projected`), a subset of the valuation's assertions: unsat there, it is
   remembered so and refutes the path under every valuation agreeing on them, so a path is asked once
   per distinct projection, not once per valuation; sat or undecided there, the whole valuation
   decides, in its own run too, within the whole budget: the first try takes at most a quarter of it
   (`Disjunction#PROJECTED_SHARE`), since its roots follow only the shared commands naming two or more
   of them and it can leave out a pin the path needs. An unsat is only ever read
   off a subset of the assertions asked, and a memout or a timeout is never one. A path's question is
   the body without the commands another path's selector guards (`(assert (=> <selector> ...))`,
   vacuous once the partition forces that selector false), its own selector asserted: the shared
   part and its scope; 90-98% of a body is guarded (hdfs-17899-bug2 r4: 1.7 of 93 MB shared;
   hdfs-11741 i1: 4.1 of 124 MB). The self-contradiction check and `mechanism`'s pinned re-asks of
   the selected path read the same text. Selectors are never asserted together: two contradict the
   partition.
   A one-shot ask (`Z3#ask`, the whole disjunction) is a verdict run, then a model run (sat) or a
   core run (unsat, where a core is wanted), each its own z3 process; only the core run tracks the
   named assertions (`smt.Z3#CORE_TRACKING`), since tracked z3 simplifies nothing across them and
   still searches a disjunct whose selector the rest forces false.
   One composition's claim asks z3 within `DECIDE_BUDGET_MS` (30 min, `ClaimPolicy#decide`,
   `Z3#until`): past it no question starts and every one running ends, each undecided -- a named
   bound (DIAGNOSTIC `decide budget`), never a refutation, so no UNSAT stands on it.
3. *As it happened* = every clock cell pinned to its reading plus `recordedPairings` (each path held to
   its own observed reads and received arrivals; an arrival is held by its own run's arm,
   `Composition#ownRun`'s, so its value still follows the producer's roots and clocks, and by its
   received value only where no own arm states it). `recordingDecides`: ordinal 0 is sat free and
   unsat as it happened; the published row 0 is then that as-happened ask, whose core is not asked
   (hbase-bugs-master-active-time HZ10: "unsat, core []" read as the clocks-free ordinal 0, which was
   sat). `clockDriven`: ordinal 0 with every `recordedPairing` held and the clocks free is a witness
   (the clocks alone reach the fatal, every pairing as recorded; "unsat with the clocks alone pinned"
   missed it wherever a re-pairing reaches the fatal too: HZ10 re-paired the new master's read of its
   active time to the INITIAL 0, so the old master's clock carried by the report was never moved); then the witness keeps
   every clock running on wherever it can (`leastClocks`: a cell's skew off its reading equals that
   of the cell before it on its node's clock, `clock_runs_on__`; a first cell stays at its reading;
   pinned back one cell at a time in seq order, so a jump lands as late as the witness allows, on the
   cell the fatal reads rather than an earlier one that carries it along), so the cells left free are
   the clock's jumps. This refinement, and the margins after it, ask the witness's own path only
   (`Disjunction#askPath`): another path's answer is no answer about this witness. A cell the
   witness's model runs on already is pinned without an ask; of its jumps, those outside the path's
   causal cone (`Composition#cone`, what `cone.py` reads) are pinned first, in one ask, else one at a
   time, then those inside it one at a time; past the budget a jump inside the cone stands as a cause
   of the fatal; no ask tries "no jump at all" where the recording decided the clocks are needed. Each refinement has 5 minutes
   (`REFINE_BUDGET_MS`); past them the witness is published as far as it got, its untried cells named
   DIAGNOSTIC `SOLVER_TIMEOUT`. Every open path is asked in its own run before any is asked free
   (`Disjunction#ownRuns`). A sat ordinal 0 on a path that did not observe the fatal,
   when the recording does not decide, is named DIAGNOSTIC `FORMULA_SAT_AT_RECORDED_VALUATION`.
   `polarityDecides` = ordinal 0 unsat with a `valuation__` pin in its core.
4. The claim, first match. First of all an explored session's own run, at any count of moved
   fault markers, fewest first (`ClaimPolicy.Reading#ownWitness`: the selected session's own run
   as defined below, a replay that planted those roots, pairings and orders and observed the fatal
   at the anchor, which CONFIRM confirms as "itself the run"; if CONFIRM refutes it, the claim loop
   excludes its arms and the next composition takes the order below). Each fatal-observing disjunct
   is asked itself, at each valuation whose moved roots it ran (`Composition#ranRoots`): its path's
   scope of the formula, fatal arm included, with its selector and its own run pinned
   (`Composition#worldRun`, `#worldClocks`) -- not filtered out of the valuation's free model, whose
   arms are any the solver picked (zk-bugs-quota-init ZA5-quota: valuation 1's free model took the
   own path with two writer arms its session did not observe, so the own run went unclaimed behind 15
   pairing claims; asked itself, it is the first claim): a world a replay already ran
   to the fatal is ahead of every world only the model holds (hbase-bugs-ns-rsgroup-removal NC7:
   EXPLORE's replay of the namespace Mutate's fault observed the fatal, while every claim composed
   moved no fault -- STATE re-pairings holding the client's synchronous calls past their own
   thread's later events, each refused by a 300 s order timeout). Then fewest moved fault markers
   first (`RootCategory.FAULT` roots a witness's valuation moves, `Composition#faultsMoved`), then
   the order below within each count: a witness injecting no failure is the nearer world, and a
   refuted fault claim costs a CONFIRM loop (HZ10: 77 sat door-marker valuations ranked ahead of the
   clock world; the two claimed were refuted). First of all, a seed replay that observed the fatal at the declared
   occurrence leaves no claim (BLOCKING `SEED_OBSERVED_FATAL`): the run as recorded is no
   counterfactual (owner 2026-10-04: a claim moving no root is never a finding); beside PLAN's
   `TARGET_FATAL_IN_RECORDING` (the recording took the fatal arm there, `RuntimeSelectedRegionFinalizer`)
   it is a declaration defect, else the replay diverged. A guard of the declared target that
   reaches it on both arms states no fatal arm to judge the recording by: PLAN names it BLOCKING
   `AMBIGUOUS_FATAL_ARM` (`StaticScopeMap.AmbiguousFatalArm`, caught by the finalizer), a
   RUN_DEFECT at EMIT, never a stack trace. A witness moving configuration only (`Composition#configurationOnly`:
   every moved root `CONFIG`) ranks after every other, so the first rule takes the others, then the
   second, and only then the first rule takes a configuration-only one. A witness moving a
   configuration whose plant leaves reads of its key at the recording's value (the scope map's
   `CONFIG_KEY` row, SYMBOL-SCOPE §4.3) is not claimed: no cluster holds that world, so no replay can
   confirm it as one; `UNPRODUCIBLE_ANSWER` DIAGNOSTIC names the root and the reads, once.
   - a moved valuation that is a witness — under the as-happened pins when the recording decides —
     whose moved roots are in no unattested arm (else DIAGNOSTIC `UNATTESTED_ARM`): its `mechanism`.
     Its own-run part is asked in the first pass above, so within the rank only the rest is left
     (`ClaimPolicy.Reading#ownRun`, the test of the own run: the selected path observed the fatal, every arm the model takes on
     it is its own run's pairing, `Composition#repaired`, and the session ran the model's world --
     its moved roots at the model's values, its clocks the model's jumps, no planted pairing,
     `Composition#ranModel`, `explore.Moved#ranBy`, the very test CONFIRM's `realizedBy` confirms
     such a claim by), judged aside so that a corpus with none is decided as without it -- a
     candidate is first one whose moved roots its session ran (`Composition#ranRoots`), and each
     valuation is asked as happened or refined (`leastClocks`, margins) once for both passes; then the
     rest in the valuations' order, which says nothing of what a run already reached (hdfs-adhoc-10
     SL1: a fault first in the root order was claimed through a writer arm re-paired from another
     session, an order the program forbids, while the SYNC fault its own session had run waited
     thirteen valuations behind);
     without `recordingDecides` it also needs `polarityDecides`, checked before the witness is
     refined (`leastClocks`, margins, `mechanism`: rounds of path asks for a witness it would refuse)
     (else DIAGNOSTIC `FORMULA_SAT_AT_RECORDED_VALUATION`, saying whether ordinal 0 was sat or refuted
     by a core naming no valuation pin; an undecided ordinal 0 is BLOCKING already and raises no
     second gap);
   - a witness moving no root whose mechanism is `CLOCK_SKEW`, `STATE_PAIRING_FLIPPED` or
     `MESSAGE_PAIRING_FLIPPED`, with `recordingDecides` or `polarityDecides`;
   - ordinal 0 sat on another session's path that observed the fatal, all its families attested, and
     every disjunct of the seed's session unsat at the recorded roots: its mechanism, if any; else,
     where that session's world planted a pairing its read took (`Composition#takenPairings`: the
     read observed the planted writer's version and could have seen another writer),
     `STATE_PAIRING_FLIPPED` -- the world's pairing is what moved, though no term of the path names
     the read (a node's view at a version lacking an alias decides nothing the VM states) --, its
     witness that session's whole world, as CONFIRM re-runs it: the path's own run with the plants in
     place of the recording's pairing at each planted location (`Composition#worldRun`), the
     world's roots (`#worldValuation`) and clock skews (`#worldClocks`), so `movedRoots` names every
     fault and clock the world planted besides the pairing; it needs no attested arm (nothing moves in
     one: solr-bugs-tra-start-overwrite Z2K, whose request arms' producers ran concretely), and the
     pairing is named in `repairedArms`, by its arm, else `PAIRING:<reader>=<writer>` where no family
     states the read. It stands only where something holds the path (or no family offers the path an
     arm, `Composition#offersArms`: its own run is then the only one asked), each taken pairing lies on the
     fatal path (`Composition#onFatalPath`: the read's symbol in the path's cone, `CONE`, or -- a read
     no term names -- its occurrence is the anchor's, `ANCHOR`, or wrote a version a read in the cone,
     or a read the anchor's own occurrence made (the occurrence-level reading `ANCHOR` takes), observed,
     `WROTE`, a role read counting as the read of each occurrence it is the role prefix of
     (`Corpus#rolePrefix`: its node's work under its causal context before that occurrence's first row,
     the one rule `PairingFlip` offers it by; round SG3B tra: node1's `getAliases()` view read in the
     request's role work at VIEW@1, whose alias update wrote `/aliases.json` v3 from it, which the
     client's `.select` occurrence read while it waited for a collection v3 no longer routed to, until
     its retry timer -- the fatal term, which names no read -- fired). An occurrence-level clause is
     acceptable because CONFIRM stays the strict filter: it plants the pairing and must reach the
     fatal, and the recording, without the pairing, did not; the clause of each pairing is named in the claim's gaps, and an `ANCHOR` or
     `WROTE` pairing stands only in a world that moved no root or clock, since nothing else shows the
     pairing decides), the path's ask is decided (an undecided one is named so), and the session is
     that world's run (`Composition#ranWorld`, `Moved#ranWorldBy`: its roots and clocks the witness's,
     its pairings exactly those its replay realized, `Composition#realizedPairings`, inherited ones and
     ones no other writer could replace included); else a DIAGNOSTIC names why and the next path that
     observed the fatal and took a pairing is tried, the recorded valuation's first;
   - else THE FORMULA DECIDES (`ClaimPolicy#closed`): the composed formula is asked whole, every
     root free over its domain -- the very text exported as `final/candidate.smt2` -- and its answer
     is the verdict; the enumeration of single and pair moves above only picks a witness's
     valuation. Unsat: `NO_SUPPORTED_WITNESS` (UNSAT_CLOSED). Undecided within the budget: BLOCKING
     (a defect, never a refutation). Sat: `FORMULA_SAT` at the first enumerated witness a replay can
     plant, else at the formula's own model (`Composition#modelValuation`: each declared root at the
     model's value; a root outside the selected path's cone, `Composition#cone`, at its recorded
     value wherever the path, asked again so, still reaches the fatal, `ClaimPolicy#inCone`,
     `Composition#inCone`: hbase-bugs-master-active-time NZ10-mat's model moved a skew root and 30
     fault markers its path never names, and CONFIRM refused the skew root, minted nowhere it
     looked), refined as a named claim is (`leastClocks`, `withMargin`), composer
     imprecision until CONFIRM says otherwise, planted and judged like any claim, a refutation
     excluded before the claim is decided again; an enumerated witness that is
     the run as recorded (the seed's path, no root moved, no clock jumped, no arm re-paired) is
     skipped, and a corpus a BLOCKING gap already withholds a verdict from names no witness; a sat
     model selecting no path,
     or one only a configuration whose plant leaves reads at the recording's value satisfies
     (`UNPRODUCIBLE_ANSWER`), is BLOCKING.
5. `mechanism`, narrowest first: pinning the path's observed reads makes it unsat →
   `STATE_PAIRING_FLIPPED`; its observed anchor arrivals (held as in 3: by their own run's arm) →
   `MESSAGE_PAIRING_FLIPPED`; a moved root →
   `MARKER_FLIPPED` (any declared root kind); `clockDriven` → `CLOCK_SKEW`.
6. In the moved-root rule without `recordingDecides` and in the no-root-moved rule, the witness is
   re-asked with each clock jump a margin (one minute in its ticks) further the same way (`withMargin`:
   all at once, else each in seq order, kept where still sat), the margin on the JUMP against the cell
   its clock runs on from -- `(cell - reading) - (before - beforeReading) >= jump + margin`, `<=` and
   `- margin` for a jump back, `Composer#clockStep` with an offset -- never on the cell's instant: a later
   reading runs on from an earlier jump, so a minute added to the earlier instant moved the cell a later
   jump runs on from and used up that jump's own (PRE4-18406: the second delete() kept 1 ns over the
   reservation its clock ran on from, natively 0/10). `movedRoots` = the valuation's moved
   roots (by root id) plus every clock cell (by cell symbol) where the model's clock jumped (its skew
   differs from the cell's before it), at the model's instant. A jump back is a jump: a cell the
   witness needs short of where its clock ran on to must be planted, or a replay runs it on ahead; it
   is named at its model instant, which can be its own reading.
7. A z3 error on any ask adds a BLOCKING gap and turns the claim into `NO_SUPPORTED_WITNESS`
   (`smt.Z3` drops z3's `WARNING:` lines before reading an answer).

| `ClaimKind` | what the witness shows |
| --- | --- |
| `MARKER_FLIPPED` | a declared root (a fault marker, a configured source, a declared integral) moved inside its domain reaches the fatal arm; where the recording decides the arm, it does so with every clock and every path's own pairing held as recorded |
| `CLOCK_SKEW` | no declared root moved; the fatal arm is reached only with clock cells off their readings (the cells where a clock jumped are `movedRoots`) |
| `STATE_PAIRING_FLIPPED` | the roots stay; the path's anchor reads must take another writer than the run's |
| `MESSAGE_PAIRING_FLIPPED` | the roots stay; the anchor's attaches must receive another delivery than the run's |
| `FORMULA_SAT` | a valuation satisfies the formula and none of the above names why: the formula's own claim, which CONFIRM plants (its arms and valuation) and judges |
| `NO_SUPPORTED_WITNESS` | the composed formula, every root free, is unsat; an answer, not an error |

`ComposeMain.campaignClaim` maps it: the formula decides, SAT or UNSAT, and a blocking gap (a total
absence, §8; an undecided formula) leaves no verdict: any BLOCKING claim gap → `RUN_DEFECT`; else a
kind other than `NO_SUPPORTED_WITNESS` → `SAT_CANDIDATE`; else, the formula's own answer unsat →
`UNSAT_CLOSED`; else `RUN_DEFECT` (no claim and no unsat is never a refutation). `UNSAT_CLOSED` means
exactly: no world of the explored corpus reaches the fatal -- each admitted path under the marker
valuation its own run ran (`valuationOf`), every declared root free over its domain, every clock
over its window, and the values `concrete[]` holds (HELD, producer unstated) -- and nothing about a
path the exploration did not admit. A VERDICT IS JUDGED ON THE PATHS IT RESTS ON (owner 2026-10-06):
a SAT on the path it claims, an UNSAT on every path. Each value the fatal condition of such a path
names that no message family under its selector binds -- or that an arm the witness chose holds FREE
or HELD -- is an open link of the chain (`compose.Cone`, the set `experiments/accept/cone.py` reads
off the same formula; `Composition#openChain`, each with the producer occurrence its arrival names):
best effort, an open link is free in the formula and named (`openChain`), and the verdict stands:
`SAT_CANDIDATE` (CONFIRM decides) or `UNSAT_CLOSED`. A SAT's other paths' open links are stated, never gating
(`unboundOffWitness`, cone.json's too). EXPLORE closes a witness's chain before it ends (§7.9); an
UNSAT's paths are closed by the exploration's own growth, which plans each demanded producer an
admitted session exposes (§7.2, §7.8), so a link still open at the fixed point is one growing could
not close. EMIT publishes
`SAT_CANDIDATE` as CONFIRM left it (`SAT_UNCONFIRMED` when the confirmation does not confirm it,
refuted or decided by no replay -- the latter also a `CONFIRM_NO_VERDICT` defect), and an `UNSAT_CLOSED`
beside a BLOCKING gap of any stage as `RUN_DEFECT` (`formulaClaim` keeps the composition's own),
with every defect in `defects[]`, what the decision rested on concretely in `concrete[]`, and the
formula it decided on in `formula` (`final/candidate.smt2`'s path and sha256: the disjunction of the
admitted paths, the fatal arm asserted, every root free over its domain and no valuation pinned,
which a standalone z3 re-solves to the same verdict, SAT or UNSAT). The manifest's `solver` block carries `state` (sat/unsat/unknown),
`reachability`, `unsatClosureComplete`, `valuations` (status, assignment, moved, selected path and
session, `fatalObserved`, `selectedArms`, unsat core) and `campaignClaim` (`claim`, `claimReason`,
`findingKind`, `valuationOrdinal`, `polarityDecides`, `movedRoots`, `movedRootCategories` (each moved
root's category, `contract.RootCategory`), `configurationOnly` (the claim moves configuration only:
the one rule, read by triage and findings), `blockers`, `whyNotAccepted`, `witnessFindings`,
`openChain` and `unboundOffWitness` where they hold a link).

## 10. CONFIRM: `explore.ConfirmMain` and `runtime.Confirmation`

Only a `SAT_CANDIDATE` is confirmed. ConfirmMain reads `claim.json` and the manifest, takes the claim's
valuation, its selected path and session, and the selected arms of that path. The manifest states
where the path decided (`cutoff`): its target row, or, for a path that left the way to the throw at a
guard and never reached the anchor, that guard; the anchor's join closure runs to it. A witness that
turns a symbolic way guard is planted and judged as any other, by the fatal at the declared
occurrence: no target row of its own run is asked for. A manifest that states no selector, `restsOn`
or `cutoff` for the path, a schedule, pairing, arm or moved root the rows do not state is refused by
name (`CONFIRM refused:`, exit 1): a defect of the rows, `refutes` false, so a claim EMIT publishes
with it is a `RUN_DEFECT`.

- **The run as recorded**: a claim whose selected session is the seed's or a forced one (§7.10: the
  recording's world), that moves no root and no clock, re-pairs no arm (the valuation's `repairedArms`
  for its path is empty), every selected arm the seed's own delivery and every chosen write the one its
  read saw, is refuted by name (`CONFIRM refutes:`, `refutes` true): it is no counterfactual, whatever a
  run of it observes (owner 2026-10-04: a claim moving no root is never a finding), and the campaign
  excludes it. A re-pairing is a move: a read of the join closure takes the write the model chose for
  its version (`StateClosure#chosen`), named by the arm's STATE interaction with that read or with any
  read of the same location and version -- the composer's symbol is one per version, and its arm may
  name a later read of it, past the cutoff (hbase-adhoc-22: the arm named the quota total's read inside
  `addTable`, the anchor's own read in `getRegionCount` saw the same version) -- so a seed-path
  re-pairing goes to its replay.
- **Realized**: when the session's world planted no pairing (a pairing is a moved choice its own
  run took under the order its replay held, which CONFIRM makes again in its own replay, strict),
  a target row of it at the anchor reached it and observed the fatal, every selected arm is the session's own
  delivery, every write the model chose for a read of the join closure at a location the fatal
  rests on (`restsOn`, below) is the one that read saw (`StateClosure#ran`), the session minted
  every moved non-clock root at the model's value, its world planted no other root at a value other
  than the recording's (a world planting more than the model moved ran another model: a replay of
  the claim's decides), and its clocks are the model's (on every cell
  the composition anchors, the skews its world planted are exactly the claim's jumps; skews compare,
  each off its own run's host), the session is the confirmation (`realized.json`, no replay).
- **Otherwise one replay**: the world is the selected session's own focus row (empty for the seed)
  overlaid with the model (`ConfirmMain.Moved`): every moved root, by root id, at its mint
  occurrence -- the recording's; else, for a root whose occurrence only the grown plan runs, the
  selected session's mint row, else the mint row of the session of a selected arm whose body names
  it (the claim's arm row lists the root ids its delivered terms reach, `roots`;
  hbase-bugs-master-active-time's T0, master0's activation clock, reaches the seed path through
  such an arm) -- any other root as its value, a clock as its skew off the reading the
  composition anchored its cell to (the manifest's `roots`) -- and, on every clock cell the
  composition anchors, the model's jumps alone: the session's own skews there are dropped, since
  the model runs those cells on from the jump before them. Where each moved root's mint came from
  is `confirm.json`'s `mintFrom` (`recording`, `selected <session>`, `arm <session>`, written by the
  plan as the worker's `mint_from.json`). A moved root none of them mints, one those sessions mint
  at different occurrences, or a moved clock the composition anchors nowhere, refuses the
  confirmation by name; a mint the replay never reaches confirms nothing (the fatal must still be
  observed at the anchor). The
  world's pairings are held by the rows its replay was held to (`ConfirmMain#holding`, the reader's
  occurrence a block; a pairing the session states no read or write of refuses, `PAIRING_UNSTATED`).
  The focus row focuses the anchor
  with `flip: null`, the anchor as declared target, no inherited flips and no forcing (a forced path's
  world is the recording's, its claim confirmed by an unforced replay, §7.10). The schedule is written
  unheld (`SchedulePrefix.write(..., held=false)`: every event is suffix; only WAKEs wait for what
  they followed, and when the selected session was cut at its witness, a WAKE it never made waits
  for its whole order). `expected_edges.jsonl`: `WIRE` per consumer of each selected message arm (producer
  as that arm's session paired it, and `value`, the arm's `texts` entry for a delivery into the
  anchor whose delivered term names a root the claim's valuation moved, `ComposedFamilies#texts`:
  a recording's text or a clock's reading is no value the model states, so the run is not held to it
  -- hbase-bugs-master-active-time HZ13 refuted a fault claim on the old master's active time, a
  recorded text the report carried, against the replay's own clock), `STATE` per read of the anchor's join closure (each reached
  occurrence's reads before its cutoff, the anchor's before its target seq) at a location the
  selected path's fatal rests on (its manifest `restsOn`: `Composer`'s constraint independence of
  what the fatal rests on -- phi, or for a concrete fatal condition the path condition before the
  target, `Composer#fatalRests` -- and the roots alone, without the locations a family merely binds: a
  read elsewhere holds no
  value the witness needs, and under a moved root the run may make it at another endpoint or not at
  all; the write the model chose, else the observed one: a `writer_arm__`'s write for a read of its location (among its
  endpoint's writes, the one the read observed, else the last, as `Arms#stateArms` chose), and for a
  query through a re-pointable reference the write of the state its arm's `referentStates` name,
  §8; a recorded join to an INITIAL is no edge -- no occurrence wrote it, and which access first
  observes the location is the run's own history (`WriteRow#initial`) -- and an INITIAL the model
  chose names writer `INITIAL`, `Confirmation#INITIAL`, which every INITIAL a run logs is to it),
  for a node's VIEW one `VIEW_HOLD {view, above, readerContext, reader, until}` row instead of
  `ORDER` rows (§7.5: the node's later publications of the view are deferred until the reader's work
  is done, never the reader's own, at most VIEW_HOLD_MAX; a VIEW row's read is checked exactly, no
  `readerAnyTurn`; a view read the model did not pair is not held: held at its observed version, a
  hold that gave way at VIEW_HOLD_MAX refuted SGF7-18413's real witness, 2026-10-16), for a STORE
  read its world paired with a later tombstone one `STORE_HOLD` row (§7.6), else
  `ORDER` rows (the writer's activation exits before the reader's read: the order holds the last
  activation entry before the read on its thread, the last call the reader's activation made before
  it, else that activation's own (`ConfirmMain.StateClosure#holdBefore`); an event in its
  occurrence's outermost activation -- a loop body's, standing on the loop's method, which spans
  every turn -- is held at the occurrence's opening and waited for until its close
  (`StateClosure#exit`, `#outermost`), which the session ran at the occurrence's last recorded
  event, so a writer it ran before that is a reordered occurrence (`StateClosure#closing`); where
  that activation runs
  as a queued task, a queue item, a hand-off task that served a queue or claimed work of no stated
  kind (`ActivationRow#heldWhereItRuns` false: a server pipeline applying one request after
  another, the writer's among them, would deadlock held), the entry of the send that started it, its
  anchor's producer followed up the chain while that send is such work too
  (`Confirmation#submitter`); an order no hold realizes is **checked** instead: where no such
  send started the work (a continuation's claim names none: hbase-adhoc-04's DisableTable request
  is sent inside `FutureUtils#addListener`'s continuation, so the DisableTableProcedure step it
  started stood on no holdable send, `ORDER_UNHELD`, and REPRODUCE planted nothing), or where the
  order's earlier end stands under that send's anchor chain (`Confirmation#standsUnder`: the
  same procedure's DISABLING step before its DISABLED step, both under the request's anchor -- held
  at the send it would wait on its own effect until the timeout), the row carries `check: true`
  and sits at the later end's own activation (`StateClosure#held`, `#holdBefore`); every order a
  hold realizes is held as before; a task its executor handed to a worker of its own (`HANDOFF_TASK`, a `ThreadPoolExecutor`
  on a `SynchronousQueue`: Solr's Overseer command Runners) holds nothing of its executor's queue
  behind it and is held where it runs, unless the session's manifest names it in `servingTasks`
  (it took work another thread started on its thread, or work of an unknown or ended starter, any
  queue item no named start filed among it: a ConcurrentUpdate client's Runner polling
  its update queue; never for work it filed and claims itself, an inline continuation of its own:
  `Identity.State#openStart`, so an HBase procedure step is held on its worker, hbase-adhoc-22's
  deletion's release among them). Such a claimed hand-off is held at its claim's entry, not at
  the last activation before the event, unless the order's earlier end runs inside the held claim
  itself: its occurrence's `threadKey` is the claim's (another occurrence of the same step) or
  extends it (a claim nested in it on that thread: a continuation or a hand-off the step filed and
  ran inline), or names no activation row -- held at the entry it would wait on itself
  (`StateClosure#inside`; H3's review); then it is held before its event as any other activation is.
  Nor where the claim, in its program order, finishes the earlier end of another order before the
  event (an activation of the claim whose last event comes before it, `ConfirmMain#prefixed`,
  `StateClosure#untangle`): held at the entry, the claim would delay what another order waits on,
  and any chain of waits back to it -- through its own earlier end's claim or a third claim -- is
  a deadlock (NC9-22's final claim: the creation's step entry-held until the release exits while
  the deletion's step is entry-held until the creation's read exits); such an order returns to the
  hold before its event, the old hold point, so the demotion costs no soundness.
  The rule is structural, never the recording's order: a CONFIRM order is often the recording
  reversed (hbase-adhoc-22's release, recorded before the creation's read, held after it). Held at
  the entry, the ORDER row's `after` is the claim's name
  (`Confirmation#claim`: `CLAIM ` and the row's `threadKey` start key, its context named as
  activations are, a WAKE turn or a delivery's count left out), which `Identity#adopt` enters as it
  opens the claim, before the claimed work runs and before its `CLAIM` schedule event is observed,
  so no realized order runs other events ahead of the held work (an HBase step: `CausynthStep.run` in
  `ProcedureExecutor$WorkerThread#runProcedure`, before `executeProcedure` takes the procedure's
  scheduler locks, `acquireLock`, and before `beforeExec`, where a TransitRegionStateProcedure takes
  its RegionStateNode lock, which the admin move/unassign's `preTransitCheck` and every region
  state report also take: held at the last activation before its write, a TRSP step would sit on
  that lock while its earlier end waited for it, an order not held in time). The hold is stronger
  than the order asks -- everything the claimed work does waits, not only its event -- and still
  realizes it: the event cannot run before the claim's entry. It deadlocks only where the earlier
  end needs something the held work does before its event; what a step does before its event is
  its own: its scheduler locks (taken after the entry, so not held while held), its procedure's
  execution lock (`IdLock` by procedure id, taken in `runProcedure` before the step and never by
  another procedure's work), its own state reads and writes, and the RPCs and child procedures it
  starts, which run only once the step runs; another procedure's step or an RPC handler waits on
  none of these. Held at the last activation before its event instead, a step sits on whatever it
  holds there: NC9-22 held the deletion's release inside `synchronized
  NamespaceStateManager#removeTable`, the creation's `synchronized
  checkAndUpdateNamespaceTableCount` blocked on that monitor, and the order timed out (300 s). The case where one would: an earlier end that is the effect of this step's own
  prefix and that the step then waits for synchronously -- a step's hbase:meta write through the
  client, awaited with `FutureUtils#get`, whose region server handler's write were the earlier end;
  meta cells are no tracked location (TODO HBase 9), so no STATE pairing and no order names such a
  write today. Held in place, such a task holds what it holds at the hold: an Overseer
  command its `LockTree` lock (a command of an overlapping lock ordered before it stays parked by
  the processor) and its pool's room (an `AbortPolicy` pool past its maximum rejects the next
  submission); both end at the order's timeout, an order not held in time; every other
  writer of the location the held write is of before the writer or after the reader, held alike, and
  for an INITIAL the model chose every writer of the location after the reader. Only a write row of
  the selected session names such a writer. A store that ran outside every activation in that
  session (`UNATTRIBUTED_STORE`) has no row, so no order holds it, and the run's read of its version
  is the `CONFIRM_MISMATCH` "stored outside every activation, which no ORDER holds". A CONFIRM
  replay runs the iteration's seed plan as every replay does, so such a writer is one the plan
  names under another address, or none. hbase-adhoc-10's `TransitRegionStateProcedure#confirmOpened`
  steps were the first: their addresses carried their workers' frames until a hand-off claim stood
  apart (IDENTITY §3, TODO HBase 21)), `MARKER`
  per planted marker, `ANCHOR`. Endpoints and activations are named as every delivery of their
  stored message is (`Confirmation#id`, `OccurrenceAddress#anyDelivery`: a watcher's second
  delivery of one version, `KIND.n`, is the store's timing, so a run that took one delivery where
  the recording took two still takes the model's edges), and an activation as every turn of its
  timed-wait loop is (`Confirmation#activation`, `OccurrenceAddress#anyTurn`: `Root:WAKE/<wait>#k`
  counts the loop's wakes, the schedule's turn family). A `referentStates` row with no reader (a query asked outside every container
  read), at a read that is no read of the closure, or naming a write the session does not state
  refuses the confirmation by name; one at a read past its cutoff holds nothing the fatal rests on.
- The replay runs through `campaign_obligation_replay` into `final/confirm/`, the three halves of
  `campaign_confirm_claim` in a row: `campaign_confirm_plan` (ConfirmMain's task; a refusal or a
  realized session is the verdict at once), `campaign_confirm_replay` (charged as the seed replay is,
  wherever there is room) and `campaign_confirm_decide` (ConfirmMain `--sessions`), then
  `campaign_confirm_settle` (a refuting verdict refutes the claim). An exploration's attempt runs the
  same halves apart, its replay a job of the pool (§7.9). At runtime
  `Confirmation` compares WIRE at the attach (`Confirmation#attached`: the producer, and the text
  that arrived where the arm states one; a consumer of the
  anchor's, where the arm's session answered the anchor by its question (IDENTITY §9, its
  `ADDRESS_UNSTABLE` row), is also taken from a producer that answers the model's producer's question, `producerQuestion` on its row,
  `ConfirmMain#question`: the same site at the same site index and attempt of an occurrence of the
  same region and node under a chain of the same shape over this run's senders, since which turn
  or iteration carried the message to it is the run's timing -- hdfs-11741 V6's witness took the
  balancer's second move to dn1 from its next dispatcher iteration, its CONFIRM run from the
  first, as recorded; each such substitution is named, an `ADDRESS_UNSTABLE` DIAGNOSTIC row on the
  consumer, `RowRuntime#confirm`, and the value must still arrive), STATE at close (both by
  `Confirmation#id`; a STATE edge is taken when the model's reader observed the model's writer, or
  when a read at its site at another turn of the loops on its path did, `readerAnyTurn`,
  `Endpoint#anyTurn`: how many turns a loop that polls for a write takes is that write's timing --
  never for an INITIAL, which every read observes before the first write, so the exact reader must;
  a `mint` row, a placeholder's, which lands on whichever occurrence reads the cell first, when a
  placeholder of the run observed a version of its `location` its writer wrote, an INITIAL included,
  and it holds no order; a STATE row marked `afterAnchor` is not compared at all,
  `ConfirmMain#afterAnchor`: the plan's ORDER rows hold its reader behind an end inside the anchor's
  occurrence, directly or through further ORDER rows -- its activation key under a held activation,
  or its activation's claim (`Confirmation#claim`) the held claim -- and the reader is not in the
  anchor's occurrence itself; a reader merely recorded later is never marked. By the model's own
  order such a reader runs only after the anchor's occurrence made the read that decides its fatal,
  so what it reads cannot decide that fatal; whatever its activation writes that the anchor's
  occurrence reads later shows in those reads' own STATE rows, which stay required, and its ORDER
  row is held and checked as any other. A run that took the fatal often ends before such a reader
  runs: hbase-adhoc-22 NC11 claims 1-3 held DeleteTableProcedure's release step behind the
  creation's region-count read, observed the fatal at the anchor, and were refuted only because the
  release step's own read of the count never ran), and holds each `ORDER` activation's
  entry until the named activations exit (`causynth.confirm.order.timeout.ms`, 300 s; a stall is a
  mismatch); a checked `ORDER` (`check: true`) is never waited for: when its activation first
  enters, the named activations must already have exited (`Confirmation#checked`), each one that
  had is an `ORDER_OBSERVED` DIAGNOSTIC gap (the order observed, not held), and one that had not is
  a mismatch as an order not held in time; every difference is a `CONFIRM_MISMATCH` gap in the
  session. `MARKER` and `ANCHOR` rows
  are not read by the runtime. A CONFIRM run (`FocusedReplay.confirming`: its obligation flips
  nothing), or a replay whose world plants pairings (`FocusedReplay.pairs`), whose
  `expected_edges.jsonl` is missing or unreadable compares nothing and files one `EDGES:` mismatch
  at the close, so it confirms nothing and the obligation is `PAIRING_UNTAKEN`. One read is held to
  one writer: two STATE rows naming two are refused by `ConfirmMain` (`STATE_CONFLICT`) and, read at
  runtime, compare nothing.
- Decision (`ConfirmMain --claim --output <worker> --sessions <dir>`, `ConfirmMain#decide`, which
  prints `final/confirm.json`), conditions in order, the first that fails named as the reason: the
  replay's verdict is `ADMITTED`; its session directory exists and its `gaps.jsonl.gz` and
  `targets.jsonl.gz` are readable (a session that did not publish them answers nothing); no gap is a
  `CONFIRM_MISMATCH`; and a target row whose occurrence id is the claim's anchor's (the id only
  the Java address computes) has `reachedAnchor` and `observedFatal` — a fatal at another
  occurrence of the target site does not confirm. A replay that fails any of them -- not ADMITTED,
  no readable session, a `CONFIRM_MISMATCH` (an edge the model chose that it did not take, an ORDER
  it could not hold within `ORDER_TIMEOUT_MS`), a plant it did not make (`ConfirmMain#unplanted`),
  no fatal at the anchor -- and a replay that published no verdict (killed at its bound, stalled)
  did not reach the exception: it REFUTES the claim, a false positive (owner 2026-10-08: "如果replay跑不到exception。或者超时卡死，就直接定义为false positive。不用给这么多细分/迭代了"), its reason
  naming which. Only a decision that failed, or a claim stating no parseable anchor, decides
  nothing: a defect of the engine.

`final/confirm.json`: `{schemaVersion 1, kind: CONFIRMATION, confirmed, refutes, reason,
sessionId}`, the same shape for a refusal, `realized.json` and the decision; a decision whose
`expected_edges.jsonl` marks STATE rows `afterAnchor` names their readers (`afterAnchor`, the rows
the close did not require); a decision over
edges with checked orders also states `ordersChecked` (the `check` rows of its
`expected_edges.jsonl`) and `ordersObserved` (the run's `ORDER_OBSERVED` gaps: orders observed in
place, not held; one that was not is the `CONFIRM_MISMATCH` the reason names). `refutes` says a
replay or ConfirmMain refuted the claim: its replay did not reach the fatal at the anchor (above),
or ConfirmMain refuted it by name (`CONFIRM refutes:`, the run as recorded). A task ConfirmMain
refused by name (`CONFIRM refused:`, `PAIRING_UNHELD` or rows that state no runnable model) and a
decision that failed ran no replay of the model (`refutes` false): undecided. Either way a claim
CONFIRM did not confirm is a false positive (owner 2026-10-08, no refused split): its model is
excluded and the next claim composed, never RUN_DEFECT for it (an undecided one is also named, a
`CONFIRM_NO_VERDICT` defect). A final claim left unconfirmed with no next claim owed (below: the
bound, the budget) is `SAT_UNCONFIRMED`; every SAT excluded, the UNSAT the formula then decides is
the claim (`UNSAT_CLOSED` with its exclusions in `refutedClaims`: COMPOSE SAT -> CONFIRM
<outcome> -> excluded -> UNSAT_CLOSED).

**A claim CONFIRM did not confirm is followed by the next.** An excluded claim (`campaign_refute`,
its `outcome` refuted or undecided, logged "COMPOSE SAT -> CONFIRM <outcome>: <reason> -> excluded")
is one row of `<iteration>/refuted_claims.jsonl`: its `model` (`campaign_claim_model`, off `claim.json`: the
finding kind, the selected path, the arm selectors it chose there -- at the selected path's ordinal in
the claim's own manifest, as CONFIRM reads them: a model's `selectedArms` also name other paths' arms the
model set, which no exclusion of this path can compose (hbase-adhoc-22 HC10-22: a forced path's
moves-nothing claim, refuted twice, kept the seed path's arm `writer_arm__32__…`, so its exclusion was
never stated and the next composition repeated it) --, the valuation, and the claim's
moved roots, a clock by its cell's symbol at the model's instant), where it was `claimed`, and the
confirmation's `reason`. Every later composition of the iteration excludes each
(`Composer#refutations`, `compose.Refutations`): `refuted_claim__k` asserts that the path's
selector, those arms (an arm's selector is `<kind>__<path ordinal>__<digest>`, taken at the path's
ordinal in this query), the valuation's non-clock roots (named as the valuations name them,
`Corpus#anyRoot`) and the claim's clock region are not all true at once -- a region, not an
instant: each clock cell the claim moved jumped the way it did, by any amount, and every other
cell of the query runs on from the cell before it (`Composer#clockStep`, the spelling of a
witness's run-on pins too); an instant alone excluded one point, and the next model sat a tick
beside it --, a
DIAGNOSTIC `CLAIM_REFUTED` gap names it, and a model whose path or arm the query no
longer composes is not stated. An exclusion is a region, so an UNSAT may rest on one: whenever one is
asserted, the free-formula ask and the self-check ask for the unsat core (a path whose self-check
core names one does not contradict its run, `Disjunction#refutedBySelfCheck`); an `UNSAT_CLOSED`
whose core names a `refuted_claim__k` publishes each as `restsOnRefutations` (its path, moved
roots and reason; `Composition#restsOn`, `ComposeMain#campaignClaim`, EMIT, `report.py`, `triage.py`),
each a false positive read against the code before the UNSAT counts (CHECKING). A core is known only where its own run said unsat and printed its core (`Z3.Answer#coreKnown`; a core run that timed out,
found no room, answered unknown or stopped at its memory cap names none, which is not the empty core),
and an UNSAT that excludes refuted claims with its core unknown is `UNSAT_CLOSED` with
`restsOnRefutationsKnown` false (`ComposeMain#campaignClaim`): which of them it rests on is unknown, never
none. A disjunction's core is known only
where every path's is, and a path's refutation answers a core-wanting ask only with a known one.
During EXPLORE a witness attempt CONFIRM did not confirm lets the exploration go on (§7.9); after
it, the final stages go on to the next claim (`campaign_next_claim`): while the claim is a
`SAT_CANDIDATE` CONFIRM refuted whose model is recorded once in `refuted_claims.jsonl` (matched by `campaign_model_key`: an arm by its kind and digest, its path ordinal being one
composition's; not one the composition was told to exclude already), the campaign's budget has
room for its reserve (`campaign_claim_room`) and fewer than `campaign_max_claims` (8) claims were
decided again (past it the last claim is published, the bound named in the log), its artifacts
move to `final/refuted/NNNN/` and COMPOSE, SOLVE, DECIDE and CONFIRM run again. The
final CONFIRM of the model the exploration's witness attempt confirmed (the same model,
`campaign_claim_model`: kind, path, arms, valuation and moved roots; the attempt's own claim where
the final COMPOSE took its composition, §8) takes that attempt's `confirm.json` and runs no replay. EMIT publishes every refuted claim (`result.json`
`refutedClaims`; `tools/adhoc/triage.py` classes a case with any and no confirmed witness
REFUTED, `report.py` lists them, `tools/analysis/timeline.py` times every CONFIRM replay).

## 10b. REPRODUCE: the confirmed world, natively

After CONFIRM confirmed a `SAT_CANDIDATE`, before EMIT, it is run again on the stock JDK, in the
recording weave, with nothing of the concolic VM (`campaign_reproduce`). A confirmed claim that
reproduced in 0 of its native runs (`runs` > 0; a claim with no native run at all is not judged so)
is kept as the campaign's fallback verdict and excluded (`campaign_unreproduced`: its model joins
`refuted_claims.jsonl` with `outcome` `unreproduced`, its artifacts move to
`final/unreproduced/NNNN/`), and the claim loop composes the next claim, within the same budget room
and `campaign_max_claims` bound as a refuted claim (§10; both kinds count); the first confirmed claim
that reproduces in at least one run ends the loop and is the verdict. If none does, the first kept
claim stands (`campaign_fallback`: `final/unreproduced/0000/` is copied back into `final/`, what the
loop ended on moved to `final/superseded/`), and `final/fallback.json` `{fallback, stood, superseded,
reason}` names it either way; `report.py` names the fallback and the reproduction in its row
(hbase-adhoc-22 NC5: the first confirmed claim was an EXPLORE replay whose fault only shifted timing,
reproduced 0/10, while the bug's own STATE claim waited behind it). Every case gets the same rule:
a study check's reproduction only adds to its verdict. `ConfirmMain --iteration --claim --manifest --static-scope-map
--confirmed-session <dir> --plant <file>` writes the plant from a subset of what CONFIRM itself
plants and holds (`ConfirmMain.Witness`, the one reading of the claim both make: the selected
session's world under the model's moved roots, and the edges the model chose; of CONFIRM's holds,
those of what the model chose and of the world's pairings, below) and from the order the session
CONFIRM saw ran in, each row numbered (`row`); where a value is the return of a call it
names the call as the task plan does (`explore.PlantSites`: the input action's `siteId`,
`<method>#u<unit>`, and its `declaredCallee`, or an unwoven accessor's call):
- a `ROOT` per root the world assigns or skews (a fault marker at `false`, the run as recorded, is no row: a native
  run answers every marker `false` without a plant), naming the occurrence id it is minted at: a FAULT
  marker `{category FAULT, rootId, occurrence, siteId: <the call site its plan input action names>,
  value: true|false}`; a tree hook's root `{category HOOK, rootId, occurrence, value}`; a
  configuration `{category CONFIG, rootId, occurrence, sites: [{siteId, callee}], javaType, value}`
  (its getter calls: the plan's call-return input actions whose `configSource` is the root, as
  RootMint names it, beside those whose `portId` is, `PlantSites#action`; NZ11-mat's getter action
  had the region's port id, and REPRODUCE found no call for the root); an unwoven accessor's read `{category READ, rootId, occurrence, siteId,
  callee, javaType, value}`; a clock the world skews `{category CLOCK, rootId, occurrence, siteId,
  callee, javaType, clock: {nanos, source}, skew}` (the model's jumps and the selected session's
  skews on cells the composition does not anchor, as CONFIRM plants them);
- when the world skews a clock, a `CLOCK_SITE {siteId, callee, javaType, clock, regions}` per
  declared clock reading of the plan (an observed one, as a replay mints it): context, applied by
  nobody;
- an `ANSWER {endpoint, port, siteId, callee, regions, value}` per attach the world answers, at its
  port's call-return capture and the regions declaring it IN; an answer equal to the arrival the
  confirmed session's attach recorded (what its producer sent anyway) is no row
  (`ConfirmMain#answers`: hbase-bugs-master-active-time NZ12-mat's flip obligation answered master1's
  RegionStateTransition attach with T0 as sent, a message field no native run answers);
- CONFIRM's own `ORDER` rows (`{before, after}` of activations, no `scope`, `check: true` where no
  hold realizes the order, §10) of what the model
  chose -- a read it chose a writer for, at the locations the fatal rests on, with every other
  writer of the location around it -- and those holding the pairings the world plants (an INITIAL
  pairing holds every other writer of the location after the read), each pair once; not a row only
  a read's own join needs (`ConfirmMain.Witness#history`): that is the confirmed session's history,
  which a native run makes on its own timing and by its own paths (HV1
  solr-bugs-snapshot-no-active: 178 of its 179 rows were joins, most ordering
  `ZkStateReader.collectionWatches`' writers and readers; natively a `waitForState` took its fast path and registered no watcher, or
  another watch notification decoded the state, and the first row waiting for an activation that
  never came released every hold, 0/10); CONFIRM still holds and compares them. Nor is a row
  either of whose ends stands in a turn-counted root (`RealizedOrder#turnCounted`: a `Root:` of any
  role but CLIENT, as for the realized order below) other than the anchor's context or one a ROOT
  row is minted in: that context is the confirmed run's timing, which a native run numbers on its
  own (hbase-adhoc-04 repro-NR2-04: the VM's slow meta update suspended a CreateTableProcedure step,
  which resumed under `Root:WAKE/AbstractProcedureScheduler.poll#5` and wrote the shared table-state
  map; no native run ever ran a step under a poll WAKE, so that write's exit never came and 10 of 10
  runs that took the fatal at the anchor with the root planted reproduced nothing); `plant.log` names
  each such row and its context ("REPRODUCE leaves out ORDER"), the summary and `reproduce.json`
  count them (`turnOrders`): a native reproduction did not enforce them, CONFIRM did. Nor is a row
  whose order causality implies in every run (`ConfirmMain#implied`, over
  `contract.ClientProgramOrder`, the one reading of a client thread's happens-before COMPOSE is to
  share): its earlier end stands directly under a request R1 and ran in the turn that took R1 in (its
  activation in the confirmed session claims no work, so it ended before that turn's reply), its
  later end stands under a request R2, one client stance sent both, and the confirmed session's
  schedule has that stance's node receiving a reply of R1 before the stance sent R2 (a RECV of a
  `<transport>#RESPONSE` sent under R1's anchor, earlier than R2's SEND; a chain R1 -> R2 -> R3 is
  the same comparison); an asynchronous call whose reply comes later, claimed work (a procedure step
  under R1, which can run after R1's reply), another client stance, or an end under no client request
  keeps its row. The rule rests on the RPC being synchronous at the wire -- an `*Async` admin call
  still waits for its reply, the procedure id -- and on the earlier end being the handler's own turn
  before that reply, so it holds in every run, not only as recorded (hbase-bugs-ns-rsgroup-removal
  NC12: the witness replay's AddRSGroup was sent three
  times, its last attempt's anchor never came natively, and its row to the later MoveServers gave
  way in 10 of 10 runs that took the fatal at the anchor with the fault planted); `plant.log` names
  each ("REPRODUCE leaves out implied ORDER", with the two schedule rows that imply it), and
  `reproduce.json` counts them (`impliedOrders`). A checked row
  (`check: true`, §10) is tested at its later end's activation entry, the frame a hold would use,
  which comes no later than the event it orders, so a check can only under-count reproductions. A read the model
  chose at is one whose writer it chose, or one at a location it chose at
  (`ConfirmMain.Witness#chosenAt`): a writer arm binds every read of its location though its
  interactions name the first, and a selected observed arm (`observed_arm__`, group
  `observed:<key>`) chooses the run as it happened there over the location's concurrent writers.
  And its `VIEW_HOLD` rows, a join's too (a hold only defers a node's publications of the view
  until its reader's work ends, at most VIEW_HOLD_MAX, and names no activation the run must make),
  each once, which the native run holds as CONFIRM does, deferring the node's
  publication (`Confirmation#publishing`, each stated held, applied or unheld, at most VIEW_HOLD_MAX); a pairing at a placeholder (a mint
  read) holds no order in CONFIRM either, and natively nothing checks the version it read: the
  plant's summary counts them (`placeholderPairings`);
- the **realized order** (`explore.RealizedOrder`): `ORDER {scope EVENT, before: <event>, after:
  <event>}` rows, an event named by the one identity both passes compute (`{kind, context, site,
  k}`, IDENTITY), so the run is the world CONFIRM saw and not merely its roots. The session CONFIRM
  saw is `final/confirm.json`'s `sessionId` (`campaign_confirmed_session`): the selected session
  itself when it realized the claim, else CONFIRM's replay, in `final/confirm/sessions/` or an
  exploration attempt's `witness-confirm/NNNN/sessions/`; a session not there refuses the plant.
  Its schedule is read from where a ROOT row's mint occurrence opened on (the occurrence's schedule
  mark, or its first event: a clock read's occurrence makes no event of its own, solr-18406); a
  step is an event but a WAKE or an END, which are the clock. Each WAKE is held after the step just
  before it, once per step and context, where the WAKE is in a context running before the start,
  and the step is in another context and the first of its kind and site there (`k` 0):
  - the roots' effect races the contexts it found running, and the trace states no edge of how it
    reaches them; a context begun later is that effect or the workload's next step and runs as the
    run makes it, its turns deciding on reads no event names;
  - a running context goes on by itself only where a wait ends, on the wall clock or a signal, and
    natively a wait ends before the world it waited on has got where the confirmed one had;
  - a later count is a loop's (a poll's, a retry's, one send per item), which natively runs
    another number of times.

  Only on the claim's cone: the WAKE's context and the step's (node and causal context, the
  handoffs left out) are each the context of an occurrence a ROOT row is minted at, of the anchor,
  or of one CONFIRM's WIRE, STATE or ORDER rows name, a VIEW_HOLD's later decodes included
  (`ConfirmMain.Witness#cone`), or, one hop,
  the context of a SEND one of these received (paired by endpoint: `RealizedOrder#withProducers`;
  restore's first RESTORE task, whose state-update message the mint's turn applied and whose wait
  the order holds -- 0/10 without the hop), and the step is
  in no turn-counted root (a `Root:` of any role but CLIENT: a daemon tick, a timed wait's turn)
  unless a ROOT row is minted there; a WAKE elsewhere is timing the claim rests on nowhere, and a
  tick's k counts turns a native run numbers on its own timing (solr-18413 Y8: 56 rows -- the
  client's REQUESTSTATUS polls, other Overseer task and state-updater turns -- and every native run
  waited at a queue write of `Root:OVERSEER_STATE_UPDATE#15` it never made at that tick, 0/10; on
  the cone none is held and Y8 reproduces 10/10, IB1 10/10).

  Both events are named by their stable contexts (`contract.StableEventNames`, computed alike by
  the plant's ScheduleLog): a context drops its frames' invocation counts (`@n`) and a timed-wait
  turn's number (`StableEventNames#turnFamily`, the schedule's rule), and each message
  hop is named by its sender's stable context and the send's site when that send was the sender's
  first of its site; a hop of a later send (a loop's) has no stable name and an edge naming one is
  not held. A producer endpoint id hashes the sender's counts, so a poll before a send renames all
  the work it starts (solr-18413 IB1: the MIGRATE task polled REQUESTSTATUS three times in the
  confirmed session and twice natively, its SPLIT request's work had another endpoint id, and a
  client WAKE held behind that work waited for an event no native run made: 0/10 while every run
  threw at the anchor).

  solr-bugs-restore-construction: a ZooKeeper session fault ends the Overseer, a new one runs the
  second RESTORE, and the client's next update routes on the restored collection while the old
  Overseer's first RESTORE task still waits for its replicas -- in the confirmed session that wait
  woke only after the second RESTORE had answered the client; natively the task finished first and
  the update found the collection active (0/10 with every root planted). Its plant holds that wake
  after the client's receipt of the answer. The whole order, one edge per context switch (restore
  42 rows, solr-18406 366, solr-18413 497), reproduced 0/10 on each: every run's first unheld row
  waited for an event the run never made (a new Overseer's state-updater turn that found its queue
  empty natively, a request handler's sixth SEND, a select whose poll count differed). The plant's
  summary counts the rows (`realizedOrders`);
- one `TARGET` per guard of the scope map's TARGET_SITE rows, `{occurrence: <the claim's anchor
  id>, siteId: <guard>, value: <its fatal arm>}`.

Refused, with no native run (`reproduce.json` `runs` 0 and the refusal as `reason`):
- by CONFIRM's own reading of the claim (`CONFIRM refused:`, §10): a valuation that selects no
  path, an unparseable anchor, a manifest stating no selector, `restsOn` or `cutoff` for the path,
  a moved root no source mints (the recording, the selected session, an arm naming it) or mints at
  two occurrences, a moved clock no reading anchors, and the edges'
  refusals (`STATE_CONFLICT`, `PAIRING_UNSTATED`, a selected arm whose consumer its session states
  no attach for);
- `NATIVE_PLANT_UNSUPPORTED`: a root minted other than at a call's return (an argument, a field or
  static read: the recording weave states no read there for a plant to take), a FAULT root its plan
  input calls at no site or at several or assigns other than true or false, a READ root at several
  calls, a clock read at other than one declared clock call or skewed by no integer, a root with no
  mint occurrence; an answer whose capture is a method parameter, a call argument or a method's
  return, or whose value a message getter's element carries (a codec port: which getter call
  attaches is the decode's binding, `MessageCodec`, which a native run does not keep -- keeping it
  would export on every send, which needs the VM); a world that plants no root and holds no order
  the model chose (it would repeat the recording); a scope map that states no fatal arm;
- a recording that measured no peak resident memory to charge a run with.

`reproduce_runs` (10) runs go out at once, then as many control runs queued behind them (a plant
run never waits for a control), each a head step (§7.7, `campaign_reproduce_one`)
charged `reproduce_charge_pct` (130) percent of the recording's peak resident memory (`execute.sh`
states it as `workload_rss_mb` in the trace directory, and holds each run to that charge as to any:
a native run's own peak scatters around the recording's, at most 1.27x it over 110 runs, and ten
charged at 100 % outgrew their host's ceiling together, so its next growth was refused and the run
ended -- LL5-lock-leak, 4 of 10) wherever there is room until it
returns, naming the host it ran on (`<run>/host.txt`), and bounded by `reproduce_time_factor` (3)
times the recording's own workload, at least `reproduce_min_s` (300: a short recording says
little of how long ten runs at once on a busy cluster take -- hdfs-17960's 8 s recording gave 24 s,
and all ten runs of round NP1 were cut before their window opened; hdfs-17897's 9 s recording, ten
runs of 119-187 s in NP7, each at the anchor; `campaign_reproduce_bound`). A
run (`campaign_reproduce_run`) runs the recording command with `-Dcausynth.plant` and the plant-run
agent, `-javaagent` of the engine's jar (`execute.sh`, `CAUSYNTH_PLANT`; `runtime.PlantAgent`, the
jar's `Premain-Class`; a JVM with no plant loads none). The agent rewrites, as they load, the caller
classes the plant's call rows name: after every invoke of a callee named there, one call
`RecordingPlant.returned(T)T` for the invoke's JVM return type (a reference through `Object` and a
cast back), in ASM API 5 with the operand stack's types kept, so no frame is recomputed and no class
loaded; the woven classes on disk, SEED's artifacts and the recording are untouched. Which call it
is, the recording weave's own call-site context states at run time (`CausynthTraceRecorder
#currentCallSiteContext`, pushed with that `siteId` and callee before the invoke), so no unit index is
mapped to a bytecode offset; an invoke no context wraps matches no row. Inside the window:
- `Debug.makeSymbolicBoolean` at a FAULT row's call site answers its value when an enclosing region
  occurrence (`CausynthTraceRecorder#enclosingOccurrences`: the thread's regions' current
  occurrences, `Identity#standingOccurrences`, innermost first -- a region a hop opened inside it
  names, as ZooKeeper's `PrepRequestProcessor.run()` is named by `CausynthZk.serve` per request,
  stands under that name while the hop stands; read off the entry instead, ZA9-rseq's fatal in Prep
  stood in no occurrence and 10 of 10 native runs missed the anchor) has the row's own id
  (`RecordingPlant#marker`);
- the tree's `CausynthSymbolicSource.symbolize` of a HOOK row's root writes its value into the field
  the hook names (`RootMint#configuredSource` -> `RecordingPlant#hook`, the replay's own
  `RootMint#writeModeledField`) under any enclosing occurrence the confirmation focuses -- the
  anchor or the mint occurrence of any root of the plant -- as a replay's mint plants under a focused
  occurrence (`RootMint#focusedRootValue`); a write that fails is a `PLANT_UNWRITTEN` row;
- at a call the plant reads (`RecordingPlant#returnedAt`): a CONFIG row's getter calls return its
  value whatever occurrence reads them (a configuration is the world's, as in a replay); a READ row's
  accessor call its value under its occurrence; a CLOCK row's first return under its occurrence is
  the host's reading plus the skew and a jump of that occurrence's node's clock (`NodeClocks`), and
  every declared clock reading (a CLOCK_SITE row) reads the host plus the skew of the latest jump at
  or before it on its node's clock, its node the one of its innermost enclosing occurrence of a
  declaring region (none: the host) -- "before" is this run's real order, a counter of declared
  readings (`RecordingPlant#PLACES`), since a native run has no recorded place; an ANSWER row's
  capture carries the call's value as the replay's weave carries it and names each leaf by the
  endpoint a replay's attach names it by in its innermost enclosing occurrence of a declaring region
  (`HandoffMint#answerNatively`: `Identity#endpointAt`, one per leaf, so the k-th attach is the
  replay's k-th where the run attaches as the replay did), writing the answer at the endpoint the row
  names; a value the call's type cannot hold is a `PLANT_UNWRITTEN` row;
- `runtime.Confirmation` holds CONFIRM's own ORDER rows at `Identity`'s frame hooks as in a CONFIRM
  run (it reads the plant in a planted run), and `runtime.ScheduleLog` the realized order at an
  event's admission, before its k is taken: the event waits until every event its rows order before
  it was made (a timed wait's WAKE asks without blocking, `ScheduleLog#timedOut`, so what the wait
  released stays released; an interrupt meanwhile is kept pending, the event still after what the
  confirmed world made before it). Each row is held at most half the run's bound
  (`causynth.confirm.order.timeout.ms`, `CAUSYNTH_ORDER_TIMEOUT_MS`) and states what it came to:
  held (`PLANT_APPLIED`), waited for (`PLANT_HOLDING`), or not held in time (`PLANT_UNHELD`); a
  checked ORDER row (`check: true`, §10) is never waited for and states `PLANT_OBSERVED` when what it
  orders before its activation had exited as it first entered, else `PLANT_UNHELD` at once. The
  first row not held releases every hold of both scopes (`RecordingPlant#gaveWay`): the run no
  longer runs the confirmed world, so it reproduces nothing whatever it reaches, and holding the
  rest would only stall it. What an UNHELD row waited for that comes after all is a `PLANT_LATE`
  row; one that never comes was not this run's (its identity missing natively: a context, site or
  count the run did not make) -- what the run states, never a refutation;
- every row applied is a `PLANT_APPLIED` trace row naming its number; a recorded branch at a TARGET
  row's guard that takes its fatal arm is a `PLANT_FATAL` row stating whether an enclosing
  occurrence is the anchor's -- at the anchor the run ends (`JUnitMethodRunner.exit`, as a focused
  replay ends at its witness), its one question answered (`runtime.RecordingPlant`).

A planted run is not the recording's world, so the workload's checks of that world are off in it
as in a replay (`CausynthTraceRecorder.replaying()` is true under `causynth.plant`). Each run states
its answer, whatever the workload's exit, as `run-<n>/answer.json` `{exit, rows, applied, unapplied,
planted, rootsPlanted, ordersHeld, ordersChecked, ordersObserved, fatal, atAnchor, control, reproduced}` (a control run never reproduced; `ordersChecked` the plant's checked ORDER rows, `ordersObserved` those the run observed in order, each unapplied row stating whether it was `checked`), read off its trace's plant rows
(each flushed as it is written, `CausynthTraceRecorder#writePlantRow`, so a run its bound kills keeps
them; the trace is closed only by the run's end, §5) against the plant: the rows to apply (ROOT, ANSWER and ORDER of either scope; CLOCK_SITE and TARGET
rows are context), how many it applied, each it did not with why (an ORDER not held in time: `LATE`
when what it waited for came after all, `MISSING` when it never came; `UNWRITTEN`, `HOLDING` at the
run's end, `NOT_REACHED`), whether it applied every row, every ROOT and ANSWER row and held every
ORDER, whether it took the fatal arm and at the anchor, and whether it **reproduced**: the fatal
arm at the claim's anchor with every ROOT and ANSWER row applied (clock jumps, configurations and
answers included) and no ORDER timed out. A run that did not plant the model's roots, or ran
another order than the world CONFIRM saw, and reaches the fatal all the same is the program's own
race, never a reproduction. **The control**: behind them go as many runs of a plant of the TARGET
rows alone (`reproduce/control.jsonl`, `reproduce/control/run-<n>`: nothing the model chose -- no
root, answer or clock, no order, no view hold), placed, charged and bounded alike, each answer
marked `control` and never `reproduced`; how many of them
take the fatal arm, and at the anchor, is the program's own rate of the fatal on the recording's
timing, the evidence a reproduction's rate is read against (a plant whose rows hold little of the
chain, a CLOCK root alone or a VIEW_HOLD alone, reproduces as often as the workload throws by
itself), and never a gate. `final/reproduce.json`: `{schemaVersion 1, kind: REPRODUCTION, runs,
planted, fatal, atAnchor, reproduced, unheld, unheldLate, unheldMissing, holding, checked,
checkedObserved, turnOrders, impliedOrders, reason, control: {runs, fatal, atAnchor, reason}}` -- runs that applied the whole plant, took the fatal arm, took it at the
anchor (planted or not), reproduced, could not hold an ORDER in time (of them, one whose
before-event came late, one whose before-event never came; a checked ORDER not observed in order
counts here), still held one when they ended, the plant's checked ORDER rows and the runs that
observed every one in order, the plant's rows left out as turn-counted (`turnOrders`) and as implied by a client thread's replies (`impliedOrders`), the runs that stated no answer as `reason`, and the control's runs, fatal, at the anchor and its runs
that stated no answer; the log
states "reproduced in k of N ...; control k' of N". REPRODUCE never touches CONFIRM: a CONFIRM that fails is a false positive as ever (§10),
and the realized order only makes a native run faithful to the world CONFIRM saw. The share of runs
that reproduced ranks a finding (`tools/adhoc/findings.py`, which reads `reproduce.json` beside
`result.json`) and never refutes it. Then the campaign exits by its verdict
(`campaign_exit_verdict`). The stage also runs alone, again, over a finished campaign
(`run_engine.sh ... reproduce`, `do_reproduce`; `tools/rounds/reproduce-again.sh <run> <case> <copy>`
copies the case's output directory -- linking what REPRODUCE reads, the replays CONFIRM ran
included, writing `final/` afresh -- so
the finished run is never written): its bound is a factor of SEED's whole time there, since the
recording's own is not kept apart.

## 11. EMIT

1. `campaign_verify_frozen_inputs` (§1).
2. `final/gaps.json` (`campaign_write_gaps`: `contract.GapLedgerMain`), one row per distinct
   (stage, source, code, subject, detail), the first raised kept, class as the row states it (none
   stated = BLOCKING): static communication gaps and the runtime plan's `gaps` as PLAN; every
   `gaps.jsonl.gz` (a session's, a round's, a worker's) under the iteration
   directory, in their paths' byte order, read once each through `smt.ArtifactIO#input`, side by
   side on the host's cores — a path matching
   `*/sessions/*/gaps.jsonl.gz` as REPLAY (a withdrawn exposing session under `before-*/sessions/`
   included), any other under `obligations-*/` as EXPLORE (a session withdrawn to
   `timed-out-sessions/` or `refused-sessions/` included), anywhere else fails EMIT. A generation's own closure file
   (`obligations-NNNN/gaps.jsonl.gz`, ExploreMain's) stands only for the newest generation that wrote one: each
   generation re-derives its closure over the whole corpus, so an earlier generation's BLOCKING row is DIAGNOSTIC,
   `superseded by obligations-NNNN`, and the newest closure file is read first, so its class wins for a row both raise
   (hbase-adhoc-31 F1H: three occurrences no session had run in generations 3-10 ran from 11 on, yet held the run at
   RUN_DEFECT); a session's or worker's file under `obligations-NNNN/<id>/` counts whatever its generation. `campaign_gaps.jsonl` rows at their
   stated stage, else IMPORT; the composer's refusals (BLOCKING), `gaps` and claim gaps as COMPOSE. Published as
   `gaps` (BLOCKING), `telemetryGaps` (DIAGNOSTIC), `gapCount`, `telemetryCount`, `byStage`, `byCode`,
   one row per distinct (stage, source, code, subject, detail), texts in their UTF-8 byte order (Gson's
   writer, two-space indent). Beside it, `iteration-*/emit_gaps.json`, what EMIT itself reads of it (`campaign_bounds`,
   the result, the counts): every BLOCKING row and the counts, of the DIAGNOSTIC rows only those
   EMIT selects (a subject naming a bound `<name>=<count>` at a line's end, `HOOK_UNDECLARED`), and
   `published`, the ledger's bytes and sha256 as written (the run manifest's digest of it). A
   reader of the DIAGNOSTIC rows added to EMIT selects in `GapLedgerMain#readByEmit` too.
3. `final/result.json`: `claim` = the campaign claim; a `SAT_CANDIDATE` whose confirmation is not
   `confirmed` is `SAT_UNCONFIRMED`, and one no replay decided (`refutes` false) also a
   `CONFIRM_NO_VERDICT` row in `defects[]` (the confirmation is copied in);
   `refutedClaims`, every row of `refuted_claims.jsonl` (§10), whatever the claim;
   `restsOnRefutations` (the refuted models an UNSAT's core names, and each world a
   replay refuted for an open arm whose flip came back UNSAT or BOUNDED, kind `REFUTED_WORLD`); `concrete[]`
   with the last round's `openArms` (kind OPEN_ARM) beside its concrete anchors, and
   `evidence.unsatClosureComplete` true only where every such arm's flip came to UNSAT or stopped at
   its named bound (BOUNDED, in `bounded`); an arm whose
   flip came to no verdict is one `OPEN_ARM_UNANSWERED` row (`campaign_open_arms`), BLOCKING under any
   claim but a `SAT_CANDIDATE`; `findingKind`,
   `polarityDecides`, `valuationOrdinal`, `movedRoots`, `movedRootCategories` (each moved root's
   category, `contract.RootCategory`), `configurationOnly`, `blockers`, `reachability`, `finalStatus`, `gapCount`,
   `telemetryCount`, `undeclaredHookCount` (an `UNSAT_CLOSED` claim's count of the tree hooks that
   ran on their own concrete value, `HOOK_UNDECLARED` rows by hook and activation; null for any
   other claim), `accepted = (claim ∈ {SAT_CANDIDATE, UNSAT_CLOSED}) ∧ gapCount = 0`,
   `targetOccurrence`, `valuations`, `witnessFindings`; `bounded` (`campaign_bounds`), whatever the
   claim: null, or `{by, detail}` naming by configuration key each declared bound that cut the
   search -- the wave budget (`region_path_max_waves`, the stop REGION_PATH_WAVE_BUDGET_REACHED),
   `region_path_max_paths_per_region` (the LAST round's deferral rows: an earlier round's the rounds
   after it read, §7.4) and `region_path_max_world_depth` (ObligationFactory's DIAGNOSTIC rows, the
   bound in their subject), `region_path_max_tasks` (the static candidates the last round's closure
   cut: `truncated` less `ceilingCut`), `region_path_closure_ceiling` (occurrences the rows connect cut
   past `ClosurePlanner.CLOSURE_CEILING`, 1024), `schedule_max_jobs` (the schedule index's `closureCut`), `open_arm_max_refuted_worlds`
   (an open arm the last round left BOUNDED, §7.1), `replay_timeout_s` (the last round's
   `boundedFlips`: flips, and the FORCE run, whose replays were killed twice, §7.6, §7.10), `unplanned_input_max` (the last round's rows
   of a marker invocation past those GROW plans inputs for, §7.8) and `campaign_max_claims`
   (a refuted claim published at it); a round's `max-flips-per-path` is none (the next round asks
   the rest), nor is the time budget (`EXPLORATION_CUT`). `report.py` puts it in the row's note and a
   `## Bounded` section, `triage.py` in its `bounded` column and `BOUNDED=` count,
   `tools/rounds/round-verify.sh` as `BOUNDED:<keys>` and a per-round count.
4. `final/run-manifest.json`: provenance, iteration manifests, the path, size and sha256 of each
   required final artifact (`candidate.smt2`, `candidate_composition_manifest.json`, `gaps.json`
   (its digest the one `GapLedgerMain` took as it wrote it), `result.json`; a missing or empty one
   fails EMIT), stage wall times, session rows and bytes.
5. After REPRODUCE (§10b), `campaign_exit_verdict`: exit 2 when the claim is not
   `SAT_CANDIDATE`/`UNSAT_CLOSED`; exit 3 when BLOCKING gaps remain (`result.json`'s `gapCount`);
   else 0.

## 12. Acceptance: `experiments/accept/`

`accept.sh` builds the jar, then per case (one at a time; `CASES`, default the nine HDFS cases of
`ACCEPT_ALL_CASES`; `EXPECTED_MECHANISM` also names solr-18413 and solr-18406, both `CLOCK_SKEW`, and
solr-bugs-reindex-cleanup, a Solr door's fault)
runs `lib/run.sh <case> validate` and `campaign` under `CASE_TIMEOUT_SECONDS`, then
`probe.sh`, `cone.py` and `report.py`, and writes `summary.tsv`. `report.py` passes a case when all
hold, read off `final/result.json`, `gaps.json` and `cone.json`:

- `claim` is `SAT_CANDIDATE` (so CONFIRM agreed) and `confirmation.confirmed` is true, `finalStatus`
  is `FINAL_READY`, `accepted` is true, and `gaps.json` names no BLOCKING gap;
- `findingKind` is one of the four mechanisms and is the case's entry in `EXPECTED_MECHANISM` (a case
  the table does not name cannot pass); `polarityDecides` is true;
- `movedRoots` is non-empty and `valuationOrdinal ≥ 1` unless `CLOCK_SKEW`; an expected `root`/`value`
  must be moved to that value; for an entry naming fault doors (a tuple of client classes: the
  RPC-failure entries' `org.apache.hadoop.ipc.Client`, the Solr and ZooKeeper doors; `clocks: False`)
  a MARKER moved to true whose declared site (the plan's `EXPLICIT_SYMBOLIC_FAULT` input action) is in
  one of those classes, and no CLOCK cell moved;
- `cone.py`: every moved root is in the causal cone of the selected path — the constants its
  `path_fatal__i` assertion names (define-funs expanded, `let`/quantifier names bound), closed over
  the `message_family*` assertions under the same path selector that intersect it — and no
  `_field_HOFF.` boundary variable in any path's fatal condition is unnamed by that path's message
  families.

`probe.sh` strips the `valuation__` pins from `candidate.smt2` and asks z3 about the formula
unpinned, with the accepted assignment and with the other polarity; it is reported, never gated on.

Before the cases and before each case, `accept.sh` requires `MIN_FREE_GB` (6) free on the
filesystem `OUT` is written to (its nearest existing parent before `OUT` exists), `acc_free_gb`;
a 1 MB probe write there that is refused reads as 0 G (a full disk or a per-user quota `df` does
not show). The preflight fails by name; a case waits up to `DISK_WAIT_SECONDS` (1800) for room and
is then skipped as `no disk`.

A sweep (`tools/adhoc/sweep.sh`) does not use `report.py`: `tools/adhoc/triage.py` classes a case
with a `result.json` `CONFIRMED` when `claim` is `SAT_CANDIDATE` and `confirmation.confirmed` is true --
`CONFIG_ONLY` when `configurationOnly` is true (COMPOSE's rule, read, never re-derived), a finding read
after the others (`findings.py` ranks its mechanism after every other: a configuration-validation throw
fires by design) --, `REFUTED` when
`claim` is `SAT_UNCONFIRMED` (refuted, or decided by no replay: the confirmation's reason is the
row's reason), `UNSAT` when it is
`UNSAT_CLOSED` (a concrete anchor of `concrete[]` is the reason), else `RUN_DEFECT` (the first of
`defects[]` is the reason). A case without one is `STOPPED` when its summary row
exists (the stage and reason its logs state: the campaign's own failure, the case timeout, a
failed trace aggregation, a stage's Java main, the engine's `die`, a full disk or quota),
`PENDING` when never started, else `RUNNING` while some lift (`LIFTS`, default lift06–15) still
runs a process naming its directory, `DEAD` when none does.

`tools/regress/offline-ab.sh --round <round>... <baseline-jar> <candidate-jar> [case...]` is the
offline regression gate: per case of the first `--round` holding it, it runs every stage that is
a pure function of the recording once per jar — the static pass in `campaign_analyze_grown_scope`'s
loop (the door step, `ScopeGrowth --doors`, when the jar ships the library catalog; then the pass
and `ScopeGrowth` over its frontier until nothing is added or the case's budget is spent, the door
step again after each growth; the stage's wall is the loop's), the trace aggregation, PLAN,
EXPLORE round 0 and its solves, IMPORT, the closing EXPLORE round, COMPOSE with SOLVE and DECIDE,
and CONFIRM's planning — over private iterations that link the recorded sessions, with no
workload and no replay; `ab_compare.py` prints one table and exits 1 when a gating stage differs,
2 when one could not be checked; the static pass's summary is the slice's size (edges, the methods
they lie in, scope rows, READ_SITEs, CONFIG_KEYs, chosen/all root-demand boundaries, skeletons,
grown classes), and `AB_STAGES=SEED.static` runs that pass alone. `AB_STAGES=EXPLORE.drift`
replays a run's landing order (`ab_landings`, each side's whole loop on one host): one iteration
that evolves as the run's did, each recorded round planned again over the sessions landed before
its planner started (a session's directory ctime is its landing), the workers of the rounds before
it and the plan generation then current, with no answer and nothing in flight, so every flip it
offers is keyed, each round by a planner of its own; the summary counts the flips offered under
more than one id (an arm the run asks again on the same path) and the ids per arm -- what a change
to an arm's key does to re-asks, which the run's own answers, keyed by the recording jar, cannot
show. `AB_STAGES=EXPLORE.serve` replays the same order with the baseline side planning each round
in a JVM of its own and the candidate side asking every round of ONE served planner: run with one
jar as both sides, every round's files (its slot-table changes among them) and the folded table
must be identical, and `walls-<case>.EXPLORE.serve.tsv` holds both sides' per-round walls. Every
EXPLORE stage's slot table is compared folded, since two jars may spell it differently. The trace chain (aggregation,
PLAN, EXPLORE round 0) of both sides reads one set of static artifacts, the recording's own;
`AB_FRESH_SLICE=1` gives each side its own fresh static pass, to see what a slice change does to
the region plan and the closure. It runs beside live rounds, so each of its engine JVMs is placed
through the host ledger (`ab_place`: the host of `AB_HOSTS`, default `LIFTS`, with the most room,
charged its heap for its whole run, waited for when none has it). Every stage gates on bytes, the static pass included: it is the
same on every host and run ([SYMBOL-SCOPE.md §2.3](SYMBOL-SCOPE.md)). A round is read as the
current engine reads it, so the gate needs a round recorded by a build whose row contract HEAD
still reads. Both sides run under the gate's own checkout's case declarations, unless
`AB_BASELINE_REPO` names the baseline's: a change that moves a declaration's format with the jar
(the target spec) is gated that way, and each side's checkout path is one token in the
comparison.

## 13. Reading a run

- A campaign that died names its stage: `[campaign:error] stage=… component=… artifact=… reason=…`
  on stderr. A REPLAY death: `iteration-0000/seed-result/focused/replay.log` and the seed session's
  `gaps.jsonl.gz`. A pool or a head that seems stalled logs `waiting for room: …` or `waiting for
  memory for a head step of <mb> MB on any host: …`; a replay ended past its charge says why in its `replay.log`; the host ledger is
  `$CAUSYNTH_HOST_LEDGER/<host>/{available,charges/,cores}`.
- How EXPLORE ended: `iteration-0000/exploration.json` (the stop, every COMPOSE attempt at a
  witness, every obligation cancelled or reaped) and the log's `round N (wave W): …` lines.
- `final/gaps.json` `byStage`/`byCode`, then the BLOCKING rows' `detail`.
- Where the wall time went: `tools/analysis/timeline.py <accept-dir>...` reads a campaign's own
  files (stage metrics, file mtimes, the log) and prints each stage (SEED split into static pass,
  weave, recording and aggregation), each planner round (planning, dispatch to its last answer,
  its obligations' wait for a start; obligations by verdict, solver JVMs that failed; focused
  replays with min/median/max duration, their wait after their solve, and how many were refused,
  flipped or ended in error, and how many ended early (§5) with the time from the end's
  replay-log line to the JVM's last write), the head steps and their gates, the witness attempts,
  the CONFIRM replay and the top time sinks (EXPLORE's planning, gates and attempts, and the rest
  of its wall: waiting on the pool).  It reads the streaming layout (`obligations-NNNN/<id>/`:
  `host.txt` and `replay-host.txt` the starts, `obligation_result.jsonl` the answer), and a run
  pruned before those were kept (`accept.sh` `ACCEPT_KEEP_GLOBS`) by its logs' last writes. A gate or
  stage that started a head JVM includes the head's wait for memory (§7.7), which the log counts.
- Why a check stayed concrete: `tools/analysis/rootcov.py <round-or-campaign>...` prints, per
  campaign and over all, the anchor rows with a phi, wave-0 obligations, roots by category, PLAN
  admissions by basis (and the basis of each occurrence that minted a root the claim moved), the
  "decided concretely" refusals and the boundaries the fatal guards' operands stop at.
- Whether an UNSAT is vacuous: `tools/analysis/vacuity.py [--latest] <round-or-campaign>...` prints,
  per check, each composed path's phi (literal false after folding, unstated, true, symbolic), the
  guard decisions' terms, every read in the slice of the guard terms and the phi with its writer
  family in the path's session and whether `smt.Arms` could offer another writer (constructor,
  same-thread and LOST writers dropped; ancestry and order not repeated), the roots in that slice,
  the claim's moved roots, the BLOCKING codes, the named gap kinds and a verdict (CHECKING trap 24).
- `iteration-0000/obligation_results.jsonl` and each `obligations-NNNN/<id>/`: the verdict's
  `detail`, `obligation_query.smt2.gz` (the query as asked, with its `check-sat` and `get-value`; it
  re-runs by hand in z3), `focused_task.jsonl` (the world), `replay.log`, `stdout.log`/`stderr.log`.
  An obligation id holds no session id (§7.3), so it repeats across runs whose replays reproduce
  the same addresses and input shapes: an earlier run's directory is a baseline.
- `sessions/<id>/`: `targets.jsonl.gz` (`observedFatal`, `reachedAnchor`), `decisions.jsonl.gz`,
  `roots.jsonl.gz`, `schedule.jsonl.gz`: gzip (CONTRACT-SPEC §2.1), read with `zcat`/`gzip -cd` (a
  session its replay never closed ends at its last row: gzip says "unexpected end of file" after
  printing every row).
- `final/claim.json` (valuations with status, unsat core, selected path, session and arms),
  `candidate_composition_manifest.json`, `compose.log`, `confirm.json`, `confirm/confirm.log`.
- A schedule divergence is read by aligning: take the rows with a `kind` of the prefix the replay
  was held to (`recorded_schedule.jsonl`, or the worker's `schedule_prefix.jsonl.gz`) and of the
  session's `schedule.jsonl.gz`, compare `(kind, context, site)` position by position to the first
  mismatch, then count how many events of the expected key the replay made at all (none: an event
  the replay never makes; as many as the prefix: it came late). The `{mark, at}` rows of both files
  say where each occurrence opened; a SEND's `endpoint` joins the recording's `EXCHANGE_SEND` rows
  in `runtime/runtime_trace.jsonl`.
