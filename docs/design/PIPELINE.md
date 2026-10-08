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
| IMPORT | `campaign_import_session`; `contract.ImportGateMain` | `session_census.jsonl`, `import_gate.json`, `import_gated.txt`, `campaign_gaps.jsonl` | a session file is missing; a BLOCKING row invariant |
| EXPLORE | `campaign_explore` (the streaming loop), `campaign_stream_grow`; `explore.ExploreMain`, `explore.ObligationSolverMain`, `plan.ExposedRegionPlanMain` | `obligations-NNNN/`, `steps/NNNN/`, `obligation_results.jsonl`, focused sessions, `exploration.json` | a round's planner fails (one out of the most heap a head JVM is given ends the exploration instead, §7.9); a host's memory or cores cannot be read; a GROW re-run does not finish; a landed session's BLOCKING row invariant (as IMPORT) |
| — | `campaign_publish_iteration_manifest` | `iteration_manifest.json` | — |
| COMPOSE | `campaign_compose`; `compose.ComposeMain` | `final/candidate.smt2`, `candidate_composition_manifest.json`, `claim.json` | ComposeMain exits nonzero, its deepest throwable the reason (every refusal is a claim, not an exit) |
| SOLVE, DECIDE | `campaign_solve`, `campaign_decide` (read the manifest) | log lines | the manifest states no solver verdict or no valuation rows |
| CONFIRM | `campaign_confirm`; `explore.ConfirmMain`, one replay, `ConfirmMain --sessions` (the decision) | `final/confirm/`, `final/confirm.json`; a refuted claim's row in `refuted_claims.jsonl` | never (a failure is "unconfirmed"; after a refutation, while the budget has room, COMPOSE..CONFIRM run again for the next claim, the refuted one in `final/refuted/NNNN/`, §10) |
| EMIT | `campaign_emit` | `final/gaps.json`, `result.json`, `run-manifest.json` | a frozen input changed |
| REPRODUCE | `campaign_reproduce`; `explore.ConfirmMain --plant`, `reproduce_runs` native runs with the plant over the worker pool | `final/reproduce/`, `final/reproduce.json` | never (it ranks a finding, and moves no claim) |
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
  `Σ|x − recorded(x)|` over the integral roots and clocks it bounds, so a model is the smallest move
  that still takes the other arm (with a one-minute margin where the arm rests on a clock).
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
| `reproduce_runs`* (10), `reproduce_time_factor`* (3), `reproduce_min_s`* (300) | how many native reproduction runs, and each one's wall clock as a multiple of the recording's workload, at least `reproduce_min_s` (§10b) |

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
   the one decision each target row's open decider arm names (`TargetRow.OpenArm`). Loop-bound
   rows are keyed by Jimple unit id (`<method signature>#uNN`, field `loopSiteId`); the ids the
   pass uses are the skeletons' `loopControlSiteIds`, and any edit to an instrumented method moves
   the ids after it, so a case's loop-bound file is re-read from the skeletons after a tree edit.
2. `do_workload`: one weave in trace mode `region-state` (lineage classes from `plan.LineageScan`
   included), then the workload itself (`workload_command`; a nonzero exit fails SEED; its wall
   time in seconds is kept as `campaign_recorded_workload_s`, the base of the seed replay's
   bound, §5; the recording itself runs under no wall-clock bound). The weave writes only the rows
   the aggregation reads (`causynth/TracedRows`): call rows at a declared site, a field-accessing
   call, a configured-source hook site or a port's capture, argument and normal-exit rows only
   where a port captures them; every hook is still called, so each row keeps its number. The weave
   leaves the digest of the three static artifacts it decided the rows on (scope map, candidate
   graph, candidate skeletons: `TracedRows#inputsDigest`) beside the woven classes; the recorder
   states it in the trace's manifest (schema 2, `tracedRows`), and the aggregation refuses a pruned
   trace over other artifacts by name (`TRACED_ROWS_MISMATCH`: a site or port they add would find
   no rows); a schema-1 trace wrote every row. A frame
   writes one decision at one site at most twice (`CausynthTraceRecorder#emitDecision`: readers
   take a frame's decisions as a set, its first, or "more than once" for a loop). Its trace is
   bounded: past `recording_max_trace_mb` its watcher (`campaign_watch_workload`) ends the
   workload and leaves `runtime/RECORDING_BOUND` saying so, and SEED fails by that name (a trace
   cut short is never aggregated). Then
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
and cut summary name the classes (`ConcolicScheduler#deciderClasses`). When the closure still holds
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

## 4. INSTRUMENT

`campaign_instrument` clears `iteration-0000/instrumented-classes/` and runs `do_analyze` with
`CAUSYNTH_CONCOLIC_TASK_PLAN`/`_TASK_ID` set to the whole plan: one union weave of every task. The
tree must hold a class file, and `causynth.VerifyWovenClasses` must verify every woven class against
the replay's class path, or the stage fails naming the class; a woven class that fails as the class the
class path holds fails unwoven (the same throwable and message, or both a `NoClassDefFoundError` for types
no entry holds: Jetty, for ZooKeeper's admin server under a recipe's workload) is listed `UNLINKED` and does
not fail it, since the workload cannot link it either way. GROW re-runs this stage's function.
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
the IPC and DataTransfer doors walk the message they carry (`MessageCodec`, `WireExport`), staging each bound element
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
ran in full (`TimedWaits#outlast`, IDENTITY.md §8). A replay publishes one session under
`iteration-0000/sessions/<sessionId>/` (layout in [CONTRACT-SPEC.md §2](CONTRACT-SPEC.md)); with no
focus row its `manifest.json` states role `SEED`. The seed replay runs under a wall clock of
`seed_replay_time_factor` × `campaign_recorded_workload_s` seconds (§2), never less than
`replay_timeout_s`. It is `required`: a replay killed on that bound or otherwise (the failure
names what killed it; for the bound, the rule and its numbers, `campaign_adapter_timeout_rule`), a
session set with no non-empty `activations.jsonl`, or no `targets.jsonl` row whose `anchorSiteId`
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

A replay JVM draws its RSA key pairs from a fixed pool (`runtime.ReplayKeys`, a JCA provider put
first by `JUnitMethodRunner`; four pairs of exponent 65537 per size of 1024-4096 bits, in the jar's
`replay-rsa-keys.txt`, one after another per size): the concolic VM has none of HotSpot's
`BigInteger` intrinsics, so one 2048-bit prime search takes it 40-70 s, and a Solr node makes one as
it starts (four nodes spent 220 s of a 470 s seed replay there). A key pair is `SecureRandom` bits no
stage reads. Another size or exponent is the JDK's own search; the replay log names either once per
size. The recording searches as always. The scope map is read once, when the workload session
opens (`GuardedStoreSites#install`, which hands its rows to `ClockLoops`).

A replay's run ends before its VM session does (`runtime.JUnitMethodRunner#exit`, for the workload's
end and the early ends alike): admission ends (`ConcolicRegionRuntime#endAdmission`: no region
starts after it), live activations settle, the run totals close the session's rows (a closed
`SessionPublisher` writes nothing more), and only then the VM session closes. The settle
(`ConcolicResultPublisher#awaitSelectedResultPublications`) is bounded by progress: it gives up once
nothing has moved for 30 s (`#Grace`: no loop body charged, no activation settled, no publication
finished, no CPU on the publication thread and no garbage collection), so a publication that
computes is never cut and one blocked is: every activation still live is then stranded, and the
publication left running and every one queued behind it (the one publication thread reaches none)
are each a `TASK_UNANSWERED` `RESULT_PUBLICATION_UNSETTLED`, a seed's or a confirmation's session
included, which holds every obligation of the replay `NOT_ADMITTED`
(`FocusedReplay#noteUnsettledPublication`: its rows may be partial or missing). A stranded
activation is finished, abandoned and moved aside in one step (`ConcolicRegionRuntime#strand`,
under the lock its terminal takes); its VM region is its thread's, so the terminal that thread still
reaches closes it (`#closeStranded`) and publishes nothing. The end runs once: a
second thread ending the same run (an early end meeting the workload's own) waits for the first's
`System.exit`, and a caller of the run totals (`ConcolicResultPublisher#publishRunTotals`, also the
shutdown hook) returns only once they are published, so no exit halts the close half-done. Cluster threads
outlive the test, and a region started after the close would open a fresh VM session in which
every handle the old one made is foreign (`HANDOFF_FOREIGN_HANDLE`).

A focused replay ends early, once, for one of two reasons (`ConcolicResultPublisher#conclude`):

- `AT_WITNESS`: the focus row's declared occurrence publishes a target row that observed the fatal
  (`#concludeAtWitness`); its schedule states the run cut there (`ScheduleLog#witnessed`: a replay
  held to it holds a `WAKE` it never made to the order's end, IDENTITY.md §8).
- `AT_REFUSAL`: a refusal decided every obligation the replay carries (`#concludeAtRefusal`,
  `FocusedReplay#refusedAt`, §7.6).

Either way admission ends, `Causynth <UTC instant>: the replay ends <reason>` goes to the replay log, the
publications running settle, every activation still live is stranded at once (`TASK_UNANSWERED`
with the reason; after the workload's own end, one live while nothing progressed for the grace is
`TERMINAL_NEVER_REACHED`), and a publication
not yet started is withheld (the reason again): at the witness, one submitted after it (the
session is read whole up to the witness); at a refusal, every one (the session is withdrawn, and
draining the queue into it cost a Solr replay two to five minutes past the test's end). A stranded or late activation's path
is withheld and its mints are published, as an abandoned one's are: other activations' rows already
name its symbols (IMPORT invariant 11). The run then ends through `JUnitMethodRunner#exit`, whose
`System.exit` ends the in-process cluster (its threads and ports) with the JVM.

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
(`runtime.RowPublication`): `phiTerm` is the VM's satisfied predicate of the target branch put in
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
writes, reads, roots, targets, gaps, schedule` `.jsonl` and a non-empty `expressions.jsonl`, and writes
one `SESSION_CENSUS` row per (session, kind) to `session_census.jsonl`. `campaign_import_gate` then runs
`contract.ImportGateMain`, which appends every `contract.RowInvariants` violation (invariants 1-12,
[CONTRACT-SPEC.md §2.6](CONTRACT-SPEC.md)) to `campaign_gaps.jsonl` and prints a summary; one BLOCKING
violation fails IMPORT naming the first subject. The same gate runs on every session EXPLORE lands (§7.9).

`campaign_import_gate <iteration> <epoch> [summary] [session-dir...]` judges each session once: the
sessions it names (none named: every session of the corpus not gated yet), recorded in the ledger
`import_gated.txt`; a session the ledger names is not judged again. Every rule but two is one
session's. The two over the set are judged against the gated sessions still in the corpus: exactly
one SEED (1), and the epoch's roots (11) -- a new session against every root of the epoch, a gated
one again only for a root (id, symbol) a new session brings. So gating the corpus a wave, or a
session, at a time files exactly the rows one gate over all of it would, each once. One caller at a
time (the head). The gate holds one session at a time, so its heap and its charge on the host it is
placed on (§7.7) are 512 MB plus four times the largest session's size on disk (`campaign_import_gate_heap_mb`), not
`engine_memory_mb`, which is sized for a JVM holding the whole corpus (SOLR-18406 i1: charged
16 GB, IMPORT waited 7 min for room on the head and a wave's gate 30 min; the gate itself ran
seconds).

## 7. EXPLORE

EXPLORE collects the arms the seed lacks: it flips decisions the anchor's failure can depend on, one
focused replay per flip, in planner rounds over one streaming pool (§7.9), and never decides a
witness (only COMPOSE and z3 do).

### 7.1 One round: `explore.ExploreMain`

ONE planner JVM serves an exploration's rounds (`ExploreMain --serve <dir> --sessions
<iteration>/sessions --results obligation_results.jsonl --static-scope-map ... --target-occurrence
<declared>` plus the root domains and bounds; each round one question naming its `round`, its
`inFlight` (`<round>/in_flight.jsonl`) and its `outputDir` (`obligations-NNNN`), asked through
`explore.Service`, the protocol the host solvers speak, §7.5; the driver's side is §7.9). What it read
for a round it keeps for the next: the sessions' rows (`Corpus#read(Path, Path, Corpus)`: a landed
session's rows never change, so only the sessions new to the listing are parsed, and one that left
-- a GROW swap, after-witness trimming -- is dropped) with what was derived from each session's rows
alone (`Corpus.Derived`: its state join, its schedule's facts, read once, and the walks of its
expressions: symbols, leaves, read locations and events, state reads), the static map while its
file reads the same (by digest), and the slot table it changed (step 4). Within a round, what a
round asks again of the same corpus is answered once: an arm's dependence per task and decision
(`Corpus#dependence`: the frontier and the candidates key the same arms) and a task's feeders, and
the closure's walks of a demand that grew reuse its group, the group's reads and each read's
eligible writes (`ClosurePlanner.Walk#group`, `Corpus#eligibleWrites`). Every index across sessions
is built anew each round, the lowerings with it, so each round's files are the ones a planner of its own, reading the
iteration then, writes (`ExploreMain --round N --output-dir ...`, the offline stages' entry over the
same code; gated by `offline-ab.sh` `EXPLORE.serve`). A late hdfs-adhoc-07 round, rebuilt whole by a
JVM of its own, was ~15 min: 2.5 min reading 653 sessions' rows and 4 min reading and rewriting a
1.9 GB slot table (PERFORMANCE §5). A round reads the corpus (`explore.Corpus.read`: every landed
session, each worker's focus row as that session's world, the verdicts, the recorded schedule) and:

1. Names planned tasks answered at two addresses (`ADDRESS_UNSTABLE`, DIAGNOSTIC).
2. Resolves the declaration against the seed session's activations (`plan.SelectorResolution`);
   no single SEED session, an unresolved selector, or an address the seed never activated is a
   BLOCKING gap and leaves the round with no root.
3. Stops the branches that cannot answer the question (`explore.Branches`, §7.4) and plans the
   anchor's closure (§7.2). A closure truncated at `--max-tasks` is the round's DIAGNOSTIC
   `ADMISSION_GAP` and its manifest's `truncated` (the occurrences not planned); whether it blocks
   a claim is the exploration's end's to say (§7.9).
4. Reconciles the slot table (`explore.SlotTable`): one slot per
   (interaction, world) inside the closure; a WIRE consumer paired with another producer in the same
   world is a replacement, and a read whose observed write the run orders after it (the two rows'
   seqs, the VM's one event clock, whatever threads ran them; never the anchor chain, which orders
   occurrences, not their events) contradicts the order (both `TOPOLOGY_DIVERGENCE`, BLOCKING when
   the session is admitted, else DIAGNOSTIC); another
   world's pairing is a new slot. A slot stands on the session that opened it: the slots of a
   session no longer in the corpus (one a GROW swap withdrew, §7.8) are dropped first, here and
   where COMPOSE reads the table, and the session in its place opens them again. An occurrence a
   replay answered by its shape (IDENTITY §9, its `ADDRESS_UNSTABLE` row) stands at the planned
   address under another chain, so its pairings are that chain's: they open slots beside the
   planned occurrence's and replace none, whichever session lands first, since each slot is
   indexed by whether its opening session answered its consumer's occurrence; only another
   answered pairing fills such a slot. On disk the table is its rounds' changes: each round writes,
   last among its files, `obligations-NNNN/slots.jsonl`, the slots it opened or replaced (`SLOT`,
   the row the slot holds now) and those it dropped (`SLOT_DROPPED`), in order; the table is those
   files folded in round order, after an iteration's whole `slots.jsonl` where a run recorded before
   the per-round files has one (`SlotTable#read`). A round's planner folds the rounds before its own
   (the served one keeps the table it changed), so a round planned again starts from the same table
   and a round directory that goes takes its changes with it; COMPOSE folds them all.
5. Builds the ledger (§7.3), takes the arms in flight (`--in-flight`: the obligation rows the
   campaign has queued or running), builds the candidates (§7.4) and opens the round:
   `obligations.jsonl`, nothing settled and nothing in flight.
6. Names the WITNESSES: every admitted focused session whose target row at the anchor observed the
   fatal (`ExploreMain#witnesses`), and states the anchor as a target row spells its occurrence
   (`anchorOccurrences`), by which the campaign tells a witness as it lands (§7.9).
7. States the round's WAVE, a generation of worlds: one past the deepest wave whose obligation
   published a landed session, 0 over the seed alone. It deepens only as sessions land.
8. Writes `graph.jsonl` (`WaveGraph`: NODE per activated occurrence of admitted sessions, EDGE per
   WIRE pairing and STATE join, each with the world digests it was seen in, and a FRONTIER row with
   the counts new since the previous round), `growth.jsonl` (§7.8), `tasks.jsonl`, `gaps.jsonl` and
   `explore_manifest.json` (anchors, round, wave, witnesses, tasks with their `why`,
   proposed/answered/in-flight counts and the candidates held in flight, the branches stopped,
   verdict histogram, gap counts, state `OBLIGATIONS_PROPOSED` | `AWAITING` (nothing new, arms in
   flight) | `FIXED_POINT`, `concreteAnchors` and `openArms`). What only the seed ran is BLOCKING at the fixed
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
#successors`), and its producer planned (hdfs-11741: the balancer's KeyManager, reached by the SASL
producer's closure, decides on the expiry dates of nn0's `updateBlockKeys@1` response, whose handler
no session ran until it was demanded so); closed over the reads those name and the writes they could
observe. Each (kind, session, occurrence, cutoff, terms) is asked once per walk. CONFIRM's ORDER
reads the same closure (`RestsOn#closure`), the anchor's reads cut where its path decided. The occurrence and its state-connected
factor are
one symbolic unit: every member's attaches and reads are asked whether a demanded value rests on them,
and a member joins the closure only through them, as a writer or a producer below, never for touching
what the occurrence touches (two readers of one location pass each other nothing).

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
`demandDistance`, joined on the method, the location kind and the type as `#carriersAt` joins).
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
  location's carrier, unless the read's session states it holding other objects only
  (`STATIC_CANDIDATE_WRITER`; a heap location is one object's, and a store reaches only an object its
  occurrence holds: an occurrence whose recorded reads and writes name owners, none of them the
  location's, is no candidate; a static field, an owner that names no one object, or an occurrence
  with no recorded access is, `ClosurePlanner.Walk#holdsOthersOnly`; `StaticScopeMap#carriersAt`: a
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
- state reads a contributed expression makes (no ReadRow names them): the same writer rule, through
  `Corpus.expressionStateReads` (never for the anchor);
- the two doors of the message a demanded occurrence served (sender and receiver of its causal
  anchor's producer endpoint), each where a session recorded a fault decision of it (its fault
  point decides whether the message exists; the doors PLAN's `CONTROL_PRODUCER_V1` admits):
  `CONTROL_PRODUCER`, contributing no value. Any other door -- run under no planned task, a role,
  or one that decided no fault (hdfs-adhoc-28/29's heartbeat tick in a scope with no IPC client
  door, HG3: it waited as "only the seed replay ran this occurrence" and blocked the fixed point) --
  is one DIAGNOSTIC `ADMISSION_GAP` row and never waited for.

An attach or read no demanded value rests on is a DIAGNOSTIC gap, once per endpoint. A region holds a
static site when the map's method set of the region contains the site's method or one of its callers;
with no method set, region-id equality. "Activated" means an instrumented activation row: an ambient
row (a port event outside every admitted activation, `RowRuntime#ambientActivation`) names where the
event ran, not a region that ran the site, so it makes no static candidate
(`ClosurePlanner#activated`); an ambient occurrence joins the closure only through the rows that name
it. A static site no session activated is a DIAGNOSTIC gap ("the retained set would have to grow"),
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
outcome and `dependence`: the earlier decisions of the path and of the inherited flips' prefixes that
share a variable with the guard (`compose.Independence.ofGuard`), plus the input shape
(`Corpus.inputShape`): whether the task's occurrence ran, its handoff sites and producers, and, for
each factor member that writes state it reads and that this session ran, the same and its write
counts at the locations the guard reads — never delivered values, and a function of the session
alone: the members and each one's producers as sets (replies to one call arrive in any order), and none the session never ran (the corpus finds feeders as sessions
land, and such a member's line, the same in every session that did not run it, re-keyed every arm of
the session). Never the session. An arm is
settled when some session recorded it under the same dependence, or an earlier round answered it
`ADMITTED`, `UNSAT` or `NOT_ADMITTED` (`SAT_MODEL_READY` is no answer). An arm in flight is not
proposed again, by its id or by its flip (`ObligationFactory#flip`: task, path, site, ordinal,
flipped outcome), since its id may move while it flies: sessions landing since its round grow the
dependence.
The ledger is rebuilt every round from the corpus, `obligation_results.jsonl` and the arms in
flight.

An id drifts as sessions land (the factor, and so the input shape, grows), so one flip is proposed
again under new ids (SOLR-18413 r5: 185 questions asked 717 times, 118 of the 166 re-asked with
byte-identical queries). Its **question** (`ObligationFactory#question`) does not drift while what its
answer rests on reads the same: `<flip>:<content>`, the flip (`#flip`: task, path, site, ordinal,
flipped outcome), then a digest of the query as its solver is asked it (or the refusal that leaves
none) and all its replay is given -- the world it plants (the path's world: roots, clock skews,
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
decisions first. Bounds (`ExploreMain` options, defaults in `ObligationFactory`/`ClosurePlanner`):
`--max-tasks` 64, `--max-paths-per-region` 32 paths per task, `--max-flips-per-path` 32 owed
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

### 7.5 One obligation: `explore.ObligationSolverMain`

The obligations of an exploration that run on one host are answered by ONE solver JVM there
(`campaign_solve_obligation`; `ObligationSolverMain --serve`, `explore.Service`, the one protocol of
a JVM that answers an exploration's questions in turn over state it keeps, the planner's too, §7.1:
questions on the serving host's own disk, oldest first, an answer `{exit, error}` whose error is the
deepest throwable): the first
question starts it if its host has room for a start's worth now (`campaign_start_solver`:
`campaign_solve_obligation` never waits for memory to start one), charged at the host ledger
`campaign_solver_start_mb` (1 GB) for as long as it runs (it holds the charge itself,
`campaign_host_keep`, past the obligation that started it) and what its resident memory grows past
that as it grows, by a running JVM's rule (`campaign_watch_workload`: refused only when the host's real use
would pass the ceiling, and then the JVM is ended); its heap is capped at the case's engine heap
(`campaign_solver_heap_mb` = `engine_memory_mb`, the heap COMPOSE reads the same corpus with; a fixed
8 GB was outgrown by hdfs-adhoc-07's doubled closure: an hour of garbage collection with 24 questions
queued, then OutOfMemoryError). A host holds at most `campaign_stream_solves_per_host` (2) of a
campaign's solves at once (`campaign_stream_try_host`): more add no answer, only their question
charges while they wait in the solver's queue. Charged that at its start, a solver waited for room it did not use, and every question of
its corpus waited behind the start (round x1, eleven cases at once: 50-75 minutes). It answers the
questions in the order they came, each from the corpus as it stands when the question is taken:
read again whenever a session landed in it or left it since (its session listing,
`ObligationSolverMain#listing`; the head lands sessions as the exploration streams), each session
the read before already holds taken from it unread (`Corpus#read(Path, Path, Corpus)`: a landed
session's rows never change, and reading them is the read's whole cost, 45 s over hdfs-11741 i1's
175 sessions), else the corpus as read (`Corpus#freshLowerings`) -- so each obligation's files are
the ones a JVM of its own, reading the corpus then, writes -- into a directory on the host's disk,
named by the corpus, that the asking worker moves into its worker directory; it ends once none has
come for `campaign_solver_idle_s` (300). Its log is `solver-<host>.log` beside the corpus. A
question still waiting when its solver ended starts the next one. A question that waits for its
solver says so after a minute and every ten minutes after (`campaign_solver_wait_said`). A host
with no room to start a solver now answers the question in a solver JVM of its own at once
(`campaign_solve_obligation_alone ... <charged_mb>`, `ObligationSolverMain --obligation-id`),
under the solve's own charge (what a solver starts at, §7.7), what it grows past that asked of the
host as it grows. A question the host's solver, or that JVM, could not answer (it ran out of heap on it,
died, or was ended at what its host could hold) is no answer: it is asked once more of a solver JVM of
its own at `engine_memory_mb`, placed as any start (`campaign_solve_obligation_placed`): its need is
what the first measurably held -- its watched peak, or the host's solver's heap -- with the usual
margin (`campaign_need_of_peak_mb`, ×1.5), at least half a solver's heap (`campaign_solver_retry_mb`:
a peak a growing solver was ended at is a lower bound; hdfs-adhoc-07 HF3's retries charged by it were
ended again), charged on the pool's host with the most room for it, this
one or a peer (`--run-placed`); no host with the room within `campaign_solver_place_patience_s` (600)
fails the worker, by name (hdfs-adhoc-11 CW4b/CW5: workers waited their whole 3900 s bound
for 16384 MB on the one host they ran on). Neither settles a question
(`question.txt`/`question.asked` are removed), and a second failure fails the worker: an unfinished
obligation (§7.7).

`ObligationFactory.locate` finds the published obligation's path in the corpus under its round's id
(a path gone from the corpus is `NOT_ADMITTED`). `FlipQuery.build` asserts the path as its replay ran
it up to the flipped decision, the flipped decision negated, and every inherited flip's prefix through
its flipped decision (`Arms.conjunct`/`Arms.pathCondition` apply the recorded polarity; terms are
lowered by the one lowering, `compose.SmtLowering`). Each symbol it names gets one rule:

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
  `maxSlowDisksToExclude <= 0` over the reconfiguration's 0 and its INITIAL 1).
  Only reads the text names are variables: a container state behind a guard is inlined by its join
  (the closure demands its writers, §7.2), so the query declares nothing for it — a variable bound
  to each writer's state would constrain nothing, and its equalities over states built by removals
  (lambdas) are outside what z3 decides (`unknown`, "incomplete (theory array)").

An undeclared name in the flipped conjunct refuses the query (`DECLARATION_MISSING`); in a prefix
conjunct it drops the conjunct (DIAGNOSTIC); a malformed lowered term likewise. A name is declared
when the query declares it, a `let` binds it, the fixed preamble states it, or it is a theory
operator of `compose.SmtNames.BUILTIN`, the one vocabulary every stage reads with, which lists every
operator the lowering writes (the string operators `str.substr`, `str.indexof`, `str.at`,
`str.from_code`, `str.to_code`, and `str.in_re`, `re.*`, `re.range` of `String.trim` among them,
the floating-point operators, `to_fp`, `int2bv`, `bv2int`
and the `Array` sort); COMPOSE refuses a path on the same test. A symbol no rule binds
refuses (`UNPRODUCIBLE_ANSWER`); a query whose flipped predicate reaches no variable of its own --
none it names, none a definition it rests on names (`FlipQuery#flipCone`) -- is not asked, whatever
variables a prefix decision binds: by the owner's ruling (only SAT or UNSAT; a concrete value is a
constant) its other arm is UNSAT on that path, named `NOT_FLIPPABLE` (`FlipQuery#NOT_FLIPPABLE`,
`ObligationFactory#solve`), unless its occurrence read a version no row of the corpus wrote (held at
what it read, its producer unstated, `FlipQuery#heldReads`): that refusal stays (`ADMISSION_GAP`,
DIAGNOSTIC), the scope hole being real; one that reaches only leaves a frame's
write was freed to (`SmtLowering#framedLeaves`: the writer computed on an arrival it refused, so no
plant reaches them) is refused before it is solved (`UNPRODUCIBLE_ANSWER`, DIAGNOSTIC, named). A construct the
lowering refuses inside a stated term becomes a fresh `unsupported__*` constant of its sort and stays
in the query. Demanded conjuncts (the flip and the inherited flips) get a one-minute clock margin on
each comparison atom over a clock whose polarity `not`/`and`/`or` resolve (`explore.ClockMargin`;
an atom it cannot strengthen is a DIAGNOSTIC gap). The objective is the nearest world:
`minimize Σ|x − recorded(x)|` over bounded Int roots and clocks (`FlipQueryText`).

z3 runs with `solver_timeout_ms`, which its driver (`smt.Z3`) enforces; a JVM that ends takes its
running z3 processes with it (a shutdown hook), every z3 is started under `setpriv --pdeathsig
KILL` (`Z3#DIES_WITH_ITS_DRIVER`), so the kernel kills it when the JVM thread that started it is
gone however the JVM ended (a KILL runs no hook), and each z3 also carries its own hard timeout ten
seconds past that budget (`-T`, `Z3#hardTimeout`), for a driver that hangs. A run starts only while
its host's `MemAvailable`, less what this JVM's running z3s may still grow to (each up to the most
any of them has held) and two such z3s for the new run, is at least the share
`CAUSYNTH_HOST_MAX_USED_PCT` keeps free (`Z3#enter`; a JVM with no run in flight starts one anyway):
sixteen z3s of hdfs-11741 m1's paths, a GB each beside the composer's 15 GB, took a host to 82 %. Every run, here and in COMPOSE, is two z3 processes, one per arithmetic engine
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
by COMPOSE's one rule (`SmtText#literal` → `VmTermLowering#smtLiteral`). A writer choice the
model sets away from the writer the recording's reads observed, the location's INITIAL among them,
is a **planted pairing**, counted like an answered handoff (`ObligationFactory#planted`: reader →
writer, each as CONFIRM names them, `ConfirmMain#writer`; one of a read another session made refuses,
`PAIRING_UNPLANTABLE`). A pairing is planted only where the recorded ones take no flip: a model
that moves one is asked again with every writer choice held to the recorded writer
(`ObligationFactory#heldToRecording`; a container state follows its writer's, and a refused term
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
the flipped world may read it again, CONFIRM's for the read's activation); a pairing that session states no read
or write of refuses (`PAIRING_UNSTATED`). The worker writes `obligation_result.jsonl`
(`SAT_MODEL_READY`), `obligation.jsonl`, `obligation_query.smt2`, `gaps.jsonl`,
`focused_task.jsonl` (the focus row, [CONTRACT-SPEC.md §3](CONTRACT-SPEC.md)), the pairings'
`expected_edges.jsonl` and the schedule cut (`SchedulePrefix.write`, held): the source session's
schedule up to the first event or mark of the flip occurrence, the focused occurrence, a factor
member, or an occurrence an `ORDER` moves after another's that the session ran first (the
prefix is followed only up to the first event the pairings reorder) goes to
`schedule_prefix.jsonl`, the rest to `schedule_suffix.jsonl`.

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
the worker had withdrawn, and the head waited for them until the campaign failed). `ADMITTED` = the flipped
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
anchor, the fatal and writers after the anchor among them), so only the witness ends it early. A
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

A replay killed on its bound: its session is withdrawn to `<worker>/timed-out-sessions/` and the
answer is `NOT_ADMITTED` naming the bound. A question no solver could answer (§7.5), and a replay
that states no verdict, fail their worker, which is then that obligation's `NOT_ADMITTED` and an
`OBLIGATION_UNFINISHED` gap (§7.7); in a GROW re-run a replay with no verdict fails EXPLORE, and in
CONFIRM it is a confirmation that did not confirm.

### 7.7 The work pool

One pool for the whole exploration. An obligation is two starts: its SOLVE
(`campaign_obligation_worker`: its question answered by its host's solver, §7.5) and, when the
solver answers `SAT_MODEL_READY`, its REPLAY (`campaign_obligation_replay` in the obligation's
worker directory, on the model's focus row the solve left there), which the head queues first the
moment the solve returns (`campaign_stream_ended`; between two starts of a dispatch too,
`campaign_stream_collect_jobs`), not at the next step -- behind only a witness's `CONFIRM` and GROW's
`RERUN`s queued first (`campaign_stream_queue_replay`; hdfs-11741 AR1: 473 replays of later solves
started ahead of the witness's confirmation, four hours) -- on the class tree and
plan the solve started on (carried by its queue entry, even when a GROW wove a newer generation
since). Until its REPLAY lands, the obligation is in flight (`stream_flying`, the planner's
`--in-flight`): solving, queued as a REPLAY or replaying, it is never proposed again; only the
replay's verdict lands, and an UNSAT, NOT_ADMITTED or reused ADMITTED answer of the solve lands as
the obligation's. The replay's answer replaces the solver's row as a new inode
(`campaign_write_whole`), never in place: written on another host than the row it replaces, an
NFS client holding the old row cached rewrote it past a truncate it lost (MCH1: the replay's row,
then the tail of the solver's, and the planner failed on the line). The head starts each queued solve, REPLAY, GROW re-run (§7.8) and confirmation,
first first, while the exploration runs fewer than its share of a shared pool (below; a REPLAY
counts like any start), on the next host of `campaign_worker_hosts` (empty: this machine, no
ssh), round-robin from the host after the last one chosen (`campaign_stream_admit_host`), a solve
first on a host where it started one within the solver's idle time (`campaign_stream_warm`: that
host's solver of its corpus likely still serves, so the question needs no solver started and no
corpus read), a REPLAY on whichever host admits it (its worker is on the shared home): a host is
taken while it runs fewer of the campaign's starts than it has cores (read once,
`campaign_host_cores`) and its memory ledger admits one more start; none admitting, the head waits
for a return, its step's end or the poll interval (`campaign_host_poll_s`). A start runs locally in
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
where its campaign's solver serves (`campaign_stream_warm`) needs its question's z3 run
(`campaign_question_mb`, 512 MB: the serving solver's JVM is charged on its own, §7.5; HI1/HI2's z3
runs: median 1 MB, p90 369 MB, at most 1.8 GB), on a cold host what a solver JVM starts at
(`campaign_solver_start_mb`, 1 GB: its question is answered in a JVM of its own under that charge
when its host has no room for its solver), either growing as its JVM does, never a replay's (HG5A-11, hdfs-adhoc-19: its eight obligations waited 12 of EXPLORE's 13
minutes for room for a 2500 MB replay each, and their solver refused all eight: none replayed). A REPLAY, a re-run
or a confirmation needs its replay's: the campaign's MEASURED REPLAY NEED (`campaign_replay_need_mb`), the largest resident peak its replays
stated so far -- the seed replay's first (HEAD STEPS below), then every obligation's, re-run's and
CONFIRM replay's as it returns (`campaign_replay_measured`, read in `campaign_stream_ended`) --
times 1.5, rounded up to 128 MB, at least 512 MB, and charged at most half a host's ceiling
(`campaign_replay_charge_mb`). An obligation replay peaks near its own seed replay (round HG4:
hdfs-11741 674 / 662-715 MB, hdfs-17897 552 / 540-555), while the static 2500 MB per obligation
and seven times the recording per CONFIRM held the lifts' ledger at 11-22 GB over 3-7 GB of real
use (HG5A); one that outgrows the need grows its charge as below and raises the need of every
start after it (hdfs-adhoc-15: seed 514 MB, obligations 939-2003). The charge is taken at the
start (`campaign_stream_admit_host`, `stream_admitted_mb`, handed to the job); the head holds it,
the job releases it as soon as its work returned, before the head waits to see what a peer wrote,
and the head again once it collected or reaped the job (`campaign_stream_release`). A replay JVM
is handed what its host was charged for it (`CAUSYNTH_CHARGED_MB`) and its whole need
(`CAUSYNTH_HEAP_BASIS_MB`): its heap is half the need (4 GB at least), and
`experiments/lib/execute.sh` watches it until it ends (`campaign_watch_workload`): one whose
resident memory grows past its charge asks its host's ledger for the excess, as one more charge,
granted unless the host's real use would pass `L` with it, and holds what it was granted, released
when it ends; one the host cannot take is ended, saying so; each states its peak at its end and
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
it waits, saying so once. A step on a peer runs through the remote worker script as
`run_engine.sh --run-placed` (`campaign_run_placed`) in the head's working directory, with the
head's exported `CAUSYNTH_`/`GRAPH_CHECKER_` variables, its output passed back as its own: a
program, or a `run_engine.sh` function whose arguments are all it reads of the head. The steps are
every engine JVM of every stage -- SEED's static passes, scope growth and trace aggregation, PLAN,
INSTRUMENT and its verifier, the import gate, the planner, COMPOSE, CONFIRM's and REPRODUCE's
`ConfirmMain`, GROW's planner and weave -- each charged while it runs at the heap
it starts at (`engine_java`, `campaign_engine_start_mb`): its main's measured need
(`campaign_engine_need_mb`: the static pass 4 GB, the planner and the composer 8 GB, the trace
aggregation, scheduler, lineage scan, scope growth, woven-class verifier, CONFIRM, GROW's
`ExposedRegionPlanMain` (0.13 GB measured) 2 GB; the import gate its own, §6), or `engine_memory_mb` (else 8192) for a main with none; a JVM
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
heap, read again at every heartbeat; before any was measured, what its planner or composer starts
at), never the case's engine heap; a step its room does not cover is placed by its own charge, as
every head step is -- (`campaign_head_reserve`,
`<host>/heads/<id>` stating its need, fresh while the head lives, idle unless one of its JVMs
runs): a start that is no head's own counts the largest idle fresh
reservation of the host as used, a head's own start counts none (heads take turns and never
block each other), and the head gives its room up when it exits. A head step that waits for room
holds its need on the pool's host with the most room when it began to wait (`campaign_head_hold`,
`<host>/heads/<id>.hold`, fresh while the head lives, given up once the step is placed or the head
exits; `campaign_head_hold_room`): every start but the head's own counts it as a reservation, so
that host drains as its starts return instead of being taken again one obligation at a time
(a40h2's 14 GB seed replay waited 70 min, V5-11741's 16 GB GROW step 40 min and more, while the
pool kept every lift busy).
An obligation whose worker does not finish (a nonzero exit, local or remote, or a result the head
cannot see) is its own answer (`campaign_obligation_unfinished`): every process on its host whose
command line names its worker directory is ended (a peer's replay JVM is in a process group the
remote wrapper's watchdog does not reach), what it staged moves to `<worker>/unfinished-sessions/`,
and its row is `NOT_ADMITTED` naming the host, the exit and the worker's own last error (an engine
failure's `die` or `campaign_fail` line). An engine failure stays loud: each such obligation files a
DIAGNOSTIC `ADMISSION_GAP` `OBLIGATION_UNFINISHED` in `campaign_gaps.jsonl`, which EMIT carries,
and `iteration_manifest.json` counts them (`unfinishedObligations`). A host whose memory or cores
cannot be read for `campaign_ssh_patience_s` fails the campaign at EXPLORE; a head that fails mid-exploration
ends everything it started first (an EXIT trap: each job's process tree, and every peer's workers).

### 7.8 GROW

When a round's `growth.jsonl` holds `EXPOSED_REGION` rows (occurrence, region, node, exposing session
and its obligation), the head grows instead of queueing the round's proposals, which a later round
asks again over the grown corpus (`campaign_stream_grow`). One GROW is one GENERATION of the plan
and the class tree, under `generations/g<k>/`: `plan.ExposedRegionPlanMain` synthesizes one task row
per exposed address (admission basis `EXPOSED_BY:`, static inputs only, the plan's
`replayGroupId`), the generation's plan is the one before it plus those rows, written as a new file
-- the iteration's plan and the seed plan are its hard links from then on, and the generation before
keeps its own inode for whatever runs on it -- and INSTRUMENT weaves it into the generation's own
tree. Each exposing obligation's replay is queued first, to re-run on whichever host of the pool
admits it (§7.7) in
`<worker>/grow-<round>/<obligation>/` (the worker's focus row and schedule cut linked in). Until every
re-run has returned and no obligation's solve runs that started before them, no solve starts and
no round is planned (a REPLAY reads no corpus and goes on, on its solve's generation); then each re-run SWAPS in (`campaign_stream_swap`): the exposing session and the
worker's previous files move to `<worker>/before-<round>/`, the re-run's files become the
worker's, its session lands, and its verdict replaces the obligation's row in
`obligation_results.jsonl`. The queue stays first and in flight: the round after the swap gets it as
`--in-flight` and proposes only what none of it asks, its new obligations queued behind it (hdfs-11741
HG3: 342 queued obligations dropped and re-proposed put the witness obligation at 81 of 409). A kept
obligation cut from an exposing session is answered by its solver by name (`NOT_ADMITTED`, "no
session of this corpus still states path ...") and a later round asks it again of the re-run's
session. The withdrawn session's slots go with it (§7.1 step 4): under the grown plan
the region's events stand in new occurrences, so its endpoints have new ids, and a slot of the old
run would read the re-run and every later session of its world as a replacement (hdfs-11741 V4:
two BLOCKING rows withheld the witness's composition). Once nothing runs, the last generation's tree is the iteration's
`instrumented-classes` (CONFIRM, REPRODUCE). An exposure no obligation names (seed exposure) fails
EXPLORE.

### 7.9 The loop

`campaign_explore` is one streaming loop on the head, with no wave barrier. It starts queued
obligations wherever a host admits one (§7.7) and collects each as it returns
(`campaign_stream_wait`). Its own JVM work is one STEP at a time, in the background
(`campaign_stream_step`, in `steps/NNNN/`), so the pool goes on starting and collecting while a step
waits for memory or runs. A step's JVMs -- the gate, the planner, an attempt's composer -- and GROW's
planner and weave are head steps (§7.7): each goes wherever there is room. Between two steps, in the head's hands (`campaign_stream_step_start`),
everything that returned meanwhile lands: each verdict is appended to `obligation_results.jsonl`
(`campaign_stream_land`), GROW's re-runs swap in once due (§7.8), and the sessions the workers
staged move into the corpus (`campaign_stream_move`). The next step then takes them in: ONE IMPORT
gate (§6) over exactly them (the list `gate`, its summary `import_gate.json`; one BLOCKING violation
fails the campaign at IMPORT) and the round now owed (`round`, planned into `obligations-NNNN/` by
the exploration's planner, §7.1) -- owed once a session has landed, or once nothing is queued or
running and an answer came since the last round. THE PLANNER SERVICE (`campaign_stream_plan`): the
step starts it when none lives, as a head step -- placed by the usual rule (`campaign_head_place`) at
what the planner starts at (`campaign_engine_start_mb`), its charge held for its life by the shell
that holds it (`campaign_host_keep`, as a host solver's), grown as a watched JVM
(`campaign_watch_workload`), the head's room marked busy while it runs on the head's host -- and asks
the round of it on its host (`campaign_planner_ask`, through the remote worker script when it runs on
a peer: its questions wait on that host's disk, `campaign_planner_dir`). Its state is
`iteration-0000/planner/`, its log `planner.log`. One that ran out of a heap below `engine_memory_mb`
(exit 3) is started again at twice it and the round asked again; out of the engine heap it is
PLANNER_HEAP_EXCEEDED (below); any other end fails EXPLORE with its deepest throwable -- never a
silent start of another. The exploration's end stops it (`campaign_planner_stop`), and so does the
head's EXIT trap. A step after which witnesses wait is followed by an
attempt at them (`witnesses`, below), a step of its own. A head JVM that outgrew its need in a step
(§7.7) is the head's from then on (`outgrown`).
When the step returns the head takes its round (`campaign_stream_take_round`): the wave budget,
GROW, else its proposals into the queue, where they start at once. The corpus and the ledger change
only between two steps, so a step reads them as a landed whole, and the round's in-flight rows
(`in_flight.jsonl`, §7.3) are what is queued or running as the step starts; the busier the head,
the more returns one step takes in. The exploration has five ends, each stated in
`exploration.json` (stop, rounds, steps, generations, answers, attempts, and every obligation
cancelled or reaped, by id):

- **WITNESSED.** A landed session whose replay was ADMITTED and whose target row at the declared
  occurrence (the last round's `anchorOccurrences`) observed the fatal -- the rule of §7.1 step 6 --
  is a witness: once the step that took it in has gated it, the next step is an attempt at every
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
  confirmation still owed is its attempt's row -- and the sessions that landed after the accepted
  attempt composed leave the corpus for `<campaign>/explore-reaped/after-witness/`
  (`exploration.json` `afterWitness`), so the corpus COMPOSE reads next is exactly the one the
  attempt read; a DIAGNOSTIC `WITNESSED` row goes to `campaign_gaps.jsonl`. Refuted, or given no
  verdict (a refused model: a mismatch, a replay that published none), its model is excluded from
  every later composition (§10) and the exploration goes on, as after any other claim. With no room
  left in the campaign's budget
  for a confirmation (`campaign_claim_room`, below), the claim is accepted unconfirmed and the
  final CONFIRM decides.
  A witness ends the exploration only once its OWN chain is closed (owner 2026-10-06): an attempt
  whose COMPOSE names an open chain (`ComposeMain#campaignClaim` `openChain`: each value the claimed
  path's fatal condition rests on that no attested producer made -- the set
  `experiments/accept/cone.py` reads off the formula, `compose.Cone` -- the claim RUN_DEFECT) is
  not confirmed (`campaign_stream_open_chain`); the head cancels the queued obligations and grows the
  producers those values' arrivals name (`campaign_stream_open`): each later round grows only its
  exposures of them, each producer once, and queues none of its obligations
  (`campaign_stream_chain_round`); once the GROW swaps in, the attempt's witnesses still in the
  corpus are attempted again, a re-run landing as a witness of its own
  (`campaign_stream_chain_reattempt`). A chain whose every producer was grown already cannot close,
  and a fixed point ends a chain no exposure reaches: the final claim names each open value
  (`WITNESS_CHAIN_OPEN`, EMIT's `defects[]`). hdfs-adhoc-12 AW2: the HA status txid's export at
  nn0 was exposed by the witness's own session, which ended the exploration before GROW.
  This is every campaign's rule: the question is one declared occurrence (owner 2026-09-28). Once
  the exploration has stopped otherwise, no attempt is made.
- **CAMPAIGN_BUDGET_REACHED.** Between two steps, the campaign's budget (`campaign_budget_s` from
  the campaign's start; `accept.sh` passes what is left of the case's `CASE_TIMEOUT_SECONDS`) has
  less left than the stages after the exploration are owed (`campaign_claim_room`): its reserve,
  `campaign_reserve`, COMPOSE and EMIT each as long as the longest COMPOSE the campaign measured
  (its stage metrics and its witness attempts; the last planner round, which reads the same corpus,
  standing for a COMPOSE not yet run: its `in_flight.jsonl`, copied as the planner starts, to its
  `explore_manifest.json`, `campaign_last_round_millis`), CONFIRM as long as the longest CONFIRM
  (the seed's REPLAY standing for a CONFIRM not yet run), REPRODUCE its own bound
  (`campaign_reproduce_bound`: `reproduce_time_factor` times the recorded workload, at least
  `reproduce_min_s`; its native runs go out at once), never less than
  `campaign_reserve_s` (600; a budget not above it is refused by
  `validate_config`). The exploration ends as at a witness (queue cancelled, what runs or returned
  unlanded reaped), and the stop is a DIAGNOSTIC row stating what it left owed.
- **REGION_PATH_WAVE_BUDGET_REACHED.** A round of wave `≥ region_path_max_waves` that still owes
  work is not dispatched (its proposals are named cancelled): the queued solves are cancelled, what
  runs lands -- a solved obligation's REPLAY too -- and the stop is a DIAGNOSTIC row. The wave bound is
  declared and generous: a last-resort valve (RULES, the owner's bound rule), named in `result.json`
  `bounded` like every declared bound that cut the search (§11), never read as the closure's own end.
- **FIXED_POINT.** Nothing queued, running or unlanded, no step running, and the last round, over
  every answer, proposed and exposed nothing.
- **PLANNER_HEAP_EXCEEDED.** The planner ran out of the most heap a head JVM is given
  (`engine_memory_mb`, exit 3, §7.7): the corpus outgrew what the head can hold, so that round is
  not planned (its directory goes, its logs stay in the step), what runs lands, and the stop is a
  DIAGNOSTIC row naming the round, the corpus's size on disk and the planner's error -- rounds
  were still owed. Any other planner failure fails EXPLORE, its deepest throwable the reason.

**THE END IS JUDGED ONCE, AT EMIT** (`campaign_exploration_cut`, the one place; owner 2026-10-04,
only SAT or UNSAT): `exploration.json` states what the end left owed -- queued obligations
cancelled, unlanded jobs and confirmations reaped, GROW re-runs dropped from the queue (the
exposing round's growth and obligations with them), a round due when the budget stopped it
(answers landed since the last round, or re-runs and swaps owed) -- and an end that owed work
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
8 GB start gives its planner and composer more (`engine_memory_mb`, hdfs-11741's 16 GB): the 70
sessions (5.7 GB on disk) of round a40h2's check DataStreamer-638 ran its round-4 planner out of
8 GB. An end other than WITNESSED on a
last round whose closure was truncated (its `truncated`) is one BLOCKING
`REGION_PATH_CLOSURE_TRUNCATED` row naming that round (`campaign_stream_truncation`): a claim over
that closure misses arms. An accepted witness asks nothing past it, so its rounds' truncations stay
DIAGNOSTIC. COMPOSE, CONFIRM and EMIT then run on the corpus EXPLORE left, as after any end.

`campaign_publish_iteration_manifest` then writes `iteration_manifest.json`: provenance, digests of the
task plan, schedule index, census and obligation results, the members and their obligation digests.

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

Corpus-level BLOCKING gaps: one solver name for two roots, a session not read whole
(`SESSION_INCOMPLETE`), a session's own verdict disagreeing with the worker's result row, not exactly
one SEED, an unreadable slot table, one name at two sorts, one name for two identities. Sessions that
replace a slot (§7.1) give no arms.

**Admission** (`admit`, `settled`): one path per session whose target row at the anchor reached it
(beside one, a target row that did not reach it is a DIAGNOSTIC gap); where none reached it, one per
session that ran the occurrence and left the way to the throw at a guard (`RestsOn#wayGuard`, the
last decision at a target site's path site), its prefix the decisions before that guard: at a
SYMBOLIC guard its fatal arm is the guard's other arm, the way to the throw (a witness turns it,
CONFIRM judges the rest), at a concrete one the constant healthy decision (`false`), the guard named
in `concrete[]` as WAY with what its term rests on (hdfs-adhoc-07, 48); the seed always, a focused session only when all its own verdicts are
`ADMITTED`; an obligation its manifest names with no verdict is BLOCKING. No target row at all --
the declared occurrence never ran -- is BLOCKING `DECLARATION_MISSING`; no disjunct is BLOCKING
`ADMISSION_GAP` naming the first refusal.

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
  what its replay planted at the consumer, not what a run delivered, so it is never a literal);
  an attach no session attests the producer of (or with no producer named) has a producer no row
  states: HELD at the value its row states it received, conjoined with the path (inside an arm: with
  the arm's body) and named (`Composer.Concrete` HELD, "producer unstated", its `arm` the arm whose
  body holds it, none on the path's own); one whose producer is attested and no export of
  it lowers, or whose row states a value the lowering places nowhere, is FREE, named: nothing pins
  it, and a path is never dropped for it;
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
  "producer unstated"), else REFUSE
  (`UNSTATED_VALUE`); a write of a frame whose producer moves is FREE before any join; dropped, the
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

Any refusal drops the path and is filed with its own class (an open lowering refusal is a
DIAGNOSTIC `UNSTATED_VALUE`); a dropped path is never silent: the claim names every admitted path
COMPOSE refused, with its first refusal (`Composition#refusedPaths`, `result.json` `refusedPaths`),
and an UNSAT says nothing about them.

Then **message families** (`ComposedFamilies.closeFamilies`): attaches grouped by correlation id,
one message under one selector; the eligible senders are the
sessions with an attested arm at every leaf of the message, whose world's flip set contains or is
contained in the path's; one `message_arm__` selector per sender (identical arm bodies share one),
exactly one, each arm guarded by its replay's value of every root it holds under (`Arms#arm`:
those its expression names, every varied root, every root its replay read and minted none -- the
valuation its path would carry, never a clock nor a derived root; a guard symbol no row has
declared yet is declared at its root's sort) and closed like a path in its own session (producer prefix before the delivery, its
P3 closure, nested families to depth 16). Every handoff the arm's conjunction names, its delivery's
and those its closure's conditions and joins read (`ComposedFamilies#handedOn`), goes by the path's
own arrival rule in the arm's session (`Composer#reachedHandoffs`): an attested arrival is a nested
family; one no producer this corpus attests is HELD at the value its row received, conjoined inside
the arm and named in `concrete[]` with the arm; one whose attested producer's exports do not lower is
FREE, named; only one its session minted no attach for refuses the arm. So an arm is never refused
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
decides it (STATE_PAIRING_FLIPPED); a location where no arm is that pairing (the one write the
reads saw has no arm) is a BLOCKING `UNSTATED_VALUE`: the run as it happened is no world of the
formula.

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
(`ContainerStateModel#unboxValue`, `ContainerSmtCodec.Term#nullness`). A value the lowering hands
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
may not have had there; each such map is named DIAGNOSTIC
`ASSOC_VIEW_UNORDERED:<why>:<map symbol (class), or the location its state was read from>@<session>`
(`SmtLowering#diagnostics`). A view walks the state each step of its chain stands for (`Host#chain`: a
read's joined version), so a map's `values()` a region iterates through a read of it is bounded by
that version's keys. A query reads a map's order only through `assoc_key_at`, `assoc_position_of`,
`assoc_view_key` or `assoc_view_position` (`ContainerStateModel.ORDER_READERS`); one that reaches
none gets maps whose puts and removals keep no order (`ContainerStateModel#unordered`, chosen by
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
cell (by seq) of the same clock of the same node that a session reading it also read, plus the time
that session's host read between the two; every seed reading anchors, whatever the formula names. A
cell no session can place refuses each path whose own terms name it, by name (`DECLARATION_MISSING`,
DIAGNOSTIC, in `refusedPaths`: no claim could say whether a witness moved it), beside
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
recording read it, else at the nearest cell both read, as a placement anchors; `Composer#clockBases`),
and an integral constant compared with an instant of that cell (the cell, or the cell plus or minus a
constant span) in that session's terms is lowered that much earlier (`SmtLowering#clockBases`,
`#onTimeline`); the recording's own constants stay. hdfs-11741 L1: dn1's first expiry check compared
each replay's startup keys, 9 to 11 minutes late on the recording's timeline, with the one dn1 clock.

**Valuations** (`valuations`): ordinal 0 = every declared root at its recorded value; then single
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
selected arms (`ComposedFamilies#texts`; a replay reads its clocks afresh).

**Cost.** COMPOSE reads the whole corpus -- every session (`SessionReader#readAll`) and every
obligation worker's answer with, once it published a session, its focus row (`ObligationDir#workersIn`),
8 directories at a time (`contract.ParallelReads`: on NFS a read is its latency) -- composes each
admitted path and decides (§9). Where each top-level command of the body ends, the path selector
guarding it and whether it asserts a refuted claim (its name closes it, so only its last 64
characters are read) are found once, as the composition is built (`Composition#commandEnds`,
`#commandGuards`, `#commandRefuted`); every path's question, the self-check's without its fatal arm
included (`#pathQuery`, `#withoutFatalArm`), is written from the one body by them, never by
searching it again: a search per command and path to the end of the body kept hdfs-adhoc-07's
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
   path is refuted for every question. When the composed formula is unsat (4), every path is asked
   once more with its fatal arm left out (`ClaimPolicy#contradictions`, `Disjunction#withoutFatalArms`,
   `Composition#withoutFatalArm`: its `path_fatal__` implication without phi), what its own run
   satisfied: a path unsat there (or undecided), or one that observed the fatal arm, contradicts its
   run -- `PATH_SELF_CONTRADICTORY` DIAGNOSTIC, and BLOCKING for the composition, since the UNSAT rests
   on it; refuted by phi alone everywhere, no root of the corpus turns any path to the fatal arm,
   which is the claim's own answer (b20h BlockTokenSecretManager-511, a40s
   BackupCmd-343: the null-checked read is pinned to the object the run read). Then every valuation is asked (4 at
   once; each question is written to its z3s from the one body the composition holds, never copied
   per ask or per arithmetic engine, `Composition#query`/`#pathQuery`, `Z3#ask`) for the path
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
   second each alone). Path by path, the paths are asked 8 at a time (`PATH_ASKS`, 16 z3
   processes), in their order, and answer in that order: the first sat path's answer (the asks
   after it stopped, their z3s killed), else undecided if any path was, else unsat with the union of
   the paths' cores. A path is asked in its own run first (`Disjunction#pathAsk`,
   `Composition#ownRun`): its own session's arm of each message the path received and each state
   read's observed writer, selectors only (never the values its handoffs carried, which are on its
   own clock), within 10 minutes at most; a model there is a model of the question, and only where
   its own run is refuted or undecided is the path asked free (hdfs-11741 L1: two fatal-observing
   paths sat in about 100 s in their own runs, undecided after 30 minutes free). A path unsat under some assertions is unsat under every set containing them,
   so it is not asked again there: its refutation answers, core and all, one asked without a core
   only an ask that wants none, unless it was asked under no assertion at all (the self-check: its
   core can name no pin). hdfs-11741 i1: 155 of 157 paths refute themselves, so every pinned re-ask
   of its witness asks two paths. A path is asked by `Composition#pathQuery`: the body without the
   commands another path's selector guards (`(assert (=> <selector> ...))`, vacuous once the
   partition forces that selector false), its own selector asserted; 90-98% of a body is guarded
   (hdfs-17899-bug2 r4: 1.7 of 93 MB shared; hdfs-11741 i1: 4.1 of 124 MB). The self-contradiction
   check and `mechanism`'s pinned re-asks of the selected path read the same text. Selectors are
   never asserted together: two contradict the partition.
   An ask is a verdict run, then a model run (sat) or a core run (unsat, where a core is wanted),
   each its own z3 process; only the core run tracks the named assertions (`smt.Z3#CORE_TRACKING`),
   since tracked z3 simplifies nothing across them and still searches a disjunct whose selector the
   rest forces false.
3. *As it happened* = every clock cell pinned to its reading plus `recordedPairings` (each path held to
   its own observed reads and received arrivals). `recordingDecides`: ordinal 0 is sat free and unsat
   as it happened. `clockDriven`: it is also unsat with the clocks alone pinned; then the witness keeps
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
4. The claim, first match. First of all, a seed replay that observed the fatal at the declared
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
     Within the rank, a witness that is its selected session's own run is claimed first
     (`ClaimPolicy.Reading#ownRun`: the selected path observed the fatal, every arm the model takes on
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
     every disjunct of the seed's session unsat at the recorded roots: its mechanism, if any;
   - else THE FORMULA DECIDES (`ClaimPolicy#closed`): the composed formula is asked whole, every
     root free over its domain -- the very text exported as `final/candidate.smt2` -- and its answer
     is the verdict; the enumeration of single and pair moves above only picks a witness's
     valuation. Unsat: `NO_SUPPORTED_WITNESS` (UNSAT_CLOSED). Undecided within the budget: BLOCKING
     (a defect, never a refutation). Sat: `FORMULA_SAT` at the first enumerated witness a replay can
     plant, else at the formula's own model (`Composition#modelValuation`: each declared root at the
     model's value), refined as a named claim is (`leastClocks`, `withMargin`), composer
     imprecision until CONFIRM says otherwise, planted and judged like any claim, a refutation
     excluded before the claim is decided again; an enumerated witness that is
     the run as recorded (the seed's path, no root moved, no clock jumped, no arm re-paired) is
     skipped, and a corpus a BLOCKING gap already withholds a verdict from names no witness; a sat
     model selecting no path,
     or one only a configuration whose plant leaves reads at the recording's value satisfies
     (`UNPRODUCIBLE_ANSWER`), is BLOCKING.
5. `mechanism`, narrowest first: pinning the path's observed reads makes it unsat →
   `STATE_PAIRING_FLIPPED`; its observed anchor arrivals → `MESSAGE_PAIRING_FLIPPED`; a moved root →
   `MARKER_FLIPPED` (any declared root kind); `clockDriven` → `CLOCK_SKEW`.
6. In the moved-root rule without `recordingDecides` and in the no-root-moved rule, the witness is
   re-asked with each clock jump a margin (one minute in its ticks) further the same way (`withMargin`:
   all at once, else each in seq order, kept where still sat). `movedRoots` = the valuation's moved
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

`ComposeMain.campaignClaim` maps it: the formula decides, SAT or UNSAT, and a blocking gap is a
defect of the run or the engine that leaves no verdict: any BLOCKING claim gap → `RUN_DEFECT`; else a
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
an open link leaves no verdict, `RUN_DEFECT` with `openChain` (EMIT: `WITNESS_CHAIN_OPEN` for a
SAT, `UNSAT_CHAIN_OPEN` for an UNSAT). A SAT's other paths' open links are stated, never gating
(`unboundOffWitness`, cone.json's too). EXPLORE closes a witness's chain before it ends (§7.9); an
UNSAT's paths are closed by the exploration's own growth, which plans each demanded producer an
admitted session exposes (§7.2, §7.8), so a link still open at the fixed point is one growing could
not close. EMIT publishes
`SAT_CANDIDATE` as CONFIRM left it (`SAT_UNCONFIRMED` when the confirmation refutes it, `RUN_DEFECT`
when it published no verdict: a `CONFIRM_NO_VERDICT` defect), and an `UNSAT_CLOSED`
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

- **The run as recorded**: a claim whose selected session is the seed's, that moves no root and no
  clock, every selected arm the seed's own delivery and every chosen write the one its read saw,
  is refuted by name (`CONFIRM refutes:`, `refutes` true): it is no counterfactual, whatever a run of
  it observes (owner 2026-10-04: a claim moving no root is never a finding), and the campaign
  excludes it.
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
  overlaid with the model (`ConfirmMain.Moved`): every moved root, by root id, at the recording's
  mint occurrence -- any other root as its value, a clock as its skew off the reading the
  composition anchored its cell to (the manifest's `roots`) -- and, on every clock cell the
  composition anchors, the model's jumps alone: the session's own skews there are dropped, since
  the model runs those cells on from the jump before them. A moved root the recording mints
  nowhere, or a moved clock the composition anchors nowhere, refuses the confirmation by name. The
  world's pairings are held by the rows its replay was held to (`ConfirmMain#holding`, the reader's
  occurrence a block; a pairing the session states no read or write of refuses, `PAIRING_UNSTATED`).
  The focus row focuses the anchor
  with `flip: null`, the anchor as declared target, no inherited flips. The schedule is written
  unheld (`SchedulePrefix.write(..., held=false)`: every event is suffix; only WAKEs wait for what
  they followed, and when the selected session was cut at its witness, a WAKE it never made waits
  for its whole order). `expected_edges.jsonl`: `WIRE` per consumer of each selected message arm (producer
  as that arm's session paired it, and `value`, the arm's `texts` entry for a delivery into the
  anchor), `STATE` per read of the anchor's join closure (each reached
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
  `ORDER` rows (the writer's activation exits before the reader's read: the order holds the last
  activation entry before the read on its thread, the last call the reader's activation made before
  it, else that activation's own (`ConfirmMain.StateClosure#holdBefore`); an event in its
  occurrence's outermost activation -- a loop body's, standing on the loop's method, which spans
  every turn -- is held at the occurrence's opening and waited for until its close
  (`StateClosure#exit`, `#outermost`), which the session ran at the occurrence's last recorded
  event, so a writer it ran before that is a reordered occurrence (`StateClosure#closing`); where
  that activation runs
  as claimed work on a consumer thread (`ActivationRow#claimed`: a server pipeline applying one
  request after another, the writer's among them, would deadlock held), the entry of the send that
  started it, its anchor's producer followed up the chain while that send is claimed work too
  (`Confirmation#submitter`; none outside one refuses the confirmation, `ORDER_UNHELD`); every other
  writer of the location the held write is of before the writer or after the reader, held alike, and
  for an INITIAL the model chose every writer of the location after the reader), `MARKER`
  per planted marker, `ANCHOR`. Endpoints and activations are named as every delivery of their
  stored message is (`Confirmation#id`, `OccurrenceAddress#anyDelivery`: a watcher's second
  delivery of one version, `KIND.n`, is the store's timing, so a run that took one delivery where
  the recording took two still takes the model's edges). A `referentStates` row with no reader (a query asked outside every container
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
  and it holds no order), and holds each `ORDER` activation's
  entry until the named activations exit (`causynth.confirm.order.timeout.ms`, 300 s; a stall is a
  mismatch); every difference is a `CONFIRM_MISMATCH` gap in the session. `MARKER` and `ANCHOR` rows
  are not read by the runtime. A CONFIRM run (`FocusedReplay.confirming`: its obligation flips
  nothing), or a replay whose world plants pairings (`FocusedReplay.pairs`), whose
  `expected_edges.jsonl` is missing or unreadable compares nothing and files one `EDGES:` mismatch
  at the close, so it confirms nothing and the obligation is `PAIRING_UNTAKEN`. One read is held to
  one writer: two STATE rows naming two are refused by `ConfirmMain` (`STATE_CONFLICT`) and, read at
  runtime, compare nothing.
- Decision (`ConfirmMain --claim --output <worker> --sessions <dir>`, `ConfirmMain#decide`, which
  prints `final/confirm.json`), conditions in order, the first that fails named as the reason: the
  replay's verdict is `ADMITTED`; its session directory exists and its `gaps.jsonl` and
  `targets.jsonl` are readable (a session that did not publish them answers nothing); no gap is a
  `CONFIRM_MISMATCH`; and a target row whose occurrence id is the claim's anchor's (the id only
  the Java address computes) has `reachedAnchor` and `observedFatal` — a fatal at another
  occurrence of the target site does not confirm. Only the last refutes, and only where the run
  ran the model (`ConfirmMain#unplanted`: every root the claim moved minted at the model's value,
  a clock's cell minted, no `ASSIGNMENT_UNPLANTED`); a `CONFIRM_MISMATCH` (the run took an edge the
  model did not choose) or a run without the model's plant did not run it. A ConfirmMain that
  exits nonzero is "unconfirmed" with its log named.

`final/confirm.json`: `{schemaVersion 1, kind: CONFIRMATION, confirmed, refutes, reason,
sessionId}`, the same shape for a refusal, `realized.json` and the decision. `refutes` says the
model is refuted: the replay ran it and disagreed (no fatal at the anchor, the model planted), or
ConfirmMain refuted it by name (`CONFIRM refutes:`, the run as recorded). A refusal (`CONFIRM
refused:`), a mismatch, a run without the model's plant, a replay that was not ADMITTED,
published no readable session or no verdict, or a decision that failed, refutes nothing: the model
is REFUSED (`campaign_refuse`, one row of `<iteration>/refused_models.jsonl`, `result.json`
`refusedModels`). An ORDER the replay cannot hold within `ORDER_TIMEOUT_MS` is such a mismatch,
never a refutation: a timeout cannot tell a slow run from an order the program forbids
(hdfs-adhoc-10 SL1: a re-paired writer arm ordered jn0's `journal()` before the `startLogSegment`
its client waits for). A refused model is excluded from every later composition as a refuted one
is (below), so the next claim follows; no witness attempt confirms it again, and the final CONFIRM
of a composition that repeated it takes its row instead of a replay (both matched as the
composition matches a model, `campaign_model_key`). A final claim of its own left with no verdict
is `RUN_DEFECT` (`CONFIRM_NO_VERDICT`); one CONFIRM refuted is `SAT_UNCONFIRMED`, not accepted, the
models refused before it published as `refusedModels` -- each excluded, none a verdict -- and an
UNSAT that follows them stands only where it rests on none (above).

**A claim CONFIRM did not confirm is followed by the next.** A refuted claim (`campaign_refute`)
is one row of `<iteration>/refuted_claims.jsonl`, a refused model one of `refused_models.jsonl`:
its `model` (`campaign_claim_model`, off `claim.json`: the
finding kind, the selected path, the arm selectors it chose there, the valuation, and the claim's
moved roots, a clock by its cell's symbol at the model's instant), where it was `claimed`, and the
confirmation's `reason`. Every later composition of the iteration excludes each
(`Composer#refutations`, `compose.Refutations`): `refuted_claim__k` (`refused_claim__k` for a
refused model) asserts that the path's
selector, those arms (an arm's selector is `<kind>__<path ordinal>__<digest>`, taken at the path's
ordinal in this query), the valuation's non-clock roots (named as the valuations name them,
`Corpus#anyRoot`) and the claim's clock region are not all true at once -- a region, not an
instant: each clock cell the claim moved jumped the way it did, by any amount, and every other
cell of the query runs on from the cell before it (`Composer#clockStep`, the spelling of a
witness's run-on pins too); an instant alone excluded one point, and the next model sat a tick
beside it --, a
DIAGNOSTIC `CLAIM_REFUTED` (`CLAIM_REFUSED`) gap names it, and a model whose path or arm the query no
longer composes is not stated. An exclusion is a region, so an UNSAT may rest on one: whenever one is
asserted, the free-formula ask and the self-check ask for the unsat core (a path whose self-check
core names one does not contradict its run, `Disjunction#refutedBySelfCheck`); an `UNSAT_CLOSED`
whose core names a `refuted_claim__k` publishes each as `restsOnRefutations` (its path, moved
roots and reason; `Composition#restsOn`, `ComposeMain#campaignClaim`, EMIT, `report.py`, `triage.py`),
and an UNSAT whose core names a `refused_claim__k`, or whose core is unknown while it excludes one, is
`RUN_DEFECT` (`unsatBesideRefused`, EMIT's defect `UNSAT_BESIDE_REFUSED`): no run decided that model.
A core is known only where its own run said unsat (`Z3.Answer#coreKnown`; a core run that timed out,
found no room or answered unknown names none, which is not the empty core), a disjunction's only
where every path's is, and a path's refutation answers a core-wanting ask only with a known one.
During EXPLORE a witness attempt CONFIRM did not confirm lets the exploration go on (§7.9); after
it, the final stages go on to the next claim (`campaign_next_claim`): while the claim is a
`SAT_CANDIDATE` CONFIRM did not confirm whose model is recorded once in the two files together
(matched by `campaign_model_key`: an arm by its kind and digest, its path ordinal being one
composition's; not one the composition was told to exclude already), the campaign's budget has
room for its reserve (`campaign_claim_room`) and fewer than `campaign_max_claims` (8) claims were
decided again (past it the last claim is published, the bound named in the log), its artifacts
move to `final/refuted/NNNN/` and COMPOSE, SOLVE, DECIDE and CONFIRM run again. The
final CONFIRM of the model the exploration's witness attempt confirmed (the same model,
`campaign_claim_model`: kind, path, arms, valuation and moved roots) takes that attempt's
`confirm.json` and runs no replay. EMIT publishes every refuted claim (`result.json`
`refutedClaims`; `tools/adhoc/triage.py` classes a case with any and no confirmed witness
REFUTED, `report.py` lists them, `tools/analysis/timeline.py` times every CONFIRM replay).

## 10b. REPRODUCE: the confirmed world, natively

After EMIT -- the verdict is published first, and nothing REPRODUCE does moves it -- a confirmed
`SAT_CANDIDATE` is run again on the stock JDK, in the recording weave, with nothing of the concolic
VM (`campaign_reproduce`). `ConfirmMain --iteration --claim --manifest --static-scope-map --plant
<file>` writes the plant from what CONFIRM itself plants and holds (`ConfirmMain.Witness`, the one
reading of the claim both make: the selected session's world under the model's moved roots, and
the edges the model chose), each row numbered (`row`):
- a `ROOT` per root the world assigns, naming the occurrence id it is minted at: a FAULT marker
  `{category FAULT, rootId, occurrence, siteId: <the call site its plan input action names>,
  value: true|false}`, a tree hook's root `{category HOOK, rootId, occurrence, value}`;
- CONFIRM's own `ORDER` rows (`{before, after}`, §10: the join closure's at the locations the fatal
  rests on, and those holding the pairings the world plants), each pair once;
- one `TARGET` per guard of the scope map's TARGET_SITE rows, `{occurrence: <the claim's anchor
  id>, siteId: <guard>, value: <its fatal arm>}`.

Refused, with no native run (`reproduce.json` `runs` 0 and the refusal as `reason`):
- by CONFIRM's own reading of the claim (`CONFIRM refused:`, §10): a valuation that selects no
  path, an unparseable anchor, a manifest stating no selector, `restsOn` or `cutoff` for the path,
  a moved root the recording mints nowhere or a moved clock no reading anchors, and the edges'
  refusals (`STATE_CONFLICT`, `PAIRING_UNSTATED`, a selected arm whose consumer its session states
  no attach for);
- `NATIVE_PLANT_UNSUPPORTED`: a world that skews a clock or answers an attach (the recording weave
  reads no clock through the model and answers no attach); a root of another category than FAULT
  or HOOK -- a configuration (the recording weave has neither the configuration-read nor the
  getter-call mint), an unwoven accessor's read, a clock; a FAULT root its plan input calls at no
  site or at several, or assigned other than true or false; a root with no mint occurrence; a world
  that plants no root and holds no order (it would repeat the recording); a scope map that states
  no fatal arm;
- a recording that measured no peak resident memory to charge a run with.

`reproduce_runs` (10) runs go out at once, each a head step (§7.7, `campaign_reproduce_one`)
charged the recording's peak resident memory (`execute.sh` states it as `workload_rss_mb` in the
trace directory, and holds each run to it as to any charge) wherever there is room until it
returns, naming the host it ran on (`<run>/host.txt`), and bounded by `reproduce_time_factor` (3)
times the recording's own workload, at least `reproduce_min_s` (300: a short recording says
little of how long ten runs at once on a busy cluster take -- hdfs-17960's 8 s recording gave 24 s,
and all ten runs of round NP1 were cut before their window opened; hdfs-17897's 9 s recording, ten
runs of 119-187 s in NP7, each at the anchor; `campaign_reproduce_bound`). A
run (`campaign_reproduce_run`) runs the recording command with `-Dcausynth.plant` (`execute.sh`,
`CAUSYNTH_PLANT`); inside the window:
- `Debug.makeSymbolicBoolean` at a FAULT row's call site answers its value when an enclosing region
  occurrence (`CausynthTraceRecorder#enclosingOccurrences`) has the row's own id
  (`RecordingPlant#marker`);
- the tree's `CausynthSymbolicSource.symbolize` of a HOOK row's root writes its value into the field
  the hook names (`RootMint#configuredSource` -> `RecordingPlant#hook`, the replay's own
  `RootMint#writeModeledField`) under any enclosing occurrence the confirmation focuses -- the
  anchor or the mint occurrence of any root of the plant -- as a replay's mint plants under a focused
  occurrence (`RootMint#focusedRootValue`); a write that fails is a `PLANT_UNWRITTEN` row;
- `runtime.Confirmation` holds the ORDER rows at `Identity`'s frame hooks as in a CONFIRM run (it
  reads the plant in a planted run), each at most half the run's bound
  (`causynth.confirm.order.timeout.ms`, `CAUSYNTH_ORDER_TIMEOUT_MS`), each row stating what it came
  to: held, waited for (`PLANT_HOLDING`, for a before-activation that had not exited), or not held
  in time (`PLANT_UNHELD`) -- what the run states, never a refutation;
- every row applied is a `PLANT_APPLIED` trace row naming its number; a recorded branch at a TARGET
  row's guard that takes its fatal arm is a `PLANT_FATAL` row stating whether an enclosing
  occurrence is the anchor's -- at the anchor the run ends (`JUnitMethodRunner.exit`, as a focused
  replay ends at its witness), its one question answered (`runtime.RecordingPlant`).

A planted run is not the recording's world, so the workload's checks of that world are off in it
as in a replay (`CausynthTraceRecorder.replaying()` is true under `causynth.plant`). Each run states
its answer, whatever the workload's exit, as `run-<n>/answer.json` `{exit, rows, applied, unapplied,
planted, rootsPlanted, fatal, atAnchor, reproduced}`, read off its trace's plant rows against the
plant: the rows to apply (ROOT and ORDER), how many it applied, each it did not with why
(`UNHELD`, `UNWRITTEN`, `HOLDING` at the run's end, `NOT_REACHED`), whether it applied every row
and every ROOT row, whether it took the fatal arm and at the anchor, and whether it **reproduced**:
the fatal arm at the claim's anchor with every ROOT row applied. A run that did not plant the
model's roots and reaches the fatal all the same is the program's own race, never a reproduction.
`final/reproduce.json`: `{schemaVersion 1, kind: REPRODUCTION, runs, planted, fatal, atAnchor,
reproduced, unheld, holding, reason}` -- runs that applied the whole plant, took the fatal arm,
took it at the anchor (planted or not), reproduced, could not hold an ORDER in time, still held one
when they ended, and the runs that stated no answer as `reason`. A native run holds the model's
order, not the recording's, so the planted occurrence may not recur: the share of runs that
reproduced ranks a finding (`tools/adhoc/findings.py`, which reads `reproduce.json` beside
`result.json`) and never refutes it. Then the campaign exits by its verdict
(`campaign_exit_verdict`).

## 11. EMIT

1. `campaign_verify_frozen_inputs` (§1).
2. `final/gaps.json` (`campaign_write_gaps`), one row per distinct (stage, source, code, subject,
   detail), class as the row states it (none stated = BLOCKING): static communication gaps and the
   runtime plan's `gaps` as PLAN; every `gaps.jsonl` under the iteration directory — a path matching
   `*/sessions/*/gaps.jsonl` as REPLAY (a withdrawn exposing session under `before-*/sessions/`
   included), any other under `obligations-*/` as EXPLORE (a session withdrawn to
   `timed-out-sessions/` or `refused-sessions/` included), anywhere else fails EMIT; `campaign_gaps.jsonl` rows at their
   stated stage, else IMPORT; the composer's refusals (BLOCKING), `gaps` and claim gaps as COMPOSE. Published as
   `gaps` (BLOCKING), `telemetryGaps` (DIAGNOSTIC), `gapCount`, `byStage`, `byCode`.
3. `final/result.json`: `claim` = the campaign claim; a `SAT_CANDIDATE` whose confirmation is not
   `confirmed` is `SAT_UNCONFIRMED` when the confirmation `refutes` it, else `RUN_DEFECT` with a
   `CONFIRM_NO_VERDICT` row in `defects[]` (the confirmation is copied in);
   `refutedClaims`, every row of `refuted_claims.jsonl` (§10), whatever the claim;
   `restsOnRefutations` (the refuted and refused models an UNSAT's core names, and each world a
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
   bound in their subject), `region_path_max_tasks` (the last round's
   `truncated`), `schedule_max_jobs` (the schedule index's `closureCut`), `open_arm_max_refuted_worlds`
   (an open arm the last round left BOUNDED, §7.1) and `campaign_max_claims`
   (a refuted claim published at it); a round's `max-flips-per-path` is none (the next round asks
   the rest), nor is the time budget (`EXPLORATION_CUT`). `report.py` puts it in the row's note and a
   `## Bounded` section, `triage.py` in its `bounded` column and `BOUNDED=` count,
   `tools/rounds/round-verify.sh` as `BOUNDED:<keys>` and a per-round count.
4. `final/run-manifest.json`: provenance, iteration manifests, the path, size and sha256 of each
   required final artifact (`candidate.smt2`, `candidate_composition_manifest.json`, `gaps.json`,
   `result.json`; a missing or empty one fails EMIT), stage wall times, session rows and bytes.
5. After REPRODUCE (§10b), `campaign_exit_verdict`: exit 2 when the claim is not
   `SAT_CANDIDATE`/`UNSAT_CLOSED`; exit 3 when BLOCKING gaps remain; else 0.

## 12. Acceptance: `experiments/accept/`

`accept.sh` builds the jar, then per case (one at a time; `CASES`, default the nine HDFS cases of
`ACCEPT_ALL_CASES`; `EXPECTED_MECHANISM` also names solr-18413 and solr-18406, both `CLOCK_SKEW`)
runs `lib/run.sh <case> validate` and `campaign` under `CASE_TIMEOUT_SECONDS`, then
`probe.sh`, `cone.py` and `report.py`, and writes `summary.tsv`. `report.py` passes a case when all
hold, read off `final/result.json`, `gaps.json` and `cone.json`:

- `claim` is `SAT_CANDIDATE` (so CONFIRM agreed) and `confirmation.confirmed` is true, `finalStatus`
  is `FINAL_READY`, `accepted` is true, and `gaps.json` names no BLOCKING gap;
- `findingKind` is one of the four mechanisms and is the case's entry in `EXPECTED_MECHANISM` (a case
  the table does not name cannot pass); `polarityDecides` is true;
- `movedRoots` is non-empty and `valuationOrdinal ≥ 1` unless `CLOCK_SKEW`; an expected `root`/`value`
  must be moved to that value; for the RPC-failure entries (`fault: org.apache.hadoop.ipc.Client`,
  `clocks: False`) a MARKER moved to true whose declared site (the plan's `EXPLICIT_SYMBOLIC_FAULT`
  input action) is in that class, and no CLOCK cell moved;
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
`claim` is `SAT_UNCONFIRMED` and the confirmation `refutes` the model (the confirmation's reason is
the row's reason; one that published no verdict is a `RUN_DEFECT`), `UNSAT` when it is
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
  `gaps.jsonl`. A pool or a head that seems stalled logs `waiting for room: …` or `waiting for
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
- `iteration-0000/obligation_results.jsonl` and each `obligations-NNNN/<id>/`: the verdict's
  `detail`, `obligation_query.smt2` (the query as asked, with its `check-sat` and `get-value`; it
  re-runs by hand in z3), `focused_task.jsonl` (the world), `replay.log`, `stdout.log`/`stderr.log`.
  An obligation id holds no session id (§7.3), so it repeats across runs whose replays reproduce
  the same addresses and input shapes: an earlier run's directory is a baseline.
- `sessions/<id>/`: `targets.jsonl` (`observedFatal`, `reachedAnchor`), `decisions.jsonl`,
  `roots.jsonl`, `schedule.jsonl`.
- `final/claim.json` (valuations with status, unsat core, selected path, session and arms),
  `candidate_composition_manifest.json`, `compose.log`, `confirm.json`, `confirm/confirm.log`.
- A schedule divergence is read by aligning: take the rows with a `kind` of the prefix the replay
  was held to (`recorded_schedule.jsonl`, or the worker's `schedule_prefix.jsonl`) and of the
  session's `schedule.jsonl`, compare `(kind, context, site)` position by position to the first
  mismatch, then count how many events of the expected key the replay made at all (none: an event
  the replay never makes; as many as the prefix: it came late). The `{mark, at}` rows of both files
  say where each occurrence opened; a SEND's `endpoint` joins the recording's `EXCHANGE_SEND` rows
  in `runtime/runtime_trace.jsonl`.
