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
| SEED | `campaign_seed`; `GraphCheckerMain`, `plan.ScopeGrowth`, `plan.LineageScan`, `runtime.CausynthTraceRecorder` (a batch: `campaign_batch_seed`, §2b) | static artifacts, the recording, `seed-skeletons/` | the workload exits nonzero; an artifact is missing or stale |
| PLAN | `campaign_plan`; `plan.ConcolicScheduler` (a batch: per target, `campaign_batch_plan`) | `iteration-0000/execution_task_plan.jsonl`, `runtime_workflow_schedule_index.json` | more tasks than `schedule_max_jobs`; the index does not commit the frozen plan; no target |
| UNION (a batch) | `campaign_batch_union`; `plan.PlanUnion` | `groups/groups.json`, `groups/group-<n>/execution_task_plan.jsonl` | `PlanUnion` exits nonzero |
| INSTRUMENT | `campaign_instrument`; `GraphCheckerMain`, `causynth.VerifyWovenClasses` | `iteration-0000/instrumented-classes/` | no class woven; a woven class does not verify |
| REPLAY | `campaign_session_replay`; the adapter (`runtime.*` in the workload JVM) | `iteration-0000/sessions/<seed>/` | killed on its bound (`seed_replay_time_factor`); no activation; no target row of the target method |
| IMPORT | `campaign_import_session`; `contract.ImportGateMain` | `session_census.jsonl`, `import_gate.json`, `campaign_gaps.jsonl` | a session file is missing; a BLOCKING row invariant |
| EXPLORE | `campaign_explore`, `campaign_grow`; `explore.ExploreMain`, `explore.ObligationSolverMain`, `plan.ExposedRegionPlanMain` | `obligations-NNNN/`, `obligation_results.jsonl`, focused sessions | the planner fails; an obligation does not finish; a replay states no verdict; a wave's BLOCKING row invariant (as IMPORT) |
| — | `campaign_publish_iteration_manifest` | `iteration_manifest.json` | — |
| COMPOSE | `campaign_compose`; `compose.ComposeMain` | `final/candidate.smt2`, `candidate_composition_manifest.json`, `claim.json` | ComposeMain exits nonzero (every refusal is a claim, not an exit) |
| SOLVE, DECIDE | `campaign_solve`, `campaign_decide` (read the manifest) | log lines | the manifest states no solver verdict or no valuation rows |
| CONFIRM | `campaign_confirm`; `explore.ConfirmMain`, one replay, `ConfirmMain --sessions` (the decision) | `final/confirm/`, `final/confirm.json` | never (a failure is "unconfirmed") |
| REPRODUCE | `campaign_reproduce`; `explore.ConfirmMain --plant`, `reproduce_runs` recordings with the plant, `runtime.CausynthTraceRecorder` | `final/reproduce/`, `final/reproduce.json` | never (it ranks a finding, and moves no claim) |
| EMIT | `campaign_emit` | `final/gaps.json`, `result.json`, `run-manifest.json` | a frozen input changed; exit 2 = no `SAT_CANDIDATE`/`UNSAT_CLOSED`, exit 3 = BLOCKING gaps |

There is one iteration (`iteration-0000`); what a replay learns past the recording is taken up by GROW
inside EXPLORE. `campaign_stop_after=IMPORT` returns successfully after IMPORT (a measurement run).
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
| `region_path_max_waves`* (12), `region_path_max_tasks`, `region_path_max_paths_per_region`, `region_path_max_flips_per_path`, `region_path_max_world_depth`, `region_path_stop_at_fatal` | EXPLORE's bounds (§7.4, §7.9) and the witness stop (§7.1) |
| `compose_max_valuations`* (16) | the valuations COMPOSE enumerates |
| `concolic_worker_count`* (8), `campaign_worker_hosts`, `obligation_memory_mb`*, `engine_memory_mb` | slots per host, the hosts, one obligation's memory at the host gate, the head JVMs' heap |
| `campaign_stop_after` | empty, or `IMPORT` |
| `causynth_static_root`, `record_timeout_s`* (300), `reproduce_runs`* (10) | the build's static slices a batch campaign or a pre-screen reads (§2b); the wall clock of a pre-screen's recording and of each native reproduction run; how many of those (§10b) |

Defaults in parentheses; `solver_timeout_ms`, `schedule_max_jobs` and `obligation_memory_mb` have
none.

## 1. PREFLIGHT, FREEZE_TOOL, SETUP, FREEZE

- PREFLIGHT: `validate_config`, a replay command is required, `jq` and `sha256sum` exist, and every
  remote host of `campaign_worker_hosts` answers `ssh` in batch mode and sees `run_engine.sh` on the
  shared home.
- FREEZE_TOOL copies the jar into `frozen-inputs/`, digesting before, after and the copy; a jar that
  changed while it was copied fails the stage. Every later stage, and every remote worker, runs the
  frozen copy (`--run-obligation` refuses a jar whose sha256 is not the frozen one).
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
   `communication_gaps.jsonl.gz`, `static_scope_map.jsonl`, `scope_frontier.jsonl`
   (`causynth.CausynthArtifactWriter`). While `causynth_scope_growth_budget > 0` and
   `causynth_lineage_roots` is set, `plan.ScopeGrowth` adds classes where the slice stops at the scope
   into `scope-classes/` and the pass runs again, until it adds nothing ([SYMBOL-SCOPE.md](SYMBOL-SCOPE.md)).
   The target spec holds one line, `exception_target: <name> <binary class name> <source line>
   [<thrown type>]`; `causynth.ExceptionTargetLineResolver` finds the one `throw new` javac compiled at
   that line of the class or a class nested in it (a lambda body, an anonymous class), by the
   LineNumberTable of the analysis inputs, and refuses `TARGET_LINE_UNRESOLVED` or
   `TARGET_LINE_AMBIGUOUS` (state the type) otherwise. Its identity is the method, the thrown type and
   the `NEW`'s ordinal among the method's `NEW`s of that type, which the analyzer matches on Jimple.
   A spec of more than one line is refused (`MULTI_TARGET_UNSUPPORTED`).
   The scope map is [SYMBOL-SCOPE.md §3](SYMBOL-SCOPE.md); its `TARGET_SITE` rows state the
   target's `guards` with their fatal arms, the helper branch deciding a guard on a helper's
   returned 0/1 (`guardDeciders`, `causynth.BooleanReturns`) and the `chain` of guards before them;
   `StaticScopeMap.Site.pathSites` = guards + chain + the chain's deciders. Loop-bound
   rows are keyed by Jimple unit id (`<method signature>#uNN`, field `loopSiteId`); the ids the
   pass uses are the skeletons' `loopControlSiteIds`, and any edit to an instrumented method moves
   the ids after it, so a case's loop-bound file is re-read from the skeletons after a tree edit.
2. `do_workload`: one weave in trace mode `region-state` (lineage classes from `plan.LineageScan`
   included), then the workload itself (`workload_command`; a nonzero exit fails SEED; its wall
   time in seconds is kept as `campaign_recorded_workload_s`, the base of the seed replay's
   bound, §5; the recording itself runs under no bound), then
   `runtime.CausynthTraceRecorder` aggregates the trace into `runtime/concolic_region_plan.jsonl`
   (the runtime region plan) and `runtime/region_skeletons.jsonl`; the recording's
   `runtime/schedule.jsonl` sits beside them.
3. Both skeleton views are copied to `<campaign root>/seed-skeletons/`.

### 2b. A batch campaign: one recording for several targets

A campaign given `causynth_static_root` (an ad-hoc sweep's batch case, `tools/adhoc/cover.py
cases`; ADHOC-INFRA WP3) runs no static pass of its own. Its spec names k ≥ 1 targets, each sliced
by the build already (`<static root>/<name>/`, `tools/adhoc/slice.sh`). After FREEZE,
`campaign_batch`:

1. SEED (`campaign_batch_seed` → `campaign_record_batch`, the same code as the pre-screen's `record`):
   each target's slice is frozen into `targets/<name>/` (candidate graph, scope map, frontier,
   communication gaps, its spec line as `target.yaml`); ONE recording is woven with every target's
   skeletons merged by root (the weave opens one region per root, the first the merged file names
   there; two targets may root one method under two authorities, hence two region ids) and every
   target's grown scope united (`campaign_union_static`), its workload run as SEED's (a nonzero exit
   fails SEED), and each target aggregated on its own slice into `targets/<name>/runtime/`, over
   its view of the merged skeletons (`campaign_region_view`, `view_region_skeletons.jsonl.gz`):
   every region the recording opened, so that a region of this target entered inside another
   target's -- folded into that occurrence -- is found there, with this target's selection at the
   roots it plans and another target's exception context as state, so that no other target's
   failure context is taken for its own.
   `runtime/record-summary.json` states each target's state (`ACTIVATED` or the refusal). Each
   target directory links the batch's merged skeletons, grown scope, lineage classes, recording
   weave and recorded schedule, so every weave and replay of every target stands on the recording's
   frames.
2. PLAN, per `ACTIVATED` target (`campaign_batch_plan`, a subshell logging to
   `targets/<name>/campaign.log`): its `causynth_output_dir` is `targets/<name>/` (so it, and every
   peer of its waves, derives its slice, scope map and region plan there), its campaign root
   `targets/<name>/schedule/`, its spec its one line, its region plan's aggregation slice the one
   REPRODUCE reuses (`campaign_target_slice`), `first` resolved per target; PLAN is the ordinary
   stage (`campaign_plan`).
3. UNION (`campaign_batch_union`, `plan.PlanUnion`): the planned targets' plans grouped, each
   target joining the first group it agrees with -- every occurrence both plan is the same task
   there (one task id: occurrence, region content, ports and, for a target's own reach, its
   target branch), every tracked site both observe the same observation. The plans stand on one
   recording and one weave, so the tasks they share are one task; two targets' different tasks at
   one occurrence (both reaching their own target there) would need one task carrying several
   target branches, which the runtime does not have, so such targets replay apart. A group's union
   plan is every task once, every task observing every site any target observes, under the union's
   own replay group: `groups/group-<n>/execution_task_plan.jsonl`, `groups/groups.json`.
4. Per group, all groups at once (`campaign_batch_group`, logging to `groups/group-<n>.log`; each
   engine JVM and replay charged to the head's host as any head's): INSTRUMENT, REPLAY and
   IMPORT once, in `groups/group-<n>/`, under the union of its targets' scope maps (the replay's
   guarded stores, and its target coverage: any target). A target the seed replay published no
   target row of fails as a solo REPLAY does, in its own log (`campaign_target_reached`); a seed
   that ended before IMPORT ends every target of its group, its failure copied into each one's log.
5. Every target its group's seed reached runs its own campaign from EXPLORE on, all at once, each in
   a subshell (`campaign_batch_target`): its iteration takes the group's union plan (a copy: GROW
   appends to it), woven classes and seed session (hard links: GROW re-weaves its own), census and
   import gate, and reads its own PLAN again (`campaign_plan_read`); EXPLORE .. EMIT are the
   ordinary stages (`campaign_iteration_explore`). `campaign_stop_after=IMPORT` stops the batch after
   the groups' IMPORT.
6. The batch fails when SEED does, when the recording activated no target, or when a target that
   was planned ends before EMIT -- its PLAN, its group's seed, or its own stages (EMIT's exits 2 and
   3 are verdicts); each target's claim is its own `targets/<name>/schedule/final/result.json`.

What is shared is the static pass (the build's), the recording weave, the recording and its
aggregation, and per group the seed's weave, replay and import; each target plans and explores on
its own. A target's EXPLORE reads the union's seed session, whose tasks include the other targets':
its closure is rooted at its own declared anchor (§7.1), so another target's task is taken up only
where it writes what that anchor depends on.

## 3. PLAN

`campaign_plan` freezes the region plan as `iteration-0000/concolic_region_plan.jsonl`, copies the
recording's schedule to `recorded_schedule.jsonl`, and runs `plan.ConcolicScheduler`
(`scheduleTargetFirst`). `RuntimeWorkflowDiscovery.workflow` schedules the declared target first, then
every other occurrence the plan states is replayable, in recorded order; no slice is applied here
(the closure is EXPLORE's). The declaration is `declared_target_occurrence`: a resolved address, a
selector (`node#epochN/region/REGION.x[@api]#k`, the k-th match in recorded order), or `first`, which
PLAN resolves against this recording and the shell then uses as the address. More tasks than
`schedule_max_jobs` fail the stage. Outputs: `execution_task_plan.jsonl` (every row stamped with one
`replayGroupId` = `REPLAY.GROUP.<sha256 of the rows>`) and `runtime_workflow_schedule_index.json`
(members TARGET/DEPENDENCY; the shell checks it commits the frozen region plan's sha256 and size and
decodes the membership once into `campaign_member_rows`). The seed replay's plan and every worker's
plan are hard links of the one task plan file, so a row GROW appends reaches all of them.

## 4. INSTRUMENT

`campaign_instrument` clears `iteration-0000/instrumented-classes/` and runs `do_analyze` with
`CAUSYNTH_CONCOLIC_TASK_PLAN`/`_TASK_ID` set to the whole plan: one union weave of every task. The
tree must hold a class file, and `causynth.VerifyWovenClasses` must verify every woven class against
the replay's class path, or the stage fails naming the class. GROW re-runs this stage's function.

## 5. REPLAY

`campaign_replay` runs `concolic_replay_command` (the adapter) with the plan, task ids, class tree,
sessions directory, worker directory and `CAUSYNTH_SCHEDULE_PREFIX`; the seed replay is held to the
recording's schedule (`recorded_schedule.jsonl`). A replay publishes one session under
`iteration-0000/sessions/<sessionId>/` (layout in [CONTRACT-SPEC.md §2](CONTRACT-SPEC.md)); with no
focus row its `manifest.json` states role `SEED`. The seed replay runs under a wall clock of
`seed_replay_time_factor` × `campaign_recorded_workload_s` seconds (§2), never less than
`replay_timeout_s`. It is `required`: a replay killed on that bound or otherwise (the failure
names what killed it; for the bound, the rule and its numbers, `campaign_adapter_timeout_rule`), a
session set with no non-empty `activations.jsonl`, or no `targets.jsonl` row whose `anchorSiteId`
is in the target method (from the scope map's `TARGET_SITE` row) fails REPLAY. The workload's exit
code is not the gate (a target that throws exits nonzero by design).

A replay's run ends before its VM session does (`runtime.JUnitMethodRunner#exit`, for the workload's
end and the early ends alike): admission ends (`ConcolicRegionRuntime#endAdmission`: no region
starts after it), live activations settle, the run totals close the session's rows (a closed
`SessionPublisher` writes nothing more), and only then the VM session closes. The settle
(`ConcolicResultPublisher#awaitSelectedResultPublications`) is bounded by progress: it gives up once
nothing has moved for 30 s (no loop body charged, no activation settled, no publication finished,
and the publication thread spent no CPU), so a publication that computes is never cut and one
blocked is: every activation still live is then stranded, and the publication left running is a
`TASK_UNANSWERED` `RESULT_PUBLICATION_UNSETTLED` that holds every obligation of the replay
`NOT_ADMITTED` (`FocusedReplay#noteUnsettledPublication`: its rows may be partial). A stranded
activation's VM region is its thread's, so the terminal that thread still reaches closes it
(`ConcolicRegionRuntime#strand`, `#closeStranded`) and publishes nothing. The end runs once: a
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

A target occurrence publishes its target row whether or not it reached the throw
(`runtime.RowPublication`): `phiTerm` is the VM's satisfied predicate of the target branch put in
the fatal polarity (`RowRuntime.fatalTerm`); when the target branch decided concretely on the 0/1 a
helper returned, the helper branch's last decision before it (its `guardDeciders` entry), the target
standing at that decision; for a target with several guards (`a || b`), the OR of the fatal arms of the tests this
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
violation fails IMPORT naming the first subject. The same gate runs after every EXPLORE wave (§7.9).

## 7. EXPLORE

EXPLORE collects the arms the seed lacks: it flips decisions the anchor's failure can depend on, one
focused replay per flip, in waves, and never decides a witness (only COMPOSE and z3 do).

### 7.1 One wave: `explore.ExploreMain`

One JVM per wave, `--sessions <iteration>/sessions --results obligation_results.jsonl
--static-scope-map ... --target-occurrence <declared> --wave N --output-dir obligations-NNNN` plus the
root domains and bounds. It reads the whole corpus (`explore.Corpus.read`: every session, each
worker's focus row as that session's world, the wave verdicts, the recorded schedule) and:

1. Names planned tasks answered at two addresses (`ADDRESS_UNSTABLE`, DIAGNOSTIC).
2. Resolves the declaration against the seed session's activations (`plan.SelectorResolution`);
   no single SEED session, an unresolved selector, or an address the seed never activated is a
   BLOCKING gap and leaves the wave with no root.
3. Plans the anchor's closure (§7.2). A closure truncated at `--max-tasks` is a BLOCKING
   `ADMISSION_GAP` (DIAGNOSTIC when the witness stop fired).
4. Reconciles the slot table (`explore.SlotTable`, `iteration-0000/slots.jsonl`): one slot per
   (interaction, world) inside the closure; a WIRE consumer paired with another producer in the same
   world is a replacement, and a read whose observed write the run orders after it (the two rows'
   seqs, the VM's one event clock, whatever threads ran them; never the anchor chain, which orders
   occurrences, not their events) contradicts the order (both `TOPOLOGY_DIVERGENCE`, BLOCKING when
   the session is admitted, else DIAGNOSTIC); another
   world's pairing is a new slot.
5. Builds the ledger (§7.3) and the candidates (§7.4) and opens the wave: `obligations.jsonl`
   (empty = the frontier closed).
6. Witness stop (`region_path_stop_at_fatal=true` → `--stop-at-fatal`): once an admitted non-seed
   session's target row at the anchor observed the fatal, this wave asks nothing and grows nothing
   (DIAGNOSTIC gap; manifest state `WITNESSED`).
7. Writes `graph.jsonl` (`WaveGraph`: NODE per activated occurrence of admitted sessions, EDGE per
   WIRE pairing and STATE join, each with the world digests it was seen in, and a FRONTIER row with
   the counts new since the previous wave), `growth.jsonl` (§7.8), `tasks.jsonl`, `gaps.jsonl` and
   `explore_manifest.json` (anchors, tasks with their `why`, proposed/answered counts, verdict
   histogram, gap counts, state `FIXED_POINT` | `OBLIGATIONS_PROPOSED` | `WITNESSED`).

### 7.2 The closure: `explore.ClosurePlanner.plan`

Demand starts at the anchor: its flip sites are the target sites' guards
(`StaticScopeMap.Site.guards`) when some run reached the anchor, else the sites of the target's path
chain (`pathSites`). The demanded symbols of an occurrence are those its demanded values reach
(`SmtLowering.reachedSymbols` over the lowered terms and, where a read's refused join gave way to its
mint or its value, over what that join lowered: `Lowered.reach`; such a lowering is no `Lowered.ok`
value a flip query stands on): the anchor's `phiTerm` (a concrete fatal condition's constant names
nothing), its own decisions at its flip sites (a factor
member deciding the same site decides it on its own objects), and the values it contributed (the
exports a demanded attach paired with, the write a demanded read could observe), closed over the
reads those name and the writes they could observe. The occurrence and its state-connected factor are
one symbolic unit: every member's attaches and reads are asked whether a demanded value rests on them,
and a member joins the closure only through them, as a writer or a producer below, never for touching
what the occurrence touches (two readers of one location pass each other nothing). Each demanded
boundary input grows the closure:

- an attach whose symbol is demanded: its paired producer occurrence (reason `CLOSURE_MEMBER`, flip
  sites = the guards of the port's static export sites, contributed = its exports), and every activated
  occurrence holding a static export site of the port on the paired producer's node
  (`STATIC_CANDIDATE_PRODUCER`); an unpaired attach is `LINEAGE_LOST` (DIAGNOSTIC) and its static
  candidates are taken on every node;
- a read whose symbol is demanded: the writers `Corpus.eligibleWrites` names (the write of the observed
  version, and writes of the same session by HB-concurrent occurrences — `Arms.concurrent`: not the
  same thread key, neither an anchor-chain ancestor of the other, both chains reaching a Root, neither
  Lost), and every activated occurrence on the reader's node holding a static write site of the
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
  anchor's producer endpoint): `CONTROL_PRODUCER`, contributing no value.

An attach or read no demanded value rests on is a DIAGNOSTIC gap, once per endpoint. A region holds a
static site when the map's method set of the region contains the site's method or one of its callers;
with no method set, region-id equality. "Activated" means an instrumented activation row: an ambient
row (a port event outside every admitted activation, `RowRuntime#ambientActivation`) names where the
event ran, not a region that ran the site, so it makes no static candidate
(`ClosurePlanner#activated`); an ambient occurrence joins the closure only through the rows that name
it. A static site no session activated is a DIAGNOSTIC gap ("the retained set would have to grow"),
not a task. One anchor's walk scans one site's holders on one node once and offers an occurrence
once per (reason, site, guard set, node), whichever read or attach asks for it: asked again it is the
same demand, and folding it changes nothing (`ClosurePlanner#candidates`); the walk says each gap
once. Each demanded occurrence becomes a `Task` (id =
`digest("task|" + occurrence id)`, focused occurrence, state-connected factor, planned from the seed if
the seed captured it, else the first admitted session that did); its flip sites are its demanded sites
plus every fault site (`Corpus.faultSites`: a decision whose lowered term reaches a MARKER root). A
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
(`Corpus.inputShape`): whether the task's occurrence and each factor member that writes state it reads
ran, their handoff sites and producers, and those members' write counts at the locations the guard
reads — never delivered values. Never the session. An arm is
settled when some session recorded it under the same dependence, or an earlier wave answered it
`ADMITTED`, `UNSAT` or `NOT_ADMITTED` (`SAT_MODEL_READY` is no answer). The ledger is rebuilt every
wave from the corpus and `obligation_results.jsonl`.

### 7.4 Candidates: `ObligationFactory.candidates`

Paths of the task's occurrence, smallest world first, cut only from admitted sessions. A flip
candidate is a decision with a term (`FlipQuery.flippable`) at one of the task's flip sites, fault
decisions first. Bounds (`ExploreMain` options, defaults in `ObligationFactory`/`ClosurePlanner`):
`--max-tasks` 64, `--max-paths-per-region` 32 paths per task, `--max-flips-per-path` 32,
`--max-world-depth` 3 (flips a cut path's world may already hold). Every bound that drops work files
a DIAGNOSTIC gap; settled candidates are filed as DIAGNOSTIC gaps too.

### 7.5 One obligation: `explore.ObligationSolverMain`

`ObligationFactory.locate` finds the published obligation's path in the corpus under the wave's id
(a path gone from the corpus is `NOT_ADMITTED`). `FlipQuery.build` asserts the path as its replay ran
it up to the flipped decision, the flipped decision negated, and every inherited flip's prefix through
its flipped decision (`Arms.conjunct`/`Arms.pathCondition` apply the recorded polarity; terms are
lowered by the one lowering, `compose.SmtLowering`). Each symbol it names gets one rule:

- ROOT: a declared MARKER is a free Bool; a CLOCK is one variable per (root, session) with domain
  `[host reading, host reading + 30 days]` in its own ticks (`RootMintRow#hostReading`: the mint's
  instant less the skew its node's clock ran at there; `JavaPrimitiveSmtSemantics.clockDomain`/
  `clockSkewCeiling`; no reading: `[0, Long.MAX]`; declared clock bounds are not read here), and its
  nearest world is the instant the session ran it at; any other root takes its domain from
  `root-domains.jsonl` (or the mint's), else is pinned to its recorded value.
- HANDOFF: an attach of the focused occurrence (a *control*) is bound per slot by
  `OR(pi_q ∧ guard_q ∧ v_H = e_q)` over `Arms.wireArms` (nested slots closed); a paired control whose
  every arm is dropped refuses the query (`UNPRODUCIBLE_ANSWER`); an unpaired one is free and listed
  `unproducible`. Every other attach (no answer is planted there) is bound by the arms of its own
  run only, nested slots closed the same way, so it moves only with the roots and clocks the replay
  plants (SOLR-18413: the leader parses a routing rule's expiry in its state watcher, and the expiry
  is the Overseer's clock plus the timeout); with no such arm it is pinned to its recorded arrival.
  Another run's arrival never binds it. A codec's hole (WIRE-CODEC) is a handoff like any other: its
  arms are the exports of its own message and hole at the producer endpoint (`Arms#sameMessage`: the
  export's `messageKey` and hole are the attach's `correlationId` and hole), bound by COMPOSE's one
  hole-arm rule (`VmTermLowering#holeArm`, §8) over the query's names, and a relay's operand, the
  upstream hole's symbol, is a nested slot.
- READ: the eligible writers (`Arms.stateArms`) become one Bool selector each (`wchoice_*`,
  exactly one); no writer: pinned to the row's `concreteValue`; neither: refused `UNSTATED_VALUE`.
  Only reads the text names are variables: a container state behind a guard is inlined by its join
  (the closure demands its writers, §7.2), so the query declares nothing for it — a variable bound
  to each writer's state would constrain nothing, and its equalities over states built by removals
  (lambdas) are outside what z3 decides (`unknown`, "incomplete (theory array)").

An undeclared name in the flipped conjunct refuses the query (`DECLARATION_MISSING`); in a prefix
conjunct it drops the conjunct (DIAGNOSTIC); a malformed lowered term likewise. A name is declared
when the query declares it, a `let` binds it, the fixed preamble states it, or it is a theory
operator of `compose.SmtNames.BUILTIN`, the one vocabulary every stage reads with, which lists every
operator the lowering writes (the string operators `str.substr`, `str.indexof`, `str.at`,
`str.from_code`, `str.to_code` among them, the floating-point operators, `to_fp`, `int2bv`, `bv2int`
and the `Array` sort); COMPOSE refuses a path on the same test. A symbol no rule binds
refuses (`UNPRODUCIBLE_ANSWER`); a query with no variable of its own is not asked. A construct the
lowering refuses inside a stated term becomes a fresh `unsupported__*` constant of its sort and stays
in the query. Demanded conjuncts (the flip and the inherited flips) get a one-minute clock margin on
each comparison atom over a clock whose polarity `not`/`and`/`or` resolve (`explore.ClockMargin`;
an atom it cannot strengthen is a DIAGNOSTIC gap). The objective is the nearest world:
`minimize Σ|x − recorded(x)|` over bounded Int roots and clocks (`FlipQueryText`).

z3 runs with `solver_timeout_ms`, which its driver (`smt.Z3`) enforces; a JVM that ends takes its
running z3 processes with it (a shutdown hook), and each z3 also carries its own hard timeout ten
seconds past that budget (`-T`, `Z3#hardTimeout`), so one whose JVM was killed outright stops by
itself. Timeout (`SOLVER_TIMEOUT` gap), `unknown` or error →
`NOT_ADMITTED`; unsat → `UNSAT`. On sat (`ObligationFactory.solve`): roots the assertions reach are
read back by root id, the flipped path's clocks as skews (`model − host reading`; one outside a Java
long refuses), controls as answers keyed by attach endpoint id (`ObligationFactory#answer`: a String
control -- a codec's STR hole -- as its JSON string literal, which the replay plants verbatim; one
whose model value is no string literal refuses, `NOT_ADMITTED`). Every recorded value a query pins
(an arrival, a read's `concreteValue`, a root) is a literal of the sort its variable is declared at
by COMPOSE's one rule (`SmtText#literal` → `VmTermLowering#smtLiteral`). A model that plants
nothing its path's session did not run -- no moved clock, no answer, and every assigned root at
the value that session minted -- is refused before any replay (`ObligationFactory#plantsNothing`,
`NOT_ADMITTED`, a DIAGNOSTIC `ADMISSION_GAP` under `EXPLORATION`): its replay would run that
session's world again. Assigning roots, all at their recorded values, it names the polarity or
binding fault that implies; assigning none (`EMPTY_WORLD`), it names the symbols the model moved
that no replay plants -- writer choices `wchoice_*`, container states `st__*`, refused terms
`unsupported__*` (SOLR-18413 r5: 67 such focused replays, r7 14, r9 2, none ever admitted). The
parent world is overlaid (model wins) and its flips inherited. Every assigned root must
have a mint in the seed session (else `ASSIGNMENT_UNMINTABLE`, `NOT_ADMITTED`). The worker writes
`obligation_result.jsonl` (`SAT_MODEL_READY`), `obligation.jsonl`, `obligation_query.smt2`,
`gaps.jsonl`, `focused_task.jsonl` (the focus row, [CONTRACT-SPEC.md §3](CONTRACT-SPEC.md)) and the
schedule cut (`SchedulePrefix.write`, held): the source session's schedule up to the first event or
mark of the flip occurrence, the focused occurrence or a factor member goes to
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
for every assigned root and clock skew, and every inherited flip held; anything else is
`NOT_ADMITTED` naming why. A mint that ran without planting its assignment is a BLOCKING
`ASSIGNMENT_UNPLANTED` gap of the session. A replay ends once the focus row's `declaredTarget`
publishes a target row that reached the anchor and observed the fatal (`AT_WITNESS`, §5).

**The early end at a refusal** (`FocusedReplay#refusedAt`). A replay is *decided* at the first
refusal after which every obligation it carries is `NOT_ADMITTED` whatever the run does next: the
prefix of an obligation's own occurrence is abandoned (`REPLAY_PREFIX_UNMATCHED`: the flip site took
the recorded arm, or the occurrence closed without reaching it), which holds every flipped
obligation of the replay `NOT_ADMITTED` too, or a flip the replay inherited took the other arm. It
ends there (`AT_REFUSAL`, §5). A flipped obligation is never decided before its replay ends: its
session is a corpus session, cut from by later waves and read whole by the closure and COMPOSE (the
anchor, the fatal and writers after the anchor among them), so only the witness ends it early. A
decided replay **publishes no session**: its verdict rows state the refusal and that the replay
ended there, the worker's row names no session, and the replay withdraws the directory it opened
to `<worker>/refused-sessions/` at its close, in one rename (`RowRuntime#closeSession`,
`SessionPublisher#withdrawTo`); `campaign_obligation_replay`, on the host that ran the replay,
withdraws one a failed move left listed. A `NOT_ADMITTED` replay ran no world (§7.4 cuts no path from one),
and rows cut at the refusal are a prefix of a run no stage could tell from a whole one. Its gap rows
stay EMIT's (§11). The head, reading a peer's row that names no session, waits until its own
listing holds no session naming the obligation (`campaign_await_remote_result`), so neither the
wave's gate nor the next planner reads one a cached listing kept.

A replay killed on its bound: its session is withdrawn to `<worker>/timed-out-sessions/` and the
answer is `NOT_ADMITTED` naming the bound. A solver JVM that exits nonzero records `NOT_ADMITTED`
with its last stderr line. A replay that states no verdict fails EXPLORE.

### 7.7 The work pool

`campaign_dispatch_wave` starts `min(slots, obligations)` slots; slots = `concolic_worker_count` per
host of `campaign_worker_hosts` (empty: local only), interleaved across hosts and starting at the
host the wave directory's `cksum` picks, so one-obligation waves spread. A slot waits for memory
on its host, then claims the next obligation by `mkdir` of its queue index, runs it (locally in a
subshell, or remotely through `ssh` running `run_engine.sh --run-obligation` with the frozen jar and
its sha256), and loops. The memory gate (`campaign_host_try_start <host> [need] [ramp]`) is a ledger
shared by all campaigns and `tools/adhoc/fanout.sh` under `$CAUSYNTH_HOST_LEDGER/<host>/`
(`tools/lib/gc-env.sh`): each row is `<epoch> <mb> <ramp_s> <id>`, and a start is allowed when
`MemAvailable − (rows still inside their own ramp) ≥ need + MemTotal × (100 − p) / 100`, where
`p` is `CAUSYNTH_HOST_MAX_USED_PCT` (70): no start leaves a host more than 70 % full. An obligation needs
`obligation_memory_mb` for 60 s. The head (`do_campaign`, `campaign_head_charged`) charges each of
its engine JVMs `engine_memory_mb` (else 8192) for 120 s and its seed and CONFIRM replays
`obligation_memory_mb` for 300 s, and releases the row when the command returns
(`campaign_host_release`); an obligation's own JVMs are inside its slot's charge. An obligation
whose worker does not finish (a nonzero exit, local or remote, or a result the head cannot see) is
its own answer and the slot goes on (`campaign_obligation_unfinished`): every process on its host
whose command line names its worker directory is ended (a peer's replay JVM is in a process group
the remote wrapper's watchdog does not reach), a session naming it moves to
`<worker>/unfinished-sessions/`, and its row is `NOT_ADMITTED` naming the host and the exit. Only a
slot whose host's memory cannot be read fails the wave (the campaign fails at EXPLORE after
reaping remote workers). Verdicts are appended to `obligation_results.jsonl` once the wave settled.

### 7.8 GROW

When `growth.jsonl` holds `EXPOSED_REGION` rows (occurrence, region, node, exposing session and its
obligation), `campaign_grow` runs after the wave's replays: `plan.ExposedRegionPlanMain` synthesizes
one task row per exposed address (admission basis `EXPOSED_BY:`, static inputs only, the plan's
`replayGroupId`), appends them to the task plan, re-runs INSTRUMENT, and re-runs the exposing
obligations' replays side by side on the head, each in its own worker directory, their starts
spaced by the head's memory gate; the wave waits for all of them. The exposing
session and the worker's previous files move to `<worker>/before-<wave>/`, and the re-run's verdict
replaces the obligation's row in `obligation_results.jsonl`. An exposure no obligation names (seed
exposure) fails EXPLORE.

### 7.9 The loop

`campaign_explore`: plan wave N; if `obligations.jsonl` is empty and no region is exposed, stop (the
fixed point). Otherwise stop with a DIAGNOSTIC `ADMISSION_GAP` row in `campaign_gaps.jsonl` when
`N ≥ region_path_max_waves` (`REGION_PATH_WAVE_BUDGET_REACHED`) or when the signature over the
proposed ids, the verdict histogram and the exposures equals the previous wave's
(`REGION_PATH_CLOSURE_NO_PROGRESS`). Else dispatch the obligations (if any), GROW (if a region is
exposed), then gate the wave: the IMPORT
gate over the whole session roster (linked under `import-gates/obligations-NNNN/`) whenever the wave
added a session; one BLOCKING violation fails the campaign at IMPORT.

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
```

Corpus-level BLOCKING gaps: one solver name for two roots, a session not read whole
(`SESSION_INCOMPLETE`), a session's own verdict disagreeing with the worker's result row, not exactly
one SEED, an unreadable slot table, one name at two sorts, one name for two identities. Sessions that
replace a slot (§7.1) give no arms.

**Admission** (`admit`, `settled`): one path per session whose target row at the anchor reached it
(a target row that did not reach it is a DIAGNOSTIC gap); the seed always, a focused session only
when all its own verdicts are `ADMITTED`; an obligation its manifest names with no verdict is
BLOCKING. No target row at all is
BLOCKING `DECLARATION_MISSING`; no disjunct is BLOCKING `ADMISSION_GAP` naming the first refusal.

**One path** (`compose(path, ordinal)`), in its own session's scope:

- P3 closure (`closure`): the occurrences the path's joins reach, each with the seq its prefix runs to,
  including earlier versions of every reached write's location; a refusal is its frame's
  (`frameRefusals`): an `UNSTATED_VALUE` row the session filed on a reached occurrence (a VM-refused
  attach, an attach that minted no `v_H`; `Corpus#refusedIn`) refuses the path, and an arm whose
  closure reaches one is no option;
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
  focus row's assignment where the replay planted it, else the mint's reading): a declared root
  minted with no value, or a mint whose `recordedValue` differs from the assignment ("stated twice
  and differently"), is a BLOCKING refusal; a root the sessions recorded differently is pinned to
  this session's value, or bounded by its declared window around it; a declared root this session
  never minted refuses the path only when the path's terms name it;
- anchor handoffs: bound only by the message family, answered or not (an obligation's answer is
  what its replay planted at the consumer, not what a run delivered, so it is never a literal);
  an attach no session attests the producer of refuses the path (`UNATTESTED_ARM`);
- the read rule (`statedReads`, `stateJoins`, through `SmtLowering.bind`, the guarded read's rule
  too): JOIN to the observed version's write expression if it lowers with no refusal, else the MINT
  of that version (a placeholder), else PIN to the value the row states, else REFUSE
  (`UNSTATED_VALUE`); a refused join is dropped for the mint or the pin only when nothing it rests on
  can move (a root, a clock cell, a handoff, an anchor location a STATE family may re-pair), and
  dropped it raises nothing (no refusal, side condition or gap); what a read row's binding required
  (container membership and cell tags, recorded readings) is stated with its join, so only where
  the conjunction asks about the read (`Composer#statedJoins`, `SmtLowering#ownConditions`); an
  object the VM named (`M_L'<class>'_<rid>`) is the reference it is, whatever its class, where a
  whole value is asked
  (`SmtLowering#whole`: a join, a published expression, a stated value) or a reference is (a
  comparison asks a named operand at the other's sort, on either side, `#binary`); an operator
  asks for its own operands, and a named container there is its state, at its class's sort
  (`Host#state`: that object's own state root, `container__`);
- `pi_p`: the anchor's decisions strictly before the target row's seq, and each reached occurrence's
  decisions before its cutoff;
- `phi_p`: the published `phiTerm` (fatal polarity); a concrete fatal condition's `true` is the
  fatal resting on `pi_p`, the path condition that reached the anchor, and its `false` refuses the
  path ("decided concretely on its healthy arm"); a row stating no phi refuses it too (invariant 9),
  as the composer never invents one;
- every other handoff the conjunction reaches, by the same rules; a handoff variable the corpus
  states of another session and this one minted no attach for refuses the path by name
  (`UNSTATED_VALUE`), so no path names a boundary variable its families do not bind.

Any refusal drops the path and is filed with its own class (an open lowering refusal is a
DIAGNOSTIC `UNSTATED_VALUE`).

Then **message families** (`ComposedFamilies.closeFamilies`): attaches grouped by correlation id --
a codec hole's is its message key, so the N readers of one stored version, and one decode read
twice, are one message under one selector; the eligible senders are the
sessions with an attested arm at every leaf of the message, whose world's flip set contains or is
contained in the path's; one `message_arm__` selector per sender (identical arm bodies share one),
exactly one, each arm closed like a path in its own session (producer prefix before the delivery, its
P3 closure, nested families to depth 16). The nested families bind every handoff the arm's conjunction
names, its delivery's and those its closure's conditions and joins read
(`ComposedFamilies#handedOn`); one its session minted no attach for, or one paired with no producer,
refuses the arm, so no arm lowers a handoff as a free constant. A message no session can send drops
the path. **A codec's
hole** (WIRE-CODEC §6.1, §6.3) is bound by `VmTermLowering#holeArm`, never by plain equality: its
symbol is declared at the DECODED leaf's sort (the attach's `javaType`, also in
`Composer#attestedArrival`), and the arm is the operand the producer's export cut out of its leaf
(`ExportRow#javaType` its sort) -- equal when the sorts agree, an integral widened by Java's rule
(its range inside the hole's), the canonical rendering read back for a String operand of an
integral (`(= (java_int_to_string v) s)` within the hole's range) or a boolean hole; a narrowing
(`HoleNarrowed`) or any other change of sort, a float read back as a double included
(`HoleSortChanged`), is refused `UNSTATED_VALUE` by name; an arm delivering Java null is
`CODEC_MISMATCH` `NULL_LEAF`; a String operand that may be null holds only where it is not, and one
whose nullness nothing states is refused (`JavaStringNullnessUnknown`). A relay's operand is the
upstream hole's symbol, closed as a nested family (SOLR-18413: the leader's `n2` is the Overseer's
`n1`, which is the overseer's clock plus the timeout). Each hole an arm binds is noted with whether
its value rests on a clock (`ComposedFamilies.BoundHole`: a CLOCK root the delivered value reaches,
or a nested hole that does), for CONFIRM. A path's
families (message and state) are all or nothing: their named assertions, arm choices and families
are stated as they are made and taken back with a refused path (`ComposedFamilies#discard`,
`SmtLowering#retract`), so the next path, composed at the ordinal a refused one left free, names
nothing twice.

**State families** (`stateFamilies`), for joined reads at the anchor only, of a static field or of a heap
location whose owner is an object rid (`Arms.namedOwner`; a class-name owner gets no alternatives):
one `writer_arm__` selector per writer occurrence of the same session (`Arms.stateArms`: the
observed writer's arm is the write the read observed, any other writer's its last write of the
location, and only attested HB-concurrent ones), plus an `observed_arm__` holding each read to its
own join or pin when a version one of the reads observed has no writing row; exactly one per
location that has two arms or more, else the reads keep their own joins. The arm the run took (the
observed arm, else the one writer every read observed) is part of the path's recorded pairing; a
location where no arm is that pairing (the reads saw two writes, or the write they saw has no arm)
is a BLOCKING `UNSTATED_VALUE`: the run as it happened is no world of the formula.

**A field through a re-pointable owner** (`SmtLowering#projection`, reached from the codec's
`Host.projection`). A field projection whose pair (`concreteOwner`/`concreteValue`) is stated
lowers to the run's cell, except through an owner that is a read `stateJoins` joined at the anchor
at a location a STATE family re-pairs (`SmtLowering#movable`: the family may bind it to another
writer's object). There it is the
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
refused, and it is named DIAGNOSTIC `CANDIDATE_UNANSWERED:<cell>@<session>`. EXPLORE lowers through
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
store producer's (`ComposedFamilies#stateClosure`, `Composer#closure` seeded with that write, the
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
the source's keys. The presence and match conditions of `putIfAbsent`, `replace` and `remove(k, v)`
are comparisons of a `READ` with null or the argument, lowered as any comparison. A String a map
answers is its cell's `valueString`, null where the cell is the null cell `(VRef nullRef)`
(`ContainerStateModel#unboxValue`, `ContainerSmtCodec.Term#nullness`). A view's positions are
stated linearly in its chain's puts: each position below the size names a present key held at that
position, and each put key present is held at a position below the size. A position is the run's
iteration count, so the chain's order is the positions' only where it is the order the map's class
iterates in (`ContainerSmtCodec#ordered`): the snapshot's members follow its base in that order
(`order`, `members`); an `INSERTION` map iterates in its chain's order after them (a `putAll` in
its source's); a `HASH` map keeps it through removals and updates of a key it holds, while a put of
another key may rebin or resize its table. Past such a put, or over a base stating no order (a
recording before it), the same facts are stated through `assoc_view_key` and
`assoc_view_position` (`ContainerSmtCodec.ViewOrder.FREE`): the positions are a bijection with the
keys in no order, so a view read as a set keeps every key and no position is tied to a key the run
may not have had there. A view walks the state each step of its chain stands for (`Host#chain`: a
read's joined version), so a map's `values()` a region iterates through a read of it is bounded by
that version's keys.

**Construction guards** (`Composer#constructionGuards`, R3-REFCONT §1.6, D5). A write that stored a
container states its `referentState`; its referent rests on every decision its occurrence took
before it at the guard sites of the mutations its method made on a container it then published
(`StaticScopeMap#constructionGuards`, the scope map's `publishedFrom` write sites, the carriers the
store's recorded type may be held by, `StaticScopeMap#carriersAt`), those that skipped a mutation included. `Independence` keeps them: a kept
read brings the guards of the write it observed, and an arm (`ComposedFamilies#producerBody`) seeds
the guards of the writes it delivers (`Arms.Arm#write`); the closure then conjoins them in the
polarity they took, and the reads they name are joined in turn. A decision whose condition is a
REMOVE_IF guard of the referent's chain, or that guard's complement, stays free. `ComposeMain`
reads the epoch's scope map (`--static-scope-map`, required; `run_engine.sh do_compose` passes it).

**An owner kept to the run's pairing** (`Composer#pinnedOwners`): a location a STATE family may
re-pair keeps the run's pairing (no family, no movable owner), named DIAGNOSTIC, when a reached
occurrence's container version is a mutation naming as its `owner` a read of it
(`OWNER_PINNED_BY_MUTATION:<location>@<session>`, R3-REFCONT C-4: another pairing would mutate an
object no row records the mutation of), or when a store of it states or refuses a referent while
the object it stored has no container log of its own in the session, a `Collections` wrapper or a
view (`OWNER_PINNED_BY_WRAPPER:<location>@<session>`: a query through a wrapper reaches its map
through a field no row records and names no owner, so it would be the run's map's answer whichever
object the family delivered), or when the anchor or a reached occurrence asks a field or a query
through a container query's read of it (`OWNER_PINNED_BY_CONTAINER_READ:<location>@<session>`, the
read names no object, `Composer#containerOwners`).

**Roots and clocks.** `domains`: a declared MARKER is free; a root the sessions recorded differently is
stated per path; a domain from `root-domains.jsonl` (absolute or `±k` from the recording) or the mint
is a window; otherwise the root is pinned. `clocks`: every clock cell the formula names gets a
reading on the recording's timeline -- the seed's, or, for a cell the seed never read (a region
woven after it), the seed's reading of the nearest cell (by seq) of the same clock that a session
reading it also read, plus the time that session's host read between the two; a cell no session can
place is BLOCKING (`DECLARATION_MISSING`) -- and a domain, floor = the reading, ceiling = reading +
30 days (in its ticks), unless the case declares bounds. On one node, each cell is no earlier than
the nearest earlier cell by seq (the recording's event, the order a replay runs a plant on in) of the
same clock (`contract.Clock#same`: the JVM clock its row states and the same tick; a cell stating
none is on no order, DIAGNOSTIC) (`clock_order__`); where the recording read the two the other way round, the link gives way by that
much (`(<= (- earlier later) d)`), so the recording always satisfies it. The cells are listed in seq
order (`Composition#clockCells`), each with its reading and the cell before it (`clockBefore`).

**Valuations** (`valuations`): ordinal 0 = every declared root at its recorded value; then single
moves sorted by distance, then pairs of moves, cut at
`compose_max_valuations` (a MARKER's move is its other polarity; an INTEGRAL's values come from its
window; clocks are not enumerated).

ComposeMain writes three files. `candidate.smt2`: the body, then valuation 0 as named pins
`(assert (! (= <root symbol> <value>) :named valuation__<symbol>))` (so the file as published asks
about the recorded valuation; every other valuation differs only in these pins), then the pins
ClaimPolicy held outcome 0 under (clock pins `clock_pinned__*`, recorded pairings), `(assert false)`
with the blocker named when the claim is blocked or there is no path, and `(check-sat)`.
`candidate_composition_manifest.json`: the `CompositionManifest` fields plus `finalStatus`
(`FINAL_READY` | `FINAL_REFUSED`), `finalStatusRefusals`, `gaps` and `solver` (§9). `claim.json`:
`{kind CLAIM, anchor, claim, solverRuns, seedSessionId, valuations, gaps}`, what CONFIRM reads; a
selected arm binding codec holes states `holeTexts`, consumer endpoint id -> the model's value of
the hole as the text it decodes to (an integral's decimal, a boolean's `true`/`false`, a String's
characters; none for a char or a floating value), for every hole whose value rests on no clock through the valuation's selected arms
(`ComposedFamilies#holeTexts`; a replay reads its clocks afresh).

## 9. SOLVE and DECIDE: `compose.ClaimPolicy.decide`

The shell stages only check and print what ComposeMain decided (`solver.state`, valuations, claim).
`ClaimPolicy`:

1. No disjunct: `NO_SUPPORTED_WITNESS`.
2. Every valuation is asked (up to 8 z3 processes at once) for the path selectors, arm selectors,
   the nested state selectors a state arm's stores are chosen among (§8), clock cells and the codec
   holes the arms bind (`Composition#holeSymbols`); a selected
   state arm keeps the states whose selector the model set. Each path is also asked alone with every root free (60 s): unsat →
   `PATH_SELF_CONTRADICTORY` DIAGNOSTIC; all paths → BLOCKING. An undecided valuation is BLOCKING.
   Every such ask (and each re-ask below) is `byDisjunct`: the disjunction whole, its verdict within
   60 s (`WHOLE_BUDGET_MS`; its model and core runs keep the full budget); undecided, one path at a
   time: the first sat path answers, else undecided if any path was, else unsat with the union of
   the paths' cores. Whole, z3 decides in seconds where it decides at all, but can spend any budget
   searching every path's conjunction at once (hdfs-11741 r3: 47 paths undecided in 30 min whole,
   about a second each alone). A path is asked by `Composition#pathQuery`: the body without the
   commands another path's selector guards (`(assert (=> <selector> ...))`, vacuous once the
   partition forces that selector false), its own selector asserted; 90-98% of a body is guarded
   (hdfs-17899-bug2 r4: 1.7 of 93 MB shared). The self-contradiction check and `mechanism`'s pinned
   re-asks of the selected path read the same text. Selectors are never asserted together: two
   contradict the partition.
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
   the clock's jumps. A sat ordinal 0 on a path that did not observe the fatal,
   when the recording does not decide, is BLOCKING `FORMULA_SAT_AT_RECORDED_VALUATION`.
   `polarityDecides` = ordinal 0 unsat with a `valuation__` pin in its core.
4. The claim, first match:
   - a moved valuation that is a witness — under the as-happened pins when the recording decides —
     whose moved roots are in no unattested arm (else BLOCKING `UNATTESTED_ARM`): its `mechanism`;
     without `recordingDecides` it also needs `polarityDecides` (else BLOCKING
     `FORMULA_SAT_AT_RECORDED_VALUATION`);
   - a witness moving no root whose mechanism is `CLOCK_SKEW`, `STATE_PAIRING_FLIPPED` or
     `MESSAGE_PAIRING_FLIPPED`, with `recordingDecides` or `polarityDecides`;
   - ordinal 0 sat on the seed's path that observed the fatal, every moved valuation decided unsat:
     its mechanism, with `polarityDecides` true unless that is `RECORDED_FAILURE_EXPLAINED` or
     `NO_SUPPORTED_WITNESS`;
   - ordinal 0 sat on another session's path that observed the fatal, all its families attested, and
     every disjunct of the seed's session unsat at the recorded roots: its mechanism, if any;
   - else `NO_SUPPORTED_WITNESS`.
5. `mechanism`, narrowest first: pinning the path's observed reads makes it unsat →
   `STATE_PAIRING_FLIPPED`; its observed anchor arrivals → `MESSAGE_PAIRING_FLIPPED`; a moved root →
   `MARKER_FLIPPED` (any declared root kind); `clockDriven` → `CLOCK_SKEW`; the seed's path at ordinal 0
   with the flips refuted → `RECORDED_FAILURE_EXPLAINED`.
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
| `RECORDED_FAILURE_EXPLAINED` | the seed itself observed the fatal and every moved valuation is refuted |
| `NO_SUPPORTED_WITNESS` | nothing in the corpus supports a witness; an answer, not an error |

`ComposeMain.campaignClaim` maps it: any BLOCKING claim gap → `INCONCLUSIVE_PARTIAL`; else a kind other
than `NO_SUPPORTED_WITNESS` → `SAT_CANDIDATE`; else every valuation decided unsat → `UNSAT_CLOSED`; else
`INCONCLUSIVE_PARTIAL`. The manifest's `solver` block carries `state` (sat/unsat/unknown),
`reachability`, `unsatClosureComplete`, `valuations` (status, assignment, moved, selected path and
session, `fatalObserved`, `selectedArms`, unsat core) and `campaignClaim` (`claim`, `claimReason`,
`findingKind`, `valuationOrdinal`, `polarityDecides`, `movedRoots`, `blockers`, `whyNotAccepted`,
`witnessFindings`).

## 10. CONFIRM: `explore.ConfirmMain` and `runtime.Confirmation`

Only a `SAT_CANDIDATE` is confirmed. ConfirmMain reads `claim.json` and the manifest, takes the claim's
valuation, its selected path and session, and the selected arms of that path; the selected session
must have a target row at the anchor that reached it (else refused, exit 1 → unconfirmed).

- **Realized**: when that target row observed the fatal, every selected arm is the session's own
  delivery, every write the model chose for a read of the join closure at a location the fatal
  rests on (`restsOn`, below) is the one that read saw (`StateClosure#ran`), the session minted
  every moved non-clock root at the model's value, and its clocks are the model's (on every cell
  the composition anchors, the skews its world planted are exactly the claim's jumps; skews compare,
  each off its own run's host), the session is the confirmation (`realized.json`, no replay).
- **Otherwise one replay**: the world is the selected session's own focus row (empty for the seed)
  overlaid with the model (`ConfirmMain.Moved`): every moved root, by root id, at the recording's
  mint occurrence -- any other root as its value, a clock as its skew off the reading the
  composition anchored its cell to (the manifest's `roots`) -- and, on every clock cell the
  composition anchors, the model's jumps alone: the session's own skews there are dropped, since
  the model runs those cells on from the jump before them. A moved root the recording mints
  nowhere, or a moved clock the composition anchors nowhere, refuses the confirmation by name. The focus row focuses the anchor
  with `flip: null`, the anchor as declared target, no inherited flips. The schedule is written
  unheld (`SchedulePrefix.write(..., held=false)`: every event is suffix; only WAKEs wait for what
  they followed, and when the selected session was cut at its witness, a WAKE it never made waits
  for its whole order). `expected_edges.jsonl`: `WIRE` per consumer of each selected message arm (producer
  as that arm's session paired it; a codec hole's also with `messageKey`, the store version the arm's
  message was when its key is a store's, `<transport> <path>@<version>`, and `value`, the arm's
  `holeTexts` entry), `STATE` per read of the anchor's join closure (each reached
  occurrence's reads before its cutoff, the anchor's before its target seq) at a location the
  selected path's fatal rests on (its manifest `restsOn`: `Composer`'s constraint independence of
  what the fatal rests on -- phi, or for a concrete fatal condition the path condition before the
  target, `Composer#fatalRests` -- and the roots alone, without the locations a family merely binds: a
  read elsewhere holds no
  value the witness needs, and under a moved root the run may make it at another endpoint or not at
  all; the write the model chose, else the observed one: a `writer_arm__`'s write for a read of its location (among its
  endpoint's writes, the one the read observed, else the last, as `Arms#stateArms` chose), and for a
  query through a re-pointable reference the write of the state its arm's `referentStates` name,
  §8), `ORDER` rows (the writer's activation exits before the reader's enters; every other writer of
  the location the held write is of before the writer or after the reader), `MARKER` per planted
  marker, `ANCHOR`. A `referentStates` row with no reader (a query asked outside every container
  read), at a read that is no read of the closure, or naming a write the session does not state
  refuses the confirmation by name; one at a read past its cutoff holds nothing the fatal rests on.
- The replay runs through `campaign_obligation_replay` into `final/confirm/`. At runtime
  `Confirmation` compares WIRE at the attach (`Confirmation#attached`: the producer, and for a codec
  hole the message key and the decoded text the mint states), STATE at close, and holds each `ORDER` activation's
  entry until the named activations exit (`causynth.confirm.order.timeout.ms`, 300 s; a stall is a
  mismatch); every difference is a `CONFIRM_MISMATCH` gap in the session. `MARKER` and `ANCHOR` rows
  are not read by the runtime. A CONFIRM run (`FocusedReplay.confirming`: its obligation flips
  nothing) whose `expected_edges.jsonl` is missing or unreadable compares nothing and files one
  `EDGES:` mismatch at the close, so it confirms nothing.
- Decision (`ConfirmMain --claim --output <worker> --sessions <dir>`, `ConfirmMain#decide`, which
  prints `final/confirm.json`), conditions in order, the first that fails named as the reason: the
  replay's verdict is `ADMITTED`; its session directory exists and its `gaps.jsonl` and
  `targets.jsonl` are readable (a session that did not publish them answers nothing); no gap is a
  `CONFIRM_MISMATCH`; and a target row whose occurrence id is the claim's anchor's (the id only
  the Java address computes) has `reachedAnchor` and `observedFatal` — a fatal at another
  occurrence of the target site does not confirm. A ConfirmMain that exits nonzero is
  "unconfirmed" with its log named.

`final/confirm.json`: `{schemaVersion 1, kind: CONFIRMATION, confirmed, reason, sessionId}`, the
same shape for a refusal, `realized.json` and the decision.

## 10b. REPRODUCE: the confirmed world, natively

A confirmed `SAT_CANDIDATE` is run again on the stock JDK, in the recording weave, with nothing of the
concolic VM (`campaign_reproduce`; ADHOC-INFRA WP5.D). `ConfirmMain --iteration --claim --plant
<file>` writes the plant from CONFIRM's own world (`ConfirmMain#world`: the selected session's focus
row overlaid by `plantModel`), one row per root, `{kind MARKER, occurrence: <mint occurrence id>,
siteId: <the call site its plan input action names>, value}`; a world that also skews a clock,
answers an attach or assigns any other root is refused (`NATIVE_PLANT_UNSUPPORTED`), and so is an
empty one. The recording command runs `reproduce_runs` (10) times, each under `record_timeout_s` and
charged as a replay, with `-Dcausynth.plant` (`execute.sh`, `CAUSYNTH_PLANT`): there
`Debug.makeSymbolicBoolean` answers a row's value when its call site is the row's and a region
occurrence enclosing it on the thread (`CausynthTraceRecorder#enclosingOccurrences`) has the row's id,
inside the window, and states each answer as a `PLANT_APPLIED` trace row (`runtime.RecordingPlant`).
A planted run is not the recording's world, so the workload's checks of that world are off in it as
in a replay (`CausynthTraceRecorder.replaying()` is true under `causynth.plant`).
Each run is aggregated for the target as the pre-screen aggregates (`--summary`: `plantsApplied`, and
per target its `occurrences` and `fatalOccurrences`, those that took the fatal arm).
`final/reproduce.json`: `{schemaVersion 1, kind: REPRODUCTION, runs, planted, fatal, atAnchor,
reason}` -- runs whose plant answered a marker, runs where a target occurrence took the fatal arm,
runs where the claim's own anchor did; `runs` 0 with the refusal as `reason` when nothing can be
planted. A native run holds no schedule, so the planted occurrence may not recur: the rate ranks a
finding (`tools/adhoc/findings.py`) and never refutes it.

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
3. `final/result.json`: `claim` = the campaign claim, downgraded to `SAT_UNCONFIRMED` when a
   `SAT_CANDIDATE`'s confirmation is not `confirmed` (the confirmation is copied in, and a
   confirmed one's `reproduction`, required then, null otherwise); `findingKind`,
   `polarityDecides`, `valuationOrdinal`, `movedRoots`, `blockers`, `reachability`, `finalStatus`,
   `gapCount`, `telemetryCount`, `accepted = (claim ∈ {SAT_CANDIDATE, UNSAT_CLOSED}) ∧ gapCount = 0`,
   `targetOccurrence`, `valuations`, `witnessFindings`.
4. `final/run-manifest.json`: provenance, iteration manifests, the path, size and sha256 of each
   required final artifact (`candidate.smt2`, `candidate_composition_manifest.json`, `gaps.json`,
   `result.json`; a missing or empty one fails EMIT), stage wall times, session rows and bytes.
5. Exit 2 when the claim is not `SAT_CANDIDATE`/`UNSAT_CLOSED`; exit 3 when BLOCKING gaps remain;
   else 0.

## 12. Acceptance: `experiments/accept/`

`accept.sh` builds the jar, then per case (one at a time; `CASES`, default the nine HDFS cases of
`ACCEPT_ALL_CASES`; `EXPECTED_MECHANISM` also names solr-18413 and solr-18406, both `CLOCK_SKEW`)
runs `lib/run.sh <case> validate` and `campaign` under `CASE_TIMEOUT_SECONDS`, then
`probe.sh`, `cone.py` and `report.py`, and writes `summary.tsv`. `report.py` passes a case when all
hold, read off `final/result.json`, `gaps.json` and `cone.json`:

- `claim` is `SAT_CANDIDATE` (so CONFIRM agreed) and `confirmation.confirmed` is true, `finalStatus`
  is `FINAL_READY`, `accepted` is true, and `gaps.json` names no BLOCKING gap;
- `findingKind` is one of the five mechanisms and is the case's entry in `EXPECTED_MECHANISM` (a case
  the table does not name cannot pass); `polarityDecides` is true unless
  `RECORDED_FAILURE_EXPLAINED`;
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

Ad-hoc sweeps do not use `report.py`: `tools/adhoc/triage.py` classes a case with a `result.json`
`CONFIRMED` when `claim` is `SAT_CANDIDATE` and `confirmation.confirmed` is true, `REFUTED` when
`claim` is `SAT_UNCONFIRMED` (the confirmation's reason is the row's reason), else `NO_WITNESS`
(`UNSAT_CLOSED` included). A case without one is `STOPPED` when its summary row exists (the stage
and reason its logs state: the campaign's own failure, the case timeout, a failed trace
aggregation, a stage's Java main, the engine's `die`, a full disk or quota), `PENDING` when never
started, else `RUNNING` while some lift (`LIFTS`, default lift06–15) still runs a process naming
its directory, `DEAD` when none does.

`tools/regress/offline-ab.sh --round <round>... <baseline-jar> <candidate-jar> [case...]` is the
offline regression gate: per case of the first `--round` holding it, it runs every stage that is
a pure function of the recording once per jar — the static pass, the trace aggregation, PLAN,
EXPLORE wave 0 and its solves, IMPORT, the closing EXPLORE wave, COMPOSE with SOLVE and DECIDE,
and CONFIRM's planning — over private iterations that link the recorded sessions, with no
workload and no replay; `ab_compare.py` prints one table and exits 1 when a gating stage differs,
2 when one could not be checked. Every stage gates on bytes, the static pass included: it is the
same on every host and run ([SYMBOL-SCOPE.md §2.3](SYMBOL-SCOPE.md)). A round is read as the
current engine reads it, so the gate needs a round recorded by a build whose row contract HEAD
still reads. Both sides run under the gate's own checkout's case declarations, unless
`AB_BASELINE_REPO` names the baseline's: a change that moves a declaration's format with the jar
(the target spec) is gated that way, and each side's checkout path is one token in the
comparison.

## 13. Reading a run

- A campaign that died names its stage: `[campaign:error] stage=… component=… artifact=… reason=…`
  on stderr. A REPLAY death: `iteration-0000/seed-result/focused/replay.log` and the seed session's
  `gaps.jsonl`. A slot or a head that seems stalled logs `waiting for memory on <host>: …`; the
  host ledger is `$CAUSYNTH_HOST_LEDGER/<host>/{available,starts}`.
- `final/gaps.json` `byStage`/`byCode`, then the BLOCKING rows' `detail`.
- Where the wall time went: `tools/analysis/timeline.py <accept-dir>...` reads a campaign's own
  files (stage metrics, file mtimes, the log) and prints each stage (SEED split into static pass,
  weave, recording and aggregation), each wave (planning, dispatch, import gate; obligations by
  verdict, solver JVMs that failed; focused replays with min/median/max duration and how many
  were refused, flipped or ended in error, and how many ended early (§5) with the time from the
  end's replay-log line to the JVM's last write), the CONFIRM replay and the top time sinks. A gate or
  stage that started a head JVM includes the head's wait for memory (§7.7), which the log counts.
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
- `CAUSYNTH_WORKLOAD_JAVA_OPTS=-Dcausynth.debug.producers=true` (read by `experiments/lib/execute.sh`
  for every workload JVM) prints each send's producer endpoint (`CAUSYNTH-PRODUCER` lines on stderr),
  to diff against the recording's when anchors drift.
