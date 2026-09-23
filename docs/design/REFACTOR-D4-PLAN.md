# REFACTOR D4 — code review and plan (2026-09-23)

Companion of `DESIGN4-FAULTS-INPUTS-ITERATION.md`. Baseline: main@497dc8beb, all
nine cases accepted (v15). Sizes: 83,469 lines of Java in `src/main`, 16,704 of
tests, 4,039 of `run_engine.sh`. Biggest files: CausynthPipeline 4,255,
RuntimeRegionPlanner 2,992, SeedBackwardStaticAnalyzer 2,968, CausynthTraceRecorder
2,627, Composer 2,383, ContainerSmtCodec 2,381, ConcolicRegionRuntime 2,208,
SmtLowering 2,094, ConcolicScheduler 2,089, RuntimeSelectedRegionFinalizer 2,032.

## 1. Findings

### 1.1 runtime (45 files, 30,070 lines; runs inside the workload JVM)

- **Mixed passes in one class.** `CausynthTraceRecorder` is the woven trace hooks
  and writer (79-1260, 2155-2330) AND the offline PLAN aggregator (`main`
  135-188, 1378-2155, 2331-2420, ~900 lines); `RuntimeRegionPlanner`,
  `RuntimeRefinedGraphBuilder`, `OccurrenceBinding` (~4,100 lines) are PLAN-side
  code living in the replay package, and the replay imports
  `RuntimeRegionPlanner.UNREGISTERED_SOURCE` (RuntimeTraceContext:1119).
- **Identity mechanisms duplicated.** Two occurrence counters for one event
  (`Lineage.COUNTERS`, window-cleared, vs `RuntimeTraceContext.REQUEST_OCCURRENCES`,
  process-lifetime, whose ordinal addresses nothing); three per-thread frame
  stacks (Identity levels; `RuntimeTraceContext.State.frames` with lane/span ids
  from trace v1; the recorder's `ACTIVE_CALL_SITES`, which the replay maintains
  only so `SymbolizeAction:336` can match a parent call site); two branch
  ordinals (Identity:948 and ActiveRegion:296-304); v1 `occurrenceId` and v2
  `d3Address` both written to rows; three window notions bumped by
  `startRecording` (Lineage, Identity, `recordingStarted`).
- **Recording-pass refusals are silent.** `RowRuntime.gap` returns when no
  publisher is installed (569-570); Identity, ScheduleLog, WakeScopes and the
  envelope refuse through it, so in the recording those refusals vanish.
- **Dead or toggle-only.** `RuntimeRegionPlanner.MethodEvent.reattribute`,
  `RuntimeTraceContext.resolvedHere/peekSeed/attributedSource`; migration toggles
  no script sets (`causynth.attribution=ambient`, `causynth.wake.scope`,
  `causynth.schedule.record/enforce`); 13 `resetForTests` plus `enforceForTests`,
  `setRecordingStartedForTests`, `reduceWriteLogForTest` in production classes.
- Case names appear only in comments; no logic keys on a case.

### 1.2 plan / causynth (PLAN static and in-JVM sides)

- **The fault-marker chain is cut** (DESIGN4 §0.1): the only producer of
  `EXPLICIT_SYMBOLIC_FAULT` actions was deleted in `f5cd60449`; admission never
  reaches the marker's occurrence; `RuntimeRefinedGraphBuilder` still computes
  the bindings (415-440, 560-575) that nothing reads.
- **The same decision made several times.** Region selection: static labels,
  `planSkeletonGraph` (P:118-140, run in both passes), `selectedRegion`
  (F:762-767), `applyClosure`. Port shape: `DeclaredSiteCapture.port`,
  `declaredCutPortAction`, `P.symbolize`. Fold rule: six places. Innermost-owner
  nesting: five passes plus `stampActivationContainment`. Loop bounds refusal:
  P:1168-1200 and S:511-547.
- **Dead.** The `RUNTIME_OCCURRENCE_LINK` half of `stampRecordedExchanges`
  (P:289-462, `runtimeOccurrenceLinks` is never read by `finalizeRegions`,
  ~150 lines); `P.symbolize`'s non-cut-port branches (unreachable); the
  `--retain-regions` / `requireRetainedRegions` / `RETAINED_SET_CANNOT_GROW`
  path (S:1939-1977, 2004-2028) whose feeder went with the IMPORT stack; the
  whole pass-1 skeleton run (`do_regions`, `aggregateSkeletonTrace`,
  `REGION_SKELETON` mode: two workload runs per seed whose only product pass 2
  recomputes).
- `CausynthPipeline` mixes ~70 lines of static PLAN with ~4,000 lines of Soot
  weaving; five replay-only classes live in `plan/`.

### 1.3 explore

- **Five spellings of "world"** (`Obligation`, `Outcome`, the FOCUSED_TASK JSON,
  `Corpus.World`, `Corpus.Flip`); `Candidate` re-derived from rows by `locate`;
  `Task` recomputable from its id yet serialised twice.
- **Three "admitted" deciders**: `SessionReader.admitted` (empty results → false),
  `ObligationFactory.cuttable` (empty results → true — inconsistent), the shell's
  verdict rewrite.
- **Triple dedup** (`offered`, `owed.settled`, `Frontier.open`).
- **The epoch loop is dead** and the skeleton feeds nothing (DESIGN4 §0.2).
- **Latent bug**: `ClosurePlanner.seedSession` (852-862) takes the first session
  in directory order, so every task of wave ≥ 1 carries a replay id as its
  "seed" (11741: 27/27, 43/43, 46/46), contradicting `Task.java:52`.
- **Gap volume**: 11741 wave 3 has 53,419 gap rows, 43,897 of them
  `ClosurePlanner.unread` re-emitted per session per wave; `result.json`
  telemetryCount 113,170.
- **Layering inversion**: COMPOSE imports `explore.Corpus` and `explore.SlotTable`.
- Dead: `FlipQuery.clockFloor`, `Bounds(int,int)`, 3-arg `ClosurePlanner.plan`,
  `ScheduleReportMain` (nothing invokes it).

### 1.4 compose / smt

- **Clock domains** are asserted per clock CELL from `DecisionRow.clockReadings`
  only (Composer:2014-2099, Corpus:493-502) and per cell only for the last
  session's symbol (2028-2042). A CLOCK root that enters the query through a
  family arm or a state join but is read by no decision is declared and never
  domained: in v15 every clock case declares 9-11 clock symbols and emits 6-8
  `clock_domain`s; re-solving bug1's query gives the three undomained cells
  −9.22e18. They are also absent from `clockCells()`, so `clockNecessary` never
  pins them and `movedRoots` never reports them.
- **No per-node monotone structure**: floor is the literal 0 (2073), ceiling
  reading + 30 d; the published 11741 model has nn0's clocks 0, 0, 0, 0,
  72000001, −9.2e18 ×3 while the seed minted them strictly increasing.
- **`movedRoots` reports solver slack**: `clockNecessary` (753-769) pins every
  cell at once with `wantCore=false`, proving "some clock matters", not which.
- **Duplication**: two `Sort` enums and two `Term` classes (VmTermLowering:52,395
  vs ContainerSmtCodec:2218,2223) with three converters; nine one-line shims
  from SmtLowering to SmtNames; boxing rules in three places; a scalar-projection
  layer (`__SCALAR_*`, ~700 lines) that re-encodes the container semantics.
- **R3d single-arm families** (DESIGN4 §0.3).
- Dead: `ComposedFamilies.declaredRootsIn`, `JavaPrimitiveBoxing.deterministicValueOfReturn`,
  `VmExpressionIr.isUntrackedReferencePlaceholder`.
- Only `ComposerTest` (3,564 lines, 21 tests) covers compose; no `smt/` tests.

### 1.5 driver and harness

- `run_engine.sh`: 4,039 lines = 1,159 comment-only + 179 blank + 2,701 code, of
  which ~2,250 run in a shipped single-host campaign, ~330 are the remote pool no
  shipped config enables, ~120 are dead or broken.
- **Broken**: the seed cache — `campaign_restore_seed_cache` demands 9 artifact
  rows (1115) but `campaign_seed_artifact_rows` emits 7, so every cache hit
  dies; masked because `accept.sh` deletes the cache first.
- **Dead**: `campaign_seeding_replay`, `campaign_max_epochs` (a constant
  "required" by `validate_config`), `causynth_process_dirs`, seven derived keys
  never set, stale keep-globs in `accept.sh` naming artifacts nothing produces.
- **Facts stated in four places**: the expected mechanism (report.py:84-103,
  probe.sh:112-118 — which disagree for 17967 —, accept/README.md, each case
  README); the analysis scope (case.sh, case-env.sh, READMEs); the target
  occurrence (17897: three different ones in case.sh, README, workflow.properties).
- **Contradictory READMEs**: 17967's says the IPC fault marker "is deliberately
  removed from all three worktrees" — all three contain it; every README names
  a branch the worktree is not on; 17899's README says two clock rows, there are
  five.
- **Machine paths in the repo**: `/u/vnr3ne/hadoop-hdfs-*` in every `case.sh`,
  `/u/vnr3ne/.local/bin/z3` in five properties files, JDK paths in five scripts,
  other people's paths in `report.py:65`, `probe.sh:99`, `hdfs-17960/artifacts/*`.
- Tests stub every stage function; 39 of 75 `campaign_*` functions are never
  named by a test.

## 2. Plan

Each phase ends at the same gate: the unit and shell suites, then the nine cases
on one commit through the acceptance workflow (assessor + two skeptics, four
checks). Offline gates (below) run first because a campaign round costs 2-3 h.

### Phase 0 — guard rails (2 days)

- Keep the v15 corpora as fixtures (`~/gc-fixtures/v15/<case>/`): the recorded
  traces, iteration directories and final formulas. Three offline golden checks
  over them, each a script under `tools/golden/`:
  - PLAN: `CausynthTraceRecorder --aggregate` + `ConcolicScheduler` over the
    recorded trace must reproduce `concolic_region_plan.jsonl` and
    `execution_task_plan.jsonl` byte for byte (row order normalised).
  - EXPLORE: `ExploreMain` over `iteration-0000` must reproduce wave 0's
    `obligations.jsonl` ids; `ObligationSolverMain --dry-run` (to add) the 636
    `obligation_query.smt2` of 11741.
  - COMPOSE: `ComposeMain` over each iteration must reproduce
    `claim.kind/valuationOrdinal/polarityDecides/movedRoots` and z3's verdict.
- Fix `ClosurePlanner.seedSession` (prefer the seed when it activated the
  occurrence, else the first admitted session) with a test.
- Delete the dead code every survey confirmed (§1: the occurrence-link half,
  refined-graph fault bindings, unreachable symbolize branches, `clockFloor`,
  the three dead compose methods, `reattribute`, the unused context accessors,
  `ScheduleReportMain` or wire it in). ~−450 lines, byte-identical goldens.

### Phase 1 — fault markers end to end (DESIGN4 §1; 3-4 days)

1. PLAN: the four edits of DESIGN4 §1.3 (scope map, finalizer admission, capture
   port, scheduler). Gate: bug1/bug2/17897 plans carry one
   `EXPLICIT_SYMBOLIC_FAULT` action per marker occurrence; marker
   `DECLARATION_MISSING` rows drop to 0.
2. REPLAY: verify the LOCAL_DEFINITION mint plants `rootAssignment`; delete
   `FaultMarker`'s stale references; publish the MARKER root row.
3. EXPLORE: marker decisions join the flip-site set of their task
   (`ClosurePlanner`); order fault flips first.
4. Shim door markers (`outbound` mints `FAULT:<transport>:SEND`, throws on true);
   delete the hand-written marker from the eight block-key trees; README rule.
5. Acceptance: expected kinds per case revised (MARKER_FLIPPED for hdfs-17899
   bug1/2/3, and 17897 if its marker is the mechanism); the bar names the
   refresh marker. Gate: bug1 MARKER_FLIPPED with the fatal observed in a replay
   whose refresh RPC threw; then all nine.

### Phase 2 — the growth loop (DESIGN4 §3; 5-7 days)

1. `graph.jsonl` per wave (nodes with world, wire/state/thread edges) written by
   ExploreMain from rows; `SlotTable` reduced to the per-world replacement check.
2. Per-world diff and relevance (backward closure from the anchor inside the
   session's own graph).
3. In-wave growth: INSTRUMENT with the grown region set, region-level plan row
   (`EXPOSED_BY`), re-run of the exposing obligation, session replacement in the
   corpus. Needs a `campaign_grow` stage in the driver and an `--exposed-regions`
   input to PLAN/INSTRUMENT (reuse `--retain-regions`).
4. Compose: world-compatible arms replace R3d; `Corpus`'s union graph goes.
5. Delete the epoch machinery (driver 3609-3722, 3947-3992; `SlotTable.unretained`;
   `campaign_max_epochs`; `seedsNextEpoch`).
   Gate: an ExploreTest whose target is reached only through a replay-exposed
   region; bug1's fault world exposes and explores its catch path; the nine
   cases unchanged or improved.

### Phase 3 — compose correctness (3 days)

1. Clock domain per declared symbol (walk `corpus.roots()` for CLOCK rows the
   lowering declared), `clockCells` = that list; every clock reaches
   `clockNecessary` and `movedRoots`.
2. Per-node monotone chain: order each node's clock mints by the seed's `seq`,
   assert `c_i ≤ c_{i+1}`, floor = the recorded reading (forward-only by default;
   a declared backward window per case if a mechanism needs one).
3. `movedRoots` from the unsat core of the pinned query (`wantCore=true`, pins
   are already `:named`), then a re-solve with the unneeded cells pinned; the
   published valuation is the forward-only one.
4. Dedupe: one Sort/Term, delete the SmtNames shims, one `ValueBoxing`, split
   `term()` into indexed/associative codecs with an op table; move the 30-day
   window and the self-check budget into the case declaration.
   Gate: the COMPOSE golden — P4-style refactors byte-identical; the three fixes
   change the text by design and are checked by `(get-value)` over every clock
   symbol (none below its floor, all in `movedRoots` when moved), 17960 unchanged.

### Phase 4 — runtime split (5 days)

1. Recorder vs aggregator: move the offline aggregator, `RuntimeRegionPlanner`,
   `RuntimeRefinedGraphBuilder`, `OccurrenceBinding` to `plan.trace`;
   `UNREGISTERED_SOURCE` to `contract`. Workload-JVM surface −5k lines.
2. One counter, one window: delete `REQUEST_OCCURRENCES`; one `RecordingWindow`
   for Identity/Lineage/`recordingStarted`.
3. Collapse the three frame stacks onto Identity levels; retire trace-v1
   lane/span fields; re-point `RuntimeRegionPlanner.TraceIndex` at the execution
   index first.
4. Split `ConcolicRegionRuntime` (hooks / admission / lifecycle / session);
   `RowRuntime` = rows only, recording-pass refusals routed to the recorder's
   gaps file; retire the toggles and v1 ids; one `RuntimeState.reset()` seam.
   Gate: `activations.jsonl` addresses and `schedule.jsonl` identical for one
   seed per case; runtime unit tests; then the nine cases.

### Phase 5 — PLAN consolidation (5 days)

1. One `Declarations` authority (DESIGN4 §2.3).
2. Delete pass 1 (the skeleton run) after diffing occurrence-address sets of the
   nine recordings.
3. One innermost-owner pass; merge `RuntimeRegionPlanner.plan` into the
   finalizer; one loop-bound and plan-row decoder; split `CausynthPipeline` into
   static discovery and weaver; move the five replay-only classes out of `plan/`.
   Gate: the PLAN golden byte-identical (except the marker actions of Phase 1).

### Phase 6 — EXPLORE consolidation (3 days)

One `World` value type; one admission rule (`SessionReader.admitted`); one dedup
point (`Frontier.open`); `FlipQuery`'s two prefix loops folded into one; `Corpus`
split (corpus view / world index / lowering cache) and moved to a `corpus`
package COMPOSE may import; diagnostics aggregated per (occurrence, site) with a
count. Gate: the EXPLORE golden and the 636 query texts of 11741 byte-identical.

### Phase 7 — driver and harness (3 days)

One declarative case manifest (`case.yaml`: repo, test, target, scope,
declaration files, budgets, expected mechanism) rendered by `run.sh` and read by
`report.py`; a `site.env` for hosts, JDKs, z3, scratch, Maven repos; delete the
seed cache (or fix 7 vs 9), the dead epoch/seeding/keep-glob code; split
`run_engine.sh` by stage with the campaign history moved to `docs/`; move EMIT's
jq schema to a `CampaignEmitMain`; decide the remote pool (keep behind
`campaign_worker_hosts` with a non-ssh test, or delete). Gate: the shell suite, a
fixture-driven end-to-end run over a finished iteration directory, then the nine.

## 3. Order and non-goals

Phases 1-2 change what the engine can find; they come first because the design
questions are about them and the current PASS set does not cover them. Phase 3
fixes published witnesses without changing verdicts. Phases 4-7 remove size and
duplication and are validated by byte-equality, so they are safe to interleave
with campaigns. Every phase lands on `main` only with the nine cases green.

Not in this plan: anything LEAN §5 deleted (carrier layer, offline value
stitching, region-entry container symbols); a Java rewrite of the whole driver;
receive-side faults (a second door, same rule, later).
