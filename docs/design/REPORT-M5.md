# REPORT-M5 — run_engine.sh reduced to the Design 3 stages

Branch `refactor/d3-contract`, tip `058ee2491` (D at `b076a1943`, staging
`19b311384` merged in between). `mvn -o -q test` green (62 @Test);
`src/test/shell/run_engine_campaign_helpers_test.sh` green.

| | before (`9b9961b0a`) | after | delta |
|---|---|---|---|
| `run_engine.sh` | 4,094 | **2,933** | **−1,161 (−28%)** |
| shell functions | 114 | **88** | −26 |
| helper test | 811 | 694 | −117 |
| config keys printed | 43 | 42 | −1 (`composer`) |

## The pipeline

`VALIDATE → FREEZE_TOOL → [SETUP] → FREEZE → SEED`, then per epoch
`PLAN → INSTRUMENT → REPLAY(seed, focused) → IMPORT → EXPLORE → COMPOSE →
SOLVE → DECIDE → EMIT`, iterating while `campaign_topology_divergences` counts
`TOPOLOGY_DIVERGENCE` GapRows and a divergent session names the next seed.
The stage *sequence* was already this; what changed is what each stage does.

### REPLAY — a session, not a result file
`campaign_replay` now exports `CAUSYNTH_CONCOLIC_SESSIONS=<dir>` beside the
existing task-plan/results/classes variables, and `campaign_session_replay`
points it at `<iteration>/sessions`. Every focused replay — seed and
obligation alike — writes its rows there under its own session id.

### IMPORT — per-kind files, no folding
`campaign_import_session` checks that each session directory published
`activations, decisions, exports, attaches, writes, reads, roots, targets,
gaps` (`.jsonl`) plus `expressions.json`, and publishes
`session_census.jsonl` (one row per session × kind). **Deleted**: `do_import`
and the whole `ConcolicSummaryImporter` invocation, the import cache
(`campaign_import_cache_key` / `restore` / `store`, 91 lines), the per-member
summary fan-out, and `import_diagnostics.jsonl` as a campaign-wide artifact.

### EXPLORE — one planner, one worker per obligation
```
campaign_explore:  loop { d3.explore.ExploreMain --sessions --task-plan
                            --results --topology-epoch --wave --output-dir
                            [--root-domains] [--max-*]   →  obligations.jsonl
                          ∥ campaign_obligation_worker per obligation
                          collect obligation_result.jsonl, deterministically }
campaign_obligation_worker: d3.explore.ObligationSolverMain --obligations
                            --obligation-id --sessions --output-dir --z3
                            --solver-timeout-ms --clock-skew-ms
                            → SAT_MODEL_READY ⇒ focused campaign_replay
```
A wave stops on `region_path_max_waves` or on a fixed point over
(obligation ids × verdicts so far); the stop is written as a `GAP_ROW`
(`ADMISSION_GAP`, `DIAGNOSTIC`) onto `campaign_gaps.jsonl`, never a failure.
**Deleted** (with linked replay): the per-member roster and per-member
`obligations-NNNN` directories, `campaign_report_worklist`,
`campaign_report_wave`, `campaign_decode_worklist_keys`,
`campaign_publish_wave` (72 lines of cross-member summary merging),
`campaign_explore_stop`, `campaign_path_closures_json`,
`campaign_materialize_path_closures`, `campaign_record_exploration`,
`campaign_publish_primary_record`, `campaign_target_reach_query` and
`campaign_member_reach_query` (the `TargetReachPathQueryBuilder` wiring), and
the `pathSetClosed` stamping pass over the corpus.

### COMPOSE / SOLVE / DECIDE — one anchor
`campaign_compose` runs `d3.compose.ComposeMain --sessions --runtime-plan
--output --manifest --clock-skew-ms --z3 [--anchor] [--root-domains]` once,
into `<iteration>/final/`. `campaign_solve` solves that one formula
(`RootValuationSolver`, unchanged). `campaign_decide` prints the claim
`ClaimPolicy` reached. **Deleted**: `campaign_compose_occurrence`,
`campaign_compose_unscheduled`, `campaign_occurrence_key`,
`campaign_report_target_occurrence`, `campaign_solve_report`, the
`final/targets/<key>/` fan-out, `target_occurrence_reports.jsonl`,
`target_occurrences.json` and the `TargetOccurrenceElection` invocation — D5
had already made the declaration the answer in Java.

### EMIT — partition, don't classify
`campaign_write_gaps` (95 lines) replaces `campaign_write_coverage_gaps`
(190). Sources: every session's `gaps.jsonl` + `campaign_gaps.jsonl` (each row
states its own `gapClass`), the composer's `finalStatusRefusals` (blocking by
construction) and its own gap rows, and the static-catalog / runtime-plan gaps
(no class of their own → the ledger, blocking by default). **Deleted**:
`sliceVerdict`, `portVerdict`'s inputs `campaign_attached_handoff_phases_json`
and `campaign_replay_wave_json`, the flip-wave demotion, and the three
conditional code lists in the published `gapLedger` block.

## Compatibility kept
- Frozen-input discipline: `campaign_freeze`, `campaign_freeze_digest`,
  `campaign_verify_frozen_inputs` and EMIT's re-hash before publishing.
- `campaign_log`, `stage_metrics.tsv` (now `COMPOSE[anchor]` / `SOLVE[anchor]`
  instead of one row per occurrence), `run-manifest.json`, the summary lines.
- `result.json`: `claim`, `claimReason`, `blockers`, `blockerCount`,
  `whyNotAccepted`, `reachability`, `solverState`, `finalStatus`,
  `finalStatusRefusals`, `evidence`, `gapCount`, `telemetryCount`, `accepted`,
  `blockingGapCodes`, `witnessFindings`, `reportedFindings`, `rootSpace`,
  `valuations` — unchanged. `targetOccurrence` now names the composed anchor;
  `targetOccurrences` / `targetOccurrenceReason` are gone (one anchor, no
  runners-up). Exit codes 0 / 2 (no accepted candidate) / 3 (blocking gaps)
  unchanged.
- `campaign_publish_epoch_final` still publishes the last epoch at
  `${campaign_root}/final`, from EMIT, whatever the claim.

## Helper test: folded, not dropped
Every check that pinned a deleted mechanism now pins its replacement. Session
gap rows replace import diagnostics (GAP-4 gains a second half: a row that
states `DIAGNOSTIC` is taken at its word). The wave's deterministic verdict
collection replaces `campaign_publish_wave`. One anchor replaces the election
ledger (COMPOSE-1, DECIDE-1). The oversized-argv check now builds a
1,600-row session `gaps.jsonl` instead of a 1,600-event handoff index — the
limit it guards is unchanged, the document that exceeds it is the one the new
fold reads. The `campaign_occurrence_key` and `campaign_record_exploration`
byte-for-byte checks are deleted with their functions.

## What the shell now calls that does not exist yet
`d3.explore.ExploreMain`, `d3.explore.ObligationSolverMain` and
`d3.compose.ComposeMain` are wired to the CLI names in CONTRACT-SPEC and land
with `refactor/d3-explore` / `refactor/d3-compose`. Until then a campaign
reaches EXPLORE and stops there; every stage before it runs unchanged.

Consequence worth naming: the old EXPLORE/COMPOSE Java now has **no shell
caller at all** — `ConcolicPathFlipPlanner`, `ConcolicPathFlipSolver`,
`ConcolicSummaryImporter`, `PathMergeComposer`, `TargetReachPathQueryBuilder`,
`TargetOccurrenceElection`. They are not deleted here (M3/M4 own their
replacements, and REPORT-D §"Not deleted" lists what each still holds up), but
after this commit nothing in the pipeline invokes them, so deleting them costs
nothing beyond their tests once the new CLIs land.

---

## Follow-ups (tip `f0be67b87`)

Four mismatches between the M5 stages and the CLIs that actually landed, found
by M4 (REPORT-M4 §run_engine mismatches) and M3 (REPORT-M3 §8), all folded in.

1. **SOLVE no longer shells a solver.** `do_reach` invoked
   `concolic.RootValuationSolver`, which D2-3 deletes. `ComposeMain` runs z3
   per valuation while it composes — it has the root domains, the selectors
   and the formula in hand — and writes `state`, `reachability`, `valuations`
   and the claim into the manifest under `solver`. A second process would
   re-derive from artifacts what the first already decided, so `campaign_solve`
   reads that manifest and checks the verdict is there. It stays a stage:
   that is where a reader looks for the solver's answer and where its wall
   time is recorded. `reach_max_inputs` and `reach_max_valuations` went with
   the process they bounded (42 config keys → 40).
2. **gaps.json and gap_ledger.json still exist for `campaign_artifact_digests`.**
   `campaign_write_gaps` builds gaps.json from the manifest's
   `.finalStatusRefusals` (blocking by construction), `.gaps` and
   `.claim.gaps` (each row's own class, blocking when it states none), plus
   the session gap rows and the static/plan gaps the ledger classes.
   `campaign_write_gap_ledger` still runs `contract.GapLedger`, which survives
   D2 with 45 registered codes.
3. **An empty obligations file is the frontier closing, not a failure.**
   `campaign_explore` did `require_nonempty` on it, so ExploreMain had to write
   a blank-id marker row to survive its own success; it now breaks cleanly and
   **the marker can go** — M3 owner please remove it.
4. **`--root-domains` reaches the obligation worker**, and ExploreMain is
   passed `--target-occurrence` like every other target-directed stage;
   ComposeMain is passed `--timeout-ms`. The shell now uses exactly the flags
   the three mains declare.

`ComposeMain` accepts `--clock-skew-ms` and `--runtime-plan` and ignores them;
the campaign keeps passing both.
