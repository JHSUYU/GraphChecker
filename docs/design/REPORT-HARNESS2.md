# REPORT-HARNESS2 — two live gates fixed, four dead blocks deleted

Branch `refactor/d3-harness2` off `refactor/flatten-handoff-next` @ `98aeaba19`.

**Commit tip: `b70e1c7eb`** — *run_engine: two live gates fixed, four dead
blocks deleted*.

`run_engine.sh` **3,014 → 2,857 lines** (−215/+58). Shell helper test green.
No new config key; the printable count stays **41** (`schedule_summaries` was
`r`-only and never printed). One `mvn package` run, clean.

---

## 1. The iteration-manifest digest (item 1)

**Before** — `campaign_publish_iteration_manifest`:

```bash
if ! summaries_sha=$(campaign_digest \
    "${iteration_dir}/concolic_region_summaries.jsonl"); then
  campaign_fail EMIT CAMPAIGN \
    "${iteration_dir}/concolic_region_summaries.jsonl" \
    "failed to digest the imported summaries"
fi
```

`campaign_digest` is `[[ -f "$1" ]] || die`. Nothing has written
`concolic_region_summaries.jsonl` since the Design 3 reduction, so this fired
on **every run that reached PLAN** — the first 17960 run would have died here.

**What the gate must test.** The manifest is published *after EXPLORE and
before COMPOSE* (`do_campaign`, one line after the EXPLORE stage), so
`candidate_composition_manifest.json` and `result.json` **do not exist yet**
and cannot be what it commits to. The artifacts this epoch's own earlier
stages did write, and that every later stage reads, are:

- `session_census.jsonl` — IMPORT builds it and `require_nonempty`s it;
- `obligation_results.jsonl` — EXPLORE creates it (`: >`) and appends each
  wave's verdicts.

**After**:

```bash
if ! census_sha=$(campaign_digest "${census}"); then
  campaign_fail EMIT CAMPAIGN "${census}" \
    "failed to digest the replay session census"
fi
if ! obligations_sha=$(campaign_digest "${obligation_results}"); then
  campaign_fail EMIT CAMPAIGN "${obligation_results}" \
    "failed to digest the obligation verdicts"
fi
```

and the manifest body `importedSummaries: {path, sha256}` becomes
`sessionCensus: {path, sha256}` + `obligationResults: {path, sha256}`
(`run_engine.sh:2072-2073`). The dead file name is gone from the file.

I kept the `campaign_fail EMIT` label to match the two failures already in
that function rather than half-fix it — see §6.

## 2. The epoch-2 death (item 2) — and why the fix is a deletion

**Before**: `campaign_seeding_results` returned
`${iteration_dir}/sessions/${session}` — a **directory** — `campaign_plan`
assigned it to `schedule_summaries`, and `do_schedule` did
`require_file "scheduler summaries"` on it. `[[ -f <dir> ]]` is false, so
**every epoch after the first died there**.

**I verified against the parser, and the option cannot be satisfied by any
artifact this pipeline writes.** `ConcolicScheduler` uses `--summaries` in
exactly two places:

| consumer | requirement | measured |
|---|---|---|
| `exactTargetSummary` (`:1644-1652`) | rows carrying `summaryId`, `goalId`, `regionId`, `occurrenceId` | **`summaryId` has 1 occurrence in all of `src/main/java` — that reader.** No writer, no `region_summaries`/`regionSummaries` anywhere. |
| `RuntimeWorkflowDiscovery.rankedWorkflow` (`:259-262`) | `ClosureMode.ACTIVE_OBSERVED` | run_engine sets `candidate` (default) and `seed-replay` only — `active-observed` is unreachable from the shell. |

So pointing `--summaries` at any existing file (the census, the session rows)
would match nothing and change nothing: a silent no-op replacing a loud
failure, which is worse. **Deleted**: the `--summaries` block in
`do_schedule`, the `schedule_summaries` config row, `campaign_plan`'s `carry`
parameter, `campaign_seeding_results`, and the loop's `carry` variable.

**What a second epoch actually varies is already here and live**:
`--retain-regions`, fed by `campaign_retained_growth` from the divergence
rows ("the retained set must grow: …"). `campaign_plan` is now
`(iteration_dir, retain)` and `do_schedule` passes `--retain-regions`.

The "same seed twice" guard is restated on that quantity:

```bash
# before
if [[ "${seeding_results}" == "${carry}" ]]; then …
# after
if [[ "${retain}" == "${previous_retain}" ]]; then
  campaign_log "epoch e+1 would plan the same retained set as this epoch
(${retain:-none}); the topology is not refining, publishing ${iteration_id}"
  return 0
fi
```

**Test (new, EPOCH-2)** — replaces the assertion that
`campaign_seeding_results` returns a session directory, which asserted the bug:
it stubs `run_java_main`, drives `do_schedule` with
`schedule_retain_regions=REGION.grown`, and asserts the scheduler is called
**with** `--retain-regions REGION.grown`, **without** `--summaries`, and that
`campaign_seeding_results` no longer exists.

## 3. `campaign_json` (item 3)

Deleted: 115 lines, zero callers, and the script's **only** `python3`
invocation. With it went `campaign_preflight`'s
`require_command_available python3` — the script no longer has that
dependency, and requiring a tool it never runs is a false precondition.
`grep -n python3 run_engine.sh` now returns nothing.

## 4. `VALIDATE` → `PREFLIGHT` (item 4)

`campaign_stage VALIDATE campaign_validate` wrote the label `VALIDATE` into
`stage_metrics.tsv` on every run, while `ComposeMain:40`, `ClaimPolicy:21` and
`CompositionManifest:12` all state the VALIDATE **stage** is gone. It is a
pre-flight config check (`validate_config` + `require_command_available` ×2).
Renamed both the label and the function: `campaign_preflight`
(`run_engine.sh:1126`, `:2701`). Nothing in the tree now reads as a validation
stage.

## 5. DEAD-3 / 4 / 5 / 6

**DEAD-4 — the one that was destroying evidence.** `campaign_collect_diagnostics`
ran `find "${iteration_dir}" -name 'campaign_gaps.jsonl' -not -path "${gaps}"`
where `${gaps}` *is* that path, so the merge list was always empty and the
function's entire effect was `: >"${gaps}"`.

**The rows it discarded, and where they go now:**

| row | written at | was truncated by |
|---|---|---|
| `GAP_ROW` / `ADMISSION_GAP` / `DIAGNOSTIC`, subject `REGION_PATH_WAVE_BUDGET_REACHED` or `REGION_PATH_CLOSURE_NO_PROGRESS` | `campaign_explore`, on the wave-stop path | the collector call **one line later** in `do_campaign` |
| `GAP_ROW` / `TOPOLOGY_DIVERGENCE` / `DIAGNOSTIC`, subject = the epoch id | `campaign_publish_pending_refinement` | that function's **own last line**, which called the collector |

EMIT then read the emptied file into `gaps.json`, so **neither kind has ever
appeared in a published gap report**. That is a Rule 5 violation in the
strongest form: the rows existed, were written, and were deleted before the
reader.

Fixed by deleting the collector and both call sites.
`${iteration_dir}/campaign_gaps.jsonl` is now append-only — whoever raises a
row appends, EMIT reads it once at `campaign_write_gaps`. Nothing truncates
it. The comment block that replaced the function records the bug so it is not
re-introduced.

**DEAD-3** `campaign_publish_bound_gap` (function + call site) — unreachable,
and doubly stale: it emitted `byStage {CLASSIFY: 1}` and `stage: "CLASSIFY"`
for a deleted stage, and wrote `>"${campaign_final}/gaps.json"`, **over the
top of the gap report EMIT had already published** for the last completed
epoch. Deleted. The loop's fall-through is not left silent — an exhausted
`campaign_max_iterations` now `die`s naming the bound and the published
campaign root, and overwrites nothing.

**DEAD-5** the `[[ -z "${seeding_results}" || ! -s "${seeding_results}" ]]`
guard — both disjuncts always false; gone with the `carry` chain.

**DEAD-6** `CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT` — not a config key, no
experiment exports it, reachable only by a hand-typed `env`; also the file's
only bare-string stage comparison. Deleted.

> **This one contradicts advice I gave you.** REPORT-LAUNCH §1.2 and §3
> recommended `CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT` as the cheap gate on M2's
> re-recording (~270–310 s per case instead of 750–3,800 s). That option no
> longer exists. If you still want the measurement run, the honest form is a
> declared config key with a `k` flag and a row in the table — say the word and
> it is a four-line change — not an undeclared env switch. Until then, the
> M2 gate has to read `session_census.jsonl` out of a full run.

## 6. Out of scope, measured, not touched

**DEAD-7 (stage labels).** `campaign_fail CACHE` (6 sites) names a stage the
pipeline does not have; there is no `campaign_fail INSTRUMENT` and no
`campaign_fail DECIDE`, so two of the nine stages cannot name themselves in a
failure; and the three `campaign_fail EMIT` calls in
`campaign_publish_iteration_manifest` fire before COMPOSE, never during EMIT.
I left all of them alone rather than fix two of nine — my two new failures in
that function use `EMIT` to match its existing convention. It is a coherent
one-commit change if you want it.

**Not in this branch** (REPORT-SHRINK §4b items 2–4): the Java deletions
(`BoundedLoopComposition`, `PathObservation`/`LocalCaseIdentity`,
`SymbolicPropagationClosure`), one of which needs a one-line import removal in
`ConcolicRegionRuntime.java` — the runtime agent's file.

**Also still standing**: the dead 7th TSV column (`target_reach`, read into a
variable nobody uses and missing from both `local` declarations, so it leaks
globally) at `run_engine.sh:1569` and `:2010`, and the stale config comment
above `solver_timeout_ms`.

## 7. Verification

| check | result |
|---|---|
| `bash -n run_engine.sh` | ok |
| `mvn -o -DskipTests package` | ok |
| `run_engine_campaign_helpers_test.sh` | **passed** |
| printable config keys | **41**, unchanged |
| `grep -n python3 run_engine.sh` | no hits |
| `grep -n concolic_region_summaries` | no hits |
| `campaign_json` / `campaign_collect_diagnostics` / `campaign_publish_bound_gap` / `campaign_seeding_results` / `schedule_summaries` | no hits |
