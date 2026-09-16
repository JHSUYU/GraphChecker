# REPORT-LAUNCH — running one case end to end on the refactored pipeline

Read-only. Staging `refactor/flatten-handoff-next` head **`132397cb2`**
(contains `a29e5c8df`). No file edited; every edit below is proposed.

**Headline: the pipeline will run, and the harness will report `FAIL` on every
case regardless of the verdict.** `probe_final.sh` reads three artifacts the
Design 3 stages no longer write (`z3-result.json`, and the manifest's
`recordedRootValues` / `configuredSourceMaterializations`), so `terms` is
always empty, the probe writes `buggy NO_ROOT`, and `report_final.py`'s
`buggy != "sat"` gate refuses the run. §2 gives the four-line fix, and it is
not a loosening: the composer now computes the same assertion the probe was
reconstructing, and ClaimPolicy already refuses a claim without it.

---

## 1. Running one case

### 1.1 Build first (one build step)

`$SP/wt-stage` is at `800a0b4b5`, **not** the head. The jar must be rebuilt at
`132397cb2` before anything runs; `run_branch.sh` resolves the jar from the
repo root it is given (`workflow_path_base=project` →
`<repo>/target/…jar`), so the repo root and the jar must be the same tree.

```
cd <staging worktree at 132397cb2> && mvn -q -o -DskipTests package
```

### 1.2 The command

```bash
SP=/tmp/claude-20003/-opt-GraphChecker/99c84a54-86ac-44a4-a030-760f664ae2a1/scratchpad
STAGE=$SP/wt-stage                     # must be at 132397cb2
OUT=<your scratchpad>/laneD3A          # fresh; the campaign refuses a reused root

env \
  FINAL_SP="$SP" \
  JAR="$STAGE/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar" \
  CAUSYNTH_CUSTOM_JDK_HOME="$SP/images/j2sdk-image-build16" \
  OUT="$OUT" \
  CASES="hdfs-17960" \
  FINAL_KEEP_ALL=1 \
  MIN_FREE_GB=6 DISK_WAIT_SECONDS=1800 \
  CASE_TIMEOUT_SECONDS=21600 \
  RUN_BRANCH="$SP/verify/run_branch.sh" \
  bash "$SP/final/accept_final.sh"
```

Notes that matter:

- **`JAR` sets the repo root**: `REPO=$(dirname $(dirname $JAR))`, and the
  preflight requires `$REPO/experiments/hadoop`. Pointing `JAR` at a jar
  outside the worktree silently runs another tree's `run_engine.sh`.
- **`CAUSYNTH_CUSTOM_JDK_HOME`** is read twice — by `accept_final.sh` as `IMG`
  and passed on as both `CUSTOM_JDK_HOME` and `CAUSYNTH_CUSTOM_JDK_HOME` — and
  overrides `workflow.properties`' relative `custom_jdk_home`, which in a
  worktree points at an unbuilt image. The build16 image is
  `OpenJDK 64-Bit Zero VM (25.71-b00) … 1.8.0-internal-_2026_09_14_00_06-b00`.
- **`DRY=1`** runs the preflight and prints the exact per-case command without
  starting anything. Use it once before the first real run.
- **`FINAL_KEEP_ALL=1`** skips pruning — required for a first run on the new
  stages, because `FINAL_KEEP_GLOBS` in `lib_final.sh` names **none** of the
  Design 3 artifacts (`sessions/`, `slots.jsonl`, `obligations-*/`,
  `session_census.jsonl`, `obligation_results.jsonl`). Without it the first
  thing the harness does after a case is delete the evidence of the stages
  under test.
- **Disk**: `/` is at **6.7 G free** against `MIN_FREE_GB=6`. With
  `FINAL_KEEP_ALL=1` a case keeps 94–192 MB (round-2 measurements), so one
  case is fine, but six unpruned plus another agent's lane is not. Either run
  in two batches or raise the cap after reading each case.
- **Stopping**: `$OUT/pgid` holds the group; `kill -TERM -$(cat $OUT/pgid)`
  stops exactly this run.
- **Measurement-only runs**: `CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT` returns
  after IMPORT (run_engine `do_campaign`). That is the cheap gate for M2's
  re-recording — seed session + census — without paying for EXPLORE..EMIT.

### 1.3 What lands under OUT

`run_branch.sh` sets `CAUSYNTH_OUTPUT_DIR=$OUT/out/<case>`, and run_engine
derives `schedule_output_dir=<that>/schedule` (`run_engine.sh:328`), which is
the campaign root.

```
OUT/logs/<case>.log                  validate + campaign stdout
OUT/logs/<case>.status               exit=/elapsed=
OUT/logs/<case>.driver.log           accept_final's own capture
OUT/summaries/<case>.tsv
OUT/report/<case>/{status,probe.tsv,probe.log,probe/,row.tsv,report.md,fatal_arms.json}
OUT/summary.tsv                      the harness table (header + one row per case)
OUT/pgid
OUT/out/<case>/                      = CAUSYNTH_OUTPUT_DIR
```

Inside `OUT/out/<case>/`, by stage:

| stage | artifact |
|---|---|
| *(analyze, pre-campaign)* | `candidate_dataflow_edges.jsonl.gz`, `communication_call_sites.jsonl.gz`, `communication_gaps.jsonl.gz`, `region_skeletons.jsonl.gz`, `retained_loops.jsonl.gz`, `target_resolved.json`, `runtime/concolic_region_plan.jsonl`, `runtime/refined_dataflow_edges.jsonl.gz` |
| FREEZE / SEED | `schedule/frozen-inputs/`, `schedule/seed-manifest.json`, `schedule/seed-skeletons/`, `schedule/stage_metrics.tsv` |
| **PLAN**`[n]` | `schedule/iteration-000n/execution_task_plan.jsonl`, `runtime_workflow_schedule_index.json`, `concolic_region_plan.jsonl` (frozen copy), `seed-replay/{execution_task_plan.jsonl,runtime_workflow_schedule_index.json}`, `workers/<taskId>/execution_task_plan.jsonl` (hard links) |
| **INSTRUMENT** | `iteration-000n/instrumented-classes/` |
| **REPLAY** | `iteration-000n/seed-result/concolic_region_results.jsonl`, `seed-result/focused/`, and **`iteration-000n/sessions/<sessionId>/`** |
| **IMPORT** | per session: `activations, decisions, exports, attaches, writes, reads, roots, targets, gaps` `.jsonl` + `expressions.json`; census at `iteration-000n/session_census.jsonl` |
| **EXPLORE** | per wave `iteration-000n/obligations-%04d/{obligations.jsonl, tasks.jsonl, gaps.jsonl, root-domains.jsonl, explore_manifest.json, stdout.log, stderr.log}` and one dir per obligation id; wave-crossing: `iteration-000n/obligation_results.jsonl`, `iteration-000n/campaign_gaps.jsonl`, and **`iteration-000n/slots.jsonl`** (iteration-level, written by `ExploreMain`, read by `Composer`) |
| **COMPOSE** | `iteration-000n/final/candidate.smt2`, `candidate_composition_manifest.json`, `compose.log` |
| **SOLVE** | *no new file* — the verdict is `…manifest.json.solver` (state, reachability, valuations, symbolicVariableModels, campaignClaim); the stage only checks it is there |
| **DECIDE** | *no new file* — prints anchor/finalStatus/claim/blockers to the log |
| **EMIT** | `iteration-000n/final/{gap_ledger.json, gaps.json, result.json, run-manifest.json}`, then `campaign_publish_epoch_final` copies the epoch's `final/` to **`schedule/final/`** |
| epoch loop | `iteration-000n/iteration_manifest.json` per epoch; a new `iteration-000(n+1)/` only on a topology divergence that names a seeding replay |

**Three names in the brief that do not exist**: there is no `manifest.json`
(it is `candidate_composition_manifest.json`; `explore_manifest.json` is
per-wave, `iteration_manifest.json` per epoch, `run-manifest.json` in final)
and no `claim.json` — the claim lives in `result.json.claim` and in
`candidate_composition_manifest.json.solver.campaignClaim`. `tasks.jsonl` is
per wave, not a top-level file.

## 2. What decides PASS/FAIL, and every mismatch

`accept_final.sh` decides nothing itself. It runs the case, then
`probe_final.sh` (which writes `probe.tsv`), then `report_final.py`, which
writes `row.tsv` — appended to `summary.tsv` — and prints
`<case>: <verdict> (<reason>)`.

### 2.1 The gate as written

`report_final.py:224-238`, reading `schedule/final/result.json`:

```python
if claim        != "SAT_CANDIDATE":  reasons.append("claim=%s" % claim)
if blockers:                         reasons.append("blockers=%s" % ...)   # result.blockers[].code
if final_status != "FINAL_READY":    reasons.append("finalStatus=%s" % ...)
if buggy        != "sat":            reasons.append("probe buggy=%s" % buggy)
verdict = "PASS" if not reasons else "FAIL"
```

`summary.tsv` columns (13):
`case, exit, elapsed, claim, finalStatus, blockers, gaps, plain, buggy, other,
verdict, reason, finding`.

run_engine exit codes (`campaign_emit`): **0** accepted; **2** when
`claim ∉ {SAT_CANDIDATE, UNSAT_CLOSED}`; **3** when `gapCount > 0`. The
harness records `exit` but never gates on it — the gate is result.json — which
is right, and it is why the EMIT publish fix (`campaign_publish_epoch_final`
inside `campaign_emit`) matters: on exit 2/3 the artifacts still exist.

### 2.2 The good news: the acceptance vocabulary did not move

`ComposeMain.campaignClaim` still publishes `SAT_CANDIDATE` /
`UNSAT_CLOSED` / `INCONCLUSIVE_PARTIAL` in `campaignClaim.claim`, and
`finalStatus` is still `FINAL_READY` / `FINAL_REFUSED`. The six Design 3
mechanisms are published **beside** it as `findingKind`. So three of the four
gate conditions work unchanged. `blockers` and `gapCount` likewise.

### 2.3 M1 (blocking) — the probe cannot decide anything

`probe_final.sh:140` takes its Boolean roots from
`reach["roots"]["booleanInputs"]`, where `reach = load("z3-result.json")`.
**`z3-result.json` is written nowhere at `132397cb2`** (`git grep` over
`run_engine.sh` and `src/main/java`: zero hits) — SOLVE now reads the
composition manifest instead. `load()` swallows the missing file, so
`markers = []`.

The one fallback (`probe_final.sh:144-148`) greps `candidate.smt2` for
`sym__HDFS_CONFIG_SNAPSHOT_DELETION_ORDERED`. That is the **old** naming;
`d3` has no `sym__` prefix anywhere (the composer's root assertions are
`root_domain__<n>`). So the fallback fails too, on the one case it existed
for.

With `terms == []` the probe writes `NO_ROOT` and exits 0
(`probe_final.sh:204-209`, `:383`), `probes["buggy"] == "NO_ROOT"`, and the
fourth condition refuses **every case** — including one where EMIT exited 0
with `SAT_CANDIDATE`, `FINAL_READY`, 0 gaps. Round 2 already showed the
symptom on bug2/bug3 (`probe buggy=NO_ROOT`); at `132397cb2` it becomes
universal.

Two further reads that are now dead but harmless (they degrade the narrative
columns, not the verdict): `manifest.recordedRootValues` and
`manifest.configuredSourceMaterializations` — neither key is published by the
new manifest (`recordedRootValues` exists only as a private `CorpusIndex`
map) — so `recorded` is empty and the probe would answer
`UNSTATED_RECORDED_VALUE` even if it had terms.

### 2.4 M2 (blocking for the `finding` column) — `findingKind` never reaches result.json

`campaign_emit`'s jq copies `claim, claimReason, blockers, blockerCount,
whyNotAccepted, witnessFindings, rootSpace` out of `campaignClaim` — but
**not `findingKind`, `polarityDecides`, `valuationOrdinal`, `movedRoots`**,
all four of which ComposeMain publishes there. So the mechanism the six cases
are judged on never leaves the composition manifest, and
`NO_SUPPORTED_WITNESS` — which surfaces only as `findingKind` — is invisible
in `result.json`.

### 2.5 M3 (cosmetic) — the witness-finding row shape changed

`report_final.py` looks for `row["accepted"] is True`, or
`row["status"]=="sat" and row["verdict"]=="EXPLAINED"`, and prints
`row["narrative"]`. The new finding row is
`{findingKind, valuationOrdinal, movedRoots, polarityDecides}` — none of those
keys. Also `rootSpace.acceptedWitnessKind` → **`acceptedFindingKind`**, and
`reportedFindings` no longer carries `code: "NOT_A_MECHANISM"`. Net effect:
the `finding` column and the report's "Witness findings" section degrade to
`?`/`-`. **The verdict is unaffected** — no gate reads them.

### 2.6 The edit

**Do not weaken the gate by deleting the fourth condition.** Replace it with
the assertion the composer now makes itself. `ClaimPolicy:148` sets
`polarityDecides = recorded outcome (valuation ordinal 0) is unsat` — the
*same* statement the probe's two-polarity run was reconstructing, computed by
the code that holds the formula and the domains. And it is already a
**condition**, not a field: `ClaimPolicy:173/192` refuse MARKER_FLIPPED and
CLOCK_SKEW outright when it is false, raising `undecidedPolarity` and falling
through to `NO_SUPPORTED_WITNESS`. Separately, a formula satisfiable at the
recorded valuation raises `FORMULA_SAT_AT_RECORDED_VALUATION`, which the
ledger classes BLOCKING. So the probe adds nothing the pipeline does not now
assert — and asserts it on a shape the probe cannot read.

**Edit A — `run_engine.sh`, `campaign_emit`, inside the `jq -n` that writes
`result.json`** (after the `whyNotAccepted` line, ~`:2525`):

```
 claim: $decided.claim,
 claimReason: $decided.claimReason,
 blockers: $decided.blockers,
 blockerCount: $decided.blockerCount,
 whyNotAccepted: $decided.whyNotAccepted,
+# WHICH mechanism the formula supports, beside WHETHER the run is accepted.
+# The two are different questions and the report needs both.
+findingKind: ($decided.findingKind // ""),
+polarityDecides: ($decided.polarityDecides // false),
+valuationOrdinal: ($decided.valuationOrdinal // 0),
+movedRoots: ($decided.movedRoots // {}),
 reachability: $reachability,
```

**Edit B — `report_final.py`**, replace the probe condition (`:235-236`) and
read the new fields (`:120-126`):

```python
 claim        = result.get("claim", "MISSING")
 final_status = result.get("finalStatus", "MISSING")
+finding_kind = result.get("findingKind", "MISSING")
+polarity     = result.get("polarityDecides", False)

 ACCEPTED_FINDINGS = {"MARKER_FLIPPED", "CLOCK_SKEW",
                      "MESSAGE_PAIRING_FLIPPED", "STATE_PAIRING_FLIPPED",
                      "RECORDED_FAILURE_EXPLAINED"}
 ...
-if buggy != "sat":
-    reasons.append("probe buggy=%s" % buggy)
+if finding_kind == "NO_SUPPORTED_WITNESS":
+    reasons.append("findingKind=NO_SUPPORTED_WITNESS (%s)"
+                   % result.get("claimReason", "no reason published"))
+elif finding_kind not in ACCEPTED_FINDINGS:
+    reasons.append("findingKind=%s" % finding_kind)
+elif not polarity and finding_kind != "RECORDED_FAILURE_EXPLAINED":
+    reasons.append("polarityDecides=false: the formula was satisfiable at the"
+                   " recorded valuation, so the mechanism explains nothing")
```

The `RECORDED_FAILURE_EXPLAINED` exemption is not a loophole: `ClaimPolicy:215`
constructs exactly that kind with `polarityDecides = false` by definition —
the seed run itself observed the fatal arm, so there is no other polarity to
refute.

**Edit C — the `finding` column.** With `findingKind` in result.json, set

```python
note = "%s valuation %s%s" % (finding_kind,
        result.get("valuationOrdinal", "?"),
        (" moving %s" % result["movedRoots"]) if result.get("movedRoots") else "")
```

and stop reading `witnessFindings`/`acceptedWitnessKind`. Keep the `plain`,
`buggy`, `other` columns as reported-not-required, so a probe that later reads
the new shape still has a home.

**Edit D — `lib_final.sh`, `FINAL_KEEP_GLOBS`.** It names no Design 3
artifact. Until it does, every run needs `FINAL_KEEP_ALL=1`. The minimal
addition:

```
'schedule/final/gap_ledger.json'
'schedule/iteration-0000/session_census.jsonl'
'schedule/iteration-0000/slots.jsonl'
'schedule/iteration-0000/obligation_results.jsonl'
'schedule/iteration-0000/campaign_gaps.jsonl'
'schedule/iteration-0000/sessions/*/*.jsonl'
'schedule/iteration-0000/obligations-*/obligations.jsonl'
'schedule/iteration-0000/obligations-*/tasks.jsonl'
'schedule/iteration-0000/obligations-*/gaps.jsonl'
'schedule/iteration-0000/obligations-*/explore_manifest.json'
```

(`fin_prune_case` uses literal `[[ -e ]]` tests, so globs need a loop — cheap,
but it is a real change, not a one-liner.)

**Not recommended**: repairing `probe_final.sh` to read the new roots. It
would re-derive, outside the composer, the polarity the composer already
decided — the exact duplication REPORT-REVIEW-M3 F3 and REPORT-REVIEW-M4 keep
finding. Keep the probe as an independent *reported* signal once someone
teaches it the new names; do not gate on it.

## 3. Config keys

The table is **byte-identical** to `e507f365c` (diff of the key list: no
change), **43 rows**. REPORT-CASES §3 stands unchanged, so in short:

| key | status |
|---|---|
| `compose_max_valuations` (default **16**) | read at `:589` as `--max-valuations`; **no case sets it** |
| `clock_skew_ms` (default 300000, accepts `unbounded`) | set by 11741/17897/17899; **17960 unset** |
| `region_path_max_waves` (default 12), `region_path_max_tasks` | read into EXPLORE's `--max-waves`/`--max-tasks`; no case sets `max_tasks`, so `ClosurePlanner.DEFAULT_MAX_TASKS = 64` applies (REPORT-REVIEW-M3 F2) |
| `declared_target_occurrence` | 11741/17897 in `workflow.properties`, 17899 via `case.sh`→`run.sh`; **17960 has none — COMPOSE refuses to start** (REPORT-CASES B1) |

**Unknown keys the six cases still set** — dropped in silence by
`known_config_key … || continue` (`run_engine.sh:157`):

| key | set in |
|---|---|
| `reach_max_inputs=8` | all four `workflow.properties` (11741:27, 17897:36, 17899:17, 17960:25) |
| `reach_max_valuations=128` | all four (11741:28, 17897:37, 17899:18, 17960:26) |

Nothing else is unknown: `schedule_max_jobs`, `solver_timeout_ms`,
`concolic_worker_count`, `campaign_max_iterations` are all in the table.
One more thing a reader should know: **`campaign_max_epochs=3` is a hardcoded
shell local** (`run_engine.sh:2777`), not a config key — the epoch bound
cannot be set per case.

## 4. Order and expected wall time

Measured per-case totals from my lanes (jar `9b9961b0a` and earlier, PARALLEL=1):

| case | measured elapsed | dominant stage |
|---|---|---|
| 17960 | **562 s** | — (single node, no closure) |
| 17897 | **749 / 792 / 794 s** | EXPLORE 365 s, REPLAY 173 s, SOLVE 87 s |
| bug3 | **672 / 1,041 / 1,127 s** | EXPLORE 446 s, SOLVE 226 s, REPLAY 201 s |
| bug2 | **1,507 / 1,626 s** | EXPLORE 861 s, SOLVE 254 s, REPLAY 203 s |
| bug1 | **2,930 s** (6,377 s on a stale jar) | — |
| 11741 | **3,764 s** | — |

Fixed floor on every case: SEED 63–87 s, INSTRUMENT 17–20 s, FREEZE ~2 s,
PLAN/IMPORT/DECIDE < 5 s each.

**One shift to expect at `132397cb2`**: SOLVE no longer runs z3 — ComposeMain
runs it per valuation while composing — so the 87–254 s that used to appear
under `SOLVE[<anchor>]` moves into `COMPOSE[n]`, which was 18–51 s. Totals
should be comparable; per-stage rows will not be. Budget by the **total**
column above, not by the old COMPOSE number.

**The order I would run, and why it differs slightly from yours**:

1. **17960** — the control, cheapest (562 s), single node, no closure. But
   run it **only after REPORT-CASES B1 is applied**: without
   `declared_target_occurrence` it dies at COMPOSE, and a control that fails
   for a configuration reason teaches nothing about the refactor.
2. **17897** (~790 s) before **bug3** (~1,000 s) — swapping your order. 17897
   is cheaper, its declaration resolves cleanly, and it is the case whose
   E1 behaviour round 2 measured most completely, so it is the best second
   data point. bug3 adds the `EXPLICIT_SYMBOLIC_FAULT` marker question
   (REPORT-CASES N1) on top of everything 17897 exercises — one variable at a
   time.
3. **bug3** (~1,000 s), then **bug2** (~1,550 s) — same anchor region, bug2
   costs 2× bug3 in EXPLORE for the same shape.
4. **bug1** (~2,930 s) before **11741** (~3,764 s) — swapping your last two.
   bug1 is cheaper and its known failure (four
   `PATH_NOT_SELF_CONSISTENT` from one clock symbol shared by two replays'
   paths, REPORT-ROUND1) is precisely what per-task admission is supposed to
   fix, so it is the strongest single test of the refactor's core claim. Run
   11741 last: it is the most expensive, and it is the case round 2 never
   reached, so it is the one with the least prior to compare against.

Two lanes are permitted (the concurrency ruling), so the practical schedule is
**queue A: 17960 → bug3 → bug2 → bug1** (≈ 6,000 s) and
**queue B: 17897 → 11741** (≈ 4,550 s), which finishes in about
1 h 40 m wall. Do not start either until the M2 re-recording is in the jar
under test — every number above is from the pre-refactor runtime.

## 5. Apply order

1. REPORT-CASES **B1** (17960's anchor) — otherwise the control cannot run.
2. **Edit A** (EMIT publishes `findingKind`/`polarityDecides`) — one jq block,
   in run_engine, testable by the shell helper test.
3. **Edit B + C** (`report_final.py` gate and `finding` column).
4. **Edit D** (`FINAL_KEEP_GLOBS`), or keep `FINAL_KEEP_ALL=1` and watch disk.
5. Then the six, in §4's order.
