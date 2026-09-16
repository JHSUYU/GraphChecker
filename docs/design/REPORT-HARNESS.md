# REPORT-HARNESS — the acceptance harness reads the composer's claim

Branch `refactor/d3-harness` off `refactor/flatten-handoff-next` @ `30f479bae`.

**Commit tip: `4c5d44f4b`** — *EMIT publishes the mechanism the claim rests on*.

One repo commit (edit A) and three harness files edited in place (edits B–D).
`src/test/shell/run_engine_campaign_helpers_test.sh` is green; 52 @Test, no
new config key, `campaign_max_epochs` untouched.

---

## 1. Diff summary

### A — `run_engine.sh` (in the commit, +19/−1)

`campaign_emit`'s `jq` now copies four more fields out of
`solver.campaignClaim` into `result.json`:

```
+findingKind: $decided.findingKind,
+polarityDecides: $decided.polarityDecides,
+valuationOrdinal: $decided.valuationOrdinal,
+movedRoots: $decided.movedRoots,
```

`campaign_require_claim` now also demands them, so a manifest that publishes a
claim without the mechanism it rests on is one EMIT may not publish a result
from:

```
+and (($r.campaignClaim.findingKind // "")
+  | IN("MARKER_FLIPPED", "CLOCK_SKEW", "MESSAGE_PAIRING_FLIPPED",
+       "STATE_PAIRING_FLIPPED", "RECORDED_FAILURE_EXPLAINED",
+       "NO_SUPPORTED_WITNESS"))
+and ($r.campaignClaim.polarityDecides | type) == "boolean"
```

That precondition is the point: defaulting `findingKind` to `""` would hand
the harness a refusal whose reason the run never had.

### A — `src/test/shell/run_engine_campaign_helpers_test.sh` (in the commit, +17/−2)

Both EMIT fixtures state the new fields; the accepted-claim assertion checks
all four reach `result.json`. The accepted fixture's `valuations` are swapped
so ordinal 0 is `unsat` — which is exactly what `polarityDecides: true`
asserts, so the fixture now tells one coherent MARKER_FLIPPED story rather
than two halves of different ones. No new test case.

### B + C — `report_final.py` (495 → 348 lines, −147)

The gate, verbatim:

```python
ACCEPTED_FINDINGS = {"MARKER_FLIPPED", "CLOCK_SKEW",
                     "MESSAGE_PAIRING_FLIPPED", "STATE_PAIRING_FLIPPED",
                     "RECORDED_FAILURE_EXPLAINED"}
reasons = []
if claim != "SAT_CANDIDATE":            reasons.append("claim=%s" % claim)
if blockers:                            reasons.append("blockers=%s" % ",".join(blockers))
if final_status != "FINAL_READY":       reasons.append("finalStatus=%s" % final_status)
if finding_kind == "NO_SUPPORTED_WITNESS":
    reasons.append("findingKind=NO_SUPPORTED_WITNESS (%s)"
                   % result.get("claimReason", "no reason published"))
elif finding_kind not in ACCEPTED_FINDINGS:
    reasons.append("findingKind=%s" % finding_kind)
elif not polarity_decides and finding_kind != "RECORDED_FAILURE_EXPLAINED":
    reasons.append("polarityDecides=false: the formula is satisfiable at the"
                   " recorded valuation, so %s explains nothing" % finding_kind)
```

The `finding` column is now the composer's own words — mechanism, valuation,
moved roots, whether the recorded valuation refutes the recording — and the
report leads with `**PASS** -- CLOCK_SKEW at valuation 2, polarity decides`
instead of three probe dashes. The probe's `plain/buggy/other` are still
printed, labelled *reported, not a gate*, and only when they exist.

**−147 lines is mostly deletion of things that had lost their reader**, and
each was checked for callers before removal (the §10 rule):

| deleted | why |
|---|---|
| `reach = load("z3-result.json")` and every `reach.*` read | the file is written nowhere in Design 3 |
| `row_for_values`, `other_finding_row`, `accepted_finding_row`, `moved_markers`, `marker_name` | their only caller was the old finding column |
| `decided`, `root_space` fallbacks | `reach` was their only source; `result.json` is now the one source |
| "Fault markers", "Root space", "Mechanism necessity" sections | carried only by `z3-result.json` |
| `root_kind()` + `POLARITY_MEANING` + the "root kind **X** -- buggy = …" line | narration of a gate that no longer exists |

"Valuations" is kept, rewired to `result.json.valuations`.

### D — `lib_final.sh` (130 → 169 lines)

`FINAL_KEEP_GLOBS` now names every Design 3 artifact and is **epoch-agnostic**
(`iteration-*`, not `iteration-0000` — a list naming one epoch would delete
every later epoch's evidence): `sessions/*/*.jsonl` + `expressions.json`,
`session_census.jsonl`, `slots.jsonl`, `obligation_results.jsonl`,
`campaign_gaps.jsonl`, per-wave `obligations/tasks/gaps/root-domains/
explore_manifest`, each obligation's `obligation_result.jsonl`, `gap_ledger.json`,
`compose.log`, `stage_metrics.tsv`, and every epoch's own `final/`.

`fin_prune_case`'s keep loop was `[[ -e "$dir/$rel" ]]` — a **literal** test,
so any pattern entry silently kept nothing. It now expands the glob and tests
`-f` on each match. No `shopt nullglob`: an unmatched pattern stays literal
and `-f` rejects it, which is the same answer without touching a shell option
the caller may rely on.

**Measured**: on a synthetic case tree of 37 files, prune keeps 35 and drops
exactly the two it should (`instrumented-classes/A.class`, a worker
`stdout.log`). **No run needs `FINAL_KEEP_ALL=1` any more.**

### D — `probe_final.sh` (462 → 472 lines): the two root sources deleted

- `markers = reach["roots"]["booleanInputs"]` — gone with `z3-result.json`.
- the `sym__HDFS_CONFIG_SNAPSHOT_DELETION_ORDERED` regex over `candidate.smt2`
  — gone; one case's variable spelling from a naming scheme `d3` does not use.

Neither is replaced. `$Z` is removed. Where the probe now has nothing to
assert it says so by name — `NO_DECLARED_BOOLEAN_ROOTS`, with the reason that
the polarity question is `ClaimPolicy.polarityDecides` in `result.json` —
rather than emitting `NO_ROOT` as though it had looked. Verified end to end:
the probe still runs and reports on the CLOCK path, and gates nothing.

Backups kept beside each file as `*.bak-d3harness`.

**One thing to note about scope**: `accept_final.sh`, `report_final.py`,
`probe_final.sh`, `lib_final.sh` and `run_branch.sh` are **not tracked in the
repo** — they live only in `$SP/final/` and `$SP/verify/`. So edits B–D cannot
be in the commit tip; they are applied in place to the live harness. If you
want them versioned I can land them under `tools/` on this branch, but that
would make `$SP/final/` a second copy, so I have not done it unasked.

## 2. Verification

| check | result |
|---|---|
| `mvn -o -DskipTests package` at `4c5d44f4b` | ok |
| `run_engine_campaign_helpers_test.sh` | **passed** |
| `D3ContractTest, D3ExploreTest, D3ComposeTest` | **passed** |
| @Test count | **52** (cap 100, target 80) |
| config keys | **43**, unchanged — no key added, so no count to bump |

The gate, across all eight claim shapes (synthetic `result.json`):

| fixture | verdict | reason |
|---|---|---|
| MARKER_FLIPPED + polarity | **PASS** | – |
| CLOCK_SKEW + polarity | **PASS** | – |
| STATE_PAIRING_FLIPPED + polarity | **PASS** | – |
| RECORDED_FAILURE_EXPLAINED, polarity false | **PASS** | – (the one exempt kind) |
| NO_SUPPORTED_WITNESS | **FAIL** | `findingKind=NO_SUPPORTED_WITNESS (no path of this corpus reached the declared occurrence)` |
| MARKER_FLIPPED, polarity false | **FAIL** | `polarityDecides=false: the formula is satisfiable at the recorded valuation, so MARKER_FLIPPED explains nothing` |
| field absent (pre-refactor corpus) | **FAIL** | `findingKind=MISSING` |
| INCONCLUSIVE_PARTIAL + blockers + gaps | **FAIL** | all four reasons, joined |

## 3. The two-lane launch

Build the jar on the branch first — `$SP/wt-stage` is at an older tip, and
`run_branch.sh` resolves the jar from the repo root it is handed, so the jar
and the worktree must be the same tree:

```bash
cd $SPN/wt-d3-explore && mvn -q -o -DskipTests package   # already done at 4c5d44f4b
```

```bash
SP=/tmp/claude-20003/-opt-GraphChecker/99c84a54-86ac-44a4-a030-760f664ae2a1/scratchpad
SPN=/tmp/claude-20003/-opt-GraphChecker/3230912f-3427-4c18-a306-eb2005a43b37/scratchpad
JARP=$SPN/wt-d3-explore/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
IMG=$SP/images/j2sdk-image-build16

# lane A
env FINAL_SP="$SP" JAR="$JARP" CAUSYNTH_CUSTOM_JDK_HOME="$IMG" \
    OUT="$SPN/laneD3A" \
    CASES="hdfs-17960 hdfs-17899-bug3 hdfs-17899-bug2 hdfs-17899-bug1" \
    MIN_FREE_GB=6 DISK_WAIT_SECONDS=1800 CASE_TIMEOUT_SECONDS=21600 \
    RUN_BRANCH="$SP/verify/run_branch.sh" \
    bash "$SP/final/accept_final.sh" >"$SPN/laneD3A.launch.log" 2>&1 &

# lane B
env FINAL_SP="$SP" JAR="$JARP" CAUSYNTH_CUSTOM_JDK_HOME="$IMG" \
    OUT="$SPN/laneD3B" \
    CASES="hdfs-17897 hdfs-11741" \
    MIN_FREE_GB=6 DISK_WAIT_SECONDS=1800 CASE_TIMEOUT_SECONDS=21600 \
    RUN_BRANCH="$SP/verify/run_branch.sh" \
    bash "$SP/final/accept_final.sh" >"$SPN/laneD3B.launch.log" 2>&1 &
```

- **No `FINAL_KEEP_ALL`** — edit D keeps the right things. Disk is 12 G free;
  each case prunes to well under the 300 MB cap.
- **`DRY=1`** on either command runs preflight and prints the per-case
  commands without starting anything. Worth one pass first.
- **Stop a lane**: `kill -TERM -$(cat $SPN/laneD3A/pgid)` — that group and
  nothing else.
- **Read as they land**: `$SPN/laneD3<X>/summary.tsv` (13 columns; `verdict`,
  `reason`, `finding` are the last three) and
  `$SPN/laneD3<X>/report/<case>/report.md`.

**`CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT`** — add it to `case_env` (or export it
before `run.sh`) to stop each case after IMPORT. That is the cheap gate on
M2's re-recording: it yields the seed session and `session_census.jsonl` —
lineage-complete share, every declared port minting, interaction rows paired —
without paying for EXPLORE..EMIT. On the round-2 numbers that is roughly
SEED + PLAN + INSTRUMENT + REPLAY + IMPORT ≈ **270–310 s per case** against
750–3,800 s for a full run. It is a measurement run, not an acceptance run:
`summary.tsv` will read `claim=MISSING` because no `result.json` is written,
which is correct and not a regression.

## 4. Expected wall time

From the round-2 lanes (pre-refactor jar, PARALLEL=1): 17960 562 s,
17897 ~790 s, bug3 ~1,000 s, bug2 ~1,550 s, bug1 2,930 s, 11741 3,764 s.
Lane A ≈ 6,000 s, lane B ≈ 4,550 s, so ≈ **1 h 40 m** for both.

Expect the per-stage split to move even if totals hold: SOLVE no longer runs
z3 (ComposeMain runs it per valuation while composing), so the 87–254 s that
used to appear under `SOLVE[<anchor>]` lands in `COMPOSE[n]`, which was
18–51 s. Budget by the totals.
