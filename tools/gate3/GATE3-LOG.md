# gate3 — one offline regression gate for cleanup round 3

`gate3.sh` re-runs the five offline owners of the engine over two frozen
corpora and writes one digest line per artifact.  It executes **no workload**,
starts **no campaign**, needs **no write access** under a corpus or under a
`/opt/hadoop-*` tree, and runs every JVM `nice -n 10` with `-Xmx8g`.

    gate3.sh <jar> <outdir>            # ~85 s, ~120 MB under <outdir>
    diff_gate.sh <outdir> [baseline]   # per-artifact differences vs baseline/

`<outdir>/DIGESTS.txt` holds one line per artifact:

    <corpus> <gate> <artifact> <sha256-of-normalised-content> <count-summary>

A sub-gate that cannot run prints `SKIPPED <reason>` in the digest field
instead of failing the gate.  `diff_gate.sh` exits 1 when anything differs.

* **baseline (current, 2026-09-16): staging tip `0e3c1ab39`** = `39bedd768`
  + `r3/C3` (merge `0e3c1ab39`, branch tip `58e148f63`), jar built in
  `$SPO/wt-stage`: `baseline/` (copied from `$MY/r3/gate-stage-C3`; the
  confirming second run is `$MY/r3/gate-stage-C3-confirm`, `0 of 46` differ).
  **Taken the campaign way**, with `GATE3_SCOPE_MAP_DIR` pointed at the run's
  own static maps -- see the standard invocation below.  Same `gate3.sh`, same
  `norm.py` as `39bedd768`; `gate3-8b91419a0.sh` is the script that matches
  every baseline before `39bedd768`
* the superseded baseline (staging tip `39bedd768` = `8b91419a0` + `r3/PC3`
  (branch tip `492280b46`)): `baseline-39bedd768/`, copied from
  `$MY/r3/gate-stage-PC3`.  Same `gate3.sh`, same `norm.py`
* the superseded baseline (staging tip `8fd51028b` = `41cd82d70` + `r3/C2`
  (branch tip `f0a2ef85a`)): `baseline-8fd51028b/`, copied from
  `$MY/r3/gate-stage-C2`.  Staging `8b91419a0` = `8fd51028b` + `r3/DOC2`, which
  touches only `docs/CONCOLIC_INTEGRATION.md` and four
  `experiments/hadoop/*/README.md` -- no sub-gate reads any of them -- so this
  directory is the `8b91419a0` content as well.  Same `norm.py`; `gate3.sh`
  differs only by the pass-2 `--static-scope-map` line noted below
* the superseded baseline (staging tip `41cd82d70` = `1357116d1` + `r3/DOC1`;
  `1357116d1` = `48dece245` + `r3/PC2` (merge `6754d3951`) + `r3/R3` (merge
  `1357116d1`, tip `e1d9b9512`)): `baseline-41cd82d70/`.  `r3/DOC1` adds only
  `experiments/hadoop/accept/**`, which no sub-gate reads, so this directory is
  the `1357116d1` content as well.  Same `norm.py`; `gate3.sh` differs only by
  the parse-before-execute braces noted below
* the superseded baseline (staging tip `48dece245` = `e33e72351` + `r3/R2`
  + `r3/PC` + `r3/R1` + the relocation commit + `r3/C`):
  `baseline-48dece245/`.  Same `gate3.sh`, same `norm.py`, but taken with the
  **corpus's** scope maps, not the run's own
* the superseded baseline (staging tip `122069b02` = `e33e72351` + `r3/R2`
  + `r3/PC`): `baseline-122069b02/`.  Same `gate3.sh`, same `norm.py`
* the superseded baseline (jar `$MY/r3/baseline.jar`, = staging tip
  `e33e72351`): `baseline-e33e72351/`, and the two runs it was taken from,
  `baseline-run1/`, `baseline-run2/` (`DIGESTS.txt` byte-identical).
  Run it with `gate3-e33e72351.sh`, the script that matches that jar.

### 2026-09-16: re-baselined onto staging `0e3c1ab39` (r3/C3 merged)

Staging tip `0e3c1ab39` = `39bedd768` + `r3/C3` (merge `0e3c1ab39`, branch tip
`58e148f63`, 2 commits; `compose/{ClaimPolicy,ComposeMain,ComposedFamilies,
Composer}.java` and `compose/ComposerTest.java` only -- no other package, no
`run_engine.sh`, no experiment).  `gate3.sh` and `norm.py` are unchanged; the
jar is the only thing that moved, so `baseline-39bedd768/` stays runnable under
the same script.

Build + 46 `@Test` + `src/test/shell/run_engine_campaign_helpers_test.sh` all
green; the gate ran `rc=0` with `0 SKIPPED` on all four passes, and pass A and
pass B again produced byte-identical `static` products (both
`static_scope_map.jsonl` `cmp`-identical; all 8 `static` rows and, since compose
never reads the scope map, all 6 `compose` rows identical between the passes).
The confirming second run is `$MY/r3/gate-stage-C3-confirm`, `0 of 46` differ.

**5 of 46 rows differ from `baseline-39bedd768`, every one `r3/C3`'s and every
one a `compose` row**, verified row-level, not only by digest:

| row | what changed | whose |
|---|---|---|
| `11741/compose/candidate.smt2` | `asserts` **79 → 135**, `bytes` **142600 → 115245**.  The handoff families now cover every interaction a path's conjunction reaches, not the anchor's attaches alone: **70 distinct family names**, **133 arm selectors** (`…__armN`), each family an exactly-one cardinality sum `(= (+ (ite sel 1 0) …) 1)` over its arms.  The seed-delivery pins (`(= HOFF.836a0f0e… 182905)` and its twin) are gone | C3 |
| `11741/compose/claim` | `claim=INCONCLUSIVE_PARTIAL`, `findingKind=NO_SUPPORTED_WITNESS`, `movedRoots=none`, `valuationOrdinal=0`, `polarityDecides=false`, `blockers=1` **all unchanged**; `z3` **`unsat/NO_EXACT_REACHABILITY` → `sat/EXACT_REACHABLE`**.  All **4 valuations are `sat`** where all 4 were `unsat`, each selecting path `cb54bd9ab7591e43` (session `a02cd2befb3f833a-75e2192b`).  The one blocker is now **`FORMULA_SAT_AT_RECORDED_VALUATION`** on that path where it was `PATH_SELF_CONTRADICTORY` on the anchor.  `claim.json`'s own gap list moves `61 → 60`: the 7 `DIAGNOSTIC PATH_SELF_CONTRADICTORY` become 6, the `BLOCKING` one is replaced.  No `UNPRODUCIBLE_ANSWER` gap is raised on either corpus, so no slot went unbound; `GapKind` gains nothing (both codes predate `39bedd768`) | C3 |
| `11741/compose/manifest` | `families` **5 → 13**; `paths=7 roots=14 valuations=4 gaps=53 finalStatus=FINAL_REFUSED` unchanged.  Each of the 4 `solver.valuations` gains **`selectedArms` with 10 entries** (`selector`, `family`, `interactionId`, `sessionId`, `producerPathId`, `expressionRef`, `attested`), and `selectedPathId`/`selectedSessionId` are non-empty where they were `""` | C3 |
| `17960/compose/candidate.smt2` | `bytes` **31514 → 23544**, `asserts=18` unchanged **and all 9 `:named` assertions identical, in the same order**.  **25 `declare-const` removed, 0 added**; every one a versioned `INSTANCE_FIELD/…@vN` or `MAP_STATE/…@vN` symbol that headed a join equation `(= \|sym\| …)` in the baseline, and **none of the 25 is mentioned anywhere in the new file** -- the unreached joins and nothing else | C3 |
| `17960/compose/manifest` | **digest only**: `paths=3 families=13 roots=1 valuations=2 gaps=0 finalStatus=FINAL_READY` unchanged, the 13 families identical arm for arm.  The only change is the new, **empty** `selectedArms` member on both `solver.valuations` | C3 |

**The `17960` CLAIM row is byte-identical** (`0cbdacc8…`): `SAT_CANDIDATE` /
`MARKER_FLIPPED`, `movedRoots=HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false`,
`valuationOrdinal=1`, `polarityDecides=true`, `blockers=0`,
`z3=sat/EXACT_REACHABLE`, `finalStatus=FINAL_READY`.

> **The gate's `claim` row is not `claim.json`.**  It is a 7-field summary
> `jq`-ed out of the MANIFEST (`gate3.sh:276`), so "byte-identical claim row"
> says nothing about the file.  `17960/compose/claim.json` itself **does move**
> -- by exactly two added lines, `"selectedArms": [],` once per valuation, and
> nothing else (`diff` is `34a35` + `54a56`).  No sub-gate digests `claim.json`.

**Byte-identical across this re-baseline (41 of 46 rows):** every `wave0` row
of both corpora (8), every `plan` row (12), every `static` row (8), every
`meta` row (12), and `17960/compose/claim`.  Nothing outside `compose` moved,
which is what a `compose/**`-only branch should do.

### 2026-09-16: re-baselined onto staging `39bedd768` (r3/PC3 merged)

Staging tip `39bedd768` = `8b91419a0` + `r3/PC3` (branch tip `492280b46`, 3
commits; `plan/**`, `runtime/{RuntimeRegionPlanner,CausynthTraceRecorder}`,
`run_engine.sh` and the shell test only).  `norm.py` is unchanged.  **`gate3.sh`
gains one line** -- `--static-scope-map "${SCOPE_MAP}"` on the pass-2
`CausynthTraceRecorder`, which is what `run_engine.sh:do_workload` now passes;
the script that matches every earlier baseline is kept as
`gate3-8b91419a0.sh`.  A jar predating the argument ignores it
(`CausynthTraceRecorder.parseArgs` stores unknown keys and never validates
them), so the old baselines remain runnable under either script.

Build + 46 `@Test` + `src/test/shell/run_engine_campaign_helpers_test.sh` all
green; the gate ran `rc=0` with `0 SKIPPED` on all four passes, and pass A and
pass B again produced byte-identical `static` products.

**6 of 46 rows differ from `baseline-8fd51028b`; five are `r3/PC3`'s and the
sixth is the Soot item**, every one verified row-level, not only by digest:

| row | what changed | whose |
|---|---|---|
| `11741/plan/concolic_region_plan.jsonl` | digest only, `rows=87` unchanged: the new `declaredSiteCaptures` member on **68 of 87** rows, **171 captures**.  Checked field by field against the baseline with that member stripped: **0 rows differ by anything else** | PC3 |
| `17960/plan/concolic_region_plan.jsonl` | digest only, `rows=46` unchanged: `declaredSiteCaptures` on **18 of 46** rows, **41 captures**; **0 rows differ by anything else** | PC3 |
| `11741/plan/execution_task_plan.jsonl` | `rows=86` unchanged, `symbolize=23[CALL_RETURN:13,…]` → **`26[CALL_RETURN:16,COMMUNICATION_SITE_PORT:10]`**.  **83 of 86 task ids are unchanged and identical in content (0 differ)**; 3 are renamed because their port set grew.  The whole change is **3 added ports**, one per occurrence of `REGION.60480aef`: `<Timer: long now()>` at `<BlockTokenSecretManager: DataEncryptionKey generateDataEncryptionKey()>#u17`, values `1789576141858` (balancer), `1789576142337` (dn1 `DATA_XCEIVER#1`), `1789576142337` (dn1 `DATA_XCEIVER#2`).  The 6 ports those 3 tasks already carried moved across unchanged | PC3 |
| `17960/plan/execution_task_plan.jsonl` | **no gate row: the normalised digest is unchanged** (`0de6ba92…`, `rows=45`, `symbolize=4[OBSERVED_FIELD_RECEIVER:4]`).  Listed here because the raw file does move -- see **member order** below | PC3 |
| `11741/plan/schedule_index.json` | derived: the two artifact digests, and the 3 renamed task ids at `members[14..16]`.  `members=86` unchanged | PC3 (follows) |
| `17960/plan/schedule_index.json` | derived: `regionPlan.sha256`/`sizeBytes` (the new member) and `executionTaskPlan.sha256` (member order).  `members=45` unchanged | PC3 (follows) |
| `17960/static/candidate_dataflow_edges.jsonl.gz` | digest only, `rows=8833` unchanged.  **17 edges, same ids, differing only in Soot local names** (`fromCell` 17, `toCell` 16): masking `$stackN`/`$rN`/… makes the two row sets identical.  Pass A and pass B of this jar agree, so it is jar-stable, not run noise.  `11741`'s candidate graph is unchanged | the Soot local-naming item (5), **not** PC3 |

**Member order.**  `SymbolicInputSelection.declaredPorts` mints a port that
replaces the finalizer's port for the same site *by symbol*, with the same
members and the same values but written in `DeclaredSiteCapture.port`'s order.
So some raw task-plan lines move while their content does not: 11741 **74 of
86 lines raw-identical, 9 more identical once keys are sorted** (83 total
unchanged task ids), and 17960 **43 of 45 raw-identical, 2 more identical once
keys are sorted** (45 of 45, same file size).  `norm.py` re-emits with
`sort_keys=True`, so the gate never sees this and `17960/plan/
execution_task_plan.jsonl` keeps its digest; the raw `sha256` recorded inside
`schedule_index.json` does move, which is the only reason that row differs for
17960.  "Byte-identical" below and in `r3/PC3`'s commit messages means
**the normalised artifact the gate digests**, not the raw file.

**Byte-identical across this re-baseline (40 of 46 rows):** every `wave0`
artifact of both corpora (10 rows), every `compose` artifact of both corpora
(4 rows: both `candidate.smt2`, both manifests, both claims), the remaining
`plan` artifacts, all four `11741/static` artifacts, the other `17960/static`
artifacts, and all 10 `meta` rows.  **Both claims are unmoved:** 17960
`SAT_CANDIDATE`/`MARKER_FLIPPED` at `valuationOrdinal=1`, `blockers=0`,
`finalStatus=FINAL_READY`; 11741 `INCONCLUSIVE_PARTIAL`/`NO_SUPPORTED_WITNESS`,
`blockers=1`, `gaps=53`, `finalStatus=FINAL_REFUSED`.

### 2026-09-16: re-baselined onto staging `8fd51028b` (r3/C2 merged)

Staging tip `8fd51028b` = `41cd82d70` + `r3/C2` (branch tip `f0a2ef85a`, 10
commits; `compose/**`, `explore/**`, `smt/**` and their tests only).  `norm.py`
is unchanged; `gate3.sh` changed only by the parse-before-execute braces (see
**`gate3.sh` fix** below), which move no digest.  Build + 46 `@Test` +
`src/test/shell/run_engine_campaign_helpers_test.sh` all green; the gate ran
`rc=0` with `0 SKIPPED` on all four passes, and pass A and pass B again produced
byte-identical `static` products.

**4 of 46 rows differ from `baseline-41cd82d70`, every one `r3/C2`'s**, and
every one verified at row/text level, not only by digest:

| row | what changed |
|---|---|
| `11741/compose/candidate.smt2` | `bytes=104529 -> 142600`, `asserts=75` unchanged, `declare` lines 77 -> 190.  **4 clock symbols declared (was 0)**: `M_J_field_REGION.aaa1cfd7-....in.{3830cfdb,db4e86ec,9e24f240,a1c9aed4}....occ.*_java/lang/Long`, each carried into a paired `M_J_field_HOFF.*_HandoffLeafCarrier`.  **All 7 `path_fatal__i` name all 4 clocks** (baseline: 0 of 7 named any) |
| `11741/compose/manifest` | `gaps=241 -> 53`; `paths=7 families=5 roots=14 valuations=4 finalStatus=FINAL_REFUSED` all unchanged.  By kind: `UNATTESTED_ARM 180 -> 0`, `DECLARATION_MISSING 13 -> 9`, `TOPOLOGY_DIVERGENCE 42 -> 38`, `ADMISSION_GAP 6 -> 6`.  **Attested arms 4 of 29 -> 29 of 29**, families carrying an attested arm 4 of 5 -> 5 of 5 |
| `17960/compose/candidate.smt2` | `bytes=26843 -> 31514`, `asserts=18` unchanged, `declare` lines 41 -> 46 (4 `INSTANCE_FIELD`, 1 `MAP_STATE`).  No clock symbol in either version -- 17960 has no clock in its slice |
| `17960/compose/manifest` | `families=12 -> 13`, `gaps=2 -> 0` (`UNATTESTED_ARM 2 -> 0`); `paths=3 roots=1 valuations=2 finalStatus=FINAL_READY` unchanged.  Attested arms 12 of 12 -> 13 of 13 |

**Both claim rows are byte-identical to `baseline-41cd82d70`** (they are not in
the table above because `diff_gate.sh` reported them unchanged):
17960 `claim=SAT_CANDIDATE findingKind=MARKER_FLIPPED
movedRoots=HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false valuationOrdinal=1
polarityDecides=true z3=sat/EXACT_REACHABLE blockers=0`; 11741
`claim=INCONCLUSIVE_PARTIAL findingKind=NO_SUPPORTED_WITNESS movedRoots=none
valuationOrdinal=0 polarityDecides=false z3=unsat/NO_EXACT_REACHABILITY
blockers=1`.

**Byte-identical across this re-baseline (42 of 46 rows):** every `meta`,
`wave0`, `plan` and `static` artifact of both corpora, and both `compose`
claims.  `r3/C2`'s worker-side flip refusals (11741 wave 0: 18 of 36 queries
refused) do **not** run in the gate -- the gate's `wave0` sub-gate proposes
obligations and never answers them -- so `11741/wave0/explore_manifest.json`
still reports `gaps=TOPOLOGY_DIVERGENCE:12,ADMISSION_GAP:271,LINEAGE_LOST:3`
exactly as before.  That is expected, not a miss.

### 2026-09-16: `gate3.sh` fix -- parse before execute

`gate3.sh` aborted `rc=127` with `line 485: o: command not found` **after** a
complete 46-row `DIGESTS.txt` (`$MY/r3/g/stage-full`, 13:45-13:47).  It is not
a typo in the script: line 485 is `else`, and the only two standalone `o` words
in the file are the `-o` option words at lines 465 and 494.  The run died at
line 494, `LC_ALL=C sort -o "${DIGESTS}" "${DIGESTS}"` -- the evidence is that
its `DIGESTS.txt` was complete but **unsorted** (17960 rows before 11741) and
`.sorttmp`, removed on the next line, survived.

The cause is that the script file was **overwritten in place while it was
running**: `gate3/gate3.sh` carries `mtime 13:35:41` but `ctime 13:46:06`, the
signature of a `cp -p` (from the byte-identical `$MY/r3/gate3-PC2.sh`, same
preserved mtime) landing mid-run.  bash reads a script incrementally from its
file descriptor, so it resumed at a stale byte offset in the new content and
executed a word fragment at a line number that no longer corresponded to
anything.  Reproduced both ways in `$MY/r3/selftest/`: overwriting an
unwrapped script mid-run loses its tail silently; wrapping the same script in
one `{ ... }` group runs the tail correctly.

**Fix:** the whole body of `gate3.sh` is wrapped in a single `{ ... }` group
(lines 12 and 513), which forces bash to parse the entire file before executing
any of it.  The group is not a subshell, so variables, functions, `exit` and the
exit status are unchanged; the only visible difference is that every line number
is one greater than before.  `$MY/r3/gate3.sh.pre-brace` is the previous file.
The two confirming passes above were taken with the fixed script and moved no
digest.  Do not remove the braces -- and do not copy over `gate3.sh` while a
gate run is using it.

### 2026-09-16: re-baselined onto staging `1357116d1` (r3/PC2 + r3/R3 merged)

Staging tip `1357116d1` = `48dece245` + `r3/PC2` (merge `6754d3951`) + `r3/R3`
(merge `1357116d1`, branch tip `e1d9b9512`, 10 commits, runtime-only).
`gate3.sh` and `norm.py` are unchanged.  Build + 46 `@Test` +
`src/test/shell/run_engine_campaign_helpers_test.sh` all green; the gate ran
`rc=0` with `0 SKIPPED` on all four passes.

**The standard invocation is now the campaign way.**  `gate3.sh` cannot point
at its own `static` output in one invocation -- it reads `SCOPE_MAP_DIR` at the
top of each corpus loop, before the `static` sub-gate has run, and it wants
`<dir>/<corpus id>/static_scope_map.jsonl` while `static` writes
`<outdir>/<corpus id>/static/out/static_scope_map.jsonl`.  So it is run twice:

    # pass A -- produce this jar's own static maps
    gate3.sh "$JAR" "$OUT-a"
    for id in 11741 17960; do
      mkdir -p "$MAPS/$id"
      cp "$OUT-a/$id/static/out/static_scope_map.jsonl" "$MAPS/$id/"
    done
    # pass B -- the recorded run; wave0 and the scheduler read $MAPS
    GATE3_SCOPE_MAP_DIR="$MAPS" gate3.sh "$JAR" "$OUT"
    diff_gate.sh "$OUT"

Pass A and pass B produce byte-identical `static` products, so `$MAPS` is this
run's own map either way.

**`r3/R3` adds nothing.**  All 46 rows at `1357116d1` are byte-identical to
`r3/PC2`'s own runs -- the 32 `meta`/`wave0`/`plan` rows against the PC2
campaign-way run `$MY/r3/gate-stage-PC2-newmap`, and the 14 `compose`/`static`
rows (which never read the scope map) against `$MY/r3/gate-stage-PC2`.  Both
claims are unmoved: 17960 `SAT_CANDIDATE`/`MARKER_FLIPPED` at
`valuationOrdinal=1`, `blockers=0`; 11741 `INCONCLUSIVE_PARTIAL`, `blockers=1`.

**9 of 46 rows differ from `baseline-48dece245`, every one `r3/PC2`'s**, and
every one verified row-level, not only by digest:

| row | what changed | whose |
|---|---|---|
| `11741/static/static_scope_map.jsonl` | 172 → **201** rows (+29 `DECLARED_SITE`) | PC2 |
| `17960/static/static_scope_map.jsonl` | 1053 → **1108** rows (+55 `DECLARED_SITE`) | PC2 |
| `11741/plan/concolic_region_plan.jsonl` | 85 → **87** lines.  `exportConsumers` gone from all 84 → 86 `CONCOLIC_REGION_PLAN` rows (84 mentions → 0); `DECLARED_COMMUNICATION_CAPTURE_V1` 0 → **30** mentions | PC2 |
| `11741/plan/execution_task_plan.jsonl` | 84 → **86** rows; 22 removed, 24 added, **all on `PBHelper.convert(BlockKey)`** (23 of the 24 added on the `BlockKey`→`BlockKeyProto` direction, 1 on the inverse).  4 surviving tasks differ only in `exportConsumers`.  `symbolize=23[CALL_RETURN:13,COMMUNICATION_SITE_PORT:10]` **unchanged** | PC2 |
| `11741/plan/schedule_index.json` | `members` 84 → **86**, same `target=TASK.SEED.c2604501…` | PC2 (follows the task plan) |
| `17960/plan/concolic_region_plan.jsonl` | digest only, `rows=46` unchanged: `exportConsumers` gone from all 45 `CONCOLIC_REGION_PLAN` rows (45 mentions → 0).  No region added, removed or otherwise changed | PC2 |
| `17960/plan/execution_task_plan.jsonl` | digest only, `rows=45` and `symbolize=4[OBSERVED_FIELD_RECEIVER:4]` unchanged: **20 tasks differ, in `inputActions` only, 510 actions in all**.  No task id gained or lost, no other field touched | PC2 — **not a defect**, the two maps differ; see below |
| `17960/plan/schedule_index.json` | digest only, `members=45` unchanged | PC2 (follows the task plan) |
| `17960/static/candidate_dataflow_edges.jsonl.gz` | digest only, `rows=8833` unchanged.  Identical to `r3/PC2`'s own value, and identical across this session's two runs of the same jar, so it is not run-to-run noise here | PC2 (the Soot local-naming item) |

> **NOT A DEFECT — corrected 2026-09-16 by `M-PC3`.**  This row was recorded
> here as an open `r3/PC2` defect ("510 `inputActions` across 20 tasks differ
> under the new map, pending `M-PC3`").  `M-PC3` established that it is not a
> `DECLARED_SITE` role leak and not an `r3/PC2` defect at all: it is **two
> different maps being compared**.  `baseline-48dece245` was taken with the
> **corpus's frozen** `static_scope_map.jsonl` -- `$MY/final-f651c4879/out/
> hdfs-17960/static_scope_map.jsonl`, **810 rows**, written by jar
> `f651c4879`, carrying **zero** `DECLARED_SITE` rows because it predates the
> role -- while every campaign-way run regenerates the map from the run's own
> `static` output: **1053 rows** then, 1108 now (the extra 55 are `r3/PC2`'s
> `DECLARED_SITE` rows).  A map with 243 more non-`DECLARED_SITE` rows scopes
> more cells, so more `inputActions` are materialised; the `DECLARED_SITE`
> rows are not what moved them.  Nothing needed fixing and `r3/PC3` did not
> move this row: at `39bedd768` it is unchanged from `8fd51028b`
> (`0de6ba92…`, `rows=45`, `symbolize=4[OBSERVED_FIELD_RECEIVER:4]`).
> The rule this cost us: **compare a campaign-way run against a campaign-way
> baseline**, never against one taken with the corpus's frozen map.

**Byte-identical across this re-baseline (37 of 46 rows):** every `wave0`
artifact of both corpora, every `compose` artifact of both corpora (both
`candidate.smt2`, both manifests, both claims), the remaining `plan` artifacts
(`refined_dataflow_edges`, `recording_gaps`, `region_skeletons`), all four
`11741/static` artifacts, `17960/static/region_skeletons.jsonl.gz`,
`17960/static/communication_gaps.jsonl.gz`, and all 10 `meta` rows.

### 2026-09-16: re-baselined onto staging `48dece245` (r3/C merged)

Staging tip `48dece245` = `122069b02` + `r3/R1` (`e69d0e324`) + the relocation
commit `a63c30966` + `r3/C` (`6d0c9d785`).  `gate3.sh` and `norm.py` are
unchanged; the jar is the only thing that moved.  Build + 46 `@Test` +
`src/test/shell/run_engine_campaign_helpers_test.sh` all green, and the gate ran
`rc=0` with `0 SKIPPED` twice.

**6 of 46 rows differ from `baseline-122069b02`**, all in `compose` plus the one
known static instability; every one verified row-level, not only by digest:

| row | what changed |
|---|---|
| `17960/compose/candidate.smt2` | 29690 → 26843 B, `asserts=18` unchanged.  12 whole-state preamble `define-fun`s gone (`assoc_has/read/key_at/value_at/put/remove`, `indexed_write/insert/remove/contains`, `java_int_to_string`, `java_long_wrap`), none added — the preamble is now reachability-gated.  Exactly **one conjunct dropped from each of the 3 paths** — the decision at the anchor occurrence (P1): `path_fatal__0` `(not (= 1 M_I_…631ed3aa…))`, `path_fatal__1` `(not (= 1 M_I_…d923eb15…))`, `path_fatal__2` `(= 2 M_I_…d923eb15…)`.  Nothing added; the other 63 lines byte-identical |
| `17960/compose/manifest` | counts **identical** (`paths=3 families=12 roots=1 valuations=2 gaps=2 finalStatus=FINAL_READY`); `manifest.gaps` unchanged (2 × `UNATTESTED_ARM`).  Inside: **+1 `DIAGNOSTIC` `PATH_SELF_CONTRADICTORY`** in `claim.gaps` (subject `fcbb3bf887582613` = path 2, `path_selector__2__c952e1e60a`, session `seed-result-199da06f`), and `solver.solverRuns` 5 → 8.  Path 2 asserts `X = 2` (via `java_int_wrap`) together with `(not (= 2 X))`, so the diagnostic is sound — and it was equally unsat in the baseline, which simply never asked |
| `17960/compose/claim` | **byte-identical** (`0cbdacc8…`): `SAT_CANDIDATE` / `MARKER_FLIPPED` / `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false` / `valuationOrdinal=1` / `polarityDecides=true` / `z3=sat/EXACT_REACHABLE` / `blockers=0`.  Not a differing row; recorded here because it is the load-bearing one |
| `11741/compose/claim` | `UNSAT_CLOSED` → **`INCONCLUSIVE_PARTIAL`**, `findingKind=NO_SUPPORTED_WITNESS` (unchanged), `movedRoots=none`, `valuationOrdinal=0`, `polarityDecides` true → **false**, `blockers` 0 → **1** |
| `11741/compose/manifest` | counts unchanged except `finalStatus` `FINAL_READY` → **`FINAL_REFUSED`** (`paths=7 families=5 roots=14 valuations=4 gaps=241`); `manifest.gaps` unchanged.  `claim.gaps` gains exactly **7 `DIAGNOSTIC` + 1 `BLOCKING` `PATH_SELF_CONTRADICTORY`** (one diagnostic per composed path; the blocking row is subject = the anchor, `sessionId=composition`, "all 7 composed paths are unsatisfiable with every root free"), nothing removed.  One `finalStatusRefusals` entry, `solver.solverRuns` 5 → 12, `symbolicPropagationComplete` true → **false**.  Valuations **0–3 all `unsat`** with the same `HDFS.BLOCK_KEY.SERIAL_NO` 182907/182908/182909/182910 and `fatalObserved=false`; only valuation 0's `unsatCore` widens (8 → 22 names, now naming `handoff_family__*` too) |
| `11741/compose/candidate.smt2` | 103036 → 104529 B, `asserts` 74 → **75**: the extra one is `(assert false) ; fail closed: PATH_SELF_CONTRADICTORY:<anchor>`.  Named asserts still 32.  10 preamble `define-fun`s gone (`assoc_key_at/read/value_at`, `indexed_append/contains/insert/read/remove/write`, `java_long_wrap`), none added.  Each of the 7 paths keeps 11 conjuncts, 2 swapped for 2: the consumer-side pin `(= HOFF.8bd44c61… 182905)` becomes the relation `(= HOFF.8bd44c61… HOFF.2fb7f999…)` plus `(= HOFF.2fb7f999… 182905)` (P2), and the per-path `(not (= container_dag__… nullRef))` at the target is gone (P1) |
| `17960/static/candidate_dataflow_edges.jsonl.gz` | the **known Soot local-naming instability only**.  `rows=8833` both, no id gained or lost, 23 rows differ, and only in `fromCell` (9) / `toCell` (14).  Confined to 2 methods; in each the `(kind,siteId)` multiset is identical and a **single transposition of two same-typed Soot temporaries maps the baseline rows exactly onto the new rows**: `$z17 ↔ $z18` in `DirectorySnapshottableFeature.computeDiffRecursively` (17 rows) and `$z5 ↔ $z6` in `FSDirectory.resolvePath` (6 rows), every one a `guard_dependency`.  Isomorphic per method.  `r3/C` touched no static-pass file, so nothing in the pass changed.  Checked with `$MY/r3/cdecheck.py` |

**Byte-identical across this re-baseline (40 of 46 rows):** every `wave0`
artifact of both corpora, every `plan` artifact of both corpora (region plan,
task plan, schedule index, refined edges, recording gaps, region skeletons),
all four `11741/static` artifacts (`candidate_dataflow_edges.jsonl.gz` included,
`33242844…`), `17960/static/static_scope_map.jsonl` (1053 rows),
`17960/static/region_skeletons.jsonl.gz`,
`17960/static/communication_gaps.jsonl.gz`, all 10 `meta` rows, and
`17960/compose/claim`.

### 2026-09-16: re-baselined onto staging `122069b02` (r3/PC merged)

`gate3.sh` changed with the jar (old copy kept as `gate3-e33e72351.sh`,
`norm.py` unchanged):

* `plan` now runs the recorder **twice**, as `run_engine.sh:do_regions` does:
  pass 1 `--region-skeleton-only true` into `<outdir>/<corpus>/plan/skeleton-pass`,
  then the REGION_STATE aggregation with `--recording-gaps <pass-1 gaps>`.  Two
  new digest rows: `plan/recording_gaps.jsonl` and `plan/region_skeletons.jsonl`.
* `static` no longer passes `-C <workflow.properties>` (the option is deleted).

Diffs from `baseline-e33e72351` (14 of 46 rows; verified row-level with
`norm.py`, not only by digest):

| what | 17960 | 11741 |
|---|---|---|
| `plan/concolic_region_plan.jsonl` | goals lose `edgeBindingIds`, gain `exportConsumers`; catalog loses `edges`; 2 of 46 rows' `closureGoals[0].runtimeDefinitionMethods` 3 → 7 (both `TARGET_REACH_CLOSURE`) | same key changes; catalog gains 4 `LINEAGE_LOST`/`DIAGNOSTIC` gap rows |
| `plan/execution_task_plan.jsonl` | rows lose `edgeBindings` (57 811 607 → 3 771 476 B); 2 of 45 `taskId`s change (the two `TARGET_REACH_CLOSURE` tasks) | rows lose `edgeBindings`, gain `exportConsumers` (3 254 306 → 1 065 634 B); 0 `taskId`s change |
| `plan/recording_gaps.jsonl` | NEW, 0 rows | NEW, 4 rows |
| `plan/region_skeletons.jsonl` | NEW, 104 rows, `sameAsCorpus=yes` | NEW, 26 rows, `sameAsCorpus=yes` |
| `plan/refined_dataflow_edges` | loses `refinementSchemaVersion`; 3559 rows otherwise identical | same; 782 rows |
| `plan/schedule_index.json` | derived: the two indexed digests/sizes, plus the two changed `taskId`s in `members[0]`, `members[3]`, `target` | derived: the two indexed digests/sizes only |
| `static/candidate_dataflow_edges.jsonl.gz` | loses `arrayLengthOperation` (22 rows); **plus the known jar-sensitive `$z13`→`$z12` flip on 7 `guard_dependency` rows** (`DF.3791/3799/3805/3806` `fromCell`, `DF.3807/3808/3809` `toCell`) in `DirectorySnapshottableFeature.computeDiffRecursively` | loses `arrayLengthOperation` (4 rows); nothing else |

Byte-identical across the re-baseline: every `wave0` and `compose` artifact
(including `candidate.smt2` and `claim.json`; the composition manifest differs
only in its own `smt2Path`), `static/static_scope_map.jsonl`,
`static/region_skeletons.jsonl.gz`, `static/communication_gaps.jsonl.gz`, and
in the task plans the `inputActions`, `communicationHandoffs`,
`observedWriteSites`, `branchMethods` and `admission` multisets.  The
`symbolize` sets still read `4[OBSERVED_FIELD_RECEIVER:4]` (17960) and
`23[CALL_RETURN:13,COMMUNICATION_SITE_PORT:10]` (11741).

## !! Never point ExploreMain at a kept corpus

`explore.ExploreMain` writes the epoch's slot table **into the parent
directory of its `--sessions` argument** — not into `--output-dir`:

    ExploreMain.java:70-73   iteration = --iteration, else sessions.getParent()
    ExploreMain.java:160     SlotTable slots = SlotTable.read(iteration);
    ExploreMain.java:164     slots.write(iteration);
    SlotTable.java:60        public static final String FILE = "slots.jsonl";
    SlotTable.java:164-165   RowCodec.writeAll(iteration.resolve(FILE), slots(), …)

So `--sessions <corpus>/schedule/iteration-0000/sessions` **rewrites
`<corpus>/schedule/iteration-0000/slots.jsonl`**, merging the run's rows into
the kept table.  That is what mutated the kept corpora before this gate
existed.  `compose.ComposeMain` only reads the iteration
(`ComposeMain.java:101 Corpus.read(arguments.iteration, null)`); it is the
explore path alone that writes.

**Never pass a kept corpus's sessions dir to ExploreMain directly; use
`gate3.sh`.**  gate3's `wave0` builds its own
`<outdir>/<id>/wave0/sessions` of symlinks, so the table lands in
`<outdir>/<id>/wave0/slots.jsonl`.  Verified: a full gate run leaves all three
kept corpora untouched to the nanosecond, and each of the four sub-gates was
checked in isolation.  All three corpora are `chmod -R a-w` (0 writable
entries); three full baseline runs finished rc=0 with 0 SKIPPED against them.

### The 2026-09-16 12:08 rewrite: checked, nothing was lost

Another agent's ExploreMain run rewrote `slots.jsonl` under both kept
`f651c4879` corpora at 12:08.  `restore_slots.sh <id> <corpus> <case>`
re-derives the campaign's own table with the corpus's **own frozen jar**
(`<corpus>/schedule/frozen-inputs/GraphChecker.jar`) in a staging iteration
directory of symlinks — nothing is written under a corpus.  The table is a
fold and nothing else feeds it (`SlotTable.read` reads only
`<iteration>/slots.jsonl`, `reconcile()` takes the corpus's session rows and
the anchor's closure), so the replay is: empty table → wave 0 over the seed
session with empty results → wave 1 over every session with the campaign's
`obligation_results.jsonl` and the prior table, with the flags
`campaign_explore` holds constant across waves.

| corpus | rows before | wave 0 → last wave | manifest `skeleton.slots` | replay vs corpus file |
|---|---|---|---|---|
| 17960 #8 | 40 | 32 → 40 | 40 | **byte-identical** |
| 11741 #3 | 426 | 257 → 426 | 426 | **byte-identical** |

The replayed last wave's `obligations.jsonl`, `tasks.jsonl`, `gaps.jsonl` and
`explore_manifest.json` are identical to the corpus's `obligations-0001`, and
composing with the frozen jar over the file reproduces the corpus's own
`schedule/final/candidate.smt2` byte for byte (17960 `4fbd100d…`, 11741 #3
`b0fa23d6…`) and its manifest with `smt2Path` removed.  Composing over the
corpus file and over the replayed file gives the same smt2 and the same
manifest, so **17960's compose digest is unchanged between the "overwritten"
and the re-derived table** — they are the same bytes.  No file was replaced;
both paths were `chmod a-w` again.

This also settles the 11741 #3 attribution below: the `f651c4879` jar over
this slot table reproduces that corpus's published claim exactly, so the
different numbers under `e33e72351` are the engine change and nothing else.

## Corpora and where the case values come from

| corpus | out dir | experiment dir |
|---|---|---|
| 17960 | `$MY/final-f651c4879/out/hdfs-17960` (pass #8, jar `f651c4879`) | `$SPO/wt-stage/experiments/hadoop/hdfs-17960` |
| 11741 | `$MY/final-e33e72351-11741/out/hdfs-11741` (campaign #4, jar `e33e72351`) | `$SPO/wt-stage/experiments/hadoop/hdfs-11741` |

`$SPO=/tmp/claude-20003/-opt-GraphChecker/99c84a54-86ac-44a4-a030-760f664ae2a1/scratchpad`,
`$MY=/tmp/claude-20003/-opt-GraphChecker/10153a9a-290a-45d1-b3c9-072f259e090e/scratchpad`
(override with `GATE3_SPO`, `GATE3_MY`, `GATE3_REPO`, `GATE3_CORPORA`,
`GATE3_SUBGATES`, `GATE3_JAVA`, `GATE3_Z3`, `GATE3_XMX`, `GATE3_STRIP`).

Nothing is hard-coded per case.  Every case-specific value — anchor, bounds,
root domains, symbolic inputs, trace test, solver limits, loop bound, class
dirs — is parsed out of the case's own `workflow.properties` exactly as
`run_engine.sh` parses it (last assignment wins; `@config/x` resolves to the
case dir, a bare relative path to the repo root).  The gate then checks the
sha256 of each declaration against the sha256 the corpus recorded for the same
file in `schedule/iteration-0000/iteration_manifest.json` `.provenance`, and
publishes the result as a `meta` row — so a declaration that has drifted since
the corpus was recorded is visible in `DIGESTS.txt` rather than silently
changing a sub-gate's answer.

The epoch is read from the corpus's own wave-0 `explore_manifest.json`
(`.topologyEpoch` = `iteration-0000` for both corpora).

## The command lines

Every JVM is launched the way `run_engine.sh:run_java_main` launches it —
the case's `java_bin` (`experiments/hadoop/hdfs-*/java.sh` =
`/usr/lib/jvm/java-8-openjdk-amd64/bin/java -Xmx8g`) plus
`-Dcausynth.loop.default.bound=<causynth_loop_default_bound>` (8 for both
cases) — with `nice -n 10` added and stdin closed:

    cd <outdir> && nice -n 10 /usr/lib/jvm/java-8-openjdk-amd64/bin/java -Xmx8g \
      -Dcausynth.loop.default.bound=8 -cp <jar>[:<project classpath>] <MainClass> …

### 1. `wave0` — `run_engine.sh:campaign_explore`, wave 0 (line 2035)

    edu.uva.liftlab.graphchecker.explore.ExploreMain \
      --sessions          <outdir>/<id>/wave0/sessions \
      --results           <outdir>/<id>/wave0/obligation_results.jsonl   # empty
      --static-scope-map  <corpus>/static_scope_map.jsonl \
      --topology-epoch    iteration-0000 \
      --wave              0 \
      --output-dir        <outdir>/<id>/wave0/obligations-0000 \
      --target-occurrence <declared_target_occurrence> \
      [--root-domains <case>/root-domains.jsonl]    # 11741 only
      [--max-tasks 128]                             # 11741 only (region_path_max_tasks)

17960 declares no `causynth_root_domains` and no `region_path_*` bound, so it
gets neither flag; neither case sets `region_path_max_paths_per_region` or
`region_path_max_flips_per_path`.

`--sessions` is a directory of symlinks to **the seed replay session only**
(`seed-result-*`).  That is the session set wave 0 actually read: every other
session in the kept corpus is named after a wave-0 obligation and was written
by that obligation's worker, after this JVM had already run.  Verified: with
the seed-only set both corpora's `obligations.jsonl`, `tasks.jsonl` and
`gaps.jsonl` come back **byte-identical to the kept corpus**.

### 2. `compose` — `run_engine.sh:do_compose` (line 647)

    edu.uva.liftlab.graphchecker.compose.ComposeMain \
      --sessions          <corpus>/schedule/iteration-0000/sessions   # all sessions
      --output            <outdir>/<id>/compose/candidate.smt2 \
      --manifest          <outdir>/<id>/compose/candidate_composition_manifest.json \
      --solver-timeout-ms 1800000 \
      --max-valuations    128 \
      --z3                /usr/local/bin/z3 \
      --anchor            <declared_target_occurrence> \
      [--root-domains <case>/root-domains.jsonl]    # 11741 only

### 3. `plan` — the offline re-derivation of the plan from the kept recording

`run_engine.sh:do_workload` pass 2 (line 724) followed by
`run_engine.sh:do_schedule` (line 635), with the workload replaced by the
recording the corpus kept.  The recorder owns its `--trace-dir`, so the kept
`runtime_trace.jsonl` + `streaming_trace_manifest.json` are copied into
`<outdir>/<id>/plan/trace` first and made writable there (the corpora are
read-only).

    -cp <jar>:$(<case>/classpath.sh)      # run_java_main adds project_classpath
                                          # for the recorder only
    edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
      --trace-dir        <outdir>/<id>/plan/trace \
      --candidate-graph  <corpus>/candidate_dataflow_edges.jsonl.gz \
      --region-skeletons <corpus>/runtime/skeleton-pass/region_skeletons.jsonl \
      --refined-graph    <outdir>/<id>/plan/refined_dataflow_edges.jsonl.gz \
      --test             <trace_test> \
      --output-dir       <outdir>/<id>/plan

    edu.uva.liftlab.graphchecker.plan.ConcolicScheduler \
      --region-plan       <outdir>/<id>/plan/concolic_region_plan.jsonl \
      --output-dir        <outdir>/<id>/plan/schedule \
      --candidate-graph   <corpus>/candidate_dataflow_edges.jsonl.gz \
      --static-scope-map  <corpus>/static_scope_map.jsonl \
      --max-jobs          128 \
      --closure-mode      candidate \
      --symbolic-inputs   <case>/symbolic-inputs.jsonl \
      --target-occurrence <declared_target_occurrence>

Nothing was pruned: both corpora kept the pass-2 trace (17960 16 MB, 11741
6.0 MB), the pass-1 skeletons and the candidate graph, so this sub-gate runs
for both.  If an input were missing the sub-gate would print
`SKIPPED pruned input(s): <paths>`.

`symbolize=N[kind:count,…]` counts the `inputActions` whose `mode` is
`SYMBOLIC` — the plan's instruction to symbolize that root — keyed by
`rootKind`, or by `sourceKind` where an action states no `rootKind`
(a communication-site port does).

### 4. `static` — the SEED stage's first `do_analyze` (line 1482 → 486)

The discovery pass, with no `CAUSYNTH_TRACE_MODE`, so no workload is needed.
28 s for 17960, 20 s for 11741.

    timeout 900 … java -Xmx8g \
      -Dcausynth.output.dir=<outdir>/<id>/static/out \
      -Dcausynth.target.spec=<case>/target.yaml \
      -Dcausynth.trace.test=<trace_test> \
      -Dcausynth.loop.bounds=<case>/loop-bounds.jsonl \
      -Dcausynth.loop.default.bound=8 \
      -Dcausynth.region.skeletons=<outdir>/<id>/static/out/runtime/skeleton-pass/region_skeletons.jsonl \
      [-Dcausynth.communication.mappings=<case>/communication-mappings.jsonl]  # 11741 only
      -Dcausynth.symbolic.inputs=<case>/symbolic-inputs.jsonl \
      -cp <jar>:$(<case>/classpath.sh) \
      edu.uva.liftlab.graphchecker.GraphCheckerMain \
      -i /tmp/graphchecker-hdfs-<case>-classes \
      -x $(<case>/classpath.sh) \
      -C <case>/workflow.properties \
      -o <outdir>/<id>/static/instrumented-classes

`causynth.output.dir` is the only place `GraphCheckerMain` takes its output
from (`CausynthTargetResolver.java:28`), so redirecting it keeps every artifact
inside `<outdir>`; `/tmp/graphchecker-hdfs-<case>` is never created.  The
hadoop trees are read for `classpath.sh` (a surefire report) and for
`target/test-classes` only.

### Deviations from `run_engine.sh`, and why

* **cwd** is `<outdir>`, not `graphchecker_work_dir` (the repo root), so a
  stage that wrote a relative path could not touch the read-only source tree.
  Every argument is absolute; the outputs come back byte-identical to the
  corpus, so no stage depends on the cwd.
* **`nice -n 10`** and closed stdin are added; a campaign lane is running.
* `wave0` uses the seed-only session set (justified above) and its own
  sessions directory (see the slot-table warning); `compose` uses the corpus's
  full session set, as `campaign_compose` does.
* No `--retain-regions`, and `--closure-mode candidate`: that is what
  `campaign_plan` passes for `iteration-0000`, whose parent is the seed.

## What is normalised, and why

Determined empirically: the baseline jar was run twice and every produced file
compared byte for byte.  **Exactly one field of one artifact differs between
two runs of the identical inputs**:

    .smt2Path   candidate_composition_manifest.json
                <run dir>/<id>/compose/candidate.smt2

So the normaliser (`norm.py`) does two things and no more:

* **masks** run-local absolute paths in the serialised row:
  `<outdir>`→`<OUT>`, `<jar>`→`<JAR>`, `<corpus>`→`<CORPUS>`,
  `<case dir>`→`<CASE>`.  The `<OUT>` mask is the one that is load-bearing
  (`.smt2Path`); the others are there so a gate run from a different corpus
  copy or a differently-named jar still compares.
* **re-serialises** each row with sorted keys and no whitespace, then sorts
  the rows with `LC_ALL=C sort` (streamed through `sort`, never held in
  Python — `execution_task_plan.jsonl` is 58 MB) and hashes the stream.

**No field is stripped by name.**  `GATE3_STRIP` exists but is empty: no
digested artifact contains a timestamp, a duration, a counter or a random id.
`candidate.smt2` and the `.jsonl.gz` products need no normalisation at all —
`candidate.smt2` is hashed raw, the gzip products are hashed over their sorted
decompressed rows (gzip framing carries an mtime).

**Nothing is excluded for nondeterminism.**  The two baseline runs produced
identical `DIGESTS.txt`.

## Superseded baseline table (jar `e33e72351`, `$MY/r3/baseline.jar`)

> This table and the section after it record the gate at staging tip
> `e33e72351`.  They are kept for the record and were **not** refreshed when
> the baseline moved to `122069b02`, `48dece245` and now `1357116d1`.  The
> authoritative row list for the current baseline is
> `baseline/DIGESTS.txt`; the dated sections above say what moved and why.

`meta` rows — declaration provenance vs the corpus that recorded it.  Every
declaration of both cases now matches; the only non-`yes` is a key the
provenance schema does not carry:

| corpus | declaration | matches corpus |
|---|---|---|
| 17960 | workflow.properties, target.yaml, loop-bounds.jsonl, symbolic-inputs.jsonl | yes |
| 11741 | workflow.properties, target.yaml, loop-bounds.jsonl, communication-mappings.jsonl, symbolic-inputs.jsonl | yes |
| 11741 | root-domains.jsonl | UNRECORDED (the provenance has no rootDomains key) |

| corpus | gate | artifact | sha256 | counts |
|---|---|---|---|---|
| 17960 | wave0 | obligations.jsonl | `36e4bb83…` | **obligations=4**, sessionsRead=1 |
| 17960 | wave0 | explore_manifest.json | `e7d0f06c…` | state=OBLIGATIONS_PROPOSED tasks=11 proposed=4 answered=0 gaps=ADMISSION_GAP:40 |
| 17960 | wave0 | tasks.jsonl | `89f094c5…` | rows=11 |
| 17960 | wave0 | gaps.jsonl | `3897f602…` | rows=40 |
| 17960 | compose | candidate.smt2 | `4fbd100d…` | bytes=29690 asserts=18 |
| 17960 | compose | manifest | `de0d29c1…` | paths=3 families=12 roots=1 valuations=2 gaps=2 finalStatus=FINAL_READY |
| 17960 | compose | claim | `0cbdacc8…` | **claim=SAT_CANDIDATE findingKind=MARKER_FLIPPED movedRoots=HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false valuationOrdinal=1** polarityDecides=true z3=sat/EXACT_REACHABLE blockers=0 |
| 17960 | plan | concolic_region_plan.jsonl | `0819f057…` | rows=46 |
| 17960 | plan | execution_task_plan.jsonl | `3fbf622b…` | rows=45 symbolize=4[OBSERVED_FIELD_RECEIVER:4] |
| 17960 | plan | schedule_index.json | `f14ce285…` | members=45 target=TASK.SEED.bd900252… |
| 17960 | plan | refined_dataflow_edges | `9722144b…` | rows=3559 |
| 17960 | static | static_scope_map.jsonl | `5ddf776d…` | rows=1053 |
| 17960 | static | candidate_dataflow_edges.jsonl.gz | `8d6bdf6d…` | rows=8833 |
| 17960 | static | region_skeletons.jsonl.gz | `81dac2da…` | rows=372 |
| 17960 | static | communication_gaps.jsonl.gz | `a4f7c555…` | rows=75 |
| 11741 | wave0 | obligations.jsonl | `0fd7b42a…` | **obligations=36**, sessionsRead=1 |
| 11741 | wave0 | explore_manifest.json | `b357ef02…` | state=OBLIGATIONS_PROPOSED tasks=78 proposed=36 answered=0 gaps=TOPOLOGY_DIVERGENCE:12,ADMISSION_GAP:271,LINEAGE_LOST:3 |
| 11741 | wave0 | tasks.jsonl | `3c28c34f…` | rows=78 |
| 11741 | wave0 | gaps.jsonl | `1c459142…` | rows=286 |
| 11741 | compose | candidate.smt2 | `50fc5bed…` | bytes=103036 asserts=74 |
| 11741 | compose | manifest | `15485f56…` | paths=7 families=5 roots=14 valuations=4 gaps=241 finalStatus=FINAL_READY |
| 11741 | compose | claim | `af19dc55…` | **SUPERSEDED — this was `e33e72351`.** It read `claim=UNSAT_CLOSED findingKind=NO_SUPPORTED_WITNESS movedRoots=none valuationOrdinal=0 polarityDecides=true z3=unsat/NO_EXACT_REACHABILITY blockers=0`.  **Since the `r3/C` merge it is `claim=INCONCLUSIVE_PARTIAL … polarityDecides=false … blockers=1`** (current baseline sha `571a8dc7…`) |
| 11741 | plan | concolic_region_plan.jsonl | `fc0886e6…` | rows=85 |
| 11741 | plan | execution_task_plan.jsonl | `bfed9dca…` | rows=84 symbolize=23[CALL_RETURN:13,COMMUNICATION_SITE_PORT:10] |
| 11741 | plan | schedule_index.json | `a4422d11…` | members=84 target=TASK.SEED.c2604501… |
| 11741 | plan | refined_dataflow_edges | `55221a03…` | rows=782 |
| 11741 | static | static_scope_map.jsonl | `a276f132…` | rows=172 |
| 11741 | static | candidate_dataflow_edges.jsonl.gz | `bf3ab201…` | rows=1268 |
| 11741 | static | region_skeletons.jsonl.gz | `55c091df…` | rows=46 |
| 11741 | static | communication_gaps.jsonl.gz | `6399db94…` | rows=4 |

Full sha256 values are in `baseline/DIGESTS.txt` (42 rows: 32 artifacts +
10 meta; no SKIPPED).

## Wall time (`baseline/TIMES.txt`)

| corpus | wave0 | compose | plan.aggregate | plan.schedule | static |
|---|---|---|---|---|---|
| 17960 | 1 s | 2 s | 7 s | 2 s | 27 s |
| 11741 | 1 s | 5 s | 2 s | 1 s | 19 s |

**Whole gate: 83–85 s** over three runs (budget was ~25 min).  Peak JVM heap `-Xmx8g`;
`<outdir>` needs ~120 MB (the 58 MB task plan and the 32 MB region plan for
17960, plus the 16 MB trace copy).

## What the `e33e72351` baseline said about the kept corpora (superseded)

* **11741 campaign #4 is reproduced exactly, in every sub-gate.**  It was
  produced by the baseline jar itself with the current declarations, so
  wave-0 `obligations.jsonl`/`tasks.jsonl`/`gaps.jsonl`,
  `concolic_region_plan.jsonl`, `execution_task_plan.jsonl`, `candidate.smt2`
  (sha `50fc5bed…`), `static_scope_map.jsonl` and all three `.jsonl.gz`
  products are byte-identical to the corpus.  Its claim **was**
  `UNSAT_CLOSED` / `NO_SUPPORTED_WITNESS` with `blockers=0` and
  `finalStatus=FINAL_READY` **at `e33e72351`; since the `r3/C` merge the claim
  is `INCONCLUSIVE_PARTIAL` / `NO_SUPPORTED_WITNESS` with `blockers=1` and
  `finalStatus=FINAL_REFUSED`**.  The corpus `result.json` states
  `claim=UNSAT_CLOSED finalStatus=FINAL_READY gapCount=5` (the manifest's
  `gaps=241` is the whole gap array, of which 5 reach the final report).
* **17960 is reproduced exactly except for the two static products the engine
  changed after the corpus was recorded.**  wave-0 obligations/tasks/gaps,
  `concolic_region_plan.jsonl` and `candidate.smt2` (sha `4fbd100d…`) are
  byte-identical to the corpus, and the claim is `MARKER_FLIPPED` moving
  `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false` at `valuationOrdinal=1` — the
  expected baseline.  Under the baseline jar `static_scope_map.jsonl` has
  **1053** rows where the corpus (jar `f651c4879`) has 810, and
  `candidate_dataflow_edges.jsonl.gz` differs; re-running the same sub-gate
  with the corpus's own frozen jar returns 810 rows and both files
  byte-identical, so the delta is `f651c4879`→`e33e72351`, not the gate.  The
  same jar delta makes 17960's `execution_task_plan.jsonl` 57811607 bytes
  against the corpus's 57804467 (same task ids and schema; some tasks carry
  different `inputActions`), byte-identical under the corpus jar.
* The superseded **11741 campaign #3** corpus
  (`$MY/final-f651c4879-11741/out/hdfs-11741`) is no longer used.  For the
  record, it was a FAIL run — `claim=INCONCLUSIVE_PARTIAL`,
  `finalStatus=FINAL_REFUSED`, `findingKind=NO_SUPPORTED_WITNESS`,
  `blockers=1`.  Its `slots.jsonl` was rewritten by a third party at 12:08:56
  on 2026-09-16; the re-derivation above proves the bytes are the campaign's
  own, and that the `f651c4879` jar over them still yields that published
  claim.

## External inputs the gate does not own

* `/tmp/graphchecker-hdfs-17960-classes`, `/tmp/graphchecker-hdfs-11741-classes`
  — the production classes `prepare-analysis.sh` builds, read (never written)
  by `static` and by the `plan` recorder's classpath.  Both were last written
  on 2026-09-11/12 and the corpus provenance records their digests.  A
  campaign that rebuilds them changes the `static` digests.
* `/opt/hadoop-hdfs-17960-jdk8`, `/opt/hadoop-hdfs-11741` — read for
  `classpath.sh` and `target/test-classes`.
* `/usr/local/bin/z3` (4.8.12) and `/usr/lib/jvm/java-8-openjdk-amd64`.
