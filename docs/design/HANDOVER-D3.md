# HANDOVER — GraphChecker Design 3 (stop snapshot 2026-09-16 07:00 CDT)

Single entry point. `d3-handover/` holds durable copies of the design docs, reports, scripts and
long-term memory (originals live in /tmp scratchpads that can be cleaned). The live memory index is
`/users/ZhenyuLi/.claude/projects/-opt-GraphChecker/memory/MEMORY.md`;
`graphchecker-refactor-goal.md` there is the dated log of every ruling and tip — **entries labelled
2026-09-15 23:00 through 2026-09-16 02:40 are ~5 h too late (CDT/UTC confusion); every entry from
`2026-09-15 17:35 CDT` onward is CDT and correct.** The main agent is the Fable planner (design,
mandates, merges); code is read and written by Opus subagents. Goal (owner's words): in-JVM symbolic
propagation + symbolic merging produce the `.smt` for an ad-hoc coordination failure's fatal
condition, z3 decides; get the six cases under `experiments/hadoop` through; delete the bloat. **No
VALIDATE stage** — the deliverable is `candidate.smt2` + the z3 verdict + the claim.

```
SPO=/tmp/claude-20003/-opt-GraphChecker/99c84a54-86ac-44a4-a030-760f664ae2a1/scratchpad
SPN=/tmp/claude-20003/-opt-GraphChecker/3230912f-3427-4c18-a306-eb2005a43b37/scratchpad
MY=/tmp/claude-20003/-opt-GraphChecker/10153a9a-290a-45d1-b3c9-072f259e090e/scratchpad
```

## 0. State

### 0.1 hdfs-17960 CLEAN PASS on 6f6f88ec6
Verification **#7**, image build24, 2026-09-16 06:25 CDT:
```
hdfs-17960  exit 0  974 s  SAT_CANDIDATE  FINAL_READY  blockers -  gaps 0
plain sat | buggy sat | other unsat  ->  PASS
MARKER_FLIPPED at valuation 1 moving HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false;
the recorded valuation refutes the recording (polarityDecides)
```
Seed `seed-result-5caa9286`: 90 activations / 1113 decisions / 66 writes / 38 reads / 1 root /
2 targets (0 exports, 0 attaches — 17960 is single-node). 3 sessions kept; wave 0 = 4 obligations,
wave 1 = fixed point; IMPORT gate 15 LINEAGE_LOST, 0 blocking. `result.json`: valuationOrdinal 1,
EXACT_REACHABLE, **gapCount 0**, telemetryCount 247. Manifest: 3 paths, 2 valuations, 1 root,
anchorId `0c9fd0c268832276`, `symbolicPropagationComplete: true`, 16 DECLARATION_MISSING gaps **all
DIAGNOSTIC** (verification #4 had five BLOCKING-class ones); valuation 0 (`ORDERED=true`) unsat.
Corpus `$MY/final-6f6f88ec6`, log `$MY/verify-6f6f88ec6.log`, report
`$MY/final-6f6f88ec6/report/hdfs-17960/report.md`; artifacts committed as staging tip **089a36aad**.
Chain unchanged from #4: ordered=false → unordered `deleteSnapshot#u7` → the list keeps 1 element
while numSnapshots = 0+1+1−1−1 = 0 → the serializer writes 1 and reads 0 → `1 != numSnapshots` fatal
at `serializeSnapshotSection#u61`; the ordered arm is contradictory.

### 0.2 Branches and worktrees
| branch | tip | worktree | state |
|---|---|---|---|
| `main` | **3d9355745** | /opt/GraphChecker | untouched; ff-merge is the last step |
| `refactor/flatten-handoff-next` (**staging**) | **089a36aad** | `$SPO/wt-stage` | clean; build + 47 @Test + `src/test/shell/run_engine_campaign_helpers_test.sh` green |
| `fix/focus-minting-occurrences` (**X15**, in flight) | 6f6f88ec6 | `$MY/wt-x15` | dispatched, no commits yet |
| `fix/vm-live-read-version` (VM) | b45005b45 | `$SPO/wt-vm2` | merged; source of image build24 |
| (verification #7 lane jar) | 6f6f88ec6 detached | `$MY/wt-verify-6f6f88ec6` | keep until X15 lands |

**432** first-parent commits on staging since main. `git -C /opt/GraphChecker worktree list` is
authoritative; never remove a worktree while a lane runs under it.

### 0.3 The seven verification rounds, and what each caught
All seven are the ONE thorough verification of the merged tree (`$MY/verify_final.sh <tip>`), not
per-mandate gates; each failure produced one mandate for the whole class. Symptoms, numbers, file:line
and the mandate diffs: `d-refactor/REPORT-2026-09-16-VERIFICATION.md` §2.

| # | tip | what it caught | mandate |
|---|---|---|---|
| 1 | 9d2761c17 | REPLAY 330 s: JVM `VerifyError` in woven `FSNamesystem.allowSnapshot` @142 — the region-entry token is read in a catch-all whose trap starts before the store | **G7**: trap after the prologue, Soot body validation at weave time, fail-closed `VerifyWovenClasses` in INSTRUMENT |
| 2 | 8563092dc | REPLAY: 14 `OCCURRENCE_ANCHOR_UNMATCHED` differing only in the anchor digest — siteIndex **k was counted per thread** and a retried send consumed one. Also exposed R1's deleted jupiter runner | **G8** (k counts the occurrence's own events); **R3** (one reflective jupiter runner) |
| 3 | 4ed6bcd75 | first end-to-end run (495 s) but UNSAT_CLOSED, 13 refusals at a uniform −1 shift of `applyEditLogOp@k` — an **unpaired identity region pop** (`popActiveRegion` CRR:4495, `else if (identityRegionEntered)` :726) wiped per-site counters | **W17960**: one push / one pop, depth check under `FRAME_UNBALANCED` |
| 4 | 7d18b9f2a | **PASS with gaps** (880 s): 5 BLOCKING-class coverage gaps the gate does not withhold on (DECLARATION_MISSING ×2, OCCURRENCE_ADDRESS_SHARED ×3), one `#u7` path cut by PROPAGATION_CUT, two dead declarations, 42 LINEAGE_LOST | **F17960** |
| 5 | 46a3224f5 | REPLAY regression: `Server.start()#u31` planned @3 vs ran @0 — G11's `scopeStart` clamp leaked the pooled handler's start frame into anchored addresses | **G12** (`Identity.scopeStart(Hop)`) |
| 6 | 05f4bf265 | harness PASS but the **WRONG claim** (MESSAGE_PAIRING_FLIPPED@0, 6 BLOCKING OCCURRENCE_ADDRESS_SHARED); and 46 sends / 28 distinct producer ids | **C17** (a path's valuation is what its replay RAN the root at) + the per-case gate (§0.4); **G13** (k at `(level, root hop, site)`) → 46/46 distinct, 158→3 shared, diagnostic |
| 7 | 6f6f88ec6 | **CLEAN PASS** (§0.1) | — |

### 0.4 Per-case harness gate (2026-09-16 04:40 CDT)
`$SPO/final/report_final.py:159` carries `EXPECTED_MECHANISM`; PASS now additionally requires, per
case, the expected mechanism, a non-empty `movedRoots` and `valuationOrdinal ≥ 1` — on top of
SAT_CANDIDATE / FINAL_READY / no blockers / polarityDecides. 17960 = MARKER_FLIPPED moving
`HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` to `false`; 17897 = CLOCK_SKEW; 11741 and 17899-bug1/2/3 =
CLOCK_SKEW or MARKER_FLIPPED. `RECORDED_FAILURE_EXPLAINED` can no longer PASS (no root moved), and
verification #6's `MESSAGE_PAIRING_FLIPPED@0` now reads FAIL. Backups `*.bak-20260916-expected`.

### 0.5 HDFS-11741 — seed and campaign #2 done, X15 open
Declared target (`experiments/hadoop/hdfs-11741/workflow.properties:38`):
`hdfs-11741/dn1#epoch0/…@hdfs-11741/balancer#epoch0/balance-block#1`. Expected: CLOCK_SKEW with
polarityDecides over ≥ 2 CLOCK roots — two flips on two nodes (NN rotation-2's `removeExpiredKeys`
drops G from the export AND the DN's `addKeys` scan removes G before re-putting the received set,
BTSM:248 vs :255). Mechanics, declared cells and the seven verify-first items:
`d-refactor/REPORT-CASE-11741.md`, `memory/case-11741-notes.md`; every row below with its numbers and
mandate diff in `REPORT-2026-09-16-VERIFICATION.md` §4.

| item | state |
|---|---|
| workload prep (C11-prep) | DONE — the BPServiceActor heartbeat threads carry a DN source anchor and per-turn requests (`$SPN/d-runtime/workload/hdfs-11741-bpserviceactor.diff`); tree rebuilt, test passes. Open on purpose: `processQueueMessages()` RPCs are outside the tick |
| SEED / PLAN / INSTRUMENT | PASS since C11-plan — 65 region plans 0 duplicate ids, declared roots are regions by declaration, 72 bodies, verifier 0 rejections, guard table 5/7 |
| replay hang (C11-replay) | FIXED — the envelope refused the NN registration response at `MAX_WIRE_LENGTH` (94% of each entry was plan consumer ids, no reader) → IOException into `BPServiceActor.register` → infinite retry. Ids off the wire (CSE5), `MAX_WIRE_LENGTH` gone, a refusal is a `MESSAGE_CONTEXT_REFUSED` row and never a throw |
| throughput (C11-move) | FIXED — the `ConcolicTaskPlan` monitor convoy → replay 980 → 318 s; the 20 refused balancer moves were that convoy starving the heartbeat threads |
| identity (G10–G13) | FIXED — CLAIM_START at the work's first identity event, index frame at every application-scope method, `Root:<role>/<api>#k`, ticks are roots, `Identity.scopeStart(Hop)`, k at `(level, root hop, site)` → seed→IMPORT exit 0, PLAN 84/84, targets 4 incl. `balance-block#1`, TASK_UNANSWERED 0, gate 0 blocking |
| closure (X11/X12) | FIXED — row seqs order reads/writes, a reused minted symbol is not a second root, one SMT reachability, container dags expand to their state symbols so the `allKeys` MAP read is demanded → wave 0: 78 tasks, 36 obligations, 29 SAT models incl. CLOCK skew on the nn0 expiry guards, 0 BLOCKING |
| wave explosion (X13) | FIXED — obligation identity `(task, site, ordinal, outcome)` owed once across the corpus → wave 1 706 → 30 → 0, wave 2 fixed point; 84 tasks at exactly one address each across 81 sessions |
| session roles (X14) | DONE — a session STATES its role (`contract/SessionManifest`: SEED \| FOCUSED), `SESSION_INCOMPLETE` at IMPORT, field mints ask `focusedRootValue`, `ASSIGNMENT_UNPLANTED` BLOCKING |

**X15 — THE OPEN ITEM**: worktree `$MY/wt-x15`, branch `fix/focus-minting-occurrences`, based on
6f6f88ec6, **no commits yet**. An obligation must focus the **minting occurrence** of every root it
assigns; models keep only reached roots; `ASSIGNMENT_UNMINTABLE`. It answers campaign #2's one
remaining BLOCKING — the SERIAL_NO valuation double-statement (session 869a1f0e: the mint states
182907, the obligation assigns 182910, so the plant did not happen at that mint site). Then **11741
campaign #3**.

### 0.6 Known residue (named, not fixed)
1. **3 OCCURRENCE_ADDRESS_SHARED** on 17960, DIAGNOSTIC — the quota `InitQuotaTask` ForkJoin workers
   (unweavable JDK fork site); not closure members.
2. **`Identity.here()` degraded occurrences index from the thread root** — 17960's 23 handler
   RESPONSE sends carry `Server.start#u31@k`; fix exists as the unlanded commit **8b9b5c0dd**.
3. **Loop-body regions are not levels** — 5 addresses × 13 activations at `REGION.16ba41cf` (11741).
4. **`Lineage` `InheritableThreadLocal` kept** — the replay has no other carry across `Thread.start`.
5. **Hadoop-side**: `Server$RpcCall.run` calls `enterCarriedScope`/inbound **before** its `try` (a
   throw there sends no response) — move inside the `try` at the next hadoop rebuild.
6. **P-C** — the `RuntimeRefinedGraphBuilder` residue (TODO 6); and 15 LINEAGE_LOST at the IMPORT
   gate on 17960 (40 diagnostic rows) toward the 0-Lost gate.

### 0.7 Code size, images, trees, corpora
- src/main **72,537** lines over 159 files (`find src/main -name '*.java' | xargs cat | wc -l` in
  `$SPO/wt-stage`): runtime 24,639, causynth 16,778, compose 9,376, plan 7,740, contract 5,883,
  explore 4,546, smt 3,016, option 146, annotation 51, transformer 29. 47 @Test. Low mark this cycle
  68,836 (P-B); G7–G13, W17960, C11-*, F17960, X11–X14 added identity, gate, wire and
  obligation-ledger code back.
- **Image: `$SPO/images/j2sdk-image-build24` only** (VM tip b45005b45 / VM25); earlier images
  deleted. Every campaign and seed passes `CAUSYNTH_CUSTOM_JDK_HOME=<build24>`.
- Hadoop trees `/opt/hadoop-hdfs-{17960,17960-jdk8,17897,11741,17899-base,17899-bug1,bug2,bug3}`:
  Java 8 `package` builds with the tracing diffs in `$SPN/d-runtime/workload/`. **They carry
  uncommitted owner changes — never `git checkout/stash/reset/commit/clean` in them.**
- Corpora kept: `$MY/final-6f6f88ec6` (**the clean 17960 run**, 261 M), `$MY/final-05f4bf265-11741`
  (**81-session 11741 corpus**, 428 M), `$MY/final-05f4bf265` (#6, 262 M), `$MY/final-7d18b9f2a`
  (#4, 221 M), `$MY/final-46a3224f5-11741` (campaign #1, 50 M), `$MY/corpus/sessions` (accepted
  17960, 4.3 M), `$MY/laneA10/seed-17960` (reference seed, 327 M). **Stale**:
  `$SPN/d-runtime/accepted/17960-laneA8-sessions` composes `paths=0` on every current jar. z3 4.8.12
  at `/usr/local/bin/z3`; ≈23 G free; harness gate `MIN_FREE_GB=6`.

## 1. Design rules — frozen; changing one needs an owner ruling
Full text: `d-design/` (REFACTOR-D3, DESIGN3-PLAN, INTERACTION-ID, IDENTITY-V3, IDENTITY-IMPL,
CLOSURE-V2, LEAN-DESIGN) + `d-refactor/CONTRACT-SPEC.md` (row contract v2.4). Finish implementing it,
pass the six cases, delete bloat — do not redesign.

1. **Core principle** (`memory/graphchecker-core-design-principle.md`): runtime symbolic propagation
   carries values (roots are manual; expressions ride with values in the JVM and across the wire);
   the static graph only **scopes** — one decision, the root-dependence slice; an anchor identifies
   the same target occurrence across replays; the composer is `Fatal_T = ⋁_paths (π_p ∧ φ)`, lowered
   once to SMT, solved by z3, gated fail-closed. Anything that decides "what matters" outside the
   slice, finds writers via the graph, synthesizes a value, or adds a cap/default/heuristic is
   REJECTED at review.
2. **Pipeline** (no VALIDATE): PLAN → INSTRUMENT → REPLAY(seed) → IMPORT (one file per row kind + the
   fail-closed gate) → EXPLORE (waves) → COMPOSE (one anchor) → SOLVE → DECIDE → EMIT. Epoch rule
   `retained set must grow: <regionId>` → new epoch, INSTRUMENT `--retain-regions`, inputs frozen.
3. **Identity v3** (`d-design/IDENTITY-V3.md`): `(node#epoch, regionId, CausalContext,
   ExecutionIndex)`; `CausalContext ∈ {Anchor(producerEndpointId, rpcSite) | Root(role/api, k) |
   Lost(role)}`, lineage recursing Anchor→Root to the innermost root hop; `ExecutionIndex` = the
   call-site frame list from `Identity.scopeStart(Hop)`; `Endpoint = (occurrence, site, siteIndex,
   attempt)`, k at `(level, root hop, site)`; no thread id, address, handle or counter in an id.
4. **Contract invariants** — full list in CONTRACT-SPEC v2.4; added this round: an obligation's
   identity is `(task, site, ordinal, outcome)` owed once across the corpus (X13), a path's valuation
   is what its replay RAN the root at (`Corpus.rootValue`, C17), a session STATES its role (X14).
   Still biting: ONE guard authority (`static_scope_map`/`SiteControlDependence` gives φ's polarity);
   `DecisionRow.term` has no polarity; a flip candidate is ANY DecisionRow with a non-empty term; an
   unbound model symbol is `UNPRODUCIBLE_ANSWER`, not SAT; a z3 `(error …)` is NOT_ADMITTED, never
   UNSAT; rows state `cls`. Declared roots: `memory/root-selection-policy.md`; one declared target
   per case (17960 / 11741 / 17897 in `workflow.properties`, the 17899 bugs in `hdfs-17899/case.sh`).
5. **Identity pass-equality rule** (G2–G13; `memory/identity-v3-execution-index.md`): ONE function
   **and one input set** in both passes. Fed identically by the SEED recording and every replay: node
   attribution (receiver source + start-frame inheritance); the region frame set (every skeleton root
   opens a frame in BOTH passes; rich and lite hooks never both on one method); thread-start frames
   claimed at the work's FIRST identity event; the index frame at every application-scope method;
   loop-root frames and any loop-iteration charge (a replay-only hook must not feed the address); the
   producer endpoint (occurrence, transport site, k-th event at that site in that occurrence);
   read/write siteIndex. **Any new hook that pushes a frame or counts an event is woven in both
   passes or in neither**, every push paired one-for-one with its pop (`FRAME_UNBALANCED`). Gate:
   SEED 0 unexplained collisions; replay planned == ran for every answered task; IMPORT gate 0
   violations; wave 0 obligations unchanged.
6. **LOV extension — only if nondeterminism actually bites**: the workload declares the varying loop
   and a monotone per-iteration value (e.g. the edit-log txid in `applyEditLogOp`) replacing that
   loop's iteration count in the index, fed identically in both passes. PEPID aligns iteration k with
   iteration k, so one extra or missing iteration shifts every later address — refused fail-closed, by
   design. Not pre-emptively: both candidates so far were engine defects (W17960).

### 1.1 Process rules (owner rulings; violations mean rework)
- **Delete first, no compat** (`memory/cleanup2-rulings.md`) — no adapters or stubs. A "no reader"
  claim needs the grep over `run_engine.sh`, `experiments/**`, `src/test/**` and the hadoop trees'
  `src` (R1 deleted the only JUnit-5 runner on a false claim and cost a round); deleting a published
  member requires its readers listed by `git grep` on the merged staging tip **and** every in-flight
  branch, in the commit message.
- **Change first, then verify** — done = build clean + unit tests + shell test + offline checks on
  KEPT corpora; **no new recording per mandate**; recordings and the full campaign happen once, on
  the merged tree.
- **Fix the flow, not the bug** — state the defect as a class, enumerate the fixed function's inputs
  per pass and stage, trace it through rows → gate → explore → compose → claim with expected numbers,
  check in-flight overlap, put the invariant in the IMPORT gate or a test.
- **Case prep determinism** — pin or disable the daemons and timers writing state in the instrumented
  window (NN autoroll, lease/resource monitors, DN heartbeat and key-update periods); explicit awaited
  checkpoints/restarts; no RPC retries across restarts. A different NUMBER of iterations is refused.
- Suite stays at a few dozen `@Test` (cap 100; now 47); no debugging tools, no HDFS class names in
  src/main (0 today). Max **two** campaign lanes; one script per lane; main untouched until ff-merge.
- `/opt/hadoop-*`: never `git checkout/stash/reset/commit/clean`; Java 8 `package` only; never rebuild
  a tree while a lane on that case runs; tracing edits permitted, diffs kept.
- Silence is a violation: refusals name the row, field and owner; gap rows are never truncated away;
  reports carry file:line and corpus numbers; the planner re-checks claimed evidence with its own
  greps before merging (`memory/subagent-rules-of-engagement.md`).

## 2. Ordered TODO
1. **Merge X15** when it reports (`$MY/wt-x15`, on 6f6f88ec6): an obligation focuses the minting
   occurrence of every assigned root, models keep only reached roots, `ASSIGNMENT_UNMINTABLE`. Review
   against §1, then build + 47 @Test + shell test.
2. **11741 campaign #3** — `bash $MY/campaign_11741_<tip>.sh` (copy
   `$MY/campaign_11741_05f4bf265.sh`; change `lane`, `OUT` and the log it waits on). Expect CLOCK_SKEW
   with polarityDecides over ≥ 2 CLOCK roots, multi-wave (two flips, two nodes). Run the seven
   verify-first checks of `memory/case-11741-notes.md` on the seed first.
3. **17897** — seed, then campaign. Expected CLOCK_SKEW.
4. **17899 bug1 / bug2 / bug3** — declared targets in `experiments/hadoop/hdfs-17899/case.sh`;
   bug2/bug3 also carry the `HDFS.RPC.SEND_FAILURE` marker. Pre-existing: analysing 17899 by hand
   outside its campaign dies in `WireFlowCatalog.fromConfiguration` ("capture method did not resolve:
   `PBHelperClient.convert(DataEncryptionKey)`").
5. **Residue** (§0.6), in order: re-land `8b9b5c0dd`; loop-body regions as levels; move the
   `Server$RpcCall.run` scope calls inside the `try` at the next hadoop rebuild (batch the CSE4
   `consumerOccurrenceIds` wire-ABI deletion with it); then the **lineage 0-Lost gate**
   (`memory/lineage-must-be-complete.md`) until the gate is 0 on all six cases.
6. **P-C** — the residue P-B could not remove: accessor **ports become static** (site-level) and the
   **occurrence binding comes from rows**, then `RuntimeRefinedGraphBuilder`, `edgesByRegion` scoping
   and `runtimeAccessorBindings` are deleted. 17960's only symbol flows through it → regression after.
7. Then staging → main ff-merge; final report (line counts, test count, six-case claim table); remove
   stale worktrees; move what is still useful out of `d3-handover/`, delete the rest.

## 3. Commands
```bash
# build + gates (staging worktree)
cd $SPO/wt-stage && mvn -o -q -DskipTests package && mvn -o -q test \
  && bash src/test/shell/run_engine_campaign_helpers_test.sh

# THE one thorough verification: fresh worktree at <commit>, build, full campaign on build24
bash $MY/verify_final.sh <commit> [hdfs-17960]   # -> $MY/final-<commit9>, $MY/verify-<commit9>.log
#   sets JAR=<lane>/target/…jar, CAUSYNTH_CUSTOM_JDK_HOME=$SPO/images/j2sdk-image-build24,
#   OUT=$MY/final-<commit9>, CASES=<case>, FINAL_KEEP_ALL=1; DRY=1 preflight, then
#   $SPO/final/accept_final.sh (serial under setsid, df gate MIN_FREE_GB=6, pgid in $OUT/pgid)

# lane 2: another case on lane 1's jar. Copy, change lane/OUT/the log it waits on; it sets
# OUT=$MY/final-<tip>-<case>, CASES=hdfs-11741, FINAL_KEEP_ALL=1, CASE_TIMEOUT_SECONDS=14400
bash $MY/campaign_11741_<tip>.sh     # cf. $MY/campaign_11741_05f4bf265.sh

# one case to IMPORT only (seed corpus + row census); sets CAUSYNTH_OUTPUT_DIR / CAUSYNTH_CACHE_DIR /
# CAUSYNTH_CUSTOM_JDK_HOME=<build24> / CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT
bash $MY/seed_11741d.sh 11741        # 17960|17897|11741|bug1|bug2|bug3
python3 $SPN/d-runtime/case_table.py # per-case row census

# rebuild one hadoop tree / run one workload test (Java 8 package; NEVER while its lane runs)
bash $SPN/d-runtime/build_tree.sh /opt/hadoop-hdfs-17897
bash $SPN/d-runtime/workload_test.sh /opt/hadoop-hdfs-17897 <TestClass> <testMethod>

# offline on a KEPT corpus — what a mandate is gated on (wave 0: $MY/gate_wave0.sh)
java -cp $SPO/wt-stage/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar \
  edu.uva.liftlab.graphchecker.d3.compose.ComposeMain --iteration <iteration-0000 dir> \
  --target-occurrence '<v1 selector>' --max-valuations 16 --out <dir>

# stopping a lane: the pgid stops the harness but NOT the focused-replay worker JVMs (run_engine puts
# them in their own group) — kill those by the lane's unique output path.
kill -TERM -- -$(cat $OUT/pgid)
for p in $(pgrep -f 'final-<tip>-<case>'); do kill -KILL $p; done
pgrep -af '<path>[x]'   # bracket trick avoids self-match; NEVER `pkill -f <pattern>` (it matches
                        # the calling shell and kills it, exit 144)

# disk hygiene (gate MIN_FREE_GB=6; ~23 G free) — prune final-* of SUPERSEDED runs only
du -sh $MY/final-*      # keep: final-6f6f88ec6, final-05f4bf265-11741, corpus/sessions, laneA10
```
Per-case `workflow.properties` keys: `declared_target_occurrence`, `compose_max_valuations=128`,
`causynth_loop_default_bound`, `causynth_symbolic_inputs`, `causynth_loop_bounds`,
`solver_timeout_ms`, `campaign_max_iterations`, `causynth_static_scope_map`,
`causynth_region_skeletons`, `campaign_stop_after`, plus 11741's `region_path_max_tasks=128`;
unknown keys are refused. Declared clock cells are `"clock": true` in `symbolic-inputs.jsonl`;
relative domains in `root-domains.jsonl`; WIRE_FLOW records in `communication-mappings.jsonl`.

## 4. Document index (`d3-handover/`)
`d-design/`: REFACTOR-D3, DESIGN3-PLAN, INTERACTION-ID, IDENTITY-V2/V3/IMPL, CLOSURE-V2, LEAN-DESIGN,
REPORT-ENTRY, causal-graph-section.tex. `d-refactor/`: CONTRACT-SPEC (row contract);
**REPORT-2026-09-16-VERIFICATION.md** = the seven rounds, the clean 17960 pass, the harness gate,
11741 through campaign #2, the residue, the corpora; **REPORT-2026-09-15-CLEANUP2.md** = the mandates
before it (M4n/M4o, R1, G2–G9, P-A, P-B, R2, R3, W17960, C11-prep, C11-plan, F17960, C11-replay);
REPORT-CASE-11741; REPORT-ACCEPT-17960; REPORT-SHRINK (+ methods.tsv); the M*/P2*/E*/VM* reports.
`d-runtime/`: seed/build/workload scripts, tracing diffs (`workload/*.diff`, incl.
`hdfs-11741-bpserviceactor.diff`, `hdfs-17960-deterministic-edits.diff`), case_table.py. `memory/`:
copy of the long-term memory — where it differs, the live originals win.

---

## 2026-09-16 (end of session) — STOP SNAPSHOT: this file is superseded by the repository

The owner stopped the work on 2026-09-16 ~16:45 CDT. From now on the entry points are IN THE REPOSITORY, on the single remote branch `main` of git@github.com:JHSUYU/GraphChecker.git:

- `README.md` — the current design (pipeline, identity v3, rows contract, closure v2, composition, claims), the worked 17960 example, and **§9 "Where this stands, and what to do next"** with the ordered to-do.
- `docs/HANDOVER.md` — operational: build, run a case, the acceptance harness (`experiments/hadoop/accept/`), archived corpora and gate scripts, Hadoop workload trees, the `docs/wip/` patches (unfinished halves of FIX1 / R4 / PC4) and how to apply them.
- `docs/wip/{FIX1,R4,PC4}/` — format-patch series + `uncommitted.patch` + NOTES.md for the three mandates stopped mid-work.

Archived on this host (not in git): `/opt/graphchecker-handover/corpora/` (17960 pass #8 and 11741 campaign #4 corpora, the offline gate `gate3/` with its baseline digests) and `/opt/graphchecker-handover/d3-handover/round3/` (round-3 surveys, the 11741 diagnosis `REVIEW-11741-4.md`, the 17960 gate-refusal diagnosis, the README drafts). Hadoop: the two git trees `/opt/hadoop-hdfs-17960{,-jdk8}` pushed to JHSUYU/hadoop `gc/hdfs-17960-snapshot-replay{,-jdk8}`; the six non-git trees' edits captured under `experiments/hadoop/<case>/tree-edits/` and `/opt/graphchecker-handover/hadoop-edits/`.

State at stop: 17960 passes offline on the kept corpus; its last LIVE run (staging 39bedd768) was refused by the new per-wave IMPORT gate (FIX1 fixes the gate's session set, the decisions invariant and a fail-open verdict). 11741: composition decides in seconds, but every valuation is satisfiable because two focused sessions carry the key-serial root's symbol without its mint row (R4). First job for whoever continues: run the acceptance harness on 17960 and 11741 from `main`.
