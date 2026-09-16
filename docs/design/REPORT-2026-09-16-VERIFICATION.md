# REPORT — verification rounds and the 11741 push (2026-09-15 17:35 → 2026-09-16 06:50 CDT)

Continues `REPORT-2026-09-15-CLEANUP2.md` (cleanup round 2: M4o, R1, G2–G6, P-A, R2, P-B, then
G7–G9, W17960, C11-prep, C11-plan, F17960, C11-replay). Sources: the planner log
`memory/graphchecker-refactor-goal.md` (entries from 2026-09-15 17:35 CDT on; the earlier block
labelled 23:00–02:40 is ~5 h too late), `memory/graphchecker-verification-runbook.md`,
`memory/case-11741-notes.md`, `memory/identity-v3-execution-index.md`, `memory/cleanup2-rulings.md`,
the staging log `2126e1e47..089a36aad`, and the on-disk corpora named below.

```
SPO=/tmp/claude-20003/-opt-GraphChecker/99c84a54-86ac-44a4-a030-760f664ae2a1/scratchpad
SPN=/tmp/claude-20003/-opt-GraphChecker/3230912f-3427-4c18-a306-eb2005a43b37/scratchpad
MY=/tmp/claude-20003/-opt-GraphChecker/10153a9a-290a-45d1-b3c9-072f259e090e/scratchpad
```

## 1. hdfs-17960 CLEAN PASS on 6f6f88ec6 — verification #7

2026-09-16 06:25 CDT, `$MY/verify_final.sh 6f6f88ec6`, image build24, 974 s, exit 0:

```
hdfs-17960  exit 0  974 s  SAT_CANDIDATE  FINAL_READY  blockers -  gaps 0
plain sat | buggy sat | other unsat  ->  PASS
MARKER_FLIPPED at valuation 1 moving HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false;
the recorded valuation refutes the recording (polarityDecides)
```

Measured in `$MY/final-6f6f88ec6/out/hdfs-17960/schedule/iteration-0000`:
- seed session `seed-result-5caa9286`: 90 activations, 1113 decisions, 66 writes, 38 reads,
  1 root, 2 targets, 0 exports / 0 attaches (17960 is single-node).
- `import_gate.json`: 1 session, 15 violations, **0 blocking**, 15 diagnostic, all LINEAGE_LOST.
- 3 sessions in the accepted corpus (seed + 2 focused); wave 0 = 4 obligations, wave 1 = fixed
  point (`obligations-0000`, `obligations-0001`).
- `final/result.json`: claim SAT_CANDIDATE, findingKind MARKER_FLIPPED, valuationOrdinal 1,
  polarityDecides true, reachability EXACT_REACHABLE, solverState sat, finalStatus FINAL_READY,
  finalStatusRefusals 0, **gapCount 0**, telemetryCount 247, accepted true.
- `final/candidate_composition_manifest.json`: 3 paths, 2 valuations, 1 root, anchorId
  `0c9fd0c268832276`, `symbolicPropagationComplete: true`, and 16 DECLARATION_MISSING gaps all
  **DIAGNOSTIC** — unlike verification #4, which carried five BLOCKING-class coverage gaps.
- valuation 0 (`ORDERED=true`) unsat, valuation 1 (`false`) sat — the polarity decides.
- target occurrence: `hdfs-17960/nn0#epoch1/region/REGION.f0132fca…/ctx:Anchor:cb189bd419932b69@`
  `HADOOP_IPC/checkpoint-namespace/idx:…serializeSnapshotSection@0`.

Artifacts committed as staging tip **089a36aad** ("hdfs-17960: composed query from verification #7
on 6f6f88ec6 — clean pass"). Log `$MY/verify-6f6f88ec6.log`, report
`$MY/final-6f6f88ec6/report/hdfs-17960/report.md`, probe
`$MY/final-6f6f88ec6/report/hdfs-17960/probe.tsv`. main `/opt/GraphChecker` is still 3d9355745;
staging is 432 first-parent commits ahead.

## 2. The seven verification rounds, and what each caught

All seven are the ONE thorough verification of the merged tree (`$MY/verify_final.sh <tip>`), not
per-mandate gates; each failure produced one mandate for the whole defect class.

1. **#1 on 9d2761c17** (17:45 CDT) — died at REPLAY in 330 s: JVM `VerifyError` in woven
   `FSNamesystem.allowSnapshot` @142 `lload_2`; G6's region-entry token (`long
   $causynthRegionEntry`) is read in a woven catch-all whose trap range starts at bci 0, before
   the token store. → **G7**: the trap begins after the store, the rule applies to every woven
   construct, Soot body validation at weave time, and a fail-closed `VerifyWovenClasses` gate in
   INSTRUMENT (15/18 campaign classes were unverifiable on 9d2761c17). Merged → 8563092dc.
2. **#2 on 8563092dc** (18:55 CDT) — died at REPLAY: 18/18 classes verified, workload ran, but 14
   `TASK_UNANSWERED OCCURRENCE_ANCHOR_UNMATCHED` — planned vs ran differed ONLY in the anchor
   digest (`Anchor:81d0aa0dbdd84d73` vs `5cd4981c9a67d41e @HADOOP_IPC/checkpoint-namespace`),
   index identical. Cause: the anchor's `siteIndex` **k was counted per thread**, and a retried
   send during the NN restart consumed a k. → **G8** (k counts the occurrence's own events;
   endpoint components stated in EXCHANGE rows and refusal details; one plan row per occurrence;
   residual shared addresses BLOCKING). The same round exposed R1's deleted JUnit-5 (jupiter)
   runner — all six workloads are jupiter and 11741's classpath has no junit-4 jar → **R3** (one
   reflective jupiter runner; merged 8a4f1809c).
3. **#3 on 4ed6bcd75** (19:40 CDT) — first end-to-end run on the cleaned tree (495 s:
   REPLAY→IMPORT→EXPLORE→COMPOSE→SOLVE→DECIDE→EMIT) but `UNSAT_CLOSED` /
   `NO_SUPPORTED_WITNESS`; 13 refusals at a uniform −1 shift of `applyEditLogOp@k`, and
   `DECLARATION_MISSING` BLOCKING refused the second MARKER root. First blamed on workload
   nondeterminism (G9's "replay applied 9 edit-log ops vs 10" — a miscount of distinct k), then
   **corrected at 21:15 CDT**: an **unpaired identity region pop** (`popActiveRegion` CRR:4495 and
   the `else if (identityRegionEntered)` path :726) let `regionExit` wipe the closed occurrence's
   per-site counters, so `applyEditLogOp` restarted at k=0 mid-loop. → **W17960** (one push / one
   pop, region-depth check under `FRAME_UNBALANCED`, refusals name the differing component); the
   17960 workload determinism edits (`hdfs-17960-deterministic-edits.diff`) were kept as case prep.
4. **#4 on 7d18b9f2a** (21:44 CDT) — **PASS with gaps**: MARKER_FLIPPED at valuation 1, 880 s, 5
   BLOCKING-class coverage gaps the gate does not withhold on (DECLARATION_MISSING ×2 on
   `isSnapshotDeletionOrdered#u1` occurrence 2 exceeding the frozen phase catalog;
   OCCURRENCE_ADDRESS_SHARED ×3 on the InitQuotaTask ForkJoin siblings), one ADMITTED `#u7` flip
   path cut by PROPAGATION_CUT, two dead declarations, 42 LINEAGE_LOST rows. → mandate **F17960**
   (one root symbol per declared configured source; OCCURRENCE_ADDRESS_SHARED class = kept-closure
   membership with the stated `cls` read by run_engine; no dead declarations; sibling-activation
   mint rows joined, 2→3 paths; `probe_final.sh` reads `manifest.roots`). Merged 22db72c7c.
5. **#5 on 46a3224f5** (02:45 CDT) — REGRESSED at REPLAY (targets 0, 14 refused): the refusal named
   frame 0 = `Server.start()#u31` planned @3 vs ran @0 — G11's `scopeStart` clamp leaked the
   pooled handler thread's start frame into anchored addresses (which handler serves a request is
   scheduling). → **G12** `Identity.scopeStart(Hop)`: an ANCHOR hop indexes from the inbound
   scope, a STARTED_ROOT tick from its claimed start frame, a SCOPE_ROOT from its own start.
   Merged d11af42c3; 17960 seed targets 2 / 0 unanswered again.
6. **#6 on 05f4bf265** (04:15 CDT) — harness PASS but the **WRONG claim**:
   `MESSAGE_PAIRING_FLIPPED` at valuation 0 (the recorded valuation), polarityDecides true, 6
   BLOCKING OCCURRENCE_ADDRESS_SHARED, sessions with 0 exports/attaches. Two consequences.
   (a) **C17** (merged fd4505746): a path's valuation is what its replay RAN the root at — the
   mint's `recordedValue` where read, the obligation's `rootAssignments` where planted
   (`Corpus.rootValue`), fail-closed both ways; one obligation ledger `contract/ObligationDir`.
   Offline on the #6 corpus this restored MARKER_FLIPPED@1 with valuation 0 unsat.
   (b) the harness gate itself did not check the finding against the case's expected mechanism —
   §3 below.
   C17 also found the #6 recording had 46 EXCHANGE_SEND / 28 distinct producer ids (six
   create-snapshot RPCs from main shared one endpoint; k did not advance after G11/G12) → 158
   OCCURRENCE_ADDRESS_SHARED, 6 BLOCKING. → **G13** (merged d41019516): an event's k is counted at
   `(level, root hop, site)`, never under a live-read causal context (the RPC response scope left
   standing on the client made every `Client.call` frame restart at @0); `Lineage.anchor()` stops
   at the innermost root hop. 17960: 46/46 distinct sends, OCCURRENCE_ADDRESS_SHARED 158→3
   (quota ForkJoin workers, diagnostic, not closure members); 11741: 72/72 and 85/85 plan rows.
7. **#7 on 6f6f88ec6** (06:25 CDT) — CLEAN PASS (§1): 0 gaps, 0 blockers, probe buggy sat / other
   unsat, 974 s.

## 3. The per-case harness gate (2026-09-16 04:40 CDT)

`$SPO/final/report_final.py:159` now carries an `EXPECTED_MECHANISM` table, and PASS additionally
requires, per case, the expected mechanism, a non-empty `movedRoots` and `valuationOrdinal ≥ 1` —
on top of SAT_CANDIDATE / FINAL_READY / no blockers / polarityDecides:

| case | expected |
|---|---|
| hdfs-17960 | MARKER_FLIPPED moving `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` to `false` |
| hdfs-11741 | CLOCK_SKEW or MARKER_FLIPPED |
| hdfs-17897 | CLOCK_SKEW |
| hdfs-17899-bug1/bug2/bug3 | MARKER_FLIPPED or CLOCK_SKEW |

`RECORDED_FAILURE_EXPLAINED` can no longer PASS (no root moved), and verification #6's
`MESSAGE_PAIRING_FLIPPED@0` now reads FAIL. Backups `*.bak-20260916-expected` next to the scripts
(`report_final.py`, `lib_final.sh`).

## 4. HDFS-11741 — prep → seed → campaign #2 → X15

Declared target (`experiments/hadoop/hdfs-11741/workflow.properties:38`): `hdfs-11741/dn1#epoch0/…
@hdfs-11741/balancer#epoch0/balance-block#1`. Expected finding: CLOCK_SKEW with polarityDecides
over ≥ 2 CLOCK roots — two flips on two nodes (NN rotation-2's `removeExpiredKeys` drops G from
the export AND the DN's `addKeys` scan removes G before re-putting the received set, BTSM:248 vs
:255). Mechanics: `REPORT-CASE-11741.md`, `memory/case-11741-notes.md`. Ordered history:

- **Workload prep (C11-prep, 18:03 CDT)** — `/opt/hadoop-hdfs-11741` edited so the BPServiceActor
  heartbeat threads carry a DN source anchor and per-turn requests (diff
  `$SPN/d-runtime/workload/hdfs-11741-bpserviceactor.diff`, 3 files); tree rebuilt (295 s),
  workload test passes. Known remaining hole (planner: leave): `processQueueMessages()`
  error/bad-block RPCs are outside the tick.
- **SEED / PLAN / INSTRUMENT pass** — on 7d18b9f2a, first time for all three: SEED aggregated 65
  region plans with 0 duplicate ids, PLAN passed with declared roots as regions (C11-plan: a
  declared symbolic input's method is a region root BY DECLARATION at all four P1 points, and every
  READY planned occurrence is a seed task), INSTRUMENT 72 bodies, verifier 0 rejections, guard
  table 5/7.
- **Replay hang fixed (C11-replay, 23:40 CDT, 52db33137)** — cause:
  `SymbolicMessageEnvelope.decode` refused the NN registration response at `MAX_WIRE_LENGTH` (94%
  of every entry was `plannedExportConsumers` ids, which had no reader) → IOException into
  `BPServiceActor.register` → infinite retry (the 51-min hang with `Problem connecting to server
  localhost:36449` ×1517). Fixed: consumer ids off the wire (CSE5), `MAX_WIRE_LENGTH` gone, and a
  header/envelope this side will not install is a `MESSAGE_CONTEXT_REFUSED` row while the message
  goes on — never a throw into the workload. Replay completed in 980 s (169 activations, 232
  exports, 42 attaches, 21 roots = 13 CLOCK + 8 INTEGRAL, gate 0 blocking) but targets 0.
- **Throughput fixed (C11-move, 00:20 CDT, 33e3a923f)** — every thread serialized on the
  `ConcolicTaskPlan` monitor computing address sha256 in `addressDifference` per candidate, and
  `rootHookGroup` was O(tasks) per root entry. Refusal detail computed once, ids cached, hook
  groups indexed → replay 980 → 318 s. The 20 balancer moves the DN had refused with
  `ReplicaAlreadyExistsException` were this convoy starving the heartbeat threads (0 refused after).
- **Identity G10–G13** — G10 (d5c913335): a started work claims its start frame at its FIRST
  identity event (CLAIM_START woven at the work's functional-method entry in both passes,
  `plan/WorkStartSites` the one list); a CLOCK mint states the instant this replay read (it had
  been publishing the PLAN's instant as `recordedValue`). SASL producer ids 8→16 distinct, PLAN
  65→74. G11 (46a3224f5): an index frame at every application-scope method in both passes (PEPID
  calling context, +5% replay), `Root:<role>/<api>#k` causal context, a daemon tick is its own
  root, `scopeStart` never hides a claimed start frame → seed exit 0, targets 4 including the
  declared `balance-block#1`, TASK_UNANSWERED 0, PLAN 84/84, gate 0 blocking. G12 (d11af42c3) and
  G13 (d41019516) as in §2.
- **Closure X11/X12** — the first full 11741 campaign (02:45 CDT) ran end to end in 448 s but
  FINAL_REFUSED: EXPLORE wave 0 proposed 0 (TOPOLOGY_DIVERGENCE 224 — reads whose writer is an
  ambient, non-task occurrence present in the corpus; ADMISSION_GAP 39) and COMPOSE raised 6
  BLOCKING `UNSTATED_VALUE` "one solver name for 2 roots" (a declared cell read in `updateKeys`
  published both as a region-input placeholder and as the declared root). **X11** (dd84fae3b):
  write/read order compares the rows' own seqs (`Corpus.seqByEndpoint` deleted — one endpoint id
  named every event of an un-indexed site); a configured-source row that reused a minted symbol is
  not a second root (`RowPublication.minted`; the SERIAL_NO recorded value was silently a rotation
  late); one SMT symbol reachability (`SmtLowering.reachedSymbols`, `FlipQuery.reached` deleted) →
  wave 0: 46 tasks, 1 obligation, 0 BLOCKING. **X12** (aaae344ad, plus
  `region_path_max_tasks=128` → 05f4bf265): a read's row symbol is recorded on the subterm it
  produced (`SmtLowering.observing`), reachability answers names-to-bind and states-demanded off
  one walk, and `StaticScopeMap.sameType` matches a container store's javaType L to the cell's
  descriptor → the `allKeys` MAP read is no longer inlined away, so its static WRITE_SITE writers
  join the closure. Wave 0 offline: 78 tasks, 36 obligations
  (`retrieveDataEncryptionKey#u8`, `addKeys#u21` ×18, `removeExpiredKeys#u15` ×17 incl. nn0 ×5),
  29 SAT models including CLOCK skew on the nn0 expiry guards, 0 BLOCKING. Notes then: `#u7` is
  not a guard of the `Iterator.remove` write (post-dominance says `#u15` only); nn0 `updateKeys`
  members propose 0; `FlipQuery` has no real `v_C` variable yet (a separate design piece).
- **Wave explosion X13** — campaign #2 (05:05 CDT) was killed at wave 1: wave 0 = 36 obligations
  over only 9 distinct `(site, ordinal, outcome)` tuples → 32 ADMITTED + 4 NOT_ADMITTED; wave 1 =
  **706** obligations, still the same 9 tuples — E10 deduplicated per session-specific occurrence,
  so every focused session re-proposed the same static arms. **X13** (758017f1f): an obligation's
  identity is `(task, site, ordinal, outcome)`, owed **once across the corpus**; `Frontier` is the
  one ledger of recorded + answered arms (SAT_MODEL_READY still owed); `ADDRESS_UNSTABLE`
  diagnostic. Wave 1 706 → 30 → 0, wave 2 fixed point; 84 tasks answered at exactly one address
  each across the 81 sessions (addresses are stable across focused sessions). Composition on the
  33-session state: 27 paths, unsat closure complete, NO_SUPPORTED_WITNESS; the BLOCKING left was
  C17's valuation double-statement on SERIAL_NO (session 869a1f0e: the mint states 182907, the
  obligation assigns 182910 — the plant did not happen at that mint site).
- **Session roles X14** (06:50 CDT, 6f6f88ec6) — a session STATES its role
  (`contract/SessionManifest`: SEED | FOCUSED + obligation ids), never inferred;
  `SESSION_INCOMPLETE` named at IMPORT; one mint-value decision for field mints too
  (`mintExactFieldLeaf` asks `focusedRootValue`); `ASSIGNMENT_UNPLANTED` BLOCKING when a replay
  cannot plant an assigned root.
- **X15 — OPEN, in flight.** Worktree `$MY/wt-x15`, branch `fix/focus-minting-occurrences`, based
  on 6f6f88ec6, **no commits yet**. Mandate: an obligation must focus the **minting occurrence** of
  every root it assigns; models keep only reached roots; new refusal `ASSIGNMENT_UNMINTABLE`. This
  is the direct answer to X13's SERIAL_NO double-statement. Then **11741 campaign #3**.

## 5. Known residue (named, not fixed)

1. **3 OCCURRENCE_ADDRESS_SHARED** on 17960, DIAGNOSTIC — the quota `InitQuotaTask` ForkJoin
   workers (the JDK fork site is unweavable); not closure members, so not BLOCKING (G13, 06:20 CDT).
2. **`Identity.here()` degraded occurrences still index from the thread root** — 17960's 23 handler
   RESPONSE sends carry `Server.start#u31@k`. The fix exists as the unlanded commit **8b9b5c0dd**
   "index a degraded occurrence from its scope root" (G12 left it out deliberately).
3. **Loop-body regions are not levels** — 5 addresses × 13 activations at `REGION.16ba41cf` on
   11741 (G11 residue).
4. **`Lineage` `InheritableThreadLocal` kept** — the replay has no other carry across
   `Thread.start`; the carried-scope ABI covers the rest.
5. **Hadoop-side fragility**: `Server$RpcCall.run` calls `enterCarriedScope`/inbound **before** its
   `try`, so a throw there sends no response. Move inside the `try` at the next hadoop rebuild.
6. **P-C** — the `RuntimeRefinedGraphBuilder` residue P-B could not remove: accessor ports must
   become static (site-level) and the occurrence binding must come from rows, then the builder plus
   `edgesByRegion` scoping and `runtimeAccessorBindings` are deleted. 17960's only symbol flows
   through it, so a 17960 regression follows it.
7. **Lineage 0-Lost gate** — verification #7 still reports 15 LINEAGE_LOST at the IMPORT gate (40
   diagnostic rows across the 3 sessions), plus 16 DECLARATION_MISSING diagnostic in the
   composition manifest and 6 MESSAGE_CONTEXT_REFUSED + 4 TASK_UNANSWERED diagnostic rows.
8. Also pending from earlier: the wire ABI item (`consumerOccurrenceIds`, CSE4 format) is batched
   with the next hadoop-tree rebuild; 11741's `FlipQuery` has no real `v_C` variable.

## 6. Corpora kept, and where

| path | what | size |
|---|---|---|
| `$MY/final-6f6f88ec6` | **the clean 17960 run** (verification #7, 3 sessions, FINAL_READY) | 261 M |
| `$MY/final-05f4bf265-11741` | the **81-session 11741 corpus** from campaign #2 (seed + focused) | 428 M |
| `$MY/final-05f4bf265` | 17960 verification #6 (the wrong-claim corpus C17 bisected offline) | 262 M |
| `$MY/final-7d18b9f2a` | 17960 verification #4 (PASS with gaps) | 221 M |
| `$MY/final-46a3224f5-11741` | 11741 campaign #1 (FINAL_REFUSED; X11's evidence) | 50 M |
| `$MY/corpus/sessions` | the accepted 3-session 17960 corpus that reproduces MARKER_FLIPPED | 4.3 M |
| `$MY/laneA10/seed-17960` | reference seed (guard-table and E12 numbering evidence) | 327 M |

Disk was pruned to 24 GB free on 2026-09-16 06:50 CDT (removed `final-9d2761c17`,
`final-8563092dc`, `final-4ed6bcd75`, `final-46a3224f5`, the `lane11741*` lanes, the
x13/pb/c11plan/basesrc/g11/r1 corpora and the d-runtime seed-p2h/p2n/g2/seed corpora); ~23 GB free
now, harness gate `MIN_FREE_GB=6`. **Stale**:
`$SPN/d-runtime/accepted/17960-laneA8-sessions` composes `paths=0` on every current jar — never use
it; use `$MY/corpus/sessions` or `$MY/final-6f6f88ec6`.

## 7. Code size at 089a36aad

src/main **72,537** lines over 159 files (`find src/main -name '*.java' | xargs cat | wc -l` in
`$SPO/wt-stage`): runtime 24,639, causynth 16,778, compose 9,376, plan 7,740, contract 5,883,
explore 4,546, smt 3,016, option 146, annotation 51, transformer 29. 47 `@Test` (cap 100). The low
mark this cycle was 68,836 at P-B (2026-09-15 17:35 CDT); G7–G13, W17960, C11-*, F17960 and
X11–X14 added the identity, gate, wire and obligation-ledger code back.

## 8. Ordered next steps

1. **X15** — merge `fix/focus-minting-occurrences` (`$MY/wt-x15`) when it reports; review against
   the frozen design, then build + 47 `@Test` + `src/test/shell/run_engine_campaign_helpers_test.sh`.
2. **11741 campaign #3** — `$MY/campaign_11741_<tip>.sh` (copy the `05f4bf265` one; change `lane`,
   `OUT` and the log it waits on). Expect CLOCK_SKEW with polarityDecides over ≥ 2 CLOCK roots,
   multi-wave. Verify-first list in `memory/case-11741-notes.md`.
3. **17897** — seed, then campaign (expected CLOCK_SKEW).
4. **17899 bug1 / bug2 / bug3** — declared targets in `experiments/hadoop/hdfs-17899/case.sh`;
   bug2/bug3 also carry the `HDFS.RPC.SEND_FAILURE` marker. Pre-existing: analysing 17899 by hand
   outside its campaign dies in `WireFlowCatalog.fromConfiguration` ("capture method did not
   resolve: `PBHelperClient.convert(DataEncryptionKey)`") — check when 17899 runs.
5. **Residue** (§5), in that order: degraded-occurrence indexing (8b9b5c0dd), loop-body levels, the
   `Server$RpcCall.run` scope calls, the 0-Lost lineage gate.
6. **P-C**, then the 17960 regression after it.
7. staging → main ff-merge; final report (line counts, test count, six-case claim table); remove
   stale worktrees; prune `d3-handover/`.
