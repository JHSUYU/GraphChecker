# Round 3 — phase 2 list (accumulated handoffs; planner's file)

## From M-R2 (2026-09-16 13:10)
- seq==0 rule (one commit): `DecisionRow` gains `vmClock` (false when the mapping has no `vmEventId`); `RowRuntime.sequence` stops borrowing `LAST_SEQ` — a clockless decision states seq 0 + vmClock false (its `term` is empty, so π is unaffected); `RowPublication.decisions` reads it. Contract + runtime + codec + RowInvariants.
- `AttachRow.pairedBy` (one commit): the attach row states which key answered (handle | correlation+port); producer `Interactions.Pairing.key()` already computes it.
- `RuntimeTraceContext.parentSpanId`: delete after M-PC drops the recorder/planner readers.
- `RuntimeTraceContext` T5 → `TraceSpanView` split; `RowRuntime` W5 → `Identity` fold (call sites in CRR/recorder).
- `RowRuntime.statedType` `depth > 64` silent cut → named cut (same shape as the four M-R2 fixed).
- NOT dead (survey wrong): `REQUEST_OCCURRENCES`; SSC's 6 constants (now private).

## From the README draft
- external-callers.txt lacks `beginDaemonTick`, `endDaemonTick`, `enterCarriedScope`, `exitCarriedScope` (called from both hadoop trees) — add to the pinned resource + the ABI test.
- Acceptance harness in-tree home: `experiments/hadoop/accept/{accept.sh, probe.sh, report.py}` from $SPO/final/*, with the per-case expected-mechanism table; README §6 TODO resolves to it.
- README §4: state-location owners are runtime object ids (`INSTANCE/<id>`, `MAP/<id>`), not allocation-site indexes — rewrite the paragraph after M-C's Arms.namedOwner fix lands; verify what makes an object id stable across replays.

## From the plan survey (not yet assigned)
- `ConcolicScheduler` split (+ `SymbolicInputSelection`), `RuntimeWorkflowDiscovery` fold → `SeedTaskPlan`; `SeedBackwardStaticAnalyzer` split (+ edge-emission suppression measurement); `CausynthPipeline` split into weave/*; `SharedExpressionTable`/`VmExpressionTable` artifact half (ruling: keep RawResolver's native DAG interning via its own `expanded` map; delete Decoder/Store/Builder artifact half); unused imports tree-wide; the three undeclared properties (grep experiments/** + hadoop trees first — `causynth.trace.start.paused` may be live).
- Deferred as documented limits: §2.2 Lost → empty index, §2.3 ITL, §2.4 loop-body level.

## From M-PC (2026-09-16 13:05)
- Relocations deferred (add coupling unless done together): RRP P20 trace types → causynth/SeedTraceEvents; recorder T5/T6/T7 → SeedTraceAggregator/SeedTraceReader; OccurrenceBinding fold (UNREGISTERED_SOURCE_KEY has 5 readers in 3 packages). Decide after M-PC2: either move the whole seed-aggregation program (recorder T5–T7 + RRP + trace types) into causynth/ as one package move, or leave it in runtime/ and say so in the README.
- Cluster A renamed/documented as region scoping (failureDirectedClosure → the static graph's region selection) — README §3 PLAN row.
- Two recording passes stay (measured); README §3 SEED row must say pass 1 (lite, candidate regions) selects the skeletons, pass 2 (rich, selected regions) records identity/decisions/captures.

## From M-R1 (2026-09-16 13:25)
- `LoopAccounting.checkReplayLoopBody` is fail-open where `checkLoopBackedge` is fail-closed (cut at 316) — make the control flow one rule.
- `resolveSwitchBranch`'s malformed switch domain (plan/weave disagreement about a switch's static domain): no GapKind names it (0 switch rows on both corpora) — ruling needed: add `PLAN_WEAVE_DISAGREEMENT`? (contract change) or fold into DECLARATION_MISSING.
- `claimStart`'s `RowRuntime.gap(..., "")` for a null carrier throws on `Fields.text` (blank subject) — pre-existing, in RowRuntime.
- `FaultMarker` (C12, ~70 lines) split not done; `FrameJournal` eviction left as a bounded leak (documented at CRR `journalRegion`).
- Gate note: `candidate_dataflow_edges.jsonl.gz` is not a usable invariant across any change to CRR's member count until M-PC2 item 1 lands.

## From M-C (2026-09-16 14:05)
- Runtime (M-R3): focused root mints publish empty `recordedValue` (invariant 8, BLOCKING) — 17960 #8 focused sessions on SNAPSHOT_DELETION_ORDERED, 11741 #4 five CLOCK roots; fix in RootMint/RowPublication: the mint row states the value the region would have read without the plant; the valuation is the session's.
- `SessionReader.gaps` field: keep (its SESSION_INCOMPLETE check on a truncated gaps.jsonl is live); `AttachRow.correlationId`: wire field, batch with the next hadoop rebuild if ever.
- `Composer.integral` (was "Composer:1817 fail-open") is the boolean-root rule — fine.

## Docs (with the README rewrite)
- `docs/CONCOLIC_INTEGRATION.md` cites deleted mechanisms (GapLedger at :719, and likely linked replay / validate / carriers) — rewrite or delete every doc under docs/ that describes a deleted design; the README becomes the one design document, docs/ keeps only build/VM instructions that are still true.
