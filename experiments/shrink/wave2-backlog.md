# Wave 2 backlog (collected from wave-1 executor feedback)

Each line: lane · item · est. lines · what unblocks it. Cross-lane items
are what wave 1 could not do inside one lane.

## smt (from the wave-1 smt report)
- DELETE `concolic/CausalGraphWriter.java` (524) + `run_engine.sh` `campaign_graph()` (~2422-2436) + `graph/causal_model.json` from the optional artifact list (~2441). README:473 = graphs are debug bundles; README "Refactor boundary" lists "default graph generation" as a collapse target; `campaign_graph` already runs under `set +e`. Then `CanonicalSessionModel` reduces to `counts` + `gaps` (~−450) with all SEVEN `run_engine.sh` reads preserved: `canonicalModel.gaps` (2491) and `counts.{unknownArmBindings,candidateBindings,exactBindings,guardedBindings,fieldVersions,fieldReads}` (2652-2658). ≈ −1,000 total.
- `contract/RelationSummary`: add `cases()` and `pathCoverageState()` beside `edgeBindings()` (~line 307); the Composer's 8 `toJson()` re-reads then collapse (≈ −40).
- `RecordedSessionModel.selectorName(long,String)` is now test-only (3 refs in RecordedMapStateTest) — delete with the test lines.
- Third solver attempt in `BooleanReachConditionExtractor.Z3Solver.check`: KEEP. Attempt 2 is the only full-budget run of the tuned options (attempt 0 is capped at min(timeout, 5000)). Inventory was wrong.
- `summaryRows` regionId re-add: KEEP (inventory premise wrong — `compose()` checks the closure's regionId, not the row's).
- Legacy unscoped `resolveEventId("", …)` pass: KEEP — a real empty-scope caller exists at RecordedSessionModel ~980 (`identity == null`).
- The big one (HIGH): second expression encoder `ConcolicConstraintSolver.Encoder` (≈1,500) → keep `ConcolicSmtComposer.Emitter`; one Java-type→SMT-sort enum; one port catalogue.

## operational
- Executors share one scratchpad; one lane overwrote another's `cut.py`. Give each executor a per-lane subdirectory in its brief.
- `mvn test` cannot run mid-wave: test compilation breaks while other lanes are still cutting (expected). The gate runs once, after every lane lands.

## contract (from the wave-1 contract report) — cross-lane follow-ups
- `runtime/RuntimeRegionPlanner.java:6098-6099` stop writing `schemaVersion`/`kind` on handoff rows (reader never reads them); then delete `CommunicationHandoffSpec.SCHEMA_VERSION` + its use in `NestedTargetSelectedRpcHandoffTest:137`.
- `ConcolicSummaryImporter.java:1813`, `ConcolicRegionRuntime.java:566`: drop the unread first argument of `LoopBoundPolicy.acceptsInstrumentedBound(String,int)`; then delete the parameter.
- `DeclaredLoopBodyBoundTest:118,123`: delete the two `boundAuthority` assertions; then delete `LoopBoundPolicy.boundAuthority()` (21).
- `StaticSymbolicSourceSelectionTest:1477,3132`: build declaration rows literally; then delete `ConfiguredSourceSelectorContract.intDeclaration()` (21).
- `RegionPathWorklist.java:297`: drop the `manifestState` argument; then delete the parameter and the `coverage.addProperty("manifestState", …)` write in `RelationSummary`.
- `causynth/DeclaredLoopBodyBounds`: third copy of the 1..64 range check → `LoopBoundPolicy.bodyBound()`.
- JSON helper copies outside the lane (causynth 8 files, runtime 6, concolic 20): `JsonFields` now exports `text(JsonObject,String)` and `trimmed(String)`; `requiredObject/primitiveString/exactInteger` are package-private and need widening.
- RegionInstancePlan's six `*View`/`occurrenceKey`/`containsOccurrence` accessors: all have callers in `RuntimeWorkflowDiscovery`/`ConcolicScheduler` — collapse to one accessor per field is a planning-lane change (wave 2).
- KEEP (unsafe, verified): `declaredOutputPorts` single-shape (changes `closureFingerprint` system-wide); `defaultBackedgeTraversals == 8` guard (LOOP-1); the plan-side decode checks in `RegionInstancePlan` (first-decode point of a different artifact).
- Wave 3 is where this lane's mass is: `ExecutionTask` decode-once (≈200 + ~70 outside), `ConfiguredSourcePhaseContract` dual JsonArray/Map codec (≈60), `RuntimePlanArtifact` triple decode, `PathObservation` 4-pass decode, the pass-through wrappers (`Member`, `InputActionCatalog`, `MaterializationSpec`, `TargetOutcome`).

## runtime (from the wave-1 runtime report)
- GATE ADDENDUM for wave 1: item G (EngineApi + 4 sub-Api classes → one table, −252) keeps all 32 VM entry-point names/signatures and degrade-to-null, but it is the reflective ABI — run the 26-smoke VM gate ([[concolic-vm-abi]] memory) before wave 2, not just the matrix.
- `Configuration.commitMapVersions` / `commitFieldVersions` are now reachable ONLY from `mapVersionLifecycleForTests` / `fieldVersionLifecycleForTests`; production uses `commitSelectedVersions`. When wave 2 restructures shared-state admission, all three pairs die together.
- Runtime copies of the PUBLISH/CONSUME bijection and phase-occurrence ownership checks were deleted (item E). They now depend on `contract/ExecutionTask.validateConfiguredSourceBindings` (~50-72) and the ctor occurrence check (~43-49) staying — the contract lane kept both.
- Behaviour change to remember: `unresolved` is a `LinkedHashSet`; `unresolvedInputs` no longer repeats duplicates.
- `FlatJsonRow` → Gson: accepts lenient JSON the hand scanner refused; interning preserved; string reads of numbers return the original token.
- NOT mergeable (verified, do not re-list): the 7 gap ledgers (5 published keys, 3 serializers, 3 guards across 2 methods); the 3 result envelopes (different status namespaces; `ReadCutGateResult` has none); recorder Lite/full (push-before-budget vs return-before-push; both names AND signatures Soot-bound); map-vs-field planned admission (measured similarity 0.52/0.68, not 0.95).
- 13 of 14 `*ForTests` seams pin admission/lifecycle with no non-test surface — they go when wave 2/3 restructures admission, not before.
- CRR has no remaining dead code (598 methods + all fields scanned).

## planning (from the wave-1 planning report)
- `run_engine.sh:1545,1745` `--target-first` is now accepted-and-ignored (scheduler has one mode); drop it there and from `knownOption` (~ConcolicScheduler:5680).
- `CausynthTraceRecorder.java:985,988` call `RuntimeRefinedGraphBuilder.normalizeNumbersInPlace` — retiring RRGB's number-folding copy needs a replacement that keeps IN-PLACE mutation and NULL-entry retention (`RRP.deepCopyValue` does neither). Cross-lane (runtime ↔ planning).
- `outputOccurrence`/`replayOccurrence`: one value, two keys; six readers outside the lane (`OutputClosureCodec:188,433-436,511-536`, `OutputCaptureSpec:94-115,280`, `ConcolicScheduler:2769`, `RuntimeSelectedRegionFinalizer:1423`) — wave-3 wire cleanup.
- `JsonFields` gaining `requireFile(Path,String)`, `textSet(JsonArray)`, `strings(Collection<String>)` unlocks ~20 more local-copy lines in `ConcolicScheduler`/`TopologyDelta`.
- KEEP (inventory wrong, verified): `RegionPathWorklist.collectAlignmentGaps` kind filter (2nd caller over `explorationRecords` at ~834; CSI:945-952 forwards `member.slice()` gaps unfiltered; guards a past silent-CLOSED incident); the "outside the replay call" refusal in `retainTaskSourcePhases` (catches a selected id absent from the task catalog); `Region.outputRowsByPort` (indexes static region rows, not closure members; poisons duplicate portIds); `runtime/RuntimeRows` (RRP/RRGB helper sets differ in exception type, stream closing, integer fallback — net negative); `dropSourcePhases` merge (net ≈ 0); CSI-vs-TD phase decode (different outputs: admission issues vs schema-digest vocabulary).
- Wave 2 planning lane (unchanged from the inventory): four `*OutputClosure` builders → one (≈270); `resolveSourcePhaseOwnership` → `phaseProjections` union per occurrence per README:964 (≈300; NOTE under the wave-3 design this whole selection layer is deleted anyway — do the upstream union only if wave 2 precedes wave 3 by long enough to matter); fold/unfold pair (≈106).

## static (from the wave-1 static report)
- `runtime/CausynthTraceRecorder.java:1027` change `planned, closure.gaps);` → `planned);` — unblocks deleting the finalizer gap channel (`Result.gaps`, `gap(...)`, 4 `gaps.add`, 4 GAP_* constants ≈43) and `CausynthTraceRecorder.java:1943-1970` (`communication_runtime_gaps.jsonl`, zero readers anywhere).
- `run_engine.sh:500-510` `CAUSYNTH_CONCOLIC_ENVELOPE_REPORT` block is dead (property no longer read).
- `runtime/RuntimeRegionPlanner.fieldOwner` is byte-identical to `causynth/CausynthStaticFacts.fieldOwner` — delete, share (make CausynthStaticFacts public or move to contract/).
- runtime/ twins of the Map coercion family (`rows/asMap/text/strings/number/longNumber`) → use `causynth/MapFields` pattern (or move MapFields to contract/ and share).
- `RecordedReadFrom.java:387,393,408` removes and rewrites `readFromProvenanceGap` — wave-3 decision whether the finalizer must pre-seed it.
- Wave-3 renames blocked by cross-package readers: `anchorMethod` vs `anchorMethods[0]`; `PORT_DEFINITION_METHOD` vs `callerMethod`.
- Bloat the inventory missed (wave-2 static lane): `CausynthPipeline` 49 hand-written 2-3-line hook emissions, duplicated ~40-line argument materialize/symbolize block (region-root vs method-argument), 4× `getThisLocal` dance, 3× `parameterLocal`, 4× unique-original-index scan, 3× get-or-make-phantom-class, 5× `instrumentationSafe` gate, `ReturnStmt/ReturnVoidStmt` twin arms; zero-reader public API on `InstrumentationPlan` (taskId/regionId/occurrenceId/targetMethod/outputRelation/replayAnchorMethods + fields), `ExactHeapOutputCapture.fieldSignature()`, `DeclaredLoopBodyBounds.isEmpty/size/source`, unused 7-arg `CommunicationCallSite.RequestPort` ctor; `SeedBackwardStaticAnalyzer` `intersectsLocal` ≡ `exactIntersects`, `MethodWorkSet`+`DirtyRelevantSet` are one class, 10 cache accessors → one `memoized`, 5× guard-operand walk, `addEdge→addEdgeInternal` shim; `RuntimeSelectedRegionFinalizer` `addUniqueValue` ≡ `addUniqueString`, 7 redundant `emittedEdgeRows.get` re-lookups; `ConcolicInstrumentationSelections` 4 capture views, 3 identical filter/build loops, 4 hand-rolled computeIfAbsent…addAll.
- Second-look items accepted with the matrix as the check: `resolveDeclaredMethod` via `getSubSignature()`; `mintOccurrences` lost an unreachable re-validation; 11 `IllegalStateException` sites without cause.
- KEEP (verified): the 5 `isApplicationClass()` guards (Soot mutable state); `uniqueInstanceField`/`exactInstanceField` (superclass-only, ambiguity scan); `walkFailureClosure`; `failureRelevantFields` ContextCell walk; `declaredField(SootFieldRef)`; `CommunicationCatalogPlanner`'s own `LoopCfg` build (pipeline mutates bodies).

## post-wave-1 scan pickups (trivial, any lane)
- delete `SymbolicEnvironment.java` (root package, 9 lines, zero refs)
- delete `SessionOrderDomain.directKind(long,long)` (4) and `.objectOf(long)` (3); `AutomaticRegionEdge.composable(JsonObject)` (3)
- scan false positive to ignore: `causynth/MapFields` is live via `import static` (scanner ignores import lines)
- POSSIBLY-REFLECTIVE, keep: `CausynthTraceRecorder.beginSourceRequest/endSourceRequest`, `ConcolicRegionRuntime.rejectConfiguredSourceField` (Hadoop adapter getMethod by name)

## runtime (from the wave-2 runtime report)
- Hook-matcher merge (8 materialize/symbolize bodies) does NOT exist as specified: 309 lines (not 730), nine structural disagreements (region resolution, null handling ×2, occurrence minting peek/advance, dedup gate, loop policy, ambiguity, unsupported-model recovery, associative read outside the family). Do not re-list.
- RE-MEASURE before wave 3: `admitPlannedSharedMapState` vs `admitPlannedSharedFieldState` (147 lines) scores 0.831 token similarity on the runtime executor's scan vs 0.52/0.68 in the inventory — largest remaining lever in CRR if the higher number holds.
- `RuntimeSelectedRegionFinalizer.Result.gaps` and `RuntimeRegionPlanner.Result.gaps` now have ZERO readers (runtime dropped `closure.gaps` and the `communication_runtime_gaps.jsonl` write) — static + planning lanes may delete both channels.
- Three more write-only artifacts (~−70), owner to confirm no external consumer: `runtime_occurrence_links.jsonl` (field still live internally at CausynthTraceRecorder:957,973 — delete only the file write), `runtime_refinement_manifest.json` (+4 stage-timing locals), `causal_source_events.jsonl` (`writeSourceEvents`). None in README/docs/run_engine.sh.
- `MapFields` still package-private in causynth/ — runtime's Map-family copies (~20 real) wait on its move to contract/.
- `normalizeNumbersInPlace` callers now at CausynthTraceRecorder:978,981 (planning lane coordination).
- APPROVED (checked 2026-08-25: zero references in run_engine.sh, experiments/*.sh|properties, README, src/test; the only experiments/ hits are this backlog): delete the file WRITES for `runtime_occurrence_links.jsonl` (keep the in-memory `occurrenceLinks` field, live at CausynthTraceRecorder ~957/973), `runtime_refinement_manifest.json` (+4 stage-timing locals), `causal_source_events.jsonl` (`writeSourceEvents`) — ≈ −70, runtime lane, next time it is touched (wave-3 step 1).

## contract (from the wave-2 contract report)
- RULING (planner): accessor-collapse to the one-line house form counts in the nonblank metric but is tracked as "formatting" in the tally, not structural reduction. Wave 2 contract: −284 total = −96 structural + −188 formatting.
- Wave-3 lever: `ExecutionTask` and `RegionInstancePlan` are two JSON views over the same row shape (sourceKey/occurrenceId/relationKey/regionId/goalId/branches()/edgeBindings()/require(); phase validation blocks byte-identical at ExecutionTask:44-48 ≡ RegionInstancePlan:46-50) — merge is allowed to introduce ONE shared base for exactly this pair (rule-3 exception).
- `JsonFields` now exports required/nonNull/requiredArray/requiredObject/requireText/primitiveString/exactInteger — the other ~180 helper lines in RuntimeRegionPlanner(41)/RuntimeWorkflowDiscovery(21)/OccurrenceMinter(19)/RuntimeRefinedGraphBuilder(14)/StaticSymbolicSourceDiscovery(13)/TargetReachPathQueryBuilder(13)/ConcolicScheduler(12)/+14 files can call them; expect a ~35% haircut for the `import static` lines that come back. `primitiveString`/`exactInteger` were widened to public with no cross-package caller yet — revert to package-private if nobody uses them by wave 3's end.
- Stale line numbers corrected: `acceptsInstrumentedBound` callers are ConcolicSummaryImporter:1612 and ConcolicRegionRuntime:446 (drop the unread first param; ≈ −7). `boundAuthority` (LoopBoundPolicy:334, 12 lines) needs DeclaredLoopBodyBoundTest:118 dropped first. `intDeclaration` (ConfiguredSourceSelectorContract:54, 21) needs StaticSymbolicSourceSelectionTest:1462,3114 rewritten — both die anyway when wave 3 deletes the selector contract.
- `MaterializationSpec.leafField()` is dead weight (decode passes the same field for root and leaf; RuntimeRegionPlanner:4468,4520 key on it — no-op to drop); RuntimeRegionPlanner round-trips Map→JSON→MaterializationSpec at :4451,:4508,:4673,:5430 only to read fields back — planning-lane simplification.
- One exception message changed: SummaryBranchMapping "must be a JSON array" → "must be an array" (no test asserts it).
- `ExecutionTask.json()` returns the live backing JsonObject while `InputActionCatalog` deep-copies — inconsistent; decide in wave 3 (decode-once).
- KEEP (verified): InputActionCatalog deep copies (0 lines; silent-aliasing risk); MaterializationSpec typed object (used as identity key at 3 of 4 sites); TargetOutcome members (all have callers); `textSet`/`strings`/`requireFile` helpers (name-bearing messages, ordering differences).

## planning (from the wave-2 planning report)
- GATE COVERAGE GAP (record): the 20-row matrix exercises ONLY `DECLARED_COMMUNICATION_EFFECT` closures; zero rows produce `EXACT_CALL_ARGUMENT_AT_CUT`, `HANDOFF_BOUND_LEAF`, `EXACT_FIELD_WRITE_AFTER_ASSIGNMENT`, `DEFINITION_INVOCATION_NORMAL_EXIT`, `REGION_EXIT_FIELD_SNAPSHOT`. The merged `declaredCutOutputClosure`'s cut-argument half and the handoff/directHeap builders are covered by unit tests only until HDFS-11741 runs. First place to look if HDFS-11741's planner output looks wrong.
- HOLD: `RegionInstancePlan` View accessors now have zero callers, but item 2 replaced live views with deep copies in traversal loops (`ConcolicScheduler.trustedIncomingBinding` per symbolic input, `projectExactIncomingAtomicState` per action, `RWD.trustedEdges` twice per goal, `discoverDemandClosure`). Compare wave-2 matrix per-row `elapsed` against `matrix-20260825T152212Z` before deleting the Views; if PLAN/EXPLORE timings regress, restore the Views (PERF-1) instead.
- `handoffComponentOutputClosure` + `directHeapOutputClosure`: NOT merged (share the skeleton, not the lines; ≈40 lines for a 700-line 4-way method). Do not re-list.
- `normalizeNumbersInPlace` must survive while `CausynthTraceRecorder:978,981` and `RuntimeRefinedGraphBuilder:256` need in-place mutation of rows already handed out; `deepCopyValue` now delegates its scalar tail to `normalizeScalar` (they must agree; now do by construction). The −50 is not available.
- `staticOutputSiteId` recomputes what each builder wrote into `capture.outputSiteId` and `assignOutputOccurrenceIdentity` overwrites the capture with the recomputed value — two implementations that must agree; belongs with OutputClosureCodec (contract lane, wave 3).
- `RuntimeRefinedGraphBuilder.refine` (10-arg, run_engine.sh-bound) ignores its `protocol` and `occurrenceLinks` parameters — ABI note for when that entry point is next revised.
- `CausynthStaticFacts` still package-private → `RuntimeRegionPlanner.fieldOwner` dedup (−6) blocked; static lane to expose.
- `ConcolicSummaryImporter.importRow`, `RegionPathWorklist.outputRelations/manifest`, `RRP.stampRecordedExchanges/stampSynchronousServerTransactions`: long procedural, no repeated bodies (clone detection: longest cross-method repeat 15 lines). Not a wave-2 target.
- SKIP list correctly removed ~2,400 of ConcolicScheduler's 4,839 lines from the wave-2 surface (SymbolicInputSelection spans 2532–4929) — those go in wave 3.

## smt (from the wave-2 smt report)
- NEW GATE FLAGS to add to gate.sh (scripts left in scratchpad/wave2-smt/ — copy into experiments/shrink/ before the session ends): (a) `--recompose <matrix-root>`: recompose all 20 rows from their real `reach_query.jsonl` + `merged_summary.jsonl` + frozen plan and diff `candidate.smt2` sha256 (~60 s); (b) `--replay-flips <matrix-root>`: replay all 175 real path-flip queries through `ConcolicPathFlipSolver` and diff `path_flip_query.smt2` + solver record (~3 min). Together they catch composer/solver drift without a matrix run.
- MATRIX COVERAGE GAP (record): the 175 matrix queries contain only SymbolExpression/BinaryExpression/FieldAccessExpression/ConstExpr/TypeCastExpression over I/Z/J/one ref class — no OpStrExpression, no MethodExpression, no boxed primitives. The Emitter/Encoder divergences in the string family and `boxedPrimitiveReferenceEquality` are NOT exercised by the matrix; HDFS-11741 is the workload that exercises them.
- Encoder route-through (Solver → Emitter): NOT a dedup — semantic divergence in binary/stringOperation/typeCast/parseIntTerm/containerHost decides `unsupported`; the two `sortOfJava` disagree (boxed → INT vs REF; unknown → REF vs UNKNOWN). Attempt only in wave 3 behind the two replay gates + HDFS-11741.
- One Sort enum: NOT doable — `sort.name()` is written into `portOccurrences[].sort`, `configuredSourceMaterializations[].sort`, and model-assignment `valueType` (drives replay materialization); vocabularies conflict (MAP/ARRAY_VALUE vs ASSOCIATIVE/INDEXED); `ScalarEncoding` additionally carries integral width.
- `canonicalScalarBindingDeclared`/`configuredSourceBindingDeclared` in BooleanReach are the fail-closed "manifest's claimed term is declared in the formula" check (pinned by `missingOrUndeclaredConfiguredSourceCatalogFailsClosed`), NOT a re-derivation. KEEP. `portOccurrences` rows carry no `javaTypeDescriptor`, so PortCatalog cannot be replaced by the manifest without adding a field (rule-5 mistake).
- Planning lane: delete `"target-first"` from `ConcolicScheduler.knownOption` (~:5027); run_engine.sh no longer passes it.
- Manifest shape change to know: `canonicalModel` now = {schemaVersion, kind, authority, gaps, counts{6}}; `graph/causal_model.json`/`.dot` no longer produced; `GRAPH` gone from stage_metrics.tsv; `counts.gaps` (size) gone, `gaps` stays.
- `RecordedMapStateTest` builds UNSCOPED selector names and passes only because `eventToken` is the identity in that fixture — fix properly in wave 3 (it dies with selectors anyway).
- MEASUREMENT: wave 1 is uncommitted, so `git diff HEAD` mixes waves. Snapshot per-file nonblank counts into `experiments/shrink/counts-<wave>.tsv` at every gate (no commit needed).

## static (from the wave-2 static report)
- Wave-2 static items 2/3/4/5 were ALREADY DONE by wave 1 (backlog was written against HEAD; wave 1 is uncommitted). Lane is mined out: scan shows 0 unreferenced / 0 test-only / 0 dead types across 25 causynth files.
- Emitter "pairs" share an idiom, not an implementation (branch: void recordBranch vs assigned resolveBranch + re-dispatch; method-exit: two axes; Lite/Rich: four; accessor vs configured-source call contexts differ in whether observation stays paused across the call). Collapsing the IDIOM (`invoke`/`invokeTo`/`emit`, `bracket`) over 68 statements + 46 `addStaticInvoke` calls is where −192 came from; proven no-op (hook-invoke sequence 0 diff on both passes).
- EXPECTED in run-manifest after wave 2: instrumented-class digests move for ~5% of classes (2/6,143 concolic tree, 308 REGION_STATE tree) — Soot's identity-hash-ordered local maps permute aliased locals (`iconst_0; istore_2; iconst_0; istore 7`); instruction multisets identical; deterministic per jar. Not a semantic change.
- Finalizer gap channel deleted (−72): `RUNTIME_SOURCE_UNSTAMPED`, `COMMUNICATION_PORT_REGION_UNRETAINED`, `RUNTIME_RECORDED_EXCHANGE_NO_TYPED_PRODUCER_EDGE` rows are no longer produced (had no reader).
- `walkFailureClosure`/`failureDirectedClosure` `gaps` parameter now provably dead (never-touch list) — drop it + two pass-throughs (~5) in wave 3.
- `RuntimeRegionPlanner.fieldOwner` (:4976) ≡ `CausynthStaticFacts.fieldOwner`; `RuntimeRegionPlanner.constructor(String)` ≡ `SymbolicRegionPlanner.constructor(String)`; bare `"REGION_SKELETON"` literal at RuntimeRefinedGraphBuilder:931 and RuntimeRegionPlanner:214 vs `SymbolicRegionPlanner.SKELETON_KIND`.
- WARNING for helper unification: `ConfiguredProtocolStubs.string(JsonObject,String)` THROWS on array/object (→ "Invalid protocol stub mapping at <path>:<line>") where `JsonFields.text` returns "" — a naive swap turns a malformed-mapping rejection into silent acceptance. `RegionSkeletonInstrumentationSelection.nonEmptyString(JsonElement)` needs an element-shaped helper.
- `MethodCallsite`/`ConstructorCallsite` now identical to base `Callsite` (dead fields gone) — collapse (~−20) lands inside the deferred caller expanders; `CommunicationCallSiteAdapter.prepare`'s `bodies` param unused in all 4 impls (~−5).

## operational (wave-2 gate)
- `run-matrix.sh` used to ALWAYS rebuild the jar (the skip flag was an output it exported to rows, not an input). Running `gate.sh --replay` concurrently with a matrix launch lost 3 recompose rows + 6 flip queries to "Could not find or load main class" (jar mid-rewrite). Fixed: an incoming `CAUSYNTH_SKIP_GRAPHCHECKER_BUILD=1` now skips the build. Gate order from here: `mvn package` → `--replay` → launch matrix with the skip flag → `--matrix/--baseline`.

- **`SymbolicSourceEvidence` ordinal shim** — `identity()` falls back to
  `sourcePhaseId` when a row states no `ordinal` (`ordinal > 0 ? "#" + ordinal
  : sourcePhaseId`). It exists only so the recompose instrument can still read
  the pre-wave-3 artifacts (`matrix-20260825T173609Z` and older), whose rows
  carry no entry count. Delete the fallback once a fresh matrix baseline is
  recorded with the wave-3 runtime; after that every mint states its ordinal
  and the phase is the mint *site*, never the identity.

- **Producer occurrence with two exact replay continuations** — wave 3 deleted
  `RuntimeWorkflowDiscovery.phaseProjections` whole, so a selected coarse
  occurrence is always one execution task (README "occurrence plan": one
  occurrence, one answer). The split it removed also handled the case where
  two selected output members state *different* `replayEntry` continuations;
  `DeclaredCutExportProjectionTest.incompatibleExactContinuationsBecomeBounded`
  `PhaseTasks` pinned it and was deleted with it. That case now fails loudly in
  `ConcolicScheduler.promoteSelectedReplayEntry` ("selected outputs require
  incompatible replay continuations") rather than silently splitting. The RPC
  matrix never reaches it (no `-phase-` campaign id in any of the twenty rows
  of `matrix-20260825T173609Z`). **Ruling (Zhenyu, wave 3): if HDFS-11741 hits
  it, the answer is region rooting — one region per RPC exchange / loop-body
  root, G1/G2 — not a task split. Do not restore `phaseProjections`.**

## Lane I findings (wave 3, 2026-08-25) — premises corrected, do not re-act on them
- `OutputCaptureSpec` occurrence equality and `validateProjectedFieldWrite` are NOT
  duplicated by `OutputClosureCodec` (`mergeReplayScalar` strips
  `outputSiteId/outputOccurrence/replayOccurrence` from merged outputs; the codec
  never reads `definitionFieldSignature/leafFieldSignature/fieldPath`). Keep both.
- `replay-flips.sh` cannot see a `LoopBoundPolicy` wire regression: the flip task is
  `source.deepCopy()`; only `execution_task_plan.jsonl` (planner output) shows it —
  use scratchpad/wave3-plan/replay.sh or a matrix run.
- `TargetOutcome` accessors all have live non-JSON callers; nothing to collapse.

## Derived fields (runtime writers, cross-lane readers) — for lane E, one pass
Wave 3 item 6, lane A side. Every key below is written by
`runtime/ConcolicRegionRuntime.java` and **restates something the reader already
holds**. Lane A did not touch them because each has a reader outside lane A's
files. The fix in every case is the same: the reader recomputes the value from
the row it already resolves, then lane A stops writing the key.

### `configuredSourcePhaseObservations[]` — the row already names its catalog row
Every observation carries `matchedPhaseId`, and the importer already builds
`phasesById` from the task's own `configuredSourcePhases` catalog
(`ConcolicSummaryImporter.java:466-470`). Six members are copies of that row:

| key | reader | should compute instead |
|---|---|---|
| `phaseKind` | `concolic/ConcolicSummaryImporter.java:539`, `concolic/TopologyDelta.java:549` | `phasesById.get(matchedPhaseId).phase().name()` — constant `PUBLISH` since wave 3 removed CONSUME phases |
| `siteId` | `concolic/ConcolicSummaryImporter.java:540` | `phasesById.get(matchedPhaseId).siteId()` |
| `replayOrdinal` | `concolic/ConcolicSummaryImporter.java:541-542`, `concolic/TopologyDelta.java:552` | already recomputed at `ConcolicSummaryImporter.java:472-478` as `replayOrdinals.get(phaseId)`; the comparison is the only use |
| `sourceId` | `concolic/ConcolicSummaryImporter.java:544-545` | `phasesById.get(matchedPhaseId).sourceId()` |
| `fieldSignature` | `concolic/ConcolicSummaryImporter.java:546-547` | `phasesById.get(matchedPhaseId).fieldSignature()` |
| `declaredCallee` | `concolic/ConcolicSummaryImporter.java:548-549` | `phasesById.get(matchedPhaseId).runtimeDeclaredCallee()` |

`exactMatch` and `orderMatched` are now written as constant `true`
(`ConcolicSummaryImporter.java:502-503` requires them present, `:539`/`:551`
requires them true). Once the six above go, the whole row collapses to
`{schemaVersion, kind, authority, observationIndex, matchedPhaseId,
ownerCallId, invocationId}` — the only members that are runtime facts. Note the
importer compares the row's key set for exact equality
(`ConcolicSummaryImporter.java:493`), so `CONFIGURED_SOURCE_PHASE_OBSERVATION_FIELDS`
must change in the same commit. (`selectedPhase` was removed by lane A in this
wave on the coordinator's instruction; lane D is dropping it from that set.)

### `outputCaptures[]`
| key | reader | should compute instead |
|---|---|---|
| `outputSiteId` | `concolic/ConcolicSummaryImporter.java:1730`, `:1766`; `concolic/CanonicalSessionModel.java:387` | `outputCapture(captureBindingId).outputSiteId()` — the row already carries `captureBindingId`, which is the plan row's primary key |

`replayOccurrence` was the same kind of copy with **no** reader on the result row
(only on the plan row, `contract/OutputCaptureSpec.java:94`); lane A deleted it
in this wave.

## Lane E: reader switches (owner does it)
Wave-3 item 1 (decode once) + item 6 (derived fields off the wire), lane E side.
`contract/PlanRow` now decodes `configuredSourcePhases` once per row and both
`ExecutionTask` and `RegionInstancePlan` expose it as
`configuredSourcePhases()` (typed, cached, unmodifiable).  Lane E already
switched the two readers it owns (`ConcolicSummaryImporter`, `TopologyDelta`).
The rest are one-line switches in files lane E does not own:

- `causynth/ConcolicInstrumentationSelections.java:161-164` → replace
  `ConfiguredSourcePhaseContract.occurrencesOf(task.json().get(PLAN_FIELD))`
  with `task.configuredSourcePhases()`.
- `runtime/ConcolicRegionRuntime.java:10123-10126` → replace
  `ConfiguredSourcePhaseContract.occurrencesOf(task.json().get(PLAN_FIELD))`
  with `task.configuredSourcePhases()`; then delete the duplicate unique-phaseId
  refusal at `:10127-10135` (`ConfiguredSourcePhaseContract`'s
  `validateOccurrenceSequence` is the sole owner of that check — README
  "Minimal cross-stage contract") and build `configuredSourcePhasesById`
  with a plain `put`.
- NOT switchable (verified, do not re-list):
  `concolic/ConcolicConstraintSolver.java:2774-2778` decodes the phase catalog
  off a merged-summary `activation` object, not off a plan row; it has no
  `ExecutionTask` in scope and its `try/catch → return null` is a real
  fail-open path.
- `loopBound` is NOT re-decoded six times over one row: `ExecutionTask` decodes
  it once (cached), and `contract/PathObservation.java:340-343`,
  `concolic/TargetReachPathQueryBuilder.java:428`,
  `concolic/ConcolicScheduler.java:1790`, `concolic/BoundedLoopComposition.java:83`
  each decode a *different* artifact (canonical summary, query owner, merged
  summary, retained-loop authority).  Nothing to collapse; premise closed.

### Derived keys: the decode point now computes them, so the writer may stop
Every key below decodes identically whether the wire carries it or not — lane E
verified with `scratchpad/wave3-plan/replay.sh` (both artifacts byte-identical).
The writer lane can now delete its write without any reader noticing.

| key | writer (stop writing) | decode point that computes it |
|---|---|---|
| `configuredSourcePhases[].siteId` | `runtime/RuntimeRegionPlanner` via `ConfiguredSourcePhaseContract.occurrence` | `validateHookSite` derives `declarationMethod#u<idx>` |
| `configuredSourcePhases[].phaseKind` | same | `validateOccurrence` derives it from `phase` |
| `configuredSourcePhases[].ownerCallId` | same | `validateOccurrence` derives it from `enclosingCallIds[0]` |
| `configuredSourcePhases[]` / `configuredSourcePhaseDeclarations[]` `schemaVersion`/`kind`/`authority` | same | `constants()` accepts absence as the member's own constant |
| `outputClosure.schemaVersion`/`.kind` | `contract/OutputClosureContract.toJson` | `decodeEnvelope` compares only when restated |
| `outputClosure.producer.{regionId,relationKey}` | same | `OutputClosureCodec.producerScoped` fills them from the artifact's own `regionId`/`relationKey` |
| `outputClosure.members[].slice.{outputPort,outputCell}` | `runtime/RuntimeRegionPlanner` slice builders | `decodeMember` fills them from `output.portId`/`output.cell` |
| `outputClosure.members[].output.replayOccurrence`, `…captureBindings[].replayOccurrence` | `runtime/RuntimeRegionPlanner`, `OutputClosureCodec.singleton` | `replayOccurrence(...)` and `OutputCaptureSpec` default it to `outputOccurrence` |
| `configuredSourcePhaseObservations[].{phaseKind,siteId,replayOrdinal,sourceId,fieldSignature,declaredCallee,exactMatch,orderMatched}` | `runtime/ConcolicRegionRuntime` (lane A) | `ConcolicSummaryImporter.IGNORED_OBSERVATION_FIELDS`; the required set is now the seven runtime facts only |

Two derived keys lane E could NOT close, with the reason:

- `outputCaptures[].outputSiteId` at `concolic/ConcolicSummaryImporter.java:1696`
  (`siteLocalBoundedVersions`): the method has only `(port, admitted, issues)` in
  scope, no `OutputCaptureSpec`, and it uses the value as the *shared* site key
  across captures.  Switch needs the caller at `:1621` to pass the port's
  `OutputCaptureSpec` (it already resolves one) — planning-lane change.  The
  other reader, `:1732` (`exactOutputCaptureOccurrence`), lane E already made
  derived from `request.outputSiteId()`.
- `concolic/CanonicalSessionModel.java:387` reads `string(raw, "outputSiteId")`
  off a result row — lane C, live.  Compute it as
  `outputCapture(string(raw, "captureBindingId")).outputSiteId()`; the row
  already carries `captureBindingId`, the plan row's primary key.

### `leafFieldSignature` ≡ `accessFieldSignature` (from the coordinator)
`contract/MaterializationSpec.actionFields()` writes both members with the same
value (`rootField`); root and leaf are one field since `leafField()` was
deleted.  Lane E has no decode point for it — `MaterializationSpec.decode`
never reads either name — so this one is entirely reader-side:

- `runtime/RuntimeRegionPlanner.java:2937` → `String leaf = firstNonBlank(
  text(input.get("leafFieldSignature")), text(input.get("accessFieldSignature")));`
- `concolic/ConcolicScheduler.java:1577`, `:2810` → same `firstNonBlank(access, leaf)`
  form already used at `:1261-1262`; then `:1341` and
  `runtime/RuntimeRegionPlanner.java:4743` stop writing `leafFieldSignature`,
  and it comes out of `ConcolicScheduler.java:2410`'s member vocabulary.
- `runtime/ConcolicRegionRuntime.java:9191` (`leafFieldSignaturesByPath`) is
  lane A's: read `accessFieldSignature` when `leafFieldSignature` is absent.

### Coverage note for whoever runs the gate
The 20-row RPC matrix carries **zero** `configuredSourcePhaseObservations` rows
(checked: `grep -c` over all three workers' `merged_summary.jsonl` in
`matrix-20260825T173609Z/scenario-01` = 0), so the observation-ledger check
above is exercised only by the unit suite and by HDFS-11741 — not by 20/20.
The plan artifacts *do* carry `configuredSourcePhases` (2 rows), so the
`ConfiguredSourcePhaseContract` codec itself is covered.

## Lane H1 findings (wave 3) — gate blind spots and deferred cuts
- The 20-row matrix has ZERO `call_argument/dispatch_*/caller_argument/
  constructor_caller_argument/literal` dataflow rows; HDFS-11741 has ~135k.
  Any change to `propagateCallArguments`, `expandCallerArguments`,
  `expandMethodCallers`, `expandConstructorCallers` needs the HDFS-11741
  SEED differential (scratchpad/wave3-h1/compare-hdfs.sh, ~4 min/leg).
- `CfgLoopControl.BY_BODY` is an unbounded static cache (two UnitGraphs +
  dominators per body, JVM lifetime); survived the 66k-method seed at 64g.
- `instrumentConcolicBranches` swallows `CONCOLIC_BRANCH_BEFORE_CONSTRUCTOR_
  INITIALIZATION` into a debug log (pre-existing; decide).
- `RuntimeRegionPlanner.text` ≡ `MapFields.stringValue` (not `text`);
  `RRP.strings` and `RRGB.integer` are NOT MapFields twins (null-literal /
  parseInt fallback differences).
- Public `CausynthPipeline.Hook` + runtime deriving reflective names from it
  (3 lines) — correctness, not a cut; do in the IR wave.

## Encoder→Emitter divergences (HDFS-11741 must confirm)
Inventory taken by lane IR-4b (wave 4) before the merge, so the first HDFS-11741
flip that misbehaves can be traced to one line here.  A: `ConcolicSmtComposer.Emitter`
(the surviving encoder).  B: `ConcolicConstraintSolver.Encoder` (to be deleted).
Every row states the resolution the owner ordered — A wins — and what that costs.

- **Unsupported result value.** B returns `null` from `term(...)` and aborts the
  constraint (`ConcolicConstraintSolver.java:355-358`); A returns a concrete
  `unsupportedTerm(sort)` — `false`/`0`/a float literal — and records the gap
  (`ConcolicSmtComposer.java:3157-3161`, `:6721-6726`). Resolution: A. Safe because
  `solve()` still refuses on a non-empty `unsupported` set before running z3
  (`ConcolicConstraintSolver.java:123-129`), but a future caller that ignores
  `unsupported` would now silently solve a query containing a substituted `false`.
- **Unsupported provenance.** B threads an `origin` string (`q_branch_<i>`,
  `q_context_<i>`, `:not`, `:cast`, …) into every code it records; A records the
  bare expression type. Resolution: A. Cost: solver `UNSUPPORTED_EXPRESSION_IR`
  records stop naming which constraint of the query was unsupported.
- **`NotExpression`.** Handled ONLY by B (`ConcolicConstraintSolver.java:337-345`);
  A's `term()` dispatch has no arm for it (`ConcolicSmtComposer.java:3106-3158`), so
  under A every negated path predicate becomes `unsupported`. This is a capability
  gap, not a divergence: **A must gain the arm as part of the merge**, or every
  flip query with a negated predicate degrades to UNSUPPORTED.
- **`PlaceholderExpression`.** Both accept only `currentTimeMills` with
  `_count >= 1` (A `:3120-3138`, B `:723-742`). Names differ:
  B `environment__<safeName(identity)>__<sha10>`, A
  `environment__<scopeToken(scope)>__<smtName(identity)>__<sha10>`. B additionally
  files a pseudo-symbol `ENVIRONMENT_PLACEHOLDER:<identity>` into the
  constraint's symbol set (`:734-739`) so the replay-control frontier sees the
  environment dependency; A has no constraint-symbol tracking at all, so **that
  tracking must be ported onto A** or `classifyReplaySupport` stops seeing
  placeholder dependencies.
- **Symbol naming.** B: `sym__<safeName(raw)>__<sha256(raw)[0:10]>` plus
  `sym__string_is_null__…` / `sym__reference_is_null__…` / `sym__fpbits__…` /
  `sym__fpisnan__…` (`ConcolicConstraintSolver.java:3300-3323`). A:
  `<prefix>__<scopeToken(currentSymbolScope)>__<smtName(raw)>`
  (`ConcolicSmtComposer.java:6713-6716`). Resolution: A. **Consequence: every
  recorded `path_flip_query.smt2` changes, so `replay-flips.sh` against
  `matrix-20260825T173609Z` goes to 0/175 by construction** — the fresh matrix has
  to become the replay baseline, exactly as README "Wave 4" already states.
- **Query rendering.** B's `finish()` (`:1690-1781`) emits
  `(set-option :produce-models true)`, `(set-option :smt.arith.solver 2)`, REF
  nullness `define-fun`s, float NaN discriminators, `:named pc_<index>` assertion
  names, `(check-sat)` and a sorted `(get-value (…))` list built from
  `controlledSymbols` + `additionalModelNames`. A's `render()` emits the
  composition preamble and descriptive `:named` assertions and no `get-value`.
  Resolution: the solver keeps its own rendering; only the expression algebra is
  shared. A `finish()` written in A's style would break the model read-back in
  `parseGetValues`/`modelAssignments`.
- **Solver-only bookkeeping with no counterpart in A** (must be ported, not
  resolved): `addConstraint` returning the constraint's symbol set
  (`:285-307`, via `currentConstraintSymbols`), `controlledSymbols`,
  `additionalModelNames`, `names` (raw→`SymbolNames`, read back by
  `modelAssignments`), `functionDeclarations`, `containerStates`, `fieldSymbols`,
  `bindRecordedReadCut` (`:673`), `materializableFieldRepresentative` (`:1098`),
  `bindSparseContainerBoundaries` (`:1127`), `bindReferenceDomains` (`:1167`),
  and the `SparseContainerBoundaries` dynamic-associative interception in
  `containerTerm` (`:361-385`).
- **`Sort` is not one enum.** A (`ConcolicSmtComposer.java:6927-6944`):
  `BOOL INT FLOAT32 FLOAT64 STRING REF MAP VALUE ARRAY_VALUE`, no `UNKNOWN` —
  `VALUE` doubles as unknown. B (`ConcolicConstraintSolver.java:1786-1807`):
  `… VALUE INDEXED ASSOCIATIVE UNKNOWN` plus `containerState()`. Resolution: A.
  Cost: B's `UNKNOWN`-vs-`VALUE` distinction disappears, and with it
  `fromContainerTerm`'s `CONTAINER_STATE_USED_AS_VALUE` refusal
  (`ConcolicConstraintSolver.java:608-611`).
- **`Term` is not one type.** A carries `precondition` + `withPrecondition`
  (`ConcolicSmtComposer.java:6955`, `:6995`); B has none. Every A rule that
  returns a *definedness precondition* — short-circuit `&&`/`||`
  (`:4301-4307`), container `require` folded into the term (`:3626-3634`,
  `:3501-3516`), string dereference (`:3080-3096`), cast dependency
  (`:4176-4180`) — becomes a global assertion in B's world. Resolution: A;
  the solver gains guard-scoped preconditions it never had.
- **`sortOfJava`.** A unboxes every wrapper (`java.lang.Boolean`→`BOOL`,
  `Integer`/`Long`→`INT`, `ConcolicSmtComposer.java:7160-7167`), maps bare
  `"String"`→`STRING` (`:7168`), and routes arrays/collections to
  `ARRAY_VALUE`/`MAP` via `containerSort` (`:7145`). B maps all of those to
  `REF` and unknown/empty to `UNKNOWN` (`ConcolicConstraintSolver.java:3256-3258`).
  Resolution: A. **This is the largest behavioural change to the solver**: boxed
  primitives and container-typed symbols change sort, so their SMT sort, their
  range assertions and their model read-back all move.
- **`castSort`.** A is a separate descriptor table where `Z`→`INT` and
  unknown→`VALUE` (`ConcolicSmtComposer.java:7261-7274`); B aliases `sortOfJava`,
  so `Z`→`BOOL`, unknown→`UNKNOWN` (`ConcolicConstraintSolver.java:3276-3278`).
  Resolution: A. A also unwraps a cast-of-a-cast when deriving the source type
  (`:7284-7286`); B does not.
- **`binary`.** Same operator set. A-only rules, all resolved in A's favour:
  boxed-primitive reference identity forces both operands to `REF`
  (`:4229-4233`); mixed-sort `==`/`!=` against null is decided `true`/`false`
  rather than refused ("Java primitives are never null", `:4285-4292`, vs B's
  `SORT_MISMATCH` at `ConcolicConstraintSolver.java:955-958`); one early
  `BinarySortConflict` gate (`:4308-4316`) replaces B's three local mismatch
  checks (`:955`, `:984`, `:1032`); `&&`/`||` carry a definedness precondition
  (`:4301-4307`). B-only rules that are LOST: `recordFieldAlias`
  (`ConcolicConstraintSolver.java:842`, the sole feed for
  `materializableFieldRepresentative`), the `NON_INTEGRAL_BITWISE` check
  (`:998-1000`), and the `STRING_MATERIALIZATION_NULLNESS` refusal (`:934-939`).
  Every `unsupported` code also changes spelling (A `CamelCase:operand:sort`,
  B `origin:UPPER_SNAKE`), so any script matching solver unsupported codes must
  be re-taught.
- **String operations.** A supports `toString` (int→String,
  `ConcolicSmtComposer.java:4599-4612`); B does not (falls to
  `OP_STRING_OPERATOR`). Null-receiver discipline is opposite in kind: A folds
  it into the term's precondition (`:4502-4503`, `:3080-3096`), B asserts
  `(not <nullness>)` globally and REFUSES when nullability is unknown
  (`ConcolicConstraintSolver.java:1487-1494`). Resolution: A — the solver loses
  `STRING_*_NULLABILITY_UNKNOWN` and instead lowers a guarded precondition.
  A's `length` range assertion is guard-scoped and de-duplicated (`:4519-4520`),
  B's is a raw un-deduplicated assertion (`:1332-1337`).
- **`parseIntTerm`.** Same arity/radix-10 rule; the round-trip recogniser is NOT
  equivalent. A's `exactSplitSegment` (`ConcolicSmtComposer.java:4717-4765`)
  resolves select-over-store first (`:4720-4722`), accepts any literal index
  `>= 0` (`:4736-4739`), and walks the concat piecewise so a multi-piece element
  is representable (`:4767-4819`). B's `exactSplitPrefix`
  (`ConcolicConstraintSolver.java:1589-1659`) accepts only index 0 (`:1602-1605`),
  requires a 3-part concat (`:1629-1631`) and every suffix to be provably
  string-valued (`:1650-1656`). A additionally refuses when the element is not
  exactly one integer rendering (`ROUNDTRIP_ELEMENT_NOT_ONE_INT_RENDERING`,
  `:4662-4668`). Resolution: A — strictly more accepting on index/limit, strictly
  stricter on the rendering.
- **`containerHost`.** A resolves container state through the recorded map
  carrier PORT (`ConcolicSmtComposer.java:3526-3546`) and scopes the field
  accessor by symbol scope (`:3648-3653`); B mints a global hashed
  `container__<safe>__<sha10>` constant (`ConcolicConstraintSolver.java:402-419`)
  and a global `container_field__<sha16>` accessor (`:533-539`). A's `box`
  delegates to `asValue` (`:3612-3614`); B open-codes it and refuses on unknown
  string nullness (`:473-477`). A's `field` refuses `VALUE`; B allows it
  (`:524-531`). Resolution: A — but A's container identity depends on
  `currentInvocation` and the carrier-port map, which a solver-side A has to
  stub, so container-heavy HDFS-11741 queries are the first place to look.
- **Capabilities B has and A has NONE of** — these are ports, not resolutions,
  and each is load-bearing for the solver:
  `addConstraint` returning the constraint's symbol set
  (`ConcolicConstraintSolver.java:285-309`, fed at `:620-622` and `:734-739`) —
  everything below is downstream of it;
  `bindReferenceDomains` (`:1167-1255`, observed-object identities, `distinct`,
  per-candidate `select_ref__` selectors) feeding `REFERENCE_ALIAS` model
  assignments (`:1892-1899`);
  `bindSparseContainerBoundaries` (`:1127-1165`) and the whole
  `SparseContainerBoundaries` machinery (`:2320-2585`);
  `bindRecordedReadCut` (`:673-711`) — in particular `additionalModelNames`
  (`:688-697`), without which a selected writer choice cannot be read back;
  `materializableFieldRepresentative` (`:1098-1125`) over `fieldSymbols`;
  `controlledSymbols` (`:273`, seeded at `:643`, mutated from outside at
  `:2854`/`:2873`);
  `SymbolNames` minting five coordinated names per raw symbol (`:3300-3323`)
  where A's `RawSymbol` (`ConcolicSmtComposer.java:6916-6925`) has three and is
  keyed by SCOPE, so there is no stable raw→name map to hand back;
  the `P_L` VM-allocated-placeholder non-null rule (`:645-648`, `:3237-3239`);
  `NotExpression` (`:337-345`);
  dynamic associative container reads (`:363-386`);
  and `finish()`'s `(check-sat)` + sorted `(get-value …)` projection
  (`:1755-1780`) — A emits no `get-value` at all.
- **Composition state the expression path reaches** (what a solver-side A must
  stub): `ports`/`findPort` (empty `PortIndex` makes `symbol` fall through to
  `scopedSymbol`, `ConcolicSmtComposer.java:3796-3814`); `currentInvocation`
  (NPEs at `:2622` and `:3550` without a synthetic `InvocationKey`); `recorded`
  (`RecordedSessionModel`, NPEs at `:3203`/`:3230` — stub it or drop the
  `GUARDED_READ_TYPE`/`RECORDED_ITE_TYPE` arms at `:3143-3148`);
  `recordedMapCarrierPorts` (empty is safe); `failureWitness` (empty is safe).
  `currentGuard`/`currentSymbolScope` default safely (`:2594-2595`).

## IR-3 → importer (wave 3/4, from the runtime lane)

### `outputVersionGaps[]` replaces the `unresolvedInputs` prose parser
`ConcolicRegionRuntime` no longer writes the two human notices that carried
`": bounded output version capacity "`.  It publishes the gap structurally, in
a new top-level result member `outputVersionGaps`, already in the exact
`OUTPUT_VERSION_ALIGNMENT_GAP` shape `alignmentGaps` admits.  Row:

```json
{ "schemaVersion": 1,
  "kind": "OUTPUT_VERSION_ALIGNMENT_GAP",
  "authority": "BOUNDED_OUTPUT_VERSION_CAPACITY_V1",
  "captureBindingId": "<plan row primary key>",
  "outputSiteId": "<request.outputSiteId()>",
  "versionCapacity": 8,          // int, loopBound.maxBackedgeTraversals()
  "versionsObserved": 11,        // int, highest occurrence this site reached
  "versionsCaptured": 8,         // int, versions that produced a relation
  "reason": "<binding> ran past its bounded output version capacity <cap> at
             <site>; <held> of <observed> observed version(s) were captured,
             so this relation is a bounded prefix of the run and not a closed
             one" }
```

One row per `captureBindingId`; the member is omitted when empty.
`versionsObserved`/`versionsCaptured` are ints, not the old strings, and
`versionsCaptured` is now a real count instead of `"NOT_CARRIED_BY_RESULT"`.

Importer owner deletes, in `ConcolicSummaryImporter`:
`BOUNDED_OUTPUT_VERSION_NOTICE`, `BOUNDED_OUTPUT_VERSION_TAIL`,
`BOUNDED_OUTPUT_VERSION_GAP_KIND`, `boundedOutputVersionNotice(JsonElement)`,
`boundedOutputVersionGaps(ResultRow)` (~:906-965, ≈55 lines) and the
`if (boundedOutputVersionNotice(unresolved)) continue;` filter at ~:444 (the
notice is no longer in `unresolvedInputs`, so nothing needs skipping).
`alignmentGaps(task, row)` then starts from the result's own rows: decode
`outputVersionGaps` on `ResultRow` and copy them in.  Nothing else changes —
`CoverageDivergence.classify` and `OutputClosureCodec.normalizeAlignmentGaps`
read only `kind`, `reason` and `fields`, all unchanged.

### Cross-lane items the runtime lane could not land

- `contract/LoopBoundPolicy.acceptsInstrumentedBound(String encodedLoopId,
  int)`: the first argument is never read.  Contract owner drops the
  parameter; the two call sites are `ConcolicSummaryImporter` (~:1523, IR-4)
  and `ConcolicRegionRuntime` (the `checkLoopBackedge` guard, IR-3, now
  inlined — the private `loopBoundMatchesPlan` wrapper is gone).  Left passing
  the id so the tree stays buildable; flip all three in one commit.
- `runtime/RuntimeRefinedGraphBuilder.refine(...)` ignores its `protocol` and
  `occurrenceLinks` parameters (verified: zero references in the body).
  IR-2a drops both from the 10-arg signature; the only caller is
  `CausynthTraceRecorder` (`RuntimeRefinedGraphBuilder.refine(...)`, the
  `trace.protocol` / `activationGraph.occurrenceLinks` arguments).  Both
  values stay live for `RuntimeRegionPlanner.planSkeletonGraph` and
  `RuntimeSelectedRegionFinalizer.finalizeRegions`, so only the two arguments
  go.  Left passing them for the same reason as above.
- `contract/ExecutionTask` accessors the runtime still decodes off
  `task.json()` (IR-2b): `targetBranch()` (object member `targetBranch`, read
  for `siteId`/`occurrence`) and the selected read-cut plan
  (`SelectedReadCut.planOf(task.json())`, read for its `gates` array).  Add
  both and `RuntimeTask` stops touching `json()` entirely.
- `contract/ExecutionTask.modelAssignments()` returns `JsonFields.array(...)`,
  which silently yields empty for a stated non-array.  The runtime's two
  shape refusals ("modelAssignments must be an array in <task>", "model
  assignment must be an object in <task>") were deleted with the switch to the
  typed accessor; the decode point should refuse the stated-but-malformed
  member instead.

## IR-2b: ConfiguredSourcePhaseContract callers — APPLIED (2026-08-25)
`contract/ConfiguredSourcePhaseContract` is Gson end to end: `declaration(...)`
and `occurrence(...)` return `JsonObject`, `declarationsOf`/`occurrencesOf` take
a `JsonElement`, and the Map codec (`jsonRow(Map)`, the private `Gson`, the
string-key check) is gone.  On the coordinator's instruction (IR-2a/IR-6 closed)
IR-2b applied every switch itself; nothing is left for another lane:

- `runtime/RuntimeRegionPlanner` `configuredSourcePhases` and its caller now
  build/carry `List<JsonObject>`; `causynth/StaticSymbolicSourceDiscovery` keeps
  `List<JsonObject> phases` and reads `JsonFields.string(phase, "siteId")`;
  `causynth/StaticProgram.sourcePhasesBySite()` converts its Map-shaped catalog
  once with `JsonFields.WRITER.toJsonTree(...)` (exactly what `jsonRow(Map)` did)
  until `RegionRow` itself is JsonObject-shaped (IR-4);
  `concolic/RegionPathWorklist` dropped the `manifestState` argument.
- Ten test files switched to the Gson shape (`ConcolicEvidenceHookBracketTest`,
  `ConcolicConstraintSolverTest`, `ConcolicSummaryImporterTest`,
  `NestedTargetFrontierProgressionTest`, `RegionPathWorklistTest`,
  `TopologyDeltaConfiguredSourcePhaseTest`, `ConcolicInstrumentationSelectionsTest`,
  `ConfiguredSourcePhaseContractTest`, plus the two runtime source tests their own
  lane had already converted).
- `concolic/RuntimeWorkflowDiscovery`: `sharedLocationConsumers` reads
  `plan.admissionBasis()/demandedByRegionIds()` (typed on `RegionInstancePlan`);
  the `Iterable<JsonObject>` `rankedWorkflow` bridge is DELETED, and the four
  fixture tests that used it decode their rows with `RegionInstancePlan.decode`
  through a local `plans(JsonObject...)` helper; `scheduleIndex` now takes
  `List<ExecutionTask>`, so the whole plan is no longer decoded a second time
  right after the scheduler built it (`ConcolicScheduler.Result.executionTasks`
  is `List<ExecutionTask>`, serialized once in `writeResult`).

### Corrected premises (do NOT act on the earlier wording)
- **`demandedSharedLocations` is NOT write-only.**  The earlier note came from a
  literal-string grep; the readers use the constant.  It is read by
  `runtime/RuntimeRegionPlanner.java:1134` (`demandedSharedCarriers`, called at
  `:996`, which turns the demand into the occurrence's shared carriers) and by
  `causynth/RuntimeSelectedRegionFinalizer.java:1017`.  The writers at
  `RuntimeRegionPlanner.java:546,878` stay.
- **`leafFieldSignature` ≡ `accessFieldSignature` does not hold for
  `RuntimeRegionPlanner.addFieldAccessIdentity` (`:4697`)**: it writes
  `accessFieldSignature = declarations[0]` and `leafFieldSignature =
  declarations[last]`, which differ on a multi-hop path.  The equivalence lane E
  found is `MaterializationSpec.actionFields()` only.  The readers are already
  tolerant — `RuntimeRegionPlanner.java:2911-2915` unions both names into
  `demandedHeapDeclarations`, and `ConcolicScheduler.java:1182,1500` already use
  `firstNonBlank(access, leaf)` — so nothing was pending on the reader side.  The
  writer half is HELD: `runtime/ConcolicRegionRuntime.java:9049,9319`
  (`leafFieldSignaturesByPath`) still resolves field paths through the key, and
  `leafFieldSignature` is already out of `ConcolicScheduler`'s
  `SEMANTIC_PORT_FIELDS`, which may not move again (task-id derivation).

### Still open for other lanes
- `concolic/SparseReadCutGate.java:318` calls `enforceable()`, which its own
  lane's in-flight edit deleted — the repo main tree does not compile because of
  it (IR-2b pinned the pre-edit copy in its isolated tree to run the proof).
- `RegionPathWorklistTest` (7) and `NestedTargetFrontierProgressionTest` (2) fail
  with `freeSymbols is not stated`: `SymbolicSourceEvidence.freeSymbolsOf` was
  made fail-closed by the C3 lane and these two fixtures never state the array.
  Pre-existing at IR-2b's first read (identical refusal in the snapshot); the
  fixtures need `freeSymbols: []` on their summary rows.

## OCC-1 result rows

Contract between the runtime (writer) and the importer/worklist/composer
(readers) for publishing every compatible activation of one task's address as
its own occurrence.  Written by the importer/composer owner; the runtime
executor holds the writer half.  Run 24 is the motivating case: the importer
diagnostics named `REGION_OCCURRENCE_ADDRESS_AMBIGUOUS` for four of six tasks
("48 further compatible activation(s) matched this address after it was
answered"), i.e. the campaign observed the occurrences and threw them away.

### Members the runtime stamps on each `CONCOLIC_REGION_RESULT` row

| member | type | required | meaning |
|---|---|---|---|
| `activationOrdinal` | int ≥ 1 | on every OCC-1 row | activation-entry order within this task's address. Dense and gapless: ordinals `1..N` for the N activations the task published. Its presence is what marks the row as OCC-1. |
| `plannedOccurrenceId` | string | when `activationOrdinal` is present | the address the task planned, i.e. `ExecutionTask.occurrenceId()` verbatim. |
| `occurrenceId` | string | when `activationOrdinal` is present | this activation's own identity, `<plannedOccurrenceId>#a<activationOrdinal>`. Stamped on **every** OCC-1 row including ordinal 1 — no special case for "only one activation", because whether a second one exists is not known when the first is written. |
| `relationallyComplete` | bool | when `activationOrdinal` is present | whether **this activation** satisfied the demanded output boundary (`completeExactOutputBoundary` over this activation's captures). Not a task-level verdict. |
| `targetReached` | bool | `TARGET_REACH_CLOSURE` rows only | whether this activation exited through the selected target throw. The existing `targetReach` object stays as it is; this is the boolean the importer selects on. |

### Rules the readers depend on

1. **Legacy rows are untouched.** A row that states no `activationOrdinal` is
   read exactly as today: `occurrenceId` from the row/task, task-level
   `relationallyComplete`, no activation cases. This is what keeps run 24 and
   the recorded matrix rows recomposing byte-identically; do **not** back-fill
   `activationOrdinal: 1` onto a build that is meant to reproduce them.
2. **Per-activation evidence, not per-task.** `sessionEventLedger`,
   `sharedFieldVersions`, `vmHandoffEvents`, `engineSummary`, `outputCaptures`,
   `branchMappings`, `symbolizedInputs`, `freeSymbols`, `rootOutputExpression`,
   `exitKind`/`exceptionType` are all scoped to the activation that produced
   the row. The session event ledger stays session-global in its *ids* (run 24
   already showed one ledger across tasks, snapshotted per region exit) — only
   the snapshot boundary is per activation.
3. **`vmHandoffEvents[].producerOccurrenceId` must name the producer's
   activation occurrence**, i.e. carry the `#a<ord>` suffix, not the planned
   address. The composer binds handoffs per occurrence by `producerTaskId` +
   producer occurrence id; a planned-address value would bind occurrence 1's
   value into occurrence 7's formula. `producerTaskId` keeps naming the task
   that publishes the row (run 24 verified this is already correct).
4. **No `CONCOLIC_REGION_SKIPPED / OCCURRENCE_ADDRESS_AMBIGUOUS` for an address
   that published ≥ 1 activation row.** That skip is precisely the condition
   OCC-1 removes. Other skip kinds stay.
5. Rows of one task may appear in any order in the results file; the importer
   sorts by `activationOrdinal`. Two rows of one task with the same ordinal is
   a fail-closed import refusal (`DUPLICATE_ACTIVATION_ORDINAL`).
6. An activation that reached no terminal publishes **no row** (as today). An
   activation that reached a terminal but missed part of the boundary
   publishes a row with `relationallyComplete: false` and whatever it did
   capture — it must not be suppressed.

### What the readers do with them (so the writer can check itself)

- Importer: one path-observation row per activation row, `occurrenceId`
  verbatim; an incomplete activation becomes a case carrying only its captured
  members plus a named `activationIncomplete` gap; the **task** is relationally
  complete iff at least one activation is. For the target task the case with
  `targetReached: true` is selected, and a target task with no such case is
  refused by name (`TARGET_REACH_NO_ACTIVATION_REACHED_TARGET`).
- Worklist: N activation cases of one task are still **one** obligation, and
  they are merged into one relation summary keyed on `plannedOccurrenceId`.
- Composer: each case is its own occurrence with its own selector and its own
  order positions — cases of one task are **not** alternative paths of one
  occurrence and are not mutually exclusive. The version ledger and read-from
  arms span all of them.

### Path-condition serializer (VM half, read by the importer)

The importer accepts the shape the VM executor is building:
`emittedConditionCount` beside `conditionCount`; one `TruncatedExpression`
marker **per remaining index** at the byte cap so `emitted == declared`; a
marker for a `NULL` expression; a 256 MB cap. `declared == emitted` with
markers present is **not** a cardinality fault. A condition that is a
truncation marker is a named coverage gap on **that path** (that path is
fail-closed), not on the whole relation — one truncated activation must not
discard the other activations' cases.

### Writer half — as implemented (runtime executor, 2026-08-26)

`ConcolicRegionRuntime` stamps the five members exactly as the table above
states them. Three decisions the reader half should know, because they are
not derivable from the field list:

1. **One row per activation, published under the address it answered.** One
   activation is one VM region context — `CURRENT_TOKEN` holds a single token
   per thread — so an activation is never published twice. The sibling
   claimant mechanism is unchanged: several occurrences of one root may ride
   one activation, every claimant's capture bindings are recorded, and at the
   exit the row is published under the entered task, or re-keyed to the first
   claimant whose demanded boundary this activation did satisfy. The
   claimants that did not answer are released and offered to the next
   activation. So `N` activations of an address yield `N` rows, never `N × M`.
2. **`activationOrdinal` is taken at admission, not at publication.** It has
   to be, because the mint symbols, the configured-source mint rows, the free
   symbol names, the recorded-evidence identity and the manual-handoff
   producer lineage all name the occurrence *while the activation is still
   running* — rule 3's `#a<ord>` on `vmHandoffEvents[].producerOccurrenceId`
   is stamped at export time, long before the row exists. Density is kept by
   returning the ordinal when an activation publishes nothing (it was refused
   as not this address's occurrence, or reached no terminal): only one
   activation of an address runs at a time, so the returned ordinal is always
   the last one taken.
3. **`targetReached` is stamped on `TARGET_REACH_CLOSURE` rows only.** It is
   `true` when the activation took the plan's declared target branch event
   with the required outcome (`reachedRequiredTargetOutcome`), and for a
   target task that declares no branch event, when the activation exited
   `THROW`. A normal exit of the target root publishes with
   `targetReached: false` and is never the target case.

What the writer no longer emits: `OCCURRENCE_ADDRESS_AMBIGUOUS` and
`TARGET_EVENT_NOT_REACHED` are gone, with their counters — the first was the
symptom this contract removes, and the second is now a member of the row
rather than a reason to discard it. `ANCHOR_UNMATCHED`,
`ANCHOR_SOURCE_NEVER_EXISTED`, `TERMINAL_NEVER_REACHED`,
`REPLAY_PREFIX_UNMATCHED`, `SEED_OUTCOME_CONFLICT`,
`UNAPPLIED_MODEL_ASSIGNMENT` and `NOT_STARTED` are unchanged: none of them is
an "which activation" question.

### OCC-1 + configured sources — writer correction (runtime executor, run 25)

Two run-25 producer gaps, both runtime, both fixed in `ConcolicRegionRuntime`:

1. **`SYMBOLIC_SOURCE_EVIDENCE_NOT_DECLARED` was a self-inflicted OCC-1
   regression.** The importer admits a mint only when the evidence's
   `sourceOccurrenceId` equals `task.occurrenceId()` (the planned address)
   — `ConcolicSummaryImporter#symbolicSourceEvidence`, ~line 1178 — and the
   composer keys these events by `rawSymbol` and requires every event sharing
   one to agree on `sourceOccurrenceId` (`ConcolicSmtComposer` ~line 2851).
   A configured source's VM label is deterministic per source phase, so N
   activations of one address mint the SAME `rawSymbol` for one phase: they
   are one logical symbol, and their `sourceOccurrenceId` must be the planned
   address, not `#a<ord>`. The writer now emits the planned occurrence id in
   the configured-source **symbol name**, **evidence `sourceOccurrenceId`**,
   and **mint row `occurrenceId`**; the per-activation `#a<ord>` stays on the
   handoff `producerOccurrenceId` (rule 3), the free-symbol names, the
   recorded-evidence identity, and the row-level `occurrenceId`.

   **Reader note:** `symbolicSourceEvidence[].sourceOccurrenceId` is the
   PLANNED address (no `#a<ord>`), by design — one configured-source symbol
   spans the activations of its address. This is the opposite of rule 3's
   handoff case, and deliberately so: a handoff value is per-occurrence, a
   configured-source phase symbol is per-address.

2. **`captureAnchorSiteId` is a fast-accept, not an exact requirement.** The
   planner states a mutation member's anchor as the enclosing walk site
   (HDFS-11741: `removeExpiredKeys()#u11`), but the runtime records a mint at
   `symbolize()`'s own declaration site (`…ExpiryDate()#u2`), never the
   caller's walk, so an exact site-string match never fires. The prerequisite
   now accepts either the exact walk site being reached OR the anchor's
   configured-source field having been minted this activation
   (`mintSiteReached` over `captureAnchorPort`'s field). This is the
   granularity OCC-1 asks for: which field, not which walk or which element.

Both need a **fresh campaign** — run-25's result rows are frozen with the old
`#a<ord>` evidence ids and zero DN mutation captures.

### OCC-1 loop-bound occurrence cap (runtime executor, run 26)

A LOOP_BODY_ROOT region now unrolls its PUBLISHED occurrence set at most
`loopBound.maxBackedgeTraversals()` (the region's declared max) times, exactly
as a bounded inner loop is unrolled. The first K_L admitted activations publish
`#a1..#a<K_L>` as before; the (K_L+1)th admission onward is a bounded cut — the
iteration runs concretely (Hadoop needs the workload to complete) but starts no
VM region, symbolizes nothing, captures nothing, and publishes no occurrence
row. `publishedActivations` is the net kept-ordinal count, so an abandoned
occurrence frees its slot: the cap is on published occurrences, not admissions.

**New marker the composer must read:** one `CONCOLIC_REGION_SKIPPED` row per
capped region, written once, with:
- `skipKind` = `"LOOP_OCCURRENCES_BOUNDED"`
- `plannedOccurrenceId` = the region's planned occurrence id
- `regionId`
- `boundedAt` = K_L

It means the address's occurrence set is BOUNDED at K_L, not silently
truncated — the composer should treat the K_L published occurrences as the
complete arm/version set for that loop-body region, not as a prefix with
missing tail. It is not a failure and does not halt the campaign.

**Cap value — read this before assuming K_L=8.** `maxBackedgeTraversals()`
(no-arg) is the region's GLOBAL max over all its loops. For the DN
`offerService` region it is 64, dominated by the inner `allKeys`-walk bounds
(64), NOT the offerService root loop's own bound (8). The cap uses the no-arg
max (64) deliberately: run-26 verification (below) shows the removal-relevant
iteration is at the 14th addKeys (~offerService ordinal 20-30), so a cap at the
root-loop bound of 8 would MISS it. If a tighter 128->8 cap is wanted, it must
be closure-directed selection of the K_L occurrences whose `allKeys` writes
reach the target read — not the first K_L.

### OCC-1 loop-bound cap — corrected to the ROOT loop's bound (run 27)

Superseding the run-26 note above: the loop-body occurrence cap is now the
ROOT loop's own K_L (`ExecutionTask.rootLoopSiteId()` -> `loopBound
.maxBackedgeTraversals(siteId)`), NOT the region's global `maxBackedgeTraversals()`.
The root loop is what generates one occurrence per iteration; the region's
inner loops (the `allKeys` walks, bound 24) are unrolled WITHIN one occurrence
and must not inflate the occurrence count. Values now: DN `offerService` = 8,
NN monitor = 24, balancer BlockKeyUpdater = 4 (previously all took the region
max). The run-26 reason for using the region max — capturing the physical
key-removal iteration (~ordinal 20-30 under the 1-min lifetime) — no longer
applies: the coordinator reverted to the 600-min lifetime where keys never
physically expire and removal is forced symbolically (REMOVE_IF), so the
producer only needs the root-loop's K_L occurrences.

This is a producer-explosion mitigation, not the run-27 target-publish fix:
see the run-27 diagnosis (target NOT reached — the workload hung on symbolic
session explosion and the JVM crashed exit 135 before the balancer's SASL
handshake). The OCC-1 target-publish path itself is correct.
