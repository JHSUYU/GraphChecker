
### 1.4 CausynthTraceRecorder.java — 2,535 lines (2,084 in top-level members). Two programs in one file.

| # | cluster | ln | notion | fired | verdict |
|---|---|---:|---|---|---|
| T1 | session open + writer lifecycle | 158 | R6 | yes / yes | KEEP |
| T2 | 47 live woven/ABI hooks | 653 | R6 | yes / yes | KEEP (frame/claim/endpoint bodies delegate to `Identity`/`RuntimeTraceContext` — correctly one function) |
| T3 | thread-local call + call-site stacks | 151 | R6 **and** R5 (`ConcolicRegionRuntime:5710,6389` read it) | yes / yes | KEEP — must not move |
| T4 | row serialization | 209 | R6 | yes / yes | KEEP minus T4a/T4b |
| T5 | offline CLI + aggregation driver (`main`, `aggregate*`, `writeRuntimeRegionPlans`) | 362 | **R8** | yes / yes | **SPLIT-OUT `causynth/SeedTraceAggregator`** (+ 2-line `run_engine.sh:685,724` change) |
| T6 | offline trace parser (`loadExistingTrace`…`FlatJsonRow`) | 370 | R8 | yes / yes | **SPLIT-OUT `causynth/SeedTraceReader`** |
| T7 | offline object renaming + source re-attribution | 181 | R8 | yes / yes | SPLIT-OUT with T6 |
| T4a | `recordArrayElement` 630–651 + `writeArrayTraceLine` 2130–2144 + `RuntimeRegionPlanner.ArrayAccessEvent` 3298–3316 + the weave (`CausynthPipeline:372-373`) | 37+ | none | rows written (456+18 on 17960, 133+51 on 11741) and **never parsed back** (`parseTraceLine` has no branch; `grep -c arrayObjectId` = 0 in both refined graphs and plans) | **DELETE** (3-file change incl. `ConcolicHookAbiTest`) |
| T4b | `protocolEventKind`'s `PROTOCOL_NOTE_EVENT` branch + `noteKind` column + parse branch | ~8 | none | unreachable: `recordExchange:806-814` throws unless SEND/RECEIVE; 0 `EXCHANGE_NOTE` rows | **DELETE** |
| T4c | `throwActiveMethodLite()` (no-arg overload) 595–597 | 3 | — | no woven caller (catalog weaves the `Throwable` overload at `CausynthPipeline:3918`), no ABI caller | **FOLD** into the 1-arg form |

**Bug (verified by me): the SEED trace's lineage gaps never reach the plan.** `parseTraceLine:2024-2031` collects `LINEAGE_GAP` rows into the per-batch `TraceData.lineageGaps` (`:2356-2357`), `mergeBatch:1919-1923` merges five of six lists and **omits `lineageGaps`**, so `aggregateStateTrace:1376`'s `planGaps.addAll(trace.lineageGaps)` always adds an empty list. Measured: 11741's REGION_STATE trace holds 2 `LINEAGE_GAP` rows and `concolic_region_plan.jsonl` holds 0 (`grep -c LINEAGE_LOST` = 0). One-line fix; `aggregateSkeletonTrace:1439-1481` never reads the list at all (8 such rows in 11741's skeleton pass), so the pass-1 channel needs 1 more line.

Config: `causynth.trace.test`/`CAUSYNTH_TRACE_TEST`, `causynth.trace.mode`/`CAUSYNTH_TRACE_MODE`, `causynth.trace.start.paused`, `CAUSYNTH_TRACE_OUTPUT_DIR` — all live. **`causynth.aggregate.threads` (`:1840` and `RuntimeRefinedGraphBuilder:264`) is set by nothing.** `DEFAULT_MAX_EVENTS` no longer exists (the cap was deleted; `shutdown():1298-1310` documents why). No thread-name/substring heuristics remain: `isThreadStart`/`isAsyncTaskSubmission`/`isTaskFork` are gone, replaced by the declared table `plan/WorkStartSites:56-71` + a real `isInstance` test. 3 `catch (Throwable)`: `:150` (exit 1), `:262` and `:287` (both file `LINEAGE_LOST` twice, by name) — none silent. Remaining silent defaults: `RuntimeTraceMode.configured()` falls back to the literal `"region-skeleton"` and `run_engine.sh:684` runs pass 1 with the variable unset; `testName` → `"unknown-test"` (:1193); `outputDir` → `"target/causynth-trace"` (:1204-1207).

### 1.5 RuntimeRefinedGraphBuilder.java — 1,127 lines. **Notion: none.** LEAN §5 names the file a deletion. Sole consumers: `CausynthTraceRecorder:1344` (`refine`, in-memory), `:1366/1369` (`normalizeNumbersInPlace`), and the same rows handed to `RuntimeSelectedRegionFinalizer.finalizeRegions` (`:1358-1364`) and `RuntimeRegionPlanner.buildFlowIndex` (`:1355-1357`).

| # | cluster | ln | fired 17960 / 11741 | verdict |
|---|---|---:|---|---|
| G1 | orchestration + activation binding (`refine`, `activations`, `requireCandidateEdge`, `Result`, `SkeletonCatalog`, `Activation`) | 285 | yes / yes | **DELETE** after `regionIds` moves (§2.1) |
| G2 | candidate-graph streaming + gz writing | 130 | yes / yes | **DELETE** (the artifact goes with G1) |
| G3 | `normalizeNumbersInPlace` / `normalizeScalar` | 35 | yes / yes | **FOLD-INTO `smt/JsonFields`** (3 external call sites, unrelated to refinement) |
| G4 | field bindings (`fieldsByValueObject`, `observedFieldPaths`, `encodeBindings`, `RuntimeFieldBinding`…) | 292 | 199 / 64 edges | **DELETE** — this is "find writers via the graph"; the replacement is the `WriteRow` + `StaticScopeMap.writeSitesOf` |
| G5 | container mutation (`completedCalls`, `callArguments`, `latestContainerFields`) | 45 | the builder emits it (**183 / 88** `"bindingKind":"CONTAINER_MUTATION"` edges, beside 4,145 / 651 `ACTIVATION_FIELD_ACCESS`) and the finalizer mints **0 ports from it on either corpus** (`grep -c CONTAINER_MUTATION` = 0 in both `concolic_region_plan.jsonl` and `execution_task_plan.jsonl`, vs 38 / 138 `ACCESSOR_RETURN` and 126 / 67 `ACTIVATION_FIELD_RECEIVER`) — computed and discarded (I re-measured; reader 1 reported 0/0 from the plan side only) | **DELETE** |
| G6 | accessor + explicit-fault bindings | 164 | accessor 35 / 24 edges → 38 / 138 `ACCESSOR_RETURN` ports; explicit-fault **0 / 0** | **DELETE `encodeExplicitFaultBindings`** now; the accessor half is the live P-C residue (§2.1) |
| G7 | event re-sorting (`sortedMethods/Runtime/Fields`, `groupRuntime`, `groupFields`, `eventsForCalls`, `seq`) | 56 | yes / yes | **DELETE** — redundant: `CausynthTraceRecorder:1324` already calls `trace.sort()` before `:1344` |

Dead members inside it: `ASSOCIATIVE_MEMBER_AUTHORITY` (52–53) 0 readers; `refinementSchemaVersion` (186) 0 readers; `RuntimeFieldBinding.mutationArguments` (948–949) and `.activationFields` (950–951) assigned, never read (`toMap():993-1026` does not touch them). The "candidate graph can be multi-gigabyte" comment at :178 is not borne out — 8,833 rows / 373 KB (17960), 1,268 rows / 78 KB (11741).

### 1.6 Identity.java (1,083) / Lineage.java (435) / RowRuntime.java (868) / RuntimeTraceContext.java (1,222) / FrameJournal.java (144) / OccurrenceBinding.java (85) / Interactions.java (250) — R2/R3/R4

| file | cluster | ln | notion | fired | verdict |
|---|---|---|---:|---|---|
| Identity | I1 thread state + levels 83–458 | 279 | R2 | every row | KEEP |
| Identity | I2 start-frame carry (`STARTS`) 382–556 | 68 | R2 | yes | KEEP |
| Identity | I3 enterFrame/exitFrame 586–636 | 40 | R2 | yes | KEEP; **FOLD** `RowRuntime`'s one-line wrappers into it |
| Identity | I4 scope-base rule 647–728 | 60 | R2 | yes | KEEP |
| Identity | I5 region + VM clock 735–1075 | 35 | R2/R6 | yes | KEEP |
| Identity | I6 address + endpoint mint 821–1042 | 91 | R2 | yes | KEEP — the sole `OccurrenceAddress.of` producer in the runtime |
| Identity | I7 `messageSent` / **`workSubmitted` 974–977** | 13 | R4 / — | messageSent yes; **workSubmitted → 0 published rows** | KEEP / **DELETE** |
| Lineage | L1 stack + counters, L2 explicit carry/restore, L4 anchor+root readers | 215 | R2 | yes | KEEP |
| Lineage | **L3 `startedBy` 102–104, 184–192 + field 92 + `STARTERS` 223/232** | 10 | R2 | **0 of 266 and 0 of 32,227** activation rows carry `startedBy`; both producers pass literal `null` (`RowRuntime:178,206`); 0 external readers of `Lineage.startedBy` | **DELETE** (≈45 lines with the chain, incl. `Identity:968-977`, `RuntimeTraceContext:206-209,325-333`). `smt/Arms:459,526-530` walks it and is already dead on both corpora |
| RowRuntime | W1 session open/close, W2 activation rows, W3 event rows, W4 gaps, W6 expr refs/types/seq | 387 | R1/R3/R7 | yes | KEEP; make `iterationOf` private |
| RowRuntime | **W5 identity pass-through 519–785** | 56 | R2 | yes | **FOLD-INTO `Identity`** — 7 one-line delegations; `degraded:330-333` ignores its `site` parameter |
| RuntimeTraceContext | T1 source registry, T2 request/tick/carried scope, T3 async seeds, T4 wire header, T6 activationSource, T7 window | 707 | R1/R2/R4 | yes | KEEP |
| RuntimeTraceContext | **T5 span/lane view state 301–1156** | 192 | **R6 only** — `laneId`/`spanId`/`parentSpanId`/`remoteParentSpanId`/`receiverAttributed` are read only by `CausynthTraceRecorder` and `RuntimeRegionPlanner`; no identity input reads them | yes | **SPLIT-OUT `TraceSpanView`**; `parentSpanId` has **0 readers** → delete it from the row schema + both event records |
| FrameJournal | J2 journal 81–139 | 48 | R2 | yes (128/175 and 30,806/41,289 endpoints answer `""` = "placed at the region entry") | KEEP; defect: `JOURNALS` (64–65) has no eviction (32,227 journals on 11741) |
| OccurrenceBinding | B1 28–83 | 52 | R6 trace rows (`rootCallId → occurrenceId`) | yes (36 `rootCallId` / 45 `occurrenceId` in 17960's region plan) | **FOLD-INTO `RuntimeRegionPlanner`** (its only caller) once the trace-row plan path moves; `bindPorts:37-65` has 0 external callers; move `UNREGISTERED_SOURCE_KEY` to `RuntimeTraceContext` first (`Identity:506` reads it) |
| Interactions | I1 export ledger 33–75, I2 89–113, I3 123–188 | 73 | R4 | 11741: 53,424/53,424 exports carry `handle>0`, 3,554/3,554 attaches resolved a producer, **0 unpaired**; 17960: inert | KEEP |
| Interactions | **I4 refusal reporting 148–225** | 29 | R4 report-only | `sharedProducer`'s refusal filed **0** rows in either corpus; `endpoint(String):216-225` is an O(n) scan over ≤8,192 `MESSAGES` | SPLIT-OUT `InteractionRefusals` (off the hot path) |
