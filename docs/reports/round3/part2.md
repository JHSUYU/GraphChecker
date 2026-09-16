
## 2. The known residue, each with a plan and a line estimate

### 2.1 `RuntimeRefinedGraphBuilder` + CausynthPipeline cluster D + the second workload pass (mandate P-C)
`refine` (`RuntimeRefinedGraphBuilder:64-250`) annotates the static candidate graph with one REGION_STATE execution and
hands the rows **in memory** to two consumers — `RuntimeRegionPlanner.buildFlowIndex` (`CausynthTraceRecorder:1355-1357`)
and `RuntimeSelectedRegionFinalizer.finalizeRegions` (`:1358-1364`, parameter `graph` at `RuntimeSelectedRegionFinalizer:127`).
Exactly which finalizer inputs still come from it, and what replaces each:

| refined field (builder line) | read at | decides | replacement | fires 17960 / 11741 |
|---|---|---|---|---|
| `regionIds` (190–192) | `StaticProgram:108-119` `edgesByRegion` → `RuntimeSelectedRegionFinalizer:2393,2498,2700,3077,3460`; `RuntimeRegionPlanner:2814` | which region an edge belongs to — the **only scoping input** | **already implemented statically**: `plan/StaticScopeMap.regions():388-409` + `holders():424-443` from `region_skeletons.jsonl`; `static_scope_map.jsonl` exists (810 / 172 rows) and is already handed to the replay (`run_engine.sh:1742`) | 3,559/3,559 / 782/782 edges |
| `runtimeAccessorBindings` (210–211) | `:2518` (`accessorPorts`), `:2709` | mints the `ACCESSOR_RETURN` IN ports + their `replayOccurrence`; suppresses a duplicate `EXTERNAL_CALL_RETURN` port | **a row**: a declared cell's read (`ReadRow`) or a declared input entry — not a graph-mined port | 35 → 38 ports / 24 → 138 |
| `runtimeObserved` (197–236) | `:2501,2703,2758` | gates the two port families above | **nothing** — "did this edge run" is what the rows say | 3,459/3,559 / 771/782 |
| `runtimeFieldBindings` (222) | `:2403` (`statePorts`), `:3067` | mints `ACTIVATION_FIELD_RECEIVER` ports (126 / 67) and the shared-field seeds | **nothing** — CLOSURE-V2 §2 replaces it with the writer occurrence from the rows ∪ `StaticScopeMap.writeSitesOf:567-587` | 199 / 64 |
| `fieldPath`, `fieldPathDeclarations` (228–229) | `:1856,2357,2565,3036,3136,3167,3216`; `ConcolicRegionRuntime:6192` | the root→leaf spelling used to materialize a read | **nothing** for the path (the expression carries its base, LEAN §1); the leaf declaration alone is a scope-map `cell` | 199 / 64 |
| `bindingKind` + 5 mutation keys (1014–1023) | `:2336-2349,2470,3117,3221` | container-mutation port role | **nothing** | 183 / 88 edges emitted → **0 ports minted** on either corpus |
| `runtimeExplicitFaultBindings` (199–200) | `:2807` | `EXPLICIT_SYMBOLIC_FAULT` ports | **nothing — already dead** | **0 / 0** |
| `graphKind="RUNTIME_REFINED_DATAFLOW"` (187) | `StaticProgram:635`, asserted `RuntimeRegionPlanner:1061-1065` | a provenance assertion | **nothing** | yes / yes |
| `refinementSchemaVersion` (186) | — | — | **nothing**, 0 readers | write-only |

So P-C is **two** roles: (1) `regionIds` → the existing `StaticScopeMap` role; (2) accessor/field **port minting** → rows.
Plan: (a) point `StaticProgram.edgesByRegion` at `StaticScopeMap.regions()` and delete `regionIds`; (b) replace
`accessorPorts`/`statePorts` with declared-cell ports from the scope map + the `ReadRow`/`WriteRow` join; (c) delete the
file (1,127) minus `normalizeScalar` folded into `smt/JsonFields` (35); (d) delete the REGION_STATE weave
(`CausynthPipeline:145-155` branch + `instrumentRuntimeState:351-386`) and the second workload run
(`run_engine.sh:723`, keeping `:684`), which also removes the `region-state` value of `CAUSYNTH_TRACE_MODE`;
(e) the surviving recording pass must keep identity, exchanges, starts and decisions (the P-B CAUTION in
`cleanup2-rulings`) — measured: the REGION_STATE pass is what writes `runtime/runtime_trace.jsonl` today
(`run_engine.sh:720-723`), so the skeleton pass must gain the rich hooks or the two passes must be folded into one.
**Estimate: −1,092 runtime lines, −~40 pipeline lines, −1 shell pass; +~60 lines in the finalizer/`StaticProgram` to read the scope map.** Precondition: the PLAN-side survey (S3-plan) confirms (b).

### 2.2 `Identity.here()` degraded occurrences indexed from the thread root
Two different things wear this name. (i) `Identity.here():821-824` (`state.from(0)`) is reached only from
`roleOccurrence:990-995`, i.e. from `RowRuntime.degraded:330-333` ← `ConcolicRegionRuntime:2073,2705` and from
`Identity.currentOccurrence:883` when no region is open: **11741 has 24,961 of 32,227 activations and 49,821 of 53,424
exports on a `ROLE.*` region id** (I re-measured both), 17960 has 0. (ii) The 6 LOST rows in 17960 go through
`Identity.occurrence:847-865`, whose index is `from(scopeBase)` with `scopeBase` clamped to 0 by `exitFrame:630-632`;
their LOST *form* comes from `context:1021-1042` falling to the unattributed arm because `Lineage.anchor()` is empty and
`Lineage.root()` is null, and the node `workload/unregistered#epoch0` is `attributedActivationSource`'s third arm
(`RuntimeTraceContext:816`). The 6 are 2 occurrences × 3 sessions, both
`REGION.d9f793b5` = `FSImage.updateLastAppliedTxIdFromWritten` on `main#1`, under `FSNamesystem.close`/`stopActiveServices`
— cluster shutdown after the `restart-namenode` scope closed. They are byte-identical across the 3 sessions, **but stable
by luck**: with an empty `Lineage` stack `rootToken()` is 0 and `Lineage.isOpenRoot(0):403-404` returns true
unconditionally, so that level's per-site counter is never dropped — a run-length ordinal over the life of `main`, which is
exactly what IDENTITY-V3 §1 forbids. Options: **(i) fail-closed (recommended)** — a `Lost` context carries an *empty*
`ExecutionIndex` (IDENTITY-V3 §1 defines the index as the path from the scope root, and a Lost context has none), so two
Lost occurrences the empty index cannot separate hit the existing named refusal instead of carrying a fragile address:
compute the context first in `Identity.occurrence:855-858`, pass `ExecutionIndex.empty()`, change `roleOccurrence:994`
`here()`→`atScope()`, delete `here()`, and raise `RowRuntime:180`'s gap to BLOCKING when `focused` — **~25 changed, 4
deleted**, and it collapses 11741's 24,961 ROLE.* addresses (collisions go up before they go down). (ii) complete the
lineage (the owner's gate `lineage-must-be-complete`): declare a scope around NN shutdown so the 2 occurrences get a
`Root` context — **~10 lines in the workload**, the only option that reaches 0 Lost. (iii) keep the thread-root index — rejected.

### 2.3 `Lineage` InheritableThreadLocal vs the explicit carry
Implicit (JDK `childValue`, identical in both passes): `Lineage.STACK:35-48` copies the whole frame list;
`Identity.CURRENT:35-49` → `State.copy():122-146` copies level frames+tokens but not counts;
`RuntimeTraceContext.CURRENT:37-48` → `inheritedState:945-957` copies source/request/exchange but not frames/scopes.
Explicit (only at woven sites): `Lineage.capture:178-181`/`restore:205-225`/`release:228-242` with `RESTORED`/`STARTERS`,
`Identity.STARTS:370-371` (filed by `startWork:488-500`, claimed by `state():451-458` or `claimStart:545-548`),
`RuntimeTraceContext.ASYNC_SEEDS` and `RequestScope`. **To delete the ITL**, `Identity.STARTS` must carry the scope, not
just the frame: `Start:382-390` gains a `Lineage.Carried`, `startWork` fills it with `Lineage.capture(...)`, `adopt:460-466`
calls `Lineage.restore(...)`, and `STACK` becomes a plain `ThreadLocal` — **~30 changed, ~14 deleted**. The trade is honest
and must be stated: the ITL is pass-equal for free, the explicit carry is pass-equal only if the weave covers every thread
creation; any thread created outside a woven start site starts with an empty stack → `Identity.context`'s Lost arm. Do it
only behind a measurement that the six cases have no unwoven thread creation. `ActivationRow.startedBy` has **no producer
in main** (`RowRuntime:178,206` pass `null`; 0 of 266 and 0 of 32,227 rows carry it), so `Lineage`'s `startedBy` chain plus
`Identity.workSubmitted:974-977` plus `RuntimeTraceContext:206-209,325-333` is **~45 deletable lines** today, and
`smt/Arms:526-530`'s walk over it is already dead.

### 2.4 Loop-body regions are not levels
`Identity.loopIteration` does not exist (0 hits for `loopIteration|LOOPOWN` in `src`) — no loop hook feeds the address,
which the pass-equality rule requires. `ConcolicRegionRuntime.chargeLoopBody:5491-5509` charges only the replay resource
cap. The reason a loop body is not its own level: only `Identity.enterFrame:586-594` pushes a `Level`, and it is woven at
application-scope **method** entries; a loop body is not a method, so the only iteration number in the index is
`nextSiteEvent:256-262` = the k-th entry of one *call site* in the enclosing level. Symptom in the corpora: index lengths
17960 `{1:3,2:6,3:3,4:6,5:3,7:156,8:21,9:24,10:12,11:21,12:11}` with charges `{1:24,2:3,3:6,4:9,5:6,6:9,7:7,8:7}`, 11741
lengths `{1:1706,2:2737,3:26885,4:73,5:146,6:486,12:146,19:48}` with charges `{1:7474,2:6867,3:6782,4:299}` — the charges
sit on the same frame as ordinary repeated calls, so "the 3rd iteration of this loop" is indistinguishable from "the 3rd
call at this site". Minimal change consistent with IDENTITY-V3 §1 (`Frame(callSiteId, iteration)` where iteration is the
innermost enclosing loop's count): `enterFrame` takes the call site's innermost enclosing loop id (the static side already
has it in `causynth/CfgLoopControl`), `nextSiteEvent`'s key becomes `(level, rootToken, site, loopId)` with a per-invocation
reset at `openLoopInvocation` — **~35 lines in `Identity` + the weave argument in `CausynthPipeline`, woven in both
passes**. The LOV alternative in `identity-v3-execution-index` stays contingent.

### 2.5 `ConcolicTaskPlan` T4 index / `ReachedUnder` leftovers
**None left.** `indexPlannedReceiverObjectIds`, `indexUniqueReceivers`, `plannedAccessSites`, `plannedAccessOccurrences`,
`ReachedUnder`, `stableReplayThreadContext`, `DEFAULT_EXECUTOR_THREAD_NAME` and the drift-reconciliation cluster
(`addressDrifts`/`noteAddressDrift`) are all absent at this tip (0 hits). What remains of T4/T7 is
`observedAddress`/`parseAddress`/`addressDifference`/`difference`/`indexDifference`/`contextDifference`/`anchorComponents`
(`:1505-1729`, 225 lines), which render the `TASK_UNANSWERED` detail that fires 4 / 1,106 times — KEEP. One fold:
`sourceAdmissionMismatch:542-546` is a pure alias for `sourceMismatch` (**−5 lines**, 2 call sites).

### 2.6 `SymbolicMessageEnvelope` consumer-list leftovers
**Already deleted.** `consumerOccurrenceIds` has 0 hits in the worktree and 0 in `/opt/hadoop-hdfs-*` + `/opt/solr`;
`SCHEMA = "CSE5"` (:59) and an entry is exactly 6 comma-separated fields (written :145-149, enforced :358). No workload
edit is pending: all nine propagation files touch the wire only as an opaque `String` through `takeOutbound()` /
`installInbound(String)` / `clearInbound()` (the frozen ABI in `src/test/resources/external-callers.txt:42-44`, the Solr
one bound by `getMethod`), with **zero** field parsing.
What is left in this file is one swallowed refusal and one dead accessor: **`Inbound.reportUnattached:306-313`** has three
callers (184, 194, 210) and its body only sets `lookedUp[index] = true` under a comment claiming the loss "is a GapRow
published by SessionPublisher (M2)" — no such call and no such kind exists, so "the sender put a value in the message and
no decode asked for it" is silently dropped on all 3,554 11741 attaches. Either file the row (+6 lines, one
`RowRuntime.gap` in the loop, `UNSTATED_VALUE`/DIAGNOSTIC) or delete the method and its three call sites (−14) and say the
loss is unnamed. `Entry.ordinal():446` has 0 callers anywhere (the ordinal is used internally as the lookup key at
292-297) → **DELETE (2 lines)**. Also `MAX_FRAMES = 64` (:75) is a silent cap **in both directions**: `Inbound.push:273`
and `Outbound.push:324` return without opening the frame, so `frame()` keeps answering the enclosing frame and every
ordinal inside the dropped frame collides with the parent's — the pairing key changes and nothing is named (its twin
`MAX_ENTRIES` refuses at :354 and is named by the caller at `ConcolicRegionRuntime:2040-2045`).

### 2.7 Members that are dead by the lean design's own vocabulary (measured, `cleanup3/refs.sh`)
`ConcolicRegionRuntime`: `FAULT_IDLE_UNANSWERED` + `RECORDED_FAULT_ANSWER` + their javadoc 1313–1346 (34, 0 readers);
`describeReadBack` 1692–1709 (18, 0); `isHandoffMintKey` 2605–2616 (12, 0); `record(HandoffResult)` 2970–2974 (5 — an
identity function whose javadoc says it reports refusals); `failed(...)`'s unused `detail` parameter (1);
`noteRecordedFaultAnswer` 5686–5688 + `noteFaultIdle` 5690–5696 + javadoc 5667–5685 (30 — **both bodies are empty**, so a
fault firing the plan controls but cannot answer is now silently `false`); `BranchDecision.replayTrace/boundaryNoun/
preparedNoun/observationNoun` 5120–5159 (40, 0 callers); `VmBranchEventAttestation.error` 5176/5184 + the 24
`invalid("…")` message strings (≈45 — **the field is never read**); `declaresReferenceInput` 6239–6242 (4, 0);
`reachedConfiguredSourceSites` 5379–5389 + writes 5758–5759 (13, write-only); `entryRequestKey` 5287–5297 (11,
write-only); `enclosingInvocationThread/Ordinal` 5325–5326 + the write block 671–679 (22, write-only);
`replayResourceCut` 5441 + 313 + 5507 (3, write-only); `CONTAINER_INPUT_NOT_MODELLED` 4390–4392 (3, 0);
`DECLARED_CUT_PORT_MINT_REFUSED` 4474–4476 (3, 0); `ReplayLoopResourceCut`/`LoopBoundCut` fields 6054–6082 (8, write-only);
5 empty `if`/`else` bodies left by the deleted telemetry (3164–3166, 3321–3322, 3371–3372, 3415–3416, 5608–5609) (≈10);
`accessorContextOverride` parameter of `matchesField` (always `null`, ≈6). **Subtotal ≈262 lines, no cross-file impact.**
Elsewhere in the package, same standard of proof: `RuntimeRefinedGraphBuilder.ASSOCIATIVE_MEMBER_AUTHORITY` +
`refinementSchemaVersion` + 2 binding fields (§1.5); `RuntimeObjectIdentity.size()`; `RowRuntime.iterationOf` (make
private); `OccurrenceBinding.bindPorts:37-65`; `RuntimeTraceContext.parentSpanId` and `REQUEST_OCCURRENCES:35-36,119-127`
(the ordinal it computes is stripped again by `inboundFamily:594-595`, ~12); `SessionPublisher.closeAll` (+ registry,
≈25); `SharedStateCapture` 4 dead status codes + 4 unreachable `reason()` cases + 6 unused constants + 2 unused imports
(≈30); `PathConditionWindow.mode()` + `TREE_MODE`/`WINDOW_MODE`/`windowed` + `Read.chars`/`Read.source` (≈14);
`SymbolicMessageEnvelope.Entry.ordinal()` (2); `GuardedStoreSites.PATH_PROPERTY` + its branch + the `-D` half of the
refusal text (5 — `causynth.static.scope.map` is set by nothing; only `CAUSYNTH_STATIC_SCOPE_MAP` is wired, at
`run_engine.sh:1742`); `RowPublication.literal`/`minted` (make private); `causynth.aggregate.threads` (2 files, set by
nothing). **Package subtotal outside CRR ≈ 190 lines.**
Single-caller members to fold rather than delete: 11 in `RowPublication` (121 lines: `refusedDeclarations`, `mintedSort`,
`javaTypeOf`, `symbolType`, `statedSite`, `kindOfLocation`, `indexLoggedEvents`, `concreteOf`, `leaf`, `fieldLocation`,
`javaDescriptor`), `SessionPublisher.writer`, `ConcolicTaskPlan.sourceAdmissionMismatch`, `RowRuntime` W5's 7 one-line
delegations.

### 2.8 Swallowed refusals and three-strength chains (the fail-closed rule)
`ConcolicRegionRuntime` has **52 `catch (Throwable)`**: 6 file a named gap (715, 776, 822, 2093, 2749, 3859), 19 return a
value, 10 assign/continue, and **17 are empty** (166, 178, 207, 218, 734, 1067, 1515, 1553, 2572, 2680, 2992, 3018, 3903,
3917, 3997, 4337, 4911). Five of the 17 sit on the mint/observe path and silently lose evidence the composer then cannot
join: `materializeField:1515`, `observeDeclaredWriteSite:1553` (this is the call that *starts the VM version log* — all 100
write rows depend on it), `mintHandoffLeaf:2572`, `symbolizeField:3997`, `symbolize:4337`. Also: `mintHandoffVariable:2478-2484`
says "Never silence" and then returns without filing anything; `HANDOFF_LEAF_LIMIT=64` (2780) truncates an attach's leaves
with no gap; `recordVmHandoffEvent` has a duplicated `if (site == null) return;` (2332 **and** 2334).
Chains measured elsewhere in the package: `RowRuntime.sequence:587-602` falls back to `LAST_SEQ` and **2,937 of 17960's
3,333 decision rows carry `seq == 0`** (I verified: 2937/3333; 11741 has 0) — the largest silent default in the package;
`RowRuntime.javaType:616-624` falls back to the literal `Ljava/lang/Object;` (2 of 175 rows on 17960, 419 of 98,267 on
11741); `RuntimeTraceContext.attributedActivationSource:802-817` third arm is the `UNREGISTERED_SOURCE` sentinel (6 of 266
on 17960, 0 on 11741) and its second arm silently accepts a non-unique frame stamp; `Interactions.keys:65-75` is down to
two strengths (handle, then correlation+port) and the row set cannot say which one answered (both were available on all
3,554 11741 attaches); `ConcolicRegionRuntime.observedOperatorImpliesBranch:4824-4836` is a named, directional tolerance
(KEEP); the value-equal anchor successor and the recorder's thread-name heuristics are **already deleted**.
**The one place the runtime still synthesizes a value** (the frame's hard rule) is `RowPublication.placeholder`: at
**:267-270** the third strength builds the read's `LocationId` from the *Java field signature* (`fieldLocation(signature)`)
when neither the mint table (:235-245, whose second strength is itself a `endsWith("_field_"+symbol)` suffix guess) nor the
expression's nested read (:259-266) names a VM location — a location the VM never stated, which the composer then joins
reads on. It has **no corpus evidence**: the cluster produced 4 rows on 17960 (all through strength 1) and 0 on 11741, and
the refusal at :271-276 fired 0/0. Same family, same file: `fieldAccess:1029-1034` fabricates
`LocationId.of(INSTANCE, "<unstated>", offset)`; `readFrom:985` and `fieldAccess:1054-1055` name a symbol
(`locationKey+"@v"`) the VM did not; `javaDescriptor:548` defaults an unstated `javaType` to `Ljava/lang/Object;` and that
default then drives the sort check at :279; four `depth > 8` walks return `""` silently (`symbolLeaf:599`,
`symbolType:671`, `nestedRead:1104`, `leaf:1114`) so "no symbol" and "the walk was cut" are one answer — the sibling
`collect:939-969` was already converted to an explicit stack for exactly this reason. In the broker,
`exportExpression:278` and `currentContextId:162`/`currentRegionEnterEventId:168` return `0L` for a malformed VM answer
while `currentEventId:182` returns `-1L` and `attachExpression:293` returns `MALFORMED_RESULT`; `0L` is
indistinguishable from a legal "no handle", and `attachDeliveredLeaf` reads `handle <= 0` as "the delivery carried no
producer expression", so a malformed answer becomes a concrete leaf instead of a refusal.
For contrast, the caps that are named and fail-closed (and fired 0/0): `SharedStateCapture.MAX_READ_OUT_PAGES` (:140),
`READ_OUT_PAGE_BYTES` (:143, a resume point, not a content cap), `ConcolicResultPublisher.TERMINAL_GRACE_MILLIS` (:68)
and its `ArrayBlockingQueue(128)` + `AbortPolicy`, `SymbolicMessageEnvelope.MAX_ENTRIES` (:354).
Each fix is small (5–15 lines) and has the same shape: publish the named refusal that already exists in
`contract/GapKind` instead of a value. The catch census for the other nine files is healthier than CRR's: of 31 catches,
17 file a row or a named refusal, 1 is fail-closed as a pair with `requireCurrentCapabilities`, and 13 are deliberate
close/shutdown swallows — the two that matter are in X15's file (`FocusedReplay:125,358`).

### 2.9 One defect found while reading (not residue)
`ConcolicRegionRuntime:1501-1506` — the container guard in `materializeField` has an **empty body**: the `continue;` was
absorbed into the comment text on line 1505 (`… it then carries;                     continue;`). The sibling path
`symbolizeField:3987-3990` returns correctly. So a declared *container* cell reached through the heap-field hook falls
through to `mintExactFieldLeaf` instead of being left to the VM's propagated expression. It did not change the two corpora
(17960's declared cells are primitives; the reads are 9 guarded-store field reads), but it is a one-line correctness fix
and it belongs to whoever touches C13.
