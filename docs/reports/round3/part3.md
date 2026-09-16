
## 3. Refactor plan for ConcolicRegionRuntime (6,467 → ≈1,650 lines, no behaviour change)

**The invariant that shapes the split.** 43 methods of this class are woven by name (`CausynthPipeline:3970-4094`, enum `Hook`,
asserted by `src/test/java/.../causynth/ConcolicHookAbiTest.java`), `symbolizeConfiguredSourceField` is called from 7
`/opt/hadoop-hdfs-*` trees, `materializeSymbolicBoolean` from `annotation/Debug:15`, and `pauseObservation`/`resumeObservation`
are bound reflectively by Solr. Those 46 signatures **stay on `ConcolicRegionRuntime`** and become ≤6-line delegates; only
mechanism bodies move. That keeps the hook catalog, the ABI test and the 8 workload trees untouched, so every step is
byte-compatible by construction. The 43 hook bodies are 782 lines today (`awk` over `members.txt`).

| new class | clusters (lines) | ln | public surface it needs | what it needs back from CRR |
|---|---|---:|---|---|
| `WireExport` | C17 1787–1918, C18 1920–2210, C20 2289–2318 | 533 | `void exportLeaf(String portId, Object carrier, String field, String descriptor)`, `void attachLeaf(...)`, `void push/popOutboundFrame()`, `void push/popInboundFrame()`, `CommunicationHandoffSpec site(String portId, boolean exporting)` | `ActiveRegion activeRegion()`, `Iterable<ActiveRegion> liveRegions()`, `beginBookkeeping/endBookkeeping`, `engineExpression(String)`, `FieldAccess.declaredInstanceField`, `recordedScalar` |
| `HandoffMint` | C21 2320–2856 | 537 | `void mintDelivered(CommunicationHandoffSpec, HandoffResult, Object owner, …)`, `void mintArrived(...)`, `void mintAmbient(...)`, `static String mintLabel(String key, String portId)` | the same six, plus `RootMint.focusedAnswer(Endpoint)` and `ActiveRegion.nextHandoffAttach` |
| `BranchObservation` | C24 3124–3435, C25 3437–3478, C39 5017–5220 | 557 | `long prepare(String method, int unitIndex, String expression)`, `void observe(BranchDecision, long handle, long vmEventId, …)`, `BranchDecision.binary/multiway` | `activeRegion()`, `finish(token, kind, …)`, `statesTargetReach`, `FocusedReplay` (already static), `ActiveRegion.branchMappings/preparedBranches/lastPathConditionSize` |
| `VmBranchAttestation` | C26 3480–3729, C37 4736–4905 | 420 | `Attestation attest(ConcolicVmBroker, ActiveRegion, String siteId, String expression, boolean outcome, long eventId, int occurrence, PathConditionWindow, int baseline, SwitchExpectation, JsonElement events)`, `JsonElement semanticCondition(...)`, `JsonElement negated(...)` | nothing but `parseJson`/`rootCause` |
| `RootMint` | C11 1111–1276, C13 1417–1518, C15 1566–1709, C19 2212–2287, C29 3937–4101, C30 4103–4199, C33 4312–4399, C34 4400–4476 | 915 | `void symbolizeArgument/MethodArgument(...)`, `Object materializeArgument/MethodArgument/Reference/Primitive/StaticPrimitiveField(...)`, `void materializeField(...)`, `boolean configuredSource(String sourceId, Object owner, String fieldSignature)`, `String focusedRootValue(ActiveRegion, String rootId, Object observed)`, `boolean writeModeledField(...)` | `activeRegion()`, `engineExpression`, `FieldAccess.*`, `ModelValues.coerce`, `ActiveRegion.recordManualSymbolization/mintIsPlaceable/materialized` |
| `FaultMarker` | C12 1278–1415 minus 64 dead lines | 74 | `boolean materialize(String name)` | `activeRegion()`, `SymbolizeAction` |
| `ActiveRegion` (own file) | C41 5284–6001, C40 5222–5282, minus ~55 write-only | 724 | package-private fields as today (same package, so no widening) + the 20 methods CRR already calls | `branchMapping(...)` (moves to `BranchObservation`, so the two-line `recordDecisionRow` calls it there) |
| `SymbolizeAction` (own file) | C43 6087–6467 minus 4 | 377 | the ctor + 14 matchers as today | `FieldAccess.resolveFieldPathLeafOwner`, `instanceOfName`, `CausynthTraceRecorder.currentCallParentSiteMatches` |
| `LoopAccounting` | C4 250–367, C10 1023–1109, C42 6003–6085 minus 8 | 280 | `void checkBackedge(String, int)`, `void checkReplayBody(String, int)`, `void open/closeInvocation(String)`, `long enterLoopRoot(...)`, `void exit/throwLoopRoot(long)`, `LoopBackedgeBudget`, the two cut `Error`s | `activeRegion()`, `finish`, `ConcolicTaskPlan.addressLoopRootInvocation` |
| `FieldAccess` | C32 4263–4310, 4478–4570, 4689–4734 | 187 | `Field declaredInstanceField(...)` ×3, `Object readExactField(...)`, `Object resolveFieldPathLeafOwner(...)`, `String exactFieldSignature(Field)`, `Object freshPrimitiveBox(Object)`, `boolean instanceOfName(...)` | nothing |
| `ModelValues` | C31 4201–4261 | 61 | `Object coerce(String valueType, String value, Class<?> requested)`, `boolean isPrimitiveBox(Object)` | nothing (`plan/SmtModelValueCodec` already holds the literal codec) |

**What stays in `ConcolicRegionRuntime` (≈1,651 lines):** the 46-signature hook facade (~180 lines of delegates), C1 consts
and thread-locals (68), C2 pause/resume + bookkeeping (52), C3 configured-source phase call sites (39), C6 session
open/close (103), C7 admission + `startSymbolicRegion` (192), C8 start/claim/method frames (87), C9 region entry (186),
C14 `observeDeclaredWriteSite`/`observeCausalSource` (45), C16 expression import (75), C22 `statesTargetReach` (37),
C23 region-frame exit + hook groups (146), C27 abandon/finish/judge (101), C28 `closeOccurrence` (104), C35 region stack
(60), C36 `installEventClock` (22), C38 helpers (63), the two enums (4), imports/javadoc (87). One notion: **R1 — a
session, an activation, its lifecycle, and the hook surface the weave binds.**

**Order of the split** (each step compiles and is offline-verifiable on its own): `FieldAccess` + `ModelValues` (no
dependencies) → `SymbolizeAction` → `ActiveRegion` → `LoopAccounting` → `VmBranchAttestation` → `BranchObservation` →
`RootMint` → `WireExport` → `HandoffMint`. Do the deletions of §2.7/§2.8 **before** the moves that contain them, so the
moves stay pure relocations (that is also why the recorder's `mergeBatch` fix must precede its own split).
