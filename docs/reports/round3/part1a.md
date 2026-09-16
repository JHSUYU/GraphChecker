
## 1. Per file: responsibility clusters

### 1.1 ConcolicRegionRuntime.java — 6,467 lines, 43 woven hooks (`CausynthPipeline:3970-4094`, asserted by `ConcolicHookAbiTest`), 1 external-ABI entry (`symbolizeConfiguredSourceField`, 7 hadoop trees)

| # | cluster (lines) | ln | notion | 2nd impl | fired 17960 / 11741 | verdict |
|---|---|---:|---|---|---|---|
| C1 | header, consts, thread-locals 88–155 | 68 | R1 | — | yes / yes | KEEP (3 dead consts, §2.7) |
| C2 | pause/resume observation 156–181 + bookkeeping 223–248 | 52 | R1 | — | yes / yes | KEEP |
| C3 | configured-source phase call sites 183–221 | 39 | R6 (delegates to recorder) | — | yes / yes | KEEP |
| C4 | loop accounting hooks 250–367 | 118 | R5 bounds | `LoopBackedgeBudget` 6003–6045, policy in `plan/LoopBoundPolicy` | yes (iterations 1–8) / yes (1–4) | SPLIT-OUT `LoopAccounting` |
| C5 | **accessor call context** 369–449, 4656–4687, `AccessorCallContext` 4975–5015, TL 139–140, `accessorCallOccurrences` 5413–5414, cleanup 3760–3766, `matchesField` arms 6381–6404 | 175 | none — replay-only frames the recording never stands on (the file says so at 379–386) | **yes**: `CausynthTraceRecorder.currentCallParentSiteMatches` is the pass-equal answer, and it is the 3rd strength of the same chain at 6385–6391 | the hooks are woven, so they run; the lightweight arm only answers inside a woven accessor call | **DELETE** (3-file change: CRR + pipeline hook catalog + ConcolicHookAbiTest). Breaks: `matchesField`/`acceptsDirectFieldOccurrence` lose the replay-only strength and fall back to the recorder arm — gate offline (wave 0 = 4 obligations, 75 reads unchanged) |
| C6 | session open/close 451–553 | 103 | R1 | — | yes / yes | KEEP |
| C7 | admission + startSymbolicRegion 555–746 | 192 | R1+R2 | — | yes / yes | KEEP (drop 671–679, §2.7) |
| C8 | start/claim/method frames 748–834 | 87 | R2 | one function with the recorder (`RowRuntime.enterFrame/startWork/claimStart`) | yes / yes | KEEP |
| C9 | region entry + enterRegionFrame 836–1021 | 186 | R2 | — | yes (FRAME_UNBALANCED 0 rows) / yes | KEEP |
| C10 | loop-root invocation frames 1023–1109 | 87 | R2 loop k | — | no (17960 has no loop-body task) / yes | SPLIT-OUT with C4 |
| C11 | symbolize/materialize argument+local 1111–1276 | 166 | R1 §1.2 | — | yes / yes | KEEP → `RootMint` |
| C12 | explicit fault marker 1278–1415 | 138 | R1 §1.1 | — | no (no marker case in these two corpora; 17960's root is a configured source) / no | KEEP the decision, **DELETE** the dead half (§2.7: the two constants + the two empty note methods = 64 lines) |
| C13 | materializeStaticField + materializeField 1417–1518 | 102 | R1 §1.2 | — | yes (9 of 75 reads are guarded-store field reads) / yes | KEEP → `RootMint`; **fix the empty container guard at 1501–1506 (bug, §2.9)** |
| C14 | observeDeclaredWriteSite + observeCausalSource 1520–1564 | 45 | R1 (starts the VM version log) | — | yes (100 write rows exist because of it) / yes | KEEP; name the silent catch at 1553 (§2.8) |
| C15 | configured-source mint 1566–1709 | 144 | R1 §1.1 | — | yes (3 root rows) / yes (1,021) | KEEP → `RootMint` (entry stays: external ABI) |
| C16 | VM expression import 1711–1785 | 75 | R1 | — | yes / yes | KEEP |
| C17 | HandoffResult + export/attach helpers 1787–1918, attach/status 2896–2975 | 212 | R4 | — | no / yes | SPLIT-OUT `WireHandoff`; **DELETE `record()` 2970–2974 (identity function) and `failed`'s unused `detail`** |
| C18 | wire message flow 1920–2210 | 291 | R4 | — | no / yes (53,424 exports) | SPLIT-OUT `WireHandoff` |
| C19 | focused root value + assignment 2212–2287 | 76 | **R5 — the one mint-value decision** | — | yes (6 focused activations) / yes (721) | KEEP → `RootMint` |
| C20 | communicationHandoffSite 2289–2318 | 30 | R4 | — | no / yes | SPLIT-OUT `WireHandoff` |
| C21 | handoff mint v_H 2320–2856 | 537 | R4 | — | no / yes (3,554 attaches) | SPLIT-OUT `WireHandoff`; 2 defects (§2.8: silent `catch` at 2572, "never silence" that returns silently at 2478–2484; dup `if (site == null)` 2332/2334; `HANDOFF_LEAF_LIMIT=64` silent cap at 2780) |
| C22 | statesTargetReach 2858–2894 | 37 | R3 | — | yes (6 target rows) / yes (194) | KEEP |
| C23 | region-frame exit + root hook groups 2977–3122 | 146 | R1 | — | yes / yes | KEEP |
| C24 | branch prepare/resolve/record 3124–3435 | 312 | R3 | — | yes (3,333 decisions) / yes | SPLIT-OUT `BranchObservation` |
| C25 | branchMapping 3437–3478 | 42 | R3 | — | yes | SPLIT-OUT `BranchObservation` |
| C26 | VM branch attestation 3480–3729 | 250 | R3 | — | yes | SPLIT-OUT; **the 24 refusal strings are write-only (§2.8)** |
| C27 | abandon/finish/judge 3731–3831 | 101 | R7 | — | yes (TASK_UNANSWERED 4 / 1,106) | KEEP |
| C28 | closeOccurrence 3833–3936 | 104 | R7 | — | yes | KEEP |
| C29 | receiver/heap field mint 3937–4101 | 165 | R1 §1.2 + R5 | — | yes / yes | KEEP → `RootMint` |
| C30 | materializePrimitiveValue + writeModeledField 4103–4199 | 97 | R5 | — | yes / yes | KEEP → `RootMint` |
| C31 | coerceModelValue 4201–4261 | 61 | R5 | `plan/SmtModelValueCodec` holds the literal decoding it calls | yes / yes | KEEP → `RootMint` |
| C32 | field-path reflection 4263–4310, field reflection 4478–4570, boxing 4689–4734 | 187 | support | — | yes / yes | SPLIT-OUT `FieldAccess` |
| C33 | symbolize + retainPropagatedInput + cut port 4312–4399 | 88 | R1 | — | yes / yes | KEEP → `RootMint` |
| C34 | authority + mint labels + dead consts 4400–4476 | 77 | R1 | — | yes | KEEP minus 6 dead lines |
| C35 | active-region stack 4572–4631 | 60 | R1 | — | yes | KEEP |
| C36 | installEventClock 4633–4654 | 22 | R2 | — | yes (every row's `index`) | KEEP |
| C37 | branch condition algebra 4736–4905 | 170 | R3 | `plan/BranchPredicateAlgebra` owns the operator complement (used) | yes | SPLIT-OUT `BranchObservation`; `observedOperatorImpliesBranch` 4824–4836 is the one tolerance (`>=` accepted for `>`/`==`) — KEEP, it is named and directional |
| C38 | misc helpers (parseJson/rootCause/recordedScalar) 4907–4969 | 63 | support | `smt/CanonicalJson` vs `ArtifactIO.sha256` are elsewhere | yes | KEEP |
| C39 | SwitchExpectation 5017–5085, BranchDecision + attestation + PreparedBranch 5087–5220 | 203 | R3 | — | switch: no / no (0 switch rows) | SPLIT-OUT `BranchObservation`; **DELETE the 4 diagnostic nouns (§2.7)** |
| C40 | OccurrenceCounter 5222–5282 | 61 | R2 **site-local counters only** | `Identity.eventSiteIndex` is the endpoint index; these are per-activation hook ordinals feeding `SymbolizeAction.acceptsOccurrence` | yes | KEEP (contract keeps site-local counters; IDENTITY-V3 §1 forbids them only *in the address*) |
| C41 | ActiveRegion 5284–6001 | 718 | R1/R3/R7 state | — | yes | SPLIT-OUT `ActiveRegion` (own file) minus 5 write-only fields |
| C42 | LoopBackedgeBudget + cut errors 6003–6085 | 83 | R5 bounds | — | yes | SPLIT-OUT `LoopAccounting`; cut-error fields write-only (8 lines) |
| C43 | SymbolizeAction 6087–6467 | 381 | R5 plan-row decode + matching | — | yes | SPLIT-OUT `SymbolizeAction` (own file); **DELETE `declaresReferenceInput` (0 readers) and the always-null `accessorContextOverride` parameter** |
