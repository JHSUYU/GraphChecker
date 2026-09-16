# SURVEY-runtime — cleanup round 3 (S3), read-only survey of `runtime/` (2026-09-16)

Tree: `/tmp/claude-20003/-opt-GraphChecker/99c84a54-86ac-44a4-a030-760f664ae2a1/scratchpad/wt-stage`, tip **089a36aad**
(`git log --oneline -1`; worktree clean). Package `src/main/java/edu/uva/liftlab/graphchecker/runtime/` =
**26 files, 24,639 lines** (`wc -l`). No edits, no builds, no campaigns were run.

## 0. Method, honesty ledger, in-flight areas

- Member spans: `cleanup2/members.py` (brace matcher) → `cleanup3/members.txt` (2,237 rows). Cluster line counts are
  **disjoint line ranges** summed by awk (`cleanup3/crr_clusters.txt`, `cleanup3/rrp_clusters.txt`); CRR ranges cover
  6,421 of 6,467 lines (the rest are single blank/brace lines between clusters), RRP 3,493 of 3,529.
- Reader counts: `cleanup3/refs.sh <OwningFile> <name>…` greps `\bname\b` over `src/main/java`, `src/test/java`,
  `/opt/hadoop-hdfs-*`, `/opt/solr`, `run_engine.sh`. Every "0 readers" below is that script's output.
- **Read in full by me**: ConcolicRegionRuntime (6,467), RuntimeRegionPlanner 985–1480 + 1560–1745 + 2064–2140 +
  member map, ConcolicTaskPlan 54–560 + member map. **Not read**: RRP 77–984, 1481–1559, 1746–2063, 2141–3528 bodies
  (verdicts there rest on the member map + call-site greps and say so); ConcolicTaskPlan 560–1796 bodies.
- The other five file groups were read in full by three parallel readers whose reports I merged and spot-verified
  (`mergeBatch`, the two workload passes, `dependencyRole` census re-measured by me).
- **Firing evidence** is the clean 17960 campaign `$MY/final-6f6f88ec6/out/hdfs-17960` (verification #7, the pass that
  closed the case) and the 11741 corpus `$MY/final-05f4bf265-11741/out/hdfs-11741` (campaign #2, killed at wave 1;
  its sessions predate `SessionManifest`, so roles come from `$MY/x14/reconstruct-manifests.py`). `$MY` =
  `/tmp/claude-20003/-opt-GraphChecker/10153a9a-290a-45d1-b3c9-072f259e090e/scratchpad`.
- **Row census** (mine, `wc -l` over `schedule/iteration-0000/sessions/*/`):

  | corpus | sessions | activations (focused) | decisions | reads | writes | roots | targets | gaps | exports | attaches |
  |---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
  | 17960 | 3 | 266 (6) | 3,333 | 75 | 100 | 3 MARKER | 6 | 50 | 0 | 0 |
  | 11741 | 81 | 32,227 (721) | 8,318 | 16,083 | 25,206 | 1,021 (937 CLOCK, 84 INTEGRAL) | 194 | 11,805 | 53,424 | 3,554 |

  Context forms: 17960 ROOT 218 / ANCHOR 42 / **LOST 6**; 11741 ROOT 24,269 / ANCHOR 7,958 / LOST 0.
  Activation `instrumented=false`: 0 (17960), 24,961 (11741).
  **The only gap kinds that fire in either corpus**: `LINEAGE_LOST` (40 / 10,214), `TASK_UNANSWERED` (4 / 1,106),
  `MESSAGE_CONTEXT_REFUSED` (6 / 484) — all `cls=DIAGNOSTIC`. Every other refusal vocabulary in the package did not
  fire on either corpus; that is stated per cluster, and it is *not* by itself a deletion reason.
- Plan census: `execution_task_plan.jsonl` 45 rows (17960) / 84 (11741); `goalKind` = TARGET_REACH_CLOSURE 2 / 4, rest
  REGION_PATH_CLOSURE; every row `admission.state=EXECUTABLE`, 0 blockers; `targetBranch` on 2 / 4 rows;
  `observedWriteSites` non-empty on 2 rows (17960) and 0 rows (11741); `edgeBindings` non-empty on **every** row
  (up to 1,568 entries); `dependencyRole` = VALUE_FRONTIER 14,004 / CONCRETE_STRUCTURE_CARRIER **86** (17960), 21 CSC (11741).
- **In-flight, do not collide**: X15 owns `explore/ObligationFactory` + `runtime/FocusedReplay` focus rows (marked
  in §1.9 and excluded from every mandate below). No G/C mandate is open on `runtime/` at this tip per the memory log
  (`graphchecker-refactor-goal.md` tail: X14 merged 6f6f88ec6, 089a36aad is the artifact commit).

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

### 1.2 RuntimeRegionPlanner.java — 3,529 lines. **Notion: R8** (seed aggregation → region plan), living in `runtime/`. Callers: `CausynthTraceRecorder` only (`:1341` `planSkeletonGraph`, `:1356` `buildFlowIndex`, `:1460` `planSkeletonGraph`, `:2303` `plan`). 0 test callers.

| # | cluster (lines) | ln | notion | 2nd impl | fired | verdict |
|---|---|---:|---|---|---|---|
| P1 | header + fields 1–76 | 76 | — | — | — | KEEP |
| P2 | planSkeletonGraph 77–134 + addSkeletonActivation/containment 449–522 | 132 | R8 | — | yes (`skeleton-pass/region_skeletons.jsonl` both corpora) | KEEP → move to `causynth/` |
| P3 | exchange stamping + delivery linking 141–214, 285–338, 342–446 | 233 | R8 wire (trace rows) | pairing authority is the rows (`Interactions`, LEAN §2) | no (17960) / yes (11741) | KEEP for now; re-survey with the wire mandate. **not read** (bodies) |
| P4 | observed communication captures 525–810 | 286 | R8 wire | same as P3 | no / yes | **not read** → no verdict |
| P5 | retainInnermost*/republishEnclosing 813–930, exact identities 933–993 | 179 | R8 | — | yes | **not read** → no verdict |
| P6 | buildFlowIndex + declaredLoopBounds 996–1032 | 37 | R8 / R5 bounds | — | yes | KEEP `declaredLoopBounds`; `buildFlowIndex` goes with P13 |
| P7 | plan() 1037–1429 | 393 | R8 | — | yes (45 / 84 plan rows) | KEEP, minus the P12/P13 call sites at 1188–1201 and the `RUNTIME_REFINED_DATAFLOW` assertion at 1061–1065 |
| P8 | edge evidence 1433–1497 | 65 | R8 | `plan/EdgeBindingCatalog` + `ExecutionTask:206` only copy it forward | fires on **every** plan row (up to 1,568 bindings) | **DELETE candidate**, cross-package: producer here (1224, 1479–1492), no consumer decides anything from it. Needs the PLAN-side ruling (P-B named `edgeBindings`/`EdgeBindingCatalog` for deletion) |
| P9 | json/copy helpers 1499–1570 | 72 | support | `deepCopyValue:1499` + `RuntimeRefinedGraphBuilder.normalizeScalar` | yes | KEEP; re-home `normalizeScalar` (§2.1) |
| P10 | **target cutoff + eligibility 1571–1740** | 170 | **none under CLOSURE-V2 §1** — it decides at PLAN time which target site "counts" and blocks a task on `UNSUPPORTED_AMBIGUOUS_TARGET_PATH` | **yes** — the target slice is the runtime's propagated expression + PLAN's guard set (`SiteControlDependence`), and EXPLORE's `ClosurePlanner` owns candidate selection | `targetBranch` on 2 / 4 rows; 0 blockers in either corpus, i.e. the refusal arm never fired | **DELETE** with P13 |
| P11 | handoff sites/declaredCutPort/putTraceContext 1742–1896 | 155 | R8 | — | yes | KEEP (`declaredCutPort`'s only external reader is the finalizer) |
| P12 | symbolize + cut-port cells 1897–2063 | 167 | R8 | — | yes (38 of 45 rows carry `inputActions`) | KEEP |
| P13 | **carrier role 2064–2092** (`effectiveDependencyRole`, `concreteStructureCarrier`) | 29 | **none** — LEAN §5 deletes the carrier layer; the flags it reads (`captureRootOnly`, `loopControlOnly`, `controlOnly`, `pathAssumptionOnly`, `symbolicDemand` prefix `CONCRETE_`) are the carrier vocabulary | `plan/DependencyRole` + finalizer stamp the same role in ~20 places | **yes**: 86 `CONCRETE_STRUCTURE_CARRIER` ports in 17960's task plan, 21 in 11741 | **DELETE candidate**, cross-package (finalizer + `plan/DependencyRole` + `plan/AutomaticRegionEdge:91-92`); runtime half is 29 lines + 3 call sites (1776, 1961, 2060) |
| P14 | symbolicLeafType + materialization/fieldAccess identity 2093–2138 | 46 | R8 | — | yes | KEEP |
| P15 | exact ports 2141–2189 + branches 2190–2245 | 105 | R8 | — | yes | KEEP |
| P16 | identity / rootSelector / causalAnchor / sources 2246–2396 | 151 | R2 (offline half) | `RuntimeTraceContext.attributedActivationSource` is shared deliberately (one rule, two call sites) | yes | KEEP |
| P17 | **RefinedFlowIndex + FlowEdge/ReturnSlice/SliceNode/SliceStep 2397–2873** | 477 | **none** — CLOSURE-V2 §1: "No static data slice is needed at runtime" | EXPLORE's `ClosurePlanner` is the flip frontier; the demand is the VM expression | **yes**: the 2 (17960) and 4 (11741) `TARGET_REACH_CLOSURE` rows went through `targetReachSlice` (plan():1188–1201), which filters both the symbolize actions and the branch sites of those tasks | **DELETE**. Breaks: those 2/4 target tasks would carry every symbolize action and branch site of their region, so the seed's decision/mint volume and the wave-0 obligation count change → must be re-driven offline before merge (§4) |
| P18 | activation keys + canonicalIdentity 2874–2990 | 117 | R2 offline | — | yes | KEEP |
| P19 | Result 2991–3023 | 33 | R8 | — | yes | KEEP |
| P20 | **trace event types + LongLongMap + TraceIndex 3024–3528** | 505 | R6/R8 data model | — | yes | **SPLIT-OUT** `causynth/SeedTraceEvents` (+`TraceIndex`): 100+ references from `CausynthTraceRecorder` and `RuntimeRefinedGraphBuilder`, none from planning proper |

### 1.3 ConcolicTaskPlan.java — 1,796 lines. Notion R2 (admission) + R5 (plan-row decode). The previous survey's T4 (planned-receiver index), T7 (drift reconciliation) and `ReachedUnder` are **gone** at this tip.

| # | cluster (lines) | ln | notion | fired | verdict |
|---|---|---:|---|---|---|
| K1 | plan singleton + slots + hook-group index 54–128, 285–377 | 168 | R2 | yes | KEEP |
| K2 | releaseCandidate/markOccurrenceClaimed 131–138, 284–288 | 13 | R2 | yes | KEEP |
| K3 | publishUnansweredAddresses 140–188 | 49 | R7 | yes — the `TASK_UNANSWERED` producer (4 / 1,106 rows; `ROOT_NEVER_EXECUTED` and `OCCURRENCE_ANCHOR_UNMATCHED`/`REPLAY_PREFIX_UNMATCHED` details) | KEEP |
| K4 | RefusedCandidate 190–282 | 93 | R7 refusal facts | yes (the detail text of K3's rows) | KEEP |
| K5 | addressLoopRootInvocation 383–464 | 82 | R2 loop k | no / yes | KEEP |
| K6 | select 466–527 | 62 | R2 | yes | KEEP |
| K7 | `sourceAdmissionMismatch` 529–546 | 18 | R2 | yes | **FOLD-INTO `sourceMismatch`** — pure alias, 2 call sites (413, 504) |
| K8 | lifecycle/epoch mismatch 548–673, attribution 675–779 | 232 | R2 | yes | KEEP. **not read** (bodies 560–779) |
| K9 | settle/load/campaignTaskIds 786–881 | 96 | R2/R5 | yes | KEEP |
| K10 | compatibleRoot + RootContextSelector + RootArgumentSelector + type predicate 883–1123 | 241 | R2 candidate filter | yes | KEEP — no thread names anywhere (the `ReachedUnder` thread-name filter is gone) |
| K11 | RuntimeTask decode + queries 1125–1510 | 386 | R5 plan decode | yes | KEEP. **not read** |
| K12 | address + difference rendering 1505–1729 | 225 | R2 refusal text | yes (K3's detail) | KEEP. **not read** (1570–1729) |
| K13 | completed-evidence + target outcome 1740–1795 | 56 | R3/R7 | yes | KEEP |

Config keys (CTP is the only reader of three of them): `causynth.concolic.task.plan` (:799, also `CAUSYNTH_CONCOLIC_TASK_PLAN`), `causynth.concolic.task.id` (:801), `causynth.concolic.results` (:807) — all live (`run_engine.sh` + 4 `execute.sh`). **0 `catch (Throwable)`** in the file.

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

### 1.7 RowPublication (1,216) / SharedStateCapture (778) / SessionPublisher (291) / ConcolicResultPublisher (367) / ConcolicVmBroker (400) / JUnitMethodRunner (359) / GuardedStoreSites (230) / PathConditionWindow (204) / SymbolicMessageEnvelope (449)

| file | cluster | ln | notion | fired 17960 / 11741 | verdict |
|---|---|---:|---|---|---|
| RowPublication | entry/dispatch 34, decision rows 22 | 56 | R3 | 3,333 / 8,318 | KEEP — one entry point anywhere (`publish` ← `ConcolicResultPublisher:286`) |
| RowPublication | **root + placeholder 421** | 421 | R3 | placeholder: **4 rows on 17960, 0 on 11741**; `refusedDeclarations` and all five placeholder gap sites: **0 / 0** | **SPLIT-OUT `RowPlaceholderMint`**; delete the synthesis strength (§2.8) |
| RowPublication | write/read rows 220 | 220 | R3 | 100 / 25,206 writes (kinds INSTANCE 65 / MAP 21 / ARRAY 14 and 21,804 / 2,531 / 871; the `STATIC` branch at 1162 is never taken), 75 / 16,083 reads | KEEP |
| RowPublication | event-log + endpoint identity 103 | 103 | R2/R3 | `performer:877-890` fires as LINEAGE_LOST: **7 / 624** rows ("this read states activation -1") | **SPLIT-OUT `LoggedEventSites`** |
| RowPublication | location vocabulary 25, target row 39 | 64 | R3 | targets 6 (4 `observedFatal`) / 194 (all `observedFatal=false, reachedAnchor=true`) | KEEP the target row; **FOLD** `locationKey`/`location`/`kindOfLocation` into `SharedStateCapture`'s (the two spellings disagree: only SharedStateCapture's validates the kind set and `MAP_STATE_SLOT`; RowPublication's defaults the kind to INSTANCE at 1165) |
| SharedStateCapture | read-out paging + decode 153, record reduction 82 | 235 | R3 source | yes / yes | KEEP |
| SharedStateCapture | admission/fault vocabulary 202 | 202 | R3 refusal | **0 / 0** — `failedShared:349-358` filed no `UNSTATED_VALUE` row in either corpus | KEEP the 4 live codes; **DELETE** `SELECT_NO_ACTIVE_CONTEXT`/`SELECT_FIELD_NOT_FOUND`/`SELECT_UNSUPPORTED_TARGET`/`INVOCATION_FAILED` (426–429) + their 4 unreachable `reason()` cases (491–498) + 6 unused constants (399, 404, 410, 414, 417, 451) + 2 unused imports |
| SessionPublisher | registry + open/manifest 40, per-kind writers 39, expression table 35, io 57 | 171 | R7 | yes (17960 manifests `{SEED:1, FOCUSED:2}`) | KEEP; **DELETE `closeAll`** (7 lines; its only caller is its own `resetForTests:287`) and make `SESSIONS`/`at` private — in production the static registry can hold one entry (−≈25) |
| ConcolicResultPublisher | exit barrier 98, daemon pool 83, run totals + halt 42, goal/target 15, gap funnel 4 | 242 | R7 | `TASK_UNANSWERED` 4 / 1,106 (reasons come from CTP/CRR: 17960 = 4× ROOT_NEVER_EXECUTED; 11741 = 363 + 260 REPLAY_PREFIX_UNMATCHED, 118 ROOT_NEVER_EXECUTED, ≈365 OCCURRENCE_ANCHOR_UNMATCHED) | KEEP. **The legacy `CONCOLIC_REGION_RESULT` envelope is gone** (1 javadoc hit tree-wide, 0 in `run_engine.sh`). Its own three reasons (`TERMINAL_NEVER_REACHED`, `RESULT_PUBLICATION_REJECTED`, `RESULT_PUBLICATION_FAILED`) fired 0 / 0 |
| ConcolicVmBroker | status ABI 16, reflective bind 87, 8 capability groups 145 | 248 | R1 | yes (the `CAUSYNTH-SESSION\|GUARDED_STORE_SITES` line appears once per session: 3 / 81) | KEEP — **all 23 bound capabilities are invoked** (per-call-site list measured; the cleanup-2 `sharedFieldVersions` demand is gone). Minor: 2 dead null-guards (140, 263) after `requireCurrentCapabilities`, and 4 status constants only `describe()` mentions |
| JUnitMethodRunner | session lifetime + exit 64 | 64 | R1/R7 | yes (all 4 `execute.sh` launch it) | KEEP |
| JUnitMethodRunner | reflective JUnit lifecycle 198 | 198 | none (harness) | yes | **SPLIT-OUT `JUnitLifecycle`** — shares only `main` with the session half |
| GuardedStoreSites | install + refusal 49, table build 63, wire format 22 | 134 | R1 (the static slice's one runtime consumer) | `installed=17\|guardSites=22` ×3 (17960), `installed=5\|guardSites=7` ×81 (11741); **zero** `GUARDED_STORE_SITES_*` refusals | KEEP; **DELETE the dead `causynth.static.scope.map` property branch** (§2.7) |
| PathConditionWindow | window value 48, VM exact-range read 51, event index decode 39 | 138 | R3 | yes (every decision term) | KEEP minus **`mode()` + `TREE_MODE`/`WINDOW_MODE` + `windowed` + `Read.chars`/`Read.source` (≈14 lines, 0 readers)**; note `ConcolicRegionRuntime:3314` recomputes `contiguousConditionIndices`, the decision `forEvent:124-131` already took |
| SymbolicMessageEnvelope | outbound staging 73, inbound install/decode 142, codec 22, entry 37, clear 6 | 280 | R4 | 53,424 / 3,554 rows; `installInbound`'s own refusal fired **0 / 0** | KEEP; **DELETE `Entry.ordinal()`** (0 callers) and decide `reportUnattached` (§2.6) |

### 1.8 What cleanup round 2 left behind: nothing in the runtime
All of R1/R2's deletions are executed at this tip: the `CONCOLIC_REGION_RESULT` envelope, `ModelAssignment`/
`GuardedReadAssignment`, `FocusedReplay`'s `causynth.task` bundle, `RowRuntime`'s five write-only maps, `Lineage.path`,
`SessionPublisher.ROOT_DOMAINS`, `SymbolicMessageEnvelope.inboundUnattached`/`peek`, `Interactions.expressionRef`, the
`sharedFieldVersions` VM demand, `ReachedUnder` + the thread-name filter, the address-drift reconciliation, the
`causynth.trace.max.events` cap, and the junit/diagnostics keys — 0 code hits each; only three comments still name them
(`SessionPublisher:33`, `SharedStateCapture:424`, `GuardedStoreSites:59`).

### 1.9 FocusedReplay (530) — R5, **X15 is editing this file right now**
Reported, not proposed. Clusters: focus-row load 112, focus set/identity 54, mint-value answers 54, prefix matcher +
verdicts 92, ctor/reset 17. Fired: 80 focus rows (11741) / 2 (17960); `results` wrote 73 obligation rows on 11741
(68 NOT_ADMITTED, 5 ADMITTED) and 2 on 17960 (both ADMITTED); the prefix refusal fired 363 times on 11741.
**There is exactly one mint-value decision**: `ConcolicRegionRuntime.focusedRootValue:2228-2252`, called from the declared-field
writer (`:2267`) and the manual-field mint (`:4128`); `FocusedReplay.clockSkew`/`rootAssignment` each have exactly one
caller (`:2236`, `:2239`). Clock deltas fire on 11741 (13 of 80 focus rows carry non-empty `clockDeltas`) and not on
17960 (both rows `{}`, consistent with 3 MARKER roots). `answers` non-empty 28/80 and 0/2; `rootAssignments` 31/80 and
2/2; `unproducible` empty everywhere; `ASSIGNMENT_UNPLANTED` (the one BLOCKING gap in this area) fired 0 / 0.
Two things for X15's own list, not a mandate: `loadPlanRows:326-329` defaults a flip row with no `ordinal` to **1** and
no `outcome` to **false**; `:358` prints an unreadable focus row to stderr after `handedAFocusRow` is already true, so the
session still reports role FOCUSED with however many obligations it parsed and nothing states the shortfall.

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

## 4. Ordered deletion / refactor list

Offline gates, used by every step that claims "no behaviour change" (all three exist and have a recorded answer):
- **G-wave0** — `ExploreMain --sessions <seed>/schedule/iteration-0000/sessions --static-scope-map <seed>/static_scope_map.jsonl --topology-epoch iteration-0000 --wave 0 --target-occurrence 'hdfs-17960/nn0#epoch1/region/REGION.f0132fca-8c1f-3f7c-93e7-dc41bfc20f40#1'` on `$MY/laneA10/seed-17960`; the accepted answer is `$MY/laneA10/explore-wave0/` = **4 obligations**, manifest `tasks 9 / proposed 4 / gaps {ADMISSION_GAP: 35}`, slots `29 opened / 2 filled`. Driver: `$MY/gate_wave0.sh` (repoint `jar` and `out`).
- **G-compose17960** — `ComposeMain --sessions $MY/corpus/sessions --anchor <same> --max-valuations 128 --z3 /usr/local/bin/z3` (3 sessions); compare `sha256 candidate.smt2` and the manifest against the kept answer; `$MY/corpus/obligation_results.jsonl` (3) + `slots.jsonl` (9) are the inputs' own answer.
- **G-compose11741** — the same on `$MY/final-05f4bf265-11741/out/hdfs-11741/schedule/iteration-0000/sessions` (81 sessions) after `python3 $MY/x14/reconstruct-manifests.py` writes the roles; driver `$MY/x14/compose.sh <jar> <sessions> <anchor> <out> [root-domains]`.

| # | step | deletes | relocates | cumulative deleted | precondition | offline proof |
|---:|---|---:|---:|---:|---|---|
| 1 | §2.7 dead members: CRR 262, `Lineage.startedBy` chain + `Identity.workSubmitted` 49, `RuntimeTraceContext.parentSpanId` + `REQUEST_OCCURRENCES` 22, `SessionPublisher.closeAll` + registry 25, `SharedStateCapture` dead codes/constants/imports 30, `PathConditionWindow` dead diagnostics 14, `RuntimeRefinedGraphBuilder` 4 fields 10, `OccurrenceBinding.bindPorts` 29, `GuardedStoreSites.PATH_PROPERTY` 5, `SymbolicMessageEnvelope.Entry.ordinal` 2, `RuntimeObjectIdentity.size` 3, `ConcolicTaskPlan.sourceAdmissionMismatch` fold 5 | **456** | — | 456 | none (no woven name, no ABI name); one test asserts `statesTargetReach` (kept), one reflects `RowPublication.publish` | build + 47 @Test methods, **G-wave0** and **G-compose17960/11741** byte-identical |
| 2 | recorder: fix `mergeBatch` (+2), delete the array cluster (37), the `PROTOCOL_NOTE_EVENT` branch (8), `throwActiveMethodLite()` (3) | **48** | — | 504 | `CausynthPipeline` hook catalog + `ConcolicHookAbiTest` (RECORD_ARRAY_ELEMENT); the fix *adds* plan gap rows where a seed lost lineage | G-wave0 + both composes; plus: the 11741 REGION_STATE trace's 2 `LINEAGE_GAP` rows must now appear in `concolic_region_plan.jsonl` |
| 3 | delete the accessor call context (§1.1 C5) | **175** | — | 679 | hook catalog + ABI test; `matchesField` keeps the recorder arm (the pass-equal one) | G-wave0 = 4 obligations **and** the 17960 seed's 75 reads / 9 guarded-store mints unchanged (re-drive the seed offline from the kept trace, `$MY/laneA10/seed-17960-cache`) |
| 4 | **CRR split** (§3): 11 new classes, CRR 6,467 → ≈1,651 | 0 | ≈4,770 | 679 | steps 1–3 first, so the moves are pure relocations; no hook name changes | compile + 47 @Test methods + G-wave0 + both composes byte-identical |
| 5 | `RuntimeRegionPlanner` P17 `RefinedFlowIndex` (477) + P10 target cutoff (170) + `buildFlowIndex` (4) | **651** | — | 1,330 | ruling that the target slice is EXPLORE's (CLOSURE-V2 §1) — the frame already says so | **changes the 2 / 4 TARGET_REACH_CLOSURE tasks' symbolize + branch sets**, so it is NOT byte-identical: re-run the seed→PLAN stage offline from the kept trace and record the new task/decision counts, then G-wave0 on the new plan; taskIds change → seed cache invalidated |
| 6 | P-C: `RuntimeRefinedGraphBuilder` (1,092 after folding `normalizeScalar`), REGION_STATE weave (~40 pipeline), the second workload pass (`run_engine.sh:723`) | **1,132** | 35 | 2,462 | the PLAN-side survey confirms accessor/field ports come from the scope map + rows (§2.1 b); one recording pass must keep identity/exchanges/starts/decisions | **cannot be proven byte-identical** (plan rows change shape): its acceptance is the final 17960 + 11741 campaign named in `goal-end-state-2026-09-16` |
| 7 | relocations: `RuntimeRegionPlanner` P20 trace types (505) → `causynth/SeedTraceEvents`; recorder T5/T6/T7 (913) → `causynth/SeedTraceAggregator` + `SeedTraceReader`; `RuntimeTraceContext` T5 (192) → `TraceSpanView`; `Interactions` I4 (29) → `InteractionRefusals`; `OccurrenceBinding` (52) folds into RRP; `RowRuntime` W5 (56) folds into `Identity`; `RowPublication` splits into `RowPlaceholderMint` (421) + `LoggedEventSites` (103) and its 11 single-caller helpers fold (121); `JUnitMethodRunner`'s lifecycle half (198) → `JUnitLifecycle`; `RowPublication`'s location vocabulary folds into `SharedStateCapture` (−16); `RuntimeRefinedGraphBuilder` G3 (35) folds into `smt/JsonFields` | 0 | ≈2,520 | 2,462 | step 6 for the RRP/recorder pair; `run_engine.sh:685,724` name the aggregator class (2-line shell change) | compile + tests + G-wave0 + both composes; after this the 14 `runtime → causynth` imports drop to 3 (`ConcolicRegionRuntime`'s two finalizer constants + `MapFields.safe`), and `Text.safe` vs `causynth/MapFields.safe` — **two spellings of one notion with different semantics (one trims, one does not) meeting on the pass-agreement path**: the recorder passes `MapFields.safe(callSiteId)` into `Identity.enterFrame`, which re-normalizes with `Text.safe` (`CausynthTraceRecorder:454` → `Identity:588`, and `:283` → `Identity:490`); recorder uses `MapFields.safe` 44×, the identity files use `Text.safe` 154× — pick `Text.safe` and delete the other use (−3 imports) |
| 8 | fail-closed fixes (§2.8), behaviour-changing by design: `sequence` seq==0 → named gap (12), `javaType` object default → gap (10), `attributedActivationSource` frame disagreement → gap (8), `Interactions` key agreement (15), the 5 silent catches on the mint/observe path (~40), attestation refusal → gap (replaces the 45 dead strings, +20), `noteFaultIdle` → gap (+10), `HANDOFF_LEAF_LIMIT` truncation → gap (+5), **`RowPublication.placeholder`'s synthesized location + `fieldAccess`'s `<unstated>` owner + `javaDescriptor`'s Object default → refusals (−40 / +15)**, the 4 `depth > 8` silent walks → stated cuts (+12), `SymbolicMessageEnvelope.MAX_FRAMES` drop → gap (+6), `reportUnattached` (§2.6, +6 or −14), the broker's `0L`-for-malformed → `MALFORMED_RESULT` (+6) | — | — | 2,462 | every new code must already exist in `contract/GapKind`; register anything new in the ledger | **not** byte-identical: expected diff is "same obligations, same claim, plus N DIAGNOSTIC rows"; measure N on both corpora (17960: 2,937 decision rows would gain a `seq` refusal — that alone argues for fixing the VM id first) |
| 9 | identity fixes: Lost context → empty index (§2.2 i, 25/−4), loop-body level (§2.4, ~35), delete `Lineage`'s ITL (§2.3, 30/−14) | −18 | — | 2,480 | each is an address change → the pass-equality gate in `identity-v3-execution-index` (SEED 0 unexplained collisions, replay planned==ran, IMPORT 0 violations, wave 0 unchanged) | campaign-gated, one at a time; (ii) in §2.2 is a workload edit and is preferable if the planner wants 0 Lost |
| 10 | cross-package deletions: `edgeBindings` producer + catalog (P8, ~65 runtime), carrier role (P13, 29 + `plan/DependencyRole` + the finalizer stamps) | ~95 | — | ~2,575 | PLAN-side ruling (P-B already named both) | re-drive PLAN offline from the kept traces; both change plan-row content, so G-wave0 is re-baselined, not compared |

**Totals.** Steps 1–5 delete **1,330 lines**; steps 1–4 are provable byte-identical offline on the two kept corpora, step 5 needs one offline re-baseline. Step 6 adds **1,132** more
(2,462 = **10.0 %** of the package's 24,639 lines) but is campaign-gated. Relocation moves ≈6,550 lines into classes with one
notion each, leaving `ConcolicRegionRuntime` at ≈1,651 and `CausynthTraceRecorder` at ≈1,450. Nothing in the list is
justified by reachability: every row names either a design rule (LEAN §1/§5, CLOSURE-V2 §1/§2, IDENTITY-V3 §1) or a
zero-reader / zero-firing measurement.

**What I did not settle** (needs the planner, or a survey I was not given):
1. Whether the accessor-return ports (§2.1 row 2) become declared cells in each case's `symbolic-inputs.jsonl` or a
   `StaticScopeMap` role — 17960's only symbol arrives through one, so the answer decides step 6's shape.
2. `edgeBindings` and the carrier role are PLAN-side vocabulary with runtime producers; both need the S3-plan survey.
3. `RuntimeRegionPlanner` clusters P3/P4/P5 (502 lines of trace-row wire stamping) — **not read**; they fire only on
   11741 and deserve their own read before the wire mandate.
4. Whether the `seq == 0` majority on 17960 is a VM id defect (the recorder's `currentEventId` returning 0 while the
   symbolic gate is closed) rather than a Java-side fallback; step 8's first item should start there.
