
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
