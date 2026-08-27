# One causal IR — the contract for the rewrite wave (wave 4)

Purpose: replace the JSON-row round trips between layers with ONE typed row
family per stage boundary, decoded exactly once by its owner and never
re-parsed downstream.  This is README "Refactor boundary" made concrete.
Gate for the whole wave is the same as wave 3 (one gate at the end); the
per-layer proof instruments are listed per lane.

## Row families (one decode point each; nobody calls `task.json()` to re-read)

| family | owner (sole decoder) | produced by | consumed by | today's parallel copies to delete |
|---|---|---|---|---|
| `RegionRow` (skeleton + refined region: id, root, rootAuthority/rootLoop, ports, retained loops, demand scope) | `causynth/StaticProgram` | finalizer | RRP, RRGB, instrumentation selection, recorder | `RuntimeRegionPlanner` Map<String,Object> region rows; `RegionSkeletonInstrumentationSelection` re-read; `CausynthTraceRecorder` skeleton re-read |
| `PlanRow` (task: identity, phases catalog, closure, loop bound, edge bindings, input actions, shared carriers, rootLoop) | `contract/PlanRow` (done in wave 3) | RRP → scheduler | runtime, importer, topology, instrumentation, solver | `RuntimeTask` ctor decode; `PathObservation.Scope.decode`; scheduler `promoteSelectedReplayEntry` re-reads |
| `ResultRow` (one replay execution: cases, symbolicSourceEvidence, freeSymbols, vmHandoffEvents, sharedFieldVersions/sharedMapCarriers, observations, branch mappings) | `concolic/ConcolicSummaryImporter` | runtime | composer (via case rows), topology, worklist | runtime-side FlatJson row builders (write typed → serialize once); importer re-validation of what the runtime already validated |
| `CaseEvidence` (per case: typed refs into ONE dedup table of expressions, versions, ledger rows) | `concolic/RecordedSessionModel` (+`ReadArm`, wave 3) | importer | composer, extractor | `Composer.recordedValueBindings`, `SharedStateEvidence` envelope views, extractor's own catalog rebuild |
| `Manifest`/`z3-result` | composer / extractor | — | run_engine.sh (jq) | none — the shell keys stay as they are |

Rules:
- A family is decoded ONCE, at the owner, into typed members; every other
  layer receives the object, never the JSON.  `json()` exists only for
  serialization at the stage boundary (the artifact file).
- Derived keys are never written; readers compute (wave 3 item 6 — the
  decode points already compute the nine known ones; extend, don't add).
- Refusal codes and coverage-gap kinds are design requirements (README
  "one owner per check"): they move to the owner, they are not deleted.
- No new abstraction beyond the five families above; nested static classes
  inside the owner are fine.

## Lanes (all written first, one gate)

| lane | files | what changes | proof instrument |
|---|---|---|---|
| IR-1 static | StaticProgram, RuntimeSelectedRegionFinalizer, SymbolicRegionPlanner, RegionSkeletonInstrumentationSelection, CausynthTraceRecorder (skeleton read) | `RegionRow` typed; finalizer emits it; readers take it | finalizer replay (G1's harness) byte-identical; HDFS seed differential |
| IR-2 planner | RuntimeRegionPlanner, RuntimeRefinedGraphBuilder, RuntimeWorkflowDiscovery, RegionPathWorklist, ConcolicScheduler | consume `RegionRow`, emit `PlanRow` directly (no Map→JSON→typed) | `wave3-plan/replay.sh` byte-identical (modulo removed keys) |
| IR-3 runtime | ConcolicRegionRuntime, OccurrenceMinter, RuntimeTraceContext | `RuntimeTask` = `PlanRow`; results built typed, serialized once | matrix rows (runtime is the layer the replay instruments cannot see) |
| IR-4 importer/composer | ConcolicSummaryImporter, TopologyDelta, ConcolicSmtComposer, RecordedSessionModel, SharedStateEvidence, RecordedReadFrom, BooleanReachConditionExtractor, ConcolicConstraintSolver | `ResultRow` decoded once; `CaseEvidence` refs; composer lowers from the table only | recompose 20/20 + flips 175/175 byte-identical |

Expected: ≈ −15,000 to −20,000 (src/main 78k → 58–63k).  Floor below that is
design-required checks; reported, not cut.
