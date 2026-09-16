# REPORT-SHRINK — reachability and deletion evidence for the Design-3 refactor

**Read-only audit.** Nothing was deleted, edited, or built outside the audit worktree.
Worktree: `$SPN/wt-audit`, detached at `98aeaba19` (`refactor/flatten-handoff-next`, staging tip).
Build: one `mvn -o -q -DskipTests compile` (exit 0) → 466 class files. Worktree removed at the end of the audit.

`$SPN = /tmp/claude-20003/-opt-GraphChecker/3230912f-3427-4c18-a306-eb2005a43b37/scratchpad`

---

## 0. Headline — measured, and it contradicts the brief's premise

| quantity | measured |
|---|---:|
| `src/main/java` | **170 files, 76,365 lines** |
| declared methods (incl. nested/synthetic) | **5,244** in 466 classes |
| intra-project call edges | **10,446** (+ 2,020 class references) |
| methods reachable from the pipeline's entry points | **4,797 (91.5%)** |
| methods **not** reachable | 447, of which **311 are real source methods** (the rest are constructors of dead classes, compiler-generated `values`/`valueOf`, 3 lambda bodies, 3 `access$`) |
| dead body lines (exclusive, compiler line table) | **1,809** total / **1,583** from real source methods |
| files with **no** reachable method | **5** (971 file lines) |
| `@Test` methods | 52 (cap ≤ 100, target ≤ 80 — not a constraint today) |

**The premise of a large dead-code harvest does not hold.** By static reachability the tree is
91.5 % live. A deletion pass that only cuts unreachable code removes ≈ 3,100 file lines
(≈ 4 % of `src/main`: 952 from the four deletable dead files, plus ~1,200 body lines of scattered dead
methods at the measured 1.5–2 × expansion). Everything else has to be cut as a *named design decision*
(§2 duplicates, §3 stale stages, §4 DEAD-AFTER), not as dead code.

**The brief's specific DEAD-AFTER hypothesis is wrong, measured three ways.** The claim was that
the eight `d3/plan` branch-record types have `ConcolicRegionRuntime`'s `ReplayProgress` use as
their last reader.

1. On `refactor/d3-runtime` (tip `13243bacd`, read-only) `ReplayProgress` is already gone from
   `ConcolicRegionRuntime` (5 references at staging → 0). Measured per type, that branch removes
   `ConcolicRegionRuntime` as a reader of **`BranchReplayContract` only** (4 refs → 0).
   `BranchWitness` (5), `BranchPredicateAlgebra` (5) and `ExactConcreteBranchObservation` (14)
   keep exactly the same reference counts in `ConcolicRegionRuntime` on both branches.
2. Simulating the cut in the call graph (remove every `ConcolicRegionRuntime → BranchReplayContract`
   edge) newly kills **34 methods / 131 body lines, all inside `BranchReplayContract`**, and
   **no file becomes dead** — because `ConcolicScheduler.branchQuery`,
   `ConcolicScheduler.latestTargetSeedDecision` and `ExecutionTask.replaySchedule` still read it,
   and all three are reachable from `ConcolicScheduler.main` /`JUnitMethodRunner.main`:
   `ConcolicScheduler.main → scheduleTargetFirst → scheduleSelections → scheduleLoaded → branchQuery`.
3. The live readers of the eight types, after the runtime cut, are the PLAN stage and the task
   loader, not the runtime: `ConcolicScheduler` (4 of the 8), `ExecutionTask` (1),
   `CommunicationCatalogPlanner` (1), `RuntimeRegionPlanner` (1).

Only **`LocalCaseIdentity`** of the eight is dead today, and its blocker is `PathObservation`,
not `ConcolicRegionRuntime`. The real DEAD-AFTER trigger is a **PLAN-stage** change; it is
quantified as scenario **S2** in §4 (1,140 body lines, four whole files).

---

## Method (so the numbers can be re-derived)

- **Class-level cross-check:** `jdeps -v -filter:none -cp target/classes target/classes`.
  Result: 168 of 170 files reachable — too coarse to act on, which is why the audit is method-level.
- **Method-level call graph (the graph every number below comes from):** `javap -p -c -s -constants`
  over all 466 classes, parsed into (class, name, descriptor) nodes and `invoke*` edges, including
  the unqualified same-class call form javap prints (`// Method run:(…)`). Lambda and method-reference
  targets resolved through the `BootstrapMethods` tables from `javap -p -v`. Virtual/interface calls
  resolved to every GraphChecker subtype declaring that name+descriptor.
- **Line attribution:** `javap -p -l` `LineNumberTable` — every method's source lines come from the
  compiler, not from a brace scanner. "body lines" = the set of source lines the compiler attributes
  to that method, minus lines also attributed to a live method. It is a **lower bound** on removal:
  signatures, javadoc, fields and blank lines are excluded. Measured over the five wholly-dead files,
  file lines = **2.36 ×** body lines.
- **Entry points** (the live surface of the product, nothing else):
  the 8 `main` methods `run_engine.sh` launches (`GraphCheckerMain`, `d3.plan.ConcolicScheduler`,
  `d3.compose.ComposeMain`, `runtime.CausynthTraceRecorder`, `d3.explore.ObligationSolverMain`,
  `d3.explore.ExploreMain`, `d3.plan.GapLedger`, `runtime.JUnitMethodRunner`);
  `GraphCheckerTransformer.internalTransform` (called by Soot);
  every `public static` of `ConcolicRegionRuntime` (40), `CausynthTraceRecorder` (34),
  `SymbolicMessageEnvelope` (12) and `annotation.Debug` — these are the woven-hook + workload ABI.
  Tests are **not** entry points, so a method used only by a test reads DEAD here (flagged where it matters).
- **Deliberate over-approximation** (an audit must not invent deletions): for any class that is
  reachable, its `<clinit>`, its `access$` synthetics, `toString`/`equals`/`hashCode`/`compare`/
  `compareTo`/`run`/`call`/`close`/`iterator`, and — when it extends or implements anything outside
  GraphChecker (`Enum` ×30, `Runnable` ×7, `ThreadLocal` ×7, `Comparator` ×2, `TypeToken` ×2,
  `soot.SceneTransformer`, `soot.tagkit.Tag`, …) — all of its methods are treated as reachable.
  DEAD here therefore means *provably unreferenced under a generous model*.
- **Known blind spot, and how it was closed:** `javac` inlines `static final` primitives and Strings,
  so a class referenced only for its constants is invisible in bytecode. Every DEAD verdict below was
  re-grepped over `src/main`, `src/test`, `run_engine.sh` and `docs/` for the identifier **and** its
  string spellings. This caught three of the five bytecode-dead files
  (`BoundedLoopComposition`, `StaticSymbolicSourceDeclaration`, and constant use inside
  `PathObservation$TargetReachEvent`) and is reflected in the verdicts.
- **Reflection:** the only reflective call sites in `src/main` are `JUnitMethodRunner` (JUnit API),
  `ConcolicVmBroker` (VM ABI), `SharedFieldFlow` (workload classes) and
  `RuntimeTraceContext:865` (`Object.equals` declaring class). The only GraphChecker class names that
  appear as string literals anywhere in `src/main` are
  `runtime.ConcolicRegionRuntime` and `runtime.CausynthTraceRecorder` — the two Soot-woven classes,
  both entry points. No other class can be reached by name.

### The out-of-repo ABI, re-measured (the memory table is stale)

Re-grepped read-only across all eight `/opt/hadoop-hdfs-*` trees and `/opt/solr`.
**25 symbols**, not 21 — the memory table
(`graphchecker-external-callers`) is missing four, all added since it was written:

| class | methods called from outside this repo |
|---|---|
| `ConcolicRegionRuntime` | `symbolizeConfiguredSourceField` (7 trees), `pauseObservation`, `resumeObservation` (Solr, **reflective, fails soft**) |
| `annotation.Debug` | `makeSymbolicBoolean` → `ConcolicRegionRuntime.materializeSymbolicBoolean` (bug1/bug2/bug3) |
| `CausynthTraceRecorder` | `captureScope`, `endInboundExchange`, `registerSourceAlias`, `outboundExchange` (**two** overloads: 5-arg Solr-only, 6-arg the 8 trees), `inboundExchange`, `registerSource`, `beginSourceRequest`, `endSourceRequest`, `startRecording`, `restartSource` (17960 + 17960-jdk8 only), `captureAsync` (bug1 only), **`beginDaemonTick`**, **`endDaemonTick`**, **`enterCarriedScope`**, **`exitCarriedScope`** (the four not in the memory table; 6–7 trees each) |
| `SymbolicMessageEnvelope` | `takeOutbound`, `installInbound`, `clearInbound` |
| `annotation.CausynthExceptionTarget` | type, referenced by 7 trees + Solr (Solr forks its own copy) |

All 25 are present at `98aeaba19`. Woven-hook ABI, measured from `CausynthPipeline`'s hook catalogs:
35 `ConcolicRegionRuntime` methods and 14 `CausynthTraceRecorder` methods.
**Only two `public static` members of the three runtime classes are neither woven, nor called from
outside, nor called in-repo:** `SymbolicMessageEnvelope.inboundUnattached` (2 body lines) and
`SymbolicMessageEnvelope.peek` (3). Both re-checked against all eight trees and Solr's
`CausynthHttpPropagation$RuntimeApi` — absent from both. The runtime ABI is otherwise tight.

---

## 1. Reachability table — all 170 top-level classes

Columns: `lines` = `wc -l`. `methods live/total` counts every method the compiler emitted for that
file, nested classes included. `dead body lines` = compiler-attributed lines belonging only to
unreachable methods (lower bound on removal; × 2.36 for real file lines).
`reached from` uses these stage labels:

| label | entry point |
|---|---|
| `SOOT` | `GraphCheckerMain` / `GraphCheckerTransformer.internalTransform` (INSTRUMENT) |
| `PLAN` | `d3.plan.ConcolicScheduler.main` |
| `REPLAY` | `runtime.JUnitMethodRunner.main` |
| `IMPORT` | `runtime.CausynthTraceRecorder.main` |
| `EXPLORE` | `d3.explore.ExploreMain.main` |
| `OBLIG` | `d3.explore.ObligationSolverMain.main` |
| `COMPOSE` | `d3.compose.ComposeMain.main` |
| `GAP` | `d3.plan.GapLedger.main` |
| `HDFS-CRR` / `HDFS-REC` / `HDFS-ENV` / `HDFS-DBG` | woven hooks + the out-of-repo ABI on `ConcolicRegionRuntime` / `CausynthTraceRecorder` / `SymbolicMessageEnvelope` / `annotation.Debug` |

Verdicts: **DEAD** = no reachable method at all. `LIVE (n dead methods)` = the class is reached but
carries `n` unreachable methods. The five DEAD rows are analysed immediately after the table —
two of them are *not* deletable as-is.

| # | class | package | lines | methods live/total | dead body lines | reached from | verdict |
|---|---|---|---:|---|---:|---|---|
| 1 | `GraphCheckerMain` | `(root)` | 337 | 15/15 | 0 | SOOT | LIVE |
| 2 | `CausynthExceptionTarget` | `annotation` | 28 | 1/1 | 0 | SOOT | LIVE |
| 3 | `Debug` | `annotation` | 23 | 3/3 | 0 | HDFS-DBG,HDFS-REC,IMPORT,SOOT | LIVE |
| 4 | `CausynthArtifactWriter` | `causynth` | 65 | 4/5 | 2 | SOOT | LIVE (1 dead methods) |
| 5 | `CausynthBranchShape` | `causynth` | 106 | 6/6 | 0 | SOOT | LIVE |
| 6 | `CausynthPipeline` | `causynth` | 3621 | 178/180 | 0 | SOOT | LIVE (2 dead methods) |
| 7 | `CausynthStaticFacts` | `causynth` | 343 | 25/26 | 2 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (1 dead methods) |
| 8 | `CausynthTargetContext` | `causynth` | 26 | 2/2 | 0 | SOOT | LIVE |
| 9 | `CausynthTargetResolver` | `causynth` | 100 | 3/4 | 2 | SOOT | LIVE (1 dead methods) |
| 10 | `CfgLoopControl` | `causynth` | 502 | 41/42 | 2 | SOOT | LIVE (1 dead methods) |
| 11 | `CommunicationCatalogPlanner` | `causynth` | 293 | 7/8 | 2 | SOOT | LIVE (1 dead methods) |
| 12 | `ConcolicInstrumentationSelections` | `causynth` | 1066 | 85/89 | 19 | SOOT | LIVE (4 dead methods) |
| 13 | `ControlDependenceEdgeSupport` | `causynth` | 210 | 10/11 | 2 | SOOT | LIVE (1 dead methods) |
| 14 | `DeclaredLoopBodyBounds` | `causynth` | 316 | 17/17 | 0 | SOOT | LIVE |
| 15 | `ExceptionTargetAnnotationScanner` | `causynth` | 273 | 14/15 | 2 | SOOT | LIVE (1 dead methods) |
| 16 | `ExceptionTargetSite` | `causynth` | 31 | 2/2 | 0 | SOOT | LIVE |
| 17 | `MapFields` | `causynth` | 170 | 16/17 | 2 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (1 dead methods) |
| 18 | `RegionSkeletonInstrumentationSelection` | `causynth` | 49 | 1/2 | 2 | SOOT | LIVE (1 dead methods) |
| 19 | `RuntimeSelectedRegionFinalizer` | `causynth` | 4474 | 241/242 | 2 | HDFS-REC,IMPORT | LIVE (1 dead methods) |
| 20 | `SeedBackwardStaticAnalyzer` | `causynth` | 3145 | 192/192 | 0 | SOOT | LIVE |
| 21 | `StaticDataflowEdgeSchema` | `causynth` | 110 | 5/6 | 2 | SOOT | LIVE (1 dead methods) |
| 22 | `StaticProgram` | `causynth` | 712 | 33/33 | 0 | HDFS-REC,IMPORT,SOOT | LIVE |
| 23 | `StaticSymbolicSourceDiscovery` | `causynth` | 243 | 8/9 | 2 | SOOT | LIVE (1 dead methods) |
| 24 | `StructuralFieldAccessorProof` | `causynth` | 108 | 2/3 | 2 | SOOT | LIVE (1 dead methods) |
| 25 | `SymbolicRegionPlanner` | `causynth` | 648 | 30/31 | 2 | SOOT | LIVE (1 dead methods) |
| 26 | `WireFlowCatalog` | `causynth` | 351 | 20/20 | 0 | SOOT | LIVE |
| 27 | `ClaimPolicy` | `d3.compose` | 431 | 18/19 | 2 | COMPOSE | LIVE (1 dead methods) |
| 28 | `ComposeMain` | `d3.compose` | 569 | 23/24 | 2 | COMPOSE | LIVE (1 dead methods) |
| 29 | `Composer` | `d3.compose` | 1655 | 82/82 | 0 | COMPOSE | LIVE |
| 30 | `ContainerSmtCodec` | `d3.compose` | 2426 | 118/127 | 65 | COMPOSE,EXPLORE,OBLIG | LIVE (9 dead methods) |
| 31 | `CorpusIndex` | `d3.compose` | 630 | 46/54 | 12 | COMPOSE,EXPLORE,OBLIG | LIVE (8 dead methods) |
| 32 | `JavaSmtSorts` | `d3.compose` | 86 | 3/5 | 8 | COMPOSE,EXPLORE,OBLIG | LIVE (2 dead methods) |
| 33 | `JsonText` | `d3.compose` | 125 | 10/11 | 2 | COMPOSE,EXPLORE,OBLIG | LIVE (1 dead methods) |
| 34 | `SlotTable` | `d3.compose` | 179 | 10/10 | 0 | COMPOSE | LIVE |
| 35 | `SmtLowering` | `d3.compose` | 1561 | 118/129 | 18 | COMPOSE,EXPLORE,OBLIG | LIVE (11 dead methods) |
| 36 | `SmtSymbolTable` | `d3.compose` | 42 | 3/3 | 0 | COMPOSE,EXPLORE,OBLIG | LIVE |
| 37 | `Solver` | `d3.compose` | 359 | 28/29 | 1 | COMPOSE | LIVE (1 dead methods) |
| 38 | `VmLoweringCore` | `d3.compose` | 997 | 46/51 | 31 | COMPOSE,EXPLORE,OBLIG | LIVE (5 dead methods) |
| 39 | `VmTermLowering` | `d3.compose` | 522 | 41/53 | 16 | COMPOSE,EXPLORE,OBLIG | LIVE (12 dead methods) |
| 40 | `ActivationRow` | `d3.contract` | 127 | 12/12 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG | LIVE |
| 41 | `Arm` | `d3.contract` | 91 | 6/10 | 4 | COMPOSE | LIVE (4 dead methods) |
| 42 | `AttachRow` | `d3.contract` | 144 | 16/16 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG | LIVE |
| 43 | `CausalContext` | `d3.contract` | 231 | 39/39 | 0 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE |
| 44 | `Claim` | `d3.contract` | 96 | 11/11 | 0 | COMPOSE | LIVE |
| 45 | `ClaimKind` | `d3.contract` | 29 | 2/4 | 0 | COMPOSE | LIVE (2 dead methods) |
| 46 | `CompositionManifest` | `d3.contract` | 103 | 5/12 | 7 | COMPOSE | LIVE (7 dead methods) |
| 47 | `DecisionRow` | `d3.contract` | 117 | 13/13 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 48 | `Endpoint` | `d3.contract` | 117 | 13/14 | 1 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-REC,OBLIG,REPLAY | LIVE (1 dead methods) |
| 49 | `ExecutionIndex` | `d3.contract` | 121 | 12/15 | 5 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE (3 dead methods) |
| 50 | `ExportRow` | `d3.contract` | 106 | 12/12 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG | LIVE |
| 51 | `ExpressionTable` | `d3.contract` | 94 | 9/12 | 3 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE (3 dead methods) |
| 52 | `Family` | `d3.contract` | 63 | 7/8 | 4 | COMPOSE | LIVE (1 dead methods) |
| 53 | `Fields` | `d3.contract` | 115 | 10/11 | 2 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE (1 dead methods) |
| 54 | `Frame` | `d3.contract` | 86 | 9/9 | 0 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE |
| 55 | `GapClass` | `d3.contract` | 11 | 3/4 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE (1 dead methods) |
| 56 | `GapKind` | `d3.contract` | 29 | 3/4 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE (1 dead methods) |
| 57 | `GapRow` | `d3.contract` | 83 | 11/11 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 58 | `Ids` | `d3.contract` | 40 | 2/3 | 2 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE (1 dead methods) |
| 59 | `Interaction` | `d3.contract` | 79 | 8/10 | 2 | COMPOSE,EXPLORE,OBLIG | LIVE (2 dead methods) |
| 60 | `InteractionKind` | `d3.contract` | 14 | 3/4 | 0 | COMPOSE,EXPLORE,OBLIG | LIVE (1 dead methods) |
| 61 | `LocationId` | `d3.contract` | 105 | 9/11 | 5 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE (2 dead methods) |
| 62 | `LocationKind` | `d3.contract` | 11 | 3/4 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE (1 dead methods) |
| 63 | `NodeId` | `d3.contract` | 85 | 8/9 | 1 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE (1 dead methods) |
| 64 | `Obligation` | `d3.contract` | 127 | 14/14 | 0 | EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 65 | `ObligationResult` | `d3.contract` | 67 | 9/9 | 0 | EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 66 | `OccurrenceAddress` | `d3.contract` | 190 | 15/15 | 0 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE |
| 67 | `PathEntry` | `d3.contract` | 74 | 5/9 | 4 | COMPOSE | LIVE (4 dead methods) |
| 68 | `ReadRow` | `d3.contract` | 120 | 13/13 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 69 | `Role` | `d3.contract` | 26 | 4/4 | 0 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE |
| 70 | `RootDomain` | `d3.contract` | 85 | 11/11 | 0 | COMPOSE,EXPLORE,OBLIG | LIVE |
| 71 | `RootKind` | `d3.contract` | 14 | 3/4 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE (1 dead methods) |
| 72 | `RootMintRow` | `d3.contract` | 138 | 16/16 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 73 | `RowCodec` | `d3.contract` | 531 | 50/52 | 8 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE (2 dead methods) |
| 74 | `Selector` | `d3.contract` | 108 | 11/11 | 0 | COMPOSE,EXPLORE,PLAN | LIVE |
| 75 | `SessionDir` | `d3.contract` | 140 | 19/19 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 76 | `SessionReader` | `d3.contract` | 191 | 18/22 | 4 | COMPOSE,EXPLORE,OBLIG | LIVE (4 dead methods) |
| 77 | `TargetRow` | `d3.contract` | 106 | 12/12 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 78 | `Task` | `d3.contract` | 77 | 9/9 | 0 | EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 79 | `Verdict` | `d3.contract` | 24 | 3/4 | 0 | EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE (1 dead methods) |
| 80 | `WriteRow` | `d3.contract` | 105 | 12/12 | 0 | COMPOSE,EXPLORE,HDFS-CRR,OBLIG,REPLAY | LIVE |
| 81 | `ClosurePlanner` | `d3.explore` | 360 | 13/15 | 3 | EXPLORE,OBLIG | LIVE (2 dead methods) |
| 82 | `Corpus` | `d3.explore` | 599 | 51/59 | 14 | COMPOSE,EXPLORE,OBLIG | LIVE (8 dead methods) |
| 83 | `ExploreCodec` | `d3.explore` | 219 | 17/20 | 16 | EXPLORE,OBLIG | LIVE (3 dead methods) |
| 84 | `ExploreIds` | `d3.explore` | 38 | 2/3 | 2 | COMPOSE,EXPLORE,OBLIG | LIVE (1 dead methods) |
| 85 | `ExploreMain` | `d3.explore` | 395 | 13/14 | 2 | EXPLORE,OBLIG | LIVE (1 dead methods) |
| 86 | `FlipQuery` | `d3.explore` | 992 | 50/54 | 58 | EXPLORE,OBLIG | LIVE (4 dead methods) |
| 87 | `Frontier` | `d3.explore` | 148 | 10/12 | 2 | EXPLORE | LIVE (2 dead methods) |
| 88 | `ObligationFactory` | `d3.explore` | 276 | 11/14 | 4 | EXPLORE,OBLIG | LIVE (3 dead methods) |
| 89 | `ObligationSolverMain` | `d3.explore` | 183 | 4/5 | 2 | OBLIG | LIVE (1 dead methods) |
| 90 | `SlotTable` | `d3.explore` | 379 | 20/22 | 1 | EXPLORE | LIVE (2 dead methods) |
| 91 | `SmtText` | `d3.explore` | 234 | 11/13 | 3 | EXPLORE,OBLIG | LIVE (2 dead methods) |
| 92 | `Z3Solver` | `d3.explore` | 180 | 12/13 | 2 | OBLIG | LIVE (1 dead methods) |
| 93 | `AutomaticRegionEdge` | `d3.plan` | 118 | 4/5 | 2 | HDFS-REC,IMPORT,PLAN | LIVE (1 dead methods) |
| 94 | `BoundedLoopComposition` | `d3.plan` | 512 | 0/20 | 257 | - | **DEAD** |
| 95 | `BranchPredicateAlgebra` | `d3.plan` | 337 | 13/18 | 40 | HDFS-CRR,HDFS-DBG,HDFS-REC,PLAN,REPLAY | LIVE (5 dead methods) |
| 96 | `BranchReplayContract` | `d3.plan` | 977 | 88/100 | 53 | HDFS-CRR,HDFS-DBG,HDFS-REC,PLAN,REPLAY | LIVE (12 dead methods) |
| 97 | `BranchWitness` | `d3.plan` | 255 | 17/22 | 5 | HDFS-CRR,HDFS-DBG,HDFS-REC,PLAN,REPLAY | LIVE (5 dead methods) |
| 98 | `ClockRootPhysics` | `d3.plan` | 171 | 2/10 | 39 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | LIVE (8 dead methods) |
| 99 | `ClosureGoalKind` | `d3.plan` | 44 | 10/10 | 0 | HDFS-CRR,PLAN,REPLAY | LIVE |
| 100 | `CommunicationCatalogContract` | `d3.plan` | 149 | 6/7 | 2 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (1 dead methods) |
| 101 | `CommunicationHandoffSpec` | `d3.plan` | 126 | 14/14 | 0 | HDFS-CRR,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE |
| 102 | `ConcolicScheduler` | `d3.plan` | 3355 | 191/196 | 34 | PLAN | LIVE (5 dead methods) |
| 103 | `ConfiguredSourcePhaseContract` | `d3.plan` | 459 | 43/47 | 4 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (4 dead methods) |
| 104 | `DependencyRole` | `d3.plan` | 47 | 3/4 | 2 | HDFS-REC,IMPORT,PLAN | LIVE (1 dead methods) |
| 105 | `EdgeBindingCatalog` | `d3.plan` | 139 | 4/7 | 13 | HDFS-REC,IMPORT,PLAN | LIVE (3 dead methods) |
| 106 | `ExactConcreteBranchObservation` | `d3.plan` | 278 | 15/16 | 2 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (1 dead methods) |
| 107 | `ExecutionTask` | `d3.plan` | 534 | 40/43 | 14 | HDFS-CRR,PLAN,REPLAY,SOOT | LIVE (3 dead methods) |
| 108 | `FieldPathSpec` | `d3.plan` | 126 | 13/14 | 2 | HDFS-CRR,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (1 dead methods) |
| 109 | `GapLedger` | `d3.plan` | 614 | 16/25 | 9 | GAP | LIVE (9 dead methods) |
| 110 | `InputActionCatalog` | `d3.plan` | 89 | 7/8 | 0 | HDFS-CRR,PLAN,REPLAY,SOOT | LIVE (1 dead methods) |
| 111 | `LocalCaseIdentity` | `d3.plan` | 248 | 0/14 | 124 | - | **DEAD** |
| 112 | `LoopBoundPolicy` | `d3.plan` | 340 | 13/15 | 13 | HDFS-CRR,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (2 dead methods) |
| 113 | `MaterializationSpec` | `d3.plan` | 119 | 8/10 | 0 | HDFS-REC,IMPORT | LIVE (2 dead methods) |
| 114 | `PathObservation` | `d3.plan` | 406 | 3/37 | 138 | PLAN | LIVE (34 dead methods) |
| 115 | `PlanRow` | `d3.plan` | 78 | 9/9 | 0 | HDFS-CRR,PLAN,REPLAY,SOOT | LIVE |
| 116 | `RecordedEvidenceIdentity` | `d3.plan` | 105 | 7/7 | 0 | HDFS-CRR,REPLAY | LIVE |
| 117 | `RegionInstancePlan` | `d3.plan` | 195 | 21/21 | 0 | PLAN | LIVE |
| 118 | `RuntimePlanArtifact` | `d3.plan` | 250 | 12/15 | 8 | HDFS-REC,IMPORT,PLAN | LIVE (3 dead methods) |
| 119 | `RuntimeWorkflowDiscovery` | `d3.plan` | 743 | 60/64 | 8 | PLAN | LIVE (4 dead methods) |
| 120 | `SelectorResolution` | `d3.plan` | 134 | 6/8 | 4 | COMPOSE,EXPLORE,PLAN | LIVE (2 dead methods) |
| 121 | `SharedExpressionTable` | `d3.plan` | 852 | 82/88 | 21 | HDFS-CRR,HDFS-DBG,HDFS-REC,PLAN,REPLAY,SOOT | LIVE (6 dead methods) |
| 122 | `SharedFieldFlow` | `d3.plan` | 117 | 6/7 | 2 | HDFS-REC,IMPORT,PLAN,SOOT | LIVE (1 dead methods) |
| 123 | `SharedStateEvidence` | `d3.plan` | 673 | 19/30 | 93 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | LIVE (11 dead methods) |
| 124 | `SiteId` | `d3.plan` | 69 | 3/4 | 2 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (1 dead methods) |
| 125 | `SmtModelValueCodec` | `d3.plan` | 207 | 7/12 | 53 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | LIVE (5 dead methods) |
| 126 | `SolverPathContext` | `d3.plan` | 286 | 12/16 | 37 | PLAN | LIVE (4 dead methods) |
| 127 | `StaticSymbolicSourceDeclaration` | `d3.plan` | 19 | 0/1 | 2 | - | **DEAD** |
| 128 | `SummaryBranchMapping` | `d3.plan` | 338 | 25/34 | 22 | PLAN | LIVE (9 dead methods) |
| 129 | `SymbolicPropagationClosure` | `d3.plan` | 106 | 0/2 | 3 | - | **DEAD** |
| 130 | `SymbolicSourceEvidence` | `d3.plan` | 550 | 10/26 | 93 | HDFS-CRR | LIVE (16 dead methods) |
| 131 | `VmExpressionTable` | `d3.plan` | 413 | 28/30 | 7 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | LIVE (2 dead methods) |
| 132 | `Arms` | `d3.smt` | 647 | 43/44 | 0 | COMPOSE,EXPLORE,OBLIG | LIVE (1 dead methods) |
| 133 | `ArtifactIO` | `d3.smt` | 270 | 18/26 | 40 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (8 dead methods) |
| 134 | `CanonicalJson` | `d3.smt` | 111 | 5/6 | 2 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY,SOOT | LIVE (1 dead methods) |
| 135 | `JavaContainerTypes` | `d3.smt` | 266 | 20/23 | 2 | COMPOSE,EXPLORE,HDFS-REC,IMPORT,OBLIG,PLAN,SOOT | LIVE (3 dead methods) |
| 136 | `JavaPrimitiveBoxing` | `d3.smt` | 101 | 13/15 | 3 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE (2 dead methods) |
| 137 | `JavaPrimitiveSmtSemantics` | `d3.smt` | 635 | 43/48 | 2 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY | LIVE (5 dead methods) |
| 138 | `JsonFields` | `d3.smt` | 235 | 21/24 | 11 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,OBLIG,PLAN,REPLAY,SOOT | LIVE (3 dead methods) |
| 139 | `VmExpressionIr` | `d3.smt` | 411 | 20/29 | 83 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-DBG,HDFS-REC,OBLIG,REPLAY | LIVE (9 dead methods) |
| 140 | `VmRows` | `d3.smt` | 137 | 4/5 | 2 | COMPOSE,EXPLORE,HDFS-CRR,HDFS-DBG,HDFS-REC,OBLIG,REPLAY | LIVE (1 dead methods) |
| 141 | `GraphCheckerOptions` | `option` | 32 | 8/8 | 0 | SOOT | LIVE |
| 142 | `OptionError` | `option` | 8 | 1/1 | 0 | SOOT | LIVE |
| 143 | `OptionParser` | `option` | 106 | 7/7 | 0 | SOOT | LIVE |
| 144 | `CausynthTraceRecorder` | `runtime` | 2325 | 204/205 | 2 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,REPLAY | LIVE (1 dead methods) |
| 145 | `ConcolicRegionRuntime` | `runtime` | 7764 | 440/447 | 4 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | LIVE (7 dead methods) |
| 146 | `ConcolicResultPublisher` | `runtime` | 668 | 36/37 | 0 | HDFS-CRR,REPLAY | LIVE (1 dead methods) |
| 147 | `ConcolicTaskPlan` | `runtime` | 2024 | 100/107 | 25 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | LIVE (7 dead methods) |
| 148 | `ConcolicVmBroker` | `runtime` | 369 | 31/31 | 0 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | LIVE |
| 149 | `D3RowPublication` | `runtime` | 384 | 14/15 | 2 | HDFS-CRR,REPLAY | LIVE (1 dead methods) |
| 150 | `JUnitMethodRunner` | `runtime` | 180 | 7/8 | 2 | REPLAY | LIVE (1 dead methods) |
| 151 | `OccurrenceMinter` | `runtime` | 158 | 8/8 | 0 | HDFS-CRR,HDFS-REC,IMPORT,PLAN,REPLAY | LIVE |
| 152 | `PathConditionWindow` | `runtime` | 210 | 13/13 | 0 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | LIVE |
| 153 | `RuntimeObjectIdentity` | `runtime` | 147 | 7/8 | 1 | HDFS-REC,IMPORT | LIVE (1 dead methods) |
| 154 | `RuntimeRefinedGraphBuilder` | `runtime` | 1202 | 119/120 | 2 | HDFS-REC,IMPORT | LIVE (1 dead methods) |
| 155 | `RuntimeRegionPlanner` | `runtime` | 3733 | 211/212 | 2 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY | LIVE (1 dead methods) |
| 156 | `RuntimeTraceContext` | `runtime` | 1227 | 156/160 | 5 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,REPLAY | LIVE (4 dead methods) |
| 157 | `RuntimeTraceMode` | `runtime` | 28 | 3/5 | 0 | SOOT | LIVE (2 dead methods) |
| 158 | `SharedStateCapture` | `runtime` | 358 | 19/21 | 3 | HDFS-CRR,REPLAY | LIVE (2 dead methods) |
| 159 | `SourceRef` | `runtime` | 73 | 10/10 | 0 | HDFS-CRR,HDFS-DBG,HDFS-REC,IMPORT,PLAN,REPLAY | LIVE |
| 160 | `SymbolicMessageEnvelope` | `runtime` | 492 | 53/57 | 5 | HDFS-CRR,HDFS-ENV,REPLAY | LIVE (4 dead methods) |
| 161 | `D3Runtime` | `runtime.d3` | 627 | 34/41 | 26 | HDFS-CRR,HDFS-REC,REPLAY | LIVE (7 dead methods) |
| 162 | `FocusedReplay` | `runtime.d3` | 553 | 24/31 | 39 | HDFS-CRR,REPLAY | LIVE (7 dead methods) |
| 163 | `Identity` | `runtime.d3` | 155 | 29/31 | 4 | HDFS-CRR,HDFS-REC,REPLAY | LIVE (2 dead methods) |
| 164 | `Interactions` | `runtime.d3` | 179 | 18/21 | 12 | HDFS-CRR,HDFS-REC | LIVE (3 dead methods) |
| 165 | `Lineage` | `runtime.d3` | 321 | 43/48 | 10 | HDFS-CRR,HDFS-REC,IMPORT | LIVE (5 dead methods) |
| 166 | `OccurrenceMinterV2` | `runtime.d3` | 62 | 2/4 | 3 | HDFS-CRR,HDFS-REC,IMPORT | LIVE (2 dead methods) |
| 167 | `Selectors` | `runtime.d3` | 86 | 0/5 | 26 | - | **DEAD** |
| 168 | `SessionPublisher` | `runtime.d3` | 282 | 21/26 | 16 | HDFS-CRR,REPLAY | LIVE (5 dead methods) |
| 169 | `Text` | `runtime.d3` | 37 | 2/3 | 2 | HDFS-CRR,HDFS-REC,IMPORT,REPLAY | LIVE (1 dead methods) |
| 170 | `GraphCheckerTransformer` | `transformer` | 29 | 2/2 | 0 | SOOT | LIVE |


### The five DEAD files, one at a time

| file | lines | verdict | evidence |
|---|---:|---|---|
| `d3/plan/SymbolicPropagationClosure.java` | **106** | **DEAD — delete** | Zero references in `src/main`, `src/test`, `run_engine.sh`, `docs/`. The only occurrence of the name outside the file is a comment, `GapLedger.java:275`. The file is 27 import lines, javadoc, 3 constants and one unreferenced method (`boundaryFamilyKey`). Deleting it also requires removing two now-unused imports: `GapLedger.java:3` (free) and **`ConcolicRegionRuntime.java:24` — the runtime agent's file, a one-line edit that must be coordinated or the tree will not compile.** |
| `runtime/d3/Selectors.java` | **86** | **DEAD — delete** | Zero references anywhere, including `docs/`. Inside the brief's avoid zone (`runtime/d3/*`), but measured against `refactor/d3-runtime` (merge-base `30f479bae` → `13243bacd`) that branch touches `D3Runtime`, `FocusedReplay`, `Identity`, `Lineage`, `OccurrenceMinterV2` and **not** `Selectors` — a zero-conflict delete if the planner lifts the zone for this one file. |
| `d3/plan/BoundedLoopComposition.java` | **512** | **DEAD methods, LIVE constants** | All 14 source methods unreachable (238 body lines). But `javac` inlines its constants and four live sites read them: `PLAN_FIELD` at `RegionInstancePlan.java:31` and `ConcolicScheduler.java:562`; `LOOP_BODY_BOUND_DISAGREES` at `ConcolicScheduler.java:572` and `DeclaredLoopBodyBounds.java:164,308`. Delete = move **2 String constants** and drop 2 unused imports (`CommunicationCatalogPlanner.java:5`, `GapLedger.java:5`). Net ≈ **−505**. |
| `d3/plan/StaticSymbolicSourceDeclaration.java` | **19** | **NOT deletable — keep** | Pure constant holder. `FIELD`, `SCHEMA_VERSION`, `KIND`, `AUTHORITY` are read by `ConcolicScheduler.java:2612,2780,2781,2783` and `StaticSymbolicSourceDiscovery.java:128,165`, all inlined by `javac`. A bytecode-only audit would have deleted this and broken the PLAN stage's schema check — the same shape as the `symbolizeConfiguredSourceField` incident recorded in the external-callers memory. |
| `d3/plan/LocalCaseIdentity.java` | **248** | **DEAD — delete with `PathObservation`** | Its only referencing file is `PathObservation.java` (lines 61, 302), and `PathObservation` is itself 3/37 live. No test references it. |

Three further whole-class results that the table alone does not show:

- **`d3/plan/PathObservation.java` (406 lines) is 3/37 live.** The only live part is the nested
  `public static final class TargetReachEvent` (declared at line 132, live span 151–246), reached from
  `ConcolicScheduler.directConcreteTarget`. The outer class's 31 source methods are dead
  (108 body lines, spanning lines 43–404). Lifting `TargetReachEvent` into its own file retires
  ≈ 250 of the 406 lines and, with it, `LocalCaseIdentity` (248).
- **`d3/compose/JavaSmtSorts.smtName` (lines 78–84) has zero callers** and is a nine-line twin of
  `JsonText.smtName` in the same package (§2, D8).
- **`d3/explore/ExploreCodec.readTask` (60–66) and `writeDomain` (160–166)** are unreachable
  serialisation halves — their counterparts `writeTask` and `readDomain` are live.

### Where the dead methods are

311 unreachable source methods, 1,583 body lines, in 72 files. Files with the most, and whether the
runtime agent owns the file (measured from `refactor/d3-runtime`'s own diff plus the brief's avoid list):

| file | dead source methods | dead body lines | owner conflict |
|---|---:|---:|---|
| `d3.plan.BoundedLoopComposition` | 14 | 238 | - |
| `d3.plan.LocalCaseIdentity` | 13 | 122 | - |
| `d3.plan.PathObservation` | 31 | 108 | - |
| `d3.plan.SharedStateEvidence` | 10 | 91 | - |
| `d3.plan.SymbolicSourceEvidence` | 15 | 91 | - |
| `d3.smt.VmExpressionIr` | 8 | 81 | - |
| `d3.compose.ContainerSmtCodec` | 6 | 63 | - |
| `d3.explore.FlipQuery` | 3 | 56 | - |
| `d3.plan.BranchReplayContract` | 12 | 53 | - |
| `d3.plan.SmtModelValueCodec` | 4 | 51 | - |
| `d3.plan.BranchPredicateAlgebra` | 4 | 38 | - |
| `d3.plan.SolverPathContext` | 4 | 37 | - |
| `runtime.d3.FocusedReplay` | 6 | 37 | **runtime agent** |
| `d3.smt.ArtifactIO` | 6 | 35 | - |
| `d3.plan.ConcolicScheduler` | 2 | 32 | - |
| `d3.compose.VmLoweringCore` | 5 | 31 | - |
| `d3.plan.ClockRootPhysics` | 6 | 29 | - |
| `runtime.ConcolicTaskPlan` | 7 | 25 | **runtime agent** |
| `runtime.d3.D3Runtime` | 6 | 24 | **runtime agent** |
| `runtime.d3.Selectors` | 4 | 24 | **runtime agent** |
| `d3.plan.SummaryBranchMapping` | 8 | 22 | - |
| `d3.compose.SmtLowering` | 11 | 18 | - |
| `causynth.ConcolicInstrumentationSelections` | 3 | 17 | - |
| `d3.plan.SharedExpressionTable` | 4 | 17 | - |
| `runtime.d3.SessionPublisher` | 5 | 16 | **runtime agent** |
| `d3.explore.ExploreCodec` | 2 | 14 | - |
| `d3.explore.Corpus` | 7 | 14 | - |
| `d3.plan.ExecutionTask` | 3 | 14 | - |
| `d3.plan.EdgeBindingCatalog` | 3 | 13 | - |
| `d3.plan.LoopBoundPolicy` | 2 | 13 | - |
| `d3.compose.CorpusIndex` | 8 | 12 | - |
| `runtime.d3.Interactions` | 2 | 10 | **runtime agent** |
| `d3.compose.VmTermLowering` | 7 | 9 | - |
| `d3.smt.JsonFields` | 2 | 9 | - |
| `d3.plan.RuntimePlanArtifact` | 3 | 8 | - |
| `runtime.d3.Lineage` | 4 | 8 | **runtime agent** |
| `d3.contract.CompositionManifest` | 7 | 7 | - |
| `d3.plan.GapLedger` | 4 | 7 | - |
| `d3.compose.JavaSmtSorts` | 1 | 6 | - |
| `d3.contract.RowCodec` | 1 | 6 | - |
| `d3.plan.RuntimeWorkflowDiscovery` | 1 | 6 | - |
| `d3.contract.LocationId` | 2 | 5 | - |
| `d3.contract.ExecutionIndex` | 3 | 5 | - |
| `d3.plan.BranchWitness` | 5 | 5 | - |
| `d3.plan.VmExpressionTable` | 1 | 5 | - |
| `d3.contract.PathEntry` | 4 | 4 | - |
| `d3.contract.Arm` | 4 | 4 | - |
| `d3.contract.Family` | 1 | 4 | - |
| `d3.contract.SessionReader` | 4 | 4 | - |
| `runtime.SymbolicMessageEnvelope` | 3 | 3 | - |
| `runtime.RuntimeTraceContext` | 3 | 3 | **runtime agent** |
| `d3.contract.ExpressionTable` | 3 | 3 | - |
| `d3.explore.ObligationFactory` | 2 | 2 | - |
| `d3.explore.Frontier` | 2 | 2 | - |
| `d3.contract.Interaction` | 2 | 2 | - |
| `d3.plan.ConfiguredSourcePhaseContract` | 2 | 2 | - |
| `d3.plan.ExactConcreteBranchObservation` | 1 | 2 | - |
| `d3.plan.SelectorResolution` | 1 | 2 | - |
| `runtime.d3.Identity` | 1 | 2 | **runtime agent** |
| `runtime.SharedStateCapture` | 1 | 1 | - |
| `runtime.ConcolicRegionRuntime` | 1 | 1 | **runtime agent** |
| `runtime.RuntimeObjectIdentity` | 1 | 1 | - |
| `d3.explore.SmtText` | 1 | 1 | - |
| `d3.explore.ClosurePlanner` | 1 | 1 | - |
| `d3.explore.SlotTable` | 1 | 1 | - |
| `d3.compose.Solver` | 1 | 1 | - |
| `d3.contract.Endpoint` | 1 | 1 | - |
| `d3.contract.NodeId` | 1 | 1 | - |
| `d3.plan.SymbolicPropagationClosure` | 1 | 1 | - |
| `d3.smt.JavaPrimitiveBoxing` | 1 | 1 | - |
| `runtime.d3.OccurrenceMinterV2` | 1 | 1 | **runtime agent** |
| `d3.smt.Arms` | 1 | 0 | - |

---

## 2. The six largest files, per method

Combined: **26,092 lines, 1,469 methods, 16 unreachable.** There is almost nothing to cut here by
reachability; what these files offer a deletion pass is a *narrow entry surface* — a 7,764-line class
with 30 externally-called methods can be cut at those 30 seams, and the `cascade` column says exactly
what each seam is worth.

| file | lines | methods | dead | dead body lines | entry surface (called from outside the file) |
|---|---:|---:|---:|---:|---:|
| `runtime/ConcolicRegionRuntime.java` | 7,764 | 447 | 7 | 8 | 30 |
| `causynth/RuntimeSelectedRegionFinalizer.java` | 4,474 | 242 | 1 | 2 | 2 |
| `runtime/RuntimeRegionPlanner.java` | 3,733 | 212 | 1 | 2 | 11 |
| `causynth/CausynthPipeline.java` | 3,621 | 180 | 2 | 2 | 3 |
| `d3/plan/ConcolicScheduler.java` | 3,355 | 196 | 5 | 36 | 0 (a `main` with no in-repo callers) |
| `causynth/SeedBackwardStaticAnalyzer.java` | 3,145 | 192 | 0 | 0 | 2 |

Two of the 16 dead methods are worth naming because they are *not* dead in the usual sense:
`ConcolicScheduler$RootDependenceSlice.reachingFatalRead` (30 body lines) — a root-dependence slice
computation the scheduler no longer consults — and `ConcolicRegionRuntime.wholeStateContainerValue`
(1 line). Everything else in the six is a constructor of an unused nested class or an enum
`values`/`valueOf`.

The complete per-method tables for all 1,469 methods are in **Appendix A**, and machine-readable at
`$SPN/d-refactor/REPORT-SHRINK-methods.tsv`
(columns: file, method, descriptor, first_line, last_line, body_lines, verdict,
callers_outside_file, in_file_caller_count, in_file_callers, stages, cascade_lines, name_used_in_tests).
The entry-surface and dead tables per file follow.

### runtime/ConcolicRegionRuntime.java — 447 methods (incl. nested/synthetic), 7 dead

Entry surface (methods called from OUTSIDE the file) — 30 of 447; `cascade` = body lines that die tree-wide if that method is removed:

| method | src lines | body | callers (outside file) | in-file callers | stages | cascade |
|---|---|---:|---|---:|---|---:|
| `ConcolicRegionRuntime$SymbolizeAction.<init>` | 7138-7265 | 68 | `ConcolicTaskPlan$RuntimeTask.<init>` | 0 | HDFS-CRR,REPLAY | 69 |
| `ConcolicRegionRuntime.materializeSymbolicBoolean` | 1281-1332 | 28 | `Debug.makeSymbolicBoolean` | 0 | HDFS-CRR,HDFS-DBG | 63 |
| `ConcolicRegionRuntime$GuardedReadAssignment.<init>` | 7681-7711 | 26 | `ConcolicTaskPlan$RuntimeTask.<init>` | 0 | HDFS-CRR,REPLAY | 59 |
| `ConcolicRegionRuntime.openWorkloadSession` | 552-573 | 18 | `JUnitMethodRunner.main` | 0 | HDFS-CRR,REPLAY | 33 |
| `ConcolicRegionRuntime$ModelAssignment.<init>` | 7539-7575 | 26 | `ConcolicTaskPlan$RuntimeTask.<init>` | 1 | HDFS-CRR,REPLAY | 26 |
| `ConcolicRegionRuntime.closeWorkloadSession` | 585-607 | 18 | `JUnitMethodRunner.reportWorkloadSessionClose` | 0 | HDFS-CRR,REPLAY | 21 |
| `ConcolicRegionRuntime.noteMessageSender` | 2268-2283 | 12 | `CausynthTraceRecorder.outboundExchange` | 0 | HDFS-REC | 20 |
| `ConcolicRegionRuntime.diag` | 5546-5566 | 14 | `SharedStateCapture.fileShared` | 13 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | 14 |
| `ConcolicRegionRuntime$LoopBackedgeBudget.bodiesToJson` | 7050-7061 | 12 | `ConcolicResultPublisher.populateCompletedResult` | 0 | HDFS-CRR | 12 |
| `ConcolicRegionRuntime$ActiveRegion.nameUnreachedTargetBranch` | 6448-6464 | 11 | `ConcolicResultPublisher.populateCompletedResult` | 0 | HDFS-CRR | 11 |
| `ConcolicRegionRuntime$LoopBackedgeBudget.toJson` | 7035-7046 | 11 | `ConcolicResultPublisher.populateCompletedResult` | 0 | HDFS-CRR | 11 |
| `ConcolicRegionRuntime$ActiveRegion.releaseActivationOrdinal` | 6192-6195 | 4 | `ConcolicResultPublisher.strandWithoutTerminal` | 3 | HDFS-CRR,REPLAY | 7 |
| `ConcolicRegionRuntime$ModelAssignment.matchesConfiguredSource` | 7586-7591 | 6 | `ConcolicTaskPlan$RuntimeTask.<init>`, `ConcolicTaskPlan$RuntimeTask.answersHandoffPhase` | 1 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | 6 |
| `ConcolicRegionRuntime.observeCausalSource` | 1591-1596 | 5 | `RuntimeTraceContext.publishCausalSource` | 1 | HDFS-CRR,HDFS-REC | 5 |
| `ConcolicRegionRuntime.parseJson` | 5588-5594 | 5 | `SharedStateCapture.captureRecordedSharedStateRaw`, `SharedStateCapture.decodeTrackedLocations` | 3 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | 5 |
| `ConcolicRegionRuntime.rootCause` | 5599-5604 | 5 | `ConcolicResultPublisher.mergeEngineSummary`, `ConcolicResultPublisher.publishCompletedResult`, `ConcolicResultPublisher.submitCompletedResultPublication`, `D3RowPublication.publishKind`, `SharedStateCapture.assembleRecordedSharedState` (+1) | 24 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | 5 |
| `ConcolicRegionRuntime$GuardedReadAssignment.matches` | 7752-7757 | 5 | `ConcolicTaskPlan$RuntimeTask.guardedReadAssignment` | 0 | HDFS-CRR | 5 |
| `ConcolicRegionRuntime$RootHookGroup.<init>` | 3230-3233 | 4 | `ConcolicTaskPlan.loopRootHookGroup`, `ConcolicTaskPlan.rootHookGroup` | 0 | HDFS-CRR | 4 |
| `ConcolicRegionRuntime$ActiveRegion.addUnresolvedOnce` | 6486-6488 | 3 | `ConcolicResultPublisher.buildCompletedResult` | 22 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | 3 |
| `ConcolicRegionRuntime$ActiveRegion.evidenceSnapshot` | 6809-6812 | 3 | `SharedStateCapture.evidenceIdentity` | 0 | HDFS-CRR,REPLAY | 3 |
| `ConcolicRegionRuntime$ModelAssignment.configuredSourceAssignment` | 7578-7580 | 3 | `ConcolicTaskPlan$RuntimeTask.<init>` | 1 | HDFS-CRR,REPLAY | 3 |
| `ConcolicRegionRuntime.decodeVmEnvelope` | 1905-1908 | 2 | `SharedStateCapture.decodeTrackedLocations` | 0 | HDFS-CRR,REPLAY | 2 |
| `ConcolicRegionRuntime.isHandoffMintKey` | 2750-2751 | 2 | `ConcolicTaskPlan$RuntimeTask.answersHandoffPhase` | 0 | HDFS-CRR,REPLAY | 2 |
| `ConcolicRegionRuntime.diagAfterVmClose` | 5570-5571 | 2 | `ConcolicResultPublisher.publishCompletedResult`, `ConcolicResultPublisher.submitCompletedResultPublication` | 0 | HDFS-CRR,REPLAY | 2 |
| `ConcolicRegionRuntime$ActiveRegion.elapsedMillis` | 5997-5998 | 2 | `ConcolicResultPublisher.addResultIdentity` | 0 | HDFS-CRR | 2 |
| `ConcolicRegionRuntime.enclosingLoopRootAdmits` | 915-915 | 1 | `ConcolicTaskPlan.select` | 0 | HDFS-CRR | 1 |
| `ConcolicRegionRuntime.sameHookIdentity` | 943-943 | 1 | `ConcolicTaskPlan.loopRootHookGroup`, `ConcolicTaskPlan.rootHookGroup` | 1 | HDFS-CRR | 1 |
| `ConcolicRegionRuntime.handoffMintLabelFor` | 2756-2756 | 1 | `ConcolicTaskPlan$RuntimeTask.answersHandoffPhase` | 1 | HDFS-CRR,REPLAY | 1 |
| `ConcolicRegionRuntime$ActiveRegion.occurrenceId` | 6208-6208 | 1 | `ConcolicResultPublisher.addResultIdentity`, `SharedStateCapture.evidenceIdentity` | 4 | HDFS-CRR,HDFS-DBG,HDFS-REC,REPLAY | 1 |
| `ConcolicRegionRuntime$ModelAssignment.hasContainerTarget` | 7595-7595 | 1 | `ConcolicTaskPlan$RuntimeTask.<init>`, `ConcolicTaskPlan$RuntimeTask.answersHandoffPhase` | 1 | HDFS-CRR,REPLAY | 1 |

DEAD methods in this file (no caller from any entry point):

| method | src lines | body | verdict |
|---|---|---:|---|
| `ConcolicRegionRuntime.<init>` | 232-233 | 2 | DEAD |
| `ConcolicRegionRuntime$HandoffLeafCarrier.<init>` | 2032-2032 | 1 | DEAD |
| `ConcolicRegionRuntime.wholeStateContainerValue` | 5022-5022 | 1 | DEAD |
| `ConcolicRegionRuntime$MissingValue.valueOf` | 5630-5630 | 1 | DEAD (name also used in tests) |
| `ConcolicRegionRuntime$MissingValue.values` | 5630-5630 | 1 | DEAD |
| `ConcolicRegionRuntime$UnsupportedReplayValue.valueOf` | 5632-5632 | 1 | DEAD (name also used in tests) |
| `ConcolicRegionRuntime$UnsupportedReplayValue.values` | 5632-5632 | 1 | DEAD |

### causynth/RuntimeSelectedRegionFinalizer.java — 242 methods (incl. nested/synthetic), 1 dead

Entry surface (methods called from OUTSIDE the file) — 2 of 242; `cascade` = body lines that die tree-wide if that method is removed:

| method | src lines | body | callers (outside file) | in-file callers | stages | cascade |
|---|---|---:|---|---:|---|---:|
| `RuntimeSelectedRegionFinalizer.finalizeRegions` | 183-312 | 80 | `CausynthTraceRecorder.aggregateStateTrace` | 0 | HDFS-REC,IMPORT | 2477 |
| `RuntimeSelectedRegionFinalizer.declaredCutPortCell` | 415-451 | 15 | `RuntimeRegionPlanner.declareCutPortCells`, `RuntimeRegionPlanner.declaredCutPortAction` | 1 | HDFS-REC,IMPORT | 15 |

DEAD methods in this file (no caller from any entry point):

| method | src lines | body | verdict |
|---|---|---:|---|
| `RuntimeSelectedRegionFinalizer.<init>` | 167-168 | 2 | DEAD |

### runtime/RuntimeRegionPlanner.java — 212 methods (incl. nested/synthetic), 1 dead

Entry surface (methods called from OUTSIDE the file) — 11 of 212; `cascade` = body lines that die tree-wide if that method is removed:

| method | src lines | body | callers (outside file) | in-file callers | stages | cascade |
|---|---|---:|---|---:|---|---:|
| `RuntimeRegionPlanner.plan` | 1051-1413 | 204 | `CausynthTraceRecorder.writeRuntimeRegionPlans` | 0 | HDFS-REC,IMPORT | 1125 |
| `RuntimeRegionPlanner.planSkeletonGraph` | 85-136 | 34 | `CausynthTraceRecorder.aggregateSkeletonTrace`, `CausynthTraceRecorder.aggregateStateTrace` | 0 | HDFS-REC,IMPORT | 414 |
| `RuntimeRegionPlanner$Result.runtimePlanJsonl` | 3226-3242 | 17 | `CausynthTraceRecorder.writeRuntimeRegionPlans` | 0 | HDFS-REC,IMPORT | 66 |
| `RuntimeRegionPlanner$MethodEvent.<init>` | 3311-3333 | 23 | `CausynthTraceRecorder.parseTraceLine` | 1 | HDFS-REC,IMPORT | 23 |
| `RuntimeRegionPlanner$ProtocolEvent.<init>` | 3390-3410 | 21 | `CausynthTraceRecorder.parseTraceLine`, `CausynthTraceRecorder.recordExchange` | 0 | HDFS-REC,IMPORT | 21 |
| `RuntimeRegionPlanner$RuntimeEvent.<init>` | 3450-3466 | 17 | `CausynthTraceRecorder.parseTraceLine` | 0 | HDFS-REC,IMPORT | 17 |
| `RuntimeRegionPlanner$FieldAccessEvent.<init>` | 3486-3498 | 13 | `CausynthTraceRecorder.parseTraceLine`, `CausynthTraceRecorder.recordField`, `RuntimeRefinedGraphBuilder.refine` | 0 | HDFS-REC,IMPORT | 13 |
| `RuntimeRegionPlanner$ArrayAccessEvent.<init>` | 3514-3525 | 12 | `CausynthTraceRecorder.recordArrayElement` | 0 | HDFS-REC | 12 |
| `RuntimeRegionPlanner$MethodEvent.reattribute` | 3346-3358 | 9 | `CausynthTraceRecorder.reattributeFramesToRegisteredOwners` | 0 | HDFS-REC,IMPORT | 9 |
| `RuntimeRegionPlanner$MethodEvent.<init>` | 3298-3302 | 2 | `CausynthTraceRecorder.enterMethod`, `CausynthTraceRecorder.enterMethodLite` | 0 | HDFS-REC | 2 |
| `RuntimeRegionPlanner.buildFlowIndex` | 1000-1000 | 1 | `CausynthTraceRecorder.aggregateStateTrace` | 0 | HDFS-REC,IMPORT | 1 |

DEAD methods in this file (no caller from any entry point):

| method | src lines | body | verdict |
|---|---|---:|---|
| `RuntimeRegionPlanner.<init>` | 74-75 | 2 | DEAD |

### causynth/CausynthPipeline.java — 180 methods (incl. nested/synthetic), 2 dead

Entry surface (methods called from OUTSIDE the file) — 3 of 180; `cascade` = body lines that die tree-wide if that method is removed:

| method | src lines | body | callers (outside file) | in-file callers | stages | cascade |
|---|---|---:|---|---:|---|---:|
| `CausynthPipeline.run` | 94-99 | 4 | `GraphCheckerTransformer.internalTransform` | 0 | SOOT | 5727 |
| `CausynthPipeline.<init>` | 88-90 | 3 | `GraphCheckerTransformer.internalTransform` | 0 | SOOT | 3 |
| `CausynthPipeline.conservativeDispatchTargets` | 2882-2882 | 1 | `SeedBackwardStaticAnalyzer.processDispatchInvoke` | 0 | SOOT | 1 |

DEAD methods in this file (no caller from any entry point):

| method | src lines | body | verdict |
|---|---|---:|---|
| `CausynthPipeline$Hook.valueOf` | 3307-3307 | 1 | DEAD (name also used in tests) |
| `CausynthPipeline$Hook.values` | 3307-3307 | 1 | DEAD |

### d3/plan/ConcolicScheduler.java — 196 methods (incl. nested/synthetic), 5 dead

Entry surface (methods called from OUTSIDE the file) — 0 of 196; `cascade` = body lines that die tree-wide if that method is removed:

| method | src lines | body | callers (outside file) | in-file callers | stages | cascade |
|---|---|---:|---|---:|---|---:|

DEAD methods in this file (no caller from any entry point):

| method | src lines | body | verdict |
|---|---|---:|---|
| `ConcolicScheduler$RootDependenceSlice.reachingFatalRead` | 2316-2352 | 30 | DEAD |
| `ConcolicScheduler.<init>` | 86-87 | 2 | DEAD |
| `ConcolicScheduler$SymbolicInputSelection.declares` | 3107-3108 | 2 | DEAD |
| `ConcolicScheduler$RootDependenceSlice.lambda$reachingFatalRead$0` | 2327-2327 | 1 | DEAD |
| `ConcolicScheduler$ClosureMode.valueOf` | 3168-3168 | 1 | DEAD (name also used in tests) |

### causynth/SeedBackwardStaticAnalyzer.java — 192 methods (incl. nested/synthetic), 0 dead

Entry surface (methods called from OUTSIDE the file) — 2 of 192; `cascade` = body lines that die tree-wide if that method is removed:

| method | src lines | body | callers (outside file) | in-file callers | stages | cascade |
|---|---|---:|---|---:|---|---:|
| `SeedBackwardStaticAnalyzer.analyze` | 252-299 | 31 | `CausynthPipeline.analyze` | 0 | SOOT | 2281 |
| `SeedBackwardStaticAnalyzer.<init>` | 129-231 | 53 | `CausynthPipeline.analyze` | 0 | SOOT | 187 |

DEAD methods in this file: none.


### 2b. Duplicate mechanisms — two implementations of one rule

Every pair below was confirmed by reading **both** bodies. Line ranges are brace-matched; call-site
counts are grep-measured. Paths are relative to
`$SPN/wt-audit/src/main/java/edu/uva/liftlab/graphchecker` (written `SRC`).

**D1 — branch polarity: "contribute `term` on the true arm, `(not term)` otherwise". Four copies.**

| impl | location | lines | callers |
|---|---|---:|---|
| A (owner) | `SRC/d3/smt/Arms.java` `conjunct(DecisionRow)` 609–612 | 4 | `Arms.pathCondition` ← `Composer.java:542` |
| B | `SRC/d3/explore/FlipQuery.java` `Lowering.conjunct(DecisionRow,String)` 317–320 | 4 | internal to `FlipQuery` |
| C | `SRC/d3/explore/FlipQuery.java` inline, 679–680 | 2 | internal (`arm(ExportRow,…)`) |
| D | `SRC/runtime/d3/D3Runtime.java` `term(String,boolean)` 287–291 | 5 | `SessionPublisher` decision publishing |

B is self-refuting and I verified the text: its own javadoc at `FlipQuery.java:313–315` reads
*"`{@link Arms#conjunct}` owns the polarity and nothing here repeats it"*, and line 319 is
`return decision.outcome() ? term : "(not " + term + ")";` — the same expression as `Arms.java:611`.

**D2 — id minting: "lowercase hex SHA-256 truncated to 16". Four copies.**

| impl | location | lines | call sites |
|---|---|---:|---:|
| A | `SRC/d3/contract/Ids.java` `sha16` 25–39 | 15 | 5 (`OccurrenceAddress`, `ExecutionIndex` ×2, `Endpoint`, `Interaction`) |
| B | `SRC/d3/explore/ExploreIds.java` `sha16` 23–37 | 15 | 3 (`ClosurePlanner:105`, `Corpus:268`, `ObligationFactory:134`) |
| C | `SRC/d3/compose/JsonText.java` `digest`/`sha256` 97–113, 92–94 | 20 | 12 (`Composer` ×6, `SmtLowering` ×2, `ClaimPolicy` ×2, `CorpusIndex`, `SmtSymbolTable`) |
| D | `SRC/d3/smt/ArtifactIO.java` `sha256`+`hex` 213–215, 257–265 | 12 | 16 (`d3/plan/*`, `CanonicalJson`, `ConcolicRegionRuntime:2760,5052,7180`) |

A and B are the same algorithm (I diffed them: identical logic, formatting-only differences — B inlines
the digest call and spells `16` where A uses its `WIDTH` constant); `ExploreIds`'s javadoc admits the copy
(*"The contract's `Ids` is package-private, deliberately"*). The consequence is live, not cosmetic:
`CorpusIndex` (COMPOSE) mints a path id as `JsonText.digest(sessionId+"|"+occurrence.render(),16)`
(`CorpusIndex.java:55`) while `Corpus` (EXPLORE) mints **the same identity** as
`ExploreIds.sha16(sessionId+"|"+occurrence.id())` (`Corpus.java:268`) — one identity, two minters,
over two different renderings of the occurrence.

**D3 — slot replacement: "a consumer already paired with a different producer is a REPLACEMENT, not growth". Two whole classes named `SlotTable`, both reading `slots.jsonl`.**

| impl | file | lines | callers |
|---|---|---:|---|
| A (EXPLORE) | `SRC/d3/explore/SlotTable.java` (`take` 252–270, `reconcile` 155–228, `read` 111–119) | 379 | `ExploreMain:127,128,288,289`, `ExploreCodec:113,126,127` |
| B (COMPOSE) | `SRC/d3/compose/SlotTable.java` (`replacements` 159–178, `read` 62–83, `endpointId` 86–98) | 179 | `Composer:311,376,380,384` |

Both keep a consumer-endpoint → producer-endpoint map and compare `AttachRow.producer()` against it;
both emit the same refusal wording. B has no `STATE`-edge case, no `contextChanged`, no `unretained`:
it is a strict subset re-derivation.

**D4 — corpus index: "one iteration's sessions, indexed by contract identity". Two implementations of the same `Arms.Rows` interface.**

| impl | file | lines | caller files |
|---|---|---:|---:|
| A (COMPOSE) | `SRC/d3/compose/CorpusIndex.java` (`index` 171–309) | 630 | 3 |
| B (EXPLORE) | `SRC/d3/explore/Corpus.java` (`index` 160–234) | 599 | 6 |

Duplicated rule-for-rule, both bodies read: `varied(rootId)` (A 581–584 / B 544–552, same rule —
more than one distinct recorded value across sessions), `anyRoot` (A 568–572 / B 531–537),
`root(rootId,sessionId)` (A 558–566 / B 427–429), `seedSessionId`/`unfocusedSessionIds`, and a shared
surface of `attachesOf`, `exportsOf`, `writesOf`, `attachOfSymbol`, `occurrenceOf`, `activationOf`,
`seqOf`, `roots`, `pathIdOf`, `decisionsOf`, `sessionIds`, `expression`, `sessions`, `session`.

**D5–D9 — the SMT text layer is written twice, once for COMPOSE and once for EXPLORE.**

| rule | COMPOSE side | EXPLORE side |
|---|---|---|
| D5 n-ary `(and …)`/`(or …)` with empty/singleton collapse | `VmTermLowering.and/or/booleanNary` 373–398 (23 lines, 9 sites) | `SmtText.conjoin/disjoin` 175–200 (24 lines, 5 sites) |
| D6 Java primitive → `Bool`/`Int` sort | `JavaSmtSorts.sortOfJava` 21–51 (31 lines, 7 sites) + thin wrapper `SmtLowering.sortOf` 330–332 | `SmtText.sortOfJavaType` 159–172 (14 lines, 1 site) |
| D7 recorded decimal → SMT literal, negatives as `(- N)` | `JsonText.smtInteger`+`smtLiteral` 71–89 (17 lines, 4 sites) | `SmtText.literal` 126–145 (20 lines, 9 sites) |
| D8 name → SMT symbol (`[^A-Za-z0-9_]`→`_`, blank→`anonymous`) | `JsonText.smtName` 116–124 (1 site) | **`JavaSmtSorts.smtName` 77–85 — same package, same rule, 0 callers** (independently confirmed DEAD by the call graph) |
| D9 `predicate(term)` — a term states a predicate unless it is `""` or `"(not )"` | `Composer.predicate` 1009–1012 | `FlipQuery.predicate` 147–150 — byte-identical bodies, same comment |

**D10 — expression canonicalisation: "memoised per-node copy preserving sharing, object members in sorted name order". Two copies.**

`SRC/d3/smt/CanonicalJson.copy` 40–72 (33 lines; 4 callers: `BranchPredicateAlgebra:139`,
`SummaryBranchMapping:269`, `BranchReplayContract:573`, `ExactConcreteBranchObservation:163`)
versus `SRC/d3/plan/BranchPredicateAlgebra.canonicalCopy` 41–73 (33 lines, 3 internal callers) and
`canonicalView` 86–136 (51 lines). Same memo table, same `IdentityHashMap`, same
`Collections.sort(names)`. `BranchPredicateAlgebra.complement` (138–140) calls **`CanonicalJson.copy`
on the output of a walk built by its own copy** — the duplication is visible inside one expression.

**D11 — replay prefix admission: "the k-th observed decision at a site must match the recorded one; the first that does not is refused as *wrong decision at `<site>#<k>`*". Two implementations, one per replay entry point.**

| impl | location | lines | callers |
|---|---|---:|---|
| A (legacy) | `SRC/d3/plan/BranchReplayContract.java` `ReplayProgress.observeDecision` 737–794 (+`observeBinary` 715–726, `observeSwitch` 728–735) | 58 (+22) | `ConcolicRegionRuntime:5797–5806` → 7 sites in `ConcolicRegionRuntime` |
| B (D3) | `SRC/runtime/d3/FocusedReplay.java` `observe` 216–252 (+`observeDecision` 204–215, `Expected.is` 82–84) | 37 (+15) | `D3Runtime:275` |

Both emit the identical refusal prefix `"wrong decision at " + siteId + "#" + ordinal`.
This is the one duplicate where **the D3 side must survive** — `refactor/d3-runtime`'s commit
`a80606031` is titled *"P1: FocusedReplay is the only prefix matcher and the only forcing path"*,
and that branch already removes `ReplayProgress` from `ConcolicRegionRuntime`. A is the side to go;
it is the S1/S2 cascade in §4.

**D12 — JSON row accessors: "read a member, answer a stated absence rather than throw". Five copies.**

| impl | location | size | reach |
|---|---|---:|---|
| A (canonical) | `SRC/d3/smt/JsonFields.java` | 235-line file | 190 references in 55 files |
| B | `SRC/d3/compose/JsonText.java` 24–68 | 45 lines | 65 references, all in `d3/compose` |
| C | `SRC/d3/explore/ExploreCodec.java` 196–218 | 23 lines | 4 references, all in `d3/explore` |
| D | `SRC/d3/contract/RowCodec.java` 496–530 | 35 lines | private to `RowCodec` |
| E | `SRC/causynth/WireFlowCatalog.java` 136–154 | 19 lines | private to `WireFlowCatalog` |

`JsonText.object` (35–40) and `JsonFields.object` (55–59) are the same three-line rule;
`firstNonBlank` differs only in whether the result is trimmed.

### Pairs investigated and found NOT to be duplicates (negative results matter as much)

| pair | why not |
|---|---|
| `runtime/OccurrenceMinter` vs `runtime/d3/OccurrenceMinterV2` | Not two minters: `OccurrenceMinter.occurrenceId` (72–81) *delegates* to `OccurrenceMinterV2.mint`; the outer layer only adds duplicate detection and row stamping. One identity computation, two layers. |
| `runtime/d3/Identity` vs the minters | Orthogonal. `Identity` is a per-thread frame stack producing an `ExecutionIndex`, which is an **input** to `OccurrenceMinterV2.mint`. |
| `d3/contract/OccurrenceAddress` + `ExecutionIndex` vs the minters | These are the value types the minters return. `OccurrenceAddress.of/render/parse` is the single spelling both sides use. |
| `d3/compose/SmtLowering` vs `d3/compose/VmLoweringCore` | Inheritance, not duplication: `SmtLowering extends VmLoweringCore` (`SmtLowering.java:53`), `VmLoweringCore implements VmTermLowering.Policy` (`VmLoweringCore.java:61`). Template method with 13 abstract hooks. |
| `d3/compose/ContainerSmtCodec` vs the lowering core | Disjoint. `ContainerSmtCodec` is the only emitter of `(select`/`(store` and the container `(ite` cascades (48 SMT-operator hits); `VmLoweringCore` has 1 and delegates via the abstract `containerTerm`. No second container lowering exists. |
| `d3/smt/JavaPrimitiveSmtSemantics`, `JavaContainerTypes`, `JavaPrimitiveBoxing`, `VmExpressionIr` | Each is the sole owner of its vocabulary and the others call it rather than re-derive it (e.g. `JavaSmtSorts.containerSort` → `JavaContainerTypes.shape`; `RuntimeRegionPlanner.java:1519` → `JavaPrimitiveSmtSemantics.referenceIdentityCarrier`). |
| `CfgLoopControl` / `DeclaredLoopBodyBounds` / `LoopBoundPolicy` / `BoundedLoopComposition` | Four **stages** of one mechanism, not four mechanisms: CFG backedge analysis → declared-`K_L` reader (which calls `LoopBoundPolicy.bodyBound:289` / `loopSiteId:313` instead of re-parsing) → field vocabulary → per-path validation. No second bound parser and no second loop-site id. (`BoundedLoopComposition` is nonetheless dead — §1 — because the last stage is no longer invoked.) |
| `RuntimeSelectedRegionFinalizer` / `RuntimeRegionPlanner` / `SymbolicRegionPlanner` / `ConcolicInstrumentationSelections` | Sequential pipeline stages with near-disjoint method surfaces (~80 methods each, ~4 shared names, and those delegate): static skeleton → bind skeletons to recorded activations → build executable region state. |
| `runtime/PathConditionWindow` vs the `ConcolicRegionRuntime` branch hooks | Already deduplicated — `PathConditionWindow.forEvent` (126–142) carries the comment *"Both branch hooks used to spell this out themselves."* |
| `d3/plan` branch shape vs `d3/contract` row shape | **Cleanly stage-partitioned, not a duplicate record shape.** The `d3/plan` shape (`BranchWitness`, `SummaryBranchMapping`, `ExactConcreteBranchObservation`, `BranchReplayContract`, `PathObservation`, `SolverPathContext`, `LocalCaseIdentity`) is read only by PLAN/REPLAY (`ConcolicScheduler`, `ExecutionTask`, `CommunicationCatalogPlanner`, `ConcolicRegionRuntime`, `ConcolicTaskPlan`, `RuntimeRegionPlanner`). `DecisionRow`/`PathEntry`/`Selector` are read only by IMPORT→EXPLORE→COMPOSE→SOLVE (`runtime/d3/*`, `RowCodec`, `SessionReader`, `d3/explore/*`, `d3/compose/*`, `Arms`). No stage reads both. What *is* duplicated across the two shapes is exactly D1 (polarity) and D11 (prefix match). This is corroborated by the reachability table: every `d3/contract` row type is reached from `COMPOSE,EXPLORE,OBLIG` (+`HDFS-CRR`,`REPLAY`), and none from `PLAN` except `Selector`. |
| `d3/contract/Fields` vs `d3/smt/JsonFields` | Different jobs despite the names: `Fields` validates **Java values** for immutable record constructors; `JsonFields` reads **Gson members**. Only `text(String)` overlaps. |
| `CanonicalJson.sha256` vs `ArtifactIO.sha256` | A two-line delegation, not a second implementation. |
| hand-rolled JSON writers in the six big files | None. Grep for `append("{")`, `append("[")`, `append("\"")` across the whole tree: **zero** hits. All JSON writing goes through Gson or `CanonicalJson.render`. |

---

## 3. `run_engine.sh` — 3,014 lines, 90 functions

Definitions found with `grep -nE '^[A-Za-z_][A-Za-z0-9_]*\(\) \{$'` (89 top-level; there are **no**
`function name` definitions) plus one nested (`restore_skeleton_classes`, 661–664, called by the
`trap … EXIT` at 665). End lines by brace matching; call sites by `grep -nw`, excluding comment-only
mentions. External consumers checked: `tools/*.sh`, `experiments/**` (which only `exec` the script),
and the 749-line contract test `src/test/shell/run_engine_campaign_helpers_test.sh`, which sources it
through the guard at 2972–2975. **No external file calls any internal function.**
Total function-body lines: 2,484 (82 % of the file).

### 3a. Functions with no caller

| function | lines | evidence |
|---|---|---|
| `campaign_json` | **1038–1152, 115 lines** | The only zero-caller function in the file. `grep -n campaign_json run_engine.sh` returns exactly two lines — the definition (1038) and a `sys.exit("unknown campaign_json mode " + mode)` **inside its own heredoc** (1150); every other hit is the unrelated `campaign_json_file` (2361–2365, 5 call sites), which is a `printf > destination` helper and does not call it. No indirect dispatch: `campaign_stage` (1023–1033) runs `"$@"`, and all 14 call sites pass literal function names, none of them `campaign_json`. The shell contract test never mentions it. Its body is a `python3` heredoc whose `DELTA_KINDS` tuple (1045–1046) is `NEW_LOCAL_CASE, NEW_EFFECT, NEW_OCCURRENCE, NEW_CAUSAL_BINDING, TOPOLOGY_DIVERGENCE, COVERAGE_GAP`, and it is **the script's only use of `python3`** (1039). |

Seven functions are mentioned once in prose but do have real call sites and are **not** dead:
`campaign_checkout_state` (comment 1447), `campaign_obligation_worker` (1740), `do_schedule` (2800),
`campaign_write_gaps` (2617), `validate_config` (557), `require_nonempty` (2031), `die` (499).

### 3b. Stage code referencing artifacts no stage writes

The brief's four named suspects are, measured, **not present** — do not spend the deletion pass on them:

| token | shell | Java | verdict |
|---|---|---|---|
| `z3-result.json` | 0 hits | 0 hits (`z3-result`, `z3_result`, `Z3Result`) | **Does not exist.** Every `z3` in the shell is the *executable* config key (82, 289, 307, 396, 599, 1920). The reason there is no solver artifact is that **SOLVE runs no solver**: `campaign_solve` (2246–2260) only re-reads `.solver.state` / `.solver.reachability` / `.solver.valuations` out of `candidate_composition_manifest.json`, which `ComposeMain` already wrote. |
| `reach` as an artifact | no file/dir named `reach*` | — | **Does not exist.** All hits are prose, jq selectors (`.targetReachGoal`, `.solver.reachability`), or JSON string constants (`ITERATION_BOUND_REACHED`, `TARGET_REACH_CLOSURE`). One genuine dead item, below. |
| `sym__` | 0 hits | 1 hit, `ConcolicRegionRuntime.java:1721` | **Not in the shell.** Its only symbolic-model reader, `campaign_print_symbolic_variable_models` (798–836), addresses models by structured jq fields (`.inputKind`, `.sourceKey`, `.sourceId`, `.sourcePhaseId`, `.fieldSignature`, `.occurrenceId`, `.portId`, `.sourceIdentity*`), never by symbol prefix. |
| request families | 2 hits, **both comments** (2000, 2894); `request-family`/`requestFamily`/`request_family` = 0 | `RuntimeTraceContext.java:121–124` builds a local `requestFamily` map key that is never serialised | **No request-family addressing in the shell at all.** |
| `VALIDATE` | 1 hit, line 2853 `campaign_stage VALIDATE campaign_validate` — **live** | 3 javadoc mentions (`ComposeMain:40`, `ClaimPolicy:21`, `CompositionManifest:12`) all asserting the pipeline stage is gone | **Naming collision, not a stale stage.** `campaign_validate` (1250–1258) is a pre-flight config check (`validate_config` + three `require_command_available`) that runs before FREEZE_TOOL. It writes the label `VALIDATE` into `stage_metrics.tsv`. Rename it (`PREFLIGHT`) rather than delete it; the owner ruling "no VALIDATE stage" is about the *pipeline* stage, and that one genuinely does not exist. |

The real orphans are different, and two of them are live failures:

**`concolic_region_summaries.jsonl` — read three times, written nowhere. This is a hard failure, not a no-op.**
Read at 2165–2166, 2168, 2178 inside `campaign_publish_iteration_manifest` (2130–2198), called from
`do_campaign` at line **2889** — right after EXPLORE, before COMPOSE. I re-ran the search myself:
`grep -rn concolic_region_summaries` over the whole worktree (excluding `third_party`) returns those
three shell lines and **nothing else** — no Java writer, no `region_summaries`/`regionSummaries`
anywhere in `src/main/java`, and no shell write primitive (`>`, `>>`, `tee`, `cp`, `mv`, `mkdir`,
`--output`, `--manifest`, …) names it. Because `campaign_digest` (753–756) is
`[[ -f "$1" ]] || die "cannot digest a missing artifact"`, line 2165 always fails and
`campaign_fail EMIT … "failed to digest the imported summaries"` (2167–2169) always fires.
Contrast the siblings that *are* written: `concolic_region_results.jsonl` (replay JVM via
`CAUSYNTH_CONCOLIC_RESULTS`, set at 1766) and `obligation_results.jsonl` (created 1992, appended 2101).
`git log -S concolic_region_summaries -- run_engine.sh` points at `058ee2491`
*"M5: run_engine.sh reduced to the Design 3 stages"* as the commit that last changed its count.

**`campaign_gaps.jsonl` — written, then silently truncated before it is read.**
`campaign_collect_diagnostics` (2114–2128) runs
`find "${iteration_dir}" -type f -name 'campaign_gaps.jsonl' -not -path "${gaps}"` (2119–2121)
where `${gaps}` *is* `${iteration_dir}/campaign_gaps.jsonl` (2116) — the only file that can match
`-name` is the one excluded by `-not -path`, and no nested writer exists anywhere. So `gap_list` is
always empty, lines 2125 and 2127 never run, and the function's only effect is line **2126**,
`: >"${gaps}"`. That discards the `GAP_ROW` `campaign_explore` wrote at 2064–2070 (collector called
one line later, 2888) and the `TOPOLOGY_DIVERGENCE` row `campaign_publish_pending_refinement` wrote
at 2734–2740 (collector called at 2741). EMIT's `campaign_write_gaps` then reads an always-empty
file at 2391–2392.

**A dead loop variable:** `campaign_decode_index_members` (1160–1199) emits a 7-column TSV whose 7th
column is `.targetReachGoal` (1194–1195). Both consumers read it into `target_reach` and never use it
(`grep -nw target_reach` → exactly 1695 and 2139, zero uses), and it is missing from both `local`
declarations (1623, 2135), so it leaks globally. The Java producer is live
(`RuntimeWorkflowDiscovery.java:567`); only the shell consumer is dead.

**A stale config comment:** the block at 99–102 documents a replay-task-count key that was deleted;
it now sits above `solver_timeout_ms` (103), which it does not describe. All 43 declared config keys
(49–117) are otherwise referenced.

### 3c. Unreachable stage blocks

| # | range | lines | why unreachable |
|---|---|---:|---|
| DEAD-1 | 1038–1152 | 115 | `campaign_json`, no caller (above). |
| DEAD-2 | 2950–2966 (and by extension the whole `iteration >= 1` body, 2862–2966) | 17 (+105) | `campaign_seeding_results` (2801–2807) returns a session **directory** (`${iteration_dir}/sessions/${session}`, 2806); `do_campaign` assigns it to `carry` (2964); `campaign_plan` forwards it as `schedule_summaries` (1631) to `do_schedule`, which does `require_file` on it (566–567) — `[[ -f dir ]]` is false → `die` (339–341). The Java side agrees it is the wrong *kind*: `ConcolicScheduler.java:117–120` does `ArtifactIO.readJsonl(arguments.summaries)`, one JSONL file. The script's own comment at 2799–2800 states the mismatch. **Every epoch after the first dies at line 567.** |
| DEAD-3 | 2706–2725 + call site 2968 | 20 | `campaign_publish_bound_gap`. The loop `return 0`s at 2957–2960 whenever `iteration+1 >= campaign_max_epochs`, and `campaign_max_epochs=3` is **hardcoded at 2828** — not a `workflow_config_keys` row (49–117), no env override (`grep -nw` → 2828, 2957, 2959 only). So `iteration` never exceeds 2 and 2968 needs `campaign_max_iterations <= 2`; all four shipped configs set it to 3 (`hdfs-17897:38`, `hdfs-17899:19`, `hdfs-17960:28`, `hdfs-11741:29`). The body is doubly stale: it emits `byStage: {CLASSIFY: 1}` (2714) and `stage: "CLASSIFY"` (2719) for a **deleted stage** (`a03ad313b` *"Delete SEED_QUERY and CLASSIFY"*), and writes `>"${campaign_final}/gaps.json"` (2723), which would clobber the real gap report EMIT published at 2512. |
| DEAD-4 | 2125, 2127 | 2 | `campaign_collect_diagnostics`' find can never match (above). |
| DEAD-5 | 2945–2949 | 5 | Both disjuncts are always false: `-z "${seeding_results}"` is covered by the earlier `return 0` at 2940–2943, and `! -s` is false for an existing directory (2806). |
| DEAD-6 | 2882–2885 | 4 | `CAUSYNTH_CAMPAIGN_STOP_AFTER == IMPORT`. Not a `workflow_config_keys` row (`grep -nw` → only 2882), no experiment exports it. Reachable only by a hand-typed `env`. Also the file's only bare-string stage comparison. |
| DEAD-7 | — | — | Not dead code but a wrong label: `campaign_fail CACHE` (926, 934, 939, 944, 948, 953) names a stage the pipeline does not have, while **no** `campaign_fail INSTRUMENT` and **no** `campaign_fail DECIDE` exist — two of the nine stages can never name themselves in a failure. `campaign_fail EMIT` at 2122 fires from `campaign_collect_diagnostics`, which runs at EXPLORE time (2888) and pending-refinement time (2741), never during EMIT. |

Shell total, mechanically safe: **115 lines** (DEAD-1) plus **31** (DEAD-3 body + call site, DEAD-4,
DEAD-5, DEAD-6) = **146 lines**. DEAD-2 is 17–122 more, but it is a **bug to fix, not code to delete**:
the epoch loop is supposed to work, and it has been dead since `058ee2491`.

---

## 4. Ranked deletion plan

### 4a. Who owns what right now (measured, not assumed)

The brief's avoid list is **incomplete**. Diffing `refactor/d3-runtime` (`13243bacd`) against its
merge-base with staging (`30f479bae`), the runtime agent is editing **13 files**:

| file | ± | on the brief's avoid list? |
|---|---|---|
| `runtime/ConcolicRegionRuntime.java` | 152 | yes |
| `runtime/D3RowPublication.java` | 331 | yes |
| `runtime/RuntimeTraceContext.java` | 32 | yes |
| `runtime/CausynthTraceRecorder.java` | 68 | yes |
| `runtime/d3/D3Runtime.java`, `FocusedReplay.java`, `Identity.java`, `Lineage.java`, `OccurrenceMinterV2.java` | 79/56/54/51/10 | yes (`runtime/d3/*`) |
| **`runtime/ConcolicTaskPlan.java`** | 54 | **no — add it** |
| **`causynth/WireFlowCatalog.java`** | 10 | **no — add it** |
| `runtime/BranchDecisionRecordingTest.java`, `runtime/D3RuntimeTest.java` | 4/9 | tests |

Four files inside the avoid zone are **not** touched by that branch and are therefore zero-conflict
if the planner lifts the zone per file: `runtime/d3/Interactions.java`,
`runtime/d3/SessionPublisher.java`, `runtime/d3/Selectors.java`, `runtime/d3/Text.java`.
No other in-flight branch (`refactor/d3-compose2`, `d3-contract`, `d3-harness`, `d3-contract-pkg`)
is ahead of staging in `src/main`.

### 4b. Ranked plan

Line figures: **file lines** where a whole file goes (`wc -l`), **body lines** where methods go
(compiler line table — a lower bound; actual removal runs ≈ 1.5–2 × once signatures, javadoc and
blank lines follow).

| # | delete | measured | touches a runtime-agent file? | precondition |
|---:|---|---:|---|---|
| **1** | `run_engine.sh` `campaign_json` (1038–1152) | **115 file lines** + drops the script's only `python3` dependency | no | none — zero callers |
| **2** | `d3/plan/BoundedLoopComposition.java`; move `PLAN_FIELD` + `LOOP_BODY_BOUND_DISAGREES` to `LoopBoundPolicy`; drop unused imports in `CommunicationCatalogPlanner:5`, `GapLedger:5` | **−512 / +~6 ⇒ ≈ −505** | no | none — all 14 methods unreachable |
| **3** | `d3/plan/PathObservation.java` minus `TargetReachEvent` (lift 132–~260 into its own file) **+** `d3/plan/LocalCaseIdentity.java` | **≈ −250 and −248 ⇒ ≈ −498** | no | none — `LocalCaseIdentity`'s only reader is the dead half of `PathObservation`; no test touches either |
| **4** | `d3/plan/SymbolicPropagationClosure.java` | **−106** | **1 import line in `ConcolicRegionRuntime.java:24`** (plus `GapLedger.java:3`) | coordinate the 1-line import removal, or the tree will not compile |
| **5** | `run_engine.sh` DEAD-3 (2706–2725 + 2968), DEAD-4 (2125, 2127), DEAD-5 (2945–2949), DEAD-6 (2882–2885) | **31 file lines** | no | DEAD-4 must be *fixed*, not just trimmed — line 2126 is silently discarding gap rows (see §3c) |
| **6** | Dead-method sweep in the 57 remaining files outside the runtime agent's set (after #2–#4) | **963 body lines / 212 methods** → ≈ 1,400–1,900 file lines | no | none; largest single files: `SharedStateEvidence` 91, `SymbolicSourceEvidence` 91, `VmExpressionIr` 81, `ContainerSmtCodec` 63, `FlipQuery` 56, `SmtModelValueCodec` 51, `BranchPredicateAlgebra` 38, `ArtifactIO` 35 |
| **7** | Duplicate consolidation, the strictly-subsumed side only (§2b ranks 1–8): `JavaSmtSorts.smtName` (9, zero callers), `FlipQuery.conjunct` + inline copy (6), one of the two `predicate` (4), `ExploreIds` (38), `BranchPredicateAlgebra.canonicalCopy` (33), `SmtText.sortOfJavaType` (14), `SmtText.conjoin/disjoin` (26), one of the two SMT-literal renderers (19) | **≈ 149 file lines** | no | `Ids` is package-private in `d3/contract` — widening it is the only blocker for the `ExploreIds` half |
| | **subtotal, no design decision and no blocked file** | **≈ 3,200–3,700 file lines (4–5 % of `src/main`)** | | |
| **8** | *(waits on `refactor/d3-runtime` landing)* `BranchReplayContract` methods orphaned by the `ReplayProgress` cut | **131 body lines** | yes | merge `refactor/d3-runtime` |
| **9** | *(waits on the same)* dead methods inside runtime-agent files: `FocusedReplay` 37, `ConcolicTaskPlan` 25, `D3Runtime` 24, `SessionPublisher` 16, `Interactions` 10, `Lineage` 8, others 31 | **151 body lines**; plus **`runtime/d3/Selectors.java` entire, 86 file lines** (untouched by that branch — could go now if the zone is lifted) | yes | merge, or a per-file zone lift for `Selectors` |
| **10** | *(design decision — scenario **S2**)* stop the PLAN stage reading the branch-record cluster: drop `ConcolicScheduler.branchQuery`, `directConcreteTarget`, `latestTargetSeedDecision`, `ExecutionTask.replaySchedule`, `CommunicationCatalogPlanner.catalogLoops`, `RuntimeRegionPlanner.addExactSwitchDecision` | **1,140 body lines**, and four files go whole: `BranchReplayContract` (977), `SummaryBranchMapping` (338), `SolverPathContext` (286), `PathObservation` (406, already in #3) ⇒ **≈ 1,600 file lines + ~410 body lines** of partial cuts | `RuntimeRegionPlanner` is *not* on the avoid list and is not being edited — safe | **planner ruling required.** This is the change the brief attributed to the runtime agent; it is not one. Measured cascade also hits `CommunicationCatalogPlanner` 109, `ConcolicScheduler` 107, `ExactConcreteBranchObservation` 59, `DeclaredLoopBodyBounds` 36, `BranchWitness` 29, `RuntimeRegionPlanner` 25 body lines |
| **11** | *(design decision)* duplicate consolidation, the structural pairs (§2b ranks 9–14): merge `d3/compose/SlotTable` into `d3/explore/SlotTable` (−179), `JsonText`/`ExploreCodec`/`WireFlowCatalog` accessors into `JsonFields` (−87), merge `CorpusIndex` into `Corpus` (−630) | **≈ 896 file lines** | `WireFlowCatalog` **is** being edited — defer that 19-line piece | one owner per rule; `CorpusIndex`/`Corpus` is the largest single win and the highest risk |
| **12** | *(bug, not a deletion)* `concolic_region_summaries.jsonl` has no writer — `campaign_fail EMIT` at 2167 fires unconditionally; and `campaign_seeding_results` hands a **directory** to `do_schedule --summaries`, killing every epoch after the first (DEAD-2) | — | no | fix before measuring anything downstream of iteration 0 |

### 4c. What the whole pass is worth, and what it is not

| tranche | measured |
|---|---:|
| available now, no design decision, no blocked file (#1–#7) | **≈ 3,200–3,700 file lines** |
| after `refactor/d3-runtime` lands (#8–#9) | + ≈ 400–500 |
| after the PLAN-stage ruling (#10) | + ≈ 2,000 |
| after duplicate consolidation (#11) | + ≈ 900 |
| **total reachable by this plan** | **≈ 6,500–7,100 lines, ≈ 9 % of `src/main`** |

Two sizes that are *not* in that total, because they are design rulings the planner owns and this
audit has no evidence for:

- **The six big files stay big.** 26,092 lines, 1,469 methods, **16 unreachable**. Their per-file
  deletion cascades (`own + everything that dies with them`) are measured in Appendix B —
  `ConcolicRegionRuntime` 4,717 body lines, `CausynthPipeline` 5,882, `ConcolicScheduler` 2,782,
  `RuntimeSelectedRegionFinalizer` 2,749 — but every one of those cascades requires deleting the
  stage itself, not dead code.
- **`RuntimeRefinedGraphBuilder` (1,202 lines) is the one file whose *purpose* the core design
  principle argues against** — the graph is meant to decide what to track, never to reconstruct
  values. It is live from exactly two call sites (`CausynthTraceRecorder.aggregateStateTrace`,
  `RuntimeRegionPlanner.deepCopyValue`), and its own cascade is 650 body lines with almost nothing
  downstream (3 lines). That makes it a clean excision **if** the planner rules the mechanism out.
  This audit records the measurement, not the ruling.

### 4d. Do not delete these (traps re-verified this round)

1. **`d3/plan/StaticSymbolicSourceDeclaration.java` (19 lines) reads as dead in bytecode and is not.**
   `javac` inlined its four constants into `ConcolicScheduler:2612,2780,2781,2783` and
   `StaticSymbolicSourceDiscovery:128,165`. Same shape as the `symbolizeConfiguredSourceField`
   incident. Grep the *string spellings*, not the symbol.
2. **`BoundedLoopComposition`'s constants** (same reason) — 2 of them survive the file.
3. **The 25 out-of-repo ABI symbols** (§0) — four of them (`beginDaemonTick`, `endDaemonTick`,
   `enterCarriedScope`, `exitCarriedScope`) are not in the external-callers memory yet; update it.
   Four more (`pauseObservation`, `resumeObservation`, and the 5-arg `outboundExchange`) are bound
   **reflectively by Solr and fail soft** — a green campaign is not evidence they survived.
4. **`FocusedReplay.resetForTests` / `loadForTests`, `D3Runtime.resetForTests`** read DEAD here only
   because tests are not entry points; the tests call them. Delete the pair together or not at all.
5. **`campaign_validate` / the `VALIDATE` label** is a live pre-flight config check, not the deleted
   pipeline stage. Rename, do not delete.

---

## Appendix A — complete per-method tables for the six largest files

All 1,469 methods, in source order. `callers` lists callers outside the file (`EXT:`) and inside it (`in:`). Machine-readable copy with descriptors, stage attribution and per-method cascade: `$SPN/d-refactor/REPORT-SHRINK-methods.tsv`.

#### `runtime.ConcolicRegionRuntime` — all 447 methods

| method | lines | body | callers | verdict |
|---|---|---:|---|---|
| `ConcolicRegionRuntime.access$4200` | 104-104 | 1 | in:signature | LIVE |
| `ConcolicRegionRuntime.access$8300` | 104-104 | 1 | in:recordPaused | LIVE |
| `ConcolicRegionRuntime.access$8400` | 104-104 | 1 | in:recordPaused | LIVE |
| `ConcolicRegionRuntime.access$8500` | 104-104 | 1 | in:<init> | LIVE |
| `ConcolicRegionRuntime.access$9100` | 104-104 | 1 | in:recordDecisionRow | LIVE |
| `ConcolicRegionRuntime.access$9500` | 104-104 | 1 | in:evidenceSnapshot | LIVE |
| `ConcolicRegionRuntime.access$9600` | 104-104 | 1 | in:matchesField | LIVE |
| `ConcolicRegionRuntime.access$9700` | 104-104 | 1 | in:matchesField | LIVE |
| `ConcolicRegionRuntime.access$9800` | 104-104 | 1 | in:matchesField | LIVE |
| `ConcolicRegionRuntime.access$9900` | 104-104 | 1 | in:referenceValue | LIVE |
| `ConcolicRegionRuntime.<clinit>` | 113-230 | 17 | none | LIVE |
| `ConcolicRegionRuntime$1.<init>` | 190-190 | 1 | in:<clinit> | LIVE |
| `ConcolicRegionRuntime$1.initialValue` | 190-190 | 1 | none | LIVE |
| `ConcolicRegionRuntime$1.initialValue` | 193-193 | 1 | in:initialValue | LIVE |
| `ConcolicRegionRuntime.lambda$static$0` | 197-197 | 1 | in:<clinit> | LIVE |
| `ConcolicRegionRuntime$2.<init>` | 203-203 | 1 | in:<clinit> | LIVE |
| `ConcolicRegionRuntime$2.initialValue` | 203-203 | 1 | none | LIVE |
| `ConcolicRegionRuntime$2.initialValue` | 206-206 | 1 | in:initialValue | LIVE |
| `ConcolicRegionRuntime$3.<init>` | 212-212 | 1 | in:<clinit> | LIVE |
| `ConcolicRegionRuntime$3.initialValue` | 212-212 | 1 | none | LIVE |
| `ConcolicRegionRuntime$3.initialValue` | 215-215 | 1 | in:initialValue | LIVE |
| `ConcolicRegionRuntime.<init>` | 232-233 | 2 | none | DEAD |
| `ConcolicRegionRuntime.pauseObservation` | 242-248 | 5 | in:beginBookkeeping | LIVE |
| `ConcolicRegionRuntime.resumeObservation` | 252-260 | 7 | in:endBookkeeping | LIVE |
| `ConcolicRegionRuntime.enterConfiguredSourcePhaseCallSite` | 268-275 | 6 | none | LIVE |
| `ConcolicRegionRuntime.exitConfiguredSourcePhaseCallSite` | 282-290 | 6 | none | LIVE |
| `ConcolicRegionRuntime.throwConfiguredSourcePhaseCallSite` | 294-300 | 5 | none | LIVE |
| `ConcolicRegionRuntime.beginBookkeeping` | 313-314 | 2 | in:attachCommunicationLeaf,attachDeclaredCommunicationExpression,completeLoopCardinality+14 | LIVE |
| `ConcolicRegionRuntime.endBookkeeping` | 318-319 | 2 | in:attachCommunicationLeaf,attachDeclaredCommunicationExpression,completeLoopCardinality+14 | LIVE |
| `ConcolicRegionRuntime.observingActiveRegion` | 326-326 | 1 | in:checkLoopBackedge,checkReplayLoopBody,completeLoopCardinality+1 | LIVE |
| `ConcolicRegionRuntime.checkLoopBackedge` | 338-373 | 24 | none | LIVE |
| `ConcolicRegionRuntime.checkReplayLoopBody` | 381-410 | 21 | none | LIVE |
| `ConcolicRegionRuntime.recordLoopCardinality` | 418-426 | 7 | none | LIVE |
| `ConcolicRegionRuntime.completeLoopCardinality` | 430-438 | 7 | none | LIVE |
| `ConcolicRegionRuntime.resumeLoopAccounting` | 446-453 | 7 | in:checkLoopBackedge,checkReplayLoopBody | LIVE |
| `ConcolicRegionRuntime.endAtCut` | 459-462 | 4 | in:checkLoopBackedge,checkReplayLoopBody | LIVE |
| `ConcolicRegionRuntime.enterAccessorCallContext` | 474-506 | 26 | none | LIVE |
| `ConcolicRegionRuntime.exitAccessorCallContext` | 512-538 | 19 | none | LIVE |
| `ConcolicRegionRuntime.openWorkloadSession` | 552-573 | 18 | EXT:JUnitMethodRunner.main | LIVE |
| `ConcolicRegionRuntime.closeWorkloadSession` | 585-607 | 18 | EXT:JUnitMethodRunner.reportWorkloadSessionClose | LIVE |
| `ConcolicRegionRuntime.awaitSelectedResultPublications` | 621-622 | 2 | in:closeWorkloadSession | LIVE |
| `ConcolicRegionRuntime.workloadSessionStatusName` | 625-630 | 6 | in:closeWorkloadSession,openWorkloadSession | LIVE |
| `ConcolicRegionRuntime.admitRegion` | 642-655 | 8 | in:enterRegionFrame | LIVE |
| `ConcolicRegionRuntime.selectTask` | 673-679 | 4 | in:admitRegion | LIVE |
| `ConcolicRegionRuntime.boundedLoopOccurrenceCut` | 693-710 | 10 | in:admitRegion | LIVE |
| `ConcolicRegionRuntime.startSymbolicRegion` | 716-816 | 71 | in:admitRegion | LIVE |
| `ConcolicRegionRuntime.prepare` | 822-826 | 5 | in:startSymbolicRegion | LIVE |
| `ConcolicRegionRuntime.enterRegionFrame` | 836-861 | 16 | none | LIVE |
| `ConcolicRegionRuntime.enterLoopRootInvocationFrame` | 872-889 | 12 | none | LIVE |
| `ConcolicRegionRuntime.exitLoopRootInvocationFrame` | 894-905 | 10 | in:throwLoopRootInvocationFrame | LIVE |
| `ConcolicRegionRuntime.throwLoopRootInvocationFrame` | 910-911 | 2 | none | LIVE |
| `ConcolicRegionRuntime.enclosingLoopRootAdmits` | 915-915 | 1 | EXT:ConcolicTaskPlan.select | LIVE |
| `ConcolicRegionRuntime.enclosingLoopRoot` | 929-938 | 6 | in:enclosingLoopRootAdmits,startSymbolicRegion | LIVE |
| `ConcolicRegionRuntime.sameHookIdentity` | 943-943 | 1 | EXT:ConcolicTaskPlan.loopRootHookGroup,ConcolicTaskPlan.rootHookGroup; in:popRootInvocationFrame | LIVE |
| `ConcolicRegionRuntime.symbolizeArgument` | 952-991 | 27 | none | LIVE |
| `ConcolicRegionRuntime.symbolizeMethodArgument` | 998-1016 | 16 | none | LIVE |
| `ConcolicRegionRuntime.materializeArgument` | 1028-1061 | 24 | none | LIVE |
| `ConcolicRegionRuntime.materializeMethodArgument` | 1069-1093 | 17 | none | LIVE |
| `ConcolicRegionRuntime.materializeReference` | 1099-1137 | 26 | none | LIVE |
| `ConcolicRegionRuntime.materializePrimitive` | 1148-1164 | 12 | none | LIVE |
| `ConcolicRegionRuntime.explicitFaultCandidates` | 1188-1199 | 11 | in:materializeSymbolicBoolean | LIVE |
| `ConcolicRegionRuntime.recordedFaultPolarity` | 1258-1262 | 5 | in:materializeSymbolicBoolean | LIVE |
| `ConcolicRegionRuntime.declaresExplicitFault` | 1268-1276 | 8 | in:materializeSymbolicBoolean | LIVE |
| `ConcolicRegionRuntime.materializeSymbolicBoolean` | 1281-1332 | 28 | EXT:Debug.makeSymbolicBoolean | LIVE |
| `ConcolicRegionRuntime.materializeStaticPrimitiveField` | 1342-1370 | 20 | none | LIVE |
| `ConcolicRegionRuntime.materializeField` | 1378-1476 | 66 | none | LIVE |
| `ConcolicRegionRuntime.materializeAssociativeRead` | 1481-1521 | 29 | none | LIVE |
| `ConcolicRegionRuntime.armGuardedRead` | 1526-1546 | 11 | in:materializeField | LIVE |
| `ConcolicRegionRuntime$ConsumerAccessAnchor.<init>` | 1562-1565 | 4 | in:consumerAccessAnchor | LIVE |
| `ConcolicRegionRuntime.consumerAccessAnchor` | 1572-1585 | 8 | in:materializeField | LIVE |
| `ConcolicRegionRuntime.observeCausalSource` | 1591-1596 | 5 | EXT:RuntimeTraceContext.publishCausalSource; in:startSymbolicRegion | LIVE |
| `ConcolicRegionRuntime$SourceSiteEntry.<init>` | 1613-1613 | 1 | in:observeConfiguredSourceEntry | LIVE |
| `ConcolicRegionRuntime$SourceSiteEntry.access$2700` | 1613-1613 | 1 | in:symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime$SourceSiteEntry.access$2800` | 1613-1613 | 1 | in:recordConfiguredSourceMint,symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime$SourceSiteEntry.access$3000` | 1613-1613 | 1 | in:recordConfiguredSourceMint,symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime$SourceSiteEntry.access$9400` | 1613-1613 | 1 | in:recordConfiguredSourceMint | LIVE |
| `ConcolicRegionRuntime$SourceSiteEntry.<init>` | 1619-1623 | 5 | in:<init> | LIVE |
| `ConcolicRegionRuntime$SourceSiteEntry.phaseId` | 1626-1626 | 1 | in:access$2800 | LIVE |
| `ConcolicRegionRuntime$SourceSiteEntry.key` | 1631-1631 | 1 | in:access$2700 | LIVE |
| `ConcolicRegionRuntime.symbolizeConfiguredSourceField` | 1650-1788 | 73 | none | LIVE |
| `ConcolicRegionRuntime.describeReadBack` | 1800-1808 | 8 | in:symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime$PropagatedExpressionImportFailure.<init>` | 1848-1849 | 2 | in:engineExpression | LIVE |
| `ConcolicRegionRuntime.engineExpression` | 1854-1870 | 10 | in:materializeField,mintAmbientHandoffLeaves,mintHandoffLeaf+6 | LIVE |
| `ConcolicRegionRuntime.refuseImportedExpression` | 1886-1892 | 7 | in:materializeField,materializePrimitiveValue,symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime.describeImportPayload` | 1896-1899 | 4 | in:engineExpression | LIVE |
| `ConcolicRegionRuntime.decodeVmEnvelope` | 1905-1908 | 2 | EXT:SharedStateCapture.decodeTrackedLocations | LIVE |
| `ConcolicRegionRuntime$HandoffResult.<init>` | 1912-1912 | 1 | in:attach,exportLeaf,failed | LIVE |
| `ConcolicRegionRuntime$HandoffResult.access$3400` | 1912-1912 | 1 | in:exportCommunicationLeaf | LIVE |
| `ConcolicRegionRuntime$HandoffResult.access$3500` | 1912-1912 | 1 | in:exportCommunicationLeaf | LIVE |
| `ConcolicRegionRuntime$HandoffResult.access$3600` | 1912-1912 | 1 | in:exportCommunicationLeaf,recordVmHandoffEvent | LIVE |
| `ConcolicRegionRuntime$HandoffResult.<init>` | 1920-1925 | 6 | in:<init> | LIVE |
| `ConcolicRegionRuntime$HandoffResult.ok` | 1928-1928 | 1 | in:toString,attachDeclaredCommunicationExpression,exportCommunicationLeaf+2 | LIVE |
| `ConcolicRegionRuntime$HandoffResult.reason` | 1933-1933 | 1 | in:toString | LIVE |
| `ConcolicRegionRuntime$HandoffResult.handle` | 1937-1937 | 1 | in:access$3500 | LIVE |
| `ConcolicRegionRuntime$HandoffResult.toString` | 1948-1949 | 2 | in:record | LIVE |
| `ConcolicRegionRuntime.exportSymbolicLeaf` | 1958-1964 | 5 | in:exportCommunicationLeaf | LIVE |
| `ConcolicRegionRuntime.exportLeaf` | 1970-2005 | 20 | in:exportSymbolicLeaf | LIVE |
| `ConcolicRegionRuntime.attachDeclaredCommunicationExpression` | 2016-2028 | 10 | in:attachDeliveredLeaf | LIVE |
| `ConcolicRegionRuntime$HandoffLeafCarrier.<init>` | 2032-2032 | 1 | none | DEAD |
| `ConcolicRegionRuntime.stageMessageExpression` | 2054-2070 | 7 | in:exportCommunicationLeaf | LIVE |
| `ConcolicRegionRuntime.plannedExportConsumers` | 2084-2091 | 8 | in:stageMessageExpression | LIVE |
| `ConcolicRegionRuntime.pushOutboundMessageFrame` | 2108-2114 | 5 | none | LIVE |
| `ConcolicRegionRuntime.popOutboundMessageFrame` | 2118-2124 | 5 | none | LIVE |
| `ConcolicRegionRuntime.pushInboundMessageFrame` | 2134-2140 | 5 | none | LIVE |
| `ConcolicRegionRuntime.popInboundMessageFrame` | 2144-2150 | 5 | none | LIVE |
| `ConcolicRegionRuntime.exportCommunicationLeaf` | 2165-2193 | 16 | none | LIVE |
| `ConcolicRegionRuntime.publishExportRow` | 2208-2255 | 30 | in:exportCommunicationLeaf | LIVE |
| `ConcolicRegionRuntime.noteMessageSender` | 2268-2283 | 12 | EXT:CausynthTraceRecorder.outboundExchange | LIVE |
| `ConcolicRegionRuntime.attemptOf` | 2288-2290 | 3 | in:mintAmbientHandoffLeaves,mintHandoffLeaf,publishExportRow | LIVE |
| `ConcolicRegionRuntime.attachCommunicationLeaf` | 2309-2337 | 17 | none | LIVE |
| `ConcolicRegionRuntime.attachDeliveredLeaf` | 2350-2379 | 5 | in:attachCommunicationLeaf | LIVE |
| `ConcolicRegionRuntime.applyFocusedRootAssignment` | 2392-2409 | 11 | in:symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime.modelValue` | 2414-2417 | 4 | in:applyFocusedRootAssignment,mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime.communicationHandoffSite` | 2436-2448 | 12 | in:attachCommunicationLeaf,exportCommunicationLeaf | LIVE |
| `ConcolicRegionRuntime.recordVmHandoffEvent` | 2463-2515 | 36 | in:attachDeclaredCommunicationExpression | LIVE |
| `ConcolicRegionRuntime.mintArrivedCommunicationLeaf` | 2529-2545 | 9 | in:attachDeliveredLeaf | LIVE |
| `ConcolicRegionRuntime.attachConsumerRegion` | 2567-2578 | 10 | in:mintArrivedCommunicationLeaf,recordVmHandoffEvent | LIVE |
| `ConcolicRegionRuntime.mintHandoffVariable` | 2605-2621 | 9 | in:mintArrivedCommunicationLeaf,recordVmHandoffEvent | LIVE |
| `ConcolicRegionRuntime.mintHandoffLeaf` | 2638-2710 | 41 | in:mintHandoffVariable | LIVE |
| `ConcolicRegionRuntime.handoffMintKey` | 2731-2738 | 6 | in:mintAmbientHandoffLeaves,mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime.isHandoffMintKey` | 2750-2751 | 2 | EXT:ConcolicTaskPlan$RuntimeTask.answersHandoffPhase | LIVE |
| `ConcolicRegionRuntime.handoffMintLabelFor` | 2756-2756 | 1 | EXT:ConcolicTaskPlan$RuntimeTask.answersHandoffPhase; in:mintAmbientHandoffLeaves | LIVE |
| `ConcolicRegionRuntime.handoffMintLabel` | 2760-2761 | 2 | in:handoffMintLabelFor,mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime.declaredConsumerOccurrence` | 2782-2794 | 7 | in:mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime.publishAttachRow` | 2809-2819 | 7 | in:mintAmbientHandoffLeaves,mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime.mintAmbientHandoffLeaves` | 2836-2894 | 39 | in:mintArrivedCommunicationLeaf,recordVmHandoffEvent | LIVE |
| `ConcolicRegionRuntime$HandoffLeaf.<init>` | 2897-2897 | 1 | in:addPrimitiveLeaves,handoffLeaves | LIVE |
| `ConcolicRegionRuntime$HandoffLeaf.access$3700` | 2897-2897 | 1 | in:mintAmbientHandoffLeaves,mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime$HandoffLeaf.access$3900` | 2897-2897 | 1 | in:mintAmbientHandoffLeaves,mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime$HandoffLeaf.access$4000` | 2897-2897 | 1 | in:mintAmbientHandoffLeaves,mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime$HandoffLeaf.access$4100` | 2897-2897 | 1 | in:mintAmbientHandoffLeaves,mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime$HandoffLeaf.<init>` | 2903-2907 | 5 | in:<init> | LIVE |
| `ConcolicRegionRuntime$HandoffLeaf.signature` | 2911-2911 | 1 | in:access$4100 | LIVE |
| `ConcolicRegionRuntime.handoffLeaves` | 2930-2955 | 21 | in:mintAmbientHandoffLeaves,mintHandoffVariable | LIVE |
| `ConcolicRegionRuntime.addPrimitiveLeaves` | 2965-2980 | 13 | in:handoffLeaves | LIVE |
| `ConcolicRegionRuntime.exactSymbolOf` | 2984-2991 | 7 | in:mintAmbientHandoffLeaves,mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime.statesTargetReach` | 3026-3027 | 2 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime.attach` | 3035-3074 | 21 | in:attachDeclaredCommunicationExpression | LIVE |
| `ConcolicRegionRuntime.missingFieldMetadata` | 3081-3088 | 6 | in:attach,exportLeaf | LIVE |
| `ConcolicRegionRuntime.exportStatus` | 3093-3096 | 3 | in:attach,exportLeaf | LIVE |
| `ConcolicRegionRuntime.failed` | 3103-3103 | 1 | in:attach,exportLeaf | LIVE |
| `ConcolicRegionRuntime.record` | 3108-3109 | 2 | in:attachDeclaredCommunicationExpression,exportLeaf | LIVE |
| `ConcolicRegionRuntime.exitRegionFrame` | 3122-3132 | 7 | none | LIVE |
| `ConcolicRegionRuntime.throwRegionFrame` | 3142-3159 | 10 | none | LIVE |
| `ConcolicRegionRuntime.popRootInvocationFrame` | 3163-3181 | 13 | in:exitRegionFrame,throwRegionFrame | LIVE |
| `ConcolicRegionRuntime$SiblingHookGroupEntry.<init>` | 3192-3195 | 4 | in:<init>,<init> | LIVE |
| `ConcolicRegionRuntime$SiblingHookGroupEntry.claimsSiblingHook` | 3199-3204 | 5 | in:enterLoopRootInvocationFrame,enterRegionFrame | LIVE |
| `ConcolicRegionRuntime$RootInvocationFrame.<init>` | 3208-3208 | 1 | in:enterRegionFrame | LIVE |
| `ConcolicRegionRuntime$RootInvocationFrame.access$4400` | 3208-3208 | 1 | in:popRootInvocationFrame | LIVE |
| `ConcolicRegionRuntime$RootInvocationFrame.access$4500` | 3208-3208 | 1 | in:popRootInvocationFrame | LIVE |
| `ConcolicRegionRuntime$RootInvocationFrame.access$900` | 3208-3208 | 1 | in:exitRegionFrame,throwRegionFrame | LIVE |
| `ConcolicRegionRuntime$RootInvocationFrame.access$902` | 3208-3208 | 1 | in:enterRegionFrame | LIVE |
| `ConcolicRegionRuntime$RootInvocationFrame.<init>` | 3218-3222 | 5 | in:<init> | LIVE |
| `ConcolicRegionRuntime$RootHookGroup.<init>` | 3230-3233 | 4 | EXT:ConcolicTaskPlan.loopRootHookGroup,ConcolicTaskPlan.rootHookGroup | LIVE |
| `ConcolicRegionRuntime$LoopRootInvocationContext.<init>` | 3237-3237 | 1 | in:enterLoopRootInvocationFrame | LIVE |
| `ConcolicRegionRuntime$LoopRootInvocationContext.access$1100` | 3237-3237 | 1 | in:enclosingLoopRoot | LIVE |
| `ConcolicRegionRuntime$LoopRootInvocationContext.<init>` | 3242-3253 | 5 | in:<init> | LIVE |
| `ConcolicRegionRuntime$LoopRootInvocationContext.ordinalOf` | 3257-3258 | 2 | in:startSymbolicRegion | LIVE |
| `ConcolicRegionRuntime.prepareBranch` | 3268-3277 | 8 | none | LIVE |
| `ConcolicRegionRuntime.resolveBranch` | 3289-3291 | 2 | none | LIVE |
| `ConcolicRegionRuntime.resolveSwitchBranch` | 3301-3314 | 10 | none | LIVE |
| `ConcolicRegionRuntime.observeDecision` | 3326-3463 | 63 | in:resolveBranch,resolveSwitchBranch | LIVE |
| `ConcolicRegionRuntime.recordBranchPaused` | 3469-3550 | 52 | in:access$8300 | LIVE |
| `ConcolicRegionRuntime.lambda$recordBranchPaused$1` | 3488-3488 | 1 | in:recordBranchPaused | LIVE |
| `ConcolicRegionRuntime$RecordedBranch.<init>` | 3566-3566 | 1 | in:recordPaused,recordBranchPaused | LIVE |
| `ConcolicRegionRuntime$RecordedBranch.access$5700` | 3566-3566 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$RecordedBranch.access$5900` | 3566-3566 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$RecordedBranch.access$6100` | 3566-3566 | 1 | in:recordBranchPaused | LIVE |
| `ConcolicRegionRuntime$RecordedBranch.<clinit>` | 3567-3567 | 1 | none | LIVE |
| `ConcolicRegionRuntime$RecordedBranch.<init>` | 3573-3576 | 4 | in:<clinit>,<init> | LIVE |
| `ConcolicRegionRuntime.recordSwitchBranchPaused` | 3584-3647 | 49 | in:access$8400 | LIVE |
| `ConcolicRegionRuntime.branchMapping` | 3681-3687 | 7 | in:access$9100,recordBranchPaused,recordSwitchBranchPaused | LIVE |
| `ConcolicRegionRuntime.attestVmBranchEvent` | 3704-3820 | 71 | in:recordBranchPaused,recordSwitchBranchPaused | LIVE |
| `ConcolicRegionRuntime.attestVmSwitchConditions` | 3826-3908 | 49 | in:attestVmBranchEvent | LIVE |
| `ConcolicRegionRuntime.switchSelectorIfMatches` | 3913-3938 | 21 | in:attestVmSwitchConditions | LIVE |
| `ConcolicRegionRuntime.abandonOccurrence` | 3944-3949 | 6 | in:judgeFinishedOccurrence | LIVE |
| `ConcolicRegionRuntime.finish` | 3954-3957 | 4 | in:endAtCut,exitRegionFrame,observeDecision+1 | LIVE |
| `ConcolicRegionRuntime.finishOccurrence` | 3962-3993 | 22 | in:finish | LIVE |
| `ConcolicRegionRuntime.judgeFinishedOccurrence` | 4002-4115 | 54 | in:finishOccurrence | LIVE |
| `ConcolicRegionRuntime.closeOccurrence` | 4125-4234 | 65 | in:finishOccurrence | LIVE |
| `ConcolicRegionRuntime.symbolizeReceiverFields` | 4242-4264 | 16 | in:prepare | LIVE |
| `ConcolicRegionRuntime.symbolizeField` | 4271-4317 | 34 | in:symbolizeFieldPath,symbolizeReceiverFields | LIVE |
| `ConcolicRegionRuntime.symbolizeFieldPath` | 4324-4342 | 13 | in:symbolizeArgument,symbolizeReceiverFields | LIVE |
| `ConcolicRegionRuntime.applyFieldPathModel` | 4348-4359 | 9 | in:materializeArgument | LIVE |
| `ConcolicRegionRuntime.applyFieldModel` | 4364-4373 | 7 | in:applyFieldPathModel | LIVE |
| `ConcolicRegionRuntime.modeledReference` | 4384-4394 | 8 | in:materializeArgument,materializeMethodArgument | LIVE |
| `ConcolicRegionRuntime.unmodeled` | 4399-4399 | 1 | in:materializeArgument | LIVE |
| `ConcolicRegionRuntime.trackMaterializedContainer` | 4406-4409 | 3 | in:materializeArgument,materializeMethodArgument | LIVE |
| `ConcolicRegionRuntime.replayModelLiteral` | 4450-4455 | 5 | in:materializePrimitiveValue | LIVE |
| `ConcolicRegionRuntime.clockSkewLiteral` | 4466-4478 | 10 | in:replayModelLiteral | LIVE |
| `ConcolicRegionRuntime.integralLiteral` | 4483-4487 | 4 | in:clockSkewLiteral | LIVE |
| `ConcolicRegionRuntime.integralValue` | 4492-4496 | 3 | in:clockSkewLiteral | LIVE |
| `ConcolicRegionRuntime.materializePrimitiveValue` | 4502-4558 | 38 | in:materializeArgument,materializeMethodArgument,materializePrimitive+2 | LIVE |
| `ConcolicRegionRuntime.primitiveBoxExpression` | 4565-4570 | 6 | in:materializePrimitiveValue | LIVE |
| `ConcolicRegionRuntime.writeModeledField` | 4576-4585 | 9 | in:applyFieldModel,applyFocusedRootAssignment,mintHandoffLeaf+1 | LIVE |
| `ConcolicRegionRuntime.writeIndexedContainerElement` | 4591-4624 | 25 | in:writeContainerTarget | LIVE |
| `ConcolicRegionRuntime.writeContainerTarget` | 4629-4643 | 10 | in:materializeField | LIVE |
| `ConcolicRegionRuntime.writeAssociativeContainerTarget` | 4649-4668 | 13 | in:materializeAssociativeRead,writeContainerTarget | LIVE |
| `ConcolicRegionRuntime.writeOrderedIterationTarget` | 4674-4735 | 50 | in:writeContainerTarget | LIVE |
| `ConcolicRegionRuntime.modeledContainerValue` | 4741-4741 | 1 | in:writeAssociativeContainerTarget,writeOrderedIterationTarget | LIVE |
| `ConcolicRegionRuntime.modeledContainerValue` | 4752-4754 | 3 | in:modeledContainerValue,writeIndexedContainerElement | LIVE |
| `ConcolicRegionRuntime.collidesWithLiveElement` | 4760-4761 | 2 | in:writeOrderedIterationTarget | LIVE |
| `ConcolicRegionRuntime.containerKey` | 4765-4780 | 13 | in:writeContainerTarget | LIVE |
| `ConcolicRegionRuntime.coerceModelValue` | 4785-4835 | 36 | in:containerKey,materializePrimitiveValue,materializeSymbolicBoolean+3 | LIVE |
| `ConcolicRegionRuntime.unquoteSmtString` | 4839-4839 | 1 | in:access$9900,containerKey | LIVE |
| `ConcolicRegionRuntime.isPrimitiveBox` | 4843-4843 | 1 | in:materializeArgument,materializeMethodArgument,materializeReference+1 | LIVE |
| `ConcolicRegionRuntime.resolveFieldPathLeafOwner` | 4850-4865 | 12 | in:leafOwner,applyFieldPathModel,symbolizeFieldPath | LIVE |
| `ConcolicRegionRuntime.readPathSegment` | 4869-4882 | 11 | in:resolveFieldPathLeafOwner | LIVE |
| `ConcolicRegionRuntime.pathIndex` | 4886-4894 | 7 | in:readPathSegment | LIVE |
| `ConcolicRegionRuntime.symbolize` | 4901-4934 | 26 | in:materializeReference,symbolizeArgument,symbolizeMethodArgument+1 | LIVE |
| `ConcolicRegionRuntime.retainPropagatedInput` | 4941-4950 | 7 | in:materializeField,materializePrimitiveValue,symbolize+1 | LIVE |
| `ConcolicRegionRuntime.observeWithoutMinting` | 4995-5009 | 12 | in:retainPropagatedInput | LIVE |
| `ConcolicRegionRuntime.wholeStateContainerValue` | 5022-5022 | 1 | none | DEAD |
| `ConcolicRegionRuntime.containerValue` | 5030-5030 | 1 | in:materializeField,observeWithoutMinting,recordVmHandoffEvent+3 | LIVE |
| `ConcolicRegionRuntime.manualMintLabel` | 5044-5052 | 7 | in:materializePrimitiveValue,symbolize,symbolizeField | LIVE |
| `ConcolicRegionRuntime.carriesInputAuthority` | 5073-5076 | 4 | in:retainPropagatedInput | LIVE |
| `ConcolicRegionRuntime.configuredSourceCarriesAuthority` | 5091-5091 | 1 | in:symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime.declaredCommunicationCutPort` | 5104-5106 | 2 | in:observeWithoutMinting | LIVE |
| `ConcolicRegionRuntime.primitiveDescriptor` | 5114-5116 | 3 | in:carriesInputAuthority,symbolizeField | LIVE |
| `ConcolicRegionRuntime.requireTrackedContainer` | 5121-5126 | 4 | in:materializeField,trackContainerOrObserveConcrete | LIVE |
| `ConcolicRegionRuntime.trackContainerOrObserveConcrete` | 5135-5140 | 5 | in:symbolize,symbolizeField | LIVE |
| `ConcolicRegionRuntime.readField` | 5144-5164 | 16 | in:readPathSegment | LIVE |
| `ConcolicRegionRuntime.readExactField` | 5169-5174 | 5 | in:symbolizeField | LIVE |
| `ConcolicRegionRuntime.declaredInstanceField` | 5180-5183 | 4 | in:materializeField,readExactField,symbolizeConfiguredSourceField+1 | LIVE |
| `ConcolicRegionRuntime.declaredInstanceField` | 5190-5190 | 1 | in:mintAmbientHandoffLeaves,mintHandoffVariable,publishExportRow+1 | LIVE |
| `ConcolicRegionRuntime.declaredInstanceField` | 5203-5228 | 21 | in:declaredInstanceField | LIVE |
| `ConcolicRegionRuntime.exactFieldSignature` | 5232-5233 | 2 | in:access$4200,addPrimitiveLeaves,handoffLeaves+2 | LIVE |
| `ConcolicRegionRuntime.activeRegion` | 5238-5240 | 3 | in:attachConsumerRegion,communicationHandoffSite,engineExpression+22 | LIVE |
| `ConcolicRegionRuntime.pushActiveRegion` | 5244-5245 | 2 | in:startSymbolicRegion | LIVE |
| `ConcolicRegionRuntime.innermostActiveRegionStack` | 5250-5255 | 5 | in:enclosingActiveRegion,hasEnclosingActiveRegion,popActiveRegion | LIVE |
| `ConcolicRegionRuntime.hasEnclosingActiveRegion` | 5260-5261 | 2 | in:closeOccurrence | LIVE |
| `ConcolicRegionRuntime.enclosingActiveRegion` | 5266-5271 | 5 | in:closeOccurrence | LIVE |
| `ConcolicRegionRuntime.popActiveRegion` | 5276-5280 | 4 | in:closeOccurrence,startSymbolicRegion | LIVE |
| `ConcolicRegionRuntime.lightweightAccessorContextMatches` | 5286-5294 | 8 | in:access$9600 | LIVE |
| `ConcolicRegionRuntime.lightweightAccessorContextOccurrence` | 5299-5306 | 6 | in:access$9700 | LIVE |
| `ConcolicRegionRuntime.ownerRegion` | 5310-5311 | 2 | in:activeRegion,attachConsumerRegion,declaredConsumerOccurrence+4 | LIVE |
| `ConcolicRegionRuntime.freshPrimitiveBox` | 5317-5344 | 19 | in:materializePrimitiveValue | LIVE |
| `ConcolicRegionRuntime.instanceOfName` | 5348-5359 | 8 | in:access$9800,instanceOfName | LIVE |
| `ConcolicRegionRuntime.branchConditionMatches` | 5364-5391 | 22 | in:attestVmBranchEvent | LIVE |
| `ConcolicRegionRuntime.booleanValueRequiredByZeroBranch` | 5397-5411 | 14 | in:branchConditionMatches | LIVE |
| `ConcolicRegionRuntime.representedBooleanValue` | 5420-5438 | 14 | in:branchConditionMatches | LIVE |
| `ConcolicRegionRuntime.observedOperatorImpliesBranch` | 5452-5461 | 8 | in:branchConditionMatches,semanticBranchCondition | LIVE |
| `ConcolicRegionRuntime.semanticBranchCondition` | 5467-5489 | 19 | in:recordBranchPaused | LIVE |
| `ConcolicRegionRuntime.binaryOperator` | 5493-5494 | 2 | in:recordBranchPaused | LIVE |
| `ConcolicRegionRuntime.symbolicNull` | 5498-5504 | 6 | in:branchConditionMatches | LIVE |
| `ConcolicRegionRuntime.resumePathCondition` | 5510-5515 | 6 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime.ensurePathRecordingStarted` | 5522-5524 | 3 | in:materializeField,materializePrimitiveValue,mintHandoffLeaf+5 | LIVE |
| `ConcolicRegionRuntime.diagnosticsEnabled` | 5528-5538 | 9 | in:diag,diagAfterVmClose | LIVE |
| `ConcolicRegionRuntime.diag` | 5546-5566 | 14 | EXT:SharedStateCapture.fileShared; in:noteFaultIdle,noteRecordedFaultAnswer,observeReplayDecision+10 | LIVE |
| `ConcolicRegionRuntime.diagAfterVmClose` | 5570-5571 | 2 | EXT:ConcolicResultPublisher.publishCompletedResult,ConcolicResultPublisher.submitCompletedResultPublication | LIVE |
| `ConcolicRegionRuntime.diagLine` | 5576-5584 | 9 | in:diag,diagAfterVmClose | LIVE |
| `ConcolicRegionRuntime.parseJson` | 5588-5594 | 5 | EXT:SharedStateCapture.captureRecordedSharedStateRaw,SharedStateCapture.decodeTrackedLocations; in:attestVmBranchEvent,recordBranchPaused,recordSwitchBranchPaused | LIVE |
| `ConcolicRegionRuntime.rootCause` | 5599-5604 | 5 | EXT:ConcolicResultPublisher.mergeEngineSummary,ConcolicResultPublisher.publishCompletedResult,ConcolicResultPublisher.submitCompletedResultPublication+3; in:armGuardedRead,attach,attestVmBranchEvent+21 | LIVE |
| `ConcolicRegionRuntime.recordedScalar` | 5620-5627 | 3 | in:materializePrimitiveValue,mintAmbientHandoffLeaves,mintHandoffLeaf+2 | LIVE |
| `ConcolicRegionRuntime$MissingValue.<clinit>` | 5630-5630 | 1 | none | LIVE |
| `ConcolicRegionRuntime$MissingValue.<init>` | 5630-5630 | 1 | in:<clinit> | LIVE |
| `ConcolicRegionRuntime$MissingValue.valueOf` | 5630-5630 | 1 | none | DEAD |
| `ConcolicRegionRuntime$MissingValue.values` | 5630-5630 | 1 | none | DEAD |
| `ConcolicRegionRuntime$UnsupportedReplayValue.<clinit>` | 5632-5632 | 1 | none | LIVE |
| `ConcolicRegionRuntime$UnsupportedReplayValue.<init>` | 5632-5632 | 1 | in:<clinit> | LIVE |
| `ConcolicRegionRuntime$UnsupportedReplayValue.valueOf` | 5632-5632 | 1 | none | DEAD |
| `ConcolicRegionRuntime$UnsupportedReplayValue.values` | 5632-5632 | 1 | none | DEAD |
| `ConcolicRegionRuntime$AccessorCallContext.<init>` | 5634-5634 | 1 | in:enterAccessorCallContext | LIVE |
| `ConcolicRegionRuntime$AccessorCallContext.access$500` | 5634-5634 | 1 | in:exitAccessorCallContext | LIVE |
| `ConcolicRegionRuntime$AccessorCallContext.access$600` | 5634-5634 | 1 | in:exitAccessorCallContext | LIVE |
| `ConcolicRegionRuntime$AccessorCallContext.access$8200` | 5634-5634 | 1 | in:lightweightAccessorContextMatches | LIVE |
| `ConcolicRegionRuntime$AccessorCallContext.<init>` | 5651-5662 | 12 | in:<init> | LIVE |
| `ConcolicRegionRuntime$AccessorCallContext.matches` | 5668-5671 | 3 | in:access$8200 | LIVE |
| `ConcolicRegionRuntime$SwitchExpectation.access$4800` | 5676-5676 | 1 | in:resolveSwitchBranch | LIVE |
| `ConcolicRegionRuntime$SwitchExpectation.access$6600` | 5676-5676 | 1 | in:multiway,attestVmSwitchConditions,recordSwitchBranchPaused | LIVE |
| `ConcolicRegionRuntime$SwitchExpectation.access$6800` | 5676-5676 | 1 | in:observationAt,observeReplayProgress,attestVmSwitchConditions+1 | LIVE |
| `ConcolicRegionRuntime$SwitchExpectation.access$6900` | 5676-5676 | 1 | in:observationAt,observeReplayProgress,attestVmSwitchConditions+1 | LIVE |
| `ConcolicRegionRuntime$SwitchExpectation.access$7000` | 5676-5676 | 1 | in:observationAt,observeReplayProgress,replayTrace+2 | LIVE |
| `ConcolicRegionRuntime$SwitchExpectation.<init>` | 5682-5687 | 5 | in:parse | LIVE |
| `ConcolicRegionRuntime$SwitchExpectation.parse` | 5692-5737 | 27 | in:access$4800 | LIVE |
| `ConcolicRegionRuntime$SwitchExpectation.caseArm` | 5742-5742 | 1 | in:access$6600 | LIVE |
| `ConcolicRegionRuntime$BranchDecision.<init>` | 5764-5767 | 4 | in:binary,multiway | LIVE |
| `ConcolicRegionRuntime$BranchDecision.binary` | 5770-5770 | 1 | in:resolveBranch | LIVE |
| `ConcolicRegionRuntime$BranchDecision.multiway` | 5774-5774 | 1 | in:resolveSwitchBranch | LIVE |
| `ConcolicRegionRuntime$BranchDecision.outcome` | 5778-5778 | 1 | in:recordConcreteDecision,observeDecision | LIVE |
| `ConcolicRegionRuntime$BranchDecision.observationAt` | 5783-5788 | 5 | in:recordConcreteDecision,recordReplayBoundary | LIVE |
| `ConcolicRegionRuntime$BranchDecision.observeReplayProgress` | 5800-5806 | 5 | in:observeReplayDecision | LIVE |
| `ConcolicRegionRuntime$BranchDecision.replayTrace` | 5811-5813 | 2 | in:observeReplayDecision | LIVE |
| `ConcolicRegionRuntime$BranchDecision.recordPaused` | 5821-5824 | 3 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$BranchDecision.boundaryNoun` | 5831-5831 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$BranchDecision.preparedNoun` | 5837-5837 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$BranchDecision.observationNoun` | 5842-5842 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$BranchDecision.addressesPermutedTargetOccurrence` | 5852-5852 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$VmBranchEventAttestation.access$6300` | 5857-5857 | 1 | in:recordBranchPaused,recordSwitchBranchPaused | LIVE |
| `ConcolicRegionRuntime$VmBranchEventAttestation.access$6400` | 5857-5857 | 1 | in:recordBranchPaused,recordSwitchBranchPaused | LIVE |
| `ConcolicRegionRuntime$VmBranchEventAttestation.access$6700` | 5857-5857 | 1 | in:recordSwitchBranchPaused | LIVE |
| `ConcolicRegionRuntime$VmBranchEventAttestation.access$7100` | 5857-5857 | 1 | in:attestVmBranchEvent,attestVmSwitchConditions | LIVE |
| `ConcolicRegionRuntime$VmBranchEventAttestation.access$7300` | 5857-5857 | 1 | in:attestVmBranchEvent,attestVmSwitchConditions | LIVE |
| `ConcolicRegionRuntime$VmBranchEventAttestation.<init>` | 5864-5869 | 5 | in:invalid,valid | LIVE |
| `ConcolicRegionRuntime$VmBranchEventAttestation.valid` | 5873-5873 | 1 | in:access$7300 | LIVE |
| `ConcolicRegionRuntime$VmBranchEventAttestation.invalid` | 5877-5878 | 2 | in:access$7100 | LIVE |
| `ConcolicRegionRuntime$PreparedBranch.<init>` | 5882-5882 | 1 | in:prepareBranch | LIVE |
| `ConcolicRegionRuntime$PreparedBranch.access$4700` | 5882-5882 | 1 | in:prepareBranch | LIVE |
| `ConcolicRegionRuntime$PreparedBranch.access$5100` | 5882-5882 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$PreparedBranch.access$5200` | 5882-5882 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$PreparedBranch.<init>` | 5890-5896 | 7 | in:<init> | LIVE |
| `ConcolicRegionRuntime$PreparedBranch.matches` | 5900-5902 | 2 | in:access$5100 | LIVE |
| `ConcolicRegionRuntime$OccurrenceCounter.<init>` | 5911-5912 | 2 | in:<init> | LIVE |
| `ConcolicRegionRuntime$OccurrenceCounter.local` | 5916-5918 | 3 | in:nextLocalMaterializationOccurrence | LIVE |
| `ConcolicRegionRuntime$OccurrenceCounter.methodArgument` | 5922-5922 | 1 | in:materializeMethodArgument | LIVE |
| `ConcolicRegionRuntime$OccurrenceCounter.observedMethodArgument` | 5927-5927 | 1 | in:symbolizeMethodArgument | LIVE |
| `ConcolicRegionRuntime$OccurrenceCounter.field` | 5940-5941 | 2 | in:materializeField | LIVE |
| `ConcolicRegionRuntime$OccurrenceCounter.explicitFault` | 5953-5953 | 1 | in:materializeSymbolicBoolean | LIVE |
| `ConcolicRegionRuntime$OccurrenceCounter.observe` | 5958-5960 | 3 | in:explicitFault,field,local+1 | LIVE |
| `ConcolicRegionRuntime$OccurrenceCounter.observed` | 5964-5964 | 1 | in:observe,observedMethodArgument | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$000` | 5968-5968 | 1 | in:checkReplayLoopBody | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$100` | 5968-5968 | 1 | in:recordLoopCardinality | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$1200` | 5968-5968 | 1 | in:symbolizeArgument | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$1300` | 5968-5968 | 1 | in:materializeField,materializeMethodArgument,materializeSymbolicBoolean+1 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$1400` | 5968-5968 | 1 | in:materializeField,materializePrimitive,materializeReference+3 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$1500` | 5968-5968 | 1 | in:materializePrimitive,materializeReference | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$1600` | 5968-5968 | 1 | in:applyFieldModel,applyFieldPathModel,materializePrimitiveValue+3 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$1700` | 5968-5968 | 1 | in:applyFieldModel,materializeAssociativeRead,materializeField+6 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$1800` | 5968-5968 | 1 | in:materializeField | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$1900` | 5968-5968 | 1 | in:materializeField,observeWithoutMinting,retainPropagatedInput+3 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$200` | 5968-5968 | 1 | in:completeLoopCardinality | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$2000` | 5968-5968 | 1 | in:materializeField,retainPropagatedInput,symbolize+1 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$2100` | 5968-5968 | 1 | in:materializeAssociativeRead | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$2200` | 5968-5968 | 1 | in:materializeAssociativeRead | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$2300` | 5968-5968 | 1 | in:judgeFinishedOccurrence,materializeAssociativeRead | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$2400` | 5968-5968 | 1 | in:armGuardedRead,judgeFinishedOccurrence | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$2500` | 5968-5968 | 1 | in:observeCausalSource | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$2600` | 5968-5968 | 1 | in:symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$2900` | 5968-5968 | 1 | in:mintHandoffLeaf,symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$300` | 5968-5968 | 1 | in:enterAccessorCallContext | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$3100` | 5968-5968 | 1 | in:symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$3200` | 5968-5968 | 1 | in:symbolizeConfiguredSourceField | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$3800` | 5968-5968 | 1 | in:mintHandoffLeaf | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$4600` | 5968-5968 | 1 | in:prepareBranch | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$4900` | 5968-5968 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$5000` | 5968-5968 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$5300` | 5968-5968 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$5400` | 5968-5968 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$5500` | 5968-5968 | 1 | in:judgeFinishedOccurrence,observeDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$5600` | 5968-5968 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$5800` | 5968-5968 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$6000` | 5968-5968 | 1 | in:observeDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$6200` | 5968-5968 | 1 | in:recordBranchPaused,recordSwitchBranchPaused | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$6202` | 5968-5968 | 1 | in:recordBranchPaused,recordSwitchBranchPaused | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$700` | 5968-5968 | 1 | in:prepare | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$702` | 5968-5968 | 1 | in:prepare | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$7200` | 5968-5968 | 1 | in:attestVmBranchEvent,ownerRegion | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$7400` | 5968-5968 | 1 | in:closeOccurrence | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$7402` | 5968-5968 | 1 | in:abandonOccurrence | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$7500` | 5968-5968 | 1 | in:finishOccurrence,judgeFinishedOccurrence | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$7600` | 5968-5968 | 1 | in:judgeFinishedOccurrence | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$7700` | 5968-5968 | 1 | in:judgeFinishedOccurrence | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$7800` | 5968-5968 | 1 | in:judgeFinishedOccurrence | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$7900` | 5968-5968 | 1 | in:closeOccurrence | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$8002` | 5968-5968 | 1 | in:closeOccurrence | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.access$8100` | 5968-5968 | 1 | in:materializePrimitiveValue | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.<init>` | 5980-6187 | 45 | in:startSymbolicRegion | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.elapsedMillis` | 5997-5998 | 2 | EXT:ConcolicResultPublisher.addResultIdentity | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.attributedSourceKeys` | 6072-6075 | 4 | in:access$7500,mintAttribution | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.beginClose` | 6079-6081 | 3 | in:access$7900 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.releaseActivationOrdinal` | 6192-6195 | 4 | EXT:ConcolicResultPublisher.strandWithoutTerminal; in:abandonOccurrence,judgeFinishedOccurrence,startSymbolicRegion | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.occurrenceId` | 6208-6208 | 1 | EXT:ConcolicResultPublisher.addResultIdentity,SharedStateCapture.evidenceIdentity; in:recordConfiguredSourceMint,recordManualSymbolization,stageMessageExpression+1 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.chargeLoopBody` | 6217-6237 | 13 | in:access$000 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordLoopCardinality` | 6242-6278 | 25 | in:access$100 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.completeLoopCardinality` | 6281-6282 | 2 | in:access$200 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.loopCardinalityGap` | 6286-6295 | 9 | in:recordLoopCardinality | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.loopBoundCut` | 6300-6307 | 6 | in:checkLoopBackedge | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.nextHandoffAttach` | 6312-6315 | 4 | in:access$3800 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.nextBranchOccurrence` | 6319-6322 | 4 | in:access$5000,prepareBranch,recordConcreteDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordConcreteDecision` | 6332-6347 | 13 | in:access$5600 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordReplayBoundary` | 6356-6362 | 7 | in:access$5300 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordDecisionRow` | 6370-6376 | 6 | in:recordConcreteDecision,recordReplayBoundary | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.observeReplayDecision` | 6380-6380 | 1 | in:access$5400 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.observeReplayDecision` | 6386-6396 | 9 | in:access$5800,observeReplayDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.replayPrefixContradicted` | 6404-6405 | 2 | in:access$5500 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.nextLocalMaterializationOccurrence` | 6410-6410 | 1 | in:access$1500 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.prepareBranch` | 6417-6430 | 10 | in:access$4600 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.takePreparedBranch` | 6434-6434 | 1 | in:access$4900 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.nameUnreachedTargetBranch` | 6448-6464 | 11 | EXT:ConcolicResultPublisher.populateCompletedResult | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordTargetReach` | 6471-6483 | 10 | in:access$6000,recordConcreteDecision | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.addUnresolvedOnce` | 6486-6488 | 3 | EXT:ConcolicResultPublisher.buildCompletedResult; in:addSourcePhaseGap,loopBoundCut,nameUnreachedTargetBranch+19 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.noteRecordedFaultAnswer` | 6511-6514 | 3 | in:materializeSymbolicBoolean | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.noteFaultIdle` | 6518-6527 | 7 | in:materializeSymbolicBoolean | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.observeConfiguredSourceEntry` | 6541-6595 | 40 | in:access$2600 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordConfiguredSourcePhaseObservation` | 6606-6618 | 11 | in:observeConfiguredSourceEntry | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.owesConfiguredSourceModel` | 6639-6646 | 7 | in:access$7700 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordConfiguredSourceMint` | 6654-6666 | 12 | in:access$3100 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordManualSymbolization` | 6678-6680 | 2 | in:access$2000 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordManualSymbolization` | 6702-6760 | 36 | in:access$8100,recordManualSymbolization | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.addSourcePhaseGap` | 6766-6790 | 24 | in:configuredSourceAssignment,observeConfiguredSourceEntry | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordSymbolicSource` | 6794-6801 | 5 | in:access$3200 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.evidenceSnapshot` | 6809-6812 | 3 | EXT:SharedStateCapture.evidenceIdentity | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordSymbolizedInputPort` | 6816-6820 | 5 | in:access$1900 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.uniqueAssignment` | 6829-6841 | 11 | in:assignment,configuredSourceAssignment | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.assignment` | 6846-6848 | 2 | in:access$1600 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.lambda$assignment$0` | 6847-6847 | 1 | in:assignment | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.configuredSourceAssignment` | 6856-6879 | 7 | in:access$2900 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.lambda$configuredSourceAssignment$1` | 6857-6857 | 1 | in:configuredSourceAssignment | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.mintAttribution` | 6892-6900 | 8 | in:configuredSourceAssignment,mintIsNotThePlannedNode | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.mintIsNotThePlannedNode` | 6926-6937 | 8 | in:configuredSourceAssignment | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.hasAppliedExactNullReferenceAssignment` | 6945-6959 | 12 | in:access$1200 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.fieldAssignments` | 6964-6972 | 8 | in:access$1800 | LIVE |
| `ConcolicRegionRuntime$ActiveRegion.recordModelAssignment` | 6976-6977 | 2 | in:access$1700 | LIVE |
| `ConcolicRegionRuntime$DynamicLoopCardinality.<init>` | 6982-6982 | 1 | in:recordLoopCardinality | LIVE |
| `ConcolicRegionRuntime$DynamicLoopCardinality.access$8600` | 6982-6982 | 1 | in:chargeLoopBody,recordLoopCardinality | LIVE |
| `ConcolicRegionRuntime$DynamicLoopCardinality.access$8800` | 6982-6982 | 1 | in:recordLoopCardinality | LIVE |
| `ConcolicRegionRuntime$DynamicLoopCardinality.<init>` | 6986-6989 | 4 | in:<init> | LIVE |
| `ConcolicRegionRuntime$LoopBackedgeBudget.<init>` | 6996-7006 | 7 | in:<init> | LIVE |
| `ConcolicRegionRuntime$LoopBackedgeBudget.recordTraversal` | 7009-7017 | 6 | in:checkLoopBackedge | LIVE |
| `ConcolicRegionRuntime$LoopBackedgeBudget.scoped` | 7021-7021 | 1 | in:chargeLoopBody | LIVE |
| `ConcolicRegionRuntime$LoopBackedgeBudget.recordBody` | 7029-7031 | 3 | in:chargeLoopBody | LIVE |
| `ConcolicRegionRuntime$LoopBackedgeBudget.toJson` | 7035-7046 | 11 | EXT:ConcolicResultPublisher.populateCompletedResult | LIVE |
| `ConcolicRegionRuntime$LoopBackedgeBudget.bodiesToJson` | 7050-7061 | 12 | EXT:ConcolicResultPublisher.populateCompletedResult | LIVE |
| `ConcolicRegionRuntime$ReplayLoopResourceCut.<init>` | 7078-7083 | 5 | in:chargeLoopBody,checkReplayLoopBody | LIVE |
| `ConcolicRegionRuntime$ReplayLoopResourceCut.toJson` | 7086-7092 | 7 | in:chargeLoopBody,checkReplayLoopBody | LIVE |
| `ConcolicRegionRuntime$LoopBoundCut.access$8900` | 7098-7098 | 1 | in:loopBoundCut | LIVE |
| `ConcolicRegionRuntime$LoopBoundCut.access$9000` | 7098-7098 | 1 | in:loopBoundCut | LIVE |
| `ConcolicRegionRuntime$LoopBoundCut.<init>` | 7105-7111 | 5 | in:loopBoundCut | LIVE |
| `ConcolicRegionRuntime$LoopBoundCut.toJson` | 7114-7119 | 6 | in:loopBoundCut | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.<init>` | 7138-7265 | 68 | EXT:ConcolicTaskPlan$RuntimeTask.<init> | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.declaresArrayInput` | 7268-7287 | 15 | in:materializeReference,symbolize,symbolizeArgument+1 | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.declaresReferenceInput` | 7291-7292 | 2 | in:hasAppliedExactNullReferenceAssignment | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.matchesLocal` | 7298-7302 | 5 | in:materializePrimitive,materializeReference | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.matchesMethodArgument` | 7307-7308 | 2 | in:materializeMethodArgument,symbolizeMethodArgument | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.acceptsOccurrence` | 7313-7313 | 1 | in:acceptsDirectFieldOccurrence,matchesField,explicitFaultCandidates+4 | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.acceptsDirectFieldOccurrence` | 7318-7322 | 4 | in:materializeField | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.repeatedPrimitiveAccessor` | 7326-7328 | 3 | in:assignment,materializePrimitive | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.declaresWallClockRead` | 7342-7343 | 2 | in:recordManualSymbolization,replayModelLiteral | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.matchesStaticField` | 7350-7376 | 20 | in:materializeStaticPrimitiveField | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.exactStaticFieldPath` | 7385-7402 | 16 | in:materializeStaticPrimitiveField | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.matchesField` | 7409-7474 | 42 | in:materializeField | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.leafOwner` | 7478-7478 | 1 | in:materializeField | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.exactLeafFieldSignature` | 7486-7486 | 1 | in:materializeField | LIVE |
| `ConcolicRegionRuntime$SymbolizeAction.exactLeafFieldSignature` | 7490-7516 | 20 | in:exactLeafFieldSignature,applyFieldModel,materializePrimitiveValue+1 | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.<init>` | 7539-7575 | 26 | EXT:ConcolicTaskPlan$RuntimeTask.<init>; in:modelValue | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.configuredSourceAssignment` | 7578-7580 | 3 | EXT:ConcolicTaskPlan$RuntimeTask.<init>; in:judgeFinishedOccurrence | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.matchesConfiguredSource` | 7586-7591 | 6 | EXT:ConcolicTaskPlan$RuntimeTask.<init>,ConcolicTaskPlan$RuntimeTask.answersHandoffPhase; in:lambda$configuredSourceAssignment$1 | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.hasContainerTarget` | 7595-7595 | 1 | EXT:ConcolicTaskPlan$RuntimeTask.<init>,ConcolicTaskPlan$RuntimeTask.answersHandoffPhase; in:materializeField | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.iterationTarget` | 7599-7600 | 2 | in:validContainerTarget,writeContainerTarget | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.dynamicAssociativeTarget` | 7604-7605 | 2 | in:fieldAssignments,validContainerTarget,materializeAssociativeRead+1 | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.validContainerTarget` | 7610-7626 | 13 | in:materializeAssociativeRead,materializeField | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.matches` | 7631-7636 | 5 | in:hasAppliedExactNullReferenceAssignment,lambda$assignment$0 | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.targetsFieldAccess` | 7640-7649 | 8 | in:fieldAssignments | LIVE |
| `ConcolicRegionRuntime$ModelAssignment.referenceValue` | 7653-7659 | 6 | in:materializeReference,modeledReference | LIVE |
| `ConcolicRegionRuntime$GuardedReadAssignment.<init>` | 7681-7711 | 26 | EXT:ConcolicTaskPlan$RuntimeTask.<init> | LIVE |
| `ConcolicRegionRuntime$GuardedReadAssignment.primitiveValueBits` | 7716-7747 | 19 | in:<init> | LIVE |
| `ConcolicRegionRuntime$GuardedReadAssignment.matches` | 7752-7757 | 5 | EXT:ConcolicTaskPlan$RuntimeTask.guardedReadAssignment | LIVE |

#### `causynth.RuntimeSelectedRegionFinalizer` — all 242 methods

| method | lines | body | callers | verdict |
|---|---|---:|---|---|
| `RuntimeSelectedRegionFinalizer$RuntimeAccessDemand.required` | 0-0 | 0 | in:boundedRuntimeAccesses | LIVE |
| `RuntimeSelectedRegionFinalizer.access$3000` | 44-44 | 1 | in:structuralLoopGuard,structureCarrierGuard | LIVE |
| `RuntimeSelectedRegionFinalizer.access$3100` | 44-44 | 1 | in:structureCarrierGuard | LIVE |
| `RuntimeSelectedRegionFinalizer.access$4600` | 44-44 | 1 | in:<init>,lambda$backwardInputs$5 | LIVE |
| `RuntimeSelectedRegionFinalizer.access$4700` | 44-44 | 1 | in:computeInputsForOutput,hasInput,hasOutput+2 | LIVE |
| `RuntimeSelectedRegionFinalizer.access$4800` | 44-44 | 1 | in:computeTargetInputs | LIVE |
| `RuntimeSelectedRegionFinalizer.access$4900` | 44-44 | 1 | in:computeInputsForOutput | LIVE |
| `RuntimeSelectedRegionFinalizer.access$5000` | 44-44 | 1 | in:computeInputsForOutput | LIVE |
| `RuntimeSelectedRegionFinalizer.<init>` | 167-168 | 2 | none | DEAD |
| `RuntimeSelectedRegionFinalizer.finalizeRegions` | 183-312 | 80 | EXT:CausynthTraceRecorder.aggregateStateTrace | LIVE |
| `RuntimeSelectedRegionFinalizer.canonicalizeRegionEdges` | 319-335 | 14 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer$CutPort.<init>` | 338-338 | 1 | in:declaredCutPorts | LIVE |
| `RuntimeSelectedRegionFinalizer$CutPort.access$300` | 338-338 | 1 | in:declareCommunicationPorts | LIVE |
| `RuntimeSelectedRegionFinalizer$CutPort.access$400` | 338-338 | 1 | in:declareCommunicationPorts | LIVE |
| `RuntimeSelectedRegionFinalizer$CutPort.access$500` | 338-338 | 1 | in:declareCommunicationPorts | LIVE |
| `RuntimeSelectedRegionFinalizer$CutPort.<init>` | 344-348 | 5 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer.declaredCutPorts` | 358-378 | 18 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.declareCommunicationPorts` | 384-411 | 22 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.declaredCutPortCell` | 415-451 | 15 | EXT:RuntimeRegionPlanner.declareCutPortCells,RuntimeRegionPlanner.declaredCutPortAction; in:boundaryCells | LIVE |
| `RuntimeSelectedRegionFinalizer.recordedOccurrenceProducerFlows` | 461-568 | 82 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$recordedOccurrenceProducerFlows$0` | 519-519 | 1 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$recordedOccurrenceProducerFlows$1` | 521-521 | 1 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.communicationCaptureOrdinals` | 574-593 | 18 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$communicationCaptureOrdinals$2` | 582-582 | 1 | in:communicationCaptureOrdinals | LIVE |
| `RuntimeSelectedRegionFinalizer.captureOrdinalKey` | 597-600 | 4 | in:communicationCaptureOrdinals,observedCommunicationCaptureOrdinals | LIVE |
| `RuntimeSelectedRegionFinalizer.observedCommunicationCaptureOrdinals` | 618-640 | 16 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.typedReceivers` | 654-682 | 22 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer$TypedReceiver.<init>` | 685-685 | 1 | in:typedReceivers | LIVE |
| `RuntimeSelectedRegionFinalizer$TypedReceiver.access$600` | 685-685 | 1 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer$TypedReceiver.access$700` | 685-685 | 1 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer$TypedReceiver.access$800` | 685-685 | 1 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer$TypedReceiver.<init>` | 692-696 | 5 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer.occurrenceKey` | 721-735 | 9 | in:exactRequestFaultControlEdges,recordedOccurrenceProducerFlows,requestFaultControlEdge+1 | LIVE |
| `RuntimeSelectedRegionFinalizer.stampOccurrenceOwnedPort` | 741-762 | 19 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.declaredOutputPort` | 767-774 | 7 | in:recordedOccurrenceProducerFlows,typedReceivers | LIVE |
| `RuntimeSelectedRegionFinalizer.exchangeOrdinal` | 788-794 | 6 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$exchangeOrdinal$3` | 789-789 | 1 | in:exchangeOrdinal | LIVE |
| `RuntimeSelectedRegionFinalizer.exchangeProducerEdge` | 802-838 | 31 | in:recordedOccurrenceProducerFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.declaredPortIds` | 844-850 | 7 | in:declareCommunicationPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.mintOccurrences` | 863-885 | 17 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.canonicalRuntimeActivations` | 891-915 | 16 | in:mintOccurrences | LIVE |
| `RuntimeSelectedRegionFinalizer.selectedRegion` | 921-923 | 3 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.failureTargetPolicies` | 934-948 | 13 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.activationSourceKey` | 956-957 | 2 | in:exactRequestFaultControlEdges,mintOccurrences,targetRequestProducerSources+1 | LIVE |
| `RuntimeSelectedRegionFinalizer.semanticSourceKey` | 966-979 | 11 | in:mintOccurrences | LIVE |
| `RuntimeSelectedRegionFinalizer.selectedBranchObservation` | 990-1009 | 17 | in:semanticSourceKey | LIVE |
| `RuntimeSelectedRegionFinalizer.orderedBranchObservations` | 1015-1025 | 8 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.bindObservedFatalTargets` | 1036-1098 | 51 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$bindObservedFatalTargets$4` | 1049-1049 | 1 | in:bindObservedFatalTargets | LIVE |
| `RuntimeSelectedRegionFinalizer.isExceptionTargetEdge` | 1101-1102 | 2 | in:branches,failureTargetPolicies | LIVE |
| `RuntimeSelectedRegionFinalizer.failureDirectedClosure` | 1112-1261 | 75 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$failureDirectedClosure$5` | 1207-1207 | 1 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.retainExactRequestFaultControls` | 1273-1287 | 14 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.exactRequestFaultControlEdges` | 1294-1423 | 92 | in:retainExactRequestFaultControls | LIVE |
| `RuntimeSelectedRegionFinalizer.targetRequestProducerSources` | 1441-1469 | 25 | in:exactRequestFaultControlEdges | LIVE |
| `RuntimeSelectedRegionFinalizer.fatalSharedLocationWriters` | 1493-1529 | 32 | in:exactRequestFaultControlEdges | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$fatalSharedLocationWriters$6` | 1508-1508 | 1 | in:fatalSharedLocationWriters | LIVE |
| `RuntimeSelectedRegionFinalizer.requestFaultControlEdge` | 1544-1580 | 33 | in:exactRequestFaultControlEdges | LIVE |
| `RuntimeSelectedRegionFinalizer.sameOptionalValue` | 1586-1589 | 4 | in:exactRequestFaultControlEdges | LIVE |
| `RuntimeSelectedRegionFinalizer.exchangeTransaction` | 1594-1601 | 7 | in:exactRequestFaultControlEdges | LIVE |
| `RuntimeSelectedRegionFinalizer.requestFlowPrefixInputs` | 1614-1656 | 38 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.fatalPrefixCutoff` | 1660-1667 | 7 | in:requestFlowPrefixInputs | LIVE |
| `RuntimeSelectedRegionFinalizer.admitSharedLocationWriters` | 1677-1681 | 5 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.demandDepth` | 1694-1695 | 2 | in:admitWritersOfDemands,transitiveSharedLocationDemand | LIVE |
| `RuntimeSelectedRegionFinalizer.recordDemandDepth` | 1702-1706 | 4 | in:admitWritersOfDemands,transitiveSharedLocationDemand | LIVE |
| `RuntimeSelectedRegionFinalizer.configuredDemandDepthBound` | 1715-1717 | 3 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.configuredDemandDepth` | 1722-1735 | 9 | in:configuredDemandDepthBound | LIVE |
| `RuntimeSelectedRegionFinalizer.caredSharedLocations` | 1763-1796 | 29 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$caredSharedLocations$7` | 1772-1772 | 1 | in:caredSharedLocations | LIVE |
| `RuntimeSelectedRegionFinalizer.symbolicRootEdge` | 1801-1807 | 7 | in:caredSharedLocations | LIVE |
| `RuntimeSelectedRegionFinalizer.declaredFieldLocations` | 1813-1825 | 13 | in:caredSharedLocations | LIVE |
| `RuntimeSelectedRegionFinalizer.recordPrunedDemand` | 1833-1846 | 6 | in:admitWritersOfDemands,transitiveSharedLocationDemand | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$recordPrunedDemand$8` | 1838-1843 | 6 | in:recordPrunedDemand | LIVE |
| `RuntimeSelectedRegionFinalizer.transitiveSharedLocationDemand` | 1883-1927 | 33 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.admitWritersOfDemands` | 1941-2014 | 51 | in:admitSharedLocationWriters,failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$admitWritersOfDemands$9` | 1978-1978 | 1 | in:admitWritersOfDemands | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$admitWritersOfDemands$10` | 1980-1980 | 1 | in:admitWritersOfDemands | LIVE |
| `RuntimeSelectedRegionFinalizer.walkFailureClosure` | 2027-2099 | 26 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$walkFailureClosure$11` | 2066-2096 | 24 | in:walkFailureClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.addRegionPathInputs` | 2113-2118 | 5 | in:lambda$walkFailureClosure$11,walkFailureClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.causalRegionRetentionEdge` | 2126-2128 | 3 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.applyClosure` | 2134-2176 | 32 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$applyClosure$12` | 2139-2140 | 2 | in:applyClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$applyClosure$13` | 2141-2142 | 2 | in:applyClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.filterPorts` | 2185-2206 | 18 | in:applyClosure | LIVE |
| `RuntimeSelectedRegionFinalizer.trimFatalPrefixAccesses` | 2211-2220 | 10 | in:filterPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.retainRuntimeAccesses` | 2226-2240 | 11 | in:filterPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.portId` | 2245-2245 | 1 | in:accessorPorts,explicitFaultPorts,externalCallReturnPorts+1 | LIVE |
| `RuntimeSelectedRegionFinalizer.portDemandKey` | 2251-2251 | 1 | in:access$4700,admitWritersOfDemands,failureDirectedClosure+5 | LIVE |
| `RuntimeSelectedRegionFinalizer.stampEdgeOccurrences` | 2261-2271 | 11 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.recordedRootCallIndex` | 2280-2288 | 8 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.recordedRootCallKey` | 2293-2293 | 1 | in:accessorPorts,canonicalRuntimeActivations,explicitFaultPorts+3 | LIVE |
| `RuntimeSelectedRegionFinalizer.markBoundedContainerStatePorts` | 2299-2328 | 26 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.exactRegionPort` | 2333-2346 | 12 | in:markBoundedContainerStatePorts | LIVE |
| `RuntimeSelectedRegionFinalizer.markBoundedContainerPort` | 2351-2354 | 4 | in:markBoundedContainerStatePorts | LIVE |
| `RuntimeSelectedRegionFinalizer.markBoundedMutationStateFrontiers` | 2362-2415 | 42 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$markBoundedMutationStateFrontiers$14` | 2387-2387 | 1 | in:markBoundedMutationStateFrontiers | LIVE |
| `RuntimeSelectedRegionFinalizer.walkValueSources` | 2425-2425 | 1 | in:markMutationValueFrontiers | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$walkValueSources$15` | 2426-2434 | 9 | in:walkValueSources | LIVE |
| `RuntimeSelectedRegionFinalizer.containerRole` | 2446-2469 | 4 | in:access$3100,statePorts | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$containerRole$16` | 2449-2467 | 16 | in:containerRole | LIVE |
| `RuntimeSelectedRegionFinalizer.markMutationValueFrontiers` | 2479-2508 | 4 | in:markBoundedMutationStateFrontiers | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$markMutationValueFrontiers$17` | 2482-2506 | 19 | in:markMutationValueFrontiers | LIVE |
| `RuntimeSelectedRegionFinalizer.addUniqueValue` | 2512-2516 | 5 | in:lambda$markMutationValueFrontiers$17,statePorts | LIVE |
| `RuntimeSelectedRegionFinalizer.containerMutationPort` | 2520-2530 | 9 | in:access$4900,markBoundedMutationStateFrontiers | LIVE |
| `RuntimeSelectedRegionFinalizer.primitiveValuePort` | 2534-2539 | 6 | in:lambda$markMutationValueFrontiers$17 | LIVE |
| `RuntimeSelectedRegionFinalizer.mutationOutputCells` | 2544-2553 | 9 | in:access$5000,markBoundedMutationStateFrontiers | LIVE |
| `RuntimeSelectedRegionFinalizer.leafDeclaration` | 2558-2561 | 4 | in:primitiveLeaf | LIVE |
| `RuntimeSelectedRegionFinalizer.primitiveLeaf` | 2565-2567 | 3 | in:primitiveValuePort | LIVE |
| `RuntimeSelectedRegionFinalizer.copyRuntimeOccurrence` | 2573-2588 | 9 | in:retainRuntimeAccesses | LIVE |
| `RuntimeSelectedRegionFinalizer.statePorts` | 2594-2650 | 46 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$statePorts$18` | 2645-2645 | 1 | in:statePorts | LIVE |
| `RuntimeSelectedRegionFinalizer.addRuntimeAccess` | 2662-2689 | 17 | in:statePorts | LIVE |
| `RuntimeSelectedRegionFinalizer.staticAccessSiteId` | 2692-2697 | 6 | in:accessorPorts,addRuntimeAccess,exactAccessorReturnEvents+1 | LIVE |
| `RuntimeSelectedRegionFinalizer.accessorPorts` | 2703-2809 | 76 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$accessorPorts$19` | 2729-2729 | 1 | in:accessorPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$accessorPorts$20` | 2731-2732 | 2 | in:accessorPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.externalCallReturnPorts` | 2822-2918 | 77 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$externalCallReturnPorts$21` | 2833-2833 | 1 | in:externalCallReturnPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.exactAccessorReturnEvents` | 2924-2953 | 23 | in:externalCallReturnPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.returnEventKey` | 2959-2959 | 1 | in:exactAccessorReturnEvents,externalCallReturnPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.semanticExternalCallReturnEdges` | 2967-3003 | 11 | in:externalCallReturnPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$semanticExternalCallReturnEdges$22` | 2977-3000 | 22 | in:semanticExternalCallReturnEdges | LIVE |
| `RuntimeSelectedRegionFinalizer.primitiveReturnType` | 3007-3014 | 8 | in:externalCallReturnPorts,lambda$semanticExternalCallReturnEdges$22 | LIVE |
| `RuntimeSelectedRegionFinalizer.explicitFaultPorts` | 3021-3076 | 45 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.callReturnValueCells` | 3083-3100 | 16 | in:declaredCutPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.markLoopControlOnlyInputs` | 3111-3147 | 29 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$markLoopControlOnlyInputs$23` | 3128-3128 | 1 | in:markLoopControlOnlyInputs | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$markLoopControlOnlyInputs$24` | 3139-3140 | 2 | in:markLoopControlOnlyInputs | LIVE |
| `RuntimeSelectedRegionFinalizer.demandScope` | 3157-3173 | 13 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.branches` | 3180-3236 | 46 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$branches$25` | 3181-3181 | 1 | in:branches | LIVE |
| `RuntimeSelectedRegionFinalizer.guardsBySite` | 3243-3253 | 10 | in:branches,failureTargetPolicies | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$guardsBySite$26` | 3250-3250 | 1 | in:guardsBySite | LIVE |
| `RuntimeSelectedRegionFinalizer.operandCells` | 3258-3265 | 8 | in:access$3000,branches | LIVE |
| `RuntimeSelectedRegionFinalizer.guardedSiteOutcomes` | 3274-3306 | 31 | in:branches | LIVE |
| `RuntimeSelectedRegionFinalizer.consistentRequiredOutcome` | 3311-3328 | 16 | in:branches,failureTargetPolicies | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.<init>` | 3332-3332 | 1 | in:branches | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.access$2700` | 3332-3332 | 1 | in:branches | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.access$2800` | 3332-3332 | 1 | in:branches | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.access$2900` | 3332-3332 | 1 | in:branches | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.<init>` | 3336-3338 | 3 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.structuralLoopGuard` | 3342-3346 | 5 | in:access$2800 | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.cfgLoopControlGuard` | 3351-3357 | 6 | in:access$2700 | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.structureCarrierGuard` | 3362-3368 | 5 | in:access$2900 | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.loopRecurrence` | 3373-3389 | 14 | in:structuralLoopGuard | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.hasStructuralSource` | 3393-3423 | 4 | in:structuralLoopGuard | LIVE |
| `RuntimeSelectedRegionFinalizer$BranchPolicyClassifier.lambda$hasStructuralSource$0` | 3396-3421 | 23 | in:hasStructuralSource | LIVE |
| `RuntimeSelectedRegionFinalizer.exactLocalPass` | 3428-3430 | 3 | in:lambda$containerRole$16 | LIVE |
| `RuntimeSelectedRegionFinalizer.fieldFlows` | 3441-3477 | 31 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$fieldFlows$27` | 3447-3448 | 2 | in:fieldFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$fieldFlows$28` | 3464-3464 | 1 | in:fieldFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.fieldFlowEdge` | 3483-3514 | 27 | in:fieldFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.failureRelevantFields` | 3518-3596 | 50 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$failureRelevantFields$29` | 3549-3549 | 1 | in:failureRelevantFields | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$failureRelevantFields$30` | 3560-3571 | 11 | in:failureRelevantFields | LIVE |
| `RuntimeSelectedRegionFinalizer.toolBookkeepingPort` | 3604-3614 | 10 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer.toolBookkeepingField` | 3618-3624 | 7 | in:failureRelevantFields,toolBookkeepingPort | LIVE |
| `RuntimeSelectedRegionFinalizer.contextKey` | 3628-3628 | 1 | in:access$4600,failureRelevantFields,lambda$failureRelevantFields$30 | LIVE |
| `RuntimeSelectedRegionFinalizer.causalHeapPort` | 3633-3636 | 4 | in:collectPorts | LIVE |
| `RuntimeSelectedRegionFinalizer.collectPorts` | 3644-3672 | 23 | in:fieldFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.semanticHeapAddress` | 3682-3712 | 26 | in:collectPorts,lambda$leafReceiverDemand$32 | LIVE |
| `RuntimeSelectedRegionFinalizer.<clinit>` | 3724-3724 | 1 | none | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$static$31` | 3725-3725 | 1 | in:<clinit> | LIVE |
| `RuntimeSelectedRegionFinalizer.planGap` | 3750-3764 | 14 | in:accessorPorts,boundedRuntimeAccesses | LIVE |
| `RuntimeSelectedRegionFinalizer.boundedRuntimeAccesses` | 3770-3808 | 29 | in:collectPorts,retainRuntimeAccesses | LIVE |
| `RuntimeSelectedRegionFinalizer.leafReceiverDemand` | 3817-3824 | 7 | in:fieldFlows | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$leafReceiverDemand$32` | 3825-3832 | 7 | in:leafReceiverDemand | LIVE |
| `RuntimeSelectedRegionFinalizer.sortByEventSeq` | 3838-3840 | 2 | in:access$4800,bindObservedFatalTargets,boundedRuntimeAccesses+2 | LIVE |
| `RuntimeSelectedRegionFinalizer.lambda$sortByEventSeq$33` | 3839-3839 | 1 | in:sortByEventSeq | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.<init>` | 3846-3846 | 1 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.access$1000` | 3846-3846 | 1 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.access$1100` | 3846-3846 | 1 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.access$1200` | 3846-3846 | 1 | in:admitSharedLocationWriters,failureDirectedClosure,walkFailureClosure | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.access$1300` | 3846-3846 | 1 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.access$1400` | 3846-3846 | 1 | in:failureDirectedClosure | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.access$1900` | 3846-3846 | 1 | in:addRegionPathInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.access$2300` | 3846-3846 | 1 | in:markBoundedMutationStateFrontiers,mutationOutputCells | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.access$5100` | 3846-3846 | 1 | in:lambda$walkFailureClosure$11 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.access$5200` | 3846-3846 | 1 | in:lambda$walkFailureClosure$11 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.<init>` | 3847-3945 | 61 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.lambda$new$0` | 3915-3915 | 1 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.lambda$new$1` | 3917-3917 | 1 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.indexPort` | 3949-3973 | 24 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.hasInput` | 3976-3976 | 1 | in:access$1300 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.hasOutput` | 3980-3980 | 1 | in:access$1400 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.communicationInputs` | 3985-3985 | 1 | in:access$5200 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.lambda$communicationInputs$2` | 3986-3987 | 2 | in:communicationInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.valueInputs` | 3992-3992 | 1 | in:computeInputsForOutput | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.lambda$valueInputs$3` | 3993-3994 | 2 | in:valueInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.instanceInputs` | 4000-4006 | 7 | in:communicationInputs,valueInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.targetInputs` | 4011-4017 | 6 | in:access$1200 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.exploredBranchInputs` | 4022-4026 | 4 | in:access$1900 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.observedFatalEvidence` | 4035-4058 | 18 | in:computeTargetInputs,observedExplicitFatalTarget | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.lambda$observedFatalEvidence$4` | 4055-4055 | 1 | in:observedFatalEvidence | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.observedExplicitFatalTarget` | 4073-4073 | 1 | in:access$1100 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.declaresExplicitFatalTarget` | 4079-4081 | 3 | in:access$1000 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.computeTargetInputs` | 4086-4156 | 52 | in:targetInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.selectedFatalOccurrence` | 4162-4172 | 8 | in:computeTargetInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.retainFatalPrefixInputs` | 4183-4207 | 19 | in:computeTargetInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.fatalPrefixEvidence` | 4216-4246 | 25 | in:retainFatalPrefixInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.inputsForOutput` | 4251-4259 | 7 | in:access$5100 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.computeInputsForOutput` | 4264-4281 | 13 | in:inputsForOutput | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.backwardInputs` | 4290-4310 | 4 | in:computeInputsForOutput,computeTargetInputs,exploredBranchInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.lambda$backwardInputs$5` | 4294-4308 | 12 | in:backwardInputs | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.boundaryCells` | 4315-4328 | 10 | in:access$2300,computeInputsForOutput,indexPort | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.instanceCellKey` | 4333-4333 | 1 | in:computeInputsForOutput,indexPort,lambda$backwardInputs$5 | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.addUnique` | 4338-4342 | 4 | in:<init>,indexPort | LIVE |
| `RuntimeSelectedRegionFinalizer$RegionDemandIndex.lambda$addUnique$6` | 4340-4340 | 1 | in:addUnique | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.<init>` | 4345-4345 | 1 | in:collectPorts | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.access$3200` | 4345-4345 | 1 | in:fieldFlows,leafReceiverDemand | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.access$3300` | 4345-4345 | 1 | in:fieldFlowEdge,fieldFlows,lambda$fieldFlows$27+1 | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.access$3400` | 4345-4345 | 1 | in:fieldFlowEdge,fieldFlows | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.access$3500` | 4345-4345 | 1 | in:fieldFlowEdge | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.access$3600` | 4345-4345 | 1 | in:fieldFlowEdge | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.access$3700` | 4345-4345 | 1 | in:fieldFlowEdge | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.access$3800` | 4345-4345 | 1 | in:fieldFlowEdge | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.access$3900` | 4345-4345 | 1 | in:fieldFlowEdge | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.access$4000` | 4345-4345 | 1 | in:fieldFlowEdge | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.<init>` | 4363-4373 | 11 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer$BoundPort.leafDeclaration` | 4376-4377 | 2 | in:access$3300 | LIVE |
| `RuntimeSelectedRegionFinalizer$SemanticHeapAddress.<init>` | 4383-4383 | 1 | in:semanticHeapAddress | LIVE |
| `RuntimeSelectedRegionFinalizer$SemanticHeapAddress.access$4200` | 4383-4383 | 1 | in:collectPorts,lambda$leafReceiverDemand$32 | LIVE |
| `RuntimeSelectedRegionFinalizer$SemanticHeapAddress.access$4300` | 4383-4383 | 1 | in:collectPorts,lambda$leafReceiverDemand$32 | LIVE |
| `RuntimeSelectedRegionFinalizer$SemanticHeapAddress.<init>` | 4388-4391 | 4 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer$DeclaredFieldCell.access$2100` | 4394-4394 | 1 | in:accessorPorts,fieldFlowEdge,markBoundedContainerStatePorts+2 | LIVE |
| `RuntimeSelectedRegionFinalizer$DeclaredFieldCell.access$2200` | 4394-4394 | 1 | in:accessorPorts,markBoundedContainerStatePorts | LIVE |
| `RuntimeSelectedRegionFinalizer$DeclaredFieldCell.access$2400` | 4394-4394 | 1 | in:accessorPorts,primitiveLeaf | LIVE |
| `RuntimeSelectedRegionFinalizer$DeclaredFieldCell.access$2500` | 4394-4394 | 1 | in:accessorPorts,fieldFlowEdge | LIVE |
| `RuntimeSelectedRegionFinalizer$DeclaredFieldCell.access$4100` | 4394-4394 | 1 | in:fieldFlowEdge,toolBookkeepingField | LIVE |
| `RuntimeSelectedRegionFinalizer$DeclaredFieldCell.<clinit>` | 4395-4396 | 2 | none | LIVE |
| `RuntimeSelectedRegionFinalizer$DeclaredFieldCell.<init>` | 4403-4407 | 5 | in:parse | LIVE |
| `RuntimeSelectedRegionFinalizer$DeclaredFieldCell.primitive` | 4410-4410 | 1 | in:access$2400 | LIVE |
| `RuntimeSelectedRegionFinalizer$DeclaredFieldCell.parse` | 4414-4423 | 10 | in:access$2100 | LIVE |
| `RuntimeSelectedRegionFinalizer$ClosureWalk.<init>` | 4428-4428 | 1 | in:walkFailureClosure | LIVE |
| `RuntimeSelectedRegionFinalizer$ClosureWalk.access$1500` | 4428-4428 | 1 | in:applyClosure,failureDirectedClosure,retainExactRequestFaultControls | LIVE |
| `RuntimeSelectedRegionFinalizer$ClosureWalk.access$1600` | 4428-4428 | 1 | in:applyClosure,failureDirectedClosure,retainExactRequestFaultControls | LIVE |
| `RuntimeSelectedRegionFinalizer$ClosureWalk.access$1700` | 4428-4428 | 1 | in:lambda$applyClosure$12,retainExactRequestFaultControls | LIVE |
| `RuntimeSelectedRegionFinalizer$ClosureWalk.access$2000` | 4428-4428 | 1 | in:applyClosure | LIVE |
| `RuntimeSelectedRegionFinalizer$ClosureWalk.<init>` | 4436-4441 | 6 | in:<init> | LIVE |
| `RuntimeSelectedRegionFinalizer$Result.<init>` | 4444-4444 | 1 | in:finalizeRegions | LIVE |
| `RuntimeSelectedRegionFinalizer$Result.<init>` | 4467-4472 | 6 | in:<init> | LIVE |

#### `runtime.RuntimeRegionPlanner` — all 212 methods

| method | lines | body | callers | verdict |
|---|---|---:|---|---|
| `RuntimeRegionPlanner.access$2400` | 60-60 | 1 | in:decode,boundaries,dependencySlice+1 | LIVE |
| `RuntimeRegionPlanner.access$2700` | 60-60 | 1 | in:reachesExplicitSymbolicFault | LIVE |
| `RuntimeRegionPlanner.access$2800` | 60-60 | 1 | in:targetReachSlice | LIVE |
| `RuntimeRegionPlanner.access$3000` | 60-60 | 1 | in:boundaries | LIVE |
| `RuntimeRegionPlanner.access$4100` | 60-60 | 1 | in:runtimePlanJsonl | LIVE |
| `RuntimeRegionPlanner.access$4300` | 60-60 | 1 | in:<init> | LIVE |
| `RuntimeRegionPlanner.<clinit>` | 61-67 | 5 | none | LIVE |
| `RuntimeRegionPlanner.<init>` | 74-75 | 2 | none | DEAD |
| `RuntimeRegionPlanner.planSkeletonGraph` | 85-136 | 34 | EXT:CausynthTraceRecorder.aggregateSkeletonTrace,CausynthTraceRecorder.aggregateStateTrace | LIVE |
| `RuntimeRegionPlanner.stampRecordedExchanges` | 147-217 | 56 | in:planSkeletonGraph | LIVE |
| `RuntimeRegionPlanner.lambda$stampRecordedExchanges$0` | 159-159 | 1 | in:stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner.lambda$stampRecordedExchanges$1` | 202-202 | 1 | in:stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner.retainedLoops` | 223-230 | 7 | in:plan | LIVE |
| `RuntimeRegionPlanner.configuredSourcePhases` | 238-282 | 31 | in:plan | LIVE |
| `RuntimeRegionPlanner.lambda$configuredSourcePhases$2` | 244-244 | 1 | in:configuredSourcePhases | LIVE |
| `RuntimeRegionPlanner.linkOneDelivery` | 289-338 | 46 | in:stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner.stampSynchronousServerTransactions` | 346-441 | 67 | in:stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner.lambda$stampSynchronousServerTransactions$3` | 361-361 | 1 | in:stampSynchronousServerTransactions | LIVE |
| `RuntimeRegionPlanner.lambda$stampSynchronousServerTransactions$4` | 365-365 | 1 | in:stampSynchronousServerTransactions | LIVE |
| `RuntimeRegionPlanner.lambda$stampSynchronousServerTransactions$5` | 369-369 | 1 | in:stampSynchronousServerTransactions | LIVE |
| `RuntimeRegionPlanner.lambda$stampSynchronousServerTransactions$6` | 373-373 | 1 | in:stampSynchronousServerTransactions | LIVE |
| `RuntimeRegionPlanner.lambda$stampSynchronousServerTransactions$7` | 434-434 | 1 | in:stampSynchronousServerTransactions | LIVE |
| `RuntimeRegionPlanner.protocolTransactionKey` | 444-444 | 1 | in:stampSynchronousServerTransactions | LIVE |
| `RuntimeRegionPlanner.stampActivationContainment` | 453-468 | 13 | in:planSkeletonGraph | LIVE |
| `RuntimeRegionPlanner.addSkeletonActivation` | 474-524 | 38 | in:planSkeletonGraph | LIVE |
| `RuntimeRegionPlanner.lambda$addSkeletonActivation$8` | 477-478 | 2 | in:addSkeletonActivation | LIVE |
| `RuntimeRegionPlanner.observedCommunicationCaptures` | 530-555 | 21 | in:addSkeletonActivation | LIVE |
| `RuntimeRegionPlanner.communicationCaptureEvent` | 560-590 | 19 | in:observedCommunicationCaptures | LIVE |
| `RuntimeRegionPlanner.bindObservedCommunicationCaptures` | 598-669 | 53 | in:stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner.lambda$bindObservedCommunicationCaptures$9` | 663-663 | 1 | in:bindObservedCommunicationCaptures | LIVE |
| `RuntimeRegionPlanner.retainInnermostCommunicationCaptureOwners` | 679-728 | 39 | in:stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner.lambda$retainInnermostCommunicationCaptureOwners$10` | 688-688 | 1 | in:retainInnermostCommunicationCaptureOwners | LIVE |
| `RuntimeRegionPlanner.communicationCaptureIdentity` | 732-741 | 8 | in:retainInnermostCommunicationCaptureOwners | LIVE |
| `RuntimeRegionPlanner.retainInnermostCommunicationConsumers` | 779-812 | 28 | in:plan | LIVE |
| `RuntimeRegionPlanner.rootSelectorMethod` | 816-818 | 3 | in:retainInnermostCommunicationConsumers | LIVE |
| `RuntimeRegionPlanner.retainInnermostExactGoalEventOwners` | 823-827 | 3 | in:plan | LIVE |
| `RuntimeRegionPlanner.republishEnclosingActivationIds` | 847-863 | 14 | in:plan | LIVE |
| `RuntimeRegionPlanner.retainInnermostExactGoalEventOwners` | 868-932 | 56 | in:retainInnermostExactGoalEventOwners | LIVE |
| `RuntimeRegionPlanner.lambda$retainInnermostExactGoalEventOwners$11` | 879-879 | 1 | in:retainInnermostExactGoalEventOwners | LIVE |
| `RuntimeRegionPlanner.lambda$retainInnermostExactGoalEventOwners$12` | 906-906 | 1 | in:retainInnermostExactGoalEventOwners | LIVE |
| `RuntimeRegionPlanner.exactBranchEventIdentity` | 937-946 | 9 | in:retainInnermostExactGoalEventOwners | LIVE |
| `RuntimeRegionPlanner.exactMaterializationEventIdentity` | 956-981 | 22 | in:retainInnermostExactGoalEventOwners | LIVE |
| `RuntimeRegionPlanner.validRootAuthority` | 988-994 | 5 | in:planSkeletonGraph | LIVE |
| `RuntimeRegionPlanner.buildFlowIndex` | 1000-1000 | 1 | EXT:CausynthTraceRecorder.aggregateStateTrace | LIVE |
| `RuntimeRegionPlanner.declaredLoopBounds` | 1006-1032 | 16 | in:plan | LIVE |
| `RuntimeRegionPlanner.plan` | 1051-1413 | 204 | EXT:CausynthTraceRecorder.writeRuntimeRegionPlans | LIVE |
| `RuntimeRegionPlanner.declareSharedCarriers` | 1420-1432 | 12 | in:plan | LIVE |
| `RuntimeRegionPlanner.declaredSharedCarriers` | 1437-1450 | 14 | in:declareSharedCarriers | LIVE |
| `RuntimeRegionPlanner.addAccessOwnedCarriers` | 1457-1494 | 21 | in:declaredSharedCarriers | LIVE |
| `RuntimeRegionPlanner.referenceIdentityCarrier` | 1519-1531 | 9 | in:addAccessOwnedCarriers | LIVE |
| `RuntimeRegionPlanner.sharedCarrierRuntimeRole` | 1538-1552 | 11 | in:addAccessOwnedCarriers | LIVE |
| `RuntimeRegionPlanner.addAccessOwnedCarrier` | 1558-1572 | 11 | in:addAccessOwnedCarriers | LIVE |
| `RuntimeRegionPlanner.sharedCarrierKey` | 1575-1580 | 6 | in:addAccessOwnedCarrier | LIVE |
| `RuntimeRegionPlanner.candidateExchangeRow` | 1588-1593 | 6 | in:plan | LIVE |
| `RuntimeRegionPlanner.edgeEvidenceRow` | 1600-1604 | 5 | in:plan | LIVE |
| `RuntimeRegionPlanner.recordEdgeEvidence` | 1616-1627 | 10 | in:plan | LIVE |
| `RuntimeRegionPlanner.appendGoalBinding` | 1631-1645 | 14 | in:recordEdgeEvidence | LIVE |
| `RuntimeRegionPlanner.deepCopyValue` | 1652-1669 | 16 | in:deepCopyValue,plan | LIVE |
| `RuntimeRegionPlanner.toJsonTreeFast` | 1676-1704 | 23 | in:access$4100,accessor,candidateExchangeRow+2 | LIVE |
| `RuntimeRegionPlanner.accessor` | 1709-1710 | 2 | in:symbolize | LIVE |
| `RuntimeRegionPlanner.addIfAllowed` | 1716-1721 | 5 | in:access$2800,addMaterializationMethods | LIVE |
| `RuntimeRegionPlanner.filterByText` | 1726-1732 | 6 | in:plan | LIVE |
| `RuntimeRegionPlanner.targetPathBlockers` | 1737-1754 | 13 | in:plan | LIVE |
| `RuntimeRegionPlanner.eligibleTargetSites` | 1759-1763 | 5 | in:targetBoundaryUpperSeq,targetPathBlockers | LIVE |
| `RuntimeRegionPlanner.guardedTargetCells` | 1769-1774 | 5 | in:targetBoundaryUpperSeq,targetPathBlockers | LIVE |
| `RuntimeRegionPlanner.guardedTargetLabel` | 1779-1781 | 3 | in:targetPathBlockers | LIVE |
| `RuntimeRegionPlanner.selectedTargetCutoff` | 1792-1802 | 10 | in:targetBoundaryUpperSeq,targetPathBlockers | LIVE |
| `RuntimeRegionPlanner.targetBoundaryUpperSeq` | 1810-1818 | 7 | in:plan | LIVE |
| `RuntimeRegionPlanner.exactTargetCutoff` | 1824-1873 | 31 | in:selectedTargetCutoff | LIVE |
| `RuntimeRegionPlanner.observedFailureTargetActivation` | 1879-1885 | 7 | in:plan | LIVE |
| `RuntimeRegionPlanner.eligibleTargetSite` | 1889-1893 | 5 | in:eligibleTargetSites | LIVE |
| `RuntimeRegionPlanner.boundTo` | 1900-1900 | 1 | in:access$2700,registerExactPorts | LIVE |
| `RuntimeRegionPlanner.boundToInput` | 1913-1917 | 4 | in:access$3000,registerExactPorts,symbolize | LIVE |
| `RuntimeRegionPlanner.communicationHandoffSites` | 1924-1945 | 15 | in:plan | LIVE |
| `RuntimeRegionPlanner.communicationHandoffSite` | 1951-1990 | 26 | in:communicationHandoffSites | LIVE |
| `RuntimeRegionPlanner.declaredCutPort` | 1995-1999 | 4 | in:boundToInput,communicationHandoffSites,declareCutPortCells+2 | LIVE |
| `RuntimeRegionPlanner.putTraceContext` | 2013-2020 | 6 | in:addSkeletonActivation,plan | LIVE |
| `RuntimeRegionPlanner.putRecordedTraceIds` | 2042-2043 | 2 | in:addSkeletonActivation | LIVE |
| `RuntimeRegionPlanner.symbolize` | 2057-2126 | 54 | in:plan | LIVE |
| `RuntimeRegionPlanner.declareCutPortCells` | 2131-2142 | 9 | in:plan | LIVE |
| `RuntimeRegionPlanner.occurrenceOwnedCutPortIds` | 2147-2155 | 7 | in:symbolize | LIVE |
| `RuntimeRegionPlanner.declaredCutPortAction` | 2161-2222 | 40 | in:symbolize | LIVE |
| `RuntimeRegionPlanner.effectiveDependencyRole` | 2230-2237 | 6 | in:communicationHandoffSites,declaredCutPortAction,sharedCarrierRuntimeRole+1 | LIVE |
| `RuntimeRegionPlanner.concreteStructureCarrier` | 2246-2254 | 9 | in:effectiveDependencyRole,referenceIdentityCarrier | LIVE |
| `RuntimeRegionPlanner.symbolicLeafType` | 2258-2271 | 11 | in:effectiveDependencyRole | LIVE |
| `RuntimeRegionPlanner.addMaterializationMethods` | 2277-2285 | 9 | in:plan | LIVE |
| `RuntimeRegionPlanner.addFieldAccessIdentity` | 2290-2302 | 11 | in:symbolize | LIVE |
| `RuntimeRegionPlanner.registerExactPorts` | 2308-2311 | 3 | in:plan | LIVE |
| `RuntimeRegionPlanner.registerExactPorts` | 2317-2332 | 13 | in:registerExactPorts | LIVE |
| `RuntimeRegionPlanner.exactPort` | 2337-2345 | 6 | in:plan | LIVE |
| `RuntimeRegionPlanner.exactPortKey` | 2350-2350 | 1 | in:exactPort,registerExactPorts | LIVE |
| `RuntimeRegionPlanner.branches` | 2357-2412 | 42 | in:plan | LIVE |
| `RuntimeRegionPlanner.lambda$branches$13` | 2361-2361 | 1 | in:branches | LIVE |
| `RuntimeRegionPlanner.addExactSwitchDecision` | 2419-2442 | 16 | in:branches | LIVE |
| `RuntimeRegionPlanner.parseSwitchCaseKeys` | 2445-2459 | 9 | in:addExactSwitchDecision | LIVE |
| `RuntimeRegionPlanner.rootSelector` | 2468-2479 | 10 | in:plan | LIVE |
| `RuntimeRegionPlanner.causalAnchor` | 2503-2520 | 8 | in:rootSelector | LIVE |
| `RuntimeRegionPlanner.replayInvocationScope` | 2543-2544 | 2 | in:plan | LIVE |
| `RuntimeRegionPlanner.stampedSources` | 2557-2568 | 12 | in:addSkeletonActivation,plan | LIVE |
| `RuntimeRegionPlanner.lambda$stampedSources$14` | 2562-2562 | 1 | in:stampedSources | LIVE |
| `RuntimeRegionPlanner.activationSource` | 2584-2584 | 1 | in:addSkeletonActivation,plan | LIVE |
| `RuntimeRegionPlanner.sourceOf` | 2593-2593 | 1 | in:<init>,putTraceContext | LIVE |
| `RuntimeRegionPlanner.relationKey` | 2599-2599 | 1 | in:plan | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.<init>` | 2617-2825 | 4 | in:build | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.access$1100` | 2617-2617 | 1 | in:buildFlowIndex | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.access$1300` | 2617-2617 | 1 | in:plan | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.addEdge` | 2626-2641 | 13 | in:build | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.lambda$addEdge$0` | 2628-2628 | 1 | in:addEdge | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.lambda$addEdge$1` | 2630-2630 | 1 | in:addEdge | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.lambda$addEdge$2` | 2637-2637 | 1 | in:addEdge | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.build` | 2648-2662 | 12 | in:access$1100 | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.dependencySlice` | 2677-2735 | 42 | in:targetReachSlice | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.reachesExplicitSymbolicFault` | 2741-2751 | 9 | in:dependencySlice | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.targetReachSlice` | 2762-2790 | 25 | in:access$1300 | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.controlsSelectedCell` | 2799-2819 | 15 | in:dependencySlice | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex$Boundaries.<init>` | 2828-2831 | 3 | in:<init> | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex$Boundaries.<init>` | 2828-2828 | 1 | in:boundaries | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex$Boundaries.access$3100` | 2828-2828 | 1 | in:backwardSlice,boundaries | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex$Boundaries.access$3200` | 2828-2828 | 1 | in:backwardSlice,boundaries | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.boundaries` | 2838-2862 | 21 | in:backwardSlice | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.lambda$boundaries$3` | 2840-2840 | 1 | in:boundaries | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.backwardSlice` | 2871-2930 | 50 | in:dependencySlice | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.enqueueSlice` | 2937-2940 | 4 | in:backwardSlice | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.addSlicePath` | 2945-2953 | 9 | in:backwardSlice | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.registerBoundary` | 2958-2961 | 4 | in:boundaries | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.lambda$registerBoundary$4` | 2960-2960 | 1 | in:registerBoundary | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.selectBoundaries` | 2967-2989 | 17 | in:backwardSlice | LIVE |
| `RuntimeRegionPlanner$RefinedFlowIndex.returnValueTransfer` | 2993-3000 | 8 | in:backwardSlice | LIVE |
| `RuntimeRegionPlanner$FlowEdge.access$1700` | 3005-3005 | 1 | in:addEdge | LIVE |
| `RuntimeRegionPlanner$FlowEdge.access$1800` | 3005-3005 | 1 | in:addEdge,add | LIVE |
| `RuntimeRegionPlanner$FlowEdge.access$1900` | 3005-3005 | 1 | in:addEdge,backwardSlice,add | LIVE |
| `RuntimeRegionPlanner$FlowEdge.access$2000` | 3005-3005 | 1 | in:addEdge,backwardSlice,add | LIVE |
| `RuntimeRegionPlanner$FlowEdge.access$2100` | 3005-3005 | 1 | in:addEdge,backwardSlice | LIVE |
| `RuntimeRegionPlanner$FlowEdge.access$2200` | 3005-3005 | 1 | in:build | LIVE |
| `RuntimeRegionPlanner$FlowEdge.access$3500` | 3005-3005 | 1 | in:backwardSlice,add | LIVE |
| `RuntimeRegionPlanner$FlowEdge.access$4000` | 3005-3005 | 1 | in:add | LIVE |
| `RuntimeRegionPlanner$FlowEdge.<init>` | 3017-3025 | 9 | in:decode | LIVE |
| `RuntimeRegionPlanner$FlowEdge.decode` | 3028-3037 | 9 | in:access$2200 | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.<init>` | 3041-3046 | 6 | in:<init> | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.<init>` | 3041-3041 | 1 | in:backwardSlice,dependencySlice,targetReachSlice | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.access$1400` | 3041-3041 | 1 | in:backwardSlice,dependencySlice,plan | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.access$1500` | 3041-3041 | 1 | in:dependencySlice,targetReachSlice,plan | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.access$1600` | 3041-3041 | 1 | in:dependencySlice,targetReachSlice,plan | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.access$2300` | 3041-3041 | 1 | in:backwardSlice,dependencySlice | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.access$2600` | 3041-3041 | 1 | in:dependencySlice,targetReachSlice | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.access$3700` | 3041-3041 | 1 | in:addSlicePath | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.add` | 3049-3056 | 8 | in:access$3700 | LIVE |
| `RuntimeRegionPlanner$ReturnSlice.merge` | 3059-3064 | 6 | in:access$2600 | LIVE |
| `RuntimeRegionPlanner$SliceNode.<init>` | 3067-3067 | 1 | in:backwardSlice | LIVE |
| `RuntimeRegionPlanner$SliceNode.access$3400` | 3067-3067 | 1 | in:backwardSlice | LIVE |
| `RuntimeRegionPlanner$SliceNode.<init>` | 3070-3072 | 3 | in:<init> | LIVE |
| `RuntimeRegionPlanner$SliceNode.equals` | 3076-3079 | 4 | in:addSlicePath | LIVE |
| `RuntimeRegionPlanner$SliceNode.hashCode` | 3084-3084 | 1 | none | LIVE |
| `RuntimeRegionPlanner$SliceStep.<init>` | 3088-3088 | 1 | in:enqueueSlice | LIVE |
| `RuntimeRegionPlanner$SliceStep.access$3800` | 3088-3088 | 1 | in:addSlicePath | LIVE |
| `RuntimeRegionPlanner$SliceStep.access$3900` | 3088-3088 | 1 | in:addSlicePath | LIVE |
| `RuntimeRegionPlanner$SliceStep.<init>` | 3092-3095 | 4 | in:<init> | LIVE |
| `RuntimeRegionPlanner.recordedActivationKey` | 3111-3113 | 2 | in:addSkeletonActivation | LIVE |
| `RuntimeRegionPlanner.activationId` | 3134-3136 | 3 | in:plan | LIVE |
| `RuntimeRegionPlanner.canonicalIdentity` | 3148-3150 | 3 | in:activationId | LIVE |
| `RuntimeRegionPlanner.appendCanonicalIdentity` | 3155-3179 | 22 | in:appendCanonicalIdentity,canonicalIdentity | LIVE |
| `RuntimeRegionPlanner.leafType` | 3182-3187 | 5 | in:symbolize | LIVE |
| `RuntimeRegionPlanner.strings` | 3193-3201 | 7 | in:access$2400,addAccessOwnedCarriers,addFieldAccessIdentity+8 | LIVE |
| `RuntimeRegionPlanner.sorted` | 3208-3211 | 4 | in:access$4300 | LIVE |
| `RuntimeRegionPlanner$Result.<init>` | 3214-3222 | 7 | in:plan,planSkeletonGraph | LIVE |
| `RuntimeRegionPlanner$Result.runtimePlanJsonl` | 3226-3242 | 17 | EXT:CausynthTraceRecorder.writeRuntimeRegionPlans | LIVE |
| `RuntimeRegionPlanner$MethodEvent.<init>` | 3298-3302 | 2 | EXT:CausynthTraceRecorder.enterMethod,CausynthTraceRecorder.enterMethodLite | LIVE |
| `RuntimeRegionPlanner$MethodEvent.<init>` | 3311-3333 | 23 | EXT:CausynthTraceRecorder.parseTraceLine; in:<init> | LIVE |
| `RuntimeRegionPlanner$MethodEvent.reattribute` | 3346-3358 | 9 | EXT:CausynthTraceRecorder.reattributeFramesToRegisteredOwners | LIVE |
| `RuntimeRegionPlanner$ProtocolEvent.<init>` | 3390-3410 | 21 | EXT:CausynthTraceRecorder.parseTraceLine,CausynthTraceRecorder.recordExchange | LIVE |
| `RuntimeRegionPlanner$ProtocolEvent.exchangeLeg` | 3414-3414 | 1 | in:bindObservedCommunicationCaptures,stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner.exchangeLeg` | 3421-3424 | 4 | in:exchangeLeg | LIVE |
| `RuntimeRegionPlanner$RuntimeEvent.<init>` | 3450-3466 | 17 | EXT:CausynthTraceRecorder.parseTraceLine | LIVE |
| `RuntimeRegionPlanner$FieldAccessEvent.<init>` | 3486-3498 | 13 | EXT:CausynthTraceRecorder.parseTraceLine,CausynthTraceRecorder.recordField,RuntimeRefinedGraphBuilder.refine | LIVE |
| `RuntimeRegionPlanner$ArrayAccessEvent.<init>` | 3514-3525 | 12 | EXT:CausynthTraceRecorder.recordArrayElement | LIVE |
| `RuntimeRegionPlanner$LongLongMap.<init>` | 3529-3532 | 3 | in:<init> | LIVE |
| `RuntimeRegionPlanner$LongLongMap.<init>` | 3529-3529 | 1 | in:<init> | LIVE |
| `RuntimeRegionPlanner$LongLongMap.access$1000` | 3529-3529 | 1 | in:selectedTargetContext,exactBranchEventIdentity,exactMaterializationEventIdentity | LIVE |
| `RuntimeRegionPlanner$LongLongMap.access$4400` | 3529-3529 | 1 | in:registerEventCall | LIVE |
| `RuntimeRegionPlanner$LongLongMap.register` | 3537-3557 | 16 | in:access$4400 | LIVE |
| `RuntimeRegionPlanner$LongLongMap.uniqueValue` | 3562-3571 | 8 | in:access$1000 | LIVE |
| `RuntimeRegionPlanner$LongLongMap.grow` | 3575-3590 | 14 | in:register | LIVE |
| `RuntimeRegionPlanner$LongLongMap.mix` | 3593-3594 | 2 | in:grow,register,uniqueValue | LIVE |
| `RuntimeRegionPlanner$TraceIndex.<init>` | 3598-3598 | 1 | in:plan,planSkeletonGraph | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$100` | 3598-3598 | 1 | in:planSkeletonGraph | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$1200` | 3598-3598 | 1 | in:plan | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$200` | 3598-3598 | 1 | in:addSkeletonActivation,configuredSourcePhases,plan+1 | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$300` | 3598-3598 | 1 | in:addSkeletonActivation,plan,planSkeletonGraph | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$400` | 3598-3598 | 1 | in:stampActivationContainment,stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$500` | 3598-3598 | 1 | in:stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$600` | 3598-3598 | 1 | in:stampRecordedExchanges | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$700` | 3598-3598 | 1 | in:configuredSourcePhases,observedCommunicationCaptures,plan | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$800` | 3598-3598 | 1 | in:configuredSourcePhases,lambda$addSkeletonActivation$8,plan+2 | LIVE |
| `RuntimeRegionPlanner$TraceIndex.access$900` | 3598-3598 | 1 | in:exactBranchEventIdentity,exactMaterializationEventIdentity | LIVE |
| `RuntimeRegionPlanner$TraceIndex.<init>` | 3600-3637 | 26 | in:<init> | LIVE |
| `RuntimeRegionPlanner$TraceIndex.lambda$new$0` | 3615-3615 | 1 | in:<init> | LIVE |
| `RuntimeRegionPlanner$TraceIndex.lambda$new$1` | 3619-3619 | 1 | in:<init> | LIVE |
| `RuntimeRegionPlanner$TraceIndex.lambda$new$2` | 3621-3621 | 1 | in:<init> | LIVE |
| `RuntimeRegionPlanner$TraceIndex.lambda$new$3` | 3624-3624 | 1 | in:<init> | LIVE |
| `RuntimeRegionPlanner$TraceIndex.lambda$new$4` | 3626-3626 | 1 | in:<init> | LIVE |
| `RuntimeRegionPlanner$TraceIndex.lambda$new$5` | 3630-3630 | 1 | in:<init> | LIVE |
| `RuntimeRegionPlanner$TraceIndex.lambda$new$6` | 3634-3634 | 1 | in:<init> | LIVE |
| `RuntimeRegionPlanner$TraceIndex.registerEventCall` | 3640-3642 | 3 | in:<init> | LIVE |
| `RuntimeRegionPlanner$TraceIndex.methods` | 3645-3646 | 2 | in:access$100 | LIVE |
| `RuntimeRegionPlanner$TraceIndex.subtree` | 3650-3660 | 10 | in:access$200 | LIVE |
| `RuntimeRegionPlanner$TraceIndex.methodNames` | 3664-3669 | 6 | in:access$300 | LIVE |
| `RuntimeRegionPlanner$TraceIndex.enclosingCalls` | 3674-3679 | 5 | in:access$400 | LIVE |
| `RuntimeRegionPlanner$TraceIndex.callSiteId` | 3685-3693 | 8 | in:access$500,entrySiteId | LIVE |
| `RuntimeRegionPlanner$TraceIndex.entrySiteId` | 3698-3700 | 3 | in:access$600 | LIVE |
| `RuntimeRegionPlanner$TraceIndex.runtime` | 3705-3711 | 7 | in:access$700 | LIVE |
| `RuntimeRegionPlanner$TraceIndex.lambda$runtime$7` | 3710-3710 | 1 | in:runtime | LIVE |
| `RuntimeRegionPlanner$TraceIndex.selectedTargetContext` | 3717-3729 | 11 | in:access$1200 | LIVE |

#### `causynth.CausynthPipeline` — all 180 methods

| method | lines | body | callers | verdict |
|---|---|---:|---|---|
| `CausynthPipeline$MethodEmitter.emit` | 0-0 | 0 | in:instrumentMethods | LIVE |
| `CausynthPipeline$PrimitiveMaterializer.invoke` | 0-0 | 0 | in:addPrimitiveRoundTrip | LIVE |
| `CausynthPipeline.access$200` | 81-81 | 1 | in:tagSelectedBodies | LIVE |
| `CausynthPipeline.access$300` | 81-81 | 1 | in:tagSelectedBodies | LIVE |
| `CausynthPipeline.access$3000` | 81-81 | 1 | in:bracket | LIVE |
| `CausynthPipeline.access$3100` | 81-81 | 1 | in:bracket | LIVE |
| `CausynthPipeline.access$3200` | 81-81 | 1 | in:concolic,trace | LIVE |
| `CausynthPipeline.access$400` | 81-81 | 1 | in:boundSelectedLoops,report | LIVE |
| `CausynthPipeline.access$500` | 81-81 | 1 | in:freezeRootLoops | LIVE |
| `CausynthPipeline.<clinit>` | 82-82 | 1 | none | LIVE |
| `CausynthPipeline.<init>` | 88-90 | 3 | EXT:GraphCheckerTransformer.internalTransform | LIVE |
| `CausynthPipeline.run` | 94-99 | 4 | EXT:GraphCheckerTransformer.internalTransform | LIVE |
| `CausynthPipeline.analyze` | 102-156 | 39 | in:run | LIVE |
| `CausynthPipeline.elapsedMillis` | 159-159 | 1 | in:analyze | LIVE |
| `CausynthPipeline.instrumentMethods` | 177-205 | 23 | in:instrumentConcolicBranches,instrumentConcolicMaterializations,instrumentConcolicMethodArguments+2 | LIVE |
| `CausynthPipeline.namedRefusal` | 210-214 | 5 | in:instrumentMethods | LIVE |
| `CausynthPipeline.instrumentableFrom` | 231-235 | 4 | in:instrumentLiteMethod,instrumentRichMethod,lambda$instrumentConcolicMaterializations$5 | LIVE |
| `CausynthPipeline.instrumentRuntimeState` | 240-257 | 8 | in:analyze | LIVE |
| `CausynthPipeline.lambda$instrumentRuntimeState$0` | 247-253 | 4 | in:instrumentRuntimeState | LIVE |
| `CausynthPipeline.skeletonCandidateMethods` | 261-276 | 14 | in:instrumentRegionSkeletonTrace | LIVE |
| `CausynthPipeline.instrumentRegionSkeletonTrace` | 303-339 | 18 | in:analyze | LIVE |
| `CausynthPipeline.lambda$instrumentRegionSkeletonTrace$1` | 312-316 | 4 | in:instrumentRegionSkeletonTrace | LIVE |
| `CausynthPipeline.annotatedTargetMethod` | 343-347 | 4 | in:instrumentRegionSkeletonTrace | LIVE |
| `CausynthPipeline$CampaignEnvelope.<init>` | 351-351 | 1 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$1000` | 351-351 | 1 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$1100` | 351-351 | 1 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$1200` | 351-351 | 1 | in:instrumentConcolicCampaign,instrumentConcolicMaterializations | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$1300` | 351-351 | 1 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$1400` | 351-351 | 1 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$1500` | 351-351 | 1 | in:instrumentConcolicRegion | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$1600` | 351-351 | 1 | in:instrumentConcolicRegion | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$2500` | 351-351 | 1 | in:instrumentConcolicMaterializations | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$3308` | 351-351 | 1 | in:lambda$instrumentConcolicMaterializations$5 | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$3400` | 351-351 | 1 | in:lambda$instrumentConcolicMaterializations$5 | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$3508` | 351-351 | 1 | in:lambda$instrumentConcolicMaterializations$5 | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$800` | 351-351 | 1 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline$CampaignEnvelope.access$900` | 351-351 | 1 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline$CampaignEnvelope.<init>` | 353-442 | 52 | in:<init> | LIVE |
| `CausynthPipeline$CampaignEnvelope.declaredReplayEntry` | 446-450 | 4 | in:<init> | LIVE |
| `CausynthPipeline$CampaignEnvelope.tagSelectedBodies` | 459-470 | 10 | in:access$800 | LIVE |
| `CausynthPipeline$CampaignEnvelope.boundSelectedLoops` | 474-482 | 6 | in:access$900 | LIVE |
| `CausynthPipeline$CampaignEnvelope.replayEntry` | 485-485 | 1 | in:access$1500 | LIVE |
| `CausynthPipeline$CampaignEnvelope.freezeRootLoops` | 494-508 | 13 | in:access$1000 | LIVE |
| `CausynthPipeline$CampaignEnvelope.rootLoop` | 512-518 | 5 | in:access$1600 | LIVE |
| `CausynthPipeline$CampaignEnvelope.loopRootKey` | 522-523 | 2 | in:freezeRootLoops,rootLoop | LIVE |
| `CausynthPipeline$CampaignEnvelope.refuseStaticFieldMaterialization` | 536-538 | 2 | in:access$3400 | LIVE |
| `CausynthPipeline$CampaignEnvelope.staticFieldCoverageGaps` | 542-549 | 7 | in:report | LIVE |
| `CausynthPipeline$CampaignEnvelope.report` | 554-579 | 13 | in:access$1400 | LIVE |
| `CausynthPipeline.selectedCarrierWriterMethods` | 585-608 | 22 | in:<init> | LIVE |
| `CausynthPipeline.instrumentConcolicCampaign` | 617-634 | 17 | in:analyze | LIVE |
| `CausynthPipeline.instrumentConcolicRegion` | 643-778 | 85 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline.instrumentLoopRootInvocationContext` | 788-849 | 47 | in:instrumentConcolicRegion | LIVE |
| `CausynthPipeline.rootedLoop` | 860-899 | 23 | in:access$500 | LIVE |
| `CausynthPipeline.lambda$rootedLoop$2` | 881-881 | 1 | in:rootedLoop | LIVE |
| `CausynthPipeline.loopBodyEntry` | 921-992 | 44 | in:instrumentConcolicRegion | LIVE |
| `CausynthPipeline.stableLoopUnit` | 999-1009 | 9 | in:loopBodyEntry | LIVE |
| `CausynthPipeline.resolveLoopControls` | 1016-1060 | 32 | in:loopBodyClosingEdges,loopBodyEntry | LIVE |
| `CausynthPipeline$ResolvedLoopControls.<init>` | 1063-1063 | 1 | in:resolveLoopControls | LIVE |
| `CausynthPipeline$ResolvedLoopControls.access$1800` | 1063-1063 | 1 | in:loopBodyEntry | LIVE |
| `CausynthPipeline$ResolvedLoopControls.access$1900` | 1063-1063 | 1 | in:loopBodyClosingEdges,loopBodyEntry | LIVE |
| `CausynthPipeline$ResolvedLoopControls.<init>` | 1068-1071 | 4 | in:<init> | LIVE |
| `CausynthPipeline.currentLoopBoundaryEdge` | 1082-1129 | 31 | in:loopBodyClosingEdges,loopBodyEntry | LIVE |
| `CausynthPipeline.insertLoopBodyEntry` | 1139-1199 | 39 | in:instrumentConcolicRegion | LIVE |
| `CausynthPipeline.normalSuccessors` | 1204-1213 | 8 | in:currentLoopBoundaryEdge | LIVE |
| `CausynthPipeline.loopBodyClosingEdges` | 1234-1271 | 28 | in:insertLoopBodyRegionExits | LIVE |
| `CausynthPipeline.insertLoopBodyRegionExits` | 1280-1295 | 14 | in:instrumentConcolicRegion | LIVE |
| `CausynthPipeline.insertLoopBodyExit` | 1305-1313 | 5 | in:insertLoopBodyRegionExits | LIVE |
| `CausynthPipeline.materializeParameter` | 1320-1343 | 18 | in:instrumentConcolicRegion,lambda$instrumentConcolicMethodArguments$6 | LIVE |
| `CausynthPipeline.lambda$materializeParameter$3` | 1325-1327 | 3 | in:materializeParameter | LIVE |
| `CausynthPipeline.instrumentConcolicCommunicationHandoffs` | 1347-1375 | 24 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline.instrumentCommunicationFrame` | 1392-1436 | 30 | in:instrumentConcolicCommunicationHandoffs | LIVE |
| `CausynthPipeline.instrumentCommunicationHandoff` | 1440-1503 | 51 | in:instrumentConcolicCommunicationHandoffs | LIVE |
| `CausynthPipeline.cutInvoke` | 1506-1520 | 13 | in:instrumentCommunicationHandoff | LIVE |
| `CausynthPipeline.addCommunicationHandoff` | 1527-1545 | 15 | in:instrumentCommunicationHandoff | LIVE |
| `CausynthPipeline.handoffFailure` | 1550-1551 | 2 | in:cutInvoke,instrumentCommunicationHandoff | LIVE |
| `CausynthPipeline.newCarrierLeaf` | 1557-1572 | 16 | in:addCommunicationHandoff,addCommunicationLeafAttach | LIVE |
| `CausynthPipeline.readCarrierLeaf` | 1578-1581 | 4 | in:addCommunicationLeafAttach | LIVE |
| `CausynthPipeline.carrierLeaf` | 1586-1588 | 3 | in:addCommunicationHandoff,addCommunicationLeafAttach | LIVE |
| `CausynthPipeline.carrierLeafType` | 1593-1594 | 2 | in:newCarrierLeaf,readCarrierLeaf | LIVE |
| `CausynthPipeline.carrierClass` | 1601-1601 | 1 | in:newCarrierLeaf,readCarrierLeaf | LIVE |
| `CausynthPipeline.addCommunicationLeafAttach` | 1608-1624 | 15 | in:addCommunicationHandoff | LIVE |
| `CausynthPipeline.instrumentConcolicConfiguredSourceCallContexts` | 1633-1706 | 53 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline.instrumentConcolicAccessorCallContexts` | 1715-1819 | 62 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline.instrumentConcolicMaterializations` | 1824-1965 | 5 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline.lambda$instrumentConcolicMaterializations$5` | 1830-1964 | 95 | in:instrumentConcolicMaterializations | LIVE |
| `CausynthPipeline.lambda$null$4` | 1954-1958 | 5 | in:lambda$instrumentConcolicMaterializations$5 | LIVE |
| `CausynthPipeline.associativeReadInvoke` | 1968-1982 | 13 | in:lambda$instrumentConcolicMaterializations$5 | LIVE |
| `CausynthPipeline.instrumentConcolicMethodArguments` | 1991-2020 | 7 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline.lambda$instrumentConcolicMethodArguments$6` | 1994-2012 | 12 | in:instrumentConcolicMethodArguments | LIVE |
| `CausynthPipeline.instrumentConsumedStaticPrimitiveFieldRead` | 2029-2060 | 21 | in:lambda$instrumentConcolicMaterializations$5 | LIVE |
| `CausynthPipeline.lambda$instrumentConsumedStaticPrimitiveFieldRead$7` | 2050-2055 | 6 | in:instrumentConsumedStaticPrimitiveFieldRead | LIVE |
| `CausynthPipeline.addPrimitiveRoundTrip` | 2067-2092 | 24 | in:instrumentConsumedStaticPrimitiveFieldRead,lambda$instrumentConcolicMaterializations$5,materializeParameter | LIVE |
| `CausynthPipeline.originalUnitIndex` | 2101-2106 | 5 | in:addLoopControlSite,currentLoopBoundaryEdge,cutInvoke+7 | LIVE |
| `CausynthPipeline.instrumentConcolicLoopBounds` | 2128-2230 | 72 | in:boundSelectedLoops | LIVE |
| `CausynthPipeline.naturalLoopHasSite` | 2236-2242 | 6 | in:instrumentConcolicLoopBounds | LIVE |
| `CausynthPipeline.naturalLoopBodyBound` | 2249-2281 | 20 | in:instrumentConcolicLoopBounds | LIVE |
| `CausynthPipeline.retainedLoopSiteId` | 2287-2300 | 11 | in:naturalLoopBodyBound | LIVE |
| `CausynthPipeline.naturalLoopControlSites` | 2306-2314 | 9 | in:naturalLoopBodyBound,naturalLoopHasSite | LIVE |
| `CausynthPipeline.addLoopControlSite` | 2319-2323 | 4 | in:naturalLoopControlSites,retainedLoopSiteId | LIVE |
| `CausynthPipeline.continuationEdges` | 2328-2354 | 17 | in:instrumentConcolicLoopBounds | LIVE |
| `CausynthPipeline.continuationEdgesFrom` | 2359-2373 | 12 | in:continuationEdges | LIVE |
| `CausynthPipeline.deduplicateEdges` | 2378-2390 | 11 | in:continuationEdges,continuationEdgesFrom,currentLoopBoundaryEdge+3 | LIVE |
| `CausynthPipeline.removeEdge` | 2395-2403 | 7 | in:instrumentConcolicLoopBounds | LIVE |
| `CausynthPipeline.splitCfgEdge` | 2410-2415 | 5 | in:instrumentConcolicLoopBounds | LIVE |
| `CausynthPipeline.splitStringHookEdge` | 2421-2424 | 3 | in:instrumentConcolicLoopBounds | LIVE |
| `CausynthPipeline.redirectEdge` | 2430-2457 | 23 | in:insertLoopBodyExit,splitCfgEdge,splitStringHookEdge | LIVE |
| `CausynthPipeline.instrumentConcolicBranches` | 2461-2482 | 2 | in:instrumentConcolicCampaign | LIVE |
| `CausynthPipeline.lambda$instrumentConcolicBranches$8` | 2463-2481 | 15 | in:instrumentConcolicBranches | LIVE |
| `CausynthPipeline.instrumentConcolicBranch` | 2487-2533 | 33 | in:lambda$instrumentConcolicBranches$8 | LIVE |
| `CausynthPipeline.instrumentConcolicSwitch` | 2538-2585 | 32 | in:lambda$instrumentConcolicBranches$8 | LIVE |
| `CausynthPipeline.insertExactBranchMarkerPrefix` | 2593-2617 | 22 | in:instrumentConcolicBranch,instrumentConcolicSwitch | LIVE |
| `CausynthPipeline.originalUnit` | 2620-2640 | 14 | in:lambda$instrumentConcolicBranches$8,rootedLoop,stableLoopUnit | LIVE |
| `CausynthPipeline.insertRegionExit` | 2646-2652 | 7 | in:instrumentConcolicRegion | LIVE |
| `CausynthPipeline.snapshotUnits` | 2655-2659 | 5 | in:access$200,cutInvoke,instrumentCommunicationFrame+9 | LIVE |
| `CausynthPipeline.tagOriginalUnits` | 2664-2675 | 10 | in:access$300,instrumentConcolicAccessorCallContexts,instrumentConcolicLoopBounds+2 | LIVE |
| `CausynthPipeline.concreteSelected` | 2681-2688 | 6 | in:instrumentCommunicationFrame,instrumentCommunicationHandoff,instrumentConcolicConfiguredSourceCallContexts | LIVE |
| `CausynthPipeline.uniqueOriginalStmt` | 2694-2702 | 8 | in:instrumentConcolicAccessorCallContexts,instrumentConcolicConfiguredSourceCallContexts | LIVE |
| `CausynthPipeline.parameterLocal` | 2708-2710 | 3 | in:instrumentConcolicRegion,instrumentLoopRootInvocationContext,instrumentRichMethod | LIVE |
| `CausynthPipeline.receiverOrNull` | 2716-2723 | 6 | in:instrumentConcolicRegion,instrumentFieldTrace,instrumentLoopRootInvocationContext+1 | LIVE |
| `CausynthPipeline.phantomClass` | 2729-2736 | 7 | in:access$3200,carrierClass | LIVE |
| `CausynthPipeline.instrumentLiteMethod` | 2744-2764 | 14 | in:lambda$instrumentRegionSkeletonTrace$1 | LIVE |
| `CausynthPipeline.instrumentRichMethod` | 2771-2819 | 35 | in:lambda$instrumentRuntimeState$0 | LIVE |
| `CausynthPipeline.instrumentCallSite` | 2824-2855 | 27 | in:instrumentRichMethod | LIVE |
| `CausynthPipeline.runtimeCallSiteReceiver` | 2859-2863 | 4 | in:instrumentCallSite | LIVE |
| `CausynthPipeline.runtimeCallSiteReturnValue` | 2872-2877 | 5 | in:instrumentCallSite,instrumentConcolicConfiguredSourceCallContexts | LIVE |
| `CausynthPipeline.conservativeDispatchTargets` | 2882-2882 | 1 | EXT:SeedBackwardStaticAnalyzer.processDispatchInvoke | LIVE |
| `CausynthPipeline.instrumentBranch` | 2889-2913 | 24 | in:instrumentRichMethod | LIVE |
| `CausynthPipeline.instrumentSwitchBranch` | 2918-2941 | 21 | in:instrumentRichMethod | LIVE |
| `CausynthPipeline.insertMethodExit` | 2945-2950 | 6 | in:instrumentRichMethod | LIVE |
| `CausynthPipeline.addThrowHandler` | 2962-2985 | 19 | in:instrumentConcolicRegion,instrumentLiteMethod,instrumentLoopRootInvocationContext+1 | LIVE |
| `CausynthPipeline.isRecorderInvoke` | 2988-2990 | 3 | in:instrumentRichMethod | LIVE |
| `CausynthPipeline.insertBeforeSequence` | 2995-2998 | 4 | in:insertExactBranchMarkerPrefix,insertFieldTrace,insertMethodExit+8 | LIVE |
| `CausynthPipeline.insertBeforeOrAppendNoRedirect` | 3002-3011 | 9 | in:insertLoopBodyEntry,instrumentCommunicationFrame,instrumentCommunicationHandoff+5 | LIVE |
| `CausynthPipeline.insertAfterSequence` | 3015-3020 | 6 | in:insertArrayTrace,insertFieldTrace,instrumentBranch+7 | LIVE |
| `CausynthPipeline.instrumentFieldTrace` | 3026-3061 | 27 | in:lambda$instrumentRuntimeState$0 | LIVE |
| `CausynthPipeline.instrumentReferenceArrayTrace` | 3067-3089 | 18 | in:lambda$instrumentRuntimeState$0 | LIVE |
| `CausynthPipeline.referenceArrayElement` | 3092-3093 | 2 | in:instrumentReferenceArrayTrace | LIVE |
| `CausynthPipeline.insertArrayTrace` | 3099-3107 | 8 | in:instrumentReferenceArrayTrace | LIVE |
| `CausynthPipeline.insertFieldTrace` | 3114-3138 | 20 | in:instrumentFieldTrace | LIVE |
| `CausynthPipeline.objectArg` | 3141-3147 | 5 | in:insertArrayTrace,insertFieldTrace,insertMethodExit+8 | LIVE |
| `CausynthPipeline.primitiveValueString` | 3151-3166 | 14 | in:insertFieldTrace,insertMethodExit,instrumentCallSite+3 | LIVE |
| `CausynthPipeline.primitiveStringLocal` | 3172-3175 | 4 | in:primitiveValueString | LIVE |
| `CausynthPipeline.invoke` | 3180-3181 | 2 | in:emit,insertFieldTrace,instrumentBranch+6 | LIVE |
| `CausynthPipeline.invokeTo` | 3187-3188 | 2 | in:emit,instrumentConcolicRegion,instrumentLoopRootInvocationContext | LIVE |
| `CausynthPipeline.emit` | 3194-3195 | 2 | in:access$3000,addCommunicationHandoff,addCommunicationLeafAttach+15 | LIVE |
| `CausynthPipeline.emit` | 3200-3201 | 2 | in:access$3100,addPrimitiveRoundTrip,insertExactBranchMarkerPrefix+6 | LIVE |
| `CausynthPipeline.immediateValue` | 3204-3209 | 5 | in:addCommunicationHandoff,insertArrayTrace,newCarrierLeaf+2 | LIVE |
| `CausynthPipeline.newTraceLocal` | 3213-3229 | 14 | in:addCommunicationHandoff,addCommunicationLeafAttach,addPrimitiveRoundTrip+16 | LIVE |
| `CausynthPipeline.firstNonIdentity` | 3233-3238 | 5 | in:safeInstrumentationEntry | LIVE |
| `CausynthPipeline.safeInstrumentationEntry` | 3243-3282 | 29 | in:instrumentCommunicationFrame,instrumentCommunicationHandoff,instrumentConcolicAccessorCallContexts+4 | LIVE |
| `CausynthPipeline.localAlias` | 3287-3291 | 5 | in:safeInstrumentationEntry | LIVE |
| `CausynthPipeline.unitAtOrAfter` | 3296-3304 | 8 | in:instrumentConcolicAccessorCallContexts,instrumentConcolicLoopBounds,lambda$instrumentConcolicBranches$8 | LIVE |
| `CausynthPipeline$Hook.<clinit>` | 3307-3359 | 53 | none | LIVE |
| `CausynthPipeline$Hook.<init>` | 3307-3307 | 1 | in:<clinit> | LIVE |
| `CausynthPipeline$Hook.valueOf` | 3307-3307 | 1 | none | DEAD |
| `CausynthPipeline$Hook.values` | 3307-3307 | 1 | none | DEAD |
| `CausynthPipeline$HookCatalog.<init>` | 3363-3364 | 2 | in:concolic,trace | LIVE |
| `CausynthPipeline$HookCatalog.access$000` | 3363-3363 | 1 | in:instrumentRegionSkeletonTrace,instrumentRuntimeState | LIVE |
| `CausynthPipeline$HookCatalog.access$100` | 3363-3363 | 1 | in:addCommunicationHandoff,addCommunicationLeafAttach,addThrowHandler+20 | LIVE |
| `CausynthPipeline$HookCatalog.access$1700` | 3363-3363 | 1 | in:addThrowHandler,insertLoopBodyRegionExits,instrumentLoopRootInvocationContext+1 | LIVE |
| `CausynthPipeline$HookCatalog.access$2200` | 3363-3363 | 1 | in:instrumentConcolicBranch,instrumentConcolicSwitch,lambda$instrumentConcolicMaterializations$5+1 | LIVE |
| `CausynthPipeline$HookCatalog.access$600` | 3363-3363 | 1 | in:instrumentConcolicCampaign,instrumentConcolicLoopBounds | LIVE |
| `CausynthPipeline$HookCatalog.add` | 3369-3371 | 3 | in:concolic,trace | LIVE |
| `CausynthPipeline$HookCatalog.ref` | 3375-3375 | 1 | in:access$100,bracket | LIVE |
| `CausynthPipeline$HookCatalog.bracket` | 3381-3384 | 4 | in:access$1700 | LIVE |
| `CausynthPipeline$HookCatalog.bracket` | 3389-3392 | 4 | in:access$2200 | LIVE |
| `CausynthPipeline$HookCatalog.trace` | 3395-3435 | 39 | in:access$000 | LIVE |
| `CausynthPipeline$HookCatalog.concolic` | 3439-3547 | 99 | in:access$600 | LIVE |
| `CausynthPipeline$PrimitiveWrapper.access$2100` | 3555-3555 | 1 | in:addPrimitiveRoundTrip,carrierLeaf,materializeParameter | LIVE |
| `CausynthPipeline$PrimitiveWrapper.access$2300` | 3555-3555 | 1 | in:carrierLeaf | LIVE |
| `CausynthPipeline$PrimitiveWrapper.access$2400` | 3555-3555 | 1 | in:carrierLeaf | LIVE |
| `CausynthPipeline$PrimitiveWrapper.access$2600` | 3555-3555 | 1 | in:addPrimitiveRoundTrip | LIVE |
| `CausynthPipeline$PrimitiveWrapper.access$2700` | 3555-3555 | 1 | in:addPrimitiveRoundTrip | LIVE |
| `CausynthPipeline$PrimitiveWrapper.<init>` | 3562-3567 | 6 | in:forType | LIVE |
| `CausynthPipeline$PrimitiveWrapper.forType` | 3570-3570 | 1 | in:access$2100 | LIVE |
| `CausynthPipeline$OriginalUnitIndexTag.<init>` | 3598-3598 | 1 | in:tagOriginalUnits | LIVE |
| `CausynthPipeline$OriginalUnitIndexTag.access$2800` | 3598-3598 | 1 | in:originalUnit,originalUnitIndex | LIVE |
| `CausynthPipeline$OriginalUnitIndexTag.<init>` | 3602-3604 | 3 | in:<init> | LIVE |
| `CausynthPipeline$OriginalUnitIndexTag.getName` | 3608-3608 | 1 | none | LIVE |
| `CausynthPipeline$OriginalUnitIndexTag.getValue` | 3613-3613 | 1 | none | LIVE |

#### `d3.plan.ConcolicScheduler` — all 196 methods

| method | lines | body | callers | verdict |
|---|---|---:|---|---|
| `ConcolicScheduler.access$3400` | 65-65 | 1 | in:from | LIVE |
| `ConcolicScheduler.access$3500` | 65-65 | 1 | in:filteredSites | LIVE |
| `ConcolicScheduler.access$3600` | 65-65 | 1 | in:<init>,admits,minted+4 | LIVE |
| `ConcolicScheduler.access$3800` | 65-65 | 1 | in:read | LIVE |
| `ConcolicScheduler.<clinit>` | 84-84 | 1 | none | LIVE |
| `ConcolicScheduler.<init>` | 86-87 | 2 | none | DEAD |
| `ConcolicScheduler.main` | 90-91 | 2 | none | LIVE |
| `ConcolicScheduler.loadInputs` | 95-131 | 25 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler.scheduleLoaded` | 145-202 | 43 | in:scheduleSelections | LIVE |
| `ConcolicScheduler.removeInboundProtocolHandoffInputs` | 214-252 | 31 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler.scheduleTargetFirst` | 257-358 | 67 | in:main | LIVE |
| `ConcolicScheduler.scheduleSelections` | 365-377 | 8 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler.withSeedReplayGroup` | 397-409 | 13 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler.artifactIdentity` | 414-417 | 4 | in:loadInputs,requireArtifactIdentity,scheduleTargetFirst | LIVE |
| `ConcolicScheduler.requireArtifactIdentity` | 423-427 | 4 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler.indexTargetQuery` | 432-440 | 7 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler.sortedValues` | 443-447 | 5 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler.copyMatching` | 456-462 | 7 | in:access$3500,objectRows,targetInputBindings+1 | LIVE |
| `ConcolicScheduler.lambda$objectRows$0` | 468-468 | 1 | in:objectRows | LIVE |
| `ConcolicScheduler.objectRows` | 468-468 | 1 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler.deduplicateTopologyEdges` | 473-500 | 24 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler.rawProposals` | 507-514 | 8 | in:scheduleLoaded,scheduleTargetFirst | LIVE |
| `ConcolicScheduler.candidates` | 524-551 | 21 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler.declaredLoopBounds` | 559-579 | 14 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler.appendGoalCandidates` | 586-680 | 60 | in:candidates | LIVE |
| `ConcolicScheduler.eligibleFailureTarget` | 683-692 | 9 | in:appendGoalCandidates | LIVE |
| `ConcolicScheduler.targetQueryInstance` | 697-698 | 2 | in:appendGoalCandidates,targetQueryOccurrence | LIVE |
| `ConcolicScheduler.targetQueryOccurrence` | 705-727 | 20 | in:appendGoalCandidates | LIVE |
| `ConcolicScheduler.targetSymbolicFrontier` | 733-733 | 1 | in:appendGoalCandidates | LIVE |
| `ConcolicScheduler.lambda$targetSymbolicFrontier$1` | 734-735 | 2 | in:targetSymbolicFrontier | LIVE |
| `ConcolicScheduler.mergeSymbolicFrontier` | 741-760 | 17 | in:appendGoalCandidates | LIVE |
| `ConcolicScheduler.targetInputBindings` | 766-766 | 1 | in:appendGoalCandidates | LIVE |
| `ConcolicScheduler.lambda$targetInputBindings$2` | 767-769 | 2 | in:targetInputBindings | LIVE |
| `ConcolicScheduler.targetReachBranchSlice` | 776-791 | 13 | in:appendGoalCandidates | LIVE |
| `ConcolicScheduler.targetGuardCatalog` | 797-814 | 13 | in:branchQuery | LIVE |
| `ConcolicScheduler.materializationPlan` | 824-1028 | 126 | in:appendGoalCandidates | LIVE |
| `ConcolicScheduler.exactCallReturnSite` | 1033-1052 | 16 | in:materializationPlan | LIVE |
| `ConcolicScheduler.exploredGuardOperands` | 1057-1071 | 14 | in:materializationPlan | LIVE |
| `ConcolicScheduler.unguardedPayloadLeaf` | 1079-1089 | 9 | in:materializationPlan | LIVE |
| `ConcolicScheduler.dependenceOrigins` | 1093-1103 | 9 | in:unguardedPayloadLeaf | LIVE |
| `ConcolicScheduler.concreteOnlyInput` | 1107-1112 | 6 | in:materializationPlan | LIVE |
| `ConcolicScheduler.unsupportedSymbolicLeafReason` | 1119-1138 | 16 | in:materializationPlan | LIVE |
| `ConcolicScheduler.unsupportedFieldLeafPathReason` | 1149-1173 | 19 | in:materializationPlan,unsupportedSymbolicLeafReason | LIVE |
| `ConcolicScheduler.declaredCarrierLocations` | 1178-1187 | 10 | in:materializationPlan | LIVE |
| `ConcolicScheduler.declaredReferenceCarrier` | 1205-1209 | 5 | in:materializationPlan | LIVE |
| `ConcolicScheduler.supportedReferenceCarrier` | 1232-1234 | 3 | in:materializationPlan | LIVE |
| `ConcolicScheduler.supportedBoundedContainerState` | 1240-1254 | 12 | in:materializationPlan | LIVE |
| `ConcolicScheduler.exactActionFieldPath` | 1259-1266 | 7 | in:pathLeafFieldSignature,staticSyntheticConstant,structureControlReason+1 | LIVE |
| `ConcolicScheduler.declaredLeaf` | 1273-1281 | 8 | in:declaredReferenceCarrier,structuralContainerCardinality,unsupportedFieldLeafPathReason | LIVE |
| `ConcolicScheduler.pathLeafFieldSignature` | 1287-1294 | 7 | in:declaredLeaf | LIVE |
| `ConcolicScheduler.staticSyntheticConstant` | 1298-1305 | 7 | in:materializationPlan | LIVE |
| `ConcolicScheduler.structureControlReason` | 1311-1323 | 10 | in:materializationPlan | LIVE |
| `ConcolicScheduler.compilerSwitchDispatchTable` | 1327-1327 | 1 | in:structureControlReason | LIVE |
| `ConcolicScheduler.enumOrdinalProjection` | 1331-1336 | 5 | in:structureControlReason | LIVE |
| `ConcolicScheduler.structuralContainerCardinality` | 1341-1364 | 16 | in:structureControlReason | LIVE |
| `ConcolicScheduler.accessorSignatures` | 1368-1385 | 11 | in:enumOrdinalProjection,structuralContainerCardinality | LIVE |
| `ConcolicScheduler.addInputAction` | 1391-1394 | 4 | in:addConcreteInputAction,materializationPlan | LIVE |
| `ConcolicScheduler.addConcreteInputAction` | 1400-1405 | 5 | in:materializationPlan | LIVE |
| `ConcolicScheduler.concreteOnlyInputReason` | 1412-1429 | 13 | in:materializationPlan | LIVE |
| `ConcolicScheduler.regionIndex` | 1435-1442 | 7 | in:loadInputs | LIVE |
| `ConcolicScheduler.branchQuery` | 1449-1511 | 46 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler.directConcreteTarget` | 1517-1550 | 23 | in:branchQuery | LIVE |
| `ConcolicScheduler.queryOccurrenceWithInputs` | 1556-1576 | 19 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler.targetBranchQueryKey` | 1581-1586 | 4 | in:branchQuery | LIVE |
| `ConcolicScheduler.latestTargetSeedDecision` | 1593-1618 | 21 | in:branchQuery | LIVE |
| `ConcolicScheduler.exactTargetSummary` | 1625-1667 | 20 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler.parseArgs` | 1673-1690 | 13 | in:parse | LIVE |
| `ConcolicScheduler.requireFile` | 1694-1697 | 3 | in:access$3800,loadInputs | LIVE |
| `ConcolicScheduler.requireRefinedGraph` | 1700-1713 | 10 | in:loadInputs | LIVE |
| `ConcolicScheduler.safe` | 1716-1716 | 1 | in:access$3600,display | LIVE |
| `ConcolicScheduler$DefinitionIndex.<init>` | 1720-1725 | 4 | in:from | LIVE |
| `ConcolicScheduler$DefinitionIndex.access$2700` | 1720-1720 | 1 | in:materializationPlan | LIVE |
| `ConcolicScheduler$DefinitionIndex.access$2800` | 1720-1720 | 1 | in:materializationPlan | LIVE |
| `ConcolicScheduler$DefinitionIndex.access$2900` | 1720-1720 | 1 | in:unguardedPayloadLeaf | LIVE |
| `ConcolicScheduler$DefinitionIndex.from` | 1727-1766 | 33 | in:loadInputs | LIVE |
| `ConcolicScheduler$DefinitionIndex.lambda$from$0` | 1735-1735 | 1 | in:from | LIVE |
| `ConcolicScheduler$DefinitionIndex.lambda$from$1` | 1761-1761 | 1 | in:from | LIVE |
| `ConcolicScheduler$DefinitionIndex.knownCell` | 1770-1770 | 1 | in:access$2900 | LIVE |
| `ConcolicScheduler$DefinitionIndex.guardDependentCells` | 1776-1784 | 9 | in:access$2700 | LIVE |
| `ConcolicScheduler$DefinitionIndex.returnSites` | 1789-1789 | 1 | in:access$2800 | LIVE |
| `ConcolicScheduler$DefinitionIndex.filteredSites` | 1795-1800 | 6 | in:returnSites | LIVE |
| `ConcolicScheduler$DefinitionIndex.lambda$filteredSites$2` | 1800-1801 | 2 | in:filteredSites | LIVE |
| `ConcolicScheduler$Region.<init>` | 1806-1806 | 1 | in:regionIndex | LIVE |
| `ConcolicScheduler$Region.access$3100` | 1806-1806 | 1 | in:regionIndex | LIVE |
| `ConcolicScheduler$Region.<init>` | 1810-1818 | 6 | in:<init> | LIVE |
| `ConcolicScheduler$TargetBranch.access$1600` | 1822-1822 | 1 | in:lambda$static$2,seedTaskId,branchQuery+3 | LIVE |
| `ConcolicScheduler$TargetBranch.access$1700` | 1822-1822 | 1 | in:seedTaskId,branchQuery,directConcreteTarget+1 | LIVE |
| `ConcolicScheduler$TargetBranch.access$2300` | 1822-1822 | 1 | in:appendGoalCandidates | LIVE |
| `ConcolicScheduler$TargetBranch.access$2500` | 1822-1822 | 1 | in:appendGoalCandidates,eligibleFailureTarget | LIVE |
| `ConcolicScheduler$TargetBranch.access$2600` | 1822-1822 | 1 | in:seedTaskId,appendGoalCandidates,branchQuery | LIVE |
| `ConcolicScheduler$TargetBranch.access$3200` | 1822-1822 | 1 | in:seedTaskId,branchQuery,directConcreteTarget | LIVE |
| `ConcolicScheduler$TargetBranch.access$3300` | 1822-1822 | 1 | in:seedTaskId,branchQuery | LIVE |
| `ConcolicScheduler$TargetBranch.access$3700` | 1822-1822 | 1 | in:lambda$static$1 | LIVE |
| `ConcolicScheduler$TargetBranch.<init>` | 1834-1841 | 8 | in:regionPath,select | LIVE |
| `ConcolicScheduler$TargetBranch.regionPath` | 1844-1844 | 1 | in:access$2300 | LIVE |
| `ConcolicScheduler$TargetBranch.select` | 1850-1864 | 12 | in:access$2500 | LIVE |
| `ConcolicScheduler$Candidate.<init>` | 1869-1869 | 1 | in:appendGoalCandidates | LIVE |
| `ConcolicScheduler$Candidate.access$1000` | 1869-1869 | 1 | in:branchQuery,scheduleLoaded | LIVE |
| `ConcolicScheduler$Candidate.access$1100` | 1869-1869 | 1 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler$Candidate.access$1200` | 1869-1869 | 1 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler$Candidate.access$1400` | 1869-1869 | 1 | in:branchQuery,latestTargetSeedDecision,scheduleLoaded | LIVE |
| `ConcolicScheduler$Candidate.access$1500` | 1869-1869 | 1 | in:branchQuery,directConcreteTarget,scheduleLoaded | LIVE |
| `ConcolicScheduler$Candidate.access$600` | 1869-1869 | 1 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler$Candidate.access$700` | 1869-1869 | 1 | in:branchQuery,exactTargetSummary,scheduleLoaded | LIVE |
| `ConcolicScheduler$Candidate.access$800` | 1869-1869 | 1 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler$Candidate.access$900` | 1869-1869 | 1 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler$Candidate.<clinit>` | 1870-1958 | 8 | none | LIVE |
| `ConcolicScheduler$Candidate.lambda$static$0` | 1871-1871 | 1 | in:<clinit> | LIVE |
| `ConcolicScheduler$Candidate.lambda$static$1` | 1874-1874 | 1 | in:<clinit> | LIVE |
| `ConcolicScheduler$Candidate.lambda$static$2` | 1876-1876 | 1 | in:<clinit> | LIVE |
| `ConcolicScheduler$Candidate.lambda$static$3` | 1878-1878 | 1 | in:<clinit> | LIVE |
| `ConcolicScheduler$Candidate.lambda$static$4` | 1879-1879 | 1 | in:<clinit> | LIVE |
| `ConcolicScheduler$Candidate.<init>` | 1896-1910 | 13 | in:<init> | LIVE |
| `ConcolicScheduler$Candidate.seedTaskId` | 1915-1928 | 13 | in:access$1100 | LIVE |
| `ConcolicScheduler$Candidate.regionContentHash` | 1933-1942 | 10 | in:seedTaskId | LIVE |
| `ConcolicScheduler$Candidate.portSetHash` | 1947-1953 | 7 | in:seedTaskId | LIVE |
| `ConcolicScheduler$Candidate.semanticPortDescriptor` | 1970-1977 | 6 | in:portSetHash | LIVE |
| `ConcolicScheduler.closureAdmissionSummary` | 1988-2017 | 28 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler.noCandidateDiagnostic` | 2024-2081 | 49 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler.display` | 2085-2085 | 1 | in:noCandidateDiagnostic | LIVE |
| `ConcolicScheduler.artifact` | 2089-2090 | 2 | in:noCandidateDiagnostic | LIVE |
| `ConcolicScheduler.rootPolicyTelemetry` | 2096-2131 | 33 | in:rootPolicyRows | LIVE |
| `ConcolicScheduler.rootPolicyRows` | 2137-2143 | 7 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler$Result.<init>` | 2146-2148 | 3 | in:scheduleLoaded,scheduleTargetFirst | LIVE |
| `ConcolicScheduler$RootDependenceSlice.<init>` | 2211-2212 | 2 | in:forward,withheld | LIVE |
| `ConcolicScheduler$RootDependenceSlice.<init>` | 2215-2219 | 5 | in:<init>,admittingActionLocations | LIVE |
| `ConcolicScheduler$RootDependenceSlice.withheld` | 2223-2224 | 2 | in:forward,<init> | LIVE |
| `ConcolicScheduler$RootDependenceSlice.admittingActionLocations` | 2240-2255 | 14 | in:seedCarrierSlice | LIVE |
| `ConcolicScheduler$RootDependenceSlice.actionLocations` | 2263-2292 | 26 | in:admittingActionLocations | LIVE |
| `ConcolicScheduler$RootDependenceSlice.reachingFatalRead` | 2316-2352 | 30 | none | DEAD |
| `ConcolicScheduler$RootDependenceSlice.lambda$reachingFatalRead$0` | 2327-2327 | 1 | none | DEAD |
| `ConcolicScheduler$RootDependenceSlice.forward` | 2394-2419 | 25 | in:seedCarrierSlice | LIVE |
| `ConcolicScheduler$RootDependenceSlice.lambda$forward$1` | 2402-2402 | 1 | in:forward | LIVE |
| `ConcolicScheduler$RootDependenceSlice.usable` | 2424-2424 | 1 | in:admittingActionLocations,decide,materializationPlan+1 | LIVE |
| `ConcolicScheduler$RootDependenceSlice.carries` | 2429-2432 | 4 | in:admittingActionLocations,decide,materializationPlan | LIVE |
| `ConcolicScheduler$RootDependenceSlice.reachesLocation` | 2445-2453 | 8 | in:declaredReferenceCarrier | LIVE |
| `ConcolicScheduler$RootDependenceSlice.reachableLocations` | 2464-2477 | 13 | in:reachesLocation | LIVE |
| `ConcolicScheduler$RootDependenceSlice.rootCellCount` | 2481-2481 | 1 | in:rootPolicyTelemetry | LIVE |
| `ConcolicScheduler$RootDependenceSlice.reachableCellCount` | 2485-2485 | 1 | in:rootPolicyTelemetry | LIVE |
| `ConcolicScheduler$RootDependenceSlice.actionCells` | 2502-2516 | 11 | in:carries,seedCarrierSlice | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.<init>` | 2573-2592 | 10 | in:read | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.declarationDiagnostics` | 2595-2595 | 1 | in:rootPolicyRows | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.read` | 2604-2639 | 26 | in:loadInputs | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.lambda$read$0` | 2618-2618 | 1 | in:read | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.lambda$read$1` | 2632-2632 | 1 | in:read | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.declaredRegions` | 2669-2707 | 27 | in:read | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.declaredMethod` | 2718-2732 | 10 | in:declaredRegions | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.scopeAdmits` | 2742-2754 | 12 | in:declaredRegions | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.regionIdDeclarationDiagnostic` | 2760-2771 | 9 | in:declaredRegions | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.declareMintSite` | 2777-2800 | 16 | in:read | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.addDeclaredNames` | 2805-2820 | 12 | in:read | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.seedCarrierSlice` | 2840-2865 | 24 | in:scheduleLoaded,scheduleTargetFirst | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.carrierSlice` | 2869-2869 | 1 | in:rootPolicyTelemetry,scheduleLoaded | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.rootAction` | 2879-2880 | 2 | in:seedCarrierSlice | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.carrierLocations` | 2885-2887 | 3 | in:rootPolicyTelemetry | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.select` | 2891-2904 | 11 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.decide` | 2918-2992 | 36 | in:select | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.declaredCutPort` | 3004-3005 | 2 | in:decide | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.workloadOwnedSymbol` | 3012-3013 | 2 | in:decide,rootAction,seedCarrierSlice | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.mintsWithoutACarrier` | 3027-3028 | 2 | in:decide | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.suppressedCandidate` | 3036-3052 | 16 | in:decide | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.record` | 3060-3079 | 20 | in:decide | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.suppressedRootCandidates` | 3084-3086 | 3 | in:rootPolicyTelemetry | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.rootDecisions` | 3091-3093 | 3 | in:rootPolicyRows,rootPolicyTelemetry | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.minted` | 3099-3102 | 4 | in:decide,rootAction,seedCarrierSlice | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.declares` | 3107-3108 | 2 | none | DEAD |
| `ConcolicScheduler$SymbolicInputSelection.admits` | 3112-3116 | 5 | in:decide,rootAction,seedCarrierSlice | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.actionField` | 3120-3121 | 2 | in:admits,decide,minted+2 | LIVE |
| `ConcolicScheduler$SymbolicInputSelection.actionPort` | 3125-3126 | 2 | in:admits,record,suppressedCandidate | LIVE |
| `ConcolicScheduler$LoadedInputs.<init>` | 3130-3130 | 1 | in:loadInputs | LIVE |
| `ConcolicScheduler$LoadedInputs.access$100` | 3130-3130 | 1 | in:scheduleLoaded,scheduleTargetFirst | LIVE |
| `ConcolicScheduler$LoadedInputs.access$1300` | 3130-3130 | 1 | in:scheduleLoaded,scheduleTargetFirst | LIVE |
| `ConcolicScheduler$LoadedInputs.access$1900` | 3130-3130 | 1 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler$LoadedInputs.access$200` | 3130-3130 | 1 | in:scheduleLoaded,scheduleTargetFirst | LIVE |
| `ConcolicScheduler$LoadedInputs.access$2000` | 3130-3130 | 1 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler$LoadedInputs.access$2100` | 3130-3130 | 1 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler$LoadedInputs.access$300` | 3130-3130 | 1 | in:scheduleLoaded,scheduleTargetFirst | LIVE |
| `ConcolicScheduler$LoadedInputs.access$400` | 3130-3130 | 1 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler$LoadedInputs.access$500` | 3130-3130 | 1 | in:scheduleLoaded | LIVE |
| `ConcolicScheduler$LoadedInputs.<init>` | 3149-3159 | 11 | in:<init> | LIVE |
| `ConcolicScheduler$ClosureMode.<clinit>` | 3168-3174 | 4 | none | LIVE |
| `ConcolicScheduler$ClosureMode.valueOf` | 3168-3168 | 1 | none | DEAD |
| `ConcolicScheduler$ClosureMode.values` | 3168-3168 | 1 | in:parse | LIVE |
| `ConcolicScheduler$ClosureMode.<init>` | 3178-3180 | 3 | in:<clinit> | LIVE |
| `ConcolicScheduler$ClosureMode.parse` | 3183-3188 | 5 | in:parse | LIVE |
| `ConcolicScheduler.requireRetainedRegions` | 3209-3226 | 12 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler$Arguments.access$1800` | 3228-3228 | 1 | in:scheduleTargetFirst | LIVE |
| `ConcolicScheduler$Arguments.access$2200` | 3228-3228 | 1 | in:scheduleSelections | LIVE |
| `ConcolicScheduler$Arguments.<init>` | 3251-3268 | 17 | in:forSelection,parse | LIVE |
| `ConcolicScheduler$Arguments.parse` | 3271-3293 | 16 | in:main | LIVE |
| `ConcolicScheduler$Arguments.splitRegions` | 3298-3303 | 5 | in:parse | LIVE |
| `ConcolicScheduler$Arguments.requiredPath` | 3308-3312 | 4 | in:parse | LIVE |
| `ConcolicScheduler$Arguments.optionalPath` | 3316-3317 | 2 | in:parse | LIVE |
| `ConcolicScheduler$Arguments.parseInt` | 3322-3324 | 3 | in:parse | LIVE |
| `ConcolicScheduler$Arguments.positiveInt` | 3332-3341 | 7 | in:parse | LIVE |
| `ConcolicScheduler$Arguments.forSelection` | 3346-3346 | 1 | in:access$2200 | LIVE |

#### `causynth.SeedBackwardStaticAnalyzer` — all 192 methods

| method | lines | body | callers | verdict |
|---|---|---:|---|---|
| `SeedBackwardStaticAnalyzer.access$1100` | 67-67 | 1 | in:add | LIVE |
| `SeedBackwardStaticAnalyzer.<clinit>` | 68-124 | 27 | none | LIVE |
| `SeedBackwardStaticAnalyzer.<init>` | 129-231 | 53 | EXT:CausynthPipeline.analyze | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$new$0` | 212-212 | 1 | in:<init> | LIVE |
| `SeedBackwardStaticAnalyzer.classImplementsOrExtends` | 234-235 | 2 | in:concreteImplementations,executionContextAuthority | LIVE |
| `SeedBackwardStaticAnalyzer.hierarchyNames` | 239-239 | 1 | in:classImplementsOrExtends,lambda$resolveDispatchSources$26 | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$hierarchyNames$2` | 240-247 | 3 | in:hierarchyNames | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$null$1` | 244-245 | 2 | in:lambda$hierarchyNames$2 | LIVE |
| `SeedBackwardStaticAnalyzer.analyze` | 252-299 | 31 | EXT:CausynthPipeline.analyze | LIVE |
| `SeedBackwardStaticAnalyzer.planCommunicationCatalog` | 307-325 | 14 | in:analyze | LIVE |
| `SeedBackwardStaticAnalyzer.concreteMethod` | 328-329 | 2 | in:analyze,controlFlow,indexMutationsForField+7 | LIVE |
| `SeedBackwardStaticAnalyzer.jimpleBody` | 337-342 | 5 | in:planCommunicationCatalog | LIVE |
| `SeedBackwardStaticAnalyzer.executionContextAuthority` | 349-381 | 24 | in:analyze | LIVE |
| `SeedBackwardStaticAnalyzer.loadMethod` | 385-395 | 9 | in:analyze,ensureLoaded,indexedFact+4 | LIVE |
| `SeedBackwardStaticAnalyzer.initializeExceptionSeedAnchors` | 399-445 | 22 | in:analyze | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$initializeExceptionSeedAnchors$3` | 424-437 | 6 | in:initializeExceptionSeedAnchors | LIVE |
| `SeedBackwardStaticAnalyzer.seedDeclaredWireFlows` | 453-490 | 26 | in:analyze | LIVE |
| `SeedBackwardStaticAnalyzer.seedExplicitFaultEntries` | 500-557 | 28 | in:analyze | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$seedExplicitFaultEntries$4` | 535-552 | 6 | in:seedExplicitFaultEntries | LIVE |
| `SeedBackwardStaticAnalyzer.ensureLoaded` | 560-562 | 3 | in:seedDeclaredWireFlows | LIVE |
| `SeedBackwardStaticAnalyzer.annotatedExceptionAllocation` | 567-589 | 18 | in:initializeExceptionSeedAnchors | LIVE |
| `SeedBackwardStaticAnalyzer.findExceptionAllocation` | 594-611 | 14 | in:annotatedExceptionAllocation | LIVE |
| `SeedBackwardStaticAnalyzer.allocatedExceptionType` | 615-620 | 5 | in:annotatedExceptionAllocation,findExceptionAllocation | LIVE |
| `SeedBackwardStaticAnalyzer.causalGuardUses` | 624-631 | 7 | in:forEachGuardOperand | LIVE |
| `SeedBackwardStaticAnalyzer.controllingGuards` | 640-640 | 1 | in:addReceiverFieldEffectPathGuards,processHeapMutationPathGuards,processRequiredPathGuards+2 | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$controllingGuards$5` | 642-642 | 1 | in:controllingGuards | LIVE |
| `SeedBackwardStaticAnalyzer.branchGuards` | 648-704 | 41 | in:initializeExceptionSeedAnchors,lambda$controllingGuards$5 | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$branchGuards$6` | 703-703 | 1 | in:branchGuards | LIVE |
| `SeedBackwardStaticAnalyzer.controlFlow` | 708-721 | 11 | in:branchGuards,loopControlGuard | LIVE |
| `SeedBackwardStaticAnalyzer.canReachWithoutRevisiting` | 732-745 | 12 | in:branchGuards | LIVE |
| `SeedBackwardStaticAnalyzer.localNames` | 749-756 | 7 | in:fieldsAliasedByLocal,findExceptionAllocation | LIVE |
| `SeedBackwardStaticAnalyzer.localName` | 760-771 | 9 | in:atomicDataflowUse,causalGuardUses,findExceptionAllocation+2 | LIVE |
| `SeedBackwardStaticAnalyzer.invokeBaseLocal` | 775-779 | 4 | in:fieldsAliasedByLocal,fieldsMutatedByInvoke,indexGlobalMethod+8 | LIVE |
| `SeedBackwardStaticAnalyzer.runWorklist` | 785-797 | 12 | in:analyze | LIVE |
| `SeedBackwardStaticAnalyzer.processMethod` | 800-859 | 44 | in:runWorklist | LIVE |
| `SeedBackwardStaticAnalyzer.processRequiredPathGuards` | 868-899 | 11 | in:processMethod | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$processRequiredPathGuards$7` | 883-898 | 7 | in:processRequiredPathGuards | LIVE |
| `SeedBackwardStaticAnalyzer.processFieldReads` | 903-921 | 15 | in:processMethod | LIVE |
| `SeedBackwardStaticAnalyzer.processFieldWrites` | 925-949 | 21 | in:processMethod | LIVE |
| `SeedBackwardStaticAnalyzer.processArrayAccesses` | 958-964 | 5 | in:processMethod | LIVE |
| `SeedBackwardStaticAnalyzer.processArrayLoad` | 969-990 | 18 | in:processArrayAccesses | LIVE |
| `SeedBackwardStaticAnalyzer.processArrayStore` | 995-1013 | 15 | in:processArrayAccesses | LIVE |
| `SeedBackwardStaticAnalyzer.arrayStoreSources` | 1016-1033 | 14 | in:processArrayStore | LIVE |
| `SeedBackwardStaticAnalyzer.arrayElementCell` | 1037-1037 | 1 | in:processArrayLoad,processArrayStore | LIVE |
| `SeedBackwardStaticAnalyzer.processHeapMutationPathGuards` | 1048-1057 | 4 | in:processFieldWrites | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$processHeapMutationPathGuards$8` | 1053-1056 | 3 | in:processHeapMutationPathGuards | LIVE |
| `SeedBackwardStaticAnalyzer.addHeapMutationPathGuardEdge` | 1062-1070 | 5 | in:lambda$processHeapMutationPathGuards$8 | LIVE |
| `SeedBackwardStaticAnalyzer.processFieldWrite` | 1075-1093 | 15 | in:expandFieldWriters,processFieldWrites | LIVE |
| `SeedBackwardStaticAnalyzer.expandFieldWriters` | 1096-1129 | 27 | in:runWorklist | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$expandFieldWriters$9` | 1122-1122 | 1 | in:expandFieldWriters | LIVE |
| `SeedBackwardStaticAnalyzer.expandConstructorCallers` | 1132-1179 | 19 | in:runWorklist | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$expandConstructorCallers$10` | 1134-1134 | 1 | in:expandConstructorCallers | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$expandConstructorCallers$11` | 1147-1147 | 1 | in:expandConstructorCallers | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$expandConstructorCallers$12` | 1150-1150 | 1 | in:expandConstructorCallers | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$expandConstructorCallers$13` | 1160-1177 | 12 | in:expandConstructorCallers | LIVE |
| `SeedBackwardStaticAnalyzer.expandMethodCallers` | 1182-1235 | 19 | in:runWorklist | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$expandMethodCallers$14` | 1206-1234 | 19 | in:expandMethodCallers | LIVE |
| `SeedBackwardStaticAnalyzer.selectActivationCaller` | 1239-1259 | 12 | in:lambda$expandDispatchCallers$25 | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$selectActivationCaller$15` | 1255-1258 | 3 | in:selectActivationCaller | LIVE |
| `SeedBackwardStaticAnalyzer.addTypedLiteralCallerArgument` | 1269-1282 | 11 | in:lambda$expandConstructorCallers$13,lambda$expandMethodCallers$14 | LIVE |
| `SeedBackwardStaticAnalyzer.invokeArgument` | 1286-1296 | 8 | in:addTypedLiteralCallerArgument | LIVE |
| `SeedBackwardStaticAnalyzer.typedLiteralValue` | 1300-1310 | 8 | in:addTypedLiteralCallerArgument | LIVE |
| `SeedBackwardStaticAnalyzer.addReceiverFieldEffectPathGuards` | 1320-1339 | 5 | in:lambda$expandMethodCallers$14 | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$addReceiverFieldEffectPathGuards$16` | 1327-1338 | 9 | in:addReceiverFieldEffectPathGuards | LIVE |
| `SeedBackwardStaticAnalyzer.addReceiverFieldEffectPathGuardEdge` | 1344-1355 | 6 | in:lambda$addReceiverFieldEffectPathGuards$16 | LIVE |
| `SeedBackwardStaticAnalyzer.constructorParam` | 1358-1379 | 17 | in:expandConstructorCallers | LIVE |
| `SeedBackwardStaticAnalyzer.buildGlobalStaticIndex` | 1385-1412 | 22 | in:analyze,expandConstructorCallers,expandDispatchCallers+2 | LIVE |
| `SeedBackwardStaticAnalyzer.indexGlobalMethod` | 1415-1478 | 49 | in:buildGlobalStaticIndex | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$indexGlobalMethod$17` | 1429-1429 | 1 | in:indexGlobalMethod | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$indexGlobalMethod$18` | 1451-1451 | 1 | in:indexGlobalMethod | LIVE |
| `SeedBackwardStaticAnalyzer.applicationFields` | 1483-1494 | 10 | in:indexGlobalMethod | LIVE |
| `SeedBackwardStaticAnalyzer.factsFromBody` | 1498-1503 | 6 | in:indexMutationsForField,loadMethod | LIVE |
| `SeedBackwardStaticAnalyzer.indexedFact` | 1508-1520 | 10 | in:captureFact,expandFieldWriters,forEachCallsite+1 | LIVE |
| `SeedBackwardStaticAnalyzer.addIndexedFieldWrite` | 1524-1529 | 5 | in:indexGlobalMethod,indexMutationsForField | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$addIndexedFieldWrite$19` | 1528-1528 | 1 | in:addIndexedFieldWrite | LIVE |
| `SeedBackwardStaticAnalyzer.addIndexedCallsite` | 1534-1540 | 6 | in:indexGlobalMethod | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$addIndexedCallsite$20` | 1538-1538 | 1 | in:addIndexedCallsite | LIVE |
| `SeedBackwardStaticAnalyzer.indexMutationsForField` | 1553-1576 | 19 | in:expandFieldWriters | LIVE |
| `SeedBackwardStaticAnalyzer.fieldWriteSources` | 1579-1593 | 11 | in:indexGlobalMethod,processFieldWrites | LIVE |
| `SeedBackwardStaticAnalyzer.fieldMutationSources` | 1597-1604 | 7 | in:indexMutationsForField,processFieldWrites | LIVE |
| `SeedBackwardStaticAnalyzer.canonicalSourcesExcludingField` | 1610-1620 | 10 | in:fieldMutationSources,fieldWriteSources | LIVE |
| `SeedBackwardStaticAnalyzer.fieldsMutatedByInvoke` | 1624-1638 | 12 | in:indexMutationsForField,processFieldWrites | LIVE |
| `SeedBackwardStaticAnalyzer.fieldsAliasedByLocal` | 1643-1663 | 17 | in:fieldsMutatedByInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.returnsBackedCollectionView` | 1671-1682 | 10 | in:fieldsAliasedByLocal | LIVE |
| `SeedBackwardStaticAnalyzer.isFieldMutator` | 1686-1694 | 8 | in:fieldsMutatedByInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.isCanonicalField` | 1698-1704 | 5 | in:fieldsMutatedByInvoke,isApplicationField,isFieldAccessValue | LIVE |
| `SeedBackwardStaticAnalyzer.isApplicationField` | 1708-1711 | 3 | in:addIndexedFieldWrite,applicationFields,expandFieldWriters | LIVE |
| `SeedBackwardStaticAnalyzer.isApplicationClassName` | 1715-1716 | 2 | in:addIndexedCallsite,constructorParam,expandMethodCallers+3 | LIVE |
| `SeedBackwardStaticAnalyzer.processInvoke` | 1722-1774 | 35 | in:processMethod | LIVE |
| `SeedBackwardStaticAnalyzer.annotateExplicitSymbolicFault` | 1779-1788 | 8 | in:processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.annotateExplicitSymbolicFaultEdge` | 1793-1797 | 5 | in:annotateExplicitSymbolicFault,seedExplicitFaultEntries | LIVE |
| `SeedBackwardStaticAnalyzer.explicitFaultName` | 1800-1806 | 6 | in:annotateExplicitSymbolicFault,seedExplicitFaultEntries | LIVE |
| `SeedBackwardStaticAnalyzer.propagateCallArguments` | 1817-1832 | 13 | in:processDispatchInvoke,processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.propagateCallReturns` | 1841-1852 | 10 | in:processDispatchInvoke,processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.processSemanticContainerOperation` | 1866-1907 | 30 | in:processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.processSemanticContainerMutation` | 1920-1938 | 16 | in:processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.processContainerCallMutationEffects` | 1945-1958 | 12 | in:processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.directlyMutatedContainerParameters` | 1962-1964 | 3 | in:processContainerCallMutationEffects | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$directlyMutatedContainerParameters$21` | 1965-2001 | 30 | in:directlyMutatedContainerParameters | LIVE |
| `SeedBackwardStaticAnalyzer.isSemanticContainerView` | 2006-2022 | 15 | in:processSemanticContainerOperation | LIVE |
| `SeedBackwardStaticAnalyzer.processConstructorObjectInvoke` | 2030-2050 | 16 | in:processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.processAccessorInvoke` | 2055-2095 | 32 | in:processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.annotateAccessorDeclaredFieldEdge` | 2099-2107 | 7 | in:processAccessorInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.annotateDirectDeclaredFieldEdge` | 2114-2124 | 9 | in:processFieldReads | LIVE |
| `SeedBackwardStaticAnalyzer.resolveDeclaredMethod` | 2128-2132 | 4 | in:uniqueAnalyzableImplementation | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$resolveDeclaredMethod$22` | 2133-2138 | 5 | in:resolveDeclaredMethod | LIVE |
| `SeedBackwardStaticAnalyzer.uniqueAnalyzableImplementation` | 2147-2162 | 12 | in:structuralFieldAccessor | LIVE |
| `SeedBackwardStaticAnalyzer.eligibleAnalyzableImplementation` | 2166-2167 | 2 | in:uniqueAnalyzableImplementation | LIVE |
| `SeedBackwardStaticAnalyzer.structuralFieldAccessor` | 2176-2185 | 8 | in:isExpandableMethod,processAccessorInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.inspectStructuralFieldAccessor` | 2190-2202 | 11 | in:structuralFieldAccessor | LIVE |
| `SeedBackwardStaticAnalyzer.processDispatchInvoke` | 2209-2248 | 29 | in:processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.resolveDispatchTargets` | 2251-2254 | 3 | in:processDispatchInvoke,processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$resolveDispatchTargets$23` | 2255-2263 | 7 | in:resolveDispatchTargets | LIVE |
| `SeedBackwardStaticAnalyzer.methodSubSignature` | 2268-2269 | 2 | in:concreteImplementations,lambda$resolveDispatchSources$26,resolveDeclaredMethod | LIVE |
| `SeedBackwardStaticAnalyzer.concreteImplementations` | 2275-2287 | 11 | in:applicationImplementationSignatures,uniqueAnalyzableImplementation | LIVE |
| `SeedBackwardStaticAnalyzer.applicationImplementationSignatures` | 2291-2296 | 5 | in:lambda$resolveDispatchTargets$23 | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$applicationImplementationSignatures$24` | 2293-2293 | 1 | in:applicationImplementationSignatures | LIVE |
| `SeedBackwardStaticAnalyzer.skipDispatchOwner` | 2300-2304 | 5 | in:lambda$resolveDispatchSources$26,resolveDispatchTargets | LIVE |
| `SeedBackwardStaticAnalyzer.captureFact` | 2308-2321 | 12 | in:seedDeclaredWireFlows | LIVE |
| `SeedBackwardStaticAnalyzer.captureNode` | 2325-2341 | 14 | in:seedDeclaredWireFlows | LIVE |
| `SeedBackwardStaticAnalyzer.expandDispatchCallers` | 2345-2377 | 15 | in:runWorklist | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$expandDispatchCallers$25` | 2361-2375 | 7 | in:expandDispatchCallers | LIVE |
| `SeedBackwardStaticAnalyzer.forEachCallsite` | 2389-2400 | 9 | in:expandConstructorCallers,expandDispatchCallers,expandMethodCallers | LIVE |
| `SeedBackwardStaticAnalyzer.expandCallerArguments` | 2412-2432 | 17 | in:lambda$expandDispatchCallers$25 | LIVE |
| `SeedBackwardStaticAnalyzer.expandCallerReceiver` | 2438-2455 | 13 | in:lambda$expandDispatchCallers$25,lambda$expandMethodCallers$14 | LIVE |
| `SeedBackwardStaticAnalyzer.resolveDispatchSources` | 2459-2459 | 1 | in:expandDispatchCallers | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$resolveDispatchSources$26` | 2460-2485 | 22 | in:resolveDispatchSources | LIVE |
| `SeedBackwardStaticAnalyzer.isExpandableMethod` | 2491-2498 | 8 | in:processInvoke | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$relevant$27` | 2502-2502 | 1 | in:relevant | LIVE |
| `SeedBackwardStaticAnalyzer.relevant` | 2502-2502 | 1 | in:expandCallerReceiver,expandConstructorCallers,expandConstructorReceiverFields+15 | LIVE |
| `SeedBackwardStaticAnalyzer.memoized` | 2508-2514 | 6 | in:cachedCanonicalList,controllingGuards,directlyMutatedContainerParameters+5 | LIVE |
| `SeedBackwardStaticAnalyzer.forEachGuardOperand` | 2524-2532 | 8 | in:addReceiverFieldEffectPathGuards,initializeExceptionSeedAnchors,processHeapMutationPathGuards+3 | LIVE |
| `SeedBackwardStaticAnalyzer.expandOnce` | 2535-2539 | 4 | in:expandCallerArguments,expandCallerReceiver,expandConstructorCallers+5 | LIVE |
| `SeedBackwardStaticAnalyzer.markDirty` | 2543-2546 | 3 | in:access$1100 | LIVE |
| `SeedBackwardStaticAnalyzer$DirtyMarkingSet.<init>` | 2548-2548 | 1 | in:<init>,lambda$relevant$27 | LIVE |
| `SeedBackwardStaticAnalyzer$DirtyMarkingSet.add` | 2548-2548 | 1 | none | LIVE |
| `SeedBackwardStaticAnalyzer$DirtyMarkingSet.<init>` | 2552-2554 | 3 | in:<init> | LIVE |
| `SeedBackwardStaticAnalyzer$DirtyMarkingSet.add` | 2558-2560 | 3 | in:add | LIVE |
| `SeedBackwardStaticAnalyzer.nonInvokeUses` | 2566-2566 | 1 | in:findExceptionAllocation,lambda$localValueUses$29 | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$nonInvokeUses$28` | 2567-2577 | 10 | in:nonInvokeUses | LIVE |
| `SeedBackwardStaticAnalyzer.localValueUses` | 2582-2582 | 1 | in:canonicalLocalValueUses,causalGuardUses,fieldWriteSources+1 | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$localValueUses$29` | 2583-2618 | 28 | in:localValueUses | LIVE |
| `SeedBackwardStaticAnalyzer.atomicDataflowUse` | 2624-2635 | 11 | in:arrayStoreSources,lambda$localValueUses$29 | LIVE |
| `SeedBackwardStaticAnalyzer.isValueLikeLibraryInvoke` | 2639-2652 | 11 | in:lambda$localValueUses$29 | LIVE |
| `SeedBackwardStaticAnalyzer.isFieldAccessValue` | 2656-2663 | 7 | in:arrayStoreSources,atomicDataflowUse,causalGuardUses+1 | LIVE |
| `SeedBackwardStaticAnalyzer.canonicalList` | 2667-2674 | 7 | in:arrayStoreSources,lambda$cachedCanonicalList$30 | LIVE |
| `SeedBackwardStaticAnalyzer.canonicalDefs` | 2678-2678 | 1 | in:addEdge,captureNode,lambda$directlyMutatedContainerParameters$21+2 | LIVE |
| `SeedBackwardStaticAnalyzer.canonicalLocalValueUses` | 2683-2684 | 2 | in:processMethod | LIVE |
| `SeedBackwardStaticAnalyzer.cachedCanonicalList` | 2690-2690 | 1 | in:canonicalDefs,canonicalLocalValueUses | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$cachedCanonicalList$30` | 2691-2693 | 3 | in:cachedCanonicalList | LIVE |
| `SeedBackwardStaticAnalyzer.canonicalPositionList` | 2698-2702 | 5 | in:captureNode,indexGlobalMethod,processInvoke+2 | LIVE |
| `SeedBackwardStaticAnalyzer.canonical` | 2706-2728 | 17 | in:canonicalList,canonicalPositionList,canonicalSourcesExcludingField+16 | LIVE |
| `SeedBackwardStaticAnalyzer.parameterNodesFromUnit` | 2732-2740 | 8 | in:processMethod | LIVE |
| `SeedBackwardStaticAnalyzer.formalParam` | 2744-2744 | 1 | in:addTypedLiteralCallerArgument,captureNode,constructorParam+6 | LIVE |
| `SeedBackwardStaticAnalyzer.factNode` | 2748-2748 | 1 | in:addTypedLiteralCallerArgument,captureNode,fieldMutationSources+5 | LIVE |
| `SeedBackwardStaticAnalyzer.methodThisNode` | 2753-2773 | 17 | in:expandConstructorCallers,expandDispatchCallers,expandMethodCallers+1 | LIVE |
| `SeedBackwardStaticAnalyzer.expandConstructorReceiverFields` | 2780-2792 | 9 | in:lambda$expandConstructorCallers$12 | LIVE |
| `SeedBackwardStaticAnalyzer.resolveDeclaredField` | 2796-2801 | 5 | in:annotateDirectDeclaredFieldEdge | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$resolveDeclaredField$32` | 2802-2802 | 1 | in:resolveDeclaredField | LIVE |
| `SeedBackwardStaticAnalyzer.lambda$null$31` | 2803-2803 | 1 | in:lambda$resolveDeclaredField$32 | LIVE |
| `SeedBackwardStaticAnalyzer.resolveInHierarchy` | 2808-2816 | 7 | in:resolveDeclaredField,resolveDeclaredMethod | LIVE |
| `SeedBackwardStaticAnalyzer.walkHierarchy` | 2822-2850 | 22 | in:lambda$hierarchyNames$2,resolveInHierarchy | LIVE |
| `SeedBackwardStaticAnalyzer.erasedTypeName` | 2854-2862 | 7 | in:inspectStructuralFieldAccessor,processAccessorInvoke,resolveDeclaredField | LIVE |
| `SeedBackwardStaticAnalyzer.addEdge` | 2867-2926 | 33 | in:addHeapMutationPathGuardEdge,addReceiverFieldEffectPathGuardEdge,addTypedLiteralCallerArgument+26 | LIVE |
| `SeedBackwardStaticAnalyzer.loopControlGuard` | 2930-2932 | 3 | in:addEdge | LIVE |
| `SeedBackwardStaticAnalyzer.exactLocalDirectCopy` | 2943-2974 | 24 | in:addEdge | LIVE |
| `SeedBackwardStaticAnalyzer.edgeKey` | 2980-2981 | 2 | in:addEdge,annotateExplicitSymbolicFault | LIVE |
| `SeedBackwardStaticAnalyzer.exactIntersects` | 2986-2991 | 5 | in:fieldsAliasedByLocal,findExceptionAllocation,processAccessorInvoke+3 | LIVE |
| `SeedBackwardStaticAnalyzer.ignoreNode` | 2995-3006 | 11 | in:addEdge,canonicalList,canonicalSourcesExcludingField+23 | LIVE |
| `SeedBackwardStaticAnalyzer$MethodSig.<init>` | 3009-3009 | 1 | in:parseMethodSig | LIVE |
| `SeedBackwardStaticAnalyzer$MethodSig.access$300` | 3009-3009 | 1 | in:constructorParam,expandMethodCallers,indexGlobalMethod+6 | LIVE |
| `SeedBackwardStaticAnalyzer$MethodSig.access$400` | 3009-3009 | 1 | in:addIndexedCallsite,concreteImplementations,constructorParam+12 | LIVE |
| `SeedBackwardStaticAnalyzer$MethodSig.access$500` | 3009-3009 | 1 | in:addTypedLiteralCallerArgument,constructorParam,expandCallerArguments+8 | LIVE |
| `SeedBackwardStaticAnalyzer$MethodSig.access$600` | 3009-3009 | 1 | in:annotateExplicitSymbolicFault,directlyMutatedContainerParameters,formalParam+9 | LIVE |
| `SeedBackwardStaticAnalyzer$MethodSig.access$700` | 3009-3009 | 1 | in:inspectStructuralFieldAccessor,isSemanticContainerView,methodSubSignature+1 | LIVE |
| `SeedBackwardStaticAnalyzer$MethodSig.<init>` | 3017-3023 | 7 | in:<init> | LIVE |
| `SeedBackwardStaticAnalyzer$StructuralFieldAccessor.<init>` | 3026-3026 | 1 | in:inspectStructuralFieldAccessor | LIVE |
| `SeedBackwardStaticAnalyzer$StructuralFieldAccessor.access$800` | 3026-3026 | 1 | in:processAccessorInvoke | LIVE |
| `SeedBackwardStaticAnalyzer$StructuralFieldAccessor.access$900` | 3026-3026 | 1 | in:processAccessorInvoke | LIVE |
| `SeedBackwardStaticAnalyzer$StructuralFieldAccessor.<init>` | 3031-3034 | 4 | in:<init> | LIVE |
| `SeedBackwardStaticAnalyzer$EdgeIdentity.<init>` | 3038-3038 | 1 | in:edgeKey | LIVE |
| `SeedBackwardStaticAnalyzer$EdgeIdentity.<init>` | 3049-3062 | 14 | in:<init> | LIVE |
| `SeedBackwardStaticAnalyzer$EdgeIdentity.hashCode` | 3066-3066 | 1 | none | LIVE |
| `SeedBackwardStaticAnalyzer$EdgeIdentity.equals` | 3071-3083 | 10 | none | LIVE |
| `SeedBackwardStaticAnalyzer$MethodControlFlow.<init>` | 3087-3087 | 1 | in:controlFlow | LIVE |
| `SeedBackwardStaticAnalyzer$MethodControlFlow.access$100` | 3087-3087 | 1 | in:branchGuards,jimpleBody | LIVE |
| `SeedBackwardStaticAnalyzer$MethodControlFlow.access$1200` | 3087-3087 | 1 | in:loopControlGuard | LIVE |
| `SeedBackwardStaticAnalyzer$MethodControlFlow.<init>` | 3093-3095 | 3 | in:<init> | LIVE |
| `SeedBackwardStaticAnalyzer$MethodControlFlow.loopControlGuards` | 3098-3101 | 3 | in:access$1200 | LIVE |
| `SeedBackwardStaticAnalyzer.parseMethodSig` | 3106-3130 | 20 | in:addIndexedCallsite,captureNode,constructorParam+14 | LIVE |
| `SeedBackwardStaticAnalyzer.stableSiteId` | 3134-3137 | 3 | in:addEdge | LIVE |
| `SeedBackwardStaticAnalyzer.names` | 3141-3142 | 2 | in:<clinit> | LIVE |


## Appendix B — per-file deletion cascade

`own` = body lines of the file's own methods. `cascade` = body lines elsewhere that become unreachable if every method of this file is removed. Both measured by re-running reachability with that file's methods deleted. Sorted by total. Files with zero cascade and small own-size are omitted below 40 total.

| file | file lines | own body | cascade body | total | what dies with it (top 4) |
|---|---:|---:|---:|---:|---|
| `runtime.CausynthTraceRecorder` | 2325 | 1261 | 6120 | 7381 | `causynth.RuntimeSelectedRegionFinalizer` 2523; `runtime.RuntimeRegionPlanner` 1941; `runtime.RuntimeRefinedGraphBuilder` 647; `runtime.RuntimeTraceContext` 412 |
| `transformer.GraphCheckerTransformer` | 29 | 8 | 5882 | 5890 | `causynth.CausynthPipeline` 2103; `causynth.SeedBackwardStaticAnalyzer` 1809; `causynth.SymbolicRegionPlanner` 339; `causynth.CfgLoopControl` 230 |
| `causynth.CausynthPipeline` | 3621 | 2103 | 3779 | 5882 | `causynth.SeedBackwardStaticAnalyzer` 1809; `causynth.SymbolicRegionPlanner` 339; `causynth.CfgLoopControl` 230; `causynth.WireFlowCatalog` 177 |
| `runtime.ConcolicRegionRuntime` | 7764 | 3377 | 1340 | 4717 | `runtime.ConcolicTaskPlan` 260; `runtime.ConcolicVmBroker` 137; `d3.plan.BranchReplayContract` 131; `runtime.ConcolicResultPublisher` 113 |
| `d3.plan.ConcolicScheduler` | 3355 | 1668 | 1114 | 2782 | `d3.plan.RuntimeWorkflowDiscovery` 352; `d3.plan.SummaryBranchMapping` 121; `d3.plan.SolverPathContext` 112; `d3.plan.BranchReplayContract` 97 |
| `causynth.RuntimeSelectedRegionFinalizer` | 4474 | 2523 | 226 | 2749 | `causynth.StaticProgram` 188; `runtime.OccurrenceMinter` 18; `d3.smt.JavaContainerTypes` 11; `d3.plan.DependencyRole` 5 |
| `d3.compose.SmtLowering` | 1561 | 636 | 1993 | 2629 | `d3.compose.ContainerSmtCodec` 1143; `d3.compose.VmLoweringCore` 365; `d3.smt.JavaPrimitiveSmtSemantics` 229; `d3.compose.VmTermLowering` 139 |
| `causynth.SeedBackwardStaticAnalyzer` | 3145 | 1809 | 781 | 2590 | `causynth.WireFlowCatalog` 177; `causynth.CommunicationCatalogPlanner` 138; `causynth.CausynthStaticFacts` 128; `causynth.DeclaredLoopBodyBounds` 108 |
| `runtime.RuntimeRegionPlanner` | 3733 | 1995 | 225 | 2220 | `d3.plan.MaterializationSpec` 54; `d3.plan.ConfiguredSourcePhaseContract` 40; `d3.plan.RuntimePlanArtifact` 36; `runtime.OccurrenceMinter` 32 |
| `d3.compose.VmLoweringCore` | 997 | 365 | 1796 | 2161 | `d3.compose.ContainerSmtCodec` 1118; `d3.smt.JavaPrimitiveSmtSemantics` 225; `d3.compose.SmtLowering` 217; `d3.compose.VmTermLowering` 128 |
| `d3.compose.ComposeMain` | 569 | 295 | 1615 | 1910 | `d3.compose.Composer` 749; `d3.compose.CorpusIndex` 210; `d3.compose.Solver` 177; `d3.compose.ClaimPolicy` 173 |
| `d3.compose.ContainerSmtCodec` | 2426 | 1143 | 57 | 1200 | `d3.compose.SmtLowering` 45; `d3.smt.VmExpressionIr` 10; `d3.compose.VmTermLowering` 2 |
| `runtime.ConcolicResultPublisher` | 668 | 276 | 811 | 1087 | `runtime.D3RowPublication` 197; `d3.plan.SharedStateEvidence` 119; `runtime.SharedStateCapture` 90; `runtime.d3.D3Runtime` 81 |
| `runtime.ConcolicTaskPlan` | 2024 | 715 | 311 | 1026 | `d3.plan.BranchReplayContract` 125; `runtime.ConcolicRegionRuntime` 125; `d3.plan.ExecutionTask` 24; `d3.smt.JavaPrimitiveSmtSemantics` 14 |
| `d3.compose.Composer` | 1655 | 749 | 261 | 1010 | `d3.compose.SmtLowering` 74; `d3.compose.SlotTable` 61; `d3.compose.CorpusIndex` 49; `d3.smt.Arms` 21 |
| `d3.explore.ObligationSolverMain` | 183 | 77 | 828 | 905 | `d3.explore.FlipQuery` 425; `d3.explore.Z3Solver` 102; `d3.compose.SmtLowering` 90; `d3.explore.SmtText` 82 |
| `d3.explore.ObligationFactory` | 276 | 106 | 757 | 863 | `d3.explore.FlipQuery` 441; `d3.explore.Z3Solver` 102; `d3.compose.SmtLowering` 90; `d3.explore.SmtText` 82 |
| `runtime.RuntimeRefinedGraphBuilder` | 1202 | 647 | 3 | 650 | `d3.smt.JavaContainerTypes` 3 |
| `d3.explore.FlipQuery` | 992 | 441 | 207 | 648 | `d3.compose.SmtLowering` 90; `d3.explore.SmtText` 82; `d3.explore.Corpus` 35 |
| `runtime.RuntimeTraceContext` | 1227 | 535 | 89 | 624 | `runtime.d3.Lineage` 81; `runtime.CausynthTraceRecorder` 3; `runtime.d3.Identity` 3; `runtime.d3.Interactions` 2 |
| `d3.explore.ExploreMain` | 395 | 194 | 399 | 593 | `d3.explore.SlotTable` 137; `d3.explore.ClosurePlanner` 122; `d3.explore.Frontier` 48; `d3.explore.ExploreCodec` 29 |
| `runtime.d3.D3Runtime` | 627 | 224 | 359 | 583 | `runtime.d3.SessionPublisher` 114; `d3.contract.RowCodec` 87; `runtime.d3.FocusedReplay` 83; `runtime.d3.Interactions` 24 |
| `d3.plan.BranchReplayContract` | 977 | 440 | 118 | 558 | `d3.plan.SolverPathContext` 112; `d3.plan.BranchWitness` 3; `d3.plan.ExactConcreteBranchObservation` 3 |
| `causynth.ConcolicInstrumentationSelections` | 1066 | 490 | 10 | 500 | `d3.plan.ExecutionTask` 6; `causynth.CausynthStaticFacts` 3; `d3.plan.InputActionCatalog` 1 |
| `d3.plan.SharedExpressionTable` | 852 | 423 | 0 | 423 | — |
| `d3.plan.ExecutionTask` | 534 | 200 | 171 | 371 | `d3.plan.BranchReplayContract` 125; `d3.plan.InputActionCatalog` 25; `d3.plan.RegionInstancePlan` 21 |
| `d3.compose.ClaimPolicy` | 431 | 173 | 185 | 358 | `d3.compose.Solver` 155; `d3.compose.Composer` 17; `d3.contract.Claim` 10; `d3.contract.Family` 2 |
| `d3.plan.RuntimeWorkflowDiscovery` | 743 | 352 | 3 | 355 | `d3.plan.AutomaticRegionEdge` 3 |
| `runtime.D3RowPublication` | 384 | 197 | 158 | 355 | `d3.contract.RowCodec` 52; `runtime.d3.D3Runtime` 51; `runtime.d3.FocusedReplay` 30; `runtime.d3.SessionPublisher` 15 |
| `causynth.SymbolicRegionPlanner` | 648 | 339 | 0 | 339 | — |
| `causynth.StaticProgram` | 712 | 313 | 11 | 324 | `d3.plan.ConfiguredSourcePhaseContract` 11 |
| `d3.contract.RowCodec` | 531 | 265 | 30 | 295 | `d3.contract.ExpressionTable` 15; `d3.contract.CausalContext` 3; `d3.contract.ExportRow` 3; `d3.contract.TargetRow` 2 |
| `d3.smt.Arms` | 647 | 231 | 50 | 281 | `d3.compose.CorpusIndex` 28; `d3.explore.Corpus` 20; `d3.contract.Interaction` 1; `d3.contract.LocationId` 1 |
| `d3.smt.JavaPrimitiveSmtSemantics` | 635 | 278 | 0 | 278 | — |
| `GraphCheckerMain` | 337 | 188 | 86 | 274 | `option.OptionParser` 57; `causynth.ConcolicInstrumentationSelections` 12; `option.GraphCheckerOptions` 9; `transformer.GraphCheckerTransformer` 3 |
| `runtime.SharedStateCapture` | 358 | 128 | 140 | 268 | `d3.plan.SharedStateEvidence` 119; `d3.plan.RecordedEvidenceIdentity` 10; `runtime.ConcolicVmBroker` 6; `runtime.ConcolicRegionRuntime` 5 |
| `d3.explore.Corpus` | 599 | 233 | 30 | 263 | `d3.compose.SmtLowering` 13; `d3.explore.ExploreCodec` 12; `d3.contract.SessionReader` 5 |
| `d3.compose.CorpusIndex` | 630 | 262 | 0 | 262 | — |
| `d3.compose.VmTermLowering` | 522 | 165 | 97 | 262 | `d3.smt.JavaPrimitiveSmtSemantics` 68; `d3.smt.VmExpressionIr` 13; `d3.compose.JavaSmtSorts` 10; `d3.compose.ContainerSmtCodec` 4 |
| `runtime.d3.FocusedReplay` | 553 | 259 | 0 | 259 | — |
| `causynth.CfgLoopControl` | 502 | 230 | 0 | 230 | — |
| `d3.plan.VmExpressionTable` | 413 | 207 | 19 | 226 | `d3.plan.SharedExpressionTable` 15; `d3.plan.SharedStateEvidence` 4 |
| `causynth.CommunicationCatalogPlanner` | 293 | 150 | 70 | 220 | `causynth.DeclaredLoopBodyBounds` 36; `causynth.WireFlowCatalog` 33; `causynth.CfgLoopControl` 1 |
| `runtime.d3.SessionPublisher` | 282 | 114 | 106 | 220 | `d3.contract.RowCodec` 87; `d3.contract.ExpressionTable` 5; `d3.contract.ExportRow` 3; `d3.contract.SessionDir` 3 |
| `d3.plan.ConfiguredSourcePhaseContract` | 459 | 201 | 0 | 201 | — |
| `d3.plan.RuntimePlanArtifact` | 250 | 106 | 91 | 197 | `d3.plan.RegionInstancePlan` 49; `d3.plan.EdgeBindingCatalog` 40; `d3.plan.PlanRow` 2 |
| `runtime.SymbolicMessageEnvelope` | 492 | 192 | 0 | 192 | — |
| `causynth.WireFlowCatalog` | 351 | 177 | 8 | 185 | `d3.plan.CommunicationCatalogContract` 8 |
| `d3.compose.Solver` | 359 | 177 | 0 | 177 | — |
| `d3.plan.SharedStateEvidence` | 673 | 176 | 0 | 176 | — |
| `d3.plan.SummaryBranchMapping` | 338 | 121 | 52 | 173 | `d3.plan.BranchWitness` 21; `d3.plan.SharedExpressionTable` 15; `d3.plan.BranchPredicateAlgebra` 12; `d3.smt.JsonFields` 4 |
| `d3.explore.SlotTable` | 379 | 137 | 33 | 170 | `d3.explore.ExploreCodec` 16; `d3.smt.Arms` 11; `d3.explore.Corpus` 4; `d3.compose.CorpusIndex` 2 |
| `d3.explore.ClosurePlanner` | 360 | 154 | 13 | 167 | `d3.explore.Corpus` 12; `d3.compose.SmtLowering` 1 |
| `causynth.ExceptionTargetAnnotationScanner` | 273 | 145 | 9 | 154 | `causynth.ExceptionTargetSite` 9 |
| `causynth.CausynthStaticFacts` | 343 | 151 | 0 | 151 | — |
| `d3.plan.BranchPredicateAlgebra` | 337 | 132 | 15 | 147 | `d3.plan.SharedExpressionTable` 15 |
| `causynth.StaticSymbolicSourceDiscovery` | 243 | 132 | 13 | 145 | `d3.plan.ConfiguredSourcePhaseContract` 13 |
| `runtime.ConcolicVmBroker` | 369 | 137 | 0 | 137 | — |
| `d3.smt.VmExpressionIr` | 411 | 106 | 28 | 134 | `d3.smt.VmRows` 28 |
| `d3.plan.GapLedger` | 614 | 133 | 0 | 133 | — |
| `d3.plan.ExactConcreteBranchObservation` | 278 | 127 | 0 | 127 | — |
| `d3.contract.SessionReader` | 191 | 54 | 67 | 121 | `d3.contract.RowCodec` 56; `d3.contract.ExpressionTable` 10; `d3.contract.SessionDir` 1 |
| `d3.plan.BranchWitness` | 255 | 94 | 26 | 120 | `d3.plan.BranchPredicateAlgebra` 26 |
| `d3.plan.SolverPathContext` | 286 | 112 | 0 | 112 | — |
| `d3.plan.SymbolicSourceEvidence` | 550 | 112 | 0 | 112 | — |
| `d3.plan.PlanRow` | 78 | 30 | 81 | 111 | `d3.plan.ConfiguredSourcePhaseContract` 81 |
| `runtime.d3.Lineage` | 321 | 110 | 0 | 110 | — |
| `d3.smt.JavaContainerTypes` | 266 | 109 | 0 | 109 | — |
| `causynth.DeclaredLoopBodyBounds` | 316 | 108 | 0 | 108 | — |
| `d3.explore.SmtText` | 234 | 107 | 0 | 107 | — |
| `d3.explore.Z3Solver` | 180 | 102 | 0 | 102 | — |
| `d3.explore.ExploreCodec` | 219 | 93 | 0 | 93 | — |
| `causynth.ControlDependenceEdgeSupport` | 210 | 91 | 0 | 91 | — |
| `runtime.JUnitMethodRunner` | 180 | 91 | 0 | 91 | — |
| `runtime.PathConditionWindow` | 210 | 86 | 1 | 87 | `runtime.ConcolicVmBroker` 1 |
| `d3.plan.LoopBoundPolicy` | 340 | 86 | 0 | 86 | — |
| `d3.plan.RegionInstancePlan` | 195 | 83 | 2 | 85 | `d3.plan.PlanRow` 2 |
| `d3.smt.ArtifactIO` | 270 | 80 | 0 | 80 | — |
| `d3.smt.JsonFields` | 235 | 80 | 0 | 80 | — |
| `d3.contract.CausalContext` | 231 | 77 | 0 | 77 | — |
| `d3.contract.OccurrenceAddress` | 190 | 62 | 8 | 70 | `d3.contract.Selector` 8 |
| `d3.plan.SmtModelValueCodec` | 207 | 70 | 0 | 70 | — |
| `causynth.StructuralFieldAccessorProof` | 108 | 64 | 0 | 64 | — |
| `option.OptionParser` | 106 | 57 | 6 | 63 | `option.GraphCheckerOptions` 4; `option.OptionError` 2 |
| `d3.compose.SlotTable` | 179 | 61 | 0 | 61 | — |
| `causynth.MapFields` | 170 | 60 | 0 | 60 | — |
| `d3.plan.FieldPathSpec` | 126 | 58 | 0 | 58 | — |
| `causynth.StaticDataflowEdgeSchema` | 110 | 55 | 0 | 55 | — |
| `d3.plan.PathObservation` | 406 | 55 | 0 | 55 | — |
| `runtime.d3.Identity` | 155 | 55 | 0 | 55 | — |
| `d3.explore.Frontier` | 148 | 48 | 6 | 54 | `d3.explore.ObligationFactory` 6 |
| `d3.plan.AutomaticRegionEdge` | 118 | 54 | 0 | 54 | — |
| `d3.plan.MaterializationSpec` | 119 | 54 | 0 | 54 | — |
| `causynth.CausynthTargetResolver` | 100 | 52 | 1 | 53 | `option.GraphCheckerOptions` 1 |
| `d3.compose.JsonText` | 125 | 53 | 0 | 53 | — |
| `d3.plan.CommunicationHandoffSpec` | 126 | 53 | 0 | 53 | — |
| `d3.smt.VmRows` | 137 | 52 | 0 | 52 | — |
| `runtime.OccurrenceMinter` | 158 | 52 | 0 | 52 | — |
| `causynth.CausynthBranchShape` | 106 | 51 | 0 | 51 | — |
| `d3.contract.ExecutionIndex` | 121 | 42 | 9 | 51 | `d3.contract.Frame` 9 |
| `d3.smt.CanonicalJson` | 111 | 51 | 0 | 51 | — |
| `runtime.d3.Interactions` | 179 | 51 | 0 | 51 | — |
| `d3.plan.SharedFieldFlow` | 117 | 41 | 9 | 50 | `d3.smt.JavaContainerTypes` 9 |
| `d3.contract.AttachRow` | 144 | 47 | 0 | 47 | — |
| `d3.smt.JavaPrimitiveBoxing` | 101 | 44 | 0 | 44 | — |
| `d3.contract.RootMintRow` | 138 | 43 | 0 | 43 | — |
| `d3.contract.SessionDir` | 140 | 43 | 0 | 43 | — |
| `d3.contract.Fields` | 115 | 41 | 0 | 41 | — |
| `d3.compose.JavaSmtSorts` | 86 | 40 | 0 | 40 | — |
| `d3.plan.EdgeBindingCatalog` | 139 | 40 | 0 | 40 | — |
