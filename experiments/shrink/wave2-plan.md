# Wave 2 plan — in-file / in-package parallel implementations

Precondition: the wave-1 gate passes (`mvn test` 531/0 done; the matrix on
jar 10:21 CDT at `matrix-20260825T152212Z` must be 20/20 with the per-row
symbolic-variable set identical to `matrix-20260825T044357Z`).

Rules are wave 1's, plus: **skip anything the wave-3 design center deletes
outright** (`symbolize-every-occurrence`): the scheduler's selection layer,
the per-version boundary ledger, selector admission in the runtime. Merging
code that is about to be removed is wasted risk.

Realistic wave-2 total: **≈ −5,000 to −5,500** (the inventories' −8k/−10k
included items that are wave-3 deletions or that wave-1 executors measured
as not mergeable). Waves 1+2 land near **81,000**.

| lane | items (est. lines) | gate sensitivity |
|---|---|---|
| **smt** (−2,800) | 1. Delete `CausalGraphWriter` + `run_engine.sh campaign_graph()` + `graph/causal_model.json` from the optional list; `CanonicalSessionModel` → `counts` + `gaps` only, all seven `run_engine.sh` reads preserved (−1,000). 2. One expression encoder: delete `ConcolicConstraintSolver.Encoder` (+Sort/Term+statics), keep `ConcolicSmtComposer.Emitter`; Solver keeps `SymbolNames`, `bindRecordedReadCut`, replay-support planning, `finish()` (−1,500). 3. One Java-type→SMT-sort enum beside `ContainerSmtCodec` (−100). 4. `BooleanReach` consumes the manifest's `portOccurrences`/`configuredSourceMaterializations` instead of re-scanning `candidate.smt2` text; one `PortIndex` (−150). 5. `RelationSummary.cases()/pathCoverageState()` → composer's 8 `toJson()` re-reads collapse (−40). | `candidate.smt2` text changes for every row → matrix + variable-set check are the gate; also compare recorded Z3 model counts per row (README table). |
| **static** (−1,500) | 1. Eight discovery/replay Jimple emitter pairs → one per hook family (floor 520 / ceiling 800). 2. `CausynthPipeline` natural-loop derivation → consume `CfgLoopControl.LoopCfg` (−150). 3. The 49 hand-written 2–3-line hook emissions + the duplicated ~40-line argument materialize/symbolize block + `getThisLocal`/`parameterLocal`/phantom-class/`instrumentationSafe` copies (−200). 4. `SeedBackwardStaticAnalyzer`: `intersectsLocal`≡`exactIntersects`, `MethodWorkSet`+`DirtyRelevantSet` → one, 10 cache accessors → one `memoized`, 5× guard-operand walk, `addEdge→addEdgeInternal` shim (−100). 5. Zero-reader public API on `InstrumentationPlan`/`ExactHeapOutputCapture`/`DeclaredLoopBodyBounds`, unused 7-arg `RequestPort` ctor (−60). DEFER the five caller expanders + six propagation walks (−360) to its own wave: it is the order-sensitive fixpoint (`DF.<n>` ids). | Emits into Hadoop bytecode → matrix is the gate; instrumented-class digests in `run-manifest.json` will change and that is expected. |
| **runtime** (−450) | 1. Eight materialize/symbolize hook bodies → one matcher behind the fixed hook names (−200, HIGH). 2. Unblock the static lane: `CausynthTraceRecorder.java:1027` drop `closure.gaps`; delete `communication_runtime_gaps.jsonl` write (1943-1970) (−60 with the causynth side). 3. runtime Map-coercion twins (`rows/asMap/text/strings/number/longNumber`) → `MapFields` (moved to `contract/`) (−90). 4. `RuntimeRegionPlanner.fieldOwner` ≡ `CausynthStaticFacts.fieldOwner` (−20). 5. `normalizeNumbersInPlace` vs `deepCopyValue`: keep one that mutates in place and retains null entries (−50, with planning). NOT: map/field admission merge (measured 0.52/0.68 — not a merge); the `*ForTests` seams and `commitMap/FieldVersions` — they die with selector admission in wave 3. | matrix. |
| **planning** (−300) | 1. Four `*OutputClosure` builders → one skeleton + slice-source strategy (−270, HIGH). 2. `--target-first` shim in `run_engine.sh:1545,1745` + `knownOption` (−2). 3. `RegionInstancePlan` six `*View` accessors → one per field, callers in `RuntimeWorkflowDiscovery`/`ConcolicScheduler` (−30). SKIP (wave-3 deletions): `resolveSourcePhaseOwnership` → `phaseProjections` union; fold/unfold pair. | matrix. |
| **contract** (−270) | 1. `JsonFields` widening (`requireFile`, `textSet`, `strings`, `requiredObject/primitiveString/exactInteger` public) + delete the remaining private copies in causynth (8 files), runtime (6), concolic (20) (−200). 2. Cross-lane small deletions now unblocked: `acceptsInstrumentedBound` first param, `boundAuthority()`, `intDeclaration()`, `manifestState`, `DeclaredLoopBodyBounds` range check → `bodyBound()`, `CommunicationHandoffSpec.SCHEMA_VERSION` + `RuntimeRegionPlanner:6098-6099` (−70). | unit suite. |

Executor brief additions for wave 2 (beyond the wave-1 template):
- per-lane scratch subdirectory (wave-1 lanes overwrote each other's scripts);
- "second pair of eyes" section required for any change that is not provably a no-op (the static lane's `getSubSignature()` switch is the model);
- the matrix-visible artifacts a lane changes must be listed (candidate.smt2 shape, instrumented-class digests, manifest members) so the gate diff can be read.

Wave 3 (the design center) is drafted separately once the wave-2 gate passes:
mint a fresh symbol per occurrence; at a read use the VM expression if present
else a new symbol; composer reads recorded lineage directly; delete
`SymbolicInputSelection`, runtime selector admission, the boundary ledger, the
Hadoop selector hooks; manifest names every free symbol without lineage.
