# REPORT-D3 — one copy of everything, and the v1 identity's last two files

Branch `refactor/d3-contract`, tip **`e3fac78b1`**. `mvn -o -q test` green
(49 @Test), `run_engine_campaign_helpers_test.sh` green, after every commit.
Staging `c360ae6e8` and contract v2.0/v2.1 (`40c5ae839`, `f59b5ff49`) merged in.

## Per-package

| package | at `f0be67b87` | now | |
|---|---|---|---|
| `runtime/` | 20,357 | 20,365 | hooks + publisher |
| `causynth/` | 16,949 | 16,955 | PLAN / static analysis |
| `d3/` | 16,437 | **32,015** | contract 3,945 · plan 14,522 · compose 8,551 · explore 2,831 · smt 2,166 |
| `concolic/` | 12,216 | **0 — gone** | |
| `contract/` | 4,498 | **351** | `OccurrenceAddress`, `OccurrenceId` only |
| transformer/option/annotation | 226 | 226 | |
| **src/main** | 71,020 | **70,249** | |

`src/main` is flat-to-down while d3 nearly doubled, because the growth is
staging's explore and compose arriving, not new code here.

## Commits

| | |
|---|---|
| `82c6d1951` | `compose_max_valuations` (CAUSYNTH_COMPOSE_MAX_VALUATIONS, default 16) passed as ComposeMain `--max-valuations`; 40 → 41 config keys |
| `eb62fcad6` | the five forked classes resolved d3-side into a new `d3.smt`; the originals deleted |
| `3fe9844a2` | contract v2.0/v2.1 merged; the d3 fixtures re-addressed the v2 way |
| `f66771c4c` | staging `c360ae6e8` merged (the owners' own fixture migration taken over mine) |
| `cf83104f0` | `d3.plan.SelectorResolution` — one home for IDENTITY-IMPL §D; ComposeMain calls it |
| `92c28af79` | the PLAN vocabulary → `d3.plan`; the JSON/digest helpers → `d3.smt` |
| `e3fac78b1` | the rest of the shared vocabulary → `d3.plan`; `concolic/` removed |

## Per-file disposition

**MOVE — `d3.smt` (8 files).** The shared VM/JSON/SMT vocabulary, one copy:
`JsonFields`, `JavaPrimitiveSmtSemantics`, `VmExpressionIr`,
`JavaContainerTypes`, `JavaPrimitiveBoxing`, `VmRows` (kept the d3 copy, the
`concolic/`+`contract/` originals deleted), plus `ArtifactIO` and
`CanonicalJson`.

**MOVE — `d3.plan` (39 files).** Every one has a live caller under PLAN or the
runtime; none is a leftover of the deleted stack.

| from | classes |
|---|---|
| `concolic/` PLAN | `ConcolicScheduler` (the PLAN main), `RuntimeWorkflowDiscovery`, `AutomaticRegionEdge`, `SharedFieldFlow`, `BoundedLoopComposition` |
| `concolic/` evidence | `SharedStateEvidence`, `SharedExpressionTable`, `VmExpressionTable`, `SymbolicSourceEvidence`, `SymbolicPropagationClosure`, `RecordedEvidenceIdentity` |
| `concolic/` branches | `BranchReplayContract`, `BranchPredicateAlgebra`, `BranchWitness`, `SummaryBranchMapping`, `ExactConcreteBranchObservation`, `SolverPathContext`, `LocalCaseIdentity` |
| `concolic/` helpers | `SmtModelValueCodec` (decodes a model value so the runtime can apply it — the answering mechanism), `ClockRootPhysics` (recognises a clock-reading callee so a clock root is minted — root minting) |
| `contract/` plan artifacts | `ExecutionTask`, `RegionInstancePlan`, `PlanRow`, `RuntimePlanArtifact`, `EdgeBindingCatalog`, `InputActionCatalog`, `CommunicationCatalogContract`, `CommunicationHandoffSpec`, `MaterializationSpec`, `FieldPathSpec`, `SiteId`, `DependencyRole`, `ClosureGoalKind`, `StaticSymbolicSourceDeclaration`, `ConfiguredSourcePhaseContract`, `LoopBoundPolicy`, `GapLedger`, `PathObservation` |
| new | `SelectorResolution` |

Two named DELETE candidates are MOVEs instead, and here is why: **`ClockRootPhysics`**
is not the old clock *policy* — it is `clockCallee()`, how the runtime knows a
call reads a clock and must mint a root there, which the brief keeps;
**`SmtModelValueCodec`** is how a solver model value becomes a Java literal the
runtime can write at a mint, which is answering, also kept. **`LocalCaseIdentity`**,
**`SolverPathContext`**, **`SummaryBranchMapping`** and **`BranchWitness`** are
not read only by the old EXPLORE/COMPOSE: `ConcolicRegionRuntime` and
`BranchReplayContract` read them to record and replay a branch decision. They
die when M2 re-expresses that publication on `DecisionRow`, not before.

**BLOCKED — `contract/` (2 files, 351 lines).** `OccurrenceAddress` (273) and
`OccurrenceId` (78), the v1 identity. Not moved, because they are not kept:
`d3.contract.OccurrenceAddress` replaces them. Eleven files still spell them —
`runtime/OccurrenceMinter`, `runtime/ConcolicRegionRuntime`,
`runtime/ConcolicTaskPlan`, `runtime/RuntimeRegionPlanner`,
`causynth/RuntimeSelectedRegionFinalizer`, and in `d3.plan`
`ConcolicScheduler`, `RuntimeWorkflowDiscovery`, `ExecutionTask`,
`SymbolicSourceEvidence`, `SymbolicPropagationClosure`,
`BoundedLoopComposition` (plus `OccurrenceAddressIsNotARequestTest`).

Every one of them is downstream of the minter: PLAN's addresses are what the
minter stamped, and the scheduler and the plan artifacts only carry them. The
v3 computation (IDENTITY-IMPL §B — the per-thread frame stack, the scope
carry, the causal context) is M2's on `refactor/d3-runtime`, and the brief is
explicit that I take its API rather than write a second one. **Blocked on that
branch; nothing else blocks it.**

## Selector resolution, consolidated
IDENTITY-IMPL §D belongs to PLAN. `ComposeMain.anchorOf` implemented it first
because PLAN did not yet, and I had written a second copy before seeing it —
two answers to "which occurrence did the case mean" is the disagreement an
identity exists to end. `d3.plan.SelectorResolution` is now the only one, with
the composer's semantics whole: an already-resolved address passes through, a
v1 selector matches on node + region + api (the declaration's last path
segment against the anchor's RPC-site tail, or an exact spelling) and takes
the k-th match in the seed's write order, and a selector nothing matches
degrades to a `Lost(UNKNOWN)` address of the region it names, so DECIDE
reports `DECLARATION_MISSING` out of the artifact. `anchorOf` is four lines
that call it.

## Notes for the other agents
- **M3**: `campaign_explore` now breaks on an empty obligations file, so
  ExploreMain's blank-id marker row can go.
- **M2**: the runtime's mint identity is `ConcolicRegionRuntime.handoffMintKey`
  / `handoffMintLabel` (private, D2 markers on both) — re-key by Endpoint when
  the minter lands.
- Test packages follow their subject: `RootDependentCarrierTest`,
  `SymbolicRootPolicyTest` and `GapLedgerTest` moved to `d3.plan`.


---

# REPORT-D3 §final — the v1 identity, and the one thing left

Tip **`f996480b5`**. `refactor/d3-runtime` `a2414f195` merged. `mvn -o -q test`
green (54 @Test), shell helper test green, after every commit.

## Per-package

| package | before D3 | now | |
|---|---|---|---|
| `runtime/` | 20,357 | 23,639 | hooks, publisher, and M2's `runtime/d3` (minter, Identity, SessionPublisher) |
| `causynth/` | 16,949 | 16,955 | PLAN / static analysis |
| `d3/` | 16,437 | 32,007 | contract 3,945 · plan 14,514 · compose 8,551 · explore 2,831 · smt 2,166 |
| `concolic/` | 12,216 | **0 — gone** | |
| `contract/` | 4,498 | **294 — one file** | `OccurrenceAddress` (v1) |
| **src/main** | 71,020 | 73,458 | +3,672 of that is M2's runtime arriving |

## Commits after the merge

| tip | |
|---|---|
| `0feb31990` | **D3-4** — `OccurrenceId` deleted |
| `f996480b5` | **D3-5** — the v1 address shrinks to the plan-identity core |

**D3-4.** Identity v1 numbered the activations of one planned address and wrote
`#a<n>` beside it, because two runs of one address were occurrences it could
not otherwise tell apart; identity v3 tells them apart by the execution index
they entered under, so an address IS the occurrence. One place minted the
suffix (`ActiveRegion.occurrenceId()`) and no longer does; the other sixteen
uses were taking it back off (`OccurrenceId.parse(x).planned()` → `x`) across
`RuntimeWorkflowDiscovery`, `ExecutionTask`, `ConcolicScheduler`,
`BoundedLoopComposition`, `SymbolicPropagationClosure` and
`ConcolicRegionRuntime`. `ExecutionTask` asked it for a consumer's component
and now reads that off the id. The v1 address still *reads* an id carrying the
suffix — a corpus written while something minted it is read, not refused —
with those ten lines inline, so the deletion costs no corpus.

**D3-5.** Two more consumers asked a question that is not about a spelling and
now ask it of the string: `SymbolicSourceEvidence.nodeOf` wants the component,
which is everything before `/region/` in both spellings, and
`ConcolicRegionRuntime` normalised a consumer id by parse-and-re-render, which
only ever stripped the suffix D3-4 stopped minting.

## Blocked: `contract/OccurrenceAddress` (294 lines, 5 files + 1 test)

Not deleted, and it is one coupled island rather than five independent
callers — **the plan's identity**:

| | |
|---|---|
| `runtime/OccurrenceMinter` | mints it, offline, from the recorded trace |
| `causynth/RuntimeSelectedRegionFinalizer` | stamps it onto every activation of the plan |
| `runtime/ConcolicTaskPlan` | counts and matches activations against it at replay |
| `runtime/RuntimeRegionPlanner` | scopes that count |
| `d3/plan/RuntimeWorkflowDiscovery` | compares a case declaration to it |
| `runtime/OccurrenceAddressIsNotARequestTest` | tests the counting rule |

**What blocks it is not the minter API — it is the recording.**
`OccurrenceMinterV2.mint(nodeKey, regionId, CausalContext, ExecutionIndex)` is
merged and I am calling nothing else, but the finalizer runs *offline over the
recorded trace*, where there is no live stack to ask. `Identity.enterCall` /
`exitCall` are wired into `CausynthTraceRecorder`, so the frame stack exists
at record time — but **no recorded event carries an `executionIndex` or a
`causalContext`** (grep: zero hits in the recorder and the finalizer). Until a
region-activation event stamps the two, the offline minter has nothing to
build a v3 address from, and the only way to finish this migration today would
be to invent a second minter, which the brief rules out.

That is the remaining half of IDENTITY-IMPL §B and it is M2's: *the recorder
stamps `Identity.regionEnter()`'s index and the scope's causal context onto
each region activation event.* With that, the migration is mechanical and
short — the finalizer calls `OccurrenceMinterV2.mint` with what the event
carries, `ConcolicTaskPlan` compares `id()`s instead of counting ordinals
(v3's own argument: an ordinal "moves whenever an unrelated invocation is
inserted earlier in the run, which is what a branch flip does"),
`RuntimeRegionPlanner`'s counter scope goes with the counting,
`RuntimeWorkflowDiscovery.declares` becomes `SelectorResolution`, and
`contract/` is removed.

## Expected end state
`runtime/`, `causynth/`, `d3/` — reached for every package except the single
file above, which needs one field on a recorded event that M2 owns.


---

# REPORT-D3 §final (2) — the v1 identity is gone; `contract/` is gone

Tip **`dcdafa875`**. Merged in: `refactor/d3-runtime` `330627375` (M2's
recording half) and staging through `a29e5c8df`. `mvn -o -q test` green
(52 @Test), `run_engine_campaign_helpers_test.sh` green, after every commit.

## Per-package — the end state

| package | before D3 | now |
|---|---|---|
| `runtime/` | 20,357 | **23,644** (hooks, publisher, `runtime/d3`) |
| `causynth/` | 16,949 | **16,962** (PLAN / static analysis) |
| `d3/` | 16,437 | **34,148** — contract 4,213 · plan 14,578 · compose 8,890 · explore 3,703 · smt 2,764 |
| `concolic/` | 12,216 | **0 — gone** |
| `contract/` | 4,498 | **0 — gone** |
| `annotation/` `option/` `transformer/` | 226 | 226 |
| **src/main** | 71,020 | 75,317 |

`src/main` is up because d3.explore, d3.compose and `runtime/d3` arrived from
three other branches; the packages this task was about are both at zero.

## Commits

| tip | |
|---|---|
| `0feb31990` | **D3-4** `OccurrenceId` deleted — an address is the occurrence |
| `f996480b5` | **D3-5** the v1 address reduced to the plan-identity core |
| `23380b59c` | **D3-6** PLAN mints identity v3 through `OccurrenceMinterV2` |
| `af02f973c` | **D3-7** admission is id equality, not a count |
| `e20c7a88d` | **D3-8** `contract/` removed |
| `2b1773ca2` | PLAN can be told to grow the retained set |
| `efb07e6be` | **D3-9** the epoch loop distinguishes the two divergence causes |

**D3-6 — the recording reaches the minter.** M2 stamps every execution event
with `executionIndex` (the call path from the scope root) and `causalContext`
(`Root:<ROLE>#k` / `Lost:<ROLE>` / `Anchor:<correlation>@<transport>/<api>`).
`MethodEvent` carries both, the offline loader reads them off the row, the
`RUNTIME_REGION_ACTIVATION` record passes them on, and
`RuntimeSelectedRegionFinalizer` mints through `OccurrenceMinterV2` — one
computation of an address, so PLAN's offline pass and the replay's live one
cannot disagree. The activation ordinal went with the v1 address that needed
it. A `causalContext` this build cannot read degrades to `Lost(UNKNOWN)`
rather than throwing.

**D3-7 — admission.** `ConcolicTaskPlan` numbered the entries of each
(node, region) bucket and admitted on a matching k. v3 has no k, for the
reason v3 gives: an ordinal moves whenever an unrelated invocation is inserted
earlier in the run, which is exactly what a branch flip does — so the count
that admits a replay is the one thing a flip is guaranteed to disturb. A
candidate's address is now minted the way the session publisher will mint it
and admission is `address.id().equals(observed.id())`. `Identity.atScope()`
rather than `regionEnter()`: same frames, no side effect, because admission
asks before the region is opened. Gone: `countEntry`, `countInvocation`,
`invocationCounterKey` (both forms), the ordinal map,
`addressesOccurrenceBeyondBound`.

**D3-8 — the last three.** `RuntimeRegionPlanner`'s counter scope was a
grouping key, not an identity, and is now the three strings it always was.
`RuntimeSelectedRegionFinalizer.occurrenceKey` validates against d3.contract.
`RuntimeWorkflowDiscovery.declares` asks the way IDENTITY-IMPL §D does —
`Selector.matches` on node, region and api — minus the k, because which
candidate the campaign is about is resolved once, against the seed session,
where the order that makes k mean anything is.

**D3-9 — the epoch rule.** INTERACTION-ID §8's two causes get two epochs. A
"retained set must grow" divergence names a region that ran with entry hooks
only; `campaign_retained_growth` reads those ids, the loop carries them to the
next epoch's PLAN as `--retain-regions`, and PLAN naming them is what makes
INSTRUMENT instrument them. Any other divergence is a new epoch over the same
retained set. `ConcolicScheduler` fails closed with `RETAINED_SET_CANNOT_GROW`
when no candidate carries a required region — instrumenting the same set again
would diverge identically. Frozen inputs stay per epoch: instrumented classes
live under `${iteration_dir}/instrumented-classes`, so a growing epoch
instruments into its own tree.

## Still open, and it is not mine to close

**The branch-record types are not dead yet.** `SummaryBranchMapping`,
`BranchWitness`, `SolverPathContext`, `LocalCaseIdentity`,
`BranchPredicateAlgebra`, `ExactConcreteBranchObservation`,
`BranchReplayContract` and `PathObservation` all still have live readers:
`ConcolicRegionRuntime` and `d3.plan.ConcolicScheduler`.

`DecisionRow` publication has not replaced them — it runs *beside* them.
`runtime/d3/FocusedReplay` reads `DecisionRow`s and matches an obligation's
prefix; `ConcolicRegionRuntime` still drives its own forcing through
`BranchReplayContract.ReplayProgress` (four call sites). Two implementations
of one rule is precisely what the no-dual-types rule forbids, but which one
dies is M2's call: it owns the replay path and built `FocusedReplay`, and
cutting `ReplayProgress` out of admission from outside would be rewriting that
path blind. When M2 says `FocusedReplay` is the only prefix matcher, the
deletion is mechanical and I will take it.
