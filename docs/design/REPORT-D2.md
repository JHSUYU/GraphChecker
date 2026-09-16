# REPORT-D2 — deleting the old EXPLORE/COMPOSE stack, and the reachability sweep

Branch `refactor/d3-contract`, tip **`f0be67b87`**. Staging `378cd6e36`
(d3.explore + d3.compose) merged in before the sweep. `mvn -o -q test` green
(44 @Test) and `src/test/shell/run_engine_campaign_helpers_test.sh` green after
every commit.

## Totals

| | before D2 (`058ee2491`) | after D2 (`f0be67b87`) |
|---|---|---|
| `runtime/` | 20,478 | 20,357 |
| `contract/` | 5,378 | **4,498** |
| `concolic/` | 37,736 | **12,216** |
| `causynth/` | 16,949 | 16,949 |
| `d3/` | 3,286 | 16,437 (merged from staging) |
| transformer/option/annotation | 226 | 226 |
| **src/main total** | **84,053** | **71,020** |
| src/test java | 6,853 | 3,769 |
| @Test | 62 | 44 |

Java deleted by D2: **26,609 lines across 91 files** (`git diff --stat
058ee2491..f0be67b87`), against 10,478 inserted — all but ~250 of which is the
merged d3.explore/d3.compose, not new code of mine.

## Commits

### D2-1 `91a9b0979` — unhook the runtime from the old row shapes
The runtime published the WIRE row (`VmHandoffEvidence`), the handoff gap row
(`RpcExpressionHandoff`) and the family key (`HandoffPhaseContract`). M5 left
those with no reader, so the publication goes and the mechanism under it
stays.

**Kept** — the woven hooks `exportCommunicationLeaf`/`attachCommunicationLeaf`,
the VM export/attach calls, the read-back of the attached expression, and the
mint of v_H with its answering. The mint needs an identity and a label, so
both became the runtime's own: `handoffMintKey(port, consumer occurrence,
k-th attach of this element, element path)` and `handoffMintLabel` →
`HOFF.<sha256>`, each carrying `// D2: … runtime/d3 SessionPublisher (M2)`.
The VM status ABI moved to `ConcolicVmBroker`, which is what returns it.

**Deleted** — `recordHandoffGap`, `drainUnownedHandoffGaps`,
`UNOWNED_HANDOFF_GAPS`, `noteAttachFiledElsewhere`,
`reportUnattachedMessageLeaf`, `noteOutboundEnvelopeRefused` (and their call
sites in `SymbolicMessageEnvelope` and `CausynthTraceRecorder`),
`ActiveRegion.vmHandoffEvents`/`rpcHandoffGaps` and their envelope members,
`PathObservation.vmHandoffEvents()`. Two constants moved to the row that
writes them: `SummaryBranchMapping.SESSION_EVENT_ID` and
`ConcolicScheduler.TARGET_CONCRETE_OBSERVATION`.

### D2-2 `a06fa960c` — the IMPORT stack (3,598 lines)
`ConcolicSummaryImporter` (2,785), `PublicationContract` (379),
`InitialContainerObservation` (434); tests `PublicationContractTest`,
`HandoffBelongsToItsConsumerTest`, `RegionPathWorklistTest` (11 @Test). It
folded because there was one row kind; per-kind session files leave nothing to
fold, and M5's IMPORT already reads the sessions.

### D2-3 `976392824` — EXPLORE + COMPOSE + SOLVE + DECIDE (~21,000 lines, 26 files)
One commit because the stack is one strongly-connected blob: the flip planner
reads the worklist, the worklist the family rows, the family rows the flip
query, the constraint solver all three, the valuation solver the constraint
solver and the composer, the claim policy the composer's manifest. No order
deletes them one at a time and leaves a tree that compiles.

`ConcolicPathFlipPlanner`, `ConcolicPathFlipSolver`, `ConcolicConstraintSolver`,
`RegionPathWorklist` (with `CLOSURE_INCOMPLETE` and `pathSetClosed`),
`ResolvedFlipQuery`, `HandoffFamilyRows`, `SymbolicRootInventory`,
`PathReplayTaskFactory`; `PathMergeComposer` (with `pinUnproducedArrivals`),
`PathMergeLowering`, `ContainerSmtCodec`, `InSessionReadResolver`,
`TargetReachPathQueryBuilder`, `TargetAnchorEvidence`, `JavaSmtSorts`,
`VmLoweringCore`, `VmTermLowering`, `SmtSymbolTable`, `ComposedManifest`;
`RootValuationSolver`, `SmtLibQueries`; `ClaimPolicy`, `WitnessLegitimacy`,
`TargetOccurrenceElection`; `CliArgs`, `CoverageDivergence`. Tests:
`TargetOccurrenceElectionTest`, `InSessionReadResolverTest`, `ClaimPolicyTest`,
`PathMergeComposerTest` (13 @Test).

### D2-4 `d5aef9834` — the handoff row contract and the gap scopes it fed
`VmHandoffEvidence`, `HandoffPhaseContract`, `RpcExpressionHandoff`,
`HandoffMintTest` (5 @Test). `GapLedger.Scope` collapses to `ALWAYS`:
`KEPT_SLICE` went with the slice in D1, `COMPOSED_PORT` with `RPC_HANDOFF_GAP`,
and `flipWaveDiagnostic` with the distinction between a flip replay and a
focused one. A GapRow states its own class where the runtime raises it, so the
fold partitions rather than re-deciding.

### D2-5 `f0be67b87` — the reachability sweep
Roots: `run_engine.sh`'s `java … <Main>` invocations, `experiments/*/execute.sh`,
everything under `d3/`, the woven runtime hooks, the 21 workload-called
statics, `annotation/`, `option/`, `transformer/`. References computed with
comments and string literals stripped, so a class reached only from prose does
not count.

**Result: 0 unreachable classes.** One looked unreachable and stays, named
rather than kept silently: `runtime/JUnitMethodRunner` (180 lines) has no
caller in the repo and is the `main` every case's `execute.sh` launches —
exactly the trap `graphchecker-external-callers` §3 describes. It is now a
root of the sweep.

What the sweep did find is the ledger promising checks that no longer happen:
**120 registered gap codes, 45 with a live raiser.** The 75 deregistered are
the vocabulary of the deleted stack — the flip solver's admission and
materialization refusals, the importer's schema and duplicate refusals, the
composer's configured-source and manual-root term refusals, the valuation
solver's undecided-model refusal, the linked replay's topology-epoch refusal.

## Against the ≤ 70,000 target: 71,020, and where the 1,020 is

Every remaining class in `concolic/`, `contract/` and `runtime/` is reachable
from a production entry point, so there is nothing further for me to delete.
The one consolidation left is **d3 forking classes it could import** — 1,922
lines held in the non-d3 copy of each pair:

| class | d3 copy | original |
|---|---|---|
| `JavaPrimitiveSmtSemantics` | d3/compose (635) | concolic (636) |
| `VmExpressionIr` | d3/compose (411) | concolic (411) |
| `JavaContainerTypes` | d3/compose (266) | contract (266) |
| `JsonFields` | d3/compose (235) | concolic (235) |
| `JavaPrimitiveBoxing` | d3/compose (101) | contract (101) |
| `OccurrenceAddress` | d3/contract (313) | contract (273) — **not a duplicate**: v2 lineage vs the v1 address PLAN still mints |
| `SessionReader` | d3/explore (101) | d3/compose (150) — two d3 copies |

The originals are live (PLAN and the runtime use them), so deleting them needs
d3 to import them instead, which is the d3 agents' call, not mine. Dropping
the five true forks would land src/main at **~69,400**.

## The mechanisms named in the brief, and where each went

| named for deletion | outcome |
|---|---|
| `pinUnproducedArrivals` | gone with `PathMergeComposer` (D2-3); d3.compose states arrivals per path |
| `elementAbsent` | gone with `VmHandoffEvidence` (D2-4); a delivery with no producer is a degraded producer Endpoint (R-I1), M2's to publish |
| `CLOSURE_INCOMPLETE` / `pathSetClosed` | gone with `RegionPathWorklist` and `PathMergeComposer` (D2-3) |
| `flipWaveDiagnostic` | gone with the scope (D2-4) |
| `RegionPathWorklist` closure/coverage machinery | gone whole (D2-3) |
| `HandoffFamilyRows` | gone (D2-3); d3.explore carries its own interaction-keyed algorithm |
| GapLedger scopes/kinds only they consumed | 75 codes deregistered, 2 scopes removed (D2-4, D2-5) |
| config keys | `composer`, `reach_max_inputs`, `reach_max_valuations` (43 → 40) |

## One open question for the planner
ComposeMain accepts `--max-valuations`; the campaign no longer passes it,
because the key that bounded the old solver's enumeration
(`reach_max_valuations`) went with that process. If the composer's valuation
enumeration should stay campaign-bounded, it needs a key of its own — say
`compose_max_valuations` — rather than the reach key coming back.
