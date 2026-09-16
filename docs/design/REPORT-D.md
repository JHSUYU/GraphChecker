# REPORT-D — deletions on refactor/d3-contract

Base: staging `9b9961b0a`. Staging `19b311384` (the `d3.contract` package) merged in
after D5. Every commit below compiles, passes `mvn -o -q test`, and passes
`src/test/shell/run_engine_campaign_helpers_test.sh`.

## Baseline and totals

| | src/main | src/test | run_engine.sh | @Test |
|---|---|---|---|---|
| base `9b9961b0a` | 82,318 | 6,741 | 4,094 | 61 |
| after D1+D2+D5 | 81,009 | 6,361 | 4,003 | 58 |
| **deleted** | **−1,309** | **−380** | **−91** | **−3** |
| after merging `19b311384` | 84,295 (+3,286 new `d3/contract`) | 6,853 | 4,003 | 62 |

## Commits

### D1 `8db218821` — Delete linked replay: one focused occurrence per obligation
A replay had a PRIMARY member and COMPANION members; the primary flipped one decision
and its companions re-ran the regions its path needed, in the same JVM. That is the
coupling DESIGN3 Phase 2 replaces, and the reason an NN-side loop-prefix mismatch
could reject a DN task.

Deleted: `concolic/LinkedReplayBundle.java` (229), `concolic/ReplayTaskSlice.java`
(523), `PathReplayTaskFactory.createLinked` + `distributeAssignments`,
`distributeGuardedReads`, `nodeOf`, `crossesAHandoff`, `handoffPhaseOwners`,
`actionOwners`, `configuredPhaseOwners`, `modelAssignments` (338 lines; replaced by
`createFocused`, 26), the bundle decode in `ConcolicPathFlipSolver`, the
`List<JsonObject> linkedActivations` parameter of `ConcolicConstraintSolver.solve`
(`LinkedActivation` → `FocusedActivation`), the slice decide/rows/telemetry/location
artifacts in `ConcolicScheduler`, `linkedReplayRole` in `ConcolicTaskPlan` +
`ConcolicResultPublisher`, `GapLedger.Scope.KEPT_SLICE` + `onKeptSlice` +
`classOf(String,boolean)` + `sliceConditional` + the `sliceConditional` ledger member,
and in `run_engine.sh` `campaign_kept_slice_json`, `sliceVerdict`, the kept-slice
document and its jq bindings, and the two `linkedReplayRole == "PRIMARY"` selections.
Tests: `ReplayTaskSliceTest` (3 @Test) deleted; `GapLedgerTest` and the shell test's
GAP-4 rewritten to the no-slice rule.

`linkedReplayGroupId` renamed `replayGroupId`: the propagation ledger the tasks of one
JVM invocation share is real and was never the bundle's.

### D2 `3d5fb0599` — Delete request-family addressing: an occurrence is not a request
The address carried a fifth component, the request family `(source, api)` of the
innermost request in force, and planner and replay both counted k within it.
INTERACTION-ID R-I2: an interaction is identified by its two endpoints, and which
request an activation was reached under names neither.

Deleted: `OccurrenceAddress.familyOf`/`family()`/the 4-arg `of()`/the family arm of
`matches`, `describe`, `counterScope`, `render`, `equals`, `hashCode`;
`ConcolicTaskPlan.countedFamily` and the family parameter of `invocationCounterKey`
and `observedAddress`; the family argument of `OccurrenceMinter.reserveOrdinal`,
`mint` and `occurrenceId`; `RuntimeRegionPlanner.replayInvocationScope`'s `familyOf`;
`RuntimeSelectedRegionFinalizer`'s family read; `TargetOccurrenceElection`'s family
sort key; `RuntimeWorkflowDiscovery`'s "family and k" declaration form.
The `@family` suffix still parses and is **discarded**, so the six cases' declaration
strings keep working and name the occurrence they always named.

### D5 `b076a1943` — Delete target-occurrence ranking
The ledger ranked reported occurrences when the case declared none (accepted over
unaccepted, composed over never-composed, anchor order to break ties) and published
the winner's verdict as the campaign's. On hdfs-17899 bug1 round 1 that elected an
unscheduled occurrence which sorted ahead of the declared one, and the campaign
stopped on a row with no artifacts.
Deleted: `outranks`, `accepted`, `composed` and the ranked-fallback arm of `elect`,
plus the multi-row branch of `electionReason`. One reported occurrence with no
declaration is the answer; several are a refusal naming them.

## Not deleted, and exactly why

Two of the six listed mechanisms were already gone at the staging tip: the composer's
**request-family arm filter** and **per-port root naming** (`PathMergeLowering`) — no
occurrences remain of either. The rest are blocked, each on a replacement another
milestone is building. Deleting them now would not remove a mechanism; it would remove
a soundness gate and leave the pipeline asserting less than it knows.

| # | mechanism | what blocks it | what it costs to delete early |
|---|---|---|---|
| 3 | `VmHandoffEvidence.elementAbsent` + the producer-omission licence | M2's **degraded producer endpoint** (R-I1: node, role, window-local k, `lineageLost=true`). Today a delivery that carried no envelope element is the only way a row may name no producer. | The publisher refuses every such row: 11 of bug3's expiry attaches and 52 of 11741's have `producerOccurrenceId = UNPLANNED` today. Recording stops. |
| 3 | `RpcExpressionHandoff` `NO_ACTIVE_REGION` / `MISSING_METADATA` / `UNKNOWN_HANDLE` | M2's **entry rule** (mint at every declared port regardless of selection). ~25 call sites in `ConcolicRegionRuntime` raise `MISSING_METADATA` alone. | These are the runtime's only statement that a capture could not be taken. With no entry rule the captures still fail; deleting the codes makes them silent, which is the opposite of fail-closed. |
| 3 | `HandoffPhaseContract.phaseId` as the family key | M3/M4's **interaction key**. `HandoffFamilyRows` is explicitly KEPT ("becomes interaction-keyed in M3/M4") and selects by phase id today. | Families lose their only key; every arm is unselectable. |
| 4 | `PathMergeComposer.pinUnproducedArrivals` (R-PIN) | M4's **per-path read** (`reads_p`: `v_H(I) = answered_p | e_paired | x_p`) and R-I5's unattested arm — the per-path pin is its degenerate form, not a separate idea. | v_H becomes free, and the solver answers the target with a delivery the system never made. That is laneRA's nine block-key-expiry phases, verbatim. |
| 4 | `CLOSURE_INCOMPLETE` / `pathSetClosed` in `RegionPathWorklist` + `PathMergeComposer` | M4's closure accounting. | This is what withholds a **closed UNSAT** when the path set is open. Deleting it lets `NO_SUPPORTED_WITNESS` be claimed on an unexplored corpus. |
| 4 | `GapLedger.flipWaveDiagnostic` (3 codes) | nothing — but its premise is still true. A flip replay addresses an occurrence of a *hypothetical* execution whether it is linked or focused; the qualifier was never about companions. | Three codes become BLOCKING on every flip wave, so every campaign stops. |
| 4 | `Scope.COMPOSED_PORT` / `composedPortConditional` | the entry rule (as #3). | Same as #3. |
| 6 | `ConcolicSummaryImporter`'s folding of the single `CONCOLIC_REGION_RESULT` row | M2's **per-kind session files** (`SessionDir`: activations/decisions/exports/attaches/writes/reads/roots/targets/gaps `.jsonl`). The importer folds the ten member arrays *because* there is one row kind. | There is nothing to read. The per-kind rows are M2's publisher; the importer's folding is the only reader the corpus has until then. |

The rule applied throughout is the one in `graphchecker-external-callers` §4: a helper
left caller-less by your own deletion is a signal to re-check, not to delete deeper.
Each row above is a mechanism whose replacement is named, owned and not yet merged.

## External-caller check
Every public member of `runtime/` and `annotation/` in the memory table was grepped
across the eight `/opt/hadoop-hdfs-*` trees and `/opt/solr` before touching it. None
of the 21 APIs changed signature. `OccurrenceMinter.reserveOrdinal`/`mint`/
`occurrenceId` are public and did change arity — they are **not** in the table and
have no caller outside this repo (`ConcolicRegionRuntime`,
`CausynthTraceRecorder`, `SymbolicMessageEnvelope`, `Debug` are the only entries).
