# Concolic integration contract

This document describes the boundary between instrumented Java code,
GraphChecker, and the custom JDK. The graph chooses what to observe and replay;
the custom JDK supplies the symbolic values used by the SMT query.

## From the annotated target to a runtime plan

Static analysis starts at the annotated target and finds a backward dependency
closure of region skeletons, communication sites, shared-state sites, explicit
symbolic sources, and retained loops. That candidate graph and its skeletons
are the only static product; every address in the plan comes from a recording.

Two traces resolve it, and one finalization mints from both:

1. **Pass-1 lite trace.** A cheap instrumented run of the workload. It says
   which skeleton regions actually activated, which causal anchors they
   activated under, and what the topology is. Nothing symbolic is recorded.
2. **Pass-2 rich trace.** Only the regions pass 1 selected are instrumented
   richly: symbolic sources, message envelopes, shared-state reads with their
   bounded writer snapshots, and loop counts.
3. **Refinement** folds the rich observations back into the dependency graph,
   dropping edges no execution took and adding the shared locations the
   recording showed are read across regions.
4. **Finalization** mints each region occurrence exactly once, from the
   refined graph, and records on every plan row the basis it was admitted
   under. Every address in the plan is an address some recording produced.

A plan row's `admissionBasis` is one of: the target's own cone; a declared
communication endpoint (`rootAuthority: COMMUNICATION_ENTRY`); or
`SHARED_LOCATION_DEMAND_V1`, the transitive demand that pulls in whoever writes
a shared location the cone reads, with `demandDepth` recording how many hops
back it sits. That demand is gated by the care set -- the locations the target's
cone actually reads -- so a workload's unrelated shared state does not enter
the plan.

The result is `concolic_region_plan.jsonl`: one row per planned occurrence,
carrying its region, occurrence id, source key, root selector, admission basis,
retained loops, `closureGoals` (including the symbolization actions and their
recorded `primitiveValue`) and `communicationHandoffs`. Every later stage
addresses the recording through this file.

A scheduled member names one region occurrence and one local path goal:

```json
{
  "taskId": "TASK.SEED.<sha256>",
  "goalId": "GOAL.REGION_PATH.<uuid>",
  "goalKind": "REGION_PATH_CLOSURE",
  "regionId": "REGION.<uuid>",
  "sourceKey": "node#epoch0",
  "occurrenceId": "node#epoch0/region/REGION.<uuid>#1",
  "rootSelector": {
    "method": "<Worker: int compute()>",
    "kind": "RECEIVER_CONTEXT",
    "causalAnchor": {"kind": "REGISTERED_SOURCE", "sourceKey": "node#epoch0"},
    "invocationOrdinal": 1
  }
}
```

A scheduled task id is `TASK.SEED.<sha256>` over the member's source
occurrence, relation content and exact port set; the replay task minted for a
solved flip is `TASK.REPLAY.<sha256>`. `goalId` is `GOAL.REGION_PATH.` or
`GOAL.TARGET_REACH.` followed by a UUID derived from the occurrence id, and
`goalKind` is correspondingly `REGION_PATH_CLOSURE` or `TARGET_REACH_CLOSURE`.

An occurrence id is a planned address,
`<sourceKey>/region/<regionId>#<ordinal>`, optionally followed by
`#a<ordinal>` naming the activation that ran it. One planned address may be
entered several times in one replay, so every compatible activation is
published as its own occurrence rather than one being answered and the rest
reported as an ambiguous address. Plan rows, relations and
target-reach queries carry the planned address; a summary row carries the
activation form and repeats its planned address in `plannedOccurrenceId` beside
`activationOrdinal`. A plan and a summary are matched on the planned address,
never on the activation.

A schedule is drawn from exactly one closure. `ConcolicScheduler
--closure-mode` is `candidate` (every occurrence the frozen region plan
declares), `seed-replay` (only the occurrences a seed activation can replay) or
`active-observed` (only the occurrences this iteration's summaries observed),
and the campaign states which one each stage uses. `schedule_max_jobs` caps how
many workload JVMs a stage starts at once; members of one linked bundle are
never split across jobs.

All members in the selected causal closure form one linked replay bundle. They
execute in one workload JVM so native expression handles, shared-state
versions, and boundary identities remain valid across the whole causal chain.
A bundle is seeded from the plan, not from whatever a worker directory happens
to hold, so the same bundle replays identically in any stage.

Two envelopes carry the VM's evidence out of that JVM:

- `SHARED_FIELD_VERSIONS` -- for each selected shared location, the retained
  version list under the version lock at the read. Each version carries its
  session-monotonic `fieldVersionId`, its writer case, and its expression. The
  earliest version is `INITIAL`; when the VM could capture the location's whole
  content at that point it also publishes `initialSnapshot`, and membership
  over the initial state is then decidable rather than free.
- `CONCOLIC_PATH_CONDITION_RANGE` -- the region-local path condition, delimited
  so the importer can tell one region's conditions from its callees' without
  re-deriving them.

## Explicit symbolic roots

There are two root authorities:

- a configured application source such as a NameNode configuration field;
- a planned manual symbolization action, including the public symbolization
  hooks used by the HDFS workloads.

Each successful mint records stable source identity, occurrence, Java type,
and solver term. A value with no explicit root or propagated expression is a
coverage gap. The runtime and composer do not manufacture an unconstrained
replacement symbol.

### Declaring which roots an experiment wants

Most roots are proposed automatically: any primitive return of a call the
analysis does not hold, reached backwards from an explored branch, becomes an
`EXTERNAL_CALL_RETURN` input port. For the HDFS block-key workloads that is
every `<org.apache.hadoop.util.Timer: long now()>` return. An experiment that
does not want the whole automatic set narrows it with
`causynth_symbolic_inputs=@config/symbolic-inputs.jsonl`.

The file is a **restrictive allowlist over roots, not over symbols**: with it
present, the only input actions that may mint are the ones it names plus the
two exempt authorities. Every other input stays `SYMBOLIC` and is tracked as
a carrier, reusing whatever expression the VM propagated to it -- with one
exception, an undeclared `EXTERNAL_CALL_RETURN`, which has no propagated
expression to reuse and is therefore `CONCRETE`. A region the file does not
mention mints nothing and still carries everything. Without the file every
automatic candidate mints. "Carriers" below has the whole decision table.

One JSONL row per region. `regionId` is required and must name a region the
runtime plan actually contains; the other three keys are optional sets of
names, any of which admits an action:

| key | matches the action's |
|---|---|
| `fieldSignatures` | `accessFieldSignature` or `declaredFieldSignature` |
| `portIds` | `portId` or `symbol` |
| `cells` | `cell` |

The retired `carrier`-prefixed twins (`carrierFieldSignatures`,
`carrierPortIds`, `carrierCells`) are refused by name: every input this file
does not mention is already tracked as a carrier.

`cells` is how a call return is named, since it carries no field signature: an
`EXTERNAL_CALL_RETURN` action's cell is `<callee signature>.return`, identical
at every call site of that callee inside the region, so one entry declares
"this region's wall clock". Example, from
`experiments/hadoop/hdfs-17899/symbolic-inputs.jsonl`:

```json
{"regionId":"REGION.aaa1cfd7-...","fieldSignatures":["<org.apache.hadoop.security.token.delegation.DelegationKey: long expiryDate>"],"cells":["<org.apache.hadoop.util.Timer: long now()>.return"]}
```

A declared row does not only survive the narrowing: it **mints**. Once a
shared-state carrier is installed, every later read of a field arrives wrapped
in a `ReadFrom`, including a field only ever written from constants, and the
automatic rule reads that wrapper as "already propagated" and skips the mint --
so a declared field could stay concrete. A declared source of primitive type
asks the strict question instead (is anything symbolic actually inside the
tree?) and mints where the answer is no, recording the usual
`PLANNED_MANUAL_SYMBOLIZATION_V1` evidence. A declared read that a symbol has
already reached still flows, so declaring both a root and the values derived
from it does not fork the chain: on the HDFS block-key experiments the clock
is the mint and `DelegationKey#expiryDate` flows from it. Non-primitive
declarations keep the loose rule, since a container or reference has no root
to mint.

### Carriers

Concretizing a read is not the neutral option it looks like. A `CONCRETE`
action is one the plan never symbolizes, so the VM publishes no `ReadFrom`
candidates and no container versions for it; the guarded read family the
composer builds over a shared location then has no writer cases to admit, the
observed closure has nothing to explore, and a root that only reaches the
fatal predicate *through* that family never appears in `candidate.smt2` at
all. Two campaigns measured it. HDFS-17960: emptying its allowlist
concretized the four reads of `AtomicInteger#value`, and the campaign went
from 25 active observed tasks, 94 consumer-boundary families and 46 guarded
reads to 1, 2 and 0, with `configuredSourceMaterializations: []` and no root
in the formula, though the narrowing never touched the hook's own field.
HDFS-11741: its per-region allowlist concretized 212 of 277 input actions,
including 14 of the 18 `BOUNDED_CONTAINER_STATE` actions outright -- among
them the DataNode's `allKeys`, which its own README calls "shared state
reconstructed from its retained writers".

So the file governs one decision and not the other. Every proposed input
carries two verdicts, and `symbolic_root_policy.jsonl` publishes both per
action alongside its summary row:

| verdict | meaning | on the plan row | who decides |
|---|---|---|---|
| TRACK | symbolize the read: the VM publishes its `ReadFrom` candidates and container versions | the surviving `mode: SYMBOLIC` | the mechanism -- true for every carrier |
| MINT | may become a *fresh* root, a free symbol the solver moves | `mintEligible` | the three declaring authorities below |

A carrier is a shared location this campaign's roots can still change. It is
not something the file declares and not "every read the recording made":
`ConcolicScheduler.RootDependenceSlice` derives it from the roots' own forward
dependence over the runtime-refined dataflow graph, which states both halves
of the relation the design asks for --

- **data dependence**: a value edge (`field_write`, `field_mutation`,
  `call_return`, `local_def_use`, `caller_argument`, the wire handoff kinds)
  carries a root-dependent value into the cell it targets;
- **control dependence**: a `GUARD` edge (`path_guard_dependency`,
  `heap_mutation_path_guard`, `receiver_field_effect_path_guard`) runs from a
  guard's operand to the definition that guard controls, so a write whose case
  partition a root decides is reached by the same walk.

-- so one transitive forward closure from the root cells answers both, and its
fixed point *is* the carrier set: a read of a carrier that feeds another store
lands on that store's cell on the next hop. Everything else is `CONCRETE` at
its recorded value, with `symbolicDemand: NOT_ROOT_DEPENDENT` and a
`symbolic_root_policy.jsonl` verdict of the same name. This is what selected
HDFS-17960's `DirectorySnapshottableFeature#snapshotsByNames` and the
`AtomicInteger#value` behind `SnapshotManager#numSnapshots` with nothing
declaring either.

Two properties fall out of the walk rather than being cases in it. **A field
nothing writes is never a carrier** -- a static final appears only as a
`fromCell`, is the target of no edge, and so cannot be reached from any root;
that is what keeps `FSDirectory.DOT_RESERVED` and
`NameNodeLayoutVersion.MINIMUM_COMPATIBLE_LAYOUT_VERSION` out of HDFS-17960's
plan, where they used to be tracked and crashed INSTRUMENT with
`STATIC_FIELD_MATERIALIZATION_UNSUPPORTED`. And **a campaign whose roots the
graph does not name narrows nothing**: the slice reports
`carrierSliceApplied: false`, `carrierSliceReason:
NO_ROOT_CELL_IN_REFINED_GRAPH`, and every carrier stays tracked, because
narrowing on an empty seed would concrete every read and delete the evidence
rather than the waste.

Carriers, so derived, are tracked and the allowlist cannot refuse them --
refusing one removes no root and deletes the evidence. Declared communication
cut ports are tracked whether or not the slice reaches them: the port is
itself a manual declaration of the wire path, and the value it names is
produced on the other side of the wire. Three things, and nothing else, are
mint-eligible:

- a name this file declares, through `fieldSignatures`, `portIds` or `cells`,
  for the region the action belongs to;
- a field a `CausynthSymbolicSource.symbolize` hook site owns -- the hook call
  is itself the declaration, and it mints at its own site, so the input action
  stands down (`CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED`);
- an `EXPLICIT_SYMBOLIC_FAULT` port, i.e. a `Debug.makeSymbolicBoolean` marker
  the workload wrote into its own source.

One input kind cannot be tracked without minting. An `EXTERNAL_CALL_RETURN`
-- a `Timer.now()` return, say -- has no writer inside the recording, so
there is no carrier expression to reuse and symbolizing it *is* minting. An
undeclared one is therefore `CONCRETE`, and is the only thing the file still
refuses; each refusal is published with its region, source kind, site and
cell as `suppressedRootCandidates`.

`ConcolicRegionRuntime` honours the second verdict. `mintEligible` decodes on
`SymbolizeAction` (default `true`, the behaviour of a campaign with no
selection file), and `retainPropagatedInput` no longer answers "nothing
propagated, go and mint" for a tracked carrier: it opens path recording and
publishes the port at its recorded value, exactly as a selected shared read
already does. Containers fall through and are still tracked, because
publishing a shared state's versions is what a carrier is for.

The authored `symbolicDemand` survives a tracked action untouched. It is how
the replay learns that a port models a whole container rather than a scalar
(`ConcolicRegionRuntime.trackContainerOrObserveConcrete`), and the previous
narrowing overwrote it with its own verdict -- which is the other half of the
HDFS-11741 defect: the four container-state actions that survived as cut
ports reached replay with their `BOUNDED_CONTAINER_STATE` demand replaced by
`DECLARED_COMMUNICATION_CUT_PORT`.

The retired `carrier*` keys said "keep this read symbolic but mint nothing",
which is now what every name the file does not mention already gets. A file
still carrying one is refused by name rather than read as a root.

Which leaves the choice of what to *declare* a soundness question, not a
budget one. **A value whose earlier members are baked into concrete state
elsewhere in the recording cannot be declared a free root.** The block key id
is the worked example: the NameNode rolls it from a counter, and the target
DataNode's `allKeys` arrives in the composition as an initial snapshot of
three recorded constants. Minting the NameNode-side id as a free symbol gives
it no identity with those constants, so the solver answers with an id outside
the recorded set and reaches the target's lookup miss whether or not the fault
fired -- a world the recording does not admit. Declare the mechanism that is
genuinely free (here the wall clock, and the expiry computed from it) and let
the counter flow as the constants it was recorded as.

#### What tracking costs, and the fold that pays it back

Tracking *every* carrier grows the plan; tracking the root-dependent ones does
not. Re-running the PLAN stage offline over three recorded corpora, with each
experiment's own file unchanged, gives three columns: what the old allowlist
narrowed to, what "track every carrier" costs, and what the root slice keeps.

| corpus | declared-only | every carrier | root-dependent | carrier locations |
|---|---|---|---|---|
| hdfs-17897 | 18 | 97 | **71** | 12 |
| hdfs-17899-bug3 | 20 | 121 | **75** | 7 |
| hdfs-17960 | 4 | 80 | **13** | 3 |

The root set is unchanged in all three, and so is the chain each case needs:
HDFS-17960 keeps `snapshotsByNames`, `AtomicInteger#value` and `Snapshot#id`
and nothing else; bug3 and 17897 keep `BlockTokenSecretManager#allKeys`,
`DelegationKey#keyId`/`#expiryDate` and the `BlockKeyProto` /
`DataEncryptionKeyProto` copies on the wire path. Most of the new symbolic actions are
reads of state written only from constants, and each becomes a guarded read
whose arms all lower to the same literal. Such a family is free of any case:
`ConcolicSmtComposer.guardedReadTerm` still mints a fresh `sym__read__` value
(ConcolicSmtComposer.java:3496), declares a selector per arm and asserts the
`exactlyOne` cardinality over them (ConcolicSmtComposer.java:3230) plus each
arm's writer-case closure (ConcolicSmtComposer.java:3823). When every arm's
lowered term is a syntactic constant and they are all equal, the read *is*
that constant: the value symbol, the selectors, the cardinality axiom and the
writer-case closure can all be dropped and every use replaced by the literal.
`collapsedContainerArm` (ConcolicSmtComposer.java:1582) already recognises
the shape for container arms, but as a refusal, not a fold. The fold is not
implemented here: it changes emitted SMT and must be gated on a byte-identical
recompose of the HDFS-17960 and bug3 corpora, whose recorded summaries predate
this plan and so do not exercise it.

### The replay task set

The same slice decides which planned occurrences a replay executes
symbolically at all. The runtime plan admits the target's whole dynamic
ancestry, and every admitted occurrence is a symbolic activation inside the
replayed workload -- on HDFS-17960 the fsimage loader,
`FSImageFormatProtobuf$Loader.loadInternal`, was 93% of every replay (~659 s
of ~800 s) and fed nothing the root could move. `ConcolicScheduler` therefore
keeps a selected occurrence only when it can carry a root's influence toward
the target, and publishes the rest as pruned instead of scheduling them:

| kept as | because |
|---|---|
| `TARGET_REACH` | the occurrence decides the fatal branch |
| `ROOT_SITE` | it contains a root: a hook-owned or declared read, an `EXPLICIT_SYMBOLIC_FAULT` marker, or a configured source phase the hook published inside it |
| `CARRIER_WRITER` | it writes a shared location on the root-dependence slice -- the case-controlled writers included, because the slice walks `GUARD` edges |
| `ROOT_DEPENDENT_FLOW` | a root site or carrier writer reaches it over the plan's own edges: a shared-location flow of a carrier, or a wire delivery / request-fault control whose producer is itself root-dependent |

Everything else replays only what the recording observed -- every arm
writes the recorded value -- and is published in `replay_task_slice.jsonl`
with `reason: REPLAY_TASK_PRUNED_NOT_ROOT_DEPENDENT`; the summary row and
the schedule index's `replayTaskSlice` member carry the counts. The
decision is a pure function of the plan, the refined graph and the roots, so
the active-observed schedule of the seed query takes the same subset. It is
withheld -- `replayTaskSliceApplied: false`, nothing pruned -- exactly when
the carrier slice is, because a root the graph does not name cannot state
what it reaches. Offline on the recorded plans it takes HDFS-17960 from 44
tasks to 18 (the loader and the whole fsimage save nest go; every region the
final formula named stays), HDFS-17899 bug3 from 41 to 35, HDFS-17897 from
29 to 26 and HDFS-11741 from 88 to 77 -- the block-key family keeps its
per-key `PBHelper.convert` fan-out because each convert writes an `allKeys`
entry the root's expiry decision controls, and drops only the test-harness
setters and the converts of keys no rotation ever re-stamped.

**Shared carriers are declared on the same slice.** `RuntimeRegionPlanner`
publishes on every closure goal every shared field its region reads or writes
at an exact runtime access, and the replay versions each declared carrier --
one guarded-read family per read, one arm per writer. `ConcolicScheduler`
keeps a task's `sharedCarriers` row only when the slice reaches its location
(`RootDependenceSlice.reachesLocation`): the root's own field, every field on
the forward closure, and the field of every action the slice carries -- which
is what keeps a library leaf such as `AtomicInteger#value`, a source cell of
its own that meets the graph only at its accessor's local. Everything else is
recorded at its concrete value: no versions, no families. The decisions are
published beside the replay task slice in `shared_carrier_slice.jsonl` -- a
`SHARED_CARRIER_SLICE` summary, then one `SHARED_CARRIER_DECISION` row per
declared carrier with `reason: SHARED_CARRIER_KEPT` or
`SHARED_CARRIER_NOT_ROOT_DEPENDENT` -- and in the schedule index's
`sharedCarrierSlice` member; a withheld slice drops nothing. Offline on the
recorded plans HDFS-17960 goes from 19 declared locations (135 carrier rows
over 18 tasks) to 4 (49 rows): `snapshotDeletionOrdered`, `snapshotsByNames`,
`AtomicInteger#value`, `Snapshot#id`; `INodeDirectory#children` (11 families,
31 arms in the recorded formula), `snapshotCounter`, `snapshotQuota`, the
edit-log op strings and the fsimage loader's fields go. The composer
manufactures no family of its own -- every arm is a VM `ReadFromExpression`
over a carrier the replay selected -- so it is consistent by construction;
given `--task-plan` it states that in the manifest's `carrierDeclarations`
ledger, which against a narrower plan names the families that plan would not
have produced.

## Trace context and topology

The workload registers a stable node owner with `registerSource`, may bind
handler aliases to it, and starts each external operation with
`beginSourceRequest`. It closes the returned scope in `finally`.

At a message boundary:

```text
outboundExchange(...) -> strict trace-context header
inboundExchange(header, ...) -> scope token
endInboundExchange(scope token)
```

The header carries sender span, source identity, request flow, and the symbolic
message envelope. `recordExchange` records the SEND or RECEIVE leg and its
REQUEST or RESPONSE half. Correlation, attempt, endpoint, and instrumentation
site identifiers describe topology and locate the exact handoff. They are not
SMT variables and are never used to reconstruct a value.

## VM propagation and consumer anchors

A declared wire flow identifies one exact producer endpoint and one exact
consumer endpoint. Instrumentation invokes:

```text
exportCommunicationLeaf(portId, carrier, field, descriptor)
attachCommunicationLeaf(portId, carrier, field, descriptor)
```

A port id names one declared endpoint of one exchange site --
`<exchangeSiteKey>.req.<name>` or `<exchangeSiteKey>.resp.<name>` -- while a
site id, `<method>#u<unitIndex>`, names the bytecode unit a capture was
instrumented at. The plan's handoff row carries both, and the hook is addressed
by the port.

The export stores the live VM expression handle in the next message envelope.
The matching receive attaches that expression to the real consumer value. A VM
handle is valid only inside the workload JVM/session; linked regions therefore
replay together.

The custom JDK leaves a transparent `ConsumerBoundaryExpression` at every
successful RPC attach and shared-state read. The anchor records boundary kind,
event identity, Java type, and the already-propagated payload expression. Java
operations continue from that payload. For example:

```text
C produces x + 1
  -> RPC attach in B anchors x + 1
  -> B computes 2 * (x + 1)
  -> RPC attach in A anchors 2 * (x + 1)
  -> A branches on the same propagated expression
```

Shared fields and containers use the same rule. When several recorded writes
can supply a read, its propagated payload is a guarded choice over every writer
expression. Each arm retains its writer case and local path condition. The SMT
query requires exactly one arm and makes that arm imply its writer case and
local path condition. All candidates in the bounded write set remain available
to this choice. An incomplete set remains a coverage gap and cannot support a
closed final claim.

Requiring the selected arm's writer is necessary but not sufficient: on its own
it leaves every *later* writer to the same location free to run as well, so a
read could take a value its own program order has already overwritten. The
model therefore also says that the selected arm is the last write the read
could have seen. The order is the VM's own -- each candidate carries the
session-monotonic `fieldVersionId` of the version it names, and a read's
candidate list is the location's retained version list taken under the version
lock at the read, so every candidate was published before the read and the ids
order them exactly. For candidates `w_1 < ... < w_n`, selecting `w_k` implies
`w_k` is active and no `w_j` with `j > k` is, where "active" is the same
conjunction of writer case closure and local path condition the arm's writer
obligation already asserts. The earliest candidate is the location's `INITIAL`
version, so selecting it forbids every tracked writer. Each arm but the last
carries one named `guarded_read_order__` assertion. Version ids minted in
different symbolic sessions do not compare, so one stable read lowered from
several sessions keeps an order only where the sessions agree; a read whose
candidates admit no single order keeps the rest of its model and is reported as
`GUARDED_READ_ORDER_UNKNOWN` in the guarded-read model, which is telemetry and
not a refusal.

## Local path conditions and symbolic merging

Each region records the path condition it executed. RPC propagation does not
copy an upstream region's path condition into the receiver thread. Instead,
the importer keeps every region case with its own selector and local path
condition.

Offline closure groups consumer anchors by stable boundary family, one family
per read event. A family's `boundaryKind` is `FIELD_READ` for a shared-state
read or `RPC_ATTACH` for a value that crossed a wire. Every observed payload
becomes one family arm selected by the exact producer case, and the selector
implies that case's local path condition. One physical read consumed by several
cases is one family addressed by all of them: sharing is not ambiguity, so no
second ordering mechanism is introduced.

Resolution is transitive. A boundary leaf that arrives inside another family's
arm payload is rewritten by the same walk, which pulls that producer's cases in
recursively until the cone ends in roots, `INITIAL` versions or constants --
NN to client to DN is one chain, not three. The `active` set guards cycles
(`CONSUMER_BOUNDARY_FAMILY_CYCLE`), and each resolved family records
`boundaryDepth`: 0 for a boundary the target reads directly, 1 for one that
arrived inside another boundary's payload, and so on. A multi-hop dependency
therefore shares its intermediate merge instead of enumerating the Cartesian
product of all upstream paths.

Two facts the closure publishes rather than hides:

- `INITIAL_CONTAINER_SNAPSHOT_TRUNCATED` -- a whole-state carrier whose
  `INITIAL` version has no complete content snapshot. Membership over its
  initial state is then a free Boolean, so "the key was never there" is
  available at zero cost. The formula is still emitted, because the same read's
  writer arms are real; the gate is what refuses a witness that stands on it.
- An attach family that reached no arm and that no consumer leaf referenced is
  named `RPC_ATTACH_SENDER_EXPRESSION_MISSING` once, by an end-of-closure
  sweep. A family nothing referenced but which some other slice may own stays
  telemetry in the wire-flow ledger with
  `reason: CONSUMER_BOUNDARY_FAMILY_UNREFERENCED`.

For two independent dependencies with two cases each, the formula contains two
two-arm merges. It does not enumerate four whole executions. For a dependent
chain, the downstream payload already contains the upstream expression and the
family selectors add the matching local path conditions. Composition directly
lowers those propagated expressions and local conditions.

## Replay waves

One path-flip obligation chooses a primary region branch. Companion regions in
the same bundle receive the same solver assignment and replay normally, so
downstream branches, RPC handoffs, and GuardedRead candidate snapshots are
observed again. Different obligations run in separate workload JVMs and may
execute in parallel.

One planner JVM runs per wave. It reads the same immutable summary snapshot
and task plan for every member named on its `--members` roster, computes the
propagation closure once, and writes each member's own path manifest and
worklist into that member's own directory. The campaign waits for the wave,
imports its new cases, then publishes one larger snapshot for the next wave. A
region is closed only at this closure-wide fixed point. An obligation whose
flip query exhausts the solver budget is recorded as the `SOLVER_TIMEOUT`
exploration status and the `PATH_FLIP_SOLVER_TIMEOUT` path coverage gap: its
sibling path stays unexplored, which blocks `UNSAT_CLOSED` and never a
`SAT_CANDIDATE`. A topology change quarantines the complete replay bundle and
starts a new topology epoch; cases from different epochs are never merged.

Retained loops use their configured finite unroll as one region-local path.
Repeated transfers and shared-state accesses keep their loop/boundary ordinal
and candidate writer versions. Loop iterations do not become separate
symbolic-merge cases merely because they repeat.

`RegionPathWorklist` is the per-member record of that loop. Each member writes
its own `region_path_worklist.jsonl` -- the sibling branches still to flip and
the verdict each obligation reached -- and its own `region_path_manifest.json`,
whose `state` is `CLOSED` only at the closure-wide fixed point. The loop ends
at that fixed point, or at one of two guards -- a wave that proposes exactly
the previous wave's obligations over an unchanged verdict histogram has learned
nothing, and failing that the loop stops after `region_path_max_waves` waves.
Either stop is written onto every still-pending worklist as a
`REGION_PATH_CLOSURE_NO_PROGRESS` or `REGION_PATH_WAVE_BUDGET_REACHED`
coverage gap. Both are telemetry: an unexplored sibling path withholds a closed
UNSAT conclusion and says nothing about a SAT candidate.

## Result contract

Every imported region summary carries `schemaVersion`, `kind`, `goalId`,
`taskId`, `sourceKey`, `topologyEpoch`, `boundarySessionScope`, `regionId`,
`occurrenceId`, `activationOrdinal`,
`plannedOccurrenceId`, `relationKey`, `loopBound`, `goalKind`, `edgeBindings`,
`pathCondition`, `branchMappings`, `normalExit`, `boundedExit`,
`exceptionType`, `localCaseId`, `summaryId` and
`pathSetClosed`. Evidence the replay did not produce is absent rather than
empty: `symbolicSourceEvidence`, `manualSymbolicInputObservations`,
`recordedSharedState`, `vmHandoffEvents`, `pathLoopCounts`,
`pathLoopCountGaps`, `alignmentGaps`, `familySnapshotDigest`,
`replayGroupId` when the replay named a group, `sharedExpressionTable` when
some payload of the row refers to a hash-consed definition, and, for a
target-reach goal, `targetReached` and `targetReach`. The importer validates
that evidence and publishes local cases or named gaps; it writes every field
above except `pathSetClosed`, which the campaign stamps on once the exploration
waves settle, matching each worklist report on `plannedOccurrenceId`.
`sharedExpressionTable` holds the hash-consed expression definitions the row's
own payloads refer to.

## Composition

The composer consumes the closure-wide cases and the target predicate. Its
manifest reports consumer-boundary families, case-to-PC dependencies,
GuardedRead choices, field versions and reads, propagation gaps, and
final-status refusals. `FINAL_READY` means the emitted formula has all
selectors, path conditions, and propagated values needed for a sound SAT
witness. `FINAL_READY` is stage-local: it states that the formula is complete,
not that the campaign proved anything. Open path, propagation, and
bounded-candidate coverage remains telemetry and prevents only a closed UNSAT
conclusion. The generated SMT follows the recorded causal chain directly from
explicit roots through propagated consumer expressions to the target condition.

**Case partitions.** A region occurrence's local cases form an exactly-one
partition. The manifest separates the two kinds, because a consumer may pin one
and not the other. `caseSelectorPartitions` are the partitions the formula
asserts unconditionally. `conditionalCaseSelectorPartitions` are those of a
fault-controlled occurrence, whose predecessor's marker decides whether any of
its cases runs at all; the formula states that as a
`request_fault_control__<edge>` assertion -- the fault implies every case of the
controlled occurrence is idle, and its negation implies the exactly-one
partition. Advertising such a partition unconditionally would invite a consumer
to pin it and silently freeze the marker.

**Dead case arms.** An EXPLORE replay can observe a case whose path condition
no model of the final composition admits -- the arm contradicts the
target-reach obligation the formula was composed under. The formula already
refutes it, but only after a solver has reasoned through the arm's whole cone,
and z3 can spend its entire budget there before it commits to the live
sibling: on HDFS-17960 the ordered-deletion arms of the root's own region carry
the binary searches over free `children` lists and the lambda-valued snapshot
chains, and the plain buggy polarity timed out at 600 s while each arm on its
own is decided in 0.3 s. When the composer is given `--z3`, `DeadCaseLemmas`
asks every arm of every unconditional multi-arm partition alone,
`formula ∧ arm`, under a deterministic z3 resource limit (`--dead-case-rlimit`,
default 5,000,000; `0` disables the pass). An `unsat` answer is a theorem of
the formula, so `(not arm)` is asserted as a named `dead_case_lemma__<hash>`
before `(check-sat)`; the model set is unchanged and nothing recorded is
assumed, which is what separates a lemma from a pinned case frontier. Lemmas
found earlier are carried into later probes, which stays sound and makes them
cheap. Conditional partitions are never probed, nor is a fail-closed formula.
The manifest's `deadCaseLemmas` ledger lists every probe with its status and
elapsed time, and every lemma with the partition it decides. Without `--z3` the
formula is untouched and the ledger says `skipped: NO_SOLVER`.

**Containers.** A Java container is lowered as a state witness, not as a fresh
symbol per access: `AssocState` for maps (`assoc_present`, `assoc_values`,
`assoc_order`, `assoc_position`) and `IndexedState` for lists and arrays. Size
is a closed form of the operations applied, so `size()` after a put is derived
rather than assumed, and an allocated container's size is stated once against
the Java int domain rather than as any one path's precondition. Element and
field reads project a scalar out of the state with the declared Java type, so
the arithmetic downstream is the program's.

**Wire flows.** `wireFlowBindings` is the ledger: one row per boundary family
on a declared port, carrying `portId`, `armCount`, `referenced`, `valueBound`,
its lowered `solverTerm`, and, where the mapping declares one, `consumerField`
and `consumerFieldRead`. The declared ports come from the plan's
`communicationHandoffs`; the declared consumer fields come from
`--mappings`, the experiment's `communication-mappings.jsonl`. The refusal
`WIRE_FLOW_VALUE_UNBOUND[<port>]` is decided **per flow**, not per family: a
flow is unbound only when no family on its port reached a term and the field
its consumer assigns was not read either. One lowered family out of eleven is
the wire's value being in the formula; the other ten stay in the ledger as
telemetry.

## Reading the formula

`BooleanReachConditionExtractor` solves the composed formula and publishes
`z3-result.json`. It enumerates the Java-boolean roots -- the injected fault
markers and configured boolean sources -- one valuation per assignment, and
leaves every other root existential. Each valuation row carries:

- `values`, the boolean assignment, and `status`;
- `pinnedCaseSelectors`, the case frontier the attempt that decided it was
  solved under, so a reader can tell a causal verdict from one the frontier
  decided;
- `existentialWitness`, the model's value for each non-boolean root;
- `witnessMechanisms`, each root the witness moved off its recorded value,
  named as what it is: `MARKER_FLIPPED` for an injected fault, `CLOCK_SKEW`
  with its `skewMillis` for a wall clock, `ROOT_MOVED` otherwise.

Three further readings sit beside the table:

- **`existentialRootProbe`.** One neighbouring value per existential root, with
  the others pinned to the witness. A rejected neighbour is the solver's own
  proof that the root decides the target. A candidate outside a clock's
  declared `ClockRootPhysics` window is not solved at all; it is recorded
  `status: "skipped", rejectedBy: "WINDOW_BOUNDARY"`, because a value the
  root's own physics forbids is refused by that assertion and not by the
  target.
- **`mechanismNecessity`.** For each declared marker whose *recorded* polarity
  is satisfiable, the mechanisms that polarity names are grouped by kind -- all
  wall clocks together, since "these nodes' clocks disagreed" is the mechanism
  and one clock is not -- pinned to their recorded values, and solved again. A
  polarity that survives that was not carried by the mechanism. A model assigns
  every free root, so a witness always names something; this is how a named
  mechanism is told from decoration.
- **`fatalStateSelection`.** The arms of the fatal predicate's own guarded
  read, with the one the model chose marked. The `fatal_path` assertion names
  one `merged_boundary__` constant, one equality binds it to a read's value
  term, and the manifest holds that read's arms.

A composition the composer refused is still solved. Everything above is
published with `evidenceOnly: true`, the eligibility gap stays in `gaps`, and
the state stays `CANDIDATE_WITH_GAPS`: a refusal is a reason to withhold a
verdict, not a reason to withhold a reading. Because a refusal also fails the
formula closed, evidence-only solving lifts that one `(assert false)` marker
and reports how many it lifted in `failClosedMarkersLifted`.

## The claim

`ClaimPolicy` decides what a campaign proved, once, and publishes that
decision inside the reach-condition report as `campaignClaim`. The EMIT stage
of `run_engine.sh` copies `claim`, `claimReason`, `blockers` and
`whyNotAccepted` from it into `result.json` and refuses to publish a result
from a reach report that carries no decision; it derives no verdict of its
own. `ClaimPolicy` can be replayed on any published pair of artifacts:

```bash
java -cp GraphChecker.jar edu.uva.liftlab.graphchecker.concolic.ClaimPolicy \
  --manifest schedule/final/candidate_composition_manifest.json \
  --reach schedule/final/z3-result.json \
  --mappings experiments/hadoop/<case>/communication-mappings.jsonl
```

A claim is accepted only when no blocker is named. `SAT_CANDIDATE` needs a
`REACHABLE` solver result, `UNSAT_CLOSED` an `UNREACHABLE` one; everything
else is `INCONCLUSIVE_PARTIAL` and every reason is one row of `blockers`
(`code`, `subject`, `detail`) and one line of `whyNotAccepted`.

| Blocker | Named when |
| --- | --- |
| `COMPOSER_NOT_FINAL_READY` | the manifest's `finalStatus` is not `FINAL_READY` |
| `COMPOSITION_GAPS_UNRESOLVED` | a Composer refusal or a solver gap is open -- the same rows EMIT counts in `gaps.json` |
| `DECLARED_WIRE_FLOWS_UNREALIZED` | a declared `WIRE_FLOW` reached the formula by neither route; the subject names those flows |
| `UNDETERMINED_INITIAL_STATE` | the fatal read's own container carries an `INITIAL_CONTAINER_SNAPSHOT_TRUNCATED` gap, so membership over its initial state is a free choice available under every arm |
| `FAULT_MARKER_NOT_DETERMINING` | the experiment injects a fault marker, both polarities are satisfiable, and no named mechanism the target cannot do without explains the polarity that has no fault |
| `DEGENERATE_ROOT_SPACE` | `degeneracyCheck` is `DEGENERATE_*`: the target provably ignores every root |
| `UNDECIDED_ROOT_SPACE` | `degeneracyCheck` is `UNDECIDED_*`: the question was never decided, so it is not answered |
| `TARGET_UNCONSTRAINED_BY_ROOTS` | a `REACHABLE` result where no single root flip changes satisfiability and no existential perturbation was rejected |
| `WITNESS_UNINFORMATIVE` | the existential witness is every-zero, or identical under every satisfying valuation, while no perturbation of it was rejected |
| `SOLVER_UNDECIDED_VALUATIONS` | the solver returned neither sat nor unsat on an enumerated valuation |
| `UNSAT_CLOSURE_INCOMPLETE` | an `UNREACHABLE` result without closed selected-path authority |
| `NO_EXACT_REACHABILITY` | the solver stage reached no exact reachability decision |

A witness is evidence only if the target predicate depends on a symbolic root.
Two enumerated valuations that differ in exactly one Boolean root and disagree
on satisfiability show that dependence; so does a rejected existential
perturbation inside the root's own declared physics. Without either, the
formula and the roots are disconnected and the witness names nothing, whatever
the formula satisfies. That check does not apply to an `UNREACHABLE` result,
which has no witness to tie to a root.

Where the experiment injects a marker, the marker is the hypothesis and the
verdict has to rest on it. `constrainsRootSpace` on some other root is evidence
about that root, so the claim also records `rootSpace.probedRoot` -- which root
the probe perturbed and whether it was rejected.

`UNSAT_CLOSURE_INCOMPLETE` is required for `UNSAT_CLOSED` and for nothing
else: one connected SAT witness stays valid while sibling paths are open.

**Reading a campaign as passed.** The claim is `SAT_CANDIDATE`, `blockers` is
empty and `finalStatus` is `FINAL_READY`; and on the plain `candidate.smt2`,
unpinned, the buggy polarity of the case's declared root is satisfiable while
the other polarity is not -- or, where the mechanism is not a marker, a
`mechanismNecessity` row names a mechanism the target cannot do without.

### Realizing a declared wire flow

A declared `WIRE_FLOW` reaches the formula by either of two routes, and the
claim's `rootSpace.wireFlows` row says which one answered in `realizedBy`:

- **`PORT_FAMILY`** -- some boundary family on the flow's own
  `XCH.<exchangeSiteKey>.<req|resp>.<flow>` port was lowered into a term. This
  is the direct route and it is reported first when both hold.
- **`CONSUMER_FIELD_READ`** -- the value left the wire on arrival. The consumer
  assigned it to a field and everything downstream reads that field, so the
  term the wire's value ends up in is a guarded read of that field and the
  port's own family is a term nobody was going to build. Only the experiment
  knows which field that is, so the mapping declares it as `consumerField`,
  named as the guarded-read model names a field -- by the class that declares
  it, for example
  `org.apache.hadoop.security.token.delegation.DelegationKey#expiryDate`.

A flow that declares no `consumerField` has only the port route. The composer
makes the same join before refusing, so the two stages cannot disagree about
one composition.

## Experiment inputs

Four declarations per experiment directory, read by `run_engine.sh` and
resolvable with `@config`, `@repo` and `@project`:

| File | Role |
| --- | --- |
| `symbolic-inputs.jsonl` | the root allowlist, one `{"regionId", "fieldSignatures": [...]}` row per region: which observed application sources this case may mint as symbolic roots. Carriers are not named here -- they are derived from the roots' forward dependence. Configured with `causynth_symbolic_inputs`; when a case declares it, minting is narrowed to exactly those fields, which is what keeps a witness about the fault rather than about whatever else happened to be free. A case that declares none mints only the roots the plan's own symbolization actions name. |
| `communication-mappings.jsonl` | one `WIRE_FLOW` row per declared cross-node value: `id`, `transport`, `direction`, `javaType`, an exact `producer` and `consumer` endpoint, and optionally `consumerField` -- the field the consumer assigns the received value to, which is the second route a flow can reach the formula by. |
| `loop-bounds.jsonl` | the finite unroll for every retained condition-controlled loop. An empty file explicitly means the workload has no such loop. |
| `target.yaml` | the `exception_target_id` the annotated throw site carries. |

`workflow.properties` holds the knobs: `schedule_max_jobs` (workload JVMs per
stage), `solver_timeout_ms` (per-query Z3 budget), `region_path_max_waves`
(EXPLORE wave budget, default 12), `clock_skew_ms` (how far a witness may move
a wall clock from the value that read returned, default 300000),
`reach_max_inputs` and `reach_max_valuations` (the Boolean enumeration bounds),
`concolic_worker_count`, and the output, cache, classpath and VM paths.
