# The concolic VM integration

**Scope.** This file used to describe the whole pipeline. Most of that is now the README,
which states the design once — declared roots, in-JVM propagation with the static graph only
scoping, identity v3, one flip on one occurrence, edges joined in the SMT, fail-closed named
gaps — and restating it here only gave the two documents room to disagree. What is left is
the part the README does not carry: the boundary between instrumented Java code,
GraphChecker's runtime, and the customized OpenJDK 8 Zero VM. Read the README first; this
file answers "what exactly does the VM do, and how does the engine talk to it".

## What the VM is for

The VM keeps a **shadow expression under each value**, by value and under the real object
identity, not by a declared location. Any symbolic write leaves its expression on the object
the write reached, and a later read of that object returns it — through fields, containers,
threads, and across the wire once the value has been exported and attached. Nothing has to
decide in advance which locations are "carriers", and nothing reconstructs a value's history
afterwards: the fatal read's value in a replay is *already* an expression over the declared
roots.

Two consequences the engine depends on:

- **A read that observes nothing symbolic has nothing to publish.** It is concrete at the
  value the run gave it, and the composer pins it to that value.
- **Containers are not modelled at region entry.** A container becomes symbolic only when a
  root-derived value is put into it, and the VM carries the INITIAL snapshot base inside the
  expression the reader gets back. Which relations hold is found by flipping root-dependent
  branches, not by minting a symbol per read.

## The broker ABI

`runtime/ConcolicVmBroker.java` is the whole Java-side view of the VM. Every entry point is
looked up by reflection, so the class stays loadable on a stock JDK and the recording pass
runs unchanged; `requireCurrentCapabilities` refuses a replay plan before its workload starts
if any part of the surface is missing, naming the missing capabilities rather than degrading.

| Capability group | VM entry points | What it buys |
| --- | --- | --- |
| session lifecycle | `openWorkloadSession`, `closeWorkloadSession`, `getWorkloadSessionStatus` | one symbolic session per workload JVM, with a status a Java caller can name |
| region framing | `startConcolicRegion`, `finishConcolicRegion`, `getCurrentConcolicContextId`, `getCurrentConcolicRegionEnterEventId`, `currentSymbolicEventId` | brackets the events an activation owns: versions, reads and region entries are numbered from one monotone session counter, which is what aligns the runtime's frame journal with the VM's log |
| minting | `symbolize`, `symbolizeField`, `symbolizeExactField` | where a declared root enters. A declared primitive source mints even when the value arrives wrapped over constants, which is the only way a case can say "the search starts here" about a cell nothing symbolic has reached |
| observation | `observeExactPrimitiveField` | not a mint: the leaf installed is a concrete expression over the value the field already holds. What it buys is that the location becomes one the VM will version, so a selected write site publishes something at all |
| readout | `getSymbolicExpression`, `getSymbolicFieldExpression` | the expression under a live value, for the row the runtime is about to publish |
| path condition | `pauseConcolicPathCondition`, `resumeConcolicPathCondition`, `getConcolicBranchEvents`, `getConcolicPathConditionRange` | the region-local decision sequence, delimited so a reader can tell one region's conditions from its callees' |
| wire | `exportExpression`, `attachExpression` | the producer's live expression staged into the message envelope, and installed on the consumer's real value on arrival. Each side reports its session-unique endpoint id |
| tracked locations | `getTrackedLocationVersions` | the write log, read out by the object the VM filed it under rather than by a location Java declared; `afterEventId` scopes it on the session clock and `maxBytes` bounds one answer, which then says where to resume |
| guarded stores | `installGuardedStoreSites` | the session's guarded-store table, one line per store method with its guard branch sites. With no table installed, no concrete store is evidence |
| teardown | `endConcolic` | cleanup after a failed region |

The broker also mirrors the VM's own status ABI (`expressionBroker.hpp`) as named constants —
`NO_ACTIVE_REGION`, `MISSING_METADATA`, `FIELD_NOT_FOUND`, `NOT_SYMBOLIC`, `FOREIGN_HANDLE`,
`UNKNOWN_HANDLE`, `SORT_MISMATCH`, `UNSUPPORTED_TARGET` — plus two bridge-local ones,
`INVOCATION_FAILED` and `MALFORMED_RESULT`, below every value the VM answers. The numbers are
the VM's and are a shared ABI: retired codes stay unassigned rather than being reused. A VM
answer that is not a number is `MALFORMED_RESULT` and never `0`, so "the engine has no
context here" and "this bridge cannot read the answer" stay distinguishable.

## The woven hooks

`causynth/CausynthPipeline` weaves both passes, and its `HookCatalog` is the one typed
registry of what may be woven. There are exactly two catalogs, and naming them is the whole
contract: `HookCatalog.trace()` targets `CausynthTraceRecorder` for the recording pass, and
`HookCatalog.concolic()` targets `ConcolicRegionRuntime` for replay. Each declares its hooks
by `Hook` constant with the owner, name, return type and parameter types Soot will emit — a
hook that is not in a catalog cannot be woven, and one that is in both is woven in both.

That last point is the pass-equality rule the identity rests on (README §4): a hook that
pushes a frame or counts an event is in both catalogs or in neither, and every push is paired
with its pop, because the address *is* the join key. `HookCatalog.bracket` is where the
catalog decides for itself whether the call needs observation paused across it — the
recording pass registers no pause hook, so asking per call site is what let one weave emit a
null invoke.

## Which reads are symbolic

No case declares its roots: the categories are recognized from the program text, as the
GreyGraph design derives its inputs from the analysis (SS3.1), and SEED states them on the
static scope map's `DECLARED_SITE` rows (`inputKind`) for every later stage to read:

- **CLOCK** (`causynth/RootCatalog`): a call of one of the JVM's clocks, or of a method with no
  parameter whose every returned value is a clock under constant arithmetic -- `Time.now()`,
  `Time.monotonicNow()` (`nanoTime / 1000000`), `Timer.now()` -- read off its body, library or
  application alike.  Every read of such a callee's return the slice reaches is a root.
- **FAULT**: a `Debug.makeSymbolicBoolean` marker, woven at the declared transport doors
  (`DoorWeave`).
- **READ**: an accessor read of a location some other region stores, when the accessor runs
  outside the woven program (`AtomicInteger.get()`), so no replay versions it: a placeholder the
  closure binds to the location's writers (hdfs-17960's snapshot counter).
- a `CausynthSymbolicSource.symbolize` hook site in the tree mints its own source.

`ConcolicScheduler.SymbolicInputSelection.decide` takes one decision per proposed input, and
a category is the only thing that makes a read symbolic:

| declaration | verdict | mints |
| --- | --- | --- |
| a clock's return or a READ placeholder's location (`StaticScopeMap.clockCallees`, `readCells`) | `declaredSymbolicRoot` | yes — the read is where the search starts |
| a fault marker the workload wrote into its own source (`Debug.makeSymbolicBoolean`) | workload-owned | yes |
| a field a `CausynthSymbolicSource.symbolize` hook site owns | `CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED` | no: the hook mints at its own site, so the action stands down `CONCRETE` |
| a port `communication-mappings.jsonl` declared | `DECLARED_COMMUNICATION_CUT_PORT` | never: tracked, and `attachCommunicationLeaf` installs the producer's expression |
| anything else | `UNDECLARED_SYMBOLIC_INPUT` | no — `CONCRETE` at its recorded value |

A declaration names a *value*, and the graph names one value once per Jimple local it is
copied into. `renameDeclaredNames` extends a declared name backwards over the edges Soot
itself proves are exact JVM value copies (`SOOT_EXACT_LOCAL_DIRECT_COPY_V1`,
`SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1`) and over nothing else, so a case can declare
`<SnapshotManager: int getNumSnapshots()>.return` and select the accessor-return port that
names the `AtomicInteger` leaf without any upstream cell becoming a root.

Which leaves *what* to declare a soundness question. **A value whose earlier members are
baked into concrete state elsewhere in the recording cannot be declared a free root.** The
block key id is the worked example: the NameNode rolls it from a counter and the target
DataNode's key map arrives as recorded constants, so minting the NameNode-side id as a free
symbol gives it no identity with those constants and the solver answers with an id outside
the recorded set — a world the recording does not admit. Declare the mechanism that is
genuinely free (the wall clock, and the expiry computed from it) and let the counter flow as
the constants it was recorded as.

## Containers

A Java container is lowered as a state witness, not as a fresh symbol per access.
`compose/ContainerStateModel` declares two SMT datatypes — `AssocState` for maps
(`assoc_present`, `assoc_values`, `assoc_order`, `assoc_position`) and `IndexedState` for
lists and arrays — and `compose/ContainerSmtCodec` encodes the operations into them. Size is a closed form of the operations applied, so `size()`
after a put is derived rather than assumed, and an allocated container's size is stated once
against the Java int domain rather than as one path's precondition. Element and field reads
project a scalar out of the state with the declared Java type, so the arithmetic downstream
is the program's.

## What a session publishes

One replay writes one session directory, `<iteration>/sessions/<sessionId>/`
(`contract/SessionDir.java`): `manifest.json` stating the role it ran as — `SEED` or
`FOCUSED`, and a manifest that states none is refused — one JSONL file per row kind
(`activations`, `decisions`, `roots`, `reads`, `writes`, `exports`, `attaches`, `targets`,
`obligations`, `gaps`), and `expressions.json`, the session's own expression table that every
reference in its rows must resolve in. One kind per file is the point: a reader of reads
never parses writes.

The row types are `contract/ActivationRow`, `DecisionRow`, `RootMintRow`, `ReadRow`,
`WriteRow`, `ExportRow`, `AttachRow`, `TargetRow` and `GapRow`; the README's §5 table says
what each states. `contract/RowInvariants` checks the row contract at `IMPORT` and nowhere
else, as pure functions over rows — it opens no file, runs no solver and consults no plan,
and where a rule cannot be decided from the rows alone it says so as a diagnostic rather than
guessing.

## Gaps

Every refusal and every diagnostic is a `contract/GapRow` carrying a `kind` from the closed
`contract/GapKind` registry, a `cls` from `contract/GapClass` — `BLOCKING`, the stage refuses
and no claim may be made over it, or `DIAGNOSTIC`, recorded for the report while the claim
stands — a `subject` and a `detail`. `GapRow.of` requires both `kind` and `cls`: a row cannot
be published without stating which it is, and the producer that raises it is what decides.

`GapKind` is closed on purpose — a kind with no consumer is a report nobody reads — and each
constant carries in its javadoc why it is classed the way it is. The registry as it stands:
`ADMISSION_GAP`, `TOPOLOGY_DIVERGENCE`, `UNATTESTED_ARM`, `UNSTATED_VALUE`,
`UNPRODUCIBLE_ANSWER`, `FORMULA_SAT_AT_RECORDED_VALUATION`, `DECLARATION_MISSING`,
`LINEAGE_LOST`, `TASK_UNANSWERED`, `ADDRESS_UNSTABLE`, `SOLVER_TIMEOUT`, `FRAME_UNBALANCED`,
`BOUNDED_LOOP_BODY_BOUND_UNDECLARED`, `BOUNDED_LOOP_FIXED_COUNT_BOUND_UNDECLARED`,
`BOUNDED_LOOP_CLASSIFICATION_INCONSISTENT`, `COMMUNICATION_REQUEST_PORT_UNRESOLVED`,
`BOUND_INSUFFICIENT`, `OCCURRENCE_ADDRESS_SHARED`, `MINT_UNATTRIBUTED`,
`MESSAGE_CONTEXT_REFUSED`, `EPOCH_UNMATCHED`, `SESSION_INCOMPLETE`, `ASSIGNMENT_UNPLANTED`,
`ASSIGNMENT_UNMINTABLE`, `PATH_SELF_CONTRADICTORY`. A new kind is registered here, with its
class argued in the same place.

## Reading the composed query and the claim

`COMPOSE` writes `candidate.smt2` and `candidate_composition_manifest.json`, and
`compose/ComposeMain` writes `claim.json` beside them; `EMIT` requires `candidate.smt2`,
`candidate_composition_manifest.json`, `gaps.json` and `result.json` under `schedule/final`
and refuses to publish a result from a manifest carrying no decision — it derives no verdict
of its own. `compose/ClaimPolicy` is the one place a campaign's claim is decided; it is a
library class with no `main`, so a claim is read off the published `claim.json` and
`result.json` rather than recomputed.

Read them together. A `claim.json` naming a mechanism is not acceptance on its own:
acceptance is the claim **plus** `polarityDecides`, no blocking gaps, and fresh provenance.
Gap rows are read with their `cls` — `DIAGNOSTIC` describes coverage the run lacked,
`BLOCKING` is why it refused.

**The published formula is pinned.** The composer asserts its own recorded valuation into the
file it publishes, as a named `valuation__…` assertion before `(check-sat)`. A plain
`z3 candidate.smt2` therefore answers about *that one valuation* and commonly answers `unsat`
for exactly that reason — on HDFS-17960 the pin is `(= M_Z_field_SRC…SnapshotManager true)`
under the comment `; valuation 0: the run as it happened`. To ask the formula at each
polarity, unpinned, use the acceptance harness's probe, `experiments/hadoop/accept/probe.sh`
(`experiments/hadoop/accept/README.md`); it is reported and never gated on, because it asks
about the whole formula rather than the slice the campaign solved. A zero exit code proves
nothing.

## Knobs

`workflow.properties` holds them, resolvable with `@config`, `@repo` and `@project`:
`causynth_target_spec`, `causynth_root_domains`,
`causynth_communication_mappings`, `causynth_loop_bounds` and `causynth_loop_default_bound`
name the declarations; `declared_target_occurrence` names the occurrence the campaign is
about; `schedule_max_jobs`, `concolic_worker_count`, `solver_timeout_ms`,
`compose_max_valuations`, `campaign_max_iterations`, `region_path_max_waves`,
`region_path_max_tasks` and `campaign_stop_after` bound the run; `custom_jdk_home`, `z3_bin`
and the project/output/cache paths say where things are. Every one may be overridden by the
matching upper-case environment variable.

A schedule is drawn from exactly one closure: `ConcolicScheduler --closure-mode` is
`candidate` (every occurrence the frozen region plan declares) or `seed-replay` (only the
occurrences a seed activation can replay), and `run_engine.sh` states which one each stage
uses.
