# CONTRACT-SPEC — the rows every stage reads

Package `edu.uva.liftlab.graphchecker.contract`. A replay writes rows; IMPORT checks them; EXPLORE,
COMPOSE and CONFIRM read nothing else about a run. Every contract type is an immutable value class:
`Value` makes two instances equal iff their `parts()` are equal, and each `of(...)` factory refuses,
naming the field, what `Fields` does not accept (a missing required value, blank text, an ordinal
below 1, a negative count); collections are unmodifiable copies. An id is the first 16 hex digits
of a SHA-256 (`smt.ArtifactIO.digest(text, 16)`) unless stated. Stages and gates are described in
[PIPELINE.md](PIPELINE.md); what the identity means and how the runtime computes it, in
[IDENTITY.md](IDENTITY.md).

## 1. Identity

| type | shape | rendered / id |
| --- | --- | --- |
| `NodeId(node, epoch)` | a component instance and its topology epoch | `<node>#epoch<N>` |
| `Role` | the scope kind a workload declares, upper-cased to `[A-Z0-9_]`; engine constants `UNKNOWN`, `CLIENT`, `EXECUTOR_TASK` | its name |
| `CausalContext` | why an occurrence ran, one of three forms: `Anchor(producerEndpointId, rpcSite)` (a message started it), `Root(role, api, windowIndex ≥ 1)` (the w-th workload action or daemon tick of that role and api in the window; `api` empty for a tick), `Lost(role)` (unattributable) | `Anchor:<id>@<rpcSite>`, `Root:<ROLE>[/<api>]#<w>`, `Lost:<ROLE>` |
| `Frame(callSite, iteration)` | a static call site `class#method#bci` (no `/`, no `@`) and the k-th entry of it in the enclosing frame, from 0 | `<callSite>@<k>` |
| `ExecutionIndex(frames)` | frames outermost first | `f/f/...`; `hash()` folds `h = sha16(h + "/" + callSite + "@" + k)` from `sha16("")` |
| `OccurrenceAddress(node, regionId, context, index)` | one region occurrence; `regionId` has no `/`; `ROLE.<role>` is work under no region (`role()`); `lineageLost()` = the context is `Lost` | `<node>/region/<regionId>/ctx:<context>/idx:<index>`; `id()` = sha16(node + "/" + regionId + "/" + context + "/" + index hash) |
| `Selector(regionId, api, k, node)` | what a case declares, `[<node>]/region/<REGION>[@api]#k` (`OccurrenceAddress.parseSelector`); `plan.SelectorResolution` resolves it to the k-th match in the seed; an `@api` selector matches only `Anchor` occurrences; never an address | its declaration spelling |
| `Endpoint(occurrence, site, siteIndex, attempt)` | one side of an interaction: `site` is the declared port id (WIRE) or `<class>#<method><descriptor>#<bci>:READ\|WRITE` (only `Endpoint.stateSite` spells it); `siteIndex` = frames from the region entry to the event; `attempt` = retry number | `<occurrence>/site:<site>/sidx:<index>/att:<n>`; `id()` = sha16(occurrence id + "/" + site + "/" + siteIndex hash + "/" + attempt); `activation()` = occurrence id + `\|` + the frames without the event's own (the unit a CONFIRM `ORDER` row holds) |
| `InteractionKind` | `WIRE` (export → attach), `STATE` (write version → read) | |
| `Interaction(kind, producer, consumer)` | one edge, named by both endpoints | `id()` = sha16(kind + producer id + consumer id) |
| `LocationKind` | `STATIC`, `INSTANCE`, `ARRAY`, `MAP` | |
| `LocationId(kind, owner, slot)` | the storage a STATE edge joins on: `owner` is the class for `STATIC`, else the VM's symbolic rid of the object — a per-run counter, so it names one object only inside one session (a class name on a heap location names every instance; `smt.Arms.namedOwner` decides); `slot` is the field, index or container state slot | join key `KIND/<owner>#<slot>` (`compose.SmtLowering.locationKey`) |

No cross-session object identity exists: the same field in two sessions is two locations.
`JvmNames` strips JVM-minted numbers from class names (reflection accessors, lambda proxies) where
the runtime mints a site; parsing never applies it.  A weave's lambda class keeps its number: every
Soot run names it by content (`GraphCheckerMain`'s `LambdaClassNames`).

## 2. Rows and the session directory

### 2.1 Layout (`SessionDir`)

One replay session is `<iteration>/sessions/<sessionId>/` (`SessionDir.sessionsIn` lists them in
name order). `runtime.SessionPublisher` creates every row file empty, the expression log's header
and `manifest.json` when the session opens, and appends and flushes each row as it is published.

| file | holds |
| --- | --- |
| `activations.jsonl` | `ActivationRow` |
| `decisions.jsonl` | `DecisionRow` |
| `exports.jsonl`, `attaches.jsonl` | `ExportRow`, `AttachRow` |
| `writes.jsonl`, `reads.jsonl` | `WriteRow`, `ReadRow` |
| `roots.jsonl` | `RootMintRow` |
| `targets.jsonl` | `TargetRow` |
| `gaps.jsonl` | `GapRow` |
| `obligations.jsonl` | the replay's `ObligationResult` per obligation it ran, written at close (`RowRuntime.closeSession`); the authority on its verdict; a SEED has none |
| `schedule.jsonl` | the run's `ScheduleEvent`s in order, with `{mark, at}` rows; not a row kind, no invariant is stated over it |
| `expressions.jsonl` | the session's expression log (§2.3) |
| `manifest.json` | `SessionManifest`: `{schemaVersion 1, kind SESSION_MANIFEST, sessionId, role SEED\|FOCUSED, obligationIds}` — FOCUSED when the replay was handed a focus row, its obligation ids from it. The only answer to "which session is the recording"; an absent or unknown role is refused |

IMPORT requires the ten files `activations` … `gaps` and `schedule` to exist and `expressions.jsonl`
to be non-empty (`campaign_import_session`). The publisher writes a root once per (occurrence, root
id, symbol, value) and an unreached target once per (occurrence, anchor site); a restatement that
differs is written, for invariants 4 and 8 to name.

### 2.2 Encoding (`RowCodec`)

JSONL, one object per line, one kind per file; reading a missing file gives no rows. A nullable
field is omitted when null and every other field is always written, so absence never means false
or zero. Every row but a `ScheduleEvent` carries `sessionId`; every row but an `ActivationRow`, a
`GapRow` and an `ObligationResult` carries `seq` (the event order). Shared parts:

- occurrence: `{node, regionId, context, index}` with `context` = `{form: ANCHOR, producerEndpointId,
  rpcSite}` | `{form: ROOT, role, api?, windowIndex}` | `{form: LOST, role}` and `index` =
  `[{callSite, iteration}, …]` (parts, never the render);
- endpoint: `{occurrence, site, siteIndex: [...], attempt}`; location: `{kind, owner, slot}`.

| row | fields (`?` = omitted when null) | meaning |
| --- | --- | --- |
| `ActivationRow` | `occurrence, taskId, focused, instrumented, threadKey, anchorProducer?` | one per activation. `focused`: ran symbolically as a task's region. `instrumented=false`: only the entry hook ran, so "no decisions" is no evidence. Same `threadKey` = program order. `anchorProducer`: the endpoint of this run that sent the message the context's anchor names. No thread-start edge exists |
| `DecisionRow` | `seq, occurrence, siteId, ordinal, outcome, term, clockReadings{symbol: reading}` | one branch: `ordinal` = k-th decision of the site in the occurrence (1-based); `term` = the predicate as written at the site (SMT-LIB over declared symbols and `EXPR.` refs; empty for a concrete branch); `outcome` = whether the term held. The conjunct is `outcome ? term : (not term)`, applied by the readers (`smt.Arms.conjunct`, `Arms.pathCondition`), never by the runtime |
| `ExportRow` | `seq, endpoint, expressionRef, javaType, handle, recordedValue` | a value put on the wire (`e_p`); `seq` cuts the producer's path condition; the sort comes from `javaType` |
| `AttachRow` | `seq, endpoint, symbol, javaType, arrival, answered, answeredValue?, producer?, correlationId, pairedBy?` | a value taken off the wire: `symbol` = the handoff variable `v_H` minted at the port; `producer` absent = unpaired; `pairedBy` = `HANDLE` or `CORRELATION_PORT` (absent = unstated); `answered` = an obligation's answer replaced the arrival |
| `WriteRow` | `seq, endpoint, location, version, expressionRef, javaType` | a write and the version of the location it produced; versions join reads within one session |
| `ReadRow` | `seq, endpoint, location, observedVersion, symbol, javaType, mintVersion?, concreteValue?` | a read: `observedVersion` = the version seen, `-1` when unknown (never 0); `mintVersion` = a placeholder's own store version (a placeholder's site contains `#PLACEHOLDER#`); `concreteValue` = what the read returned as `ReadRow.returned` spells it (a scalar's payload, a String as its JSON string literal, Java null as `N`; absent for an identity) |
| `RootMintRow` | `seq, occurrence, rootId, symbol, kind, recordedValue, domainMin?, domainMax?, declared, clockNanos?` | a root minted here. `kind` `MARKER` (a boolean: fault marker or boolean configured source), `INTEGRAL`, `CLOCK`; `symbol` is the root's one solver name; `recordedValue` is the value the region ran the root at — a fresh-box mint states the box it handed the region, the plant where one was applied (`runtime.RootMint.materializePrimitiveValue`) — except a CLOCK, which states the instant it read (its counterfactual is the focus row's skew); a clock site read again inside the occurrence is a later instant of the same root and stays concrete, so a clock root is the site's first reading in the occurrence. `domainMin/Max` absolute or absent (both absent = pinned); `clockNanos` = a CLOCK's tick in ns (1 for `nanoTime`, 1,000,000 for `currentTimeMillis`), present exactly for CLOCK |
| `TargetRow` | `seq, occurrence, anchorSiteId, phiTerm, observedFatal, reachedAnchor` | the annotated site, published whether or not the run reached it (unreached: `seq` 0). `phiTerm` is in the FATAL polarity and nobody re-derives it; empty when the anchor decided concretely. How the runtime forms it: [PIPELINE.md §5](PIPELINE.md) |
| `GapRow` | `kind, cls, subject, detail` | a refusal or diagnostic naming its subject; `sessionId` is the session, or `exploration` / `composition` for a stage's own rows |
| `ObligationResult` | `schemaVersion 1, kind OBLIGATION_RESULT, obligationId, verdict, detail` | §3 |
| `ScheduleEvent` | `seq, kind, context, site, k, occurrence?, endpoint?` (no `sessionId`) | `kind` ∈ `START, CLAIM, SEND, RECV, WAKE, END, INTERRUPT`; `context` = `<node>\|<causal context>[\|<start frames>]`; `k` = the k-th event of (kind, context, site); `occurrence` = the open region, where a prefix is cut; `endpoint` = the producer endpoint a SEND minted. Two runs compare events by `key()` = (kind, context, site). A `{mark: <occurrence id>, at: <seq>}` row marks where an occurrence opened. Readers stop at the first unreadable line. How the runtime records and holds it: [IDENTITY.md §8](IDENTITY.md) |

A focused replay's valuation is not read off `recordedValue` alone: EXPLORE and COMPOSE take the
focus row's `rootAssignments` where the replay planted a root (`explore.Corpus.rootValue`), and
invariant 6 judges a clock at its reading plus the focus row's `clockDeltas`
(`RowInvariants.executed`).

### 2.3 Expressions

A row names an expression by `EXPR.` + 16 hex digits (`ExpressionRefs`): a 64-bit Merkle hash over
the expression's JSON DAG — an object folds its member names in sorted order with their values, an
array its elements, a scalar its type tag and text (FNV-1a over UTF-16 units, finished with
murmur3's 64-bit finalizer); each node, by identity, is hashed once. Equal expressions have equal
refs in every session. Expression objects are the VM's nodes (`_type` names the kind;
[VM.md](VM.md)).

`expressions.jsonl` (`SessionExpressionLog`) is append-only: line 1 is `{kind:
SESSION_EXPRESSION_LOG, schemaVersion: 1}`; then `{node: n, expression: {...}}` lines, children
first, each child expression inside replaced by `{_type: SessionExpressionNode, node: m}` for a
node an earlier line defined; and `{ref: EXPR.…, node: n}` lines naming a node. Each node is
written once per session. Reading (`SessionExpressionLog.read`) rebuilds the shared DAG into an
`ExpressionTable` (ref → expression) and refuses a missing file or one with no header (never
published: an empty table would hide it behind `UNSTATED_VALUE`), a wrong header, a node named
before it is defined, or a node defined twice. Rows cite only this spelling (invariant 3); the
`EXPR.v1.<sha256>` anchors of `SharedExpressionTable`/`VmExpressionTable` live inside the
runtime's region store.

### 2.4 Reading (`SessionReader`)

`SessionReader.read` reads every file of a session whole. A file the codec refuses leaves that kind
empty and sets `incomplete()` (IMPORT: `SESSION_INCOMPLETE`, BLOCKING); `readHeader` reads only the
manifest and the roots. `seed()` = the manifest states SEED. `admitted()` = the seed, or at least one
own `obligations.jsonl` row and every one `ADMITTED`; only an admitted session states a topology.
The schedule is read on demand.

### 2.5 Gaps

`GapClass`: `BLOCKING` (no claim may be made over it) or `DIAGNOSTIC` (recorded; the claim stands).
The producer states the class on the row; EMIT reads a row with no class as BLOCKING.

| `GapKind` | raised for |
| --- | --- |
| `ADMISSION_GAP` | an occurrence, path or session that cannot be admitted or planned, a bound that dropped work |
| `TOPOLOGY_DIVERGENCE` | a pairing that contradicts the slot table or the run's order, an interaction outside the closure |
| `UNATTESTED_ARM` | an arm whose producer states no path condition (no instrumented activation) |
| `SCHEDULE_DIVERGED` | a focused replay left its schedule prefix (stated with both events; DIAGNOSTIC) |
| `UNSTATED_VALUE` | a value no row states: a read joining no version and pinning no value, a lowering refusal, a malformed row; a STATE location at the anchor whose reads' recorded pairing no family arm states (BLOCKING, [PIPELINE.md §8](PIPELINE.md)) |
| `UNPRODUCIBLE_ANSWER` | an attach answered or needed with a value no producer arm can produce |
| `FORMULA_SAT_AT_RECORDED_VALUATION` | the composed formula reaches the fatal arm at the recorded valuation on a healthy path |
| `DECLARATION_MISSING` | a root, port or name the case never declared; an undecided or erroring solver ask |
| `LINEAGE_LOST` | an address degraded by an unattributable hop; an unpaired attach; a missing site index |
| `TASK_UNANSWERED` | a planned task no activation answered (BLOCKING when PLAN states it) |
| `ADDRESS_UNSTABLE` | one planned task answered at two addresses across the corpus |
| `SOLVER_TIMEOUT` | a flip query z3 did not answer in time |
| `FRAME_UNBALANCED` | an activation closed at another execution-index depth than it opened at |
| `BOUNDED_LOOP_BODY_BOUND_UNDECLARED`, `BOUNDED_LOOP_FIXED_COUNT_BOUND_UNDECLARED`, `BOUNDED_LOOP_CLASSIFICATION_INCONSISTENT` | a retained loop ran under an inherited bound, an array loop declared none, a loop nest's control sites classify differently |
| `COMMUNICATION_REQUEST_PORT_UNRESOLVED` | a declared wire flow no region of the slice captures |
| `BOUND_INSUFFICIENT` | a port truncated its recorded accesses |
| `OCCURRENCE_ADDRESS_SHARED` | two activations of one region share one address |
| `MINT_UNATTRIBUTED` | a mint attributable to no node; a root symbol a session names without its `RootMintRow` (invariant 11) |
| `MESSAGE_CONTEXT_REFUSED` | a message-carried context the receiving side refused to install |
| `EPOCH_UNMATCHED` | a mint of the right site at the wrong node epoch |
| `SESSION_INCOMPLETE` | a session no reader could read whole |
| `ASSIGNMENT_UNPLANTED` | an assigned root whose mint ran without planting the value |
| `ASSIGNMENT_UNMINTABLE` | an assigned root the recording mints nowhere (the obligation is not run) |
| `PATH_SELF_CONTRADICTORY` | a composed path unsatisfiable with every root free (BLOCKING when every path is) |
| `CONFIRM_MISMATCH` | the confirmation replay took an edge the model did not choose, could not hold its order, or could not read the edges it was handed (`EDGES:`) |

### 2.6 The row invariants (`RowInvariants`, run by `ImportGateMain`)

`ImportGateMain --sessions <iteration>/sessions --out <gaps file> --topology-epoch <id>` reads the
sessions and each obligation worker's focus rows (joined to a session by the worker's result row,
never by directory name), appends every violation to the gaps file with `topologyEpoch`, and prints
`{topologyEpoch, sessions, violations, blocking, diagnostic, firstBlockingSubject, gaps,
blockingSubjects}`; it exits 0 unless the sessions are unreadable, and IMPORT fails on `blocking >
0`. One session is held in memory at a time. A violation's subject is `<kind>.jsonl seq=<n>
field=<f> <subject>`.

| # | rule | kind, class |
| --- | --- | --- |
| 1 | exactly one session states role SEED, and the SEED names no obligation; every session reads whole (`SESSION_INCOMPLETE`); every decision, target, read and write row's occurrence has an `ActivationRow` in its session | `ADMISSION_GAP`, BLOCKING |
| 2 | a read with `observedVersion < 0` states a `concreteValue`; an attach's `pairedBy` is absent, `HANDLE` or `CORRELATION_PORT` | `UNSTATED_VALUE`, BLOCKING |
| 3 | every `EXPR.`-like token in `term`, `phiTerm`, `expressionRef`, an attach's `symbol` and `arrival` is `EXPR.` + 16 hex and is in the session's table | `UNSTATED_VALUE`, BLOCKING |
| 4 | one row per event: no two reads or writes at one (seq, location), decisions at one (seq, site, ordinal), targets at one (occurrence, seq when reached else 0, anchor site) — BLOCKING; events of one kind at different seqs sharing one endpoint id — DIAGNOSTIC `LINEAGE_LOST` (the site index does not tell them apart) | `UNSTATED_VALUE` |
| 5 | a minted symbol `M_<sort>_<name>` has one sort per name across roots, attaches and reads, and a read's symbol sort is its `javaType`'s | `UNSTATED_VALUE`, BLOCKING |
| 6 | a decision term that evaluates at the valuation the session ran under (declared roots and literals through `==, !=, <, <=, >, >=, +, -, *, &, \|, ^`, boundary and read-from nodes) agrees with `outcome`; the valuation is the mints' `recordedValue` for the seed and the focus row's ask for a focused session (a CLOCK = reading + skew); a FOCUSED session with no focus row is BLOCKING | `UNSTATED_VALUE`, BLOCKING |
| 7 | an observed version no `WriteRow` and no `mintVersion` of the session states — DIAGNOSTIC; a placeholder read without `mintVersion`, or a `WriteRow` at a placeholder's minted version (a fabricated write) — BLOCKING | `UNSTATED_VALUE` |
| 8 | a `RootMintRow` only for a declared root (`DECLARATION_MISSING`); a MARKER reads `true`/`false`, an INTEGRAL or CLOCK a plain decimal; one row per (occurrence, root id) (`UNSTATED_VALUE`) | BLOCKING |
| 9 | a reached anchor states a `phiTerm` (BLOCKING when it observed the fatal, else DIAGNOSTIC: a concrete branch); an observed fatal's `phiTerm` does not evaluate false at the session's valuation (BLOCKING) | `UNSTATED_VALUE` |
| 10 | a focused session states a decision at its focus row's flip (site, ordinal) with the asked outcome | `ADMISSION_GAP`, DIAGNOSTIC |
| 11 | every root symbol a session names (in a term, a `phiTerm`, or its expression table) has a `RootMintRow` of that session | `MINT_UNATTRIBUTED`, BLOCKING |

## 3. Exploration contract

- `Task(taskId, focused, factor, seedSessionId)`: one focused occurrence and its state-connected
  co-occurrences (`factor`, may be empty), planned from `seedSessionId`'s recording. `taskId` =
  sha16(`task|` + focused id) (`explore.ClosurePlanner.taskId`). `tasks.jsonl`: `{taskId, focused,
  factor, seedSessionId}` with occurrences as parts.
- `Obligation(obligationId, taskId, pathId, siteId, ordinal, flippedOutcome, rootAssignments,
  answers, unproducible)`: one path prefix and one decision to take the other way.
  `rootAssignments` = root id → value, `answers` = attach endpoint id → value (one attach, not a
  port), `unproducible` = attach endpoint ids answered without a producer arm. `pathId` = sha16(session
  id + `|` + occurrence id) (`explore.Corpus.pathId`). `Obligation.confirming` is a CONFIRM run: empty
  site, ordinal 0, `flips()` false. `obligations.jsonl` rows carry exactly these fields.
- `Verdict`: `SAT_MODEL_READY` (a model exists, the replay may run), `UNSAT`, `ADMITTED` (a focused
  replay took the flipped arm and published its rows; never "validated"), `NOT_ADMITTED`.
  `ObligationResult(obligationId, verdict, sessionId, detail)`, `sessionId` "" when no replay ran.
- The worker directory (`ObligationDir`): `<iteration>/obligations-NNNN/<obligationId>/` with
  `obligation.jsonl`, `obligation_result.jsonl`, `focused_task.jsonl`, plus `obligation_query.smt2`,
  `gaps.jsonl`, `schedule_prefix.jsonl`, `schedule_suffix.jsonl` and the replay's logs.
  `ObligationDir.workersIn` lists the workers whose result row names a session.
- The focus row (`focused_task.jsonl`, `explore.ExploreCodec.writeFocusRow`, read by
  `runtime.FocusedReplay` and, as the session's world, by `ExploreCodec.readWorld`):
  `{schemaVersion 1, kind FOCUSED_TASK, taskId, focused, focusedOccurrenceId, declaredTarget?,
  seedSessionId, factor, obligationId, pathId, flip: {siteId, ordinal, outcome} | null,
  inheritedFlips: [{focusedOccurrenceId, siteId, ordinal, outcome, obligationId}], rootAssignments,
  clockDeltas: {rootId: skew}, answers, rootMints: {rootId: rendered mint occurrence}, unproducible,
  schedulePrefix?: {sessionId, events, rest, of, cutAtFocus}}`. A clock's counterfactual is a skew
  the replay adds to its own reading; a root is planted only at a focused mint, so each assigned
  root's mint occurrence is focused.
- CONFIRM's worker adds `expected_edges.jsonl` (`runtime.Confirmation.FILE`): `WIRE {consumer,
  producer, selector}`, `STATE {reader, mint, writer, version, location}`, `ORDER {before, after}`
  (activation keys), `MARKER {root, value}`, `ANCHOR {occurrence, seq}`. A run whose obligation
  flips nothing (`Obligation.confirming`) owes these rows: missing or unreadable, it files a
  `CONFIRM_MISMATCH`. `final/confirm.json` is `{schemaVersion 1, kind CONFIRMATION, confirmed,
  reason, sessionId}` ([PIPELINE.md §10](PIPELINE.md)).

## 4. Composition contract

- `Arm(producerPathId, piRef, expressionRef, guardRoots, attested)`: one producer path's delivery
  `pi_q ∧ guard_q ∧ v_H = e_q`; `guardRoots` = only the roots `e_q` depends on; `attested` = the
  producer's session has an instrumented activation for it, so it states a path condition.
- `Family(interactionId, arms)`: the arms one interaction's consumer could have received.
- `PathEntry(pathId, sessionId, selector, fatalObserved)`: one composed path and its selector.
- `RootDomain(rootId, kind, recordedValue, min, max)`: absolute bounds, both null = pinned.
  `RootDomain.declared(file)` is the one reader of `root-domains.jsonl` (rows `{sourceId,
  declaredDomainMin, declaredDomainMax}`, each absolute or `+k`/`-k` from the recorded value; no file
  declares nothing); `RootDomain.resolved(mint, declared)` is the one join: the case's declaration
  if any, else the mint's bounds, with the mint's kind and recorded value.
- `ClaimKind`: `MARKER_FLIPPED`, `CLOCK_SKEW`, `MESSAGE_PAIRING_FLIPPED`, `STATE_PAIRING_FLIPPED`,
  `RECORDED_FAILURE_EXPLAINED`, `NO_SUPPORTED_WITNESS` ([PIPELINE.md §9](PIPELINE.md)).
- `Claim(kind, valuationOrdinal, movedRoots, polarityDecides, gaps)`: `valuationOrdinal` 0 is the
  recorded valuation; `movedRoots` maps a moved root's id, or a moved clock cell's symbol, to its
  value in the witness; `polarityDecides` = the recorded valuation's disjunct is unsat with a
  valuation pin in its core; `blocked()` = a BLOCKING gap travels with it.
- `CompositionManifest(anchor, paths, families, roots, valuations, claim, smt2Path)`: written by
  `compose.ComposeMain` into `candidate_composition_manifest.json`, which adds `schemaVersion`,
  `kind COMPOSITION_MANIFEST`, `anchor` (rendered), `anchorId`, `seedSessionId`,
  `symbolicPropagationComplete`, `finalStatus`, `finalStatusRefusals`, `gaps` and `solver`.

## 5. Rules every stage keeps

- Identity is by `Endpoint` and `Interaction`; a family is keyed by its interaction.
- `phiTerm` is published in the fatal polarity by the runtime; COMPOSE never re-derives polarity.
- A decision's polarity is applied by its reader (`Arms.conjunct`, `Arms.pathCondition`), for
  COMPOSE and flip queries alike.
- One lowering, `compose.SmtLowering`, serves COMPOSE and the flip queries
  (`explore.FlipQuery.statedTerm`), and one tokenizer and vocabulary, `compose.SmtNames`: a name
  is a theory operator iff `SmtNames.BUILTIN` lists it, and it lists every operator the lowering
  writes; any other name must be declared, let-bound or in the preamble.
- A read binds, in order: to the expression of the write it observed if that lowers with no
  refusal, else to its version's mint, else to the value its row states, else it is refused
  `UNSTATED_VALUE` (`compose.SmtLowering.bind`, the one rule of a read row in
  `compose.Composer.stateJoins` and of a guarded read node). A join that refused yields to the mint
  or the value only if nothing it rests on can move -- a root or clock cell, a handoff, a read a
  STATE family may re-pair, through every read's own write; otherwise the read is refused. A flip
  query offers eligible writers as choices first ([PIPELINE.md §7.5](PIPELINE.md)).
- A method-return symbol (`M_<t>_return<n>`) is the call its node states (VM f14 member `call`:
  `_name` `"<holder> <method>"`, `_param_list`): `Integer.parseInt`/`Long.parseLong` of a String and
  `String.valueOf`/`Integer`/`Long.toString` of an integral are relations; any other callee is pinned
  to the node's `concreteValue` by a named assertion, only if nothing its arguments rest on can move.
  A node stating no call is refused.
- A per-session fact — arrivals, clock readings, the valuation — stays inside that path's
  conjunction, never a global assertion.
- A root without a domain is pinned in COMPOSE and in flip queries; a declared MARKER is free over
  both values; a CLOCK's window is `[reading, reading + 30 days]` in its own ticks
  (`smt.JavaPrimitiveSmtSemantics.clockDomain`/`clockSkewCeiling`), in COMPOSE replaced by the
  case's bounds when `root-domains.jsonl` declares them.
