# DESIGN 4 — fault points, symbolic inputs, and the iteration (2026-09-23)

Status: proposal for the owner. Frame: `LEAN-DESIGN.md` (fixed) and the paper's
§4.2. Evidence: the nine v15 corpora at main@497dc8beb (`~/gc-out/accept-v15-*`)
and five read-only code surveys of PLAN, runtime, EXPLORE, COMPOSE and the
driver (2026-09-23). Line numbers are of main@497dc8beb.

## 0. What the evidence says

1. **Fault markers never reach a formula.** Every block-key workload models
   "the key-refresh RPC fails" with `Debug.makeSymbolicBoolean("hadoopIpcRequestFails")`
   in `ipc.Client.sendRpcRequest` (Client.java:1253). It fires in every recording
   (bug1: 6 firings, bug2: 34, 17897: 5), and yet no session of any case holds a
   MARKER root: the roots of all seven block-key cases are CLOCK and INTEGRAL
   only, and every replay files `DECLARATION_MISSING marker=hadoopIpcRequestFails#1
   … NO_ACTION_ACCEPTS_THIS_OCCURRENCE` (62 rows in bug1's gaps.json). Three
   cuts, all in the engine:
   - `f5cd60449` (2026-09-16, "Delete the discovered ports…") removed
     `RuntimeSelectedRegionFinalizer.explicitFaultPorts`, the only producer of
     `sourceKind=EXPLICIT_SYMBOLIC_FAULT` actions, as "inert already". Every
     downstream reader (RuntimeRegionPlanner:1912-1926, ConcolicScheduler:734-760,
     822-844, 1745-1748, FaultMarker:59-76) is still there, fed by nothing.
   - `failureDirectedClosure` (Finalizer:956-1170) admits an occurrence only as a
     fatal target, a holder of a declared input, a cut-port capture, or a writer
     the write-site walk reaches. The marker's occurrence (REGION.763d087e =
     `Client$Connection.sendRpcRequest`, which exists in region_skeletons and
     survives pass 1) is none of these: a fault is a CONTROL effect — the RPC is
     not sent — not a store into a cell the fatal reads. So `applyClosure` drops
     the region and the plan has no row for it.
   - At replay `FaultMarker.materialize` (FaultMarker:106-142) returns the
     recorded polarity as a plain concrete boolean; `if (causynth.active() && m)`
     is a concrete branch and never a DecisionRow with a term, so it is never a
     flip candidate.
   The CLOCK_SKEW witnesses the acceptance confirmed are real, but they are the
   only kind the engine could ask for. MARKER_FLIPPED was unreachable by
   construction for hdfs-17899 bug1/2/3 and hdfs-17897.
2. **The paper's iteration (§4.2.4) has no counterpart.** The woven class set is
   frozen at INSTRUMENT[0]; an occurrence first reached in a replay publishes
   only an `instrumented=false` activation (SlotTable:568-576) and can never
   hold a decision, export or attach; the epoch loop's producer
   (`seedsNextEpoch`) no longer exists in `src/main` (run_engine.sh:3956-3958
   admits it); a new producer paired with a known consumer is a "replacement",
   BLOCKING, emptying the wave (ExploreMain:182-185) instead of becoming a new
   arm. ClosurePlanner recomputes tasks per wave over the UNION of every
   session's rows (Corpus:891-918), so per-world topology is conflated. Opened
   slots feed nothing: tasks are planned before `SlotTable.reconcile`
   (ExploreMain:147 vs 164) and `skeleton.opened` reaches only the manifest.
3. **Alternative RPC outputs exist only across disjuncts.** A message family has
   ONE arm whenever the consumer path's own session is eligible (rule R3d,
   ComposedFamilies:521-526): every `message_family` of hdfs-17899 is
   `(and arm (=> arm (= v 119978)))`. The paper's `x = ite(s, x1, x2)` is
   realised only as "one disjunct per replay", never inside a path.

Everything below keeps LEAN §1-§4: three mint places, rows as the contract,
explore collects arms, compose aligns/merges/lowers/gates. No stitching, no
carrier layer.

## 1. Fault injection points (Q1)

### 1.1 Definition

A fault point is a Boolean root `m` minted at an interaction operation inside a
region occurrence. `m = false` is the recorded behaviour; `m = true` is the fault
behaviour the door implements (the transport's failure: `IOException` at an IPC
send, the SASL exchange's failure at a SASL send). It is LEAN §1 root kind 1 ("fault
markers"): no new symbol kind, no new row kind. Its identity is the identity of
any handoff: (occurrence, door site, k-th firing) — `HandoffMint.nextAttach`'s rule.

### 1.2 Two declarations, one mint

- **Workload-declared** (kept): `Debug.makeSymbolicBoolean(name)` written into the
  program text, as today. It is the general escape hatch for faults the catalog
  cannot name (a disk write, a local timeout).
- **Door-declared** (canonical): every mapped transport door. The transports are
  the ones `communication-mappings.jsonl` names (`HADOOP_IPC`, `HDFS_SASL`). At
  each client send door the tree's canonical instrumentation mints
  `Debug.makeSymbolicBoolean("FAULT:<TRANSPORT>:<DIRECTION>")` — the same call
  as (a), with a name the catalog fixes — and throws the transport's failure
  when the polarity is true: `if (Debug.makeSymbolicBoolean("FAULT:HADOOP_IPC:REQUEST"))
  throw new IOException(...)` before the request header is built, and the SASL
  client's send likewise. The mint stays in the tree because the static slice
  reads the caller's region; it is one hunk, byte-identical in every tree
  (the hand-written `hadoopIpcRequestFails` with its `causynth.active()` guard
  is replaced by it, and hdfs-11741's tree gets it too).
- Both mint **unconditionally** (the recording's rule since `278e80a2dbf`): a
  planted `true` exists only inside a focused world, so the throw needs no
  guard. The recorded polarity is always false.
- Receive-side faults (a response lost, a timeout) are a second door
  (`inbound`). Out of scope for this design; the same rule applies when added.

### 1.3 What makes a marker symbolic at replay

- **PLAN.** The firing is a declared site: `StaticScopeMap.addDeclaredSite`
  (536-548) also accepts the `explicitSymbolicFault` edge (a `CALL_RETURN` of
  type boolean, carrying `symbolicName`); the finalizer's `declaresACapturedCallee`
  (1302-1315) treats `Debug.isBooleanMarkerSignature(callee)` as declared, so the
  firing's occurrence (or its fold owner) is admitted exactly like an occurrence
  that read a declared clock; `DeclaredSiteCapture.callReturnPort` (279-292) stamps
  `sourceKind=EXPLICIT_SYMBOLIC_FAULT`, `symbolicName`, `javaType=boolean`;
  `ConcolicScheduler` (1629) lets a workload-owned symbol through the
  declaration check it already states at 1700-1702. A door marker is a catalog
  declaration with a fixed callee (the shim door) and follows the same path.
- **REPLAY.** The plan's `CALL_RETURN` action binds the local the firing defines
  (`$z1` at `sendRpcRequest#u16`) as `LOCAL_DEFINITION`
  (ConcolicScheduler:734-760; woven by ConcolicInstrumentationSelections:464).
  The mint is `RootMint.materializePrimitiveValue` (867-935): kind MARKER
  (`javaType=boolean`, RowPlaceholderMint:819), concrete = the recorded polarity
  (`FaultMarker.materialize`), planted = `FocusedReplay.rootAssignment(symbol)`
  when the wave asks for the flip. The branch on `m` is then a DecisionRow whose
  term is `m` — a flip site like any other. `FaultMarker` keeps one job: answer
  the recorded polarity.

### 1.4 Which fault points are explored

A marker decision `d_m` of occurrence `o` is a flip candidate iff `o` is a task
of the wave (in the target's closure). One rule change in `ClosurePlanner`: the
flip-site set of a task = guards of the demanded sites ∪ every marker decision of
the occurrence — a fault guards everything the send would have produced, so the
demanded export's producer path carries `¬m`. Bounds: one fault flip per
(occurrence, door site, k) per world; nesting under `maxWorldDepth` as for clocks.
Order: in the first wave that reaches the occurrence, fault flips are proposed
before that task's clock flips (the query is `prefix ∧ m`, cheap; the world it
opens is the one that grows the graph, §3).

### 1.5 Domain and claim

MARKER free in {recorded, flipped} (LEAN §4). A witness whose valuation flips a
marker is MARKER_FLIPPED; one that also moves clocks reports both kinds, the
polarity gate deciding from the unsat core which pins matter. For hdfs-17899 the
acceptance bar becomes: the refresh RPC's marker in `movedRoots`; clocks optional.

## 2. Symbolic variables (Q2)

LEAN §1 already states the rule and the owner's formulation is the same rule:
what enters a region from outside is temporarily a symbol, it is joined to its
producers by propagation and composition, and every RPC fault marker is a symbol.
What changes is coverage and automation, not the rule.

### 2.1 The inputs of an occurrence `o`

- **(R) roots minted inside `o`.** Every clock API read in an instrumented region
  (callee-level rows of `symbolic-inputs.jsonl`: `Timer.now`, `Time.now`,
  `Time.monotonicNow`; the per-method clock rows select regions and no longer
  take part in the input rule), configured sources (`CausynthSymbolicSource`
  hooks), fault markers (§1).
- **(B) boundary values.** (B1) wire attaches: one `v_H` per element
  (port, occurrence, k, element path) — as today. (B2) shared state: reads join
  the version they observed, a location becomes versioned at its first symbolic
  or guarded write — as today (LEAN addendum 09-15). (B3) thread handoffs: the
  value travels with the object (shadows by value), the consumer's identity is
  the started root; add `BlockingQueue.put/take` to `WorkStartSites` so a queued
  command's consumer (a DataNode's command processor) is attributed to the turn
  that enqueued it rather than Lost.
- **(C) everything else is concrete** until a symbolic value is written into it.

### 2.2 Binding at compose

`v_H := ite` over arms; each arm = the producer path's condition ∧ `v_H = e_p` ∧
the producer's world. Rule R3d (one arm when the own session is eligible) becomes:
every producer path whose world is compatible with the consumer path's world is
an arm (§3.4). A boundary symbol nothing binds refuses the path (UNATTESTED_ARM);
it is never free. This is the lesson of the spurious v9 witnesses (one symbol for
four keys): a free leaf is a witness the engine invented.

### 2.3 One declaration surface

One `Declarations` table — case callees and cells, hook mints, cut ports from the
mappings, door markers from the transports, workload markers from the program
text — consumed by the scope map, the finalizer's admission and the scheduler's
port rule. Today three deciders each hold part of it
(`declaresACapturedCallee` / `foldedADeclaredInputRoot` / `attachedADeclaredPort`
in the finalizer; `workloadOwnedSymbol` + `admits` in the scheduler) and the
marker fell into the gap between them.

### 2.4 What stays out

No region-entry container symbols, no carrier lists, no window-start deliveries
(LEAN §5). The static slice decides which regions are woven; it does not invent
inputs.

## 3. The iteration after a flip (Q3)

### 3.1 Persist `G_k`

Nodes = occurrences (r, c, i) with their node and the world (flip set) they were
observed in. Edges = wire slots (producer endpoint → consumer endpoint), state
edges (writer → reader, by version), thread edges (START → CLAIM). All of it is
already in the rows (activations, exports/attaches, writes/reads, schedule);
`graph.jsonl` per wave replaces `slots.jsonl`, world-labelled.

### 3.2 Diff per world

After each wave, for every ADMITTED session `S` with world `w`: build `S`'s own
graph, take the backward closure from `o_T` inside it (per world — not the union),
and diff against `G_k`. New relevant nodes and edges enter `G_{k+1}` labelled `w`.

### 3.3 Three kinds of growth, three responses

- (a) **A new occurrence of an instrumented region** (a retry runs the handler
  again; another daemon turn). It has rows, so it becomes a task in the next
  wave. This works today.
- (b) **A new occurrence of a region in scope but not woven** (a recovery handler
  reached only under a fault). Today it is an ambient activation forever. New:
  a growth step inside the wave — INSTRUMENT with the grown region set (the
  weave takes ~15 s per campaign), a region-level plan row synthesised for it
  (`admissionBasis = EXPOSED_BY(session, world)`; its symbolize actions are the
  region's static declarations: clocks, cut ports, markers), and the exposing
  obligation's replay re-run under the same world; the re-run session replaces
  the exposing one in the corpus. The next wave's closure then sees its
  decisions and exports.
- (c) **A new producer for a known consumer under world `w`.** Today a
  replacement, BLOCKING. New: a new arm keyed by `w` — the paper's selector `s`
  IS the world's flip. Replacement stays BLOCKING only within one world: two
  pairings under the same flips mean the schedule did not hold, and
  SCHEDULE_DIVERGED already says so.

### 3.4 Compose over `G_k`

Family arms = the producer sessions whose world is compatible with the consumer
path's world (the producer's flip set ⊆ the consumer's inherited flips, or the
reverse); one selector per arm; exactly one. This replaces R3d and gives the
paper's `ite(s, x1, x2)` inside a path.

### 3.5 Loop and termination

wave := tasks over `G_k` → obligations (fault flips, then decision flips) →
replays → diff and growth → `G_{k+1}`. Stop when no new relevant node or edge and
no open obligation; bounds = world depth, waves, an obligation budget. A bound hit
is stated (`BOUND_REACHED`, claim `INCONCLUSIVE_BOUNDED`) — never silent.

### 3.6 Deleted

The epoch loop (`campaign_max_epochs`, `seedsNextEpoch`, `retain/grown/unplannable`,
`campaign_refinement_*`), `SlotTable.unretained`'s BLOCKING, the "topology closed
at iteration-0000" manifest. `--retain-regions` stays as the INSTRUMENT input of
the growth step.

### 3.7 Schedule under a fault world

Prefix up to the flipped send (the cut is at the target as today); the recovery
path's events are unnamed and run free; the rest holds the timeouts (D3 rule 26).
Nothing new is needed.

## 4. Validation

- V1 PLAN: bug1/bug2/17897 plans carry one `EXPLICIT_SYMBOLIC_FAULT` action per
  marker occurrence; marker `DECLARATION_MISSING` rows drop to 0.
- V2 wave 0 proposes the marker flip on the refresh RPC; the replay throws; the
  session records the catch path; a MARKER root row is present.
- V3 hdfs-17899 bug1 yields a MARKER_FLIPPED witness: the balancer's refresh
  fails, the NameNode's two recorded rotations retire the cached key, the
  DataNode rejects it. The acceptance bar: the refresh marker in `movedRoots`.
- V4 growth: a fault world whose recovery path reaches an unwoven region gets
  it woven and explored in the same campaign (a synthetic ExploreTest plus bug1's
  catch path).
- V5 all nine cases on one commit through the acceptance workflow, with the
  expected kinds per case revised: MARKER_FLIPPED for hdfs-17899 bug1/2/3 (and
  17897 if its marker is the mechanism), CLOCK_SKEW for hdfs-17967 A/B/C and
  hdfs-11741, MARKER_FLIPPED (config) for hdfs-17960.

## 5. CONFIRM (a SAT claim, checked by one replay)

SAT says the model satisfies our formula; CONFIRM says the program agrees.
One focused replay after DECIDE, only for a `SAT_CANDIDATE`: re-run the
world the selected path's own session ran -- the root values, clock skews
and answers its obligation's focus row planted, MARKERs included, proven in
an execution -- with no flip forced and none inherited (the values drive the
decisions), hold that session's schedule exactly as an obligation replay
does (strict prefix to the anchor, timeouts after), and run once. The
model's own instants are the published witness, not what the run is held
to: a solver sits on the boundary of its constraints and a run's timeline
moves by more than that (bug1: the anchor reached, the fatal not observed,
with the model's clock deltas planted). The recording's own session planted
nothing, and nothing is planted for it.
The claim is confirmed iff (a) no
`SCHEDULE_DIVERGED` before the anchor's cut, (b) every edge the model chose
is the edge the run took -- per message family the selected arm (consumer
endpoint ← producer endpoint), per state join the writer version the read
observed, per marker its planted polarity -- and (c) the anchor's target
row states `observedFatal` and `reachedAnchor`. Checking, never enforcing:
the existing hooks (the attach, the read and write rows, the target row)
compare against `expected_edges.jsonl` and file `CONFIRM_MISMATCH`
(DIAGNOSTIC) gaps; the run is scheduled by the session's schedule as today.
Failing any of the three downgrades the claim to `SAT_UNCONFIRMED` with the
first mismatch named (`final/confirm.json`, copied into `result.json`); the
acceptance harness passes a case only on `confirmed=true`.
