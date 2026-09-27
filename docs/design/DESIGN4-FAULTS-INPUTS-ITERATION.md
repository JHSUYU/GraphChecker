# DESIGN 4 — fault points, symbolic inputs, and the iteration (2026-09-23)

Status: implemented on `refactor/deterministic-prefix`. Frame: `LEAN-DESIGN.md`
(fixed) and the paper's §4.2. Where the code and this page disagree, the rows decide
and this page is corrected.

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
  reads the caller's region; it is one hunk, byte-identical in every tree.
- Both mint **unconditionally** (the recording's rule since `278e80a2dbf`): a
  planted `true` exists only inside a focused world, so the throw needs no
  guard. The recorded polarity is always false.
- Receive-side faults (a response lost, a timeout) are a second door, by the same
  rule: `FAULT:HADOOP_IPC:RESPONSE` at `Client.getRpcResponse`, where the caller
  takes the reply; true throws the transport's `IOException` after the server
  applied the request (§1.5, corrected).

### 1.3 What makes a marker symbolic at replay

- **PLAN.** The firing is a declared site: `StaticScopeMap.addDeclaredSite`
  (536-548) also accepts the `explicitSymbolicFault` edge (a `CALL_RETURN` of
  type boolean, carrying `symbolicName`); the finalizer's `declaresACapturedCallee`
  (1302-1315) treats `Debug.isBooleanMarkerSignature(callee)` as declared, so the
  firing's occurrence (or its fold owner) is admitted exactly like an occurrence
  that read a declared clock; `DeclaredSiteCapture.callReturnPort` (279-292) stamps
  `sourceKind=EXPLICIT_SYMBOLIC_FAULT`, `symbolicName`, `javaType=boolean`;
  `ConcolicScheduler` (1629) lets a workload-owned symbol through the
  declaration check it already states at 1700-1702. A door marker
  `FAULT:<TRANSPORT>:<DIRECTION>` is declared iff the case's
  communication-mappings.jsonl maps that transport
  (`WireFlowCatalog.declaredTransports`, `StaticScopeMap.declaredFault`): a
  case that maps no transport admits no door, so its unregistered client is
  not planned (hdfs-17960).  Every other symbolic name follows the same path.
- **REPLAY.** The plan's `CALL_RETURN` action binds the local the firing defines
  (`$z1` at `sendRpcRequest#u16`) as `LOCAL_DEFINITION`
  (ConcolicScheduler:734-760; woven by ConcolicInstrumentationSelections:464).
  The mint is `RootMint.materializePrimitiveValue` (867-935): kind MARKER
  (`javaType=boolean`, RowPlaceholderMint:819), concrete = the recorded polarity
  (`ConcolicRegionRuntime.materializeSymbolicBoolean`, always false), planted =
  `FocusedReplay.rootAssignment(symbol)` when the wave asks for the flip, and
  the mint row states the value the region was handed (the plant where one
  followed). The branch on `m` is then a DecisionRow whose term is `m` — a
  flip site like any other; at the door `if (fault) throw`, the throw branch
  is the decision's `false` outcome and the solver assigns `m = true` for it.

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
marker is MARKER_FLIPPED. The run as it happened is the recorded roots, every
clock at the instant its session read, and every path on the pairing its own run
had (the value each attach a family binds received, anchor and upstream alike).
Where the clocks or the pairings are what refute the recorded valuation, a
flipped marker is asked with all of them held: the fault is a finding only if it
reaches the fatal arm with time and pairing as recorded, and only when no fault
does is the clock (CLOCK_SKEW) or the pairing (STATE/MESSAGE_PAIRING_FLIPPED) the
mechanism. FORMULA_SAT_AT_RECORDED_VALUATION is raised only when a healthy path
reaches the fatal arm with all of it held. The witness a claim publishes keeps
every clock pin it can.

Which mechanism each case must show follows from its tree, not from a preference:
every tree of the block-key family (hdfs-17899 bug1/2/3, hdfs-17897, hdfs-17967
A/B/C) carries 11741's expiry check, so a key goes stale there only through a
failed RPC, and those cases are accepted only with an IPC door fault flipped and
no clock moved. hdfs-11741 has no expiry check, so a flipped branch with no fault
already reaches its fatal: CLOCK_SKEW. hdfs-17960's mechanism is its configured
Boolean.

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
  again; another daemon turn). A planned task admits only its own address, so
  an occurrence no task admitted has no decisions -- but the hooks ran it, and
  its runtime identity is in the rows (a SEND, the sender an anchor names, a
  delivery's producer). The closure decides: a demanded occurrence some session
  captured is a task; one only named by an admitted focused replay is grown as
  (b) is, re-running that replay with a plan row at its address; one only the
  seed replay ran waits for a focused replay, and is a BLOCKING gap only at the
  fixpoint (owner 2026-09-27: the hooks discover runtime regions).
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
no open obligation; the corpus is composed once, at that fixpoint, whatever the
claim (owner 2026-09-27: the per-wave witness probe that stopped early on a
MARKER_FLIPPED witness is gone -- a special path for one claim kind, costing a
whole composition every wave). Bounds = world depth, waves, an obligation budget. A bound hit is stated (`BOUND_REACHED`,
claim `INCONCLUSIVE_BOUNDED`) — never silent.

### 3.6 Schedule under a fault world

Prefix up to the flipped send (the cut is at the target as today); the recovery
path's events are unnamed and run free; the rest holds the timeouts (D3 rule 26).
Nothing new is needed.

### 3.7 The nearest world (obligation queries)

A root's domain is a window and a flip query is satisfiable at many points of
it; z3 answers with one of them, usually on a boundary. The formula is
satisfied there, but the program is not held to the formula: a clock moved by
the whole window rotates keys the path never read and reorders the loop the
flipped decision sits in, so the replay takes an inherited flip the other way.
Every obligation query therefore asks for the world nearest the recording:
`(minimize Σ |x − recorded(x)|)` over the Int roots and clocks it bounds
(`FlipQuery.Builder#nearest`, rendered by `FlipQueryText`). The answer is the
smallest move that still takes the other arm, with the margin -- what a
witness means -- and it is deterministic across encodings of the same corpus.

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
  expected kinds per case revised (as corrected by the owner, §1.5): MARKER_FLIPPED
  by an IPC door fault with the clocks at the recording for hdfs-17899 bug1/2/3,
  hdfs-17897 and hdfs-17967 A/B/C; CLOCK_SKEW for hdfs-11741; MARKER_FLIPPED
  (config) for hdfs-17960.

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
What the claim needs is one run that took every edge the model chose, with
the moved roots at the model's values, and observed the fatal at the anchor.
When every arm the model chose is a delivery the selected session itself
recorded, and that session minted each moved root at the model's value and
observed the fatal, the selected session IS that run: it is the confirmation
(`ConfirmMain.realizedBy`, `realized.json`) and nothing is replayed -- a
replay of its world would test only whether a race the order does not hold
goes the same way twice (hdfs-17899 bug2, v38: the replay's schedule stalled
at the DataNode actor's heartbeat and one chosen consumer never attached,
while the selected session had taken both chosen edges and the fatal). A
model that combines deliveries of different sessions has no such run, and
the replay makes one.
The replay's claim is confirmed iff (a) every edge the model chose
is the edge the run took -- per message family the selected arm (consumer
endpoint ← producer endpoint), per state join the model chose among alternative writers the writer the read
observed (a join with one candidate is the recording's, and rule (b) checks where it leads), per marker its planted polarity -- and (b) the anchor's target
row states `observedFatal` and `reachedAnchor`. The edges and the fatal are
the evidence; the schedule is how the replay reproduces the selected
session, and a divergence of it stays a diagnostic gap (2026-09-24): the
order holds communication and thread events, not plain field accesses, so a
race between threads can move events the model's explanation does not
depend on. Round v36's hdfs-17899-bug2 CONFIRM took every edge the model
chose and observed the fatal at the anchor, and was refused on the order
alone: the workload's `triggerHeartbeatForTests` read the DataNode actor's
`nextHeartbeatTime` after that actor's heartbeat instead of before, waited
for the next one, which the order places after the workload's own request,
and the watchdog gave the slots up. Checking, never enforcing:
the existing hooks (the attach, the read and write rows, the target row)
compare against `expected_edges.jsonl` and file `CONFIRM_MISMATCH`
(DIAGNOSTIC) gaps; the run is scheduled by the session's schedule as today.
Failing either downgrades the claim to `SAT_UNCONFIRMED` with the
first mismatch named (`final/confirm.json`, copied into `result.json`); the
acceptance harness passes a case only on `confirmed=true`.
